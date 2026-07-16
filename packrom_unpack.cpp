// ============================================================================
//  Unpacker for  *_PACK.rom  files
//  (Konami "Disney Sports"-family GameCube format)
//
//  WHAT THESE FILES ACTUALLY ARE
//  -----------------------------
//  A *_PACK.rom is NOT an LZ-compressed archive. It is a *relocated memory
//  snapshot* of a resource that was serialized straight out of RAM:
//
//    * big-endian 32-bit words (the game ran on PowerPC / GameCube)
//    * internal pointers are stored as ABSOLUTE addresses in a virtual
//      address space whose load base is 0x40000000
//    * the payload is a dense graph of small allocations: tagged property
//      lists, arrays, null-terminated strings, texture data and quantized
//      animation curves.
//
//  Empirically every file in the set is >99% covered by the pointer graph
//  reachable through those 0x40000000 addresses, which is what confirms the
//  format.
//
//  WHAT "UNPACK" MEANS HERE
//  -----------------------
//    1. (optional) transparently DECOMPRESS if a known container magic is
//       present (Yaz0 is implemented; raw files pass straight through).
//    2. RELOCATE: rewrite every pointer word to a file-relative offset so the
//       structure becomes position-independent            -> <name>.unpacked.bin
//    3. DECOMPOSE: split the image into its allocation blocks
//       (one per distinct pointer target)                 -> blocks/
//    4. Extract metadata: printable ASCII strings          -> strings.txt
//    5. Dump a best-effort structured view of the graph    -> layout.txt
//    6. Write the relocation site table (for re-packing)   -> reloc.txt
//
//  BUILD
//    g++ -O2 -std=c++17 -o packrom_unpack packrom_unpack.cpp
//
//  USAGE
//    ./packrom_unpack <file.rom | directory> [options]
//      -o <dir>       output directory            (default: ./unpacked)
//      --base 0xADDR  override load base          (default: auto, else 0x40000000)
//      --rebase 0xN   base to write into output   (default: 0  => raw offsets)
//      --max-dump N   words dumped per block in layout.txt (default: 48)
//      --no-blocks    skip writing individual block files
//      -q             quiet (summary only)
// ============================================================================

#include <cstdint>
#include <cstring>
#include <cmath>
#include <cstdio>
#include <string>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <fstream>
#include <filesystem>
#include <iostream>

namespace fs = std::filesystem;

// ----------------------------------------------------------------------------
// byte helpers (host may be little-endian; we read/write big-endian explicitly)
// ----------------------------------------------------------------------------
static inline uint32_t rd_be32(const uint8_t* p) {
    return (uint32_t(p[0]) << 24) | (uint32_t(p[1]) << 16) |
           (uint32_t(p[2]) << 8)  |  uint32_t(p[3]);
}
static inline void wr_be32(uint8_t* p, uint32_t v) {
    p[0] = uint8_t(v >> 24); p[1] = uint8_t(v >> 16);
    p[2] = uint8_t(v >> 8);  p[3] = uint8_t(v);
}

static std::vector<uint8_t> read_file(const fs::path& p) {
    std::ifstream f(p, std::ios::binary);
    if (!f) { std::cerr << "error: cannot open " << p << "\n"; return {}; }
    return std::vector<uint8_t>((std::istreambuf_iterator<char>(f)),
                                 std::istreambuf_iterator<char>());
}
static void write_file(const fs::path& p, const uint8_t* d, size_t n) {
    std::ofstream f(p, std::ios::binary);
    f.write(reinterpret_cast<const char*>(d), std::streamsize(n));
}

// ----------------------------------------------------------------------------
// Optional decompression front-end.
// The .rom files here are not compressed, but a real toolchain should be
// defensive: if a known container magic is found we decode it first.  Yaz0 is
// the canonical Nintendo run-length/LZ container and is fully implemented; any
// unrecognised input is returned unchanged.
// ----------------------------------------------------------------------------
static bool yaz0_decompress(const std::vector<uint8_t>& in, std::vector<uint8_t>& out) {
    if (in.size() < 16 || std::memcmp(in.data(), "Yaz0", 4) != 0) return false;
    uint32_t decoded = rd_be32(&in[4]);
    out.clear(); out.reserve(decoded);
    size_t src = 16;
    while (out.size() < decoded && src < in.size()) {
        uint8_t group = in[src++];
        for (int bit = 0; bit < 8 && out.size() < decoded; ++bit) {
            if (group & (0x80 >> bit)) {                 // literal
                if (src >= in.size()) break;
                out.push_back(in[src++]);
            } else {                                     // back-reference
                if (src + 1 >= in.size()) break;
                uint8_t b1 = in[src++], b2 = in[src++];
                uint32_t dist = (((b1 & 0x0F) << 8) | b2) + 1;
                uint32_t len  = (b1 >> 4);
                if (len == 0) { if (src >= in.size()) break; len = in[src++] + 0x12; }
                else            len += 2;
                if (dist > out.size()) return false;
                size_t from = out.size() - dist;
                for (uint32_t i = 0; i < len; ++i) out.push_back(out[from + i]);
            }
        }
    }
    return true;
}

// Returns possibly-decompressed data and reports which codec fired.
static std::vector<uint8_t> maybe_decompress(std::vector<uint8_t> data,
                                             std::string& codec) {
    std::vector<uint8_t> out;
    if (yaz0_decompress(data, out)) { codec = "Yaz0"; return out; }
    codec = "none (raw relocated image)";
    return data;
}

// ----------------------------------------------------------------------------
// Load-base detection.
// The confirmed base for this title is 0x40000000. Auto-detection makes the
// tool usable on sibling titles: for each aligned word we look at its top bits
// as a candidate base and keep the base that turns the most words into valid,
// 4-aligned, in-bounds pointers.
// ----------------------------------------------------------------------------
static uint32_t detect_base(const std::vector<uint8_t>& d) {
    const size_t n = d.size();
    std::map<uint32_t, uint32_t> hits;               // base -> pointer count
    auto score = [&](uint32_t base) {
        uint32_t c = 0;
        for (size_t o = 0; o + 4 <= n; o += 4) {
            uint32_t w = rd_be32(&d[o]);
            if (w >= base && w < base + n && ((w - base) & 3u) == 0) ++c;
        }
        return c;
    };
    // candidate bases: observed high halfwords + common console load bases.
    // Bases below 0x00100000 are excluded: base 0 is degenerate (every small
    // integer would masquerade as a pointer), and real load addresses are high.
    std::set<uint32_t> cands = {0x40000000u, 0x80000000u};
    for (size_t o = 0; o + 4 <= n; o += 4) {
        uint32_t w = rd_be32(&d[o]);
        if (w >= 0x00100000u) cands.insert(w & 0xFFFF0000u);
    }
    uint32_t best = 0x40000000u, bestc = score(0x40000000u);
    for (uint32_t b : cands) {
        uint32_t c = score(b);
        if (c > bestc) { bestc = c; best = b; }
    }
    return best;
}

// ----------------------------------------------------------------------------
// value classification for the human-readable layout dump
// ----------------------------------------------------------------------------
static bool looks_float(uint32_t w) {
    float f; std::memcpy(&f, &w, 4);
    if (w == 0) return true;                 // 0.0f
    if (!std::isfinite(f)) return false;
    float a = std::fabs(f);
    return a >= 1e-4f && a <= 1e9f;
}
static bool looks_tag(uint32_t w) {          // 0xTT0000LL, TT != 0, LL small
    return (w & 0x00FFFF00u) == 0 && (w >> 24) != 0;
}

// ----------------------------------------------------------------------------
// per-file unpack
// ----------------------------------------------------------------------------
struct Options {
    fs::path outdir = "unpacked";
    uint32_t base = 0x40000000; // confirmed load base for this title
    bool     base_set = false;  // true if user passed --base
    bool     auto_base = false; // true if user passed --auto
    uint32_t rebase = 0;
    int      max_dump = 48;
    bool     write_blocks = true;
    bool     quiet = false;
};

static void unpack_one(const fs::path& in_path, const Options& opt) {
    std::vector<uint8_t> raw = read_file(in_path);
    if (raw.empty()) return;

    std::string codec;
    std::vector<uint8_t> d = maybe_decompress(std::move(raw), codec);
    const size_t n = d.size();

    uint32_t base = opt.base;
    if (opt.base_set)      base = opt.base;          // user override wins
    else if (opt.auto_base) base = detect_base(d);   // opt-in detection

    // --- scan pointers -------------------------------------------------------
    std::vector<size_t> sites;          // offsets of pointer words
    std::set<uint32_t>  targets;        // pointer destinations (file-relative)
    for (size_t o = 0; o + 4 <= n; o += 4) {
        uint32_t w = rd_be32(&d[o]);
        if (w >= base && w < base + n) {
            sites.push_back(o);
            targets.insert(w - base);
        }
    }
    targets.insert(0);                  // the root always starts a block

    // --- output folder -------------------------------------------------------
    fs::path stem = in_path.stem();
    fs::path out  = opt.outdir / stem;
    fs::create_directories(out);

    // --- relocated copy ------------------------------------------------------
    std::vector<uint8_t> reloc = d;
    for (size_t o : sites) {
        uint32_t w = rd_be32(&d[o]);
        wr_be32(&reloc[o], (w - base) + opt.rebase);
    }
    write_file(out / (stem.string() + ".unpacked.bin"), reloc.data(), reloc.size());

    // --- block decomposition -------------------------------------------------
    std::vector<uint32_t> tv(targets.begin(), targets.end());
    std::sort(tv.begin(), tv.end());
    size_t nblocks = 0;
    {
        std::ofstream idx(out / "blocks_index.txt");
        idx << "# block  offset      size    (source: " << in_path.filename().string() << ")\n";
        if (opt.write_blocks) fs::create_directories(out / "blocks");
        for (size_t i = 0; i < tv.size(); ++i) {
            uint32_t start = tv[i];
            uint32_t end   = (i + 1 < tv.size()) ? tv[i + 1] : uint32_t(n);
            if (end <= start) continue;
            uint32_t sz = end - start;
            char name[64];
            std::snprintf(name, sizeof name, "blk%04zu_0x%06x.bin", nblocks, start);
            idx << name << "  0x" << std::hex << start << "  " << std::dec << sz << "\n";
            if (opt.write_blocks)
                write_file(out / "blocks" / name, reloc.data() + start, sz);
            ++nblocks;
        }
    }

    // --- string table --------------------------------------------------------
    size_t nstrings = 0;
    {
        std::ofstream sf(out / "strings.txt");
        sf << "# offset    string   (source: " << in_path.filename().string() << ")\n";
        size_t i = 0;
        while (i < n) {
            if (d[i] >= 0x20 && d[i] <= 0x7e) {
                size_t j = i;
                while (j < n && d[j] >= 0x20 && d[j] <= 0x7e) ++j;
                if (j - i >= 4) {
                    sf << "0x" << std::hex << i << std::dec << "\t";
                    sf.write(reinterpret_cast<const char*>(&d[i]), std::streamsize(j - i));
                    sf << "\n";
                    ++nstrings;
                }
                i = j;
            } else ++i;
        }
    }

    // --- relocation site table ----------------------------------------------
    {
        std::ofstream rf(out / "reloc.txt");
        rf << "# load_base=0x" << std::hex << base << std::dec
           << "  codec=" << codec << "  pointer_sites=" << sites.size() << "\n";
        rf << "# each line: file offset of a 32-bit word that holds a pointer\n";
        for (size_t o : sites) rf << "0x" << std::hex << o << "\n";
    }

    // --- best-effort structured layout dump ---------------------------------
    {
        std::ofstream lf(out / "layout.txt");
        lf << "PACK.rom structured dump\n";
        lf << "  source     : " << in_path.filename().string() << "\n";
        lf << "  size       : " << n << " bytes\n";
        lf << "  codec      : " << codec << "\n";
        lf << "  load base  : 0x" << std::hex << base << std::dec << "\n";
        lf << "  ptr sites  : " << sites.size() << "\n";
        lf << "  blocks     : " << nblocks << "\n";
        lf << "  strings    : " << nstrings << "\n";
        lf << "  legend     : PTR=pointer  FLT=float  TAG=type id  INT=integer  STR=text\n\n";

        for (size_t i = 0; i < tv.size(); ++i) {
            uint32_t start = tv[i];
            uint32_t end   = (i + 1 < tv.size()) ? tv[i + 1] : uint32_t(n);
            if (end <= start) continue;
            lf << "block @0x" << std::hex << start << "  size=" << std::dec
               << (end - start) << "\n";
            int shown = 0;
            for (uint32_t o = start; o + 4 <= end; o += 4) {
                if (shown >= opt.max_dump) {
                    lf << "    ... (" << ((end - o) / 4) << " more words)\n";
                    break;
                }
                uint32_t w = rd_be32(&d[o]);
                char line[96];
                if (w >= base && w < base + n) {
                    std::snprintf(line, sizeof line, "    +0x%04x  PTR ->0x%06x",
                                  o - start, w - base);
                } else if (looks_tag(w)) {
                    std::snprintf(line, sizeof line, "    +0x%04x  TAG 0x%02x (raw 0x%08x)",
                                  o - start, w >> 24, w);
                } else if (looks_float(w)) {
                    float f; std::memcpy(&f, &w, 4);
                    std::snprintf(line, sizeof line, "    +0x%04x  FLT %g", o - start, f);
                } else {
                    std::snprintf(line, sizeof line, "    +0x%04x  INT 0x%08x (%d)",
                                  o - start, w, int32_t(w));
                }
                lf << line << "\n";
                ++shown;
            }
            lf << "\n";
        }
    }

    if (!opt.quiet) {
        std::printf("  %-34s %8zu B  base=0x%08x  ptrs=%-6zu blocks=%-5zu strings=%-5zu [%s]\n",
                    in_path.filename().string().c_str(), n, base,
                    sites.size(), nblocks, nstrings, codec.c_str());
    }
}

// ----------------------------------------------------------------------------
int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr <<
          "packrom_unpack - unpack *_PACK.rom relocated resource images\n\n"
          "usage: " << argv[0] << " <file.rom | directory> [options]\n"
          "  -o <dir>       output directory            (default ./unpacked)\n"
          "  --base 0xADDR  override load base           (default 0x40000000)\n"
          "  --auto         auto-detect load base (for other titles)\n"
          "  --rebase 0xN   base written into output     (default 0)\n"
          "  --max-dump N   words per block in layout    (default 48)\n"
          "  --no-blocks    do not write per-block files\n"
          "  -q             quiet\n";
        return 1;
    }

    Options opt;
    fs::path input;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        auto need = [&](const char* nm) -> std::string {
            if (i + 1 >= argc) { std::cerr << "missing value for " << nm << "\n"; std::exit(1); }
            return argv[++i];
        };
        if      (a == "-o")          opt.outdir = need("-o");
        else if (a == "--base")    { opt.base = std::stoul(need("--base"), nullptr, 0); opt.base_set = true; }
        else if (a == "--auto")      opt.auto_base = true;
        else if (a == "--rebase")    opt.rebase = std::stoul(need("--rebase"), nullptr, 0);
        else if (a == "--max-dump")  opt.max_dump = std::stoi(need("--max-dump"));
        else if (a == "--no-blocks") opt.write_blocks = false;
        else if (a == "-q")          opt.quiet = true;
        else if (!a.empty() && a[0] == '-') { std::cerr << "unknown option " << a << "\n"; return 1; }
        else                         input = a;
    }
    if (input.empty()) { std::cerr << "no input given\n"; return 1; }

    fs::create_directories(opt.outdir);

    std::vector<fs::path> jobs;
    if (fs::is_directory(input)) {
        for (auto& e : fs::directory_iterator(input)) {
            std::string ext = e.path().extension().string();
            std::transform(ext.begin(), ext.end(), ext.begin(), ::tolower);
            if (ext == ".rom") jobs.push_back(e.path());
        }
        std::sort(jobs.begin(), jobs.end());
    } else {
        jobs.push_back(input);
    }
    if (jobs.empty()) { std::cerr << "no .rom files found\n"; return 1; }

    std::printf("Unpacking %zu file(s) -> %s\n",
                jobs.size(), opt.outdir.string().c_str());
    for (auto& j : jobs) unpack_one(j, opt);
    std::printf("Done. %zu file(s) written under %s\n",
                jobs.size(), opt.outdir.string().c_str());
    return 0;
}
