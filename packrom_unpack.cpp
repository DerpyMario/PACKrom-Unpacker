// ============================================================================
//  packrom_unpack.cpp   (v2 - GameCube resource extractor)
//
//  Unpacks  *_PACK.rom  serialized resource images from a big-endian GameCube
//  title (Konami "Disney Sports"-family). Reverse-engineered from the data.
//
//  WHAT A .rom IS
//  -------------
//  A relocated RAM snapshot: big-endian 32-bit words, internal pointers stored
//  as absolute addresses in a virtual space with load base 0x40000000, holding
//  a dense graph of small allocations. Inside that graph the game serialized
//  actual GameCube assets:
//
//    * GX TEXTURES  - descriptor {w,h,format,data_ptr,...,pal_fmt,pal_ptr}
//                     with GX-tiled pixel data (I4 I8 IA4 IA8 RGB565 RGB5A3
//                     RGBA8 C4 C8 C14X2 CMPR). Verified by decoding to images.
//    * GX MODELS    - display lists (draw opcodes 0x80..0xB8) over float vertex
//                     arrays. Verified (e.g. DEBUG_MODEL is a [-5,+5] cube).
//    * game data    - property lists, strings, quantized animation curves.
//
//  WHAT THIS TOOL PRODUCES  (per input .rom, in <out>/<name>/)
//  --------------------------------------------------------
//    textures/*.png            every GX texture, decoded to RGBA PNG
//    textures/index.txt        offset / format / size of each texture
//    gx_models.txt             display-list draw ops found (primitive/verts)
//    <name>.unpacked.bin       image with pointers rebased to file offsets
//    blocks/                   image split into its allocation blocks
//    strings.txt               printable ASCII (names, sound ids, ...)
//    layout.txt                best-effort structured dump of the graph
//    reloc.txt                 pointer-site table (for re-packing)
//
//  BUILD   g++ -O2 -std=c++17 -o packrom_unpack packrom_unpack.cpp
//  USAGE   ./packrom_unpack <file.rom | dir> [-o out] [--base 0xADDR]
//                           [--auto] [--rebase 0xN] [--max-dump N]
//                           [--no-blocks] [--no-textures] [--allow-npot] [-q]
// ============================================================================

#include <cstdint>
#include <cstring>
#include <cmath>
#include <cstdio>
#include <string>
#include <vector>
#include <set>
#include <array>
#include <map>
#include <algorithm>
#include <fstream>
#include <filesystem>
#include <iostream>

namespace fs = std::filesystem;

// --------------------------------------------------------------------------
// byte helpers (host may be little-endian; big-endian handled explicitly)
// --------------------------------------------------------------------------
static inline uint16_t rd_be16(const uint8_t* p){ return (uint16_t(p[0])<<8)|p[1]; }
static inline uint32_t rd_be32(const uint8_t* p){
    return (uint32_t(p[0])<<24)|(uint32_t(p[1])<<16)|(uint32_t(p[2])<<8)|p[3];
}
static inline void wr_be32(uint8_t* p, uint32_t v){
    p[0]=uint8_t(v>>24); p[1]=uint8_t(v>>16); p[2]=uint8_t(v>>8); p[3]=uint8_t(v);
}
static std::vector<uint8_t> read_file(const fs::path& p){
    std::ifstream f(p,std::ios::binary);
    if(!f){ std::cerr<<"error: cannot open "<<p<<"\n"; return {}; }
    return std::vector<uint8_t>((std::istreambuf_iterator<char>(f)),
                                 std::istreambuf_iterator<char>());
}
static void write_file(const fs::path& p, const uint8_t* d, size_t n){
    std::ofstream f(p,std::ios::binary); f.write((const char*)d,(std::streamsize)n);
}

// ==========================================================================
//  Minimal PNG writer (no libpng/zlib): stored DEFLATE blocks + zlib wrapper.
// ==========================================================================
static uint32_t crc32_buf(const uint8_t* d, size_t n, uint32_t crc=0xFFFFFFFFu){
    static uint32_t T[256]; static bool init=false;
    if(!init){ for(uint32_t i=0;i<256;i++){ uint32_t c=i;
        for(int k=0;k<8;k++) c = (c&1)?0xEDB88320u^(c>>1):c>>1; T[i]=c; } init=true; }
    for(size_t i=0;i<n;i++) crc = T[(crc^d[i])&0xFF]^(crc>>8);
    return crc;
}
static uint32_t adler32_buf(const uint8_t* d, size_t n){
    uint32_t a=1,b=0; for(size_t i=0;i<n;i++){ a=(a+d[i])%65521; b=(b+a)%65521; }
    return (b<<16)|a;
}
static void png_chunk(std::vector<uint8_t>& out, const char* type, const std::vector<uint8_t>& data){
    uint8_t len[4]; wr_be32(len,(uint32_t)data.size());
    out.insert(out.end(),len,len+4);
    size_t s=out.size();
    out.insert(out.end(),type,type+4);
    out.insert(out.end(),data.begin(),data.end());
    uint32_t crc = crc32_buf(out.data()+s, out.size()-s) ^ 0xFFFFFFFFu;
    uint8_t c[4]; wr_be32(c,crc); out.insert(out.end(),c,c+4);
}
// rgba: w*h*4 bytes; writes a valid 8-bit RGBA PNG
static void write_png(const fs::path& path, const std::vector<uint8_t>& rgba, int w, int h){
    // build raw scanlines with filter byte 0 per row
    std::vector<uint8_t> raw; raw.reserve((size_t)h*(w*4+1));
    for(int y=0;y<h;y++){ raw.push_back(0);
        raw.insert(raw.end(), rgba.begin()+(size_t)y*w*4, rgba.begin()+(size_t)(y+1)*w*4); }
    // zlib stream: header + stored deflate blocks + adler32
    std::vector<uint8_t> z; z.push_back(0x78); z.push_back(0x01);
    size_t off=0;
    while(off<raw.size()){
        size_t n=std::min<size_t>(65535, raw.size()-off);
        z.push_back(off+n>=raw.size()?1:0);           // BFINAL, BTYPE=00 (stored)
        z.push_back(n&0xFF); z.push_back((n>>8)&0xFF); // LEN LE
        uint16_t nl=~(uint16_t)n; z.push_back(nl&0xFF); z.push_back((nl>>8)&0xFF);
        z.insert(z.end(), raw.begin()+off, raw.begin()+off+n); off+=n;
    }
    uint32_t ad=adler32_buf(raw.data(),raw.size());
    uint8_t a[4]; wr_be32(a,ad); z.insert(z.end(),a,a+4);

    std::vector<uint8_t> out={0x89,'P','N','G','\r','\n',0x1A,'\n'};
    std::vector<uint8_t> ihdr(13,0);
    wr_be32(&ihdr[0],(uint32_t)w); wr_be32(&ihdr[4],(uint32_t)h);
    ihdr[8]=8; ihdr[9]=6; /*RGBA*/ ihdr[10]=0; ihdr[11]=0; ihdr[12]=0;
    png_chunk(out,"IHDR",ihdr);
    png_chunk(out,"IDAT",z);
    png_chunk(out,"IEND",{});
    write_file(path,out.data(),out.size());
}

// ==========================================================================
//  GX texture decoding
// ==========================================================================
struct GXFmt { const char* name; int bpp; int tw; int th; };
static bool gx_fmt(uint32_t f, GXFmt& o){
    switch(f){
        case 0:  o={"I4",    4,8,8}; return true;
        case 1:  o={"I8",    8,8,4}; return true;
        case 2:  o={"IA4",   8,8,4}; return true;
        case 3:  o={"IA8",  16,4,4}; return true;
        case 4:  o={"RGB565",16,4,4}; return true;
        case 5:  o={"RGB5A3",16,4,4}; return true;
        case 6:  o={"RGBA8", 32,4,4}; return true;
        case 8:  o={"C4",    4,8,8}; return true;
        case 9:  o={"C8",    8,8,4}; return true;
        case 10: o={"C14X2",16,4,4}; return true;
        case 14: o={"CMPR",  4,8,8}; return true;
        default: return false;
    }
}
static inline int c4to8(int v){ return (v<<4)|v; }
static inline int c3to8(int v){ return (v<<5)|(v<<2)|(v>>1); }
static inline int c5to8(int v){ return (v<<3)|(v>>2); }
static inline int c6to8(int v){ return (v<<2)|(v>>4); }

static void put(std::vector<uint8_t>& img,int w,int h,int x,int y,int r,int g,int b,int a){
    if(x<0||y<0||x>=w||y>=h) return;
    size_t o=((size_t)y*w+x)*4; img[o]=r; img[o+1]=g; img[o+2]=b; img[o+3]=a;
}
static void pal_color(uint32_t palfmt, uint16_t v, int& r,int& g,int& b,int& a){
    switch(palfmt){
        case 0: /*IA8*/ { int A=v>>8, I=v&0xFF; r=g=b=I; a=A; } break;
        case 1: /*RGB565*/ { r=c5to8((v>>11)&0x1f); g=c6to8((v>>5)&0x3f); b=c5to8(v&0x1f); a=255; } break;
        default:/*RGB5A3*/
            if(v&0x8000){ r=c5to8((v>>10)&0x1f); g=c5to8((v>>5)&0x1f); b=c5to8(v&0x1f); a=255; }
            else        { a=c3to8((v>>12)&0x7); r=c4to8((v>>8)&0xf); g=c4to8((v>>4)&0xf); b=c4to8(v&0xf); }
    }
}
// Decode one texture into RGBA. Returns false if data would run past end.
static bool gx_decode(const std::vector<uint8_t>& d, size_t off, int w, int h,
                      uint32_t fmt, uint32_t palfmt, size_t paloff, bool have_pal,
                      std::vector<uint8_t>& img){
    GXFmt gf; if(!gx_fmt(fmt,gf)) return false;
    size_t need = (size_t)w*h*gf.bpp/8;
    if(off+need>d.size()) return false;
    img.assign((size_t)w*h*4,0);
    const uint8_t* p=d.data()+off; size_t rem=d.size()-off;
    auto avail=[&](size_t n){ return n<=rem; };

    if(fmt==14){ // CMPR: 8x8 tile = four 4x4 DXT1 blocks (TL,TR,BL,BR)
        size_t i=0;
        for(int ty=0;ty<h;ty+=8) for(int tx=0;tx<w;tx+=8)
          for(int sy=0;sy<8;sy+=4) for(int sx=0;sx<8;sx+=4){
            if(!avail(i+8)) return false;
            uint16_t c0=rd_be16(p+i), c1=rd_be16(p+i+2);
            uint32_t bits=rd_be32(p+i+4); i+=8;
            int col[4][4];
            col[0][0]=c5to8((c0>>11)&0x1f); col[0][1]=c6to8((c0>>5)&0x3f); col[0][2]=c5to8(c0&0x1f); col[0][3]=255;
            col[1][0]=c5to8((c1>>11)&0x1f); col[1][1]=c6to8((c1>>5)&0x3f); col[1][2]=c5to8(c1&0x1f); col[1][3]=255;
            if(c0>c1){
                for(int k=0;k<3;k++){ col[2][k]=(2*col[0][k]+col[1][k])/3; col[3][k]=(col[0][k]+2*col[1][k])/3; }
                col[2][3]=col[3][3]=255;
            } else {
                for(int k=0;k<3;k++){ col[2][k]=(col[0][k]+col[1][k])/2; col[3][k]=0; }
                col[2][3]=255; col[3][3]=0;
            }
            for(int yy=0;yy<4;yy++) for(int xx=0;xx<4;xx++){
                int idx=(bits>>((15-(yy*4+xx))*2))&0x3;
                put(img,w,h,tx+sx+xx,ty+sy+yy,col[idx][0],col[idx][1],col[idx][2],col[idx][3]);
            }
        }
        return true;
    }

    // tiled loop for the non-CMPR formats
    size_t bit=0; // for I4/C4 nibble addressing
    size_t bytepos=0;
    for(int ty=0;ty<h;ty+=gf.th) for(int tx=0;tx<w;tx+=gf.tw){
        if(fmt==6){ // RGBA8: 4x4 tile, 64 bytes = 16 (A,R) then 16 (G,B)
            if(!avail(bytepos+64)) return false;
            const uint8_t* t=p+bytepos; bytepos+=64;
            for(int yy=0;yy<4;yy++) for(int xx=0;xx<4;xx++){
                int k=yy*4+xx; int A=t[k*2], R=t[k*2+1], G=t[32+k*2], B=t[32+k*2+1];
                put(img,w,h,tx+xx,ty+yy,R,G,B,A);
            }
            continue;
        }
        for(int yy=0;yy<gf.th;yy++) for(int xx=0;xx<gf.tw;xx++){
            int r=0,g=0,b=0,a=255;
            if(fmt==0){ // I4
                size_t bi=bytepos+ (bit>>1); if(!avail(bi+1)) return false;
                int v=(bit&1)?(p[bi]&0xf):(p[bi]>>4); int I=c4to8(v); r=g=b=I; a=255; bit++;
            } else if(fmt==8){ // C4 (palette)
                size_t bi=bytepos+ (bit>>1); if(!avail(bi+1)) return false;
                int idx=(bit&1)?(p[bi]&0xf):(p[bi]>>4); bit++;
                uint16_t pv=have_pal&&paloff+idx*2+1<d.size()? rd_be16(d.data()+paloff+idx*2):0;
                pal_color(palfmt,pv,r,g,b,a);
            } else if(fmt==1){ // I8
                if(!avail(bytepos+1)) return false; int I=p[bytepos++]; r=g=b=I; a=255; goto placed;
            } else if(fmt==2){ // IA4
                if(!avail(bytepos+1)) return false; int v=p[bytepos++]; a=c4to8((v>>4)&0xf); int I=c4to8(v&0xf); r=g=b=I; goto placed;
            } else if(fmt==9){ // C8 (palette)
                if(!avail(bytepos+1)) return false; int idx=p[bytepos++];
                uint16_t pv=have_pal&&paloff+idx*2+1<d.size()? rd_be16(d.data()+paloff+idx*2):0;
                pal_color(palfmt,pv,r,g,b,a); goto placed;
            } else if(fmt==3){ // IA8
                if(!avail(bytepos+2)) return false; uint16_t v=rd_be16(p+bytepos); bytepos+=2; a=v>>8; int I=v&0xFF; r=g=b=I; goto placed;
            } else if(fmt==4){ // RGB565
                if(!avail(bytepos+2)) return false; uint16_t v=rd_be16(p+bytepos); bytepos+=2; r=c5to8((v>>11)&0x1f); g=c6to8((v>>5)&0x3f); b=c5to8(v&0x1f); a=255; goto placed;
            } else if(fmt==5){ // RGB5A3
                if(!avail(bytepos+2)) return false; uint16_t v=rd_be16(p+bytepos); bytepos+=2; pal_color(2,v,r,g,b,a); goto placed;
            } else if(fmt==10){ // C14X2 (palette, 14-bit index)
                if(!avail(bytepos+2)) return false; uint16_t v=rd_be16(p+bytepos)&0x3FFF; bytepos+=2;
                uint16_t pv=have_pal&&paloff+v*2+1<d.size()? rd_be16(d.data()+paloff+v*2):0;
                pal_color(palfmt,pv,r,g,b,a); goto placed;
            }
            placed:
            put(img,w,h,tx+xx,ty+yy,r,g,b,a);
        }
        if(fmt==0||fmt==8){ // 4bpp tiles consumed 'bit' nibbles; advance bytepos to tile end
            bytepos += (gf.tw*gf.th)/2; bit=0;
        }
    }
    return true;
}

// ==========================================================================
//  Optional decompression front-end (Yaz0). Raw input passes through.
// ==========================================================================
static bool yaz0(const std::vector<uint8_t>& in, std::vector<uint8_t>& out){
    if(in.size()<16||std::memcmp(in.data(),"Yaz0",4)!=0) return false;
    uint32_t dec=rd_be32(&in[4]); out.clear(); out.reserve(dec); size_t s=16;
    while(out.size()<dec&&s<in.size()){
        uint8_t grp=in[s++];
        for(int bt=0;bt<8&&out.size()<dec;bt++){
            if(grp&(0x80>>bt)){ if(s>=in.size())break; out.push_back(in[s++]); }
            else{ if(s+1>=in.size())break; uint8_t b1=in[s++],b2=in[s++];
                uint32_t dist=(((b1&0xF)<<8)|b2)+1,len=b1>>4;
                if(len==0){ if(s>=in.size())break; len=in[s++]+0x12; } else len+=2;
                if(dist>out.size())return false; size_t f=out.size()-dist;
                for(uint32_t i=0;i<len;i++) out.push_back(out[f+i]); }
        }
    }
    return true;
}
static std::vector<uint8_t> maybe_decompress(std::vector<uint8_t> data, std::string& codec){
    std::vector<uint8_t> o; if(yaz0(data,o)){ codec="Yaz0"; return o; }
    codec="none (raw relocated image)"; return data;
}

// ==========================================================================
//  Load-base detection (opt-in; default is the confirmed 0x40000000)
// ==========================================================================
static uint32_t detect_base(const std::vector<uint8_t>& d){
    const size_t n=d.size();
    auto score=[&](uint32_t base){ uint32_t c=0;
        for(size_t o=0;o+4<=n;o+=4){ uint32_t w=rd_be32(&d[o]);
            if(w>=base&&w<base+n&&((w-base)&3u)==0) ++c; } return c; };
    std::set<uint32_t> cands={0x40000000u,0x80000000u};
    for(size_t o=0;o+4<=n;o+=4){ uint32_t w=rd_be32(&d[o]); if(w>=0x00100000u) cands.insert(w&0xFFFF0000u); }
    uint32_t best=0x40000000u,bc=score(best);
    for(uint32_t b:cands){ uint32_t c=score(b); if(c>bc){ bc=c; best=b; } }
    return best;
}

// ==========================================================================
//  GX model extraction -> Wavefront OBJ
//
//  A mesh descriptor is  [dl_size:u32][dl_ptr][pos_ptr][nrm_ptr]...  where the
//  display list is a stream of GX primitives and the vertex is a run of indices
//  (optionally led by a 1-byte matrix index). Per-mesh we solve for the vertex
//  stride (the value that walks every primitive cleanly to dl_size) and for the
//  position-index field (the offset/size whose values stay < the position count
//  and yield the most non-degenerate triangles). Verified against DEBUG_MODEL
//  (a ground quad) and character models.
// ==========================================================================
static inline bool is_prim(uint8_t p){
    return p==0x80||p==0x90||p==0x98||p==0xA0||p==0xA8||p==0xB0||p==0xB8;
}
struct Prim { uint8_t op; std::vector<size_t> voff; };

static bool parse_prims(const std::vector<uint8_t>& d, size_t dl, uint32_t ds,
                        int stride, std::vector<Prim>& prims, size_t& endo){
    size_t o=dl, end=dl+ds; prims.clear();
    while(o<end){
        uint8_t op=d[o];
        if(op==0x00){ for(size_t i=o;i<end;i++) if(d[i]){ endo=o; return false; } endo=o; return true; }
        uint8_t p=op&0xF8;
        if(!is_prim(p)){ endo=o; return false; }
        if(o+3>end){ endo=o; return false; }
        uint16_t cnt=rd_be16(&d[o+1]); o+=3;
        if(cnt<1 || o+(size_t)cnt*stride>end){ endo=o; return false; }
        Prim pr; pr.op=p; pr.voff.reserve(cnt);
        for(int k=0;k<cnt;k++) pr.voff.push_back(o+(size_t)k*stride);
        o+=(size_t)cnt*stride; prims.push_back(std::move(pr));
    }
    endo=o; return true;
}
// choose stride minimising leftover bytes while walking every primitive to dl_size
static int pick_stride(const std::vector<uint8_t>& d, size_t dl, uint32_t ds,
                       std::vector<Prim>& out){
    int bestS=-1; long bestResid=-1, bestPrims=-1, bestVerts=-1;
    for(int S=3;S<=24;S++){
        std::vector<Prim> pr; size_t endo;
        if(!parse_prims(d,dl,ds,S,pr,endo)) continue;
        long resid=(long)(dl+ds)-(long)endo; if(resid<0||resid>S) continue;
        long np=(long)pr.size(); long nv=0; for(auto&p:pr) nv+=(long)p.voff.size();
        if(np<1) continue;
        bool better = bestS<0 || resid<bestResid ||
                     (resid==bestResid && (np>bestPrims ||
                     (np==bestPrims && nv>bestVerts)));
        if(better){ bestS=S; bestResid=resid; bestPrims=np; bestVerts=nv; out=pr; }
    }
    return bestS;
}
static inline uint32_t rd_idx(const std::vector<uint8_t>& d,size_t off,int sz){
    return sz==1? d[off] : rd_be16(&d[off]);
}
// choose (offset,size) of the position index within the vertex
static bool pick_index(const std::vector<uint8_t>& d, const std::vector<Prim>& prims,
                       uint32_t pos_count, int stride, int& outO, int& outSz){
    long bestGood=-1, bestDistinct=-1; int bestO=-1,bestSz=0;
    for(int sz=2;sz>=1;sz--) for(int O=0;O+sz<=stride;O++){
        uint32_t mn=0xffffffffu,mx=0; std::set<uint32_t> distinct; bool bad=false;
        for(auto&pr:prims){ for(size_t vo:pr.voff){ uint32_t v=rd_idx(d,vo+O,sz);
            if(v>=pos_count){ bad=true; break; } mn=std::min(mn,v); mx=std::max(mx,v); distinct.insert(v);} if(bad)break; }
        if(bad||mx==mn) continue;                      // out of range or constant
        long good=0;
        for(auto&pr:prims){ size_t c=pr.voff.size(); std::vector<uint32_t> id(c);
            for(size_t k=0;k<c;k++) id[k]=rd_idx(d,pr.voff[k]+O,sz);
            if(pr.op==0x98){ for(size_t k=0;k+2<c;k++){ uint32_t a=id[k],b=id[k+1],cc=id[k+2];
                    if(a!=b&&b!=cc&&a!=cc) good++; } }
            else if(pr.op==0xA0){ for(size_t k=1;k+1<c;k++){ if(id[0]!=id[k]&&id[k]!=id[k+1]&&id[0]!=id[k+1]) good++; } }
            else if(pr.op==0x90){ for(size_t k=0;k+2<c;k+=3){ if(id[k]!=id[k+1]&&id[k+1]!=id[k+2]&&id[k]!=id[k+2]) good++; } }
            else if(pr.op==0x80){ good+=2*(long)(c/4); } }
        long dcount=(long)distinct.size();
        if(good>bestGood || (good==bestGood && dcount>bestDistinct)){
            bestGood=good; bestDistinct=dcount; bestO=O; bestSz=sz; }
    }
    if(bestO<0) return false; outO=bestO; outSz=bestSz; return true;
}
static void emit_tris(uint8_t op, const std::vector<uint32_t>& g,
                      std::vector<std::array<uint32_t,3>>& faces){
    size_t c=g.size();
    if(op==0x98){ for(size_t k=0;k+2<c;k++){ uint32_t a,b,cc;
        if(k%2==0){ a=g[k]; b=g[k+1]; cc=g[k+2]; } else { a=g[k+1]; b=g[k]; cc=g[k+2]; }
        if(a!=b&&b!=cc&&a!=cc) faces.push_back({a,b,cc}); } }
    else if(op==0xA0){ for(size_t k=1;k+1<c;k++) if(g[0]!=g[k]&&g[k]!=g[k+1]&&g[0]!=g[k+1]) faces.push_back({g[0],g[k],g[k+1]}); }
    else if(op==0x90){ for(size_t k=0;k+2<c;k+=3) if(g[k]!=g[k+1]&&g[k+1]!=g[k+2]&&g[k]!=g[k+2]) faces.push_back({g[k],g[k+1],g[k+2]}); }
    else if(op==0x80){ for(size_t k=0;k+3<c;k+=4){ faces.push_back({g[k],g[k+1],g[k+2]}); faces.push_back({g[k],g[k+2],g[k+3]}); } }
}
// A face corner references position/texcoord/normal by index (0 = absent).
struct Corner { uint32_t p, t, n; };
static void emit_tris3(uint8_t op, const std::vector<Corner>& g,
                       std::vector<std::array<Corner,3>>& faces){
    size_t c=g.size();
    auto ok=[&](const Corner&a,const Corner&b,const Corner&cc){ return a.p!=b.p&&b.p!=cc.p&&a.p!=cc.p; };
    if(op==0x98){ for(size_t k=0;k+2<c;k++){ const Corner&a=(k%2==0)?g[k]:g[k+1];
        const Corner&b=(k%2==0)?g[k+1]:g[k]; const Corner&cc=g[k+2];
        if(ok(a,b,cc)) faces.push_back({a,b,cc}); } }
    else if(op==0xA0){ for(size_t k=1;k+1<c;k++) if(ok(g[0],g[k],g[k+1])) faces.push_back({g[0],g[k],g[k+1]}); }
    else if(op==0x90){ for(size_t k=0;k+2<c;k+=3) if(ok(g[k],g[k+1],g[k+2])) faces.push_back({g[k],g[k+1],g[k+2]}); }
    else if(op==0x80){ for(size_t k=0;k+3<c;k+=4){ faces.push_back({g[k],g[k+1],g[k+2]}); faces.push_back({g[k],g[k+2],g[k+3]}); } }
}
static inline float rd_f32(const std::vector<uint8_t>& d,size_t o){ uint32_t w=rd_be32(&d[o]); float f; std::memcpy(&f,&w,4); return std::isfinite(f)&&std::fabs(f)<1e6f? f:0.f; }

// Scan the whole image for mesh descriptors and write one combined OBJ (+MTL).
// Uses the GX attribute order (Table 1): matrix indices (u8) precede POS, NRM,
// CLR, TEX0 (index16). Positions/normals are F32 XYZ; texcoords F32 ST.
static void export_obj(const std::vector<uint8_t>& d, uint32_t base, const fs::path& path,
                       const fs::path& mtlname, const std::string& tex_material,
                       size_t& outV, size_t& outF, size_t& outM){
    const size_t n=d.size();
    std::vector<std::array<float,3>> P, N;
    std::vector<std::array<float,2>> T;
    std::vector<std::array<Corner,3>> faces;
    std::vector<std::pair<size_t,size_t>> groups;   // (face_start, desc_off)
    size_t nmesh=0;
    for(size_t o=0;o+24<=n;o+=4){
        uint32_t ds=rd_be32(&d[o]), dlp=rd_be32(&d[o+4]), posp=rd_be32(&d[o+8]),
                 nrmp=rd_be32(&d[o+12]), clrp=rd_be32(&d[o+16]), texp=rd_be32(&d[o+20]);
        if(ds<4||ds>0x200000) continue;
        if(!(dlp>=base&&dlp<base+n&&posp>=base&&posp<base+n)) continue;
        size_t dl=dlp-base, pos=posp-base;
        if(dl+ds>n||!is_prim(d[dl]&0xF8)||d[dl]==0) continue;
        if(!(nrmp>=base&&nrmp<base+n&&(nrmp-base)>pos)) continue;
        size_t pos_count=((nrmp-base)-pos)/12;
        if(pos_count<3||pos_count>100000) continue;
        for(int i=0;i<3;i++) for(int c=0;c<3;c++){ uint32_t w=rd_be32(&d[pos+i*12+c*4]);
            float f; std::memcpy(&f,&w,4); if(!std::isfinite(f)||std::fabs(f)>1e6f){ pos_count=0; } }
        if(pos_count<3) continue;
        std::vector<Prim> prims; int stride=pick_stride(d,dl,ds,prims);
        if(stride<0||prims.empty()) continue;
        int O,sz; if(!pick_index(d,prims,(uint32_t)pos_count,stride,O,sz)) continue;
        // GX order: matrix bytes = O ; POS@O, then NRM,CLR,TEX each +sz if present
        bool hasN=(nrmp>=base&&nrmp<base+n);
        bool hasC=(clrp>=base&&clrp<base+n);
        bool hasT=(texp>=base&&texp<base+n);
        int offP=O, cur=O+sz, offN=-1, offC=-1, offT=-1;
        if(hasN){ offN=cur; cur+=sz; } if(hasC){ offC=cur; cur+=sz; } if(hasT){ offT=cur; cur+=sz; }
        if(cur>stride){ hasT=false; offT=-1; if(cur-sz>stride){ hasN=false; offN=-1; } } // fall back
        size_t nrm=hasN?nrmp-base:0, tex=hasT?texp-base:0;
        uint32_t SKIP=(sz==1?0xFF:0xFFFF);
        // gather ranges + validate
        uint32_t maxP=0,maxN2=0,maxT2=0; bool bad=false;
        for(auto&pr:prims) for(size_t vo:pr.voff){ uint32_t p=rd_idx(d,vo+offP,sz);
            if(p==SKIP) continue; if(p>=pos_count){ bad=true; } maxP=std::max(maxP,p);
            if(hasN){ uint32_t v=rd_idx(d,vo+offN,sz); if(v!=SKIP) maxN2=std::max(maxN2,v); }
            if(hasT){ uint32_t v=rd_idx(d,vo+offT,sz); if(v!=SKIP) maxT2=std::max(maxT2,v); } }
        if(bad) continue;
        // normals must fit their array; texcoords must fit theirs; else drop that attr
        if(hasN && nrm+(size_t)(maxN2+1)*12>n) { hasN=false; }
        if(hasT && tex+(size_t)(maxT2+1)*8>n) { hasT=false; }
        groups.push_back({faces.size(),o});
        uint32_t vb=(uint32_t)P.size(), nb=(uint32_t)N.size(), tb=(uint32_t)T.size();
        for(uint32_t i=0;i<=maxP;i++) P.push_back({rd_f32(d,pos+i*12),rd_f32(d,pos+i*12+4),rd_f32(d,pos+i*12+8)});
        if(hasN) for(uint32_t i=0;i<=maxN2;i++) N.push_back({rd_f32(d,nrm+i*12),rd_f32(d,nrm+i*12+4),rd_f32(d,nrm+i*12+8)});
        if(hasT) for(uint32_t i=0;i<=maxT2;i++){ float u=rd_f32(d,tex+i*8), v=rd_f32(d,tex+i*8+4); T.push_back({u,1.f-v}); }
        for(auto&pr:prims){ std::vector<Corner> g; g.reserve(pr.voff.size()); bool brk=false;
            for(size_t vo:pr.voff){ uint32_t p=rd_idx(d,vo+offP,sz);
                if(p==SKIP){ // strip break: flush current run
                    if(g.size()>=3) emit_tris3(pr.op,g,faces); g.clear(); continue; }
                Corner c; c.p=vb+p+1;
                c.n=hasN? nb+(rd_idx(d,vo+offN,sz)%(maxN2+1))+1 : 0;
                c.t=hasT? tb+(rd_idx(d,vo+offT,sz)%(maxT2+1))+1 : 0;
                g.push_back(c); }
            if(g.size()>=3) emit_tris3(pr.op,g,faces); }
        ++nmesh;
    }
    std::ofstream f(path);
    f<<"# extracted by packrom_unpack from a GameCube GX resource image\n";
    f<<"# "<<P.size()<<" positions, "<<T.size()<<" texcoords, "<<N.size()<<" normals, "
     <<faces.size()<<" faces, "<<nmesh<<" meshes\n";
    if(!tex_material.empty()) f<<"mtllib "<<mtlname.filename().string()<<"\n";
    for(auto&v:P){ char b[64]; std::snprintf(b,sizeof b,"v %.5f %.5f %.5f\n",v[0],v[1],v[2]); f<<b; }
    for(auto&t:T){ char b[48]; std::snprintf(b,sizeof b,"vt %.5f %.5f\n",t[0],t[1]); f<<b; }
    for(auto&v:N){ char b[64]; std::snprintf(b,sizeof b,"vn %.5f %.5f %.5f\n",v[0],v[1],v[2]); f<<b; }
    if(!tex_material.empty()) f<<"usemtl "<<tex_material<<"\n";
    size_t gi=0;
    for(size_t i=0;i<faces.size();i++){
        while(gi<groups.size()&&groups[gi].first==i){ f<<"g mesh_"<<gi<<"_0x"<<std::hex<<groups[gi].second<<std::dec<<"\n"; ++gi; }
        f<<"f";
        for(int k=0;k<3;k++){ const Corner&c=faces[i][k]; f<<" "<<c.p;
            if(c.t||c.n){ f<<"/"; if(c.t)f<<c.t; f<<"/"; if(c.n)f<<c.n; } }
        f<<"\n";
    }
    outV=P.size(); outF=faces.size(); outM=nmesh;
}

// classification for the layout dump
static bool looks_float(uint32_t w){ float f; std::memcpy(&f,&w,4);
    if(w==0) return true; if(!std::isfinite(f)) return false;
    float a=std::fabs(f); return a>=1e-4f&&a<=1e9f; }
static bool looks_tag(uint32_t w){ return (w&0x00FFFF00u)==0&&(w>>24)!=0; }

// ==========================================================================
struct Options {
    fs::path outdir="unpacked";
    uint32_t base=0x40000000; bool base_set=false, auto_base=false;
    uint32_t rebase=0; int max_dump=48;
    bool write_blocks=true, write_textures=true, write_obj=true, allow_npot=false, quiet=false;
};
static bool is_pow2(uint32_t x){ return x&&((x&(x-1))==0); }

// ==========================================================================
//  per-file unpack
// ==========================================================================
static void unpack_one(const fs::path& in_path, const Options& opt){
    std::vector<uint8_t> rawf=read_file(in_path); if(rawf.empty()) return;
    std::string codec; std::vector<uint8_t> d=maybe_decompress(std::move(rawf),codec);
    const size_t n=d.size();
    uint32_t base=opt.base;
    if(opt.base_set) base=opt.base; else if(opt.auto_base) base=detect_base(d);

    // pointer scan
    std::vector<size_t> sites; std::set<uint32_t> targets;
    for(size_t o=0;o+4<=n;o+=4){ uint32_t w=rd_be32(&d[o]);
        if(w>=base&&w<base+n){ sites.push_back(o); targets.insert(w-base); } }
    targets.insert(0);

    fs::path stem=in_path.stem(); fs::path out=opt.outdir/stem;
    fs::create_directories(out);

    // relocated copy
    std::vector<uint8_t> reloc=d;
    for(size_t o:sites){ uint32_t w=rd_be32(&d[o]); wr_be32(&reloc[o],(w-base)+opt.rebase); }
    write_file(out/(stem.string()+".unpacked.bin"),reloc.data(),reloc.size());

    // blocks
    std::vector<uint32_t> tv(targets.begin(),targets.end()); std::sort(tv.begin(),tv.end());
    size_t nblocks=0;
    { std::ofstream idx(out/"blocks_index.txt");
      idx<<"# block  offset      size    (source: "<<in_path.filename().string()<<")\n";
      if(opt.write_blocks) fs::create_directories(out/"blocks");
      for(size_t i=0;i<tv.size();++i){ uint32_t st=tv[i],en=(i+1<tv.size())?tv[i+1]:(uint32_t)n;
        if(en<=st) continue; char nm[64]; std::snprintf(nm,sizeof nm,"blk%04zu_0x%06x.bin",nblocks,st);
        idx<<nm<<"  0x"<<std::hex<<st<<"  "<<std::dec<<(en-st)<<"\n";
        if(opt.write_blocks) write_file(out/"blocks"/nm,reloc.data()+st,en-st); ++nblocks; } }

    // ------------------------------------------------------------------ TEXTURES
    size_t ntex=0;
    std::string biggest_png; uint32_t biggest_area=0;
    if(opt.write_textures){
        std::ofstream tix; bool opened=false; std::set<size_t> done;
        for(size_t o=0;o+0x30<=n;o+=4){
            uint16_t w=rd_be16(&d[o]), h=rd_be16(&d[o+2]);
            uint32_t fmt=rd_be32(&d[o+4]), pd=rd_be32(&d[o+8]);
            GXFmt gf; if(!gx_fmt(fmt,gf)) continue;
            if(w<1||h<1||w>1024||h>1024) continue;
            if(!(opt.allow_npot||(is_pow2(w)&&is_pow2(h)))) continue;
            if(!(pd>=base&&pd<base+n)) continue;
            size_t data=pd-base; size_t need=(size_t)w*h*gf.bpp/8;
            if(data+need>n) continue;
            if(done.count(data)) continue;               // dedup by pixel data
            // palette for CI formats
            uint32_t palfmt=2; size_t palo=0; bool havePal=false;
            if(fmt==8||fmt==9||fmt==10){
                uint32_t pf=rd_be32(&d[o+0x28]), pp=rd_be32(&d[o+0x2c]);
                if(pp>=base&&pp<base+n){ palo=pp-base; palfmt=(pf<=2?pf:2); havePal=true; }
                else { size_t pe=(fmt==8?16:(fmt==9?256:16384))*2; // palette precedes data
                       if(data>=pe){ palo=data-pe; palfmt=2; havePal=true; } }
            }
            std::vector<uint8_t> img;
            if(!gx_decode(d,data,w,h,fmt,palfmt,palo,havePal,img)) continue;
            if(!opened){ fs::create_directories(out/"textures");
                tix.open(out/"textures"/"index.txt");
                tix<<"# png  desc_off  data_off  format  w  h  bytes\n"; opened=true; }
            char nm[96]; std::snprintf(nm,sizeof nm,"tex_%04zu_0x%06zx_%s_%dx%d.png",
                                       ntex,(size_t)data,gf.name,(int)w,(int)h);
            write_png(out/"textures"/nm,img,w,h);
            if((uint32_t)w*h>biggest_area){ biggest_area=(uint32_t)w*h; biggest_png=std::string("textures/")+nm; }
            tix<<nm<<"  0x"<<std::hex<<o<<"  0x"<<data<<std::dec<<"  "<<gf.name
               <<"  "<<w<<"  "<<h<<"  "<<need<<"\n";
            done.insert(data); ++ntex;
        }
    }

    // ------------------------------------------------------------------ MODELS
    // GX display-list draw opcodes: high 5 bits select primitive, low 3 = VAT.
    size_t nmodel=0;
    { std::ofstream mf(out/"gx_models.txt");
      mf<<"# GX display-list draw commands (heuristic scan)\n";
      mf<<"# offset    primitive     vat  vertices\n";
      auto primname=[](uint8_t op)->const char*{ switch(op){
        case 0x80:return"QUADS"; case 0x88:return"QUADS2"; case 0x90:return"TRIANGLES";
        case 0x98:return"TRISTRIP"; case 0xA0:return"TRIFAN"; case 0xA8:return"LINES";
        case 0xB0:return"LINESTRIP"; case 0xB8:return"POINTS"; default:return nullptr; } };
      for(size_t o=0;o+3<=n;){
        uint8_t op=d[o]&0xF8, vat=d[o]&0x07; const char* pn=primname(op);
        if(pn && d[o]!=0x00){
            uint16_t cnt=rd_be16(&d[o+1]);
            if(cnt>=1&&cnt<=4096){
                char line[96]; std::snprintf(line,sizeof line,"0x%06zx  %-12s  %d    %d",o,pn,vat,cnt);
                mf<<line<<"\n"; ++nmodel; o+=3; continue;
            }
        }
        ++o;
      }
      mf<<"\n# total draw commands: "<<nmodel<<"\n";
      mf<<"# note: display lists index into adjacent float vertex arrays; full\n";
      mf<<"#       mesh export requires the per-object vertex descriptor (VCD).\n";
    }

    // ------------------------------------------------------------------ OBJ EXPORT
    size_t objV=0,objF=0,objM=0;
    if(opt.write_obj){
        std::string material; fs::path mtlpath=out/(stem.string()+".mtl");
        if(!biggest_png.empty()){
            material="tex_default";
            std::ofstream mf(mtlpath);
            mf<<"# material references the largest decoded texture in this file.\n";
            mf<<"# GX meshes don't carry an explicit texture id here, so reassign per\n";
            mf<<"# mesh in your 3D tool if needed; UVs are exported correctly.\n";
            mf<<"newmtl "<<material<<"\nKa 1 1 1\nKd 1 1 1\nd 1\nillum 1\nmap_Kd "<<biggest_png<<"\n";
        }
        export_obj(d,base,out/(stem.string()+".obj"),mtlpath,material,objV,objF,objM);
        if(objM==0){ std::error_code ec; fs::remove(out/(stem.string()+".obj"),ec); fs::remove(mtlpath,ec); }
    }

    // strings
    size_t nstr=0;
    { std::ofstream sf(out/"strings.txt");
      sf<<"# offset    string   (source: "<<in_path.filename().string()<<")\n";
      size_t i=0; while(i<n){ if(d[i]>=0x20&&d[i]<=0x7e){ size_t j=i;
        while(j<n&&d[j]>=0x20&&d[j]<=0x7e)++j; if(j-i>=4){ sf<<"0x"<<std::hex<<i<<std::dec<<"\t";
        sf.write((const char*)&d[i],(std::streamsize)(j-i)); sf<<"\n"; ++nstr; } i=j; } else ++i; } }

    // reloc table
    { std::ofstream rf(out/"reloc.txt");
      rf<<"# load_base=0x"<<std::hex<<base<<std::dec<<"  codec="<<codec
        <<"  pointer_sites="<<sites.size()<<"\n";
      for(size_t o:sites) rf<<"0x"<<std::hex<<o<<"\n"; }

    // layout dump
    { std::ofstream lf(out/"layout.txt");
      lf<<"PACK.rom structured dump\n  source     : "<<in_path.filename().string()
        <<"\n  size       : "<<n<<" bytes\n  codec      : "<<codec
        <<"\n  load base  : 0x"<<std::hex<<base<<std::dec
        <<"\n  ptr sites  : "<<sites.size()<<"\n  blocks     : "<<nblocks
        <<"\n  textures   : "<<ntex<<"\n  draw cmds  : "<<nmodel
        <<"\n  obj meshes : "<<objM<<" ("<<objV<<" verts, "<<objF<<" faces)"
        <<"\n  strings    : "<<nstr
        <<"\n  legend     : PTR=pointer FLT=float TAG=type id INT=integer\n\n";
      for(size_t i=0;i<tv.size();++i){ uint32_t st=tv[i],en=(i+1<tv.size())?tv[i+1]:(uint32_t)n;
        if(en<=st) continue; lf<<"block @0x"<<std::hex<<st<<"  size="<<std::dec<<(en-st)<<"\n";
        int shown=0; for(uint32_t o=st;o+4<=en;o+=4){ if(shown>=opt.max_dump){
            lf<<"    ... ("<<((en-o)/4)<<" more words)\n"; break; }
          uint32_t w=rd_be32(&d[o]); char ln[96];
          if(w>=base&&w<base+n) std::snprintf(ln,sizeof ln,"    +0x%04x  PTR ->0x%06x",o-st,w-base);
          else if(looks_tag(w)) std::snprintf(ln,sizeof ln,"    +0x%04x  TAG 0x%02x (0x%08x)",o-st,w>>24,w);
          else if(looks_float(w)){ float f; std::memcpy(&f,&w,4); std::snprintf(ln,sizeof ln,"    +0x%04x  FLT %g",o-st,f); }
          else std::snprintf(ln,sizeof ln,"    +0x%04x  INT 0x%08x (%d)",o-st,w,(int32_t)w);
          lf<<ln<<"\n"; ++shown; } lf<<"\n"; } }

    if(!opt.quiet)
        std::printf("  %-30s %8zu B  ptrs=%-5zu blk=%-4zu tex=%-4zu obj=%zu(%zuf) str=%-4zu\n",
                    in_path.filename().string().c_str(),n,sites.size(),nblocks,ntex,objM,objF,nstr);
}

// ==========================================================================
int main(int argc,char**argv){
    if(argc<2){
        std::cerr<<"packrom_unpack - GameCube resource extractor for *_PACK.rom\n\n"
          "usage: "<<argv[0]<<" <file.rom | directory> [options]\n"
          "  -o <dir>        output directory            (default ./unpacked)\n"
          "  --base 0xADDR   override load base           (default 0x40000000)\n"
          "  --auto          auto-detect load base\n"
          "  --rebase 0xN    base written into output     (default 0)\n"
          "  --max-dump N    words per block in layout    (default 48)\n"
          "  --no-blocks     do not write per-block files\n"
          "  --no-textures   do not decode textures to PNG\n"
          "  --no-obj        do not export models to OBJ\n"
          "  --allow-npot    accept non-power-of-two texture sizes\n"
          "  -q              quiet\n";
        return 1;
    }
    Options opt; fs::path input;
    for(int i=1;i<argc;i++){ std::string a=argv[i];
        auto need=[&](const char*nm)->std::string{ if(i+1>=argc){ std::cerr<<"missing value for "<<nm<<"\n"; std::exit(1);} return argv[++i]; };
        if(a=="-o") opt.outdir=need("-o");
        else if(a=="--base"){ opt.base=std::stoul(need("--base"),nullptr,0); opt.base_set=true; }
        else if(a=="--auto") opt.auto_base=true;
        else if(a=="--rebase") opt.rebase=std::stoul(need("--rebase"),nullptr,0);
        else if(a=="--max-dump") opt.max_dump=std::stoi(need("--max-dump"));
        else if(a=="--no-blocks") opt.write_blocks=false;
        else if(a=="--no-textures") opt.write_textures=false;
        else if(a=="--no-obj") opt.write_obj=false;
        else if(a=="--allow-npot") opt.allow_npot=true;
        else if(a=="-q") opt.quiet=true;
        else if(!a.empty()&&a[0]=='-'){ std::cerr<<"unknown option "<<a<<"\n"; return 1; }
        else input=a;
    }
    if(input.empty()){ std::cerr<<"no input given\n"; return 1; }
    fs::create_directories(opt.outdir);

    std::vector<fs::path> jobs;
    if(fs::is_directory(input)){
        for(auto&e:fs::directory_iterator(input)){ std::string ext=e.path().extension().string();
            std::transform(ext.begin(),ext.end(),ext.begin(),::tolower);
            if(ext==".rom") jobs.push_back(e.path()); }
        std::sort(jobs.begin(),jobs.end());
    } else jobs.push_back(input);
    if(jobs.empty()){ std::cerr<<"no .rom files found\n"; return 1; }

    std::printf("Unpacking %zu file(s) -> %s\n",jobs.size(),opt.outdir.string().c_str());
    for(auto&j:jobs) unpack_one(j,opt);
    std::printf("Done. %zu file(s) under %s\n",jobs.size(),opt.outdir.string().c_str());
    return 0;
}
