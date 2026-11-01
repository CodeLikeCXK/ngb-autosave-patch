#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <d3d9.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <intrin.h>

// Exports are declared via linker pragmas (no .def) so exported symbol names are exact.
#pragma comment(linker, "/EXPORT:Direct3DCreate9=_Proxy_Direct3DCreate9@4")
#pragma comment(linker, "/EXPORT:Direct3DCreate9Ex=_Proxy_Direct3DCreate9Ex@8")
#pragma comment(linker, "/EXPORT:D3DPERF_BeginEvent=_Proxy_D3DPERF_BeginEvent@8")
#pragma comment(linker, "/EXPORT:D3DPERF_EndEvent=_Proxy_D3DPERF_EndEvent@0")
#pragma comment(linker, "/EXPORT:D3DPERF_SetMarker=_Proxy_D3DPERF_SetMarker@8")
#pragma comment(linker, "/EXPORT:D3DPERF_SetRegion=_Proxy_D3DPERF_SetRegion@8")
#pragma comment(linker, "/EXPORT:D3DPERF_QueryRepeatFrame=_Proxy_D3DPERF_QueryRepeatFrame@0")
#pragma comment(linker, "/EXPORT:D3DPERF_SetOptions=_Proxy_D3DPERF_SetOptions@4")
#pragma comment(linker, "/EXPORT:D3DPERF_GetStatus=_Proxy_D3DPERF_GetStatus@0")

// Real system d3d9 exports
static HMODULE g_hRealD3D9 = NULL;
typedef IDirect3D9* (WINAPI *PFN_Direct3DCreate9)(UINT SDKVersion);
typedef HRESULT (WINAPI *PFN_Direct3DCreate9Ex)(UINT SDKVersion, IDirect3D9Ex** ppD3D);

static PFN_Direct3DCreate9 g_pfnDirect3DCreate9 = NULL;
static PFN_Direct3DCreate9Ex g_pfnDirect3DCreate9Ex = NULL;

// Optional XInput support for Xbox controller hotkeys
typedef struct _XINPUT_GAMEPAD_MINI {
    WORD  wButtons;
    BYTE  bLeftTrigger;
    BYTE  bRightTrigger;
    SHORT sThumbLX;
    SHORT sThumbLY;
    SHORT sThumbRX;
    SHORT sThumbRY;
} XINPUT_GAMEPAD_MINI;

typedef struct _XINPUT_STATE_MINI {
    DWORD               dwPacketNumber;
    XINPUT_GAMEPAD_MINI Gamepad;
} XINPUT_STATE_MINI;

typedef DWORD (WINAPI *PFN_XInputGetState)(DWORD dwUserIndex, XINPUT_STATE_MINI* pState);
static PFN_XInputGetState g_pfnXInputGetState = NULL;
static BOOL g_XInputChecked = FALSE;

static FILE* g_log = NULL;
static volatile LONG g_LogLock = 0;   // tiny spinlock: Log() is called from worker, game, and D3D threads

void Log(const char* fmt, ...) {
    while (InterlockedCompareExchange(&g_LogLock, 1, 0) != 0) Sleep(0);
    if (!g_log) {
        g_log = fopen("autosave_proxy.log", "a");
    }
    if (g_log) {
        va_list va;
        va_start(va, fmt);
        vfprintf(g_log, fmt, va);
        va_end(va);
        fflush(g_log);
    }
    InterlockedExchange(&g_LogLock, 0);
}

// ============================================================================
// PART 1: D3D9On12 Shader Signature Sanitizer (Fixes dxilconv.dll + 0x34855)
// ============================================================================
// Root cause: blackrt.dll's nv2a_psh compiles Xbox register-combiner pixel shaders
// (e.g. Chapter 5 Hydracubus boss PS #5, 073ca24318354205.bin) w;po9p-0[=]=0p]-p0o9p-0[=0ith dcl v0 / dcl t0.xyzw / dcl t1.xy.
// When paired with Fixed-Function Vertex Processing (SetVertexShader(NULL)) whose bound FVF /
// VertexDeclaration omits COLOR0/TEXCOORDn or provides fewer components (e.g. FLOAT2 instead of FLOAT4
// for projective t0.xyzw), Windows 11 D3D9On12's dxilconv.dll dereferences NULL in DxilSignature::Find
// (dxilconv.dll + 0x34855). We dynamically narrow/strip missing PS input declarations and supply exact
// D3D9/NV2A default components (v0=(1,1,1,1), v1=(0,0,0,0), tN=(0,0,0,1)) while preserving all present
// vertex components (such as real t0.xy when only .zw is missing).

static CRITICAL_SECTION g_D3DLock;
static BOOL g_D3DLockInit = FALSE;

static DWORD GetShaderRegType(DWORD tok) {
    return ((tok >> 28) & 0x7) | (((tok >> 11) & 0x3) << 3);
}

// 40-bit component mask packed in ULONGLONG (10 slots * 4 bits):
//   slot 0 (bits  0..3 ): v0 (COLOR0)
//   slot 1 (bits  4..7 ): v1 (COLOR1)
//   slot 2..9 (bits 8..39): t0..t7 (TEXCOORD0..7)
static ULONGLONG ScanPSCompMask(const DWORD* bc, DWORD* outDwordLen) {
    if (!bc || (bc[0] >> 16) != 0xFFFF) {
        if (outDwordLen) *outDwordLen = 0;
        return 0;
    }
    ULONGLONG mask = 0;
    DWORD i = 1;
    for (;;) {
        DWORD tok = bc[i];
        DWORD op = tok & 0xFFFF;
        if (op == 0xFFFF) { i++; break; }
        if (op == 0xFFFE) {
            i += 1 + ((tok >> 16) & 0x7FFF);
            continue;
        }
        DWORD ilen = (tok >> 24) & 0x0F;
        if (ilen == 0) {
            if (outDwordLen) *outDwordLen = 0;
            return 0;
        }
        if (op == 0x1F && ilen >= 2) { // DCL
            DWORD regTok = bc[i + 2];
            DWORD rtype = GetShaderRegType(regTok);
            DWORD rnum  = regTok & 0x7FF;
            ULONGLONG comp = (regTok >> 16) & 0x0F;
            if (rtype == 1 && rnum < 2) mask |= (comp << (rnum * 4));
            else if (rtype == 3 && rnum < 8) mask |= (comp << ((2 + rnum) * 4));
        }
        i += 1 + ilen;
    }
    if (outDwordLen) *outDwordLen = i;
    return mask;
}

static ULONGLONG ScanVSOutputCompMask(const DWORD* bc) {
    if (!bc || (bc[0] >> 16) != 0xFFFE) return 0xFFFFFFFFFFULL;
    DWORD ver = bc[0] & 0xFFFF;
    ULONGLONG mask = 0;
    DWORD i = 1;
    for (;;) {
        DWORD tok = bc[i];
        DWORD op = tok & 0xFFFF;
        if (op == 0xFFFF) break;
        if (op == 0xFFFE) {
            i += 1 + ((tok >> 16) & 0x7FFF);
            continue;
        }
        DWORD ilen = (tok >> 24) & 0x0F;
        if (ilen == 0) return 0xFFFFFFFFFFULL;
        if (ver >= 0x0300) {
            if (op == 0x1F && ilen >= 2) {
                DWORD semTok = bc[i + 1];
                DWORD regTok = bc[i + 2];
                DWORD rtype = GetShaderRegType(regTok);
                if (rtype == 6) { // D3DSPR_OUTPUT
                    DWORD usage = semTok & 0x0F;
                    DWORD usageIdx = (semTok >> 16) & 0x0F;
                    ULONGLONG comp = (regTok >> 16) & 0x0F;
                    if (usage == D3DDECLUSAGE_COLOR && usageIdx < 2) mask |= (comp << (usageIdx * 4));
                    else if (usage == D3DDECLUSAGE_TEXCOORD && usageIdx < 8) mask |= (comp << ((2 + usageIdx) * 4));
                }
            }
        } else {
            if (op != 0x51 && op != 0x1F && ilen >= 1) {
                DWORD dst = bc[i + 1];
                DWORD rtype = GetShaderRegType(dst);
                DWORD rnum  = dst & 0x7FF;
                ULONGLONG comp = (dst >> 16) & 0x0F;
                if (rtype == 5 && rnum < 2) mask |= (comp << (rnum * 4));          // oD0..oD1
                else if (rtype == 6 && rnum < 8) mask |= (comp << ((2 + rnum) * 4)); // oT0..oT7
            }
        }
        i += 1 + ilen;
    }
    return mask;
}

static DWORD* BuildSanitizedPSBytecode(const DWORD* bc, ULONGLONG availCompMask) {
    DWORD totalLen = 0;
    ULONGLONG reqMask = ScanPSCompMask(bc, &totalLen);
    ULONGLONG missingMask = reqMask & ~availCompMask;
    if (!missingMask || totalLen == 0) return NULL;

    DWORD usedC = 0, usedR = 0, lastDefOrDclEnd = 1, i = 1;
    while (i < totalLen) {
        DWORD tok = bc[i], op = tok & 0xFFFF;
        if (op == 0xFFFF) break;
        if (op == 0xFFFE) {
            DWORD nx = i + 1 + ((tok >> 16) & 0x7FFF);
            if (lastDefOrDclEnd == i) lastDefOrDclEnd = nx;
            i = nx;
            continue;
        }
        DWORD ilen = (tok >> 24) & 0x0F;
        if (op == 0x51) {
            DWORD rn = bc[i + 1] & 0x7FF;
            if (rn < 32) usedC |= (1u << rn);
            lastDefOrDclEnd = i + 1 + ilen;
        } else if (op == 0x1F) {
            lastDefOrDclEnd = i + 1 + ilen;
        } else {
            for (DWORD k = 1; k <= ilen; k++) {
                DWORD rt = GetShaderRegType(bc[i + k]);
                DWORD rn = bc[i + k] & 0x7FF;
                if (rt == 0 && rn < 32) usedR |= (1u << rn);
                else if (rt == 2 && rn < 32) usedC |= (1u << rn);
            }
        }
        i += 1 + ilen;
    }

    int freeC = -1;
    for (int c = 31; c >= 0; c--) {
        if (!(usedC & (1u << c))) { freeC = c; break; }
    }
    if (freeC < 0) return NULL;

    int slotTemp[10];
    for (int s = 0; s < 10; s++) slotTemp[s] = -1;
    int sharedOnes = -1, sharedZero = -1, sharedTex = -1;

    for (int s = 0; s < 10; s++) {
        DWORD req = (DWORD)((reqMask >> (s * 4)) & 0x0F);
        DWORD avl = (DWORD)((availCompMask >> (s * 4)) & 0x0F);
        DWORD mis = req & ~avl;
        if (!mis) continue;
        if ((req & avl) == 0) {
            int* shared = (s == 0) ? &sharedOnes : ((s == 1) ? &sharedZero : &sharedTex);
            if (*shared < 0) {
                for (int r = 0; r < 12; r++) {
                    if (!(usedR & (1u << r))) { usedR |= (1u << r); *shared = r; break; }
                }
            }
            slotTemp[s] = *shared;
        } else {
            for (int r = 0; r < 12; r++) {
                if (!(usedR & (1u << r))) { usedR |= (1u << r); slotTemp[s] = r; break; }
            }
        }
        if (slotTemp[s] < 0) return NULL;
    }

    DWORD* out = (DWORD*)HeapAlloc(GetProcessHeap(), 0, (totalLen + 80) * sizeof(DWORD));
    if (!out) return NULL;

    DWORD w = 0;
    out[w++] = bc[0];
    BOOL emDef = FALSE, emMov = FALSE;
    i = 1;
    while (i < totalLen) {
        DWORD tok = bc[i], op = tok & 0xFFFF;
        if (!emDef && op != 0xFFFE) {
            emDef = TRUE;
            // def cFree, 0.0f, 0.0f, 0.0f, 1.0f (only legal ps_2_0 replicate/identity swizzles needed!)
            out[w++] = 0x05000051;
            out[w++] = 0xA00F0000 | (DWORD)freeC;
            out[w++] = 0x00000000;
            out[w++] = 0x00000000;
            out[w++] = 0x00000000;
            out[w++] = 0x3F800000;
        }
        if (!emMov && i >= lastDefOrDclEnd) {
            emMov = TRUE;
            if (sharedOnes >= 0) {
                out[w++] = 0x02000001;
                out[w++] = 0x800F0000 | (DWORD)sharedOnes;
                out[w++] = 0xA0FF0000 | (DWORD)freeC; // cFree.wwww = (1,1,1,1)
            }
            if (sharedZero >= 0) {
                out[w++] = 0x02000001;
                out[w++] = 0x800F0000 | (DWORD)sharedZero;
                out[w++] = 0xA0000000 | (DWORD)freeC; // cFree.xxxx = (0,0,0,0)
            }
            if (sharedTex >= 0) {
                out[w++] = 0x02000001;
                out[w++] = 0x800F0000 | (DWORD)sharedTex;
                out[w++] = 0xA0E40000 | (DWORD)freeC; // cFree.xyzw = (0,0,0,1)
            }
            for (int s = 0; s < 10; s++) {
                DWORD req = (DWORD)((reqMask >> (s * 4)) & 0x0F);
                DWORD avl = (DWORD)((availCompMask >> (s * 4)) & 0x0F);
                DWORD keep = req & avl;
                if (keep != 0 && (req & ~avl) != 0) {
                    int r = slotTemp[s];
                    DWORD defSwz = (s == 0) ? 0xA0FF0000 : ((s == 1) ? 0xA0000000 : 0xA0E40000);
                    out[w++] = 0x02000001;
                    out[w++] = 0x800F0000 | (DWORD)r;
                    out[w++] = defSwz | (DWORD)freeC;

                    DWORD srcTok = (s < 2) ? (0x90E40000u | (DWORD)s) : (0xB0E40000u | (DWORD)(s - 2));
                    out[w++] = 0x02000001;
                    out[w++] = 0x80000000u | (keep << 16) | (DWORD)r;
                    out[w++] = srcTok;
                }
            }
        }
        if (op == 0xFFFF) { out[w++] = tok; break; }
        if (op == 0xFFFE) {
            DWORD cl = (tok >> 16) & 0x7FFF;
            memcpy(&out[w], &bc[i], (1 + cl) * sizeof(DWORD));
            w += 1 + cl; i += 1 + cl;
            continue;
        }
        DWORD ilen = (tok >> 24) & 0x0F;
        if (op == 0x1F && ilen >= 2) {
            DWORD regTok = bc[i + 2];
            DWORD rt = GetShaderRegType(regTok), rn = regTok & 0x7FF;
            int s = (rt == 1 && rn < 2) ? (int)rn : ((rt == 3 && rn < 8) ? (int)(2 + rn) : -1);
            if (s >= 0 && slotTemp[s] >= 0) {
                DWORD req = (DWORD)((reqMask >> (s * 4)) & 0x0F);
                DWORD avl = (DWORD)((availCompMask >> (s * 4)) & 0x0F);
                DWORD keep = req & avl;
                if (keep == 0) {
                    i += 1 + ilen;
                    continue;
                } else {
                    out[w++] = tok;
                    out[w++] = bc[i + 1];
                    out[w++] = (regTok & ~0x000F0000u) | (keep << 16);
                    i += 1 + ilen;
                    continue;
                }
            }
            memcpy(&out[w], &bc[i], (1 + ilen) * sizeof(DWORD));
            w += 1 + ilen; i += 1 + ilen;
            continue;
        }
        if (op == 0x51) {
            memcpy(&out[w], &bc[i], (1 + ilen) * sizeof(DWORD));
            w += 1 + ilen; i += 1 + ilen;
            continue;
        }

        out[w++] = tok;
        for (DWORD k = 1; k <= ilen; k++) {
            DWORD p = bc[i + k];
            if (k >= 2 || (op == 0x41 && k == 1)) {
                DWORD rt = GetShaderRegType(p), rn = p & 0x7FF;
                int s = (rt == 1 && rn < 2) ? (int)rn : ((rt == 3 && rn < 8) ? (int)(2 + rn) : -1);
                if (s >= 0 && slotTemp[s] >= 0) {
                    p = (p & ~0x70001FFFu) | (DWORD)slotTemp[s];
                }
            }
            out[w++] = p;
        }
        i += 1 + ilen;
    }
    return out;
}

struct DeclInfo {
    IDirect3DVertexDeclaration9* decl;
    ULONGLONG compMask;
    BOOL hasPosT;
    BOOL hasNormal;
};

struct VSEntry {
    IDirect3DVertexShader9* vs;
    ULONGLONG outCompMask;
};

struct PSVariant {
    ULONGLONG effAvailMask;
    IDirect3DPixelShader9* ps;
};

struct PSEntry {
    IDirect3DPixelShader9* origPS;
    DWORD* bytecode;
    ULONGLONG reqCompMask;
    PSVariant variants[16];
    int variantCount;
};

#define MAX_DECL_CACHE 1024
#define MAX_VS_CACHE   1024
#define MAX_PS_CACHE   2048

static DeclInfo g_DeclCache[MAX_DECL_CACHE];
static int g_DeclCount = 0;
static int g_DeclEvictIdx = 0;

static VSEntry g_VSCache[MAX_VS_CACHE];
static int g_VSCount = 0;
static int g_VSEvictIdx = 0;
static IDirect3DVertexShader9* g_LastVS = NULL;
static ULONGLONG g_LastVSMask = 0xFFFFFFFFFFULL;

static PSEntry g_PSCache[MAX_PS_CACHE];
static int g_PSCount = 0;
static int g_PSEvictIdx = 0;
static PSEntry* g_LastPSEntry = NULL;

static BOOL g_InStateBlockRecord = FALSE;
static BOOL g_DeviceIsEx = FALSE;
static LONG g_RehookLogCount = 0;
static LONG g_PSRegLogCount = 0;

static DWORD DeclTypeCompMask(BYTE type) {
    switch (type) {
        case D3DDECLTYPE_FLOAT1:    return 0x1;
        case D3DDECLTYPE_FLOAT2:
        case D3DDECLTYPE_SHORT2:
        case D3DDECLTYPE_SHORT2N:
        case D3DDECLTYPE_USHORT2N:
        case D3DDECLTYPE_FLOAT16_2: return 0x3;
        case D3DDECLTYPE_FLOAT3:
        case D3DDECLTYPE_UDEC3:
        case D3DDECLTYPE_DEC3N:     return 0x7;
        case D3DDECLTYPE_FLOAT4:
        case D3DDECLTYPE_D3DCOLOR:
        case D3DDECLTYPE_UBYTE4:
        case D3DDECLTYPE_SHORT4:
        case D3DDECLTYPE_UBYTE4N:
        case D3DDECLTYPE_SHORT4N:
        case D3DDECLTYPE_USHORT4N:
        case D3DDECLTYPE_FLOAT16_4: return 0xF;
        default:                    return 0xF;
    }
}

static void ParseVertexElements(const D3DVERTEXELEMENT9* elems, ULONGLONG* outMask, BOOL* outPosT, BOOL* outNormal) {
    ULONGLONG mask = 0;
    BOOL posT = FALSE, norm = FALSE;
    if (elems) {
        for (int i = 0; i < 64 && elems[i].Stream != 0xFF; i++) {
            BYTE u = elems[i].Usage;
            BYTE idx = elems[i].UsageIndex;
            if (u == D3DDECLUSAGE_POSITIONT) posT = TRUE;
            else if (u == D3DDECLUSAGE_NORMAL) norm = TRUE;
            else if (u == D3DDECLUSAGE_COLOR && idx < 2) mask |= (0xFULL << (idx * 4));
            else if (u == D3DDECLUSAGE_TEXCOORD && idx < 8) {
                ULONGLONG cm = DeclTypeCompMask(elems[i].Type);
                mask |= (cm << ((2 + idx) * 4));
            }
        }
    }
    *outMask = mask;
    *outPosT = posT;
    *outNormal = norm;
}

static void ParseFVF(DWORD fvf, ULONGLONG* outMask, BOOL* outPosT, BOOL* outNormal) {
    ULONGLONG mask = 0;
    BOOL posT = ((fvf & D3DFVF_POSITION_MASK) == D3DFVF_XYZRHW);
    BOOL norm = ((fvf & D3DFVF_NORMAL) != 0);
    if (fvf & D3DFVF_DIFFUSE)  mask |= 0x0FULL;
    if (fvf & D3DFVF_SPECULAR) mask |= 0xF0ULL;
    DWORD nTex = (fvf & D3DFVF_TEXCOUNT_MASK) >> D3DFVF_TEXCOUNT_SHIFT;
    if (nTex > 8) nTex = 8;
    for (DWORD k = 0; k < nTex; k++) {
        DWORD fmt = (fvf >> (16 + k * 2)) & 0x3;
        ULONGLONG cm = (fmt == 0) ? 0x3 : ((fmt == 1) ? 0x7 : ((fmt == 2) ? 0xF : 0x1));
        mask |= (cm << ((2 + k) * 4));
    }
    *outMask = mask;
    *outPosT = posT;
    *outNormal = norm;
}

static void CacheDeclEntryLocked(IDirect3DVertexDeclaration9* decl, ULONGLONG mask, BOOL posT, BOOL norm) {
    int slot = -1;
    for (int i = g_DeclCount - 1; i >= 0; i--) {
        if (g_DeclCache[i].decl == decl) { slot = i; break; }
    }
    if (slot < 0) {
        if (g_DeclCount < MAX_DECL_CACHE) {
            slot = g_DeclCount++;
        } else {
            slot = g_DeclEvictIdx;
            g_DeclEvictIdx = (g_DeclEvictIdx + 1) % MAX_DECL_CACHE;
        }
    }
    g_DeclCache[slot].decl = decl;
    g_DeclCache[slot].compMask = mask;
    g_DeclCache[slot].hasPosT = posT;
    g_DeclCache[slot].hasNormal = norm;
}

static void LookupOrRegisterDeclLocked(IDirect3DVertexDeclaration9* decl, ULONGLONG* outMask, BOOL* outPosT, BOOL* outNormal) {
    for (int i = g_DeclCount - 1; i >= 0; i--) {
        if (g_DeclCache[i].decl == decl) {
            *outMask = g_DeclCache[i].compMask;
            *outPosT = g_DeclCache[i].hasPosT;
            *outNormal = g_DeclCache[i].hasNormal;
            return;
        }
    }
    D3DVERTEXELEMENT9 elems[65];
    UINT num = 65;
    if (SUCCEEDED(decl->GetDeclaration(elems, &num))) {
        ParseVertexElements(elems, outMask, outPosT, outNormal);
        CacheDeclEntryLocked(decl, *outMask, *outPosT, *outNormal);
    } else {
        *outMask = 0;
        *outPosT = FALSE;
        *outNormal = FALSE;
    }
}

static void CacheVSEntryLocked(IDirect3DVertexShader9* vs, ULONGLONG outMask) {
    int slot = -1;
    for (int i = g_VSCount - 1; i >= 0; i--) {
        if (g_VSCache[i].vs == vs) { slot = i; break; }
    }
    if (slot < 0) {
        if (g_VSCount < MAX_VS_CACHE) {
            slot = g_VSCount++;
        } else {
            slot = g_VSEvictIdx;
            g_VSEvictIdx = (g_VSEvictIdx + 1) % MAX_VS_CACHE;
        }
    }
    g_VSCache[slot].vs = vs;
    g_VSCache[slot].outCompMask = outMask;
    g_LastVS = vs;
    g_LastVSMask = outMask;
}

static ULONGLONG LookupOrRegisterVSLocked(IDirect3DVertexShader9* vs) {
    if (vs == g_LastVS && vs != NULL) return g_LastVSMask;
    for (int i = g_VSCount - 1; i >= 0; i--) {
        if (g_VSCache[i].vs == vs) {
            g_LastVS = vs;
            g_LastVSMask = g_VSCache[i].outCompMask;
            return g_LastVSMask;
        }
    }
    UINT byteLen = 0;
    ULONGLONG outMask = 0xFFFFFFFFFFULL;
    if (SUCCEEDED(vs->GetFunction(NULL, &byteLen)) && byteLen >= 8) {
        DWORD* tmp = (DWORD*)HeapAlloc(GetProcessHeap(), 0, byteLen);
        if (tmp) {
            if (SUCCEEDED(vs->GetFunction(tmp, &byteLen))) {
                outMask = ScanVSOutputCompMask(tmp);
            }
            HeapFree(GetProcessHeap(), 0, tmp);
        }
    }
    CacheVSEntryLocked(vs, outMask);
    return outMask;
}

static void ClearPSEntrySlotLocked(PSEntry* pe) {
    if (pe->bytecode) {
        HeapFree(GetProcessHeap(), 0, pe->bytecode);
        pe->bytecode = NULL;
    }
    for (int v = 0; v < pe->variantCount; v++) {
        if (pe->variants[v].ps) {
            pe->variants[v].ps->Release();
            pe->variants[v].ps = NULL;
        }
    }
    pe->variantCount = 0;
    pe->origPS = NULL;
    pe->reqCompMask = 0;
}

static PSEntry* RegisterPSBytecodeLocked(IDirect3DPixelShader9* ps, const DWORD* pFunction) {
    DWORD dwLen = 0;
    ULONGLONG reqMask = ScanPSCompMask(pFunction, &dwLen);
    if (dwLen == 0) return NULL;

    DWORD* copyBC = (DWORD*)HeapAlloc(GetProcessHeap(), 0, dwLen * sizeof(DWORD));
    if (!copyBC) return NULL;
    memcpy(copyBC, pFunction, dwLen * sizeof(DWORD));

    int slot = -1;
    for (int i = g_PSCount - 1; i >= 0; i--) {
        if (g_PSCache[i].origPS == ps) { slot = i; break; }
    }
    if (slot >= 0) {
        ClearPSEntrySlotLocked(&g_PSCache[slot]);
    } else if (g_PSCount < MAX_PS_CACHE) {
        slot = g_PSCount++;
    } else {
        slot = g_PSEvictIdx;
        g_PSEvictIdx = (g_PSEvictIdx + 1) % MAX_PS_CACHE;
        ClearPSEntrySlotLocked(&g_PSCache[slot]);
    }

    g_PSCache[slot].origPS = ps;
    g_PSCache[slot].bytecode = copyBC;
    g_PSCache[slot].reqCompMask = reqMask;
    g_PSCache[slot].variantCount = 0;
    g_LastPSEntry = &g_PSCache[slot];

    // Log first few projective (.zw) pixel shaders registered so startup hook health is verifiable
    if ((reqMask & 0xCCCCCCCC00ULL) != 0 && g_PSRegLogCount < 4) {
        g_PSRegLogCount++;
        Log("[D3D9Fix] Registered projective PS %p (dwords=%u, reqCompMask=0x%llX)\n", ps, dwLen, reqMask);
    }
    return &g_PSCache[slot];
}

static PSEntry* LookupOrRegisterPSLocked(IDirect3DPixelShader9* ps) {
    if (g_LastPSEntry && g_LastPSEntry->origPS == ps) return g_LastPSEntry;
    for (int i = g_PSCount - 1; i >= 0; i--) {
        if (g_PSCache[i].origPS == ps) {
            g_LastPSEntry = &g_PSCache[i];
            return g_LastPSEntry;
        }
    }
    // On-the-fly fallback via IDirect3DPixelShader9::GetFunction if created outside hook
    UINT byteLen = 0;
    if (SUCCEEDED(ps->GetFunction(NULL, &byteLen)) && byteLen >= 8) {
        DWORD* tmp = (DWORD*)HeapAlloc(GetProcessHeap(), 0, byteLen);
        if (tmp) {
            PSEntry* pe = NULL;
            if (SUCCEEDED(ps->GetFunction(tmp, &byteLen))) {
                pe = RegisterPSBytecodeLocked(ps, tmp);
            }
            HeapFree(GetProcessHeap(), 0, tmp);
            return pe;
        }
    }
    return NULL;
}

// Queries LIVE pipeline state directly from IDirect3DDevice9 so IDirect3DStateBlock9::Apply()
// (used by blackrt.dll's perfhud/blit overlays) can NEVER desynchronize our state view!
static ULONGLONG QueryLiveVSOutputMaskLocked(IDirect3DDevice9* dev, ULONGLONG reqCompMask,
                                             IDirect3DVertexShader9** outDbgVS, DWORD* outDbgFVF) {
    IDirect3DVertexShader9* curVS = NULL;
    if (SUCCEEDED(dev->GetVertexShader(&curVS)) && curVS != NULL) {
        if (outDbgVS) *outDbgVS = curVS;
        if (outDbgFVF) *outDbgFVF = 0;
        ULONGLONG mask = LookupOrRegisterVSLocked(curVS);
        curVS->Release();
        return mask;
    }

    if (outDbgVS) *outDbgVS = NULL;

    // Fixed-Function Vertex Pipeline (curVS == NULL)
    ULONGLONG declMask = 0;
    BOOL hasPosT = FALSE, hasNormal = FALSE;
    DWORD curFVF = 0;
    dev->GetFVF(&curFVF);
    if (outDbgFVF) *outDbgFVF = curFVF;

    IDirect3DVertexDeclaration9* curDecl = NULL;
    if (SUCCEEDED(dev->GetVertexDeclaration(&curDecl)) && curDecl != NULL) {
        LookupOrRegisterDeclLocked(curDecl, &declMask, &hasPosT, &hasNormal);
        curDecl->Release();
    } else if (curFVF != 0) {
        ParseFVF(curFVF, &declMask, &hasPosT, &hasNormal);
    }

    ULONGLONG outMask = 0;
    DWORD lighting = 0, specular = 0;
    if ((reqCompMask & 0xFFULL) != 0) {
        dev->GetRenderState(D3DRS_LIGHTING, &lighting);
        if ((reqCompMask & 0xF0ULL) != 0 && lighting) {
            dev->GetRenderState(D3DRS_SPECULARENABLE, &specular);
        }
    }

    // v0 (COLOR0): present if vertex has COLOR0 or if FF lighting is active with vertex normals
    if ((declMask & 0x0FULL) != 0 || (!hasPosT && lighting && hasNormal)) {
        outMask |= 0x0FULL;
    }
    // v1 (COLOR1): present if vertex has COLOR1 or if FF specular lighting is active with normals
    if ((declMask & 0xF0ULL) != 0 || (!hasPosT && lighting && specular && hasNormal)) {
        outMask |= 0xF0ULL;
    }

    // t0..t7 (TEXCOORD0..7): only query stages actually declared by this pixel shader
    for (int stage = 0; stage < 8; stage++) {
        if (((reqCompMask >> ((2 + stage) * 4)) & 0x0FULL) == 0) continue;

        DWORD tci = (DWORD)stage;
        DWORD ttf = 0;
        dev->GetTextureStageState(stage, D3DTSS_TEXCOORDINDEX, &tci);
        dev->GetTextureStageState(stage, D3DTSS_TEXTURETRANSFORMFLAGS, &ttf);

        DWORD texGen = tci & 0xFFFF0000u;
        DWORD srcIdx = tci & 0x7u;
        ULONGLONG stageComp = 0;
        if (texGen != 0 && !hasPosT) {
            stageComp = (texGen == D3DTSS_TCI_SPHEREMAP) ? 0x3ULL : 0x7ULL;
        } else {
            stageComp = (declMask >> ((2 + srcIdx) * 4)) & 0x0FULL;
        }
        if (stageComp != 0 && !hasPosT) {
            DWORD cnt = ttf & 0xFFu;
            if (cnt >= 1 && cnt <= 4) {
                stageComp = (1ULL << cnt) - 1ULL;
            }
        }
        outMask |= (stageComp << ((2 + stage) * 4));
    }
    return outMask;
}

// Original IDirect3DDevice9 / IDirect3D9 vtable function pointers
typedef HRESULT (STDMETHODCALLTYPE *PFN_CreateDevice)(IDirect3D9*, UINT, D3DDEVTYPE, HWND, DWORD, D3DPRESENT_PARAMETERS*, IDirect3DDevice9**);
typedef HRESULT (STDMETHODCALLTYPE *PFN_CreateDeviceEx)(IDirect3D9Ex*, UINT, D3DDEVTYPE, HWND, DWORD, D3DPRESENT_PARAMETERS*, D3DDISPLAYMODEEX*, IDirect3DDevice9Ex**);

typedef HRESULT (STDMETHODCALLTYPE *PFN_Reset)(IDirect3DDevice9*, D3DPRESENT_PARAMETERS*);
typedef HRESULT (STDMETHODCALLTYPE *PFN_ResetEx)(IDirect3DDevice9Ex*, D3DPRESENT_PARAMETERS*, D3DDISPLAYMODEEX*);
typedef HRESULT (STDMETHODCALLTYPE *PFN_BeginScene)(IDirect3DDevice9*);
typedef HRESULT (STDMETHODCALLTYPE *PFN_BeginStateBlock)(IDirect3DDevice9*);
typedef HRESULT (STDMETHODCALLTYPE *PFN_EndStateBlock)(IDirect3DDevice9*, IDirect3DStateBlock9**);
typedef HRESULT (STDMETHODCALLTYPE *PFN_SetSoftwareVertexProcessing)(IDirect3DDevice9*, BOOL);
typedef HRESULT (STDMETHODCALLTYPE *PFN_SetNPatchMode)(IDirect3DDevice9*, float);
typedef HRESULT (STDMETHODCALLTYPE *PFN_DrawPrimitive)(IDirect3DDevice9*, D3DPRIMITIVETYPE, UINT, UINT);
typedef HRESULT (STDMETHODCALLTYPE *PFN_DrawIndexedPrimitive)(IDirect3DDevice9*, D3DPRIMITIVETYPE, INT, UINT, UINT, UINT, UINT);
typedef HRESULT (STDMETHODCALLTYPE *PFN_DrawPrimitiveUP)(IDirect3DDevice9*, D3DPRIMITIVETYPE, UINT, CONST void*, UINT);
typedef HRESULT (STDMETHODCALLTYPE *PFN_DrawIndexedPrimitiveUP)(IDirect3DDevice9*, D3DPRIMITIVETYPE, UINT, UINT, UINT, CONST void*, D3DFORMAT, CONST void*, UINT);
typedef HRESULT (STDMETHODCALLTYPE *PFN_CreateVertexDeclaration)(IDirect3DDevice9*, CONST D3DVERTEXELEMENT9*, IDirect3DVertexDeclaration9**);
typedef HRESULT (STDMETHODCALLTYPE *PFN_CreateVertexShader)(IDirect3DDevice9*, CONST DWORD*, IDirect3DVertexShader9**);
typedef HRESULT (STDMETHODCALLTYPE *PFN_CreatePixelShader)(IDirect3DDevice9*, CONST DWORD*, IDirect3DPixelShader9**);

static PFN_CreateDevice                g_OrigCreateDevice = NULL;
static PFN_CreateDeviceEx              g_OrigCreateDeviceEx = NULL;
static PFN_Reset                       g_OrigReset = NULL;
static PFN_ResetEx                     g_OrigResetEx = NULL;
static PFN_BeginScene                  g_OrigBeginScene = NULL;
static PFN_BeginStateBlock             g_OrigBeginStateBlock = NULL;
static PFN_EndStateBlock               g_OrigEndStateBlock = NULL;
static PFN_SetSoftwareVertexProcessing g_OrigSetSoftwareVertexProcessing = NULL;
static PFN_SetNPatchMode               g_OrigSetNPatchMode = NULL;
static PFN_DrawPrimitive               g_OrigDrawPrimitive = NULL;
static PFN_DrawIndexedPrimitive        g_OrigDrawIndexedPrimitive = NULL;
static PFN_DrawPrimitiveUP             g_OrigDrawPrimitiveUP = NULL;
static PFN_DrawIndexedPrimitiveUP      g_OrigDrawIndexedPrimitiveUP = NULL;
static PFN_CreateVertexDeclaration     g_OrigCreateVertexDeclaration = NULL;
static PFN_CreateVertexShader          g_OrigCreateVertexShader = NULL;
static PFN_CreatePixelShader           g_OrigCreatePixelShader = NULL;

// Temporarily binds a sanitized PS variant if any declared PS input component is missing on the live
// vertex pipeline, returning the caller-owned original PS (with +1 ref) so the caller restores it
// immediately after the Draw* call! Keeping the real PS bound at all other times makes StateBlock
// capture/apply and GetPixelShader 100% transparent.
static IDirect3DPixelShader9* BindSanitizedPSForDrawLocked(IDirect3DDevice9* dev) {
    IDirect3DPixelShader9* curPS = NULL;
    if (FAILED(dev->GetPixelShader(&curPS)) || !curPS) {
        return NULL;
    }

    PSEntry* pe = LookupOrRegisterPSLocked(curPS);
    if (!pe || pe->reqCompMask == 0) {
        curPS->Release();
        return NULL;
    }

    IDirect3DVertexShader9* dbgVS = NULL;
    DWORD dbgFVF = 0;
    ULONGLONG avail = QueryLiveVSOutputMaskLocked(dev, pe->reqCompMask, &dbgVS, &dbgFVF);
    ULONGLONG missing = pe->reqCompMask & ~avail;
    if (missing == 0) {
        curPS->Release();
        return NULL;
    }

    ULONGLONG effAvail = pe->reqCompMask & avail;
    IDirect3DPixelShader9* varPS = NULL;
    for (int v = 0; v < pe->variantCount; v++) {
        if (pe->variants[v].effAvailMask == effAvail) {
            varPS = pe->variants[v].ps;
            break;
        }
    }
    if (!varPS) {
        DWORD* sanBC = BuildSanitizedPSBytecode(pe->bytecode, effAvail);
        if (sanBC) {
            HRESULT hr = g_OrigCreatePixelShader(dev, sanBC, &varPS);
            HeapFree(GetProcessHeap(), 0, sanBC);
            if (SUCCEEDED(hr) && varPS) {
                if (pe->variantCount < 16) {
                    pe->variants[pe->variantCount].effAvailMask = effAvail;
                    pe->variants[pe->variantCount].ps = varPS;
                    pe->variantCount++;
                }
                Log("[D3D9Fix] Created sanitized PS %p for origPS=%p (req=0x%llX, avail=0x%llX, VS=%p, FVF=0x%X)\n",
                    varPS, curPS, pe->reqCompMask, effAvail, dbgVS, dbgFVF);
            } else {
                Log("[D3D9Fix] WARNING: CreatePixelShader failed (0x%08X) for origPS=%p (req=0x%llX, avail=0x%llX)\n",
                    hr, curPS, pe->reqCompMask, effAvail);
            }
        }
    }

    if (!varPS) {
        curPS->Release();
        return NULL;
    }

    dev->SetPixelShader(varPS);
    return curPS;
}

static HRESULT STDMETHODCALLTYPE Hook_CreateVertexDeclaration(IDirect3DDevice9* dev, CONST D3DVERTEXELEMENT9* elems, IDirect3DVertexDeclaration9** ppDecl) {
    HRESULT hr = g_OrigCreateVertexDeclaration(dev, elems, ppDecl);
    if (SUCCEEDED(hr) && ppDecl && *ppDecl && elems) {
        ULONGLONG mask = 0; BOOL posT = FALSE, norm = FALSE;
        ParseVertexElements(elems, &mask, &posT, &norm);
        EnterCriticalSection(&g_D3DLock);
        CacheDeclEntryLocked(*ppDecl, mask, posT, norm);
        LeaveCriticalSection(&g_D3DLock);
    }
    return hr;
}

static HRESULT STDMETHODCALLTYPE Hook_CreateVertexShader(IDirect3DDevice9* dev, CONST DWORD* pFunction, IDirect3DVertexShader9** ppShader) {
    HRESULT hr = g_OrigCreateVertexShader(dev, pFunction, ppShader);
    if (SUCCEEDED(hr) && ppShader && *ppShader && pFunction) {
        ULONGLONG outMask = ScanVSOutputCompMask(pFunction);
        EnterCriticalSection(&g_D3DLock);
        CacheVSEntryLocked(*ppShader, outMask);
        LeaveCriticalSection(&g_D3DLock);
    }
    return hr;
}

static HRESULT STDMETHODCALLTYPE Hook_CreatePixelShader(IDirect3DDevice9* dev, CONST DWORD* pFunction, IDirect3DPixelShader9** ppShader) {
    HRESULT hr = g_OrigCreatePixelShader(dev, pFunction, ppShader);
    if (SUCCEEDED(hr) && ppShader && *ppShader && pFunction) {
        EnterCriticalSection(&g_D3DLock);
        RegisterPSBytecodeLocked(*ppShader, pFunction);
        LeaveCriticalSection(&g_D3DLock);
    }
    return hr;
}

static HRESULT STDMETHODCALLTYPE Hook_DrawPrimitive(IDirect3DDevice9* dev, D3DPRIMITIVETYPE pt, UINT startV, UINT primCnt) {
    EnterCriticalSection(&g_D3DLock);
    IDirect3DPixelShader9* restorePS = BindSanitizedPSForDrawLocked(dev);
    HRESULT hr = g_OrigDrawPrimitive(dev, pt, startV, primCnt);
    if (restorePS) {
        dev->SetPixelShader(restorePS);
        restorePS->Release();
    }
    LeaveCriticalSection(&g_D3DLock);
    return hr;
}

static HRESULT STDMETHODCALLTYPE Hook_DrawIndexedPrimitive(IDirect3DDevice9* dev, D3DPRIMITIVETYPE pt, INT baseV, UINT minV, UINT numV, UINT startI, UINT primCnt) {
    EnterCriticalSection(&g_D3DLock);
    IDirect3DPixelShader9* restorePS = BindSanitizedPSForDrawLocked(dev);
    HRESULT hr = g_OrigDrawIndexedPrimitive(dev, pt, baseV, minV, numV, startI, primCnt);
    if (restorePS) {
        dev->SetPixelShader(restorePS);
        restorePS->Release();
    }
    LeaveCriticalSection(&g_D3DLock);
    return hr;
}

static HRESULT STDMETHODCALLTYPE Hook_DrawPrimitiveUP(IDirect3DDevice9* dev, D3DPRIMITIVETYPE pt, UINT primCnt, CONST void* vData, UINT stride) {
    EnterCriticalSection(&g_D3DLock);
    IDirect3DPixelShader9* restorePS = BindSanitizedPSForDrawLocked(dev);
    HRESULT hr = g_OrigDrawPrimitiveUP(dev, pt, primCnt, vData, stride);
    if (restorePS) {
        dev->SetPixelShader(restorePS);
        restorePS->Release();
    }
    LeaveCriticalSection(&g_D3DLock);
    return hr;
}

static HRESULT STDMETHODCALLTYPE Hook_DrawIndexedPrimitiveUP(IDirect3DDevice9* dev, D3DPRIMITIVETYPE pt, UINT minV, UINT numV, UINT primCnt, CONST void* iData, D3DFORMAT iFmt, CONST void* vData, UINT stride) {
    EnterCriticalSection(&g_D3DLock);
    IDirect3DPixelShader9* restorePS = BindSanitizedPSForDrawLocked(dev);
    HRESULT hr = g_OrigDrawIndexedPrimitiveUP(dev, pt, minV, numV, primCnt, iData, iFmt, vData, stride);
    if (restorePS) {
        dev->SetPixelShader(restorePS);
        restorePS->Release();
    }
    LeaveCriticalSection(&g_D3DLock);
    return hr;
}

// Updates *outOrig whenever vtbl[idx] is replaced by d3d9.dll's internal CD3DBase::SwitchApiSet
// (e.g. after BeginStateBlock/EndStateBlock, Reset, or SetSoftwareVertexProcessing).
static void PatchVtableSlot(void** vtbl, int idx, void* hookFn, void** outOrig) {
    if (vtbl[idx] == hookFn) return;
    DWORD oldProt = 0;
    if (VirtualProtect(&vtbl[idx], sizeof(void*), PAGE_EXECUTE_READWRITE, &oldProt)) {
        *outOrig = vtbl[idx];
        vtbl[idx] = hookFn;
        VirtualProtect(&vtbl[idx], sizeof(void*), oldProt, &oldProt);
    }
}

static void ApplyApiSetHooksLocked(IDirect3DDevice9* dev, const char* reason);

static HRESULT STDMETHODCALLTYPE Hook_BeginStateBlock(IDirect3DDevice9* dev) {
    EnterCriticalSection(&g_D3DLock);
    g_InStateBlockRecord = TRUE;
    HRESULT hr = g_OrigBeginStateBlock(dev);
    if (FAILED(hr)) g_InStateBlockRecord = FALSE;
    LeaveCriticalSection(&g_D3DLock);
    return hr;
}

static HRESULT STDMETHODCALLTYPE Hook_EndStateBlock(IDirect3DDevice9* dev, IDirect3DStateBlock9** ppSB) {
    EnterCriticalSection(&g_D3DLock);
    HRESULT hr = g_OrigEndStateBlock(dev, ppSB);
    g_InStateBlockRecord = FALSE;
    // CRITICAL: CD3DBase::EndStateBlock copies d3d9.dll's internal NormalApiSet over vtbl[44..118],
    // which previously wiped our hooks at 0.533s before shader cache creation! Re-apply immediately!
    ApplyApiSetHooksLocked(dev, "EndStateBlock");
    LeaveCriticalSection(&g_D3DLock);
    return hr;
}

static HRESULT STDMETHODCALLTYPE Hook_SetSoftwareVertexProcessing(IDirect3DDevice9* dev, BOOL bSoftware) {
    EnterCriticalSection(&g_D3DLock);
    HRESULT hr = g_OrigSetSoftwareVertexProcessing(dev, bSoftware);
    if (!g_InStateBlockRecord) ApplyApiSetHooksLocked(dev, "SetSoftwareVertexProcessing");
    LeaveCriticalSection(&g_D3DLock);
    return hr;
}

static HRESULT STDMETHODCALLTYPE Hook_SetNPatchMode(IDirect3DDevice9* dev, float nSegments) {
    EnterCriticalSection(&g_D3DLock);
    HRESULT hr = g_OrigSetNPatchMode(dev, nSegments);
    if (!g_InStateBlockRecord) ApplyApiSetHooksLocked(dev, "SetNPatchMode");
    LeaveCriticalSection(&g_D3DLock);
    return hr;
}

static HRESULT STDMETHODCALLTYPE Hook_BeginScene(IDirect3DDevice9* dev) {
    if (!g_InStateBlockRecord && (*(void***)dev)[81] != (void*)Hook_DrawPrimitive) {
        EnterCriticalSection(&g_D3DLock);
        if (!g_InStateBlockRecord && (*(void***)dev)[81] != (void*)Hook_DrawPrimitive) {
            ApplyApiSetHooksLocked(dev, "BeginScene");
        }
        LeaveCriticalSection(&g_D3DLock);
    }
    return g_OrigBeginScene(dev);
}

static HRESULT STDMETHODCALLTYPE Hook_Reset(IDirect3DDevice9* dev, D3DPRESENT_PARAMETERS* pp) {
    EnterCriticalSection(&g_D3DLock);
    g_InStateBlockRecord = FALSE;
    HRESULT hr = g_OrigReset(dev, pp);
    ApplyApiSetHooksLocked(dev, "Reset");
    LeaveCriticalSection(&g_D3DLock);
    return hr;
}

static HRESULT STDMETHODCALLTYPE Hook_ResetEx(IDirect3DDevice9Ex* dev, D3DPRESENT_PARAMETERS* pp, D3DDISPLAYMODEEX* fsMode) {
    EnterCriticalSection(&g_D3DLock);
    g_InStateBlockRecord = FALSE;
    HRESULT hr = g_OrigResetEx(dev, pp, fsMode);
    ApplyApiSetHooksLocked((IDirect3DDevice9*)dev, "ResetEx");
    LeaveCriticalSection(&g_D3DLock);
    return hr;
}

static void ApplyApiSetHooksLocked(IDirect3DDevice9* dev, const char* reason) {
    if (!dev || g_InStateBlockRecord) return;
    void** vtbl = *(void***)dev;
    BOOL wasUnhooked = (vtbl[81] != (void*)Hook_DrawPrimitive);

    // Non-ApiSet lifecycle hooks (slots 16, 41, 60, 61, 132)
    PatchVtableSlot(vtbl, 16,  (void*)Hook_Reset,                       (void**)&g_OrigReset);
    PatchVtableSlot(vtbl, 41,  (void*)Hook_BeginScene,                  (void**)&g_OrigBeginScene);
    PatchVtableSlot(vtbl, 60,  (void*)Hook_BeginStateBlock,             (void**)&g_OrigBeginStateBlock);
    PatchVtableSlot(vtbl, 61,  (void*)Hook_EndStateBlock,               (void**)&g_OrigEndStateBlock);
    if (g_DeviceIsEx) {
        PatchVtableSlot(vtbl, 132, (void*)Hook_ResetEx,                 (void**)&g_OrigResetEx);
    }

    // ApiSet hooks (slots 77, 79, 81..84, 86, 91, 106)
    PatchVtableSlot(vtbl, 77,  (void*)Hook_SetSoftwareVertexProcessing, (void**)&g_OrigSetSoftwareVertexProcessing);
    PatchVtableSlot(vtbl, 79,  (void*)Hook_SetNPatchMode,               (void**)&g_OrigSetNPatchMode);
    PatchVtableSlot(vtbl, 81,  (void*)Hook_DrawPrimitive,               (void**)&g_OrigDrawPrimitive);
    PatchVtableSlot(vtbl, 82,  (void*)Hook_DrawIndexedPrimitive,        (void**)&g_OrigDrawIndexedPrimitive);
    PatchVtableSlot(vtbl, 83,  (void*)Hook_DrawPrimitiveUP,             (void**)&g_OrigDrawPrimitiveUP);
    PatchVtableSlot(vtbl, 84,  (void*)Hook_DrawIndexedPrimitiveUP,      (void**)&g_OrigDrawIndexedPrimitiveUP);
    PatchVtableSlot(vtbl, 86,  (void*)Hook_CreateVertexDeclaration,     (void**)&g_OrigCreateVertexDeclaration);
    PatchVtableSlot(vtbl, 91,  (void*)Hook_CreateVertexShader,          (void**)&g_OrigCreateVertexShader);
    PatchVtableSlot(vtbl, 106, (void*)Hook_CreatePixelShader,           (void**)&g_OrigCreatePixelShader);

    if (reason && wasUnhooked && g_RehookLogCount < 4) {
        g_RehookLogCount++;
        Log("[D3D9Fix] Re-applied IDirect3DDevice9 ApiSet hooks after %s on device %p\n", reason, dev);
    }
}

static void HookD3D9DeviceVtable(IDirect3DDevice9* dev, BOOL isEx) {
    if (!dev) return;
    EnterCriticalSection(&g_D3DLock);
    g_DeviceIsEx = isEx;
    g_InStateBlockRecord = FALSE;
    ApplyApiSetHooksLocked(dev, NULL);
    LeaveCriticalSection(&g_D3DLock);
    Log("[D3D9Fix] Hooked IDirect3DDevice9%s vtable on device %p (live-state + StateBlock guard active)\n",
        isEx ? "Ex" : "", dev);
}

static HRESULT STDMETHODCALLTYPE Hook_CreateDevice(IDirect3D9* d3d, UINT adapter, D3DDEVTYPE devType, HWND hwnd, DWORD flags, D3DPRESENT_PARAMETERS* pp, IDirect3DDevice9** ppDev) {
    flags &= ~D3DCREATE_PUREDEVICE; // ensure live Get* queries always succeed
    HRESULT hr = g_OrigCreateDevice(d3d, adapter, devType, hwnd, flags, pp, ppDev);
    if (SUCCEEDED(hr) && ppDev && *ppDev) {
        HookD3D9DeviceVtable(*ppDev, FALSE);
    }
    return hr;
}

static HRESULT STDMETHODCALLTYPE Hook_CreateDeviceEx(IDirect3D9Ex* d3d, UINT adapter, D3DDEVTYPE devType, HWND hwnd, DWORD flags, D3DPRESENT_PARAMETERS* pp, D3DDISPLAYMODEEX* fsMode, IDirect3DDevice9Ex** ppDev) {
    flags &= ~D3DCREATE_PUREDEVICE; // ensure live Get* queries always succeed
    HRESULT hr = g_OrigCreateDeviceEx(d3d, adapter, devType, hwnd, flags, pp, fsMode, ppDev);
    if (SUCCEEDED(hr) && ppDev && *ppDev) {
        HookD3D9DeviceVtable((IDirect3DDevice9*)*ppDev, TRUE);
    }
    return hr;
}

// ============================================================================
// PART 2: Game Engine Autosave & Quickload Hooks (default.xbe)
// ============================================================================

// Addresses in default.xbe (virtual addresses, XBE is mapped 1:1 in the process)
#define ADDR_SAVE_IMAGE         0x00572F40
#define ADDR_CHECKPOINT_BACKUP  0x007F1CA0
#define SIZE_SAVE_IMAGE         0x17460
#define OFFSET_PACKED_VALID     0x16813
#define ADDR_FIELD_PACKED_VALID 0x00589753   // byte (1 = mid-stage packed position/room valid)
#define ADDR_BACKUP_PACKED_VAL  0x008084B3   // byte (0x007F1CA0 + 0x16813: backup buffer PACKED_VALID)
#define ADDR_FIELD_DIFFICULTY   0x00589755   // byte (0 = Ninja Dog, 1 = Normal, 2 = Hard, 3 = Very Hard, 4 = Master Ninja)
#define ADDR_FIELD_CHAPTER      0x00589757   // byte (Saved Chapter ID inside 0x00572F40)
#define ADDR_FIELD_STATE_MODE   0x0058975A   // byte (1 = Alive, 2 = Dead/GameOver)
#define ADDR_FIELD_WIPE_FLAG    0x0058975B   // byte (non-zero wipes save image on 0x2ec1c0)
#define ADDR_FIELD_SAVED_ROOM   0x0058975E   // word (Saved Room ID packed by 0x2fbde0)
#define ADDR_FIELD_CHAP_TRANS   0x0058A389   // byte (1 = chapter transition)
#define ADDR_FIELD_SLOT_INDEX   0x0058A38A   // byte (save slot index, 0xFF = none)
#define ADDR_FIELD_SPAWN_POINT  0x0058A38C   // word (0x0200 = normal gameplay, < 0x0200 = demo/spawn)
#define ADDR_RYU_HP             0x0058A566   // word (Ryu current HP)
#define ADDR_RYU_MAX_KI         0x0058A56C   // word (Ryu live MaxKi)
#define ADDR_RYU_CUR_KI         0x0058A56E   // word (Ryu live CurKi)
#define ADDR_RYU_EQUIP_NINPO    0x0058A574   // word (Ryu live EquipNinpo)
#define ADDR_SAVE_MAX_KI        0x005895AC   // word (Save buffer MaxKi)
#define ADDR_SAVE_CUR_KI        0x005895AE   // word (Save buffer CurKi)
#define ADDR_SAVE_EQUIP_NINPO   0x005895BE   // word (Save buffer EquipNinpo)
#define ADDR_RYU_SPAWNED        0x0058A594   // byte (non-zero = Ryu actor spawned & active)
#define ADDR_RYU_MATRIX         0x004B4E50   // 4x4 float matrix (Ryu transform)
#define ADDR_RYU_POS            0x004B5710   // vec4 float (Ryu live world position)
#define ADDR_RYU_EVENT_LOCK     0x004B75DE   // byte (+ actorSlot * 0x2800: non-zero = cutscene/grab/scripted lock)
#define ADDR_ACTOR_SLOT_INDEX   0x00DB9C60   // byte (active player actor slot index, stride 0x2800)
#define ADDR_ROOM_TRANSITION    0x00D6A11E   // byte (1 = door/room transition in progress)
#define ADDR_LIVE_BGM_TRACK     0x00D5268E   // word (currently playing live BGM track)

#define ADDR_TASK1_STATE        0x007F1B12   // byte (0 = respawn Task 1, 1 = active gameplay, 2 = room load/popup)
#define ADDR_GLOBAL_STATE       0x00DB5A60   // byte (5 = Story Gameplay, 9 = Transition, 0x0C = Mission Gameplay)
#define ADDR_PAUSE_DEPTH        0x00DB5A68   // byte (0 = unpaused, >0 = pause menu open)
#define ADDR_STAGE_SUBSTATE     0x00DB9894   // byte (3 = active room gameplay, 0x80 = Game Over loop)
#define ADDR_CURRENT_ROOM       0x00DB9AC2   // word (current loaded Room ID, 0x0200 = none)
#define ADDR_LIVE_CHAPTER       0x00DB9AD4   // byte (live Chapter ID in active gameplay)
#define ADDR_STATE_TRIGGER      0x00DB9AD6   // byte (3/4 = stop tasks & trigger State 9 checkpoint load)
#define ADDR_CUTSCENE_STATE     0x008D3A50   // word (0xFFFF / 1 / 2 = cutscene playing per 0x001DBA70; 0 / 3 = finished)
#define ADDR_CUTSCENE_ID        0x00DB9C6E   // word (cutscene ID; NOT cleared to 0xFFFF after some cutscenes!)
#define ADDR_INTERACTION_LOCK   0x00D52B37   // byte (1 = door/chest/safe/shrine interaction active)
#define ADDR_SAVE_POOL          0x00C05FE8   // dword: heap used by the save routines while they run

// Xbox controller internal button bitmask in default.xbe (+0x08 into 0x78-byte pad struct; +0x00 is dwPacketNumber!)
#define ADDR_PAD_BTN_MASK       0x00D219A8
#define PAD_STRIDE              0x78
#define XBE_BTN_BACK            0x00000020
#define XBE_BTN_LTHUMB          0x00000040
#define XBE_BTN_RTHUMB          0x00000080
#define XBE_BTN_BLACK_RB        0x00001000
#define XBE_BTN_WHITE_LB        0x00002000

// Target engine routines
#define ADDR_FUNC_SAVE_FILE     0x0030F840
#define ADDR_FUNC_LOAD_FILE     0x00310050
#define ADDR_FUNC_PACK_PLAYER   0x002FBDE0   // packs Ryu pos/rot/HP/room into 0x572F40, sets [0x589753]=1
#define ADDR_FUNC_PACK_ROOM     0x002F1780   // packs current room doors/chests/objects into 0x572F40
#define ADDR_FUNC_PACK_GLOBAL   0x002F1820   // packs global flags/enemy states into 0x572F40
#define ADDR_COOKIE_CHECK       0x00379C29   // cmp ecx,[0x41ccd8] ; jne ; ret  (called on every function return)

// Hook sites
#define ADDR_HOOK_DOOR          0x002EF5CB   // Seamless door room update: mov [0xdb9ac2], bx (7 bytes)
#define ADDR_HOOK_ITEM          0x00154300   // Inventory item add/remove (6 bytes: 51 55 56 83 CA FF)
#define ADDR_HOOK_SHRINE_NEW    0x001DA15F   // Dragon statue / Chapter clear save (NEW slot): call 0x30f840 (5 bytes)
#define ADDR_HOOK_SHRINE_OVER   0x001DA1EE   // Dragon statue / Chapter clear save (OVERWRITE slot): call 0x30f840 (5 bytes)
#define ADDR_HOOK_CASE3_LOAD    0x0016656A   // State 9 Case 3/4 checkpoint load: call 0x16b680 (5 bytes)
#define ADDR_HOOK_GAMEOVER_TICK 0x002E08EA   // GameOver loop tick: call 0x2026f0 (5 bytes)
#define ADDR_HOOK_USE_SPIRIT    0x001E23D6   // Spirit of the Devils MaxKi write: mov [edx+1cc], ax (7 bytes)
#define ADDR_HOOK_UNPACK_KI     0x002FC270   // Stage unpack MaxKi write: mov [0x58a56c], cx (7 bytes)

// Global state
static volatile LONG g_PendingSave = 0;
static volatile LONG g_PendingLoad = 0;
static volatile LONG g_InPump = 0;
static volatile LONG g_AutoloadPending = 0;
static volatile DWORD g_GameTid = 0;

// Diagnostics: how often each hook fired (source ids for QueueSaveC)
#define SRC_ROOM   1
#define SRC_ITEM   2
#define SRC_SHRINE 3
static volatile LONG g_HookCount[4] = {0, 0, 0, 0};
static const char* const g_HookName[4] = { "?", "RoomEnter", "ItemGet", "ShrineSave" };
static volatile LONG g_PumpBusyLogTick = 0;
static volatile LONG g_SaveWaitLogTick = 0;
static volatile DWORD g_LastLoadTick = 0;
static volatile DWORD g_LastRoomSaveTick = 0;
static volatile DWORD g_ChapterStartTick = 0;
static WORD g_LastRoomId = 0xFFFF;
static BYTE g_CurrentChapter = 0;
static BYTE g_LastSavedChapter = 0;

// Game-thread detection fallback: while g_SampleActive, PumpC counts calls per thread.
#define MAX_SAMPLE 64
static volatile LONG g_SampleActive = 0;
static volatile LONG g_SampleTid[MAX_SAMPLE];
static volatile LONG g_SampleCnt[MAX_SAMPLE];

static void SampleThread() {
    LONG tid = (LONG)GetCurrentThreadId();
    for (int i = 0; i < MAX_SAMPLE; i++) {
        LONG t = g_SampleTid[i];
        if (t == 0) t = InterlockedCompareExchange(&g_SampleTid[i], tid, 0);
        if (t == 0 || t == tid) { InterlockedIncrement(&g_SampleCnt[i]); return; }
    }
}

static BOOL IsOurProcessForeground() {
    HWND fg = GetForegroundWindow();
    DWORD pid = 0;
    if (fg) GetWindowThreadProcessId(fg, &pid);
    return pid == GetCurrentProcessId();
}

static BOOL g_AutosaveValid = FALSE;
static char g_SlotPath[0x104] = {0};        // "U:\xxxxxxxxxxxx\" returned by the game
static WCHAR g_SaveName[0x104 / 2] = L"Autosave";
static char g_SlotFile[MAX_PATH] = {0};     // remembers g_SlotPath across game restarts

static void InitPaths() {
    GetFullPathNameA("autosave_slot.txt", MAX_PATH, g_SlotFile, NULL);
    FILE* f = fopen(g_SlotFile, "r");
    if (f) {
        char buf[0x104] = {0};
        if (fgets(buf, sizeof(buf), f)) {
            size_t n = strlen(buf);
            while (n && (buf[n-1] == '\n' || buf[n-1] == '\r')) buf[--n] = 0;
            if (n > 2) { memcpy(g_SlotPath, buf, n + 1); g_AutosaveValid = TRUE; }
        }
        fclose(f);
    }
    Log("[Autosave] Slot file: %s, remembered slot: '%s'\n", g_SlotFile, g_SlotPath);
}

static LONG ExcFilter(EXCEPTION_POINTERS* ep, const char* where) {
    Log("[Autosave] EXCEPTION in %s: code=0x%08X at 0x%p\n", where,
        ep->ExceptionRecord->ExceptionCode, ep->ExceptionRecord->ExceptionAddress);
    return EXCEPTION_EXECUTE_HANDLER;
}

static BOOL IsInActiveGameplayFrame() {
    BYTE gstate = *(BYTE*)ADDR_GLOBAL_STATE;
    if (gstate != 5 && gstate != 0x0C) return FALSE;
    if (*(BYTE*)ADDR_TASK1_STATE != 1) return FALSE;
    if (*(BYTE*)ADDR_STAGE_SUBSTATE != 3) return FALSE;
    if (*(BYTE*)ADDR_RYU_SPAWNED == 0) return FALSE;
    return TRUE;
}

static BOOL IsCutscenePlayingNow() {
    // Matches default.xbe's native IsCutscenePlaying() at 0x001DBA70:
    // 0x00DB9C6E retains finished cutscene IDs in Chapter 5 when 0x001DD7E2 / 0x001DC099 exits directly!
    WORD csState = *(WORD*)ADDR_CUTSCENE_STATE;
    return (csState == 0xFFFF || csState == 1 || csState == 2);
}

// Checks if the game is currently in unpaused, active gameplay where packing & saving Ryu's state is safe.
static BOOL IsSafeToSaveNow(const char** outBlockReason = NULL) {
    #define FAIL_SAVE(why) do { if (outBlockReason) *outBlockReason = why; return FALSE; } while (0)

    BYTE gstate = *(BYTE*)ADDR_GLOBAL_STATE;
    if (gstate != 5 && gstate != 0x0C) FAIL_SAVE("GlobalState!=5/0xC");
    if (*(BYTE*)ADDR_TASK1_STATE != 1) FAIL_SAVE("Task1State!=1");
    if (*(BYTE*)ADDR_STAGE_SUBSTATE != 3) FAIL_SAVE("StageSubState!=3");
    if (*(BYTE*)ADDR_PAUSE_DEPTH != 0) FAIL_SAVE("Paused");
    if (*(BYTE*)ADDR_INTERACTION_LOCK != 0) FAIL_SAVE("InteractionLock");
    if (*(BYTE*)ADDR_RYU_SPAWNED == 0) FAIL_SAVE("RyuNotSpawned");
    if (*(WORD*)ADDR_RYU_HP == 0) FAIL_SAVE("RyuHP==0");
    if (*(BYTE*)ADDR_FIELD_STATE_MODE == 2) FAIL_SAVE("GameOverMode");
    if (IsCutscenePlayingNow()) FAIL_SAVE("CutsceneActive");
    if (*(BYTE*)ADDR_FIELD_CHAP_TRANS != 0) FAIL_SAVE("ChapTransActive");
    if (*(BYTE*)ADDR_ROOM_TRANSITION != 0) FAIL_SAVE("RoomTransition");
    if (*(BYTE*)ADDR_STATE_TRIGGER != 0) FAIL_SAVE("StateTrigger");

    BYTE actorSlot = *(BYTE*)ADDR_ACTOR_SLOT_INDEX;
    DWORD actorOff = (actorSlot < 4) ? ((DWORD)actorSlot * 0x2800u) : 0;
    if (*(BYTE*)(ADDR_RYU_EVENT_LOCK + actorOff) != 0) FAIL_SAVE("RyuEventLock");

    DWORD now = GetTickCount();
    if (now - g_ChapterStartTick < 2000) FAIL_SAVE("ChapterGracePeriod");
    if (now - g_LastLoadTick < 2000) FAIL_SAVE("QuickloadGracePeriod");

    WORD curRoom = *(WORD*)ADDR_CURRENT_ROOM;
    if (curRoom == 0x0200 || curRoom == 0xFFFF) FAIL_SAVE("InvalidRoom");

    float py = *(float*)(ADDR_RYU_POS + 4);
    if (py < -2000.0f) FAIL_SAVE("VoidY<-2000");

    #undef FAIL_SAVE
    return TRUE;
}

// Packs Ryu's live world position, rotation matrix, HP, inventory, and room objects into 0x00572F40,
// then writes the save buffer to disk via 0x0030F840. Must run on the game thread.
static BOOL DoAutosave() {
    __try {
        if (!IsSafeToSaveNow(NULL)) {
            return FALSE;
        }

        WORD curRoom = *(WORD*)ADDR_CURRENT_ROOM;
        WORD musicIdx = *(WORD*)0x005896EE;
        // Track 0x1E is specifically the chapter clear / save screen BGM. Never record 0x1E in gameplay!
        if (musicIdx == 0x1E || musicIdx >= 0x2F) {
            WORD liveBgm = *(WORD*)ADDR_LIVE_BGM_TRACK;
            if (liveBgm != 0x1E && liveBgm < 0x2F && liveBgm > 0) {
                musicIdx = liveBgm;
            } else {
                musicIdx = 0; // 0 lets the game pick stage room BGM dynamically
            }
        }

        // Pack live player state, room state, and global flags into ADDR_SAVE_IMAGE (0x00572F40)
        // Mirrors 0x002FD540 without calling 0x002FD580 (which would open the interactive save UI).
        __asm {
            push ADDR_RYU_MATRIX
            push ADDR_RYU_POS
            movzx edx, musicIdx
            mov eax, ADDR_FUNC_PACK_PLAYER
            call eax
            add esp, 8

            mov ax, curRoom
            mov ecx, ADDR_FUNC_PACK_ROOM
            call ecx

            mov eax, ADDR_FUNC_PACK_GLOBAL
            call eax
        }

        // Ensure mid-stage packed flags are set in the buffer for when the save is LOADED
        *(BYTE*)ADDR_FIELD_PACKED_VALID = 1;
        *(BYTE*)ADDR_FIELD_CHAP_TRANS   = 0;
        *(BYTE*)ADDR_FIELD_WIPE_FLAG    = 0;
        *(BYTE*)ADDR_FIELD_STATE_MODE   = 1;

        BYTE chapter = *(BYTE*)ADDR_FIELD_CHAPTER;
        BYTE difficulty = *(BYTE*)ADDR_FIELD_DIFFICULTY;
        WORD savedRoom = *(WORD*)ADDR_FIELD_SAVED_ROOM;
        float px = *(float*)(ADDR_RYU_POS + 0);
        float py = *(float*)(ADDR_RYU_POS + 4);
        float pz = *(float*)(ADDR_RYU_POS + 8);
        Log("[Autosave] Saving (Chapter %u, Diff %u, Room 0x%04X, Pos [%.1f, %.1f, %.1f], HP %u, BGM 0x%02X)...\n",
            chapter, difficulty, savedRoom, px, py, pz, *(WORD*)ADDR_RYU_HP, musicIdx);

        char pathOut[0x104];
        memset(pathOut, 0, sizeof(pathOut));
        WCHAR* name = g_SaveName;
        int res = -1;

        __asm {
            push 0
            push 0
            push SIZE_SAVE_IMAGE
            push ADDR_SAVE_IMAGE
            push name
            xor ecx, ecx
            lea edx, pathOut
            mov eax, ADDR_FUNC_SAVE_FILE
            call eax
            add esp, 0x14
            mov res, eax
        }

        // CRITICAL: Immediately restore live memory PACKED_VALID = 0 (and backup buffer too)!
        // PACKED_VALID = 1 is saved inside the file on disk for autoloading,
        // but live gameplay memory MUST have PACKED_VALID = 0 so doors/cutscenes (e.g. Han's Bar 0x002DF940) work!
        *(BYTE*)ADDR_FIELD_PACKED_VALID = 0;
        *(BYTE*)ADDR_BACKUP_PACKED_VAL  = 0;

        if (res == 0 && pathOut[0]) {
            strcpy_s(g_SlotPath, pathOut);
            g_LastSavedChapter = chapter;
            g_AutosaveValid = TRUE;
            FILE* f = fopen(g_SlotFile, "w");
            if (f) { fprintf(f, "%s\n", g_SlotPath); fclose(f); }
            Log("[Autosave] Save successful -> %s\n", g_SlotPath);
            return TRUE;
        }
        Log("[Autosave] Save failed, code %d, path '%s'\n", res, pathOut);
    } __except (ExcFilter(GetExceptionInformation(), "DoAutosave")) {
        *(BYTE*)ADDR_FIELD_PACKED_VALID = 0;
        *(BYTE*)ADDR_BACKUP_PACKED_VAL  = 0;
    }
    return FALSE;
}

// Intercepts State 9 Case 3/4 checkpoint file loader (0x0016656A).
extern "C" int __cdecl Hook_CheckpointLoad_Impl(int slotIdx) {
    if (g_AutoloadPending) {
        if (!g_AutosaveValid || !g_SlotPath[0]) {
            Log("[Autosave] Autoload requested but no valid slot exists\n");
            g_AutoloadPending = 0;
            return 0;
        }
        Log("[Autosave] State 9 Case 4: loading autosave from '%s' into 0x00572F40...\n", g_SlotPath);
        const char* path = g_SlotPath;
        int res = -1;
        __asm {
            push 0
            push SIZE_SAVE_IMAGE
            push ADDR_SAVE_IMAGE
            push path
            xor edx, edx
            xor ecx, ecx
            mov eax, ADDR_FUNC_LOAD_FILE
            call eax
            add esp, 0x10
            mov res, eax
        }
        if (res == 0) {
            BYTE loadedChapter = *(BYTE*)ADDR_FIELD_CHAPTER;
            WORD savedRoom     = *(WORD*)ADDR_FIELD_SAVED_ROOM;
            WORD spawnId       = *(WORD*)ADDR_FIELD_SPAWN_POINT;
            BYTE wasPacked     = *(BYTE*)ADDR_FIELD_PACKED_VALID;

            // Ensure state mode is Alive and normal gameplay spawn mode (0x0200)
            *(BYTE*)ADDR_FIELD_STATE_MODE   = 1;
            *(BYTE*)ADDR_FIELD_WIPE_FLAG    = 0;
            *(BYTE*)ADDR_FIELD_SLOT_INDEX   = 0;
            if (wasPacked) {
                *(BYTE*)ADDR_FIELD_PACKED_VALID = 1;
                *(BYTE*)ADDR_FIELD_CHAP_TRANS   = 0;
            }

            // Synchronize checkpoint backup buffer (0x007F1CA0) with the loaded image,
            // keeping backup PACKED_VALID cleared so native checkpoint restores stay clean.
            WORD* pSaveMaxKi = (WORD*)ADDR_SAVE_MAX_KI;
            WORD* pSaveCurKi = (WORD*)ADDR_SAVE_CUR_KI;
            WORD* pSaveNinpo = (WORD*)ADDR_SAVE_EQUIP_NINPO;
            if (*pSaveNinpo != 0 && *pSaveNinpo != 0xFFFF && *pSaveMaxKi < 200) {
                *pSaveMaxKi = 400;
                *pSaveCurKi = 400;
                Log("[Autosave] [LoadImage] Repaired zeroed MaxKi/CurKi in save buffer -> 400\n");
            }

            memcpy((void*)ADDR_CHECKPOINT_BACKUP, (void*)ADDR_SAVE_IMAGE, SIZE_SAVE_IMAGE);
            *(BYTE*)ADDR_BACKUP_PACKED_VAL = 0;

            // Use Case 4 ([0x00DB9AD6] = 4) so 0x00166595 skips incrementing death count [0x00589414]
            *(BYTE*)ADDR_STATE_TRIGGER = 4;

            g_LastLoadTick    = GetTickCount();
            g_LastRoomId      = savedRoom;
            g_CurrentChapter  = loadedChapter;
            g_AutoloadPending = 0;

            Log("[Autosave] Autoload successful (Chapter %u, Room 0x%04X, Spawn 0x%04X, Packed %u) -> resuming via State 9 -> State 5\n",
                loadedChapter, savedRoom, spawnId, wasPacked);
            return 1;
        }
        Log("[Autosave] Autoload failed with code: %d\n", res);
        g_AutoloadPending = 0;
        return 0;
    }

    // Normal checkpoint load: call original 0x0016B680
    typedef int (__cdecl *PFN_LoadCheckpoint)(int);
    return ((PFN_LoadCheckpoint)0x0016B680)(slotIdx);
}

extern "C" void __cdecl QueueSaveC(int src) {
    DWORD tid = GetCurrentThreadId();   // these hooks all fire on the game thread
    g_GameTid = tid;

    // Suppress only if end-of-chapter transition flag is active; otherwise queue and let PumpC wait until settled!
    if (*(BYTE*)ADDR_FIELD_CHAP_TRANS != 0) {
        Log("[Autosave] [Hook:%s] suppressed (chapter transition active)\n", g_HookName[src & 3]);
        return;
    }

    DWORD now = GetTickCount();
    if (src == SRC_ROOM) {
        // Debounce back-to-back duplicate notifications for the same door
        if (now - g_LastRoomSaveTick < 1500) {
            return;
        }
        g_LastRoomSaveTick = now;
    }

    LONG n = InterlockedIncrement(&g_HookCount[src & 3]);
    Log("[Autosave] [Hook:%s] fired #%d on thread %u -> queue save\n",
        g_HookName[src & 3], n, tid);
    InterlockedExchange(&g_PendingSave, 1);
}

// Called on the game thread from the cookie-check hook (hot path: keep the early-outs cheap).
extern "C" void __cdecl PumpC() {
    if (g_SampleActive) SampleThread();
    if (g_GameTid == 0) {
        if (IsInActiveGameplayFrame()) {
            g_GameTid = GetCurrentThreadId();
            Log("[Autosave] [Detect] Game thread auto-bound from active gameplay = %u\n", g_GameTid);
        } else {
            return;
        }
    } else if (GetCurrentThreadId() != g_GameTid) {
        return;
    }
    if (g_InPump) return;

    BYTE gstate   = *(BYTE*)ADDR_GLOBAL_STATE;
    BYTE subState = *(BYTE*)ADDR_STAGE_SUBSTATE;
    DWORD now     = GetTickCount();

    // CRITICAL FIX FOR HAN'S BAR / CUTSCENE DOORS:
    // Clear PACKED_VALID on the VERY FIRST active gameplay frame (NEVER gated behind grace period timers!).
    // STAGE_UNPACK / UNPACK_PLAYER (0x002FC110) already consumed PACKED_VALID while Task1State == 0.
    // Leaving PACKED_VALID == 1 during the 3-8s grace period caused 0x002DF940 (Han's Bar door) to skip
    // cutscene/geometry setup and drop Ryu into an infinite void fall!
    if (IsInActiveGameplayFrame()) {
        if (*(BYTE*)ADDR_FIELD_PACKED_VALID != 0) {
            *(BYTE*)ADDR_FIELD_PACKED_VALID = 0;
        }
        if (*(BYTE*)ADDR_BACKUP_PACKED_VAL != 0) {
            *(BYTE*)ADDR_BACKUP_PACKED_VAL = 0;
        }

        // 1. Live Chapter Change Detection (using real live chapter 0x00DB9AD4, NOT difficulty 0x00589755!)
        BYTE curChapter = *(BYTE*)ADDR_LIVE_CHAPTER;
        if (curChapter != 0) {
            if (g_CurrentChapter == 0) {
                g_CurrentChapter = curChapter;
                g_LastSavedChapter = curChapter;
                g_LastRoomId = *(WORD*)ADDR_CURRENT_ROOM;
                g_ChapterStartTick = now;
            } else if (curChapter != g_CurrentChapter) {
                Log("[Autosave] Chapter transition detected: Chapter %u -> Chapter %u\n", g_CurrentChapter, curChapter);
                g_CurrentChapter = curChapter;
                g_LastSavedChapter = curChapter;
                g_LastRoomId = *(WORD*)ADDR_CURRENT_ROOM;
                g_ChapterStartTick = now;
                // Queue an initial autosave for the newly entered chapter once settled!
                InterlockedExchange(&g_PendingSave, 1);
            }
        }

        // 2. Room Change Detection (catches both non-seamless 0x2DF930 and seamless 0x2EF3F0 doors)
        WORD curRoom = *(WORD*)ADDR_CURRENT_ROOM;
        if (curRoom != 0x0200 && curRoom != 0xFFFF) {
            if (g_LastRoomId == 0xFFFF || g_LastRoomId == 0x0200) {
                g_LastRoomId = curRoom;
            } else if (curRoom != g_LastRoomId) {
                WORD prevRoom = g_LastRoomId;
                g_LastRoomId = curRoom;
                Log("[Autosave] Room transition detected: 0x%04X -> 0x%04X (Chapter %u)\n",
                    prevRoom, curRoom, *(BYTE*)ADDR_LIVE_CHAPTER);
                QueueSaveC(SRC_ROOM);
            }
        }

        // 3. Ninpo / Ki Auto-Recovery Guard:
        // If player has equipped a Ninpo scroll (e.g. 0x009B) but MaxKi < 200 (corrupted/zeroed state),
        // auto-recover MaxKi to 400 (2 full slots) and refill CurKi to 400, syncing to save buffer!
        WORD curMaxKi = *(WORD*)ADDR_RYU_MAX_KI;
        WORD curEquipNinpo = *(WORD*)ADDR_RYU_EQUIP_NINPO;
        if (curEquipNinpo != 0 && curEquipNinpo != 0xFFFF && curMaxKi < 200) {
            *(WORD*)ADDR_RYU_MAX_KI = 400;
            *(WORD*)ADDR_RYU_CUR_KI = 400;
            *(WORD*)ADDR_SAVE_MAX_KI = 400;
            *(WORD*)ADDR_SAVE_CUR_KI = 400;
            Log("[Autosave] [KiGuard] Auto-recovered zeroed MaxKi/CurKi -> 400 (Ninpo: 0x%04X, 2 slots)\n", curEquipNinpo);
            InterlockedExchange(&g_PendingSave, 1);
        }
    }

    if (!(g_PendingSave | g_PendingLoad)) return;

    // Never allow a Quickload request pressed on Title / Load Game / Cutscene menus to stay armed as a trap!
    if (g_PendingLoad && gstate != 5 && gstate != 0x0C && subState != 0x80) {
        if (InterlockedCompareExchange(&g_PendingLoad, 0, 1) == 1) {
            Log("[Autosave] Discarded Quickload request outside gameplay/GameOver (GlobalState=%u, SubState=0x%02X)\n",
                gstate, subState);
        }
        if (!g_PendingSave) return;
    }

    // Never interrupt the game's own save routine (it owns the global pool while running)
    DWORD pool = *(volatile DWORD*)ADDR_SAVE_POOL;
    if (pool != 0) {
        if ((LONG)now - g_PumpBusyLogTick > 2000) {
            g_PumpBusyLogTick = (LONG)now;
            Log("[Autosave] [Pump] request pending but save pool busy (0x%08X) - waiting\n", pool);
        }
        return;
    }

    g_InPump = 1;
    if (g_PendingLoad) {
        BYTE taskState = *(BYTE*)ADDR_TASK1_STATE;
        BYTE pauseDep  = *(BYTE*)ADDR_PAUSE_DEPTH;
        BYTE stateMode = *(BYTE*)ADDR_FIELD_STATE_MODE;

        if (subState == 0x80) {
            // Inside Game Over screen (0x002E06E0): Hook_GameOver_Tick_Stub (0x002E08EA) will consume g_PendingLoad.
        } else if ((gstate == 5 || gstate == 0x0C) && taskState == 1 && subState == 3 && pauseDep == 0 && stateMode != 2) {
            if (InterlockedCompareExchange(&g_PendingLoad, 0, 1) == 1) {
                InterlockedExchange(&g_PendingSave, 0);
                if (!g_AutosaveValid || !g_SlotPath[0]) {
                    Log("[Autosave] Quickload requested in gameplay, but no valid autosave slot exists.\n");
                } else {
                    g_AutoloadPending = 1;
                    *(BYTE*)ADDR_STATE_TRIGGER = 4;
                    Log("[Autosave] Quickload armed in active gameplay (StateTrigger=4, slot='%s')\n", g_SlotPath);
                }
            }
        }
    } else if (g_PendingSave) {
        const char* blockWhy = NULL;
        if (IsSafeToSaveNow(&blockWhy)) {
            if (InterlockedCompareExchange(&g_PendingSave, 0, 1) == 1) {
                DoAutosave();
            }
        } else if ((LONG)now - g_SaveWaitLogTick > 3000) {
            g_SaveWaitLogTick = (LONG)now;
            Log("[Autosave] [Pump] queued save waiting for safe state (%s)\n", blockWhy ? blockWhy : "?");
        }
    }
    g_InPump = 0;
}

// Trampolines & Hooks

// 1. Seamless door transition room update at 0x002EF5CB (7 bytes replaced)
// Original: 66 89 1D C2 9A DB 00 (mov word ptr [0x00DB9AC2], bx)
static void __declspec(naked) Hook_DoorEnter_Stub() {
    __asm {
        mov word ptr ds:[0x00DB9AC2], bx
        cmp byte ptr ds:[0x0058A389], 0
        jne SkipDoorSave
        pushad
        pushfd
        mov g_LastRoomId, bx
        push SRC_ROOM
        call QueueSaveC
        add esp, 4
        popfd
        popad
    SkipDoorSave:
        push 0x002EF5D2
        ret
    }
}

// 2. Inventory item acquisition / Chest & Safe reward hook at 0x00154300 (6 bytes replaced)
// Original: 51 55 56 83 CA FF (push ecx; push ebp; push esi; or edx, 0xffffffff)
// Args: eax = item_id, ebx = count (> 0 when acquiring an item, < 0 when removing/consuming)
static void __declspec(naked) Hook_ItemGet_Stub() {
    __asm {
        test ebx, ebx
        jle SkipItemSave
        cmp byte ptr ds:[0x00DB5A60], 5
        jne SkipItemSave
        cmp byte ptr ds:[0x0058A389], 0
        jne SkipItemSave
        cmp byte ptr ds:[0x0058A594], 0
        je SkipItemSave
        cmp word ptr ds:[0x008D3A50], 0xFFFF
        je SkipItemSave
        cmp word ptr ds:[0x008D3A50], 1
        je SkipItemSave
        cmp word ptr ds:[0x008D3A50], 2
        je SkipItemSave
        cmp byte ptr ds:[0x00D6A11E], 0
        jne SkipItemSave
        cmp byte ptr ds:[0x00DB5A68], 0
        jne SkipItemSave
        cmp byte ptr ds:[0x00DB9AD6], 0
        jne SkipItemSave
        cmp byte ptr ds:[0x007F1B12], 1
        jne SkipItemSave
        cmp byte ptr ds:[0x00DB9894], 3
        jne SkipItemSave

        pushad
        pushfd
        push SRC_ITEM
        call QueueSaveC
        add esp, 4
        popfd
        popad
    SkipItemSave:
        push ecx
        push ebp
        push esi
        or edx, 0xFFFFFFFF
        push 0x00154306
        ret
    }
}

// 3a & 3b. Dragon Statue / Chapter Clear save hooks at BOTH 0x001DA15F (new slot) and 0x001DA1EE (overwrite slot)
extern "C" void __cdecl Hook_ShrineSave_Callback(int res, const char* pathOut) {
    if (res == 0 && pathOut && pathOut[0]) {
        strcpy_s(g_SlotPath, pathOut);
        g_AutosaveValid = TRUE;
        g_LastSavedChapter = *(BYTE*)ADDR_FIELD_CHAPTER;
        FILE* f = fopen(g_SlotFile, "w");
        if (f) { fprintf(f, "%s\n", g_SlotPath); fclose(f); }
        Log("[Autosave] [NativeSave] Saved to slot '%s' (Chapter %u, Diff %u, Room 0x%04X, ChapTrans %u)\n",
            g_SlotPath, *(BYTE*)ADDR_FIELD_CHAPTER, *(BYTE*)ADDR_FIELD_DIFFICULTY,
            *(WORD*)ADDR_FIELD_SAVED_ROOM, *(BYTE*)ADDR_FIELD_CHAP_TRANS);
    }
    // Cancel any pending pre-transition autosave so next chapter starts clean
    InterlockedExchange(&g_PendingSave, 0);
    InterlockedIncrement(&g_HookCount[SRC_SHRINE]);
}

static void __declspec(naked) Hook_ShrineSaveNew_Stub() {
    __asm {
        mov eax, 0x0030F840
        call eax
        pushad
        pushfd
        push esi              // pathOut
        push eax              // res
        call Hook_ShrineSave_Callback
        add esp, 8
        popfd
        popad
        push 0x001DA164
        ret
    }
}

static void __declspec(naked) Hook_ShrineSaveOver_Stub() {
    __asm {
        mov eax, 0x0030F840
        call eax
        pushad
        pushfd
        push esi              // pathOut
        push eax              // res
        call Hook_ShrineSave_Callback
        add esp, 8
        popfd
        popad
        push 0x001DA1F3
        ret
    }
}

// 4. Runs on every function return in the game (all threads); only acts on the game thread.
// Original at 0x00379C29: 3B 0D D8 CC 41 00 (cmp ecx, dword ptr [0x0041CCD8])
static void __declspec(naked) Hook_Pump_Stub() {
    __asm {
        pushad
        pushfd
        call PumpC
        popfd
        popad
        cmp ecx, dword ptr ds:[0x0041CCD8]
        push 0x00379C2F
        ret
    }
}

// 5. Intercepts State 9 Case 3/4 checkpoint load at 0x0016656A (5 bytes replaced)
// Original: E8 11 51 00 00 (call 0x0016B680)
static void __declspec(naked) Hook_Case3_Load_Stub() {
    __asm {
        push dword ptr [esp + 4]
        call Hook_CheckpointLoad_Impl
        add esp, 4
        ret
    }
}

// 6. Intercepts Game Over loop tick at 0x002E08EA (5 bytes replaced)
// Original: E8 01 1E F2 FF (call 0x2026f0)
static void __declspec(naked) Hook_GameOver_Tick_Stub() {
    __asm {
        mov eax, 0x002026F0
        call eax

        cmp g_PendingLoad, 1
        je TriggerGameOverQuickLoad
        cmp g_AutoloadPending, 1
        je TriggerGameOverQuickLoad

        push 0x002E08EF
        ret

    TriggerGameOverQuickLoad:
        mov g_PendingLoad, 0
        mov g_AutoloadPending, 1

        // Ensure [0x0058A38A] != 0xFF so 0x002E0C9F takes Continue branch (bl = 1) instead of Title (bl = 3)
        cmp byte ptr ds:[0x0058A38A], 0xFF
        jne SlotIndexOk
        mov byte ptr ds:[0x0058A38A], 0
    SlotIndexOk:
        xor edi, edi
        xor ebx, ebx
        mov dword ptr [esp + 0x18], 2
        push 0x002E0B87
        ret
    }
}

// 7. Spirit of the Devils (0x001E2390) hook at 0x001E23D6 (7 bytes replaced)
// Original engine bug: UseSpiritOfTheDevils only increments MaxKi (+200) but never refills CurKi.
// If Ryu's CurKi was 0, after consuming Spirit of the Devils, CurKi remains 0, leaving HUD flame unlit.
// We intercept the MaxKi write, set MaxKi, auto-refill CurKi += 200 (clamped to MaxKi), and sync save buffer!
extern "C" void __cdecl Hook_UseSpirit_Callback(void* ryuBase, WORD newMaxKi) {
    WORD* pMaxKi = (WORD*)((BYTE*)ryuBase + 0x1cc);
    WORD* pCurKi = (WORD*)((BYTE*)ryuBase + 0x1ce);
    *pMaxKi = newMaxKi;

    WORD cur = *pCurKi;
    cur += 200;
    if (cur > newMaxKi) cur = newMaxKi;
    *pCurKi = cur;

    *(WORD*)ADDR_SAVE_MAX_KI = newMaxKi;
    *(WORD*)ADDR_SAVE_CUR_KI = cur;

    Log("[Autosave] [SpiritOfDevils] Used: MaxKi updated to %u, CurKi refilled to %u (slots: %u)\n",
        newMaxKi, cur, newMaxKi / 200);
}

static void __declspec(naked) Hook_UseSpirit_Stub() {
    __asm {
        pushad
        pushfd
        movzx eax, ax            // newMaxKi
        push eax
        push edx                 // ryuBase (edx = 0x0058A3A0)
        call Hook_UseSpirit_Callback
        add esp, 8
        popfd
        popad
        ret
    }
}

// 8. Stage unpack player stats hook at 0x002FC270 (7 bytes replaced)
// Intercepts stage loading (Title Screen Load Game, Shrine load, Checkpoint load)
// whenever save data is unpacked into Ryu live memory (0x0058A56C / 0x0058A56E).
extern "C" void __cdecl Hook_UnpackStats_Callback(WORD liveEquipNinpo, WORD saveMaxKi) {
    WORD maxKi = saveMaxKi;
    WORD curKi = *(WORD*)ADDR_RYU_CUR_KI;

    // If player has Ninpo equipped/unlocked, but MaxKi was zeroed, repair it immediately!
    if (liveEquipNinpo != 0 && liveEquipNinpo != 0xFFFF) {
        if (maxKi < 200) {
            maxKi = 400; // 2 slots
            curKi = 400; // 2 filled slots
            *(WORD*)ADDR_SAVE_MAX_KI = maxKi;
            *(WORD*)ADDR_SAVE_CUR_KI = curKi;
            *(WORD*)ADDR_RYU_CUR_KI  = curKi;
            Log("[Autosave] [UnpackHook] Repaired zeroed stats -> MaxKi=400, CurKi=400 (Ninpo: 0x%04X)\n", liveEquipNinpo);
        }
    }
    *(WORD*)ADDR_RYU_MAX_KI = maxKi;
}

static void __declspec(naked) Hook_UnpackStats_Stub() {
    __asm {
        pushad
        pushfd
        movzx ecx, cx            // saveMaxKi
        push ecx
        movzx eax, ax            // liveEquipNinpo
        push eax
        call Hook_UnpackStats_Callback
        add esp, 8
        popfd
        popad
        ret
    }
}

static BOOL BytesMatch(DWORD addr, const BYTE* expect, int n) {
    __try {
        return memcmp((void*)addr, expect, n) == 0;
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        return FALSE;
    }
}

// Only patch once the XBE code at the hook sites is really mapped and unmodified
static BOOL HookSitesReady() {
    static const BYTE door[7]      = { 0x66, 0x89, 0x1D, 0xC2, 0x9A, 0xDB, 0x00 };
    static const BYTE item[6]      = { 0x51, 0x55, 0x56, 0x83, 0xCA, 0xFF };
    static const BYTE shrine[1]    = { 0xE8 };
    static const BYTE cookie[6]    = { 0x3B, 0x0D, 0xD8, 0xCC, 0x41, 0x00 };
    static const BYTE case3[5]     = { 0xE8, 0x11, 0x51, 0x00, 0x00 };
    static const BYTE gameOver[5]  = { 0xE8, 0x01, 0x1E, 0xF2, 0xFF };
    static const BYTE spirit[7]    = { 0x66, 0x89, 0x82, 0xCC, 0x01, 0x00, 0x00 };
    static const BYTE unpack[7]    = { 0x66, 0x89, 0x0D, 0x6C, 0xA5, 0x58, 0x00 };
    return BytesMatch(ADDR_HOOK_DOOR, door, 7) &&
           BytesMatch(ADDR_HOOK_ITEM, item, 6) &&
           BytesMatch(ADDR_HOOK_SHRINE_NEW, shrine, 1) &&
           BytesMatch(ADDR_HOOK_SHRINE_OVER, shrine, 1) &&
           BytesMatch(ADDR_COOKIE_CHECK, cookie, 6) &&
           BytesMatch(ADDR_HOOK_CASE3_LOAD, case3, 5) &&
           BytesMatch(ADDR_HOOK_GAMEOVER_TICK, gameOver, 5) &&
           BytesMatch(ADDR_HOOK_USE_SPIRIT, spirit, 7) &&
           BytesMatch(ADDR_HOOK_UNPACK_KI, unpack, 7);
}

static BOOL IsMapped(DWORD addr) {
    MEMORY_BASIC_INFORMATION mbi;
    return VirtualQuery((void*)addr, &mbi, sizeof(mbi)) && mbi.State == MEM_COMMIT;
}

static void PatchJump5(DWORD siteAddr, void* stubFn) {
    DWORD oldProtect;
    VirtualProtect((void*)siteAddr, 8, PAGE_EXECUTE_READWRITE, &oldProtect);
    BYTE jmp[5] = { 0xE9, 0, 0, 0, 0 };
    DWORD rel = (DWORD)stubFn - (siteAddr + 5);
    memcpy(&jmp[1], &rel, 4);
    memcpy((void*)siteAddr, jmp, 5);
    VirtualProtect((void*)siteAddr, 8, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)siteAddr, 8);
}

void InstallHooks() {
    DWORD oldProtect;
    Log("[Autosave] Installing game engine hooks...\n");

    // 1. Seamless door transition room update (0x002EF5CB), 7 bytes replaced (5-byte jmp + 2 NOPs)
    VirtualProtect((void*)ADDR_HOOK_DOOR, 16, PAGE_EXECUTE_READWRITE, &oldProtect);
    BYTE jmpDoor[7] = { 0xE9, 0, 0, 0, 0, 0x90, 0x90 };
    DWORD relDoor = (DWORD)Hook_DoorEnter_Stub - (ADDR_HOOK_DOOR + 5);
    memcpy(&jmpDoor[1], &relDoor, 4);
    memcpy((void*)ADDR_HOOK_DOOR, jmpDoor, 7);
    VirtualProtect((void*)ADDR_HOOK_DOOR, 16, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)ADDR_HOOK_DOOR, 16);

    // 2. Inventory item acquisition / Chest & Safe reward (0x00154300), 6 bytes replaced (5-byte jmp + 1 NOP)
    VirtualProtect((void*)ADDR_HOOK_ITEM, 16, PAGE_EXECUTE_READWRITE, &oldProtect);
    BYTE jmpItem[6] = { 0xE9, 0, 0, 0, 0, 0x90 };
    DWORD relItem = (DWORD)Hook_ItemGet_Stub - (ADDR_HOOK_ITEM + 5);
    memcpy(&jmpItem[1], &relItem, 4);
    memcpy((void*)ADDR_HOOK_ITEM, jmpItem, 6);
    VirtualProtect((void*)ADDR_HOOK_ITEM, 16, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)ADDR_HOOK_ITEM, 16);

    // 3a & 3b. Shrine / Chapter Clear save: BOTH new-slot (0x001DA15F) and overwrite-slot (0x001DA1EE)
    PatchJump5(ADDR_HOOK_SHRINE_NEW,  (void*)Hook_ShrineSaveNew_Stub);
    PatchJump5(ADDR_HOOK_SHRINE_OVER, (void*)Hook_ShrineSaveOver_Stub);

    // 4. Cookie check (0x00379C29): atomic 8-byte compare-exchange on aligned 0x379C28..0x379C2F
    VirtualProtect((void*)0x00379C28, 8, PAGE_EXECUTE_READWRITE, &oldProtect);
    volatile LONGLONG* blk = (volatile LONGLONG*)0x00379C28;
    for (int tries = 0; tries < 100; tries++) {
        LONGLONG oldv = *blk;
        BYTE nb[8];
        memcpy(nb, &oldv, 8);
        nb[1] = 0xE9;
        DWORD relPump = (DWORD)Hook_Pump_Stub - (0x00379C29 + 5);
        memcpy(&nb[2], &relPump, 4);
        LONGLONG newv;
        memcpy(&newv, nb, 8);
        if (_InterlockedCompareExchange64(blk, newv, oldv) == oldv) break;
    }
    VirtualProtect((void*)0x00379C28, 8, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)0x00379C28, 8);

    // 5. State 9 Case 3/4 checkpoint load (0x0016656A), 5-byte call
    VirtualProtect((void*)ADDR_HOOK_CASE3_LOAD, 8, PAGE_EXECUTE_READWRITE, &oldProtect);
    BYTE callCase3[5] = { 0xE8, 0, 0, 0, 0 };
    DWORD relCase3 = (DWORD)Hook_Case3_Load_Stub - (ADDR_HOOK_CASE3_LOAD + 5);
    memcpy(&callCase3[1], &relCase3, 4);
    memcpy((void*)ADDR_HOOK_CASE3_LOAD, callCase3, 5);
    VirtualProtect((void*)ADDR_HOOK_CASE3_LOAD, 8, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)ADDR_HOOK_CASE3_LOAD, 8);

    // 6. Game Over loop tick (0x002E08EA), 5-byte jump
    PatchJump5(ADDR_HOOK_GAMEOVER_TICK, (void*)Hook_GameOver_Tick_Stub);

    // 7. Spirit of the Devils (0x001E23D6), 7 bytes replaced (5-byte call + 2 NOPs)
    VirtualProtect((void*)ADDR_HOOK_USE_SPIRIT, 16, PAGE_EXECUTE_READWRITE, &oldProtect);
    BYTE callSpirit[7] = { 0xE8, 0, 0, 0, 0, 0x90, 0x90 };
    DWORD relSpirit = (DWORD)Hook_UseSpirit_Stub - (ADDR_HOOK_USE_SPIRIT + 5);
    memcpy(&callSpirit[1], &relSpirit, 4);
    memcpy((void*)ADDR_HOOK_USE_SPIRIT, callSpirit, 7);
    VirtualProtect((void*)ADDR_HOOK_USE_SPIRIT, 16, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)ADDR_HOOK_USE_SPIRIT, 16);

    // 8. Stage unpack player Ki fix (0x002FC270), 7 bytes replaced (5-byte call + 2 NOPs)
    VirtualProtect((void*)ADDR_HOOK_UNPACK_KI, 16, PAGE_EXECUTE_READWRITE, &oldProtect);
    BYTE callUnpack[7] = { 0xE8, 0, 0, 0, 0, 0x90, 0x90 };
    DWORD relUnpack = (DWORD)Hook_UnpackStats_Stub - (ADDR_HOOK_UNPACK_KI + 5);
    memcpy(&callUnpack[1], &relUnpack, 4);
    memcpy((void*)ADDR_HOOK_UNPACK_KI, callUnpack, 7);
    VirtualProtect((void*)ADDR_HOOK_UNPACK_KI, 16, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)ADDR_HOOK_UNPACK_KI, 16);

    Log("[Autosave] [Verify] door=%02X item=%02X shrineNew=%02X shrineOver=%02X pump=%02X case3=%02X gameOver=%02X spirit=%02X unpack=%02X | PID=%u\n",
        *(BYTE*)ADDR_HOOK_DOOR, *(BYTE*)ADDR_HOOK_ITEM,
        *(BYTE*)ADDR_HOOK_SHRINE_NEW, *(BYTE*)ADDR_HOOK_SHRINE_OVER,
        *(BYTE*)ADDR_COOKIE_CHECK, *(BYTE*)ADDR_HOOK_CASE3_LOAD, *(BYTE*)ADDR_HOOK_GAMEOVER_TICK,
        *(BYTE*)ADDR_HOOK_USE_SPIRIT, *(BYTE*)ADDR_HOOK_UNPACK_KI,
        GetCurrentProcessId());
    Log("[Autosave] All hooks successfully installed!\n");
}

static BOOL DetectGameThread() {
    if (g_GameTid != 0) return TRUE;
    memset((void*)g_SampleTid, 0, sizeof(g_SampleTid));
    memset((void*)g_SampleCnt, 0, sizeof(g_SampleCnt));
    InterlockedExchange(&g_SampleActive, 1);
    Sleep(500);
    InterlockedExchange(&g_SampleActive, 0);

    int best = -1;
    for (int i = 0; i < MAX_SAMPLE; i++) {
        if (g_SampleTid[i] == 0) break;
        Log("[Autosave] [Detect] thread %d: %d pump calls in 500ms\n", g_SampleTid[i], g_SampleCnt[i]);
        if (best < 0 || g_SampleCnt[i] > g_SampleCnt[best]) best = i;
    }
    if (best < 0) {
        Log("[Autosave] [Detect] pump hook was NOT executed by any thread in 500ms\n");
        return FALSE;
    }
    g_GameTid = (DWORD)g_SampleTid[best];
    Log("[Autosave] [Detect] game thread assumed = %u\n", g_GameTid);
    return TRUE;
}

static void LogHookStats() {
    Log("[Autosave] [Stats] hooks fired: RoomEnter=%d ItemGet=%d ShrineSave=%d | gameTid=%u slotValid=%d pendingSave=%d pendingLoad=%d\n",
        g_HookCount[SRC_ROOM], g_HookCount[SRC_ITEM], g_HookCount[SRC_SHRINE],
        g_GameTid, g_AutosaveValid, g_PendingSave, g_PendingLoad);
}

// Poll Xbox controller state for two-button combinations:
//   Quick Load (same as F9): Back + RB (View + Right Shoulder) OR LS + RS (L3 + R3 thumbstick clicks)
//   Quick Save (same as F5): Back + LB (View + Left Shoulder)
// NOTE: Uses real XInputGetState (or corrected XBE button offset +0x08 at 0x00D219A8 — NEVER +0x00 which is dwPacketNumber!).
static void PollControllerCombos(BOOL* outLoadCombo, BOOL* outSaveCombo) {
    *outLoadCombo = FALSE;
    *outSaveCombo = FALSE;

    if (!g_XInputChecked) {
        g_XInputChecked = TRUE;
        const char* dlls[] = { "xinput1_4.dll", "xinput1_3.dll", "xinput9_1_0.dll" };
        for (int i = 0; i < 3 && !g_pfnXInputGetState; i++) {
            HMODULE hX = GetModuleHandleA(dlls[i]);
            if (!hX) hX = LoadLibraryA(dlls[i]);
            if (hX) {
                g_pfnXInputGetState = (PFN_XInputGetState)GetProcAddress(hX, "XInputGetState");
            }
        }
    }

    BOOL gotXInput = FALSE;
    if (g_pfnXInputGetState) {
        for (DWORD i = 0; i < 4; i++) {
            XINPUT_STATE_MINI st;
            if (g_pfnXInputGetState(i, &st) == 0) {
                gotXInput = TRUE;
                WORD w = st.Gamepad.wButtons;
                // XINPUT_GAMEPAD_BACK (0x0020) + XINPUT_GAMEPAD_RIGHT_SHOULDER (0x0200)
                // or XINPUT_GAMEPAD_LEFT_THUMB (0x0040) + XINPUT_GAMEPAD_RIGHT_THUMB (0x0080)
                if ((w & 0x0220) == 0x0220 || (w & 0x00C0) == 0x00C0) {
                    *outLoadCombo = TRUE;
                }
                // XINPUT_GAMEPAD_BACK (0x0020) + XINPUT_GAMEPAD_LEFT_SHOULDER (0x0100)
                if ((w & 0x0120) == 0x0120) {
                    *outSaveCombo = TRUE;
                }
            }
        }
    }

    // Fallback to XBE's internal button bitmask (+0x08 = 0x00D219A8) ONLY if XInput was unavailable
    if (!gotXInput) {
        __try {
            for (int port = 0; port < 4; port++) {
                DWORD btns = *(volatile DWORD*)(ADDR_PAD_BTN_MASK + port * PAD_STRIDE);
                if (btns == 0) continue;
                if ((btns & (XBE_BTN_BACK | XBE_BTN_BLACK_RB)) == (XBE_BTN_BACK | XBE_BTN_BLACK_RB) ||
                    (btns & (XBE_BTN_LTHUMB | XBE_BTN_RTHUMB)) == (XBE_BTN_LTHUMB | XBE_BTN_RTHUMB)) {
                    *outLoadCombo = TRUE;
                }
                if ((btns & (XBE_BTN_BACK | XBE_BTN_WHITE_LB)) == (XBE_BTN_BACK | XBE_BTN_WHITE_LB)) {
                    *outSaveCombo = TRUE;
                }
            }
        } __except (EXCEPTION_EXECUTE_HANDLER) {
        }
    }
}

// Background thread: waits for the XBE, installs hooks, polls hotkeys & Xbox controller combos
DWORD WINAPI MainWorkerThread(LPVOID lpParam) {
    InitPaths();
    Log("[Autosave] Waiting for XBE mapping at 0x00010000...\n");

    for (;;) {
        if (IsMapped(0x00010000) && IsMapped(ADDR_HOOK_DOOR) && IsMapped(ADDR_HOOK_ITEM) &&
            IsMapped(ADDR_HOOK_SHRINE_NEW) && IsMapped(ADDR_HOOK_SHRINE_OVER) &&
            IsMapped(0x00379C28) && IsMapped(ADDR_HOOK_CASE3_LOAD) &&
            IsMapped(ADDR_HOOK_GAMEOVER_TICK) && IsMapped(ADDR_HOOK_USE_SPIRIT) &&
            IsMapped(ADDR_HOOK_UNPACK_KI) && HookSitesReady()) break;
        Sleep(100);
    }

    Log("[Autosave] XBE detected! Installing hooks in 1 second...\n");
    Sleep(1000);
    if (!HookSitesReady()) {
        Log("[Autosave] Hook sites changed unexpectedly; hooks NOT installed.\n");
        return 0;
    }
    InstallHooks();
    DetectGameThread();

    BOOL wasSaveDown = FALSE;
    BOOL wasLoadDown = FALSE;
    int  padSaveHoldTicks = 0;
    int  padLoadHoldTicks = 0;

    for (;;) {
        Sleep(16); // ~60 Hz tick

        if (!IsOurProcessForeground()) {
            wasSaveDown = FALSE;
            wasLoadDown = FALSE;
            padSaveHoldTicks = 0;
            padLoadHoldTicks = 0;
            continue;
        }

        BOOL rawPadLoad = FALSE, rawPadSave = FALSE;
        PollControllerCombos(&rawPadLoad, &rawPadSave);

        // Require ~130ms (8 ticks) continuous hold on controller combos to prevent accidental combat misfires
        padSaveHoldTicks = rawPadSave ? (padSaveHoldTicks + 1) : 0;
        padLoadHoldTicks = rawPadLoad ? (padLoadHoldTicks + 1) : 0;
        BOOL padSave = (padSaveHoldTicks >= 8);
        BOOL padLoad = (padLoadHoldTicks >= 8);

        BOOL isSave = ((GetAsyncKeyState(VK_F5) & 0x8000) != 0) || padSave;
        if (isSave && !wasSaveDown) {
            BYTE gstate = *(BYTE*)ADDR_GLOBAL_STATE;
            if (gstate != 5 && gstate != 0x0C) {
                Log("[Autosave] [%s] Manual save ignored outside gameplay (GlobalState=%u)\n",
                    padSave ? "Pad:Back+LB" : "F5", gstate);
            } else {
                Log("[Autosave] [%s] Manual save requested (Chapter %u, game thread id %u)\n",
                    padSave ? "Pad:Back+LB" : "F5", *(BYTE*)ADDR_LIVE_CHAPTER, g_GameTid);
                LogHookStats();
                if (DetectGameThread()) {
                    InterlockedExchange(&g_PendingSave, 1);
                } else {
                    Log("[Autosave] Manual save ignored: game thread unknown\n");
                }
            }
        }
        wasSaveDown = isSave;

        BOOL isLoad = ((GetAsyncKeyState(VK_F9) & 0x8000) != 0) || padLoad;
        if (isLoad && !wasLoadDown) {
            BYTE gstate   = *(BYTE*)ADDR_GLOBAL_STATE;
            BYTE subState = *(BYTE*)ADDR_STAGE_SUBSTATE;
            // NEVER arm g_PendingLoad on Title / Load Game menus — only in active gameplay or Game Over!
            if (gstate != 5 && gstate != 0x0C && subState != 0x80) {
                Log("[Autosave] [%s] Quickload ignored outside gameplay/GameOver (GlobalState=%u, SubState=0x%02X)\n",
                    padLoad ? "Pad:Back+RB/LS+RS" : "F9", gstate, subState);
            } else {
                Log("[Autosave] [%s] Quickload requested (GlobalState=%u, GameOverState=%d, SubState=0x%02X)\n",
                    padLoad ? "Pad:Back+RB/LS+RS" : "F9",
                    gstate, *(BYTE*)ADDR_FIELD_STATE_MODE, subState);
                LogHookStats();
                if (DetectGameThread()) {
                    InterlockedExchange(&g_PendingLoad, 1);
                } else {
                    Log("[Autosave] Quickload ignored: game thread unknown\n");
                }
            }
        }
        wasLoadDown = isLoad;
    }
    return 0;
}

// ============================================================================
// PART 3: D3D9 Proxy Exports & DllMain
// ============================================================================

static void EnsureD3DLock() {
    if (!g_D3DLockInit) {
        InitializeCriticalSection(&g_D3DLock);
        g_D3DLockInit = TRUE;
    }
}

void LoadRealD3D9() {
    EnsureD3DLock();
    if (!g_hRealD3D9) {
        char sysPath[MAX_PATH];
        GetSystemDirectoryA(sysPath, MAX_PATH);
        strcat_s(sysPath, "\\d3d9.dll");
        g_hRealD3D9 = LoadLibraryA(sysPath);
        if (g_hRealD3D9) {
            g_pfnDirect3DCreate9 = (PFN_Direct3DCreate9)GetProcAddress(g_hRealD3D9, "Direct3DCreate9");
            g_pfnDirect3DCreate9Ex = (PFN_Direct3DCreate9Ex)GetProcAddress(g_hRealD3D9, "Direct3DCreate9Ex");
            Log("[Proxy] Real system d3d9.dll loaded from %s\n", sysPath);
        } else {
            Log("[Proxy] ERROR: Failed to load system d3d9.dll!\n");
        }
    }
}

extern "C" IDirect3D9* WINAPI Proxy_Direct3DCreate9(UINT SDKVersion) {
    LoadRealD3D9();
    if (g_pfnDirect3DCreate9) {
        IDirect3D9* d3d = g_pfnDirect3DCreate9(SDKVersion);
        if (d3d) {
            EnterCriticalSection(&g_D3DLock);
            void** vtbl = *(void***)d3d;
            PatchVtableSlot(vtbl, 16, (void*)Hook_CreateDevice, (void**)&g_OrigCreateDevice);
            LeaveCriticalSection(&g_D3DLock);
        }
        return d3d;
    }
    return NULL;
}

extern "C" HRESULT WINAPI Proxy_Direct3DCreate9Ex(UINT SDKVersion, IDirect3D9Ex** ppD3D) {
    LoadRealD3D9();
    if (g_pfnDirect3DCreate9Ex) {
        HRESULT hr = g_pfnDirect3DCreate9Ex(SDKVersion, ppD3D);
        if (SUCCEEDED(hr) && ppD3D && *ppD3D) {
            EnterCriticalSection(&g_D3DLock);
            void** vtbl = *(void***)(*ppD3D);
            PatchVtableSlot(vtbl, 16, (void*)Hook_CreateDevice,   (void**)&g_OrigCreateDevice);
            PatchVtableSlot(vtbl, 20, (void*)Hook_CreateDeviceEx, (void**)&g_OrigCreateDeviceEx);
            LeaveCriticalSection(&g_D3DLock);
        }
        return hr;
    }
    return E_FAIL;
}

// D3DPERF_* forwarders (PIX markers; harmless no-ops if the real function is missing)
extern "C" int WINAPI Proxy_D3DPERF_BeginEvent(DWORD col, LPCWSTR name) {
    LoadRealD3D9();
    typedef int (WINAPI *F)(DWORD, LPCWSTR);
    F f = g_hRealD3D9 ? (F)GetProcAddress(g_hRealD3D9, "D3DPERF_BeginEvent") : NULL;
    return f ? f(col, name) : 0;
}
extern "C" int WINAPI Proxy_D3DPERF_EndEvent() {
    LoadRealD3D9();
    typedef int (WINAPI *F)();
    F f = g_hRealD3D9 ? (F)GetProcAddress(g_hRealD3D9, "D3DPERF_EndEvent") : NULL;
    return f ? f() : 0;
}
extern "C" void WINAPI Proxy_D3DPERF_SetMarker(DWORD col, LPCWSTR name) {
    LoadRealD3D9();
    typedef void (WINAPI *F)(DWORD, LPCWSTR);
    F f = g_hRealD3D9 ? (F)GetProcAddress(g_hRealD3D9, "D3DPERF_SetMarker") : NULL;
    if (f) f(col, name);
}
extern "C" void WINAPI Proxy_D3DPERF_SetRegion(DWORD col, LPCWSTR name) {
    LoadRealD3D9();
    typedef void (WINAPI *F)(DWORD, LPCWSTR);
    F f = g_hRealD3D9 ? (F)GetProcAddress(g_hRealD3D9, "D3DPERF_SetRegion") : NULL;
    if (f) f(col, name);
}
extern "C" BOOL WINAPI Proxy_D3DPERF_QueryRepeatFrame() {
    LoadRealD3D9();
    typedef BOOL (WINAPI *F)();
    F f = g_hRealD3D9 ? (F)GetProcAddress(g_hRealD3D9, "D3DPERF_QueryRepeatFrame") : NULL;
    return f ? f() : FALSE;
}
extern "C" void WINAPI Proxy_D3DPERF_SetOptions(DWORD opt) {
    LoadRealD3D9();
    typedef void (WINAPI *F)(DWORD);
    F f = g_hRealD3D9 ? (F)GetProcAddress(g_hRealD3D9, "D3DPERF_SetOptions") : NULL;
    if (f) f(opt);
}
extern "C" DWORD WINAPI Proxy_D3DPERF_GetStatus() {
    LoadRealD3D9();
    typedef DWORD (WINAPI *F)();
    F f = g_hRealD3D9 ? (F)GetProcAddress(g_hRealD3D9, "D3DPERF_GetStatus") : NULL;
    return f ? f() : 0;
}

BOOL WINAPI DllMain(HINSTANCE hinstDLL, DWORD fdwReason, LPVOID lpvReserved) {
    if (fdwReason == DLL_PROCESS_ATTACH) {
        EnsureD3DLock();
        DisableThreadLibraryCalls(hinstDLL);
        Log("[Proxy] d3d9.dll Proxy Attached to Process PID=%d\n", GetCurrentProcessId());
        CreateThread(NULL, 0, MainWorkerThread, NULL, 0, NULL);
    } else if (fdwReason == DLL_PROCESS_DETACH) {
        if (g_log) {
            fclose(g_log);
            g_log = NULL;
        }
    }
    return TRUE;
}
