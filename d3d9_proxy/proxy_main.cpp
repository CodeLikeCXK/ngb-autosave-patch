#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <d3d9.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <intrin.h>
#include <math.h>

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
#define ADDR_RYU_EVENT_LOCK     0x004B75DE   // byte (Ryu Actor 0 lock/state byte, read directly without actorSlot offset)
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
// Note: 0x00D52B37 is set to 1 every frame in stage loop (0x002DF631) and must NOT be used as an interaction lock!
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
#define ADDR_HOOK_DOOR_INTERACT 0x002DF46E   // Pre-mutation trigger activation: cmp byte ptr [esi+0x24], 1; jne 0x2df47b (6 bytes)
// ADDR_HOOK_ITEM (0x00154300) and ADDR_HOOK_SOBJ_INTERACT (0x002DF57F) removed per user requirement:
// prevents undesirable autosaves during chests, levers, puzzles, or Chapter 6 chalice altar boss trigger.
#define ADDR_HOOK_SAVE_ENUM     0x001DA26D   // Save enum slot filter in 0x001da220 (11 bytes)
#define ADDR_HOOK_GAMEOVER_CONTINUE 0x002E0C9F // GameOver Continue slot check: cmp [0x58a38a], 0xff (7 bytes)
#define ADDR_HOOK_SHRINE_NEW    0x001DA15F   // Dragon statue / Chapter clear save (NEW slot): call 0x30f840 (5 bytes)
#define ADDR_HOOK_SHRINE_OVER   0x001DA1EE   // Dragon statue / Chapter clear save (OVERWRITE slot): call 0x30f840 (5 bytes)
#define ADDR_HOOK_CASE3_LOAD    0x0016656A   // State 9 Case 3/4 checkpoint load: call 0x16b680 (5 bytes)
#define ADDR_HOOK_GAMEOVER_TICK 0x002E08EA   // GameOver loop tick: call 0x2026f0 (5 bytes)
#define ADDR_HOOK_USE_SPIRIT    0x001E23D6   // Spirit of the Devils MaxKi write: mov [edx+1cc], ax (7 bytes)
#define ADDR_HOOK_UNPACK_KI     0x002FC270   // Stage unpack MaxKi write: mov [0x58a56c], cx (7 bytes)

// Difficulty unlock patch sites (0x001DB598 jump table entries for IsFeatureUnlocked)
#define ADDR_UNLOCK_HARD        0x001DB5B4   // Case 7 (Hard)
#define ADDR_UNLOCK_VERY_HARD   0x001DB5B8   // Case 8 (Very Hard)
#define ADDR_UNLOCK_MASTER_NINJA 0x001DB5BC  // Case 9 (Master Ninja)
#define ADDR_UNLOCK_TARGET_FUNC 0x001DB590   // mov eax, 1; ret

// Global state
static volatile LONG g_PendingSave = 0;
static volatile LONG g_PendingLoad = 0;
static volatile LONG g_InPump = 0;
static volatile LONG g_AutoloadPending = 0;
static volatile DWORD g_GameTid = 0;

// Diagnostics: how often each hook fired (source ids for QueueSaveC)
#define SRC_DOOR            1  // 开门进入下一个房间时 (Door Transition / Room Change)
#define SRC_CHAPTER_START   2  // 关卡开始时 (Level / Chapter Start)
#define SRC_ENEMY_ENCOUNTER 3  // 遭遇敌人时 (Enemy Encounter / Battle Start)
#define SRC_SHRINE          4  // 龙之雕像手动保存同步 (Dragon Shrine sync)
static volatile LONG g_HookCount[5] = {0, 0, 0, 0, 0};
static const char* const g_HookName[5] = { "Unknown", "DoorEnter", "ChapterStart", "Encounter", "ShrineSave" };
static volatile LONG g_PumpBusyLogTick = 0;
static volatile LONG g_SaveWaitLogTick = 0;
static volatile DWORD g_LastLoadTick = 0;
static volatile DWORD g_LastRoomSaveTick = 0;
static volatile DWORD g_LastEncounterSaveTick = 0;
static volatile DWORD g_ChapterStartTick = 0;
static volatile DWORD g_DoorInteractTick = 0;
static WORD g_LastRoomId = 0xFFFF;
static BYTE g_CurrentChapter = 0xFF;
static BYTE g_LastSavedChapter = 0xFF;
static int g_LastEnemyCount = 0;
static BOOL g_ChapterSavePending = FALSE;
static volatile LONG g_PendingSaveSrc = 0;

// Rolling pre-door snapshot: refreshed every ~350ms while gameplay is safe.
// This is the source image for the frozen per-door snapshot below.
static BYTE  g_PreDoorImage[SIZE_SAVE_IMAGE];
static BOOL  g_PreDoorImageValid = FALSE;
static DWORD g_LastSnapshotTick = 0;
static WORD  g_PreDoorRoom = 0xFFFF;
static float g_PreDoorPos[3] = {0};
static BYTE  g_PreDoorChapter = 0xFF;
static BYTE  g_PreDoorDiff = 0;
static WORD  g_PreDoorHP = 0;

// Previous full rolling snapshot (~350ms earlier). The door hook fires after
// the trigger state has already become 1, so the current rolling image can be
// from the activation/approach. The previous image is the closest snapshot
// that still has the door idle; use it as the true pre-trigger checkpoint.
static BYTE  g_PrevPreDoorImage[SIZE_SAVE_IMAGE];
static BOOL  g_PrevPreDoorImageValid = FALSE;
static DWORD g_PrevPreDoorTick = 0;
static WORD  g_PrevPreDoorRoom = 0xFFFF;
static float g_PrevPreDoorPos[3] = {0};
static BYTE  g_PrevPreDoorChapter = 0xFF;
static BYTE  g_PrevPreDoorDiff = 0;
static WORD  g_PrevPreDoorHP = 0;

// Frozen door-sequence snapshot: copied from g_PreDoorImage when a door
// interaction starts. SRC_DOOR saves always write this image, never the live
// state, so subsequent room-change events cannot overwrite the pre-door
// position with the position inside the destination room. The rolling snapshot
// above keeps updating independently, so chained doors still get fresh data.
static BYTE  g_DoorSaveImage[SIZE_SAVE_IMAGE];
static BOOL  g_DoorSaveValid = FALSE;
static WORD  g_DoorSaveRoom = 0xFFFF;
static float g_DoorSavePos[3] = {0};
static BYTE  g_DoorSaveChapter = 0xFF;
static BYTE  g_DoorSaveDiff = 0;
static WORD  g_DoorSaveHP = 0;
static DWORD g_DoorSaveCapturedTick = 0;
static volatile BOOL  g_DoorSeqActive = FALSE;
static volatile DWORD g_DoorSeqTick = 0;
static const BYTE*    g_DoorSeqTrig = NULL;
static BOOL           g_DoorSaveWritten = FALSE;
static volatile LONG  g_InSnapshot = 0;
// One-shot reset applied on the first active gameplay frame after a load, so
// the room-unpack pass cannot restore a stale "door already active" state.
static const BYTE*    g_PostLoadDoorTrig = NULL;
static WORD           g_PostLoadDoorRoom = 0xFFFF;
static volatile BOOL  g_PostLoadDoorResetPending = FALSE;
static volatile DWORD g_PostLoadDoorResetRoomTick = 0;
static volatile BOOL  g_PostLoadDoorCheckDone = TRUE;

// Counts active spawned enemies with HP > 0 in actor slots 1..63 (slot 0 is player Ryu)
static int GetActiveEnemyCount() {
    int count = 0;
    for (int i = 1; i < 64; i++) {
        DWORD actorBase = 0x0058A3A0 + (DWORD)i * 0x210;
        if (*(BYTE*)(actorBase + 0x1F4) != 0) { // is_spawned
            WORD hp = *(WORD*)(actorBase + 0x1CC);
            if (hp > 0 && hp != 0xFFFF) {
                count++;
            }
        }
    }
    return count;
}

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

static BOOL IsMapped(DWORD addr) {
    MEMORY_BASIC_INFORMATION mbi;
    return VirtualQuery((void*)addr, &mbi, sizeof(mbi)) && mbi.State == MEM_COMMIT;
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

static BOOL VerifySaveSlotOnDisk(const char* slotPath) {
    if (!slotPath || !slotPath[0]) return FALSE;
    const char* p = slotPath;
    if ((p[0] == 'U' || p[0] == 'u') && p[1] == ':' && (p[2] == '\\' || p[2] == '/')) {
        p += 3;
    }
    char subDir[64] = {0};
    int i = 0;
    while (*p && *p != '\\' && *p != '/' && i < 60) {
        subDir[i++] = *p++;
    }
    subDir[i] = 0;
    if (i == 0) return FALSE;

    char checkPath[MAX_PATH];
    sprintf_s(checkPath, "savedata\\Partition1\\UDATA\\5443000d\\%s\\save000.dat", subDir);
    DWORD attr = GetFileAttributesA(checkPath);
    if (attr == INVALID_FILE_ATTRIBUTES || (attr & FILE_ATTRIBUTE_DIRECTORY)) {
        return FALSE;
    }

    HANDLE hFile = CreateFileA(checkPath, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, OPEN_EXISTING, 0, NULL);
    if (hFile == INVALID_HANDLE_VALUE) {
        return FALSE;
    }
    DWORD sz = GetFileSize(hFile, NULL);
    CloseHandle(hFile);
    return (sz > 1000);
}

static BOOL ScanDiskForAutosaveSlot(char* outSlotPath, size_t maxLen) {
    char searchPattern[MAX_PATH];
    sprintf_s(searchPattern, "savedata\\Partition1\\UDATA\\5443000d\\*");
    WIN32_FIND_DATAA fd;
    HANDLE hFind = FindFirstFileA(searchPattern, &fd);
    if (hFind == INVALID_HANDLE_VALUE) return FALSE;

    BOOL found = FALSE;
    do {
        if ((fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) &&
            strcmp(fd.cFileName, ".") != 0 && strcmp(fd.cFileName, "..") != 0) {

            char metaPath[MAX_PATH];
            sprintf_s(metaPath, "savedata\\Partition1\\UDATA\\5443000d\\%s\\SaveMeta.xbx", fd.cFileName);

            FILE* mf = fopen(metaPath, "rb");
            if (mf) {
                BYTE metaBuf[256] = {0};
                size_t readBytes = fread(metaBuf, 1, sizeof(metaBuf) - 2, mf);
                fclose(mf);
                if (readBytes > 4) {
                    // Check UTF-16LE sequence for "Autosave"
                    static const BYTE needle[] = { 'A', 0, 'u', 0, 't', 0, 'o', 0, 's', 0, 'a', 0, 'v', 0, 'e', 0 };
                    BOOL match = FALSE;
                    for (size_t k = 0; k + sizeof(needle) <= readBytes; ++k) {
                        if (memcmp(metaBuf + k, needle, sizeof(needle)) == 0) {
                            match = TRUE;
                            break;
                        }
                    }
                    if (match) {
                        char datPath[MAX_PATH];
                        sprintf_s(datPath, "savedata\\Partition1\\UDATA\\5443000d\\%s\\save000.dat", fd.cFileName);
                        DWORD datAttr = GetFileAttributesA(datPath);
                        if (datAttr != INVALID_FILE_ATTRIBUTES && !(datAttr & FILE_ATTRIBUTE_DIRECTORY)) {
                            HANDLE hf = CreateFileA(datPath, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL, OPEN_EXISTING, 0, NULL);
                            if (hf != INVALID_HANDLE_VALUE) {
                                DWORD sz = GetFileSize(hf, NULL);
                                CloseHandle(hf);
                                if (sz > 1000) {
                                    sprintf_s(outSlotPath, maxLen, "U:\\%s\\", fd.cFileName);
                                    found = TRUE;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
        }
    } while (FindNextFileA(hFind, &fd));
    FindClose(hFind);
    return found;
}

static void InitPaths() {
    GetFullPathNameA("autosave_slot.txt", MAX_PATH, g_SlotFile, NULL);
    FILE* f = fopen(g_SlotFile, "r");
    if (f) {
        char buf[0x104] = {0};
        if (fgets(buf, sizeof(buf), f)) {
            size_t n = strlen(buf);
            while (n && (buf[n-1] == '\n' || buf[n-1] == '\r')) buf[--n] = 0;
            if (n > 2 && VerifySaveSlotOnDisk(buf)) {
                memcpy(g_SlotPath, buf, n + 1);
                g_AutosaveValid = TRUE;
            } else {
                Log("[Autosave] Slot in file '%s' ('%s') is invalid or missing on disk.\n", g_SlotFile, buf);
            }
        }
        fclose(f);
    }

    if (!g_AutosaveValid) {
        char diskSlot[0x104] = {0};
        if (ScanDiskForAutosaveSlot(diskSlot, sizeof(diskSlot))) {
            strcpy_s(g_SlotPath, diskSlot);
            g_AutosaveValid = TRUE;
            FILE* fw = fopen(g_SlotFile, "w");
            if (fw) { fprintf(fw, "%s\n", g_SlotPath); fclose(fw); }
            Log("[Autosave] Discovered existing autosave slot on disk: '%s', updated slot file.\n", g_SlotPath);
        } else {
            g_SlotPath[0] = 0;
            Log("[Autosave] No valid autosave slot found on disk yet. Ready to create on first save.\n");
        }
    } else {
        Log("[Autosave] Verified valid autosave slot: '%s'\n", g_SlotPath);
    }
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
static BOOL IsSafeToSaveNow(const char** outBlockReason = NULL, BOOL bypassGrace = FALSE,
                            BOOL ignoreSobjRoomTransition = FALSE, BOOL ignoreInteractionLocks = FALSE) {
    #define FAIL_SAVE(why) do { if (outBlockReason) *outBlockReason = why; return FALSE; } while (0)

    BYTE gstate = *(BYTE*)ADDR_GLOBAL_STATE;
    if (gstate != 5 && gstate != 0x0C) FAIL_SAVE("GlobalState!=5/0xC");
    if (*(BYTE*)ADDR_TASK1_STATE != 1) FAIL_SAVE("Task1State!=1");
    if (*(BYTE*)ADDR_STAGE_SUBSTATE != 3) FAIL_SAVE("StageSubState!=3");
    if (*(BYTE*)ADDR_PAUSE_DEPTH != 0) FAIL_SAVE("Paused");
    if (*(BYTE*)ADDR_RYU_SPAWNED == 0) FAIL_SAVE("RyuNotSpawned");
    if (*(WORD*)ADDR_RYU_HP == 0) FAIL_SAVE("RyuHP==0");
    if (*(BYTE*)ADDR_FIELD_STATE_MODE == 2) FAIL_SAVE("GameOverMode");
    if (IsCutscenePlayingNow()) FAIL_SAVE("CutsceneActive");
    if (*(BYTE*)ADDR_FIELD_CHAP_TRANS != 0) FAIL_SAVE("ChapTransActive");
    if (!ignoreSobjRoomTransition && *(BYTE*)ADDR_ROOM_TRANSITION != 0) FAIL_SAVE("RoomTransition");
    if (*(BYTE*)ADDR_STATE_TRIGGER != 0) FAIL_SAVE("StateTrigger");

    if (!ignoreInteractionLocks) {
        if (*(BYTE*)ADDR_RYU_EVENT_LOCK != 0) FAIL_SAVE("RyuEventLock");
        if ((*(DWORD*)0x00C0611C & 1) != 0) FAIL_SAVE("ScreenFadeActive");
    }

    if (!bypassGrace) {
        DWORD now = GetTickCount();
        if (now - g_ChapterStartTick < 2000) FAIL_SAVE("ChapterGracePeriod");
        if (now - g_LastLoadTick < 2000) FAIL_SAVE("QuickloadGracePeriod");
        if (g_DoorInteractTick != 0) {
            if (now - g_DoorInteractTick < 1500) FAIL_SAVE("DoorTransitionSettle");
            g_DoorInteractTick = 0;
        }
    }

    WORD curRoom = *(WORD*)ADDR_CURRENT_ROOM;
    if (curRoom == 0x0200 || curRoom == 0xFFFF) FAIL_SAVE("InvalidRoom");

    float py = *(float*)(ADDR_RYU_POS + 4);
    if (py < -2000.0f) FAIL_SAVE("VoidY<-2000");

    #undef FAIL_SAVE
    return TRUE;
}

// Packs Ryu's live world position, rotation matrix, HP, inventory, and room objects into 0x00572F40.
// If outBuf is non-NULL, copies the packed save image to outBuf and immediately restores live PACKED_VALID=0.
static void PackLiveToBuffer(BYTE* outBuf, WORD* outRoom, float* outPos, BYTE* outChap, BYTE* outDiff, WORD* outHP, WORD* outBgm) {
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
    // 0x002F1820 (PACK_GLOBAL) reads curRoom from SI via 0x002FCA30, matching 0x002FD550.
    __asm {
        push esi
        push ADDR_RYU_MATRIX
        push ADDR_RYU_POS
        movzx edx, musicIdx
        mov eax, ADDR_FUNC_PACK_PLAYER
        call eax
        add esp, 8

        movzx esi, curRoom
        mov eax, esi
        mov ecx, ADDR_FUNC_PACK_ROOM
        call ecx

        mov eax, ADDR_FUNC_PACK_GLOBAL
        call eax
        pop esi
    }

    // Ensure mid-stage packed flags are set in the buffer for when the save is LOADED
    *(BYTE*)ADDR_FIELD_PACKED_VALID = 1;
    *(BYTE*)ADDR_FIELD_CHAP_TRANS   = 0;
    *(BYTE*)ADDR_FIELD_WIPE_FLAG    = 0;
    *(BYTE*)ADDR_FIELD_STATE_MODE   = 1;

    if (outChap) *outChap = *(BYTE*)ADDR_FIELD_CHAPTER;
    if (outDiff) *outDiff = *(BYTE*)ADDR_FIELD_DIFFICULTY;
    if (outRoom) *outRoom = *(WORD*)ADDR_FIELD_SAVED_ROOM;
    if (outPos) {
        outPos[0] = *(float*)(ADDR_RYU_POS + 0);
        outPos[1] = *(float*)(ADDR_RYU_POS + 4);
        outPos[2] = *(float*)(ADDR_RYU_POS + 8);
    }
    if (outHP)  *outHP  = *(WORD*)ADDR_RYU_HP;
    if (outBgm) *outBgm = musicIdx;

    if (outBuf) {
        memcpy(outBuf, (void*)ADDR_SAVE_IMAGE, SIZE_SAVE_IMAGE);
        // Live gameplay memory MUST keep PACKED_VALID = 0 so doors/cutscenes work!
        *(BYTE*)ADDR_FIELD_PACKED_VALID = 0;
        *(BYTE*)ADDR_BACKUP_PACKED_VAL  = 0;
    }
}

// Writes a packed save buffer (ADDR_SAVE_IMAGE or pre-door snapshot) to disk via 0x0030F840
// and clears PACKED_VALID in live memory so native door/cutscene triggers remain operational.
static BOOL WriteSaveBufferToDisk(void* pSaveBuf, BYTE chapter) {
    char pathOut[0x104];
    memset(pathOut, 0, sizeof(pathOut));
    WCHAR* name = g_SaveName;
    int res = -1;

    __asm {
        push 0
        push 0
        push SIZE_SAVE_IMAGE
        push pSaveBuf
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
    return FALSE;
}

// Freezes a door-sequence snapshot at the moment a door interaction starts.
// We prefer the latest rolling snapshot instead of packing live state here:
// this hook runs inside the SOBJ update loop after the trigger's state byte
// has already become 1/2, and PACK_ROOM would serialize that in-progress state.
static void ClearDoorSequence(const char* why);
static void AbandonDoorSequence(const char* why);

// Maps a game room ID to its 0-based packed room slot index via 0x002FCA30 (si = room),
// matching PACK_ROOM (0x002F1780) and UNPACK_ROOM (0x002F1900).
static WORD GetPackedRoomSlot(WORD room) {
    if (room >= 0x0200) return 0x0200;
    WORD slot = 0x0200;
    __try {
        if (*(DWORD*)0x00DB98C4 != 0) {
            __asm {
                push esi
                movzx esi, room
                mov eax, 0x002FCA30
                call eax
                mov slot, ax
                pop esi
            }
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        slot = 0x0200;
    }
    return slot;
}

// PACK_ROOM serializes each SOBJ trigger's +0x24 state byte into the save
// image's room block using the packed room slot index from 0x002FCA30.
// Returns the byte offset of the current trigger's state in the image.
static BOOL GetDoorTriggerImageOffset(const BYTE* trig, WORD room, DWORD* outOff) {
    if (!trig || !outOff) return FALSE;
    DWORD addr = (DWORD)trig;
    if (addr < 0xD53320) return FALSE;
    DWORD delta = addr - 0xD53320;
    if ((delta % 0x68) != 0) return FALSE;
    DWORD n = delta / 0x68;
    if (n >= 0x380) return FALSE;
    WORD slot = GetPackedRoomSlot(room);
    if (slot >= 0x0200) return FALSE; // PACK_ROOM skips invalid/unmapped rooms

    // Room state block: VA 0x572F90 + slot*0x790, state bytes at +0x410.
    // The image starts at VA 0x572F40, so offset = 0x50 + 0x410 + slot*0x790 + n.
    DWORD off = 0x00000460 + (DWORD)slot * 0x790 + n;
    if (off >= SIZE_SAVE_IMAGE) return FALSE;
    *outOff = off;
    return TRUE;
}

// Restores an in-progress (2) or mistakenly exhausted (3 when live was 1) door
// state back to idle/armed (1) in the frozen image. Never patch to 3: in
// DoorInteract_2DF3C0 (0x002DF3E3: cmp al,1; jne 0x2df4a0), state 3 skips
// ConditionEval completely and permanently deadlocks reusable doors.
static void ResetSavedDoorTriggerState(const BYTE* trig, WORD room, BYTE liveState) {
    DWORD off = 0;
    if (!GetDoorTriggerImageOffset(trig, room, &off)) {
        Log("[Autosave] [DoorSeq] Trigger state patch skipped (trig=%p, room=0x%04X)\n", trig, room);
        return;
    }

    BYTE old = g_DoorSaveImage[off];
    BYTE patched = old;
    if (old == 2 || (old == 3 && liveState == 1)) patched = 1;
    g_DoorSaveImage[off] = patched;
    Log("[Autosave] [DoorSeq] Saved trigger state (trig=%p, room=0x%04X, off=0x%X): 0x%02X -> 0x%02X (live=0x%02X)\n",
        trig, room, off, old, patched, liveState);
}

static BOOL CaptureDoorSequenceSnapshot(const BYTE* trig) {
    DWORD now = GetTickCount();

    // A new door interaction always replaces any previous frozen image.
    AbandonDoorSequence("new door capture");

    DWORD age = (g_LastSnapshotTick != 0) ? (now - g_LastSnapshotTick) : 0xFFFFFFFF;
    BYTE liveChapter = *(BYTE*)ADDR_LIVE_CHAPTER;
    WORD liveRoom = *(WORD*)ADDR_CURRENT_ROOM;

    BOOL chapterMismatch = (g_PreDoorImageValid && g_PreDoorChapter != liveChapter);
    BOOL roomMismatch = (g_PreDoorImageValid && g_PreDoorRoom != liveRoom);

    float dx = *(float*)(ADDR_RYU_POS + 0) - g_PreDoorPos[0];
    float dy = *(float*)(ADDR_RYU_POS + 4) - g_PreDoorPos[1];
    float dz = *(float*)(ADDR_RYU_POS + 8) - g_PreDoorPos[2];
    BOOL positionTooFar = (g_PreDoorImageValid && (dx * dx + dy * dy + dz * dz) > (20.0f * 20.0f));
    BOOL currentUsable = g_PreDoorImageValid && age <= 2000 && !chapterMismatch && !roomMismatch && !positionTooFar;

    // The door hook fires after [trig+0x24] has already become 1. If the current
    // rolling image already has this door active (1/2), use the previous full
    // image: it is the closest snapshot that still has the door idle and the
    // player outside the doorway. This is the practical "save before trigger".
    BYTE curState = 0xFF, prevState = 0xFF;
    DWORD stateOff = 0;
    if (currentUsable && GetDoorTriggerImageOffset(trig, g_PreDoorRoom, &stateOff)) {
        curState = g_PreDoorImage[stateOff];
    }

    BOOL prevRoomMatches = g_PrevPreDoorImageValid && g_PrevPreDoorRoom == liveRoom;
    BOOL prevChapterMatches = (g_PrevPreDoorChapter == liveChapter);
    float pdx = *(float*)(ADDR_RYU_POS + 0) - g_PrevPreDoorPos[0];
    float pdy = *(float*)(ADDR_RYU_POS + 4) - g_PrevPreDoorPos[1];
    float pdz = *(float*)(ADDR_RYU_POS + 8) - g_PrevPreDoorPos[2];
    BOOL prevPosTooFar = (pdx * pdx + pdy * pdy + pdz * pdz) > (20.0f * 20.0f);
    BOOL prevRecent = prevRoomMatches && prevChapterMatches && !prevPosTooFar &&
                      (DWORD)(now - g_PrevPreDoorTick) <= 3000;
    if (prevRoomMatches && GetDoorTriggerImageOffset(trig, g_PrevPreDoorRoom, &stateOff)) {
        prevState = g_PrevPreDoorImage[stateOff];
    }

    BOOL currentDoorActive = (curState == 1 || curState == 2);
    BOOL prevStateKnown = (prevState != 0xFF);
    BOOL prevDoorIdle = prevStateKnown && !(prevState == 1 || prevState == 2);
    BOOL usePrev = prevRecent && prevDoorIdle && (!currentUsable || currentDoorActive);
    const char* source = usePrev ? "previous" : (currentUsable ? "current" : "live");
    BYTE chosenState = usePrev ? prevState : (currentUsable ? curState : 0xFF);

    if (usePrev) {
        memcpy(g_DoorSaveImage, g_PrevPreDoorImage, SIZE_SAVE_IMAGE);
        g_DoorSaveRoom    = g_PrevPreDoorRoom;
        g_DoorSavePos[0]  = g_PrevPreDoorPos[0];
        g_DoorSavePos[1]  = g_PrevPreDoorPos[1];
        g_DoorSavePos[2]  = g_PrevPreDoorPos[2];
        g_DoorSaveChapter = g_PrevPreDoorChapter;
        g_DoorSaveDiff    = g_PrevPreDoorDiff;
        g_DoorSaveHP      = g_PrevPreDoorHP;
    } else if (currentUsable) {
        memcpy(g_DoorSaveImage, g_PreDoorImage, SIZE_SAVE_IMAGE);
        g_DoorSaveRoom    = g_PreDoorRoom;
        g_DoorSavePos[0]  = g_PreDoorPos[0];
        g_DoorSavePos[1]  = g_PreDoorPos[1];
        g_DoorSavePos[2]  = g_PreDoorPos[2];
        g_DoorSaveChapter = g_PreDoorChapter;
        g_DoorSaveDiff    = g_PreDoorDiff;
        g_DoorSaveHP      = g_PreDoorHP;
    } else {
        if (!IsInActiveGameplayFrame()) {
            Log("[Autosave] [DoorSeq] No usable rolling snapshot and not in active gameplay; capture skipped\n");
            return FALSE;
        }
        Log("[Autosave] [DoorSeq] No usable current/previous snapshot (cur=0x%02X prev=0x%02X); packing live fallback\n",
            curState, prevState);
        InterlockedExchange(&g_InSnapshot, 1);
        __try {
            PackLiveToBuffer(g_DoorSaveImage, &g_DoorSaveRoom, g_DoorSavePos,
                             &g_DoorSaveChapter, &g_DoorSaveDiff, &g_DoorSaveHP, NULL);
        } __except (ExcFilter(GetExceptionInformation(), "CaptureDoorSequenceSnapshot")) {
            *(BYTE*)ADDR_FIELD_PACKED_VALID = 0;
            *(BYTE*)ADDR_BACKUP_PACKED_VAL  = 0;
            InterlockedExchange(&g_InSnapshot, 0);
            return FALSE;
        }
        InterlockedExchange(&g_InSnapshot, 0);
    }

    // Keep the checkpoint even when the door was already used (state 3) or is
    // mid-activation (1/2). Skipping these saves loses the player's progress
    // between the manual save and the door. The local trigger state byte is
    // still patched to 0 below; the game re-arms used doors when A is pressed.
    if (chosenState != 0) {
        Log("[Autosave] [DoorSeq] Door state 0x%02X (source=%s, current=0x%02X, previous=0x%02X); saving checkpoint anyway\n",
            chosenState, source, curState, prevState);

        DWORD diagOff = 0;
        if (GetDoorTriggerImageOffset(trig, g_DoorSaveRoom, &diagOff)) {
            WORD diagSlot = GetPackedRoomSlot(g_DoorSaveRoom);
            DWORD n = (diagSlot < 0x0200) ? (diagOff - 0x00000460 - (DWORD)diagSlot * 0x790) : 0;
            Log("[Autosave] [DoorState] n=%u (slot=%u) image states:", n, (unsigned)diagSlot);
            for (int d = -8; d <= 8; ++d) {
                int idx = (int)n + d;
                if (idx >= 0 && idx < 0x380) {
                    BYTE b = g_DoorSaveImage[diagOff + d];
                    if (b != 0) Log(" %d:0x%02X", idx, b);
                }
            }
            Log("\n[Autosave] [DoorState] live states:");
            for (int d = -8; d <= 8; ++d) {
                int idx = (int)n + d;
                if (idx >= 0 && idx < 0x380) {
                    BYTE b = *(BYTE*)(0xD53344 + (DWORD)idx * 0x68);
                    if (b != 0) Log(" %d:0x%02X", idx, b);
                }
            }
            Log("\n");
        }

        const DWORD* act = *(const DWORD**)(trig + 8);
        if (act) {
            Log("[Autosave] [DoorState] act:");
            for (int i = 0; i < 24; ++i) Log(" %08X", act[i]);
            Log("\n");
        }
    }

    // Convert an in-progress state (1/2) to finished (3) so loading cannot
    // execute the action list automatically, while keeping it re-armable by the
    // normal interaction scan. Fresh (0) and already-finished (3) states are
    // preserved. No positional offset is applied.
    BYTE liveTrigState = 0xFF;
    __try {
        liveTrigState = *(const BYTE*)(trig + 0x24);
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        liveTrigState = 0xFF;
    }
    ResetSavedDoorTriggerState(trig, g_DoorSaveRoom, liveTrigState);

    g_DoorSaveValid        = TRUE;
    g_DoorSaveWritten      = FALSE;
    g_DoorSaveCapturedTick = now;
    g_DoorSeqActive        = TRUE;
    g_DoorSeqTick          = now;
    g_DoorSeqTrig          = trig;

    Log("[Autosave] [DoorSeq] Frozen pre-door snapshot (source=%s, currentState=0x%02X, prevState=0x%02X, age=%ums, Chapter %u, Diff %u, Room 0x%04X, Pos [%.1f, %.1f, %.1f], HP %u)\n",
        source, curState, prevState, age,
        g_DoorSaveChapter, g_DoorSaveDiff, g_DoorSaveRoom,
        g_DoorSavePos[0], g_DoorSavePos[1], g_DoorSavePos[2], g_DoorSaveHP);
    return TRUE;
}

// Drops the frozen door-sequence image. Used when the sequence expires or a
// new live save supersedes it, so later room-change saves cannot reuse stale
// pre-door data.
static void ClearDoorSequence(const char* why) {
    if (g_DoorSaveValid || g_DoorSeqActive) {
        Log("[Autosave] [DoorSeq] Clearing frozen snapshot (%s)\n", why);
    }
    g_DoorSaveValid        = FALSE;
    g_DoorSaveWritten      = FALSE;
    g_DoorSeqActive        = FALSE;
    g_DoorSeqTrig          = NULL;
}

// Drops the frozen snapshot and cancels any pending deferred SRC_DOOR save, so
// it cannot later live-pack the destination position over the pre-door file.
// Used when the sequence is deliberately abandoned (load/chapter/menu).
static void AbandonDoorSequence(const char* why) {
    if (g_PendingSave && (int)g_PendingSaveSrc == SRC_DOOR) {
        InterlockedExchange(&g_PendingSave, 0);
    }
    ClearDoorSequence(why);
}

// Writes either the frozen door-sequence snapshot (for SRC_DOOR) or live packed state to disk via 0x0030F840.
static BOOL DoAutosave(int saveSrc) {
    __try {
        if (!IsSafeToSaveNow(NULL, FALSE)) {
            return FALSE;
        }

        BYTE chapter = 0, difficulty = 0;
        WORD savedRoom = 0, hp = 0, musicIdx = 0;
        float pos[3] = {0};
        void* pSaveBuf = (void*)ADDR_SAVE_IMAGE;
        DWORD now = GetTickCount();
        BOOL usedDoorSeq = (saveSrc == SRC_DOOR && g_DoorSaveValid);

        if (usedDoorSeq) {
            pSaveBuf   = (void*)g_DoorSaveImage;
            chapter    = g_DoorSaveChapter;
            difficulty = g_DoorSaveDiff;
            savedRoom  = g_DoorSaveRoom;
            pos[0]     = g_DoorSavePos[0];
            pos[1]     = g_DoorSavePos[1];
            pos[2]     = g_DoorSavePos[2];
            hp         = g_DoorSaveHP;
            Log("[Autosave] [DoorSeq] Saving frozen pre-door snapshot (captured %ums ago, Chapter %u, Diff %u, Room 0x%04X, Pos [%.1f, %.1f, %.1f], HP %u)...\n",
                now - g_DoorSaveCapturedTick,
                chapter, difficulty, savedRoom, pos[0], pos[1], pos[2], hp);
        } else {
            PackLiveToBuffer(NULL, &savedRoom, pos, &chapter, &difficulty, &hp, &musicIdx);
            Log("[Autosave] Saving (Chapter %u, Diff %u, Room 0x%04X, Pos [%.1f, %.1f, %.1f], HP %u, BGM 0x%02X)...\n",
                chapter, difficulty, savedRoom, pos[0], pos[1], pos[2], hp, musicIdx);
        }

        BOOL ok = WriteSaveBufferToDisk(pSaveBuf, chapter);
        if (ok) {
            if (saveSrc == SRC_DOOR && usedDoorSeq) {
                // Keep the frozen image and cover active: the room-change events
                // that follow this door must not overwrite the pre-door position.
                g_DoorSaveWritten = TRUE;
                g_DoorSeqTick = GetTickCount();
            } else {
                // A live save (manual F5 / chapter start / encounter / shrine)
                // supersedes any door-sequence snapshot.
                ClearDoorSequence("superseded by live save");
            }
        }
        return ok;
    } __except (ExcFilter(GetExceptionInformation(), "DoAutosave")) {
        *(BYTE*)ADDR_FIELD_PACKED_VALID = 0;
        *(BYTE*)ADDR_BACKUP_PACKED_VAL  = 0;
    }
    return FALSE;
}

extern "C" void __cdecl QueueSaveC(int src);

// Packs live pre-mutation state directly into g_DoorSaveImage when safe at 0x002DF46E.
static BOOL CaptureLiveDoorSequenceSnapshot(const BYTE* trig) {
    if (!IsInActiveGameplayFrame()) return FALSE;
    DWORD now = GetTickCount();
    AbandonDoorSequence("new live door capture");

    BYTE liveTrigState = 0xFF;
    __try {
        liveTrigState = *(const BYTE*)(trig + 0x24);
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        liveTrigState = 0xFF;
    }

    InterlockedExchange(&g_InSnapshot, 1);
    BOOL packedOk = FALSE;
    __try {
        PackLiveToBuffer(g_DoorSaveImage, &g_DoorSaveRoom, g_DoorSavePos,
                         &g_DoorSaveChapter, &g_DoorSaveDiff, &g_DoorSaveHP, NULL);
        packedOk = TRUE;
    } __except (ExcFilter(GetExceptionInformation(), "CaptureLiveDoorSequenceSnapshot")) {
        *(BYTE*)ADDR_FIELD_PACKED_VALID = 0;
        *(BYTE*)ADDR_BACKUP_PACKED_VAL  = 0;
        packedOk = FALSE;
    }
    InterlockedExchange(&g_InSnapshot, 0);
    if (!packedOk) return FALSE;

    ResetSavedDoorTriggerState(trig, g_DoorSaveRoom, liveTrigState);

    g_DoorSaveValid        = TRUE;
    g_DoorSaveWritten      = FALSE;
    g_DoorSaveCapturedTick = now;
    g_DoorSeqActive        = TRUE;
    g_DoorSeqTick          = now;
    g_DoorSeqTrig          = trig;

    Log("[Autosave] [DoorSeq] Frozen pre-door snapshot (source=live-pre-mutation, state=0x%02X, Chapter %u, Diff %u, Room 0x%04X, Pos [%.1f, %.1f, %.1f], HP %u)\n",
        liveTrigState, g_DoorSaveChapter, g_DoorSaveDiff, g_DoorSaveRoom,
        g_DoorSavePos[0], g_DoorSavePos[1], g_DoorSavePos[2], g_DoorSaveHP);
    return TRUE;
}

// Captures a frozen pre-door image before DoorInteract_2DF3C0 mutates any
// trigger or room flags, then tries to write it to disk synchronously BEFORE
// the door action list runs. If the write is not safe, the same frozen image
// is queued and written once the game settles.
static BOOL SavePreDoorNow(const BYTE* trig, BOOL preferRollingSnapshot) {
    DWORD now = GetTickCount();
    g_GameTid = GetCurrentThreadId();

    if (*(BYTE*)ADDR_FIELD_CHAP_TRANS != 0) {
        Log("[Autosave] Pre-door save suppressed (chapter transition active)\n");
        return FALSE;
    }

    if (g_PendingLoad) {
        Log("[Autosave] [DoorSeq] save not queued while autoload is pending\n");
        g_DoorInteractTick = 0;
        AbandonDoorSequence("autoload pending");
        return FALSE;
    }

    BOOL captured = FALSE;
    if (!preferRollingSnapshot && *(volatile DWORD*)ADDR_SAVE_POOL == 0 &&
        IsSafeToSaveNow(NULL, TRUE, TRUE, TRUE)) {
        captured = CaptureLiveDoorSequenceSnapshot(trig);
    }
    if (!captured) {
        captured = CaptureDoorSequenceSnapshot(trig);
    }

    if (!captured) {
        // Never queue a live save when no usable pre-door snapshot exists: by
        // the time it runs the player may already be inside the destination
        // room, or the door may already be in a used state. Keep the previous
        // consistent quick save.
        Log("[Autosave] [DoorSeq] no usable pre-door snapshot; keeping previous quick save\n");
        g_DoorInteractTick = 0;
        AbandonDoorSequence("no usable pre-door snapshot");
        return FALSE;
    }

    // Save first, then open the door. This hook is still before the action
    // list at 0x2DF4C0. The SOBJ-loop RoomTransition flag is a false positive
    // here, and the interaction locks only describe gameplay input, so both
    // are ignored for this frozen-image write.
    const char* syncWhy = NULL;
    if (*(volatile DWORD*)ADDR_SAVE_POOL != 0) {
        syncWhy = "SavePoolBusy";
    } else if (!IsSafeToSaveNow(&syncWhy, TRUE, TRUE, TRUE)) {
        // syncWhy populated by IsSafeToSaveNow
    }

    if (syncWhy == NULL) {
        DWORD syncStart = GetTickCount();
        LONG prevInPump = InterlockedExchange(&g_InPump, 1);
        BOOL syncOk = FALSE;
        __try {
            syncOk = WriteSaveBufferToDisk((void*)g_DoorSaveImage, g_DoorSaveChapter);
        } __except (ExcFilter(GetExceptionInformation(), "SavePreDoorNow")) {
            *(BYTE*)ADDR_FIELD_PACKED_VALID = 0;
            *(BYTE*)ADDR_BACKUP_PACKED_VAL  = 0;
            syncOk = FALSE;
        }
        InterlockedExchange(&g_InPump, prevInPump);

        if (syncOk) {
            g_DoorSaveWritten = TRUE;
            g_DoorSeqTick = now;
            g_DoorInteractTick = now;
            InterlockedIncrement(&g_HookCount[SRC_DOOR]);
            // The pre-door save is newer than any save that was already queued
            // (e.g. the delayed level-start autosave); let it win.
            InterlockedExchange(&g_PendingSave, 0);
            InterlockedExchange(&g_PendingSaveSrc, 0);
            Log("[Autosave] [DoorSeq] Pre-door sync save completed BEFORE door action (took %ums, Chapter %u, Room 0x%04X, Pos [%.1f, %.1f, %.1f])\n",
                GetTickCount() - syncStart, g_DoorSaveChapter, g_DoorSaveRoom,
                g_DoorSavePos[0], g_DoorSavePos[1], g_DoorSavePos[2]);
            return TRUE;
        }
        Log("[Autosave] [DoorSeq] Pre-door sync save failed after %ums; falling back to deferred SRC_DOOR\n",
            GetTickCount() - syncStart);
    } else {
        Log("[Autosave] [DoorSeq] Pre-door sync save skipped (%s); falling back to deferred SRC_DOOR\n", syncWhy);
    }

    g_DoorInteractTick = now;

    // Queue the deferred fallback with the same frozen pre-door image.
    QueueSaveC(SRC_DOOR);
    if (!g_PendingSave) {
        // QueueSaveC may have debounced this as a duplicate room-change event;
        // force the fallback because we have a fresh frozen snapshot.
        InterlockedExchange(&g_PendingSaveSrc, SRC_DOOR);
        InterlockedExchange(&g_PendingSave, 1);
        Log("[Autosave] [DoorSeq] forced deferred SRC_DOOR fallback after debounce\n");
    }
    return captured;
}

// Drops all pre-door/quick-save snapshot state before any checkpoint load.
static void ResetDoorStateForLoad(const char* why) {
    g_PreDoorImageValid = FALSE;
    g_PrevPreDoorImageValid = FALSE;
    g_PrevPreDoorTick = 0;
    AbandonDoorSequence(why);
    g_DoorInteractTick = 0;

    // A stale interaction/button global from the door action that preceded F9
    // must not be visible to the first SOBJ update after the load.
    __try {
        *(DWORD*)0x00D52CE8 = 0;
    } __except (EXCEPTION_EXECUTE_HANDLER) {
    }
}

// Normalizes the live SOBJ trigger state for the door that produced the quick
// save. In-progress state (2) is restored to armed/idle (1), never 3 (dead).
static void ResetLiveDoorTriggerAfterLoad(const BYTE* trig, WORD doorRoom, WORD loadedRoom) {
    if (!trig || doorRoom != loadedRoom) return;

    // Apply again on the first active gameplay frame: State 9/unpack can run
    // after this hook and restore the state byte from the save image.
    g_PostLoadDoorTrig = trig;
    g_PostLoadDoorRoom = loadedRoom;
    g_PostLoadDoorResetPending = TRUE;
    g_PostLoadDoorResetRoomTick = 0;
    g_PostLoadDoorCheckDone = FALSE;
    g_LastLoadTick = GetTickCount();

    __try {
        BYTE old = *(BYTE*)(trig + 0x24);
        *(BYTE*)(trig + 0x24) = (old == 2) ? 1 : old;
        *(DWORD*)(trig + 0x0C) = 0;
        *(DWORD*)0x00D52CE8 = 0;
        Log("[Autosave] [DoorSeq] Live trigger normalized after load (trig=%p, room=0x%04X): state 0x%02X -> 0x%02X\n",
            trig, doorRoom, old, *(BYTE*)(trig + 0x24));
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        Log("[Autosave] [DoorSeq] Live trigger reset skipped (invalid trig=%p)\n", trig);
    }
}

// Intercepts State 9 Case 3/4 checkpoint file loader (0x0016656A).
extern "C" int __cdecl Hook_CheckpointLoad_Impl(int slotIdx) {
    if (g_AutoloadPending) {
        if (!g_AutosaveValid || !g_SlotPath[0]) {
            Log("[Autosave] Autoload requested but no valid slot exists, falling back to native checkpoint\n");
            g_AutoloadPending = 0;
            const BYTE* lastTrig = g_DoorSeqTrig;
            WORD lastDoorRoom = g_DoorSaveRoom;
            ResetDoorStateForLoad("native checkpoint load (no autosave slot)");
            typedef int (__cdecl *PFN_LoadCheckpoint)(int);
            int loadRes = ((PFN_LoadCheckpoint)0x0016B680)(slotIdx);
            ResetLiveDoorTriggerAfterLoad(lastTrig, lastDoorRoom, *(WORD*)ADDR_FIELD_SAVED_ROOM);
            return loadRes;
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
            if (*pSaveNinpo != 0 && *pSaveNinpo != 0xFFFF) {
                if (*pSaveMaxKi < 200) {
                    *pSaveMaxKi = 400;
                    *pSaveCurKi = 400;
                    Log("[Autosave] [LoadImage] Repaired zeroed MaxKi/CurKi in save buffer -> 400\n");
                } else if (*pSaveCurKi < 200) {
                    *pSaveCurKi = *pSaveMaxKi;
                    Log("[Autosave] [LoadImage] Repaired zeroed CurKi in save buffer -> %u\n", *pSaveCurKi);
                }
            }

            memcpy((void*)ADDR_CHECKPOINT_BACKUP, (void*)ADDR_SAVE_IMAGE, SIZE_SAVE_IMAGE);
            *(BYTE*)ADDR_BACKUP_PACKED_VAL = 0;

            // Use Case 4 ([0x00DB9AD6] = 4) so 0x00166595 skips incrementing death count [0x00589414]
            *(BYTE*)ADDR_STATE_TRIGGER = 4;

            g_LastLoadTick    = GetTickCount();
            g_LastRoomId      = savedRoom;
            g_CurrentChapter  = loadedChapter;
            const BYTE* lastTrig = g_DoorSeqTrig;
            WORD lastDoorRoom = g_DoorSaveRoom;
            ResetDoorStateForLoad("autoload");
            ResetLiveDoorTriggerAfterLoad(lastTrig, lastDoorRoom, savedRoom);
            g_AutoloadPending = 0;

            Log("[Autosave] Autoload successful (Chapter %u, Room 0x%04X, Spawn 0x%04X, Packed %u) -> resuming via State 9 -> State 5\n",
                loadedChapter, savedRoom, spawnId, wasPacked);
            return 1;
        }
        Log("[Autosave] Autoload failed with code: %d, falling back to native checkpoint\n", res);
        g_AutoloadPending = 0;
        const BYTE* lastTrig = g_DoorSeqTrig;
        WORD lastDoorRoom = g_DoorSaveRoom;
        ResetDoorStateForLoad("native checkpoint load (autoload failed)");
        typedef int (__cdecl *PFN_LoadCheckpoint)(int);
        int loadRes = ((PFN_LoadCheckpoint)0x0016B680)(slotIdx);
        ResetLiveDoorTriggerAfterLoad(lastTrig, lastDoorRoom, *(WORD*)ADDR_FIELD_SAVED_ROOM);
        return loadRes;
    }

    // Normal checkpoint load: call original 0x0016B680
    const BYTE* lastTrig = g_DoorSeqTrig;
    WORD lastDoorRoom = g_DoorSaveRoom;
    ResetDoorStateForLoad("native checkpoint load");
    typedef int (__cdecl *PFN_LoadCheckpoint)(int);
    int loadRes = ((PFN_LoadCheckpoint)0x0016B680)(slotIdx);
    ResetLiveDoorTriggerAfterLoad(lastTrig, lastDoorRoom, *(WORD*)ADDR_FIELD_SAVED_ROOM);
    return loadRes;
}

extern "C" void __cdecl QueueSaveC(int src) {
    DWORD tid = GetCurrentThreadId();   // these hooks all fire on the game thread
    g_GameTid = tid;

    const char* hookTag = (src > 0 && src <= 4) ? g_HookName[src] : "?";

    // Suppress only if end-of-chapter transition flag is active; otherwise queue and let PumpC wait until settled!
    if (*(BYTE*)ADDR_FIELD_CHAP_TRANS != 0) {
        Log("[Autosave] [Hook:%s] suppressed (chapter transition active)\n", hookTag);
        return;
    }

    // A door snapshot captured after the current level-start tick is a newer
    // checkpoint than the delayed level-start autosave. Do not let the latter
    // overwrite it with a position inside the room the player just entered.
    if (src == SRC_CHAPTER_START && g_DoorSeqActive && g_DoorSaveValid &&
        (LONG)(g_DoorSaveCapturedTick - g_ChapterStartTick) > 0) {
        Log("[Autosave] [DoorSeq] Chapter-start save suppressed: newer door snapshot exists\n");
        return;
    }

    DWORD now = GetTickCount();
    if (src == SRC_DOOR) {
        // Debounce back-to-back duplicate notifications for the same door
        if (now - g_LastRoomSaveTick < 1500) {
            return;
        }
        g_LastRoomSaveTick = now;
    }

    int hookIdx = (src > 0 && src <= 4) ? src : 0;
    LONG n = InterlockedIncrement(&g_HookCount[hookIdx]);
    Log("[Autosave] [Hook:%s] fired #%d on thread %u -> queue save\n",
        hookTag, n, tid);
    InterlockedExchange(&g_PendingSaveSrc, src);
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
    if (g_InPump || g_InSnapshot) return;

    BYTE gstate   = *(BYTE*)ADDR_GLOBAL_STATE;
    BYTE subState = *(BYTE*)ADDR_STAGE_SUBSTATE;
    DWORD now     = GetTickCount();

    // Difficulty Unlocks Sync (Hard, Very Hard, Master Ninja in T:\system.dat memory)
    if (IsMapped(0x00DB93FC) && *(DWORD*)0x00DB93FC == 0x20030730) {
        if (*(BYTE*)0x00DB9472 == 0) *(BYTE*)0x00DB9472 = 1; // Hard
        if (*(BYTE*)0x00DB9473 == 0) *(BYTE*)0x00DB9473 = 1; // Very Hard
        if (*(BYTE*)0x00DB9474 == 0) *(BYTE*)0x00DB9474 = 1; // Master Ninja
    }

    // Reset chapter/room tracking when back on Title / Menus so a New Game in Chapter 1 (index 0) re-arms cleanly
    if (gstate != 5 && gstate != 0x0C && gstate != 9 && subState != 0x80) {
        g_CurrentChapter = 0xFF;
        g_LastRoomId = 0xFFFF;
        g_ChapterSavePending = FALSE;
        g_LastEnemyCount = 0;
        g_DoorInteractTick = 0;
        AbandonDoorSequence("returned to menus");
        g_PostLoadDoorResetPending = FALSE;
        g_PostLoadDoorResetRoomTick = 0;
        g_PreDoorImageValid = FALSE;
        g_PrevPreDoorImageValid = FALSE;
        g_PrevPreDoorTick = 0;
    }

    if (g_DoorSeqActive) {
        BOOL transitioning = !IsInActiveGameplayFrame() ||
                             *(BYTE*)ADDR_PAUSE_DEPTH != 0 ||
                             IsCutscenePlayingNow() ||
                             *(BYTE*)ADDR_ROOM_TRANSITION != 0 ||
                             *(BYTE*)ADDR_STATE_TRIGGER != 0 ||
                             *(BYTE*)ADDR_FIELD_CHAP_TRANS != 0 ||
                             *(BYTE*)ADDR_RYU_EVENT_LOCK != 0 ||
                             (*(DWORD*)0x00C0611C & 1) != 0;
        if (transitioning) {
            // Do not age out during a long load/cutscene/pause/Game Over; the
            // player must still be able to F9 back to the pre-door state.
            g_DoorSeqTick = now;
        } else if (now - g_DoorSeqTick >= 8000 &&
                   !(g_PendingSave && (int)g_PendingSaveSrc == SRC_DOOR)) {
            ClearDoorSequence("sequence timeout");
        }
        if (now - g_DoorSaveCapturedTick >= 60000 &&
            !(g_PendingSave && (int)g_PendingSaveSrc == SRC_DOOR)) {
            ClearDoorSequence("sequence hard timeout");
        }
    }

    // Post-load door trigger guard: the load hook and the room-unpack pass can
    // both restore a serialized "door active" state. Keep forcing the last door
    // trigger to idle for a short window after the destination room appears, so
    // the first SOBJ updates cannot auto-execute the door action. This also
    // repairs older quick saves written before the state-byte patch existed.
    if (g_PostLoadDoorResetPending) {
        DWORD elapsed = now - g_LastLoadTick;
        if (gstate == 5 || gstate == 0x0C) {
            WORD curRoom = *(WORD*)ADDR_CURRENT_ROOM;
            if (curRoom == g_PostLoadDoorRoom) {
                float dx = *(float*)(ADDR_RYU_POS + 0) - g_DoorSavePos[0];
                float dy = *(float*)(ADDR_RYU_POS + 4) - g_DoorSavePos[1];
                float dz = *(float*)(ADDR_RYU_POS + 8) - g_DoorSavePos[2];
                BOOL nearSavedPos = (dx * dx + dy * dy + dz * dz) < (10.0f * 10.0f);
                if (nearSavedPos) {
                    if (g_PostLoadDoorResetRoomTick == 0) {
                        g_PostLoadDoorResetRoomTick = now;
                    }
                    __try {
                        BYTE old = *(BYTE*)(g_PostLoadDoorTrig + 0x24);
                        *(BYTE*)(g_PostLoadDoorTrig + 0x24) = (old == 2) ? 1 : old;
                        *(DWORD*)(g_PostLoadDoorTrig + 0x0C) = 0;
                        *(DWORD*)0x00D52CE8 = 0;
                        Log("[Autosave] [DoorSeq] Post-load trigger normalized (trig=%p, room=0x%04X, pos [%.1f, %.1f, %.1f]): state 0x%02X -> 0x%02X\n",
                            g_PostLoadDoorTrig, g_PostLoadDoorRoom,
                            *(float*)(ADDR_RYU_POS + 0), *(float*)(ADDR_RYU_POS + 4), *(float*)(ADDR_RYU_POS + 8),
                            old, *(BYTE*)(g_PostLoadDoorTrig + 0x24));
                    } __except (EXCEPTION_EXECUTE_HANDLER) {
                        Log("[Autosave] [DoorSeq] Post-load trigger reset skipped (invalid trig=%p)\n",
                            g_PostLoadDoorTrig);
                    }
                    g_PostLoadDoorResetPending = FALSE;
                }
            }
        }
        if (g_PostLoadDoorResetPending &&
            g_PostLoadDoorResetRoomTick == 0 && elapsed > 5000) {
            Log("[Autosave] [DoorSeq] Post-load trigger reset abandoned (room 0x%04X, doorRoom 0x%04X, pos [%.1f, %.1f, %.1f])\n",
                *(WORD*)ADDR_CURRENT_ROOM, g_PostLoadDoorRoom,
                *(float*)(ADDR_RYU_POS + 0), *(float*)(ADDR_RYU_POS + 4), *(float*)(ADDR_RYU_POS + 8));
            g_PostLoadDoorResetPending = FALSE;
        }
    }

    // One-shot live-state probe when the player reaches the saved door area
    // after a load: shows whether the game re-activated or reverted the door.
    if (!g_PostLoadDoorCheckDone && g_PostLoadDoorTrig &&
        (gstate == 5 || gstate == 0x0C)) {
        float ldx = *(float*)(ADDR_RYU_POS + 0) - g_DoorSavePos[0];
        float ldy = *(float*)(ADDR_RYU_POS + 4) - g_DoorSavePos[1];
        float ldz = *(float*)(ADDR_RYU_POS + 8) - g_DoorSavePos[2];
        if ((ldx * ldx + ldy * ldy + ldz * ldz) < (3.0f * 3.0f)) {
            __try {
                BYTE* p = (BYTE*)(g_PostLoadDoorTrig + 0x24);
                Log("[Autosave] [DoorLive] near door pos [%.1f, %.1f, %.1f] state=0x%02X cursor=%d prompt=0x%X bytes=%02X %02X %02X %02X %02X %02X %02X %02X\n",
                    *(float*)(ADDR_RYU_POS + 0), *(float*)(ADDR_RYU_POS + 4), *(float*)(ADDR_RYU_POS + 8),
                    p[0], *(DWORD*)(g_PostLoadDoorTrig + 0x0C), *(DWORD*)0x00D52CE8,
                    p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7]);
            } __except (EXCEPTION_EXECUTE_HANDLER) {
                Log("[Autosave] [DoorLive] probe skipped (invalid trig=%p)\n", g_PostLoadDoorTrig);
            }
            g_PostLoadDoorCheckDone = TRUE;
        } else if ((DWORD)(now - g_LastLoadTick) > 10000) {
            g_PostLoadDoorCheckDone = TRUE;
        }
    }

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

        // 1. Live Chapter Change & Initial Chapter Detection (0x00DB9AD4 is 0-indexed: 0 = Chapter 1)
        BYTE curChapter = *(BYTE*)ADDR_LIVE_CHAPTER;
        if (curChapter != 0xFF) {
            if (g_CurrentChapter == 0xFF) {
                g_CurrentChapter = curChapter;
                g_LastSavedChapter = curChapter;
                g_LastRoomId = *(WORD*)ADDR_CURRENT_ROOM;
                g_ChapterStartTick = now;
                g_ChapterSavePending = TRUE;
                AbandonDoorSequence("initial chapter detection");
                Log("[Autosave] Initial chapter detected: Chapter %u -> arm level start autosave\n", curChapter + 1);
            } else if (curChapter != g_CurrentChapter) {
                Log("[Autosave] Chapter transition detected: Chapter %u -> Chapter %u\n", g_CurrentChapter + 1, curChapter + 1);
                g_CurrentChapter = curChapter;
                g_LastSavedChapter = curChapter;
                g_LastRoomId = *(WORD*)ADDR_CURRENT_ROOM;
                g_ChapterStartTick = now;
                g_ChapterSavePending = TRUE;
                AbandonDoorSequence("chapter transition");
            }
        }

        // Trigger Chapter Start autosave once the chapter grace period (2.0s) has elapsed
        if (g_ChapterSavePending && (now - g_ChapterStartTick >= 2000)) {
            if (!IsCutscenePlayingNow()) {
                g_ChapterSavePending = FALSE;
                Log("[Autosave] Level start settled (Chapter %u) -> queue autosave\n", g_CurrentChapter + 1);
                QueueSaveC(SRC_CHAPTER_START);
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
                if (g_DoorSeqActive && g_DoorSaveValid && (now - g_DoorSeqTick < 8000)) {
                    g_DoorSeqTick = now; // extend cover until this door sequence settles
                    Log("[Autosave] [DoorSeq] Door transition 0x%04X -> 0x%04X covered by frozen pre-door snapshot\n",
                        prevRoom, curRoom);
                } else {
                    ClearDoorSequence("room change outside active sequence");
                    Log("[Autosave] Door transition to next room: 0x%04X -> 0x%04X (Chapter %u)\n",
                        prevRoom, curRoom, *(BYTE*)ADDR_LIVE_CHAPTER);
                    QueueSaveC(SRC_DOOR);
                }
            }
        }

        // 3. Enemy Encounter Detection (Enemies spawned from 0 -> >0)
        int curEnemies = GetActiveEnemyCount();
        if (g_LastEnemyCount == 0 && curEnemies > 0) {
            // Transition from peace to combat encounter!
            if (g_DoorSeqActive && g_DoorSaveValid && (now - g_DoorSeqTick < 8000)) {
                // Do not replace the fresh pre-door quick save with a position
                // inside the room the player just entered.
                Log("[Autosave] [DoorSeq] Enemy encounter save suppressed by active door sequence\n");
            } else if (now - g_LastEncounterSaveTick >= 5000 &&
                now - g_LastRoomSaveTick >= 2500 &&
                now - g_ChapterStartTick >= 2000 &&
                !IsCutscenePlayingNow()) {
                g_LastEncounterSaveTick = now;
                Log("[Autosave] Enemy encounter detected! Active enemies: %d -> queue autosave\n", curEnemies);
                QueueSaveC(SRC_ENEMY_ENCOUNTER);
            }
        } else if (g_LastEnemyCount > 0 && curEnemies == 0) {
            Log("[Autosave] Battle encounter cleared (all enemies defeated).\n");
        }
        g_LastEnemyCount = curEnemies;

        // 4. Ninpo / Ki Auto-Recovery Guard:
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
            if (g_DoorSeqActive && g_DoorSaveValid && (now - g_DoorSeqTick < 8000)) {
                // Keep the pre-door image intact; the live repair is persisted
                // by the next normal save (and UnpackHook also repairs on load).
                Log("[Autosave] [DoorSeq] KiGuard save skipped during active door sequence\n");
            } else {
                InterlockedExchange(&g_PendingSaveSrc, 0);
                InterlockedExchange(&g_PendingSave, 1);
            }
        }

        // 5. Rolling Pre-Door Snapshot: keep a recent safe in-RAM state (~350ms cadence).
        // This buffer is independent of the frozen door-sequence image, so it can
        // keep refreshing for the next door while a door save is still pending.
        BOOL pendingDoorAlreadyFlushed = (g_PendingSave && (int)g_PendingSaveSrc == SRC_DOOR && g_DoorSaveValid && g_DoorSaveWritten);
        if ((g_PendingSave == 0 || pendingDoorAlreadyFlushed) && g_PendingLoad == 0 &&
            *(volatile DWORD*)ADDR_SAVE_POOL == 0 &&
            (now - g_LastSnapshotTick >= 350) && IsSafeToSaveNow(NULL)) {
            if (g_PreDoorImageValid) {
                memcpy(g_PrevPreDoorImage, g_PreDoorImage, SIZE_SAVE_IMAGE);
                g_PrevPreDoorRoom    = g_PreDoorRoom;
                g_PrevPreDoorPos[0]  = g_PreDoorPos[0];
                g_PrevPreDoorPos[1]  = g_PreDoorPos[1];
                g_PrevPreDoorPos[2]  = g_PreDoorPos[2];
                g_PrevPreDoorChapter = g_PreDoorChapter;
                g_PrevPreDoorDiff    = g_PreDoorDiff;
                g_PrevPreDoorHP      = g_PreDoorHP;
                g_PrevPreDoorTick    = g_LastSnapshotTick;
                g_PrevPreDoorImageValid = TRUE;
            }
            InterlockedExchange(&g_InSnapshot, 1);
            PackLiveToBuffer(g_PreDoorImage, &g_PreDoorRoom, g_PreDoorPos,
                             &g_PreDoorChapter, &g_PreDoorDiff, &g_PreDoorHP, NULL);
            InterlockedExchange(&g_InSnapshot, 0);
            g_PreDoorImageValid = TRUE;
            g_LastSnapshotTick = now;
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
                int saveSrc = (int)InterlockedExchange(&g_PendingSaveSrc, 0);
                if (saveSrc == SRC_DOOR && g_DoorSaveValid && g_DoorSaveWritten) {
                    Log("[Autosave] [DoorSeq] Deferred SRC_DOOR already written by early flush; skipping duplicate\n");
                    g_DoorSeqTick = now;
                } else {
                    DoAutosave(saveSrc);
                }
            }
        } else if ((LONG)now - g_SaveWaitLogTick > 3000) {
            g_SaveWaitLogTick = (LONG)now;
            Log("[Autosave] [Pump] queued save waiting for safe state (%s)\n", blockWhy ? blockWhy : "?");
        }
    }
    g_InPump = 0;
}

// Trampolines & Hooks

extern "C" void __cdecl OnDoorEnterC(WORD nextRoom) {
    g_LastRoomId = nextRoom;
    DWORD now = GetTickCount();
    if (g_DoorSeqActive && g_DoorSaveValid && (now - g_DoorSeqTick < 8000)) {
        // Same door sequence: keep the frozen pre-door image and extend the
        // cover window. Do NOT clear the flag after the first event, otherwise
        // a second room transition (e.g. vestibule -> inner hall) overwrites
        // the quick save with the position inside the destination room.
        g_DoorSeqTick = now;
        Log("[Autosave] [DoorSeq] DoorEnter 0x%04X covered by frozen pre-door snapshot (Pos [%.1f, %.1f, %.1f])\n",
            nextRoom, g_DoorSavePos[0], g_DoorSavePos[1], g_DoorSavePos[2]);
        return;
    }
    ClearDoorSequence("DoorEnter outside active sequence");
    QueueSaveC(SRC_DOOR);
}

// 1. Seamless door transition room update at 0x002EF5CB (7 bytes replaced)
// Original: 66 89 1D C2 9A DB 00 (mov word ptr [0x00DB9AC2], bx)
static void __declspec(naked) Hook_DoorEnter_Stub() {
    __asm {
        mov word ptr ds:[0x00DB9AC2], bx
        cmp byte ptr ds:[0x0058A389], 0
        jne SkipDoorSave
        pushad
        pushfd
        movzx eax, bx
        push eax
        call OnDoorEnterC
        add esp, 4
        popfd
        popad
    SkipDoorSave:
        push 0x002EF5D2
        ret
    }
}

static BOOL IsHardExcludedNonDoorOpcode(DWORD op) {
    return (op == 0x82000123 || // Dragon Statue
            op == 0x82000122 || // Muramasa Shop
            op == 0x82000121 || // UI / save menu
            op == 0x82000111 || // examine / text dialog
            op == 0x82000115 || // Ch6 chalice altar
            op == 0x8200011F || // missing item / locked prompt
            op == 0x82000083 || // key / prompt UI
            op == 0x820000ED || // give item
            op == 0x8200011D);  // chest model open
}

// These opcodes appear in chests/statues, but also legitimately appear inside
// direct-animation sliding door triggers that move Ryu with MOVE_RYU (0x820000DC).
static BOOL IsSoftDoorAnimOpcode(DWORD op) {
    return (op == 0x82000131 || // chest open / player door-slide anim
            op == 0x820000AE || // statue restore / lock player control
            op == 0x820000AC);  // statue restore / lock camera
}

// Checks whether a trigger's condition bytecode contains any spatial/area/proximity
// opcode (0x8200001F .. 0x82000025). Triggers without spatial conditions (such as
// room-wide 4F(0x11) skip/reset helpers) can fire anywhere on A/X button presses.
static BOOL HasSpatialCondition(const DWORD* cond, const DWORD* act) {
    if (!cond) return FALSE;
    int maxDwords = 256;
    if (act && act > cond) {
        size_t diff = (size_t)(act - cond);
        if (diff < (size_t)maxDwords) maxDwords = (int)diff;
    }
    for (int i = 0; i < maxDwords; ++i) {
        DWORD op = cond[i];
        if (op == 0x82000142) break;
        if (op >= 0x8200001F && op <= 0x82000025) return TRUE;
    }
    return FALSE;
}

// Inspects a target trigger activated via 0x820000D6 <idx> 1 (e.g. Ninja Fortress
// sliding fusuma doors where the button trigger only enables the door-walk animation trigger).
static BOOL IsRelayDoorTarget(DWORD targetIdx, int depth) {
    if (depth > 2 || targetIdx >= 0x380) return FALSE;
    const BYTE* tTrig = (const BYTE*)(0x00D53320 + targetIdx * 0x68);
    if (*(const DWORD*)tTrig == 0) return FALSE;
    const DWORD* tAct = *(const DWORD**)(tTrig + 8);
    if (!tAct) return FALSE;

    BOOL hasFade30 = FALSE;
    BOOL hasAnyFadeB6 = FALSE;
    BOOL hasMoveRyuDC = FALSE;
    BOOL hasObjAnim5B = FALSE;
    BOOL hasOp73 = FALSE;
    BOOL hasSwitch13B = FALSE;
    DWORD subTarget = 0xFFFFFFFF;

    for (int i = 0; i < 256; ++i) {
        DWORD op = tAct[i];
        if (op == 0x82000142) break;
        if (IsHardExcludedNonDoorOpcode(op)) {
            return FALSE;
        }
        if (op == 0x820000B6) {
            hasAnyFadeB6 = TRUE;
            if (i + 1 < 256 && tAct[i + 1] == 0x0000001E) hasFade30 = TRUE;
        } else if (op == 0x820000DC) {
            hasMoveRyuDC = TRUE;
        } else if (op == 0x8200005B) {
            hasObjAnim5B = TRUE;
        } else if (op == 0x82000073) {
            hasOp73 = TRUE;
        } else if (op == 0x8200013B) {
            hasSwitch13B = TRUE;
        } else if (op == 0x820000D6 && i + 2 < 256 && tAct[i + 2] == 1 && tAct[i + 1] < 0x380) {
            if (subTarget == 0xFFFFFFFF && tAct[i + 1] != targetIdx) {
                subTarget = tAct[i + 1];
            }
        }
    }

    if (hasFade30 || hasSwitch13B ||
        (hasMoveRyuDC && (hasObjAnim5B || hasOp73 || hasAnyFadeB6))) {
        return TRUE;
    }
    if (depth < 1 && subTarget != 0xFFFFFFFF) {
        return IsRelayDoorTarget(subTarget, depth + 1);
    }
    return FALSE;
}

extern "C" void __cdecl OnDoorInteractCheckC(const BYTE* trig) {
    if (!trig) return;
    if (*(BYTE*)0x0058A389 != 0) return; // suppress during cutscene / movie
    __try {
        // Only match at script start (state == 1 or action cursor == 0), never mid-animation waits.
        BYTE trigState = *(const BYTE*)(trig + 0x24);
        DWORD actCursor = *(const DWORD*)(trig + 0x0C);
        if (trigState != 1 && actCursor != 0) return;

        const DWORD* cond = *(const DWORD**)(trig + 4);
        const DWORD* act = *(const DWORD**)(trig + 8);
        if (!act) return;

        DWORD promptPressed = *(const DWORD*)0x00D52CE8;
        BOOL hardExcluded = FALSE;
        BOOL softExcluded = FALSE;
        BOOL hasFade30 = FALSE;
        BOOL hasAnyFadeB6 = FALSE;
        BOOL hasTeleport66 = FALSE;
        BOOL hasMoveRyuDC = FALSE;
        BOOL hasObjAnim5B = FALSE;
        BOOL hasOp73 = FALSE;
        BOOL hasRoomPrep13D = FALSE;
        BOOL hasAnySwitch13B = FALSE;
        BOOL hasImmediateSwitch13B = FALSE;
        DWORD relayTargets[4] = { 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF };
        int relayCount = 0;

        for (int i = 0; i < 256; ++i) {
            DWORD op = act[i];
            if (op == 0x82000142) break;
            if (IsHardExcludedNonDoorOpcode(op)) {
                hardExcluded = TRUE;
                break;
            }
            if (IsSoftDoorAnimOpcode(op)) {
                softExcluded = TRUE;
                continue;
            }
            if (op == 0x820000B6) {
                hasAnyFadeB6 = TRUE;
                if (i + 1 < 256 && act[i + 1] == 0x0000001E) {
                    hasFade30 = TRUE;
                }
            } else if (op == 0x82000066) {
                hasTeleport66 = TRUE;
            } else if (op == 0x820000DC) {
                hasMoveRyuDC = TRUE;
            } else if (op == 0x8200005B) {
                hasObjAnim5B = TRUE;
            } else if (op == 0x82000073) {
                hasOp73 = TRUE;
            } else if (op == 0x8200013D) {
                hasRoomPrep13D = TRUE;
            } else if (op == 0x8200013B) {
                hasAnySwitch13B = TRUE;
                if (i < 24) {
                    hasImmediateSwitch13B = TRUE;
                }
            } else if (op == 0x820000D6 && i + 2 < 256 && act[i + 2] == 1 && act[i + 1] < 0x380) {
                if (relayCount < 4) {
                    relayTargets[relayCount++] = act[i + 1];
                }
            }
        }

        if (hardExcluded) return;

        BOOL hasSpatialCond = HasSpatialCondition(cond, act);
        BOOL allowPromptDoor = (promptPressed != 0 && hasSpatialCond);

        BOOL isDirectAnimDoor = (allowPromptDoor && hasMoveRyuDC &&
                                 (hasObjAnim5B || hasOp73 || hasAnyFadeB6));
        if (softExcluded && !isDirectAnimDoor) return;

        BOOL isFadeDoor   = (allowPromptDoor && !softExcluded && hasFade30);
        BOOL isAnimDoor   = (allowPromptDoor && !softExcluded && hasTeleport66 &&
                             (hasObjAnim5B || hasRoomPrep13D || hasAnySwitch13B || hasAnyFadeB6));
        BOOL isRelayDoor  = FALSE;
        if (allowPromptDoor && !softExcluded && !isFadeDoor && !isAnimDoor &&
            !isDirectAnimDoor && relayCount > 0) {
            for (int r = 0; r < relayCount; ++r) {
                if (IsRelayDoorTarget(relayTargets[r], 0)) {
                    isRelayDoor = TRUE;
                    break;
                }
            }
        }
        BOOL isWalkPortal = (!softExcluded && hasImmediateSwitch13B);
        if (!isFadeDoor && !isAnimDoor && !isRelayDoor && !isDirectAnimDoor && !isWalkPortal) return;

        DWORD now = GetTickCount();
        if (trig == g_DoorSeqTrig && (now - g_DoorSeqTick < 3000)) {
            return;
        }
        // Do not start a second capture while a door animation/transition from the
        // current sequence is already underway (e.g. an auxiliary 4F(0x11) skip/fade
        // trigger firing mid-animation after MOVE_RYU 0xDC has begun).
        if (g_DoorSeqActive && g_DoorSaveValid && (now - g_DoorSeqTick < 5000)) {
            BOOL midAnimOrTransition = (*(BYTE*)ADDR_RYU_EVENT_LOCK != 0) ||
                                       ((*(DWORD*)0x00C0611C & 1) != 0) ||
                                       (*(BYTE*)ADDR_ROOM_TRANSITION != 0);
            if (midAnimOrTransition || !(promptPressed != 0 && trig != g_DoorSeqTrig)) {
                return;
            }
        }

        const char* kind = isFadeDoor ? "Fade"
                         : (isAnimDoor ? "Anim/Unbar"
                         : (isRelayDoor ? "Sliding/Relay"
                         : (isDirectAnimDoor ? "Sliding/Direct" : "Portal")));
        Log("[Autosave] Pre-mutation door trigger detected (%s, trig=%p, act=%p, prompt=%u, state=%u, cursor=%u)\n",
            kind, trig, act, promptPressed, (unsigned)trigState, (unsigned)actCursor);

        BOOL preferRollingSnapshot = (!isFadeDoor && !isAnimDoor && !isRelayDoor && !isDirectAnimDoor);
        SavePreDoorNow(trig, preferRollingSnapshot);
    } __except (EXCEPTION_EXECUTE_HANDLER) {
    }
}

// 1b. Pre-mutation stage trigger activation at 0x002DF46E (6 bytes replaced)
// Original: 80 7E 24 01 75 07 (cmp byte ptr [esi+0x24], 1; jne 0x002DF47B)
static void __declspec(naked) Hook_DoorInteract_Stub() {
    __asm {
        pushad
        pushfd
        push esi
        call OnDoorInteractCheckC
        add esp, 4
        popfd
        popad
        cmp byte ptr [esi + 0x24], 1
        jne InteractNotOne
        push 0x002DF474
        ret
    InteractNotOne:
        push 0x002DF47B
        ret
    }
}

// 2a & 2b. Dragon Statue / Chapter Clear save hooks at BOTH 0x001DA15F (new slot) and 0x001DA1EE (overwrite slot)
extern "C" void __cdecl Hook_ShrineSave_Callback(int res, const char* pathOut) {
    if (res == 0 && pathOut && pathOut[0]) {
        Log("[Autosave] [NativeSave] Manual save recorded: %s (Chapter %u, Diff %u, Room 0x%04X)\n",
            pathOut, *(BYTE*)ADDR_FIELD_CHAPTER, *(BYTE*)ADDR_FIELD_DIFFICULTY,
            *(WORD*)ADDR_FIELD_SAVED_ROOM);
        // Queue an autosave into our dedicated Autosave slot so quicksave stays in sync,
        // without overwriting g_SlotPath with the player's manual dragon shrine slot!
        QueueSaveC(SRC_SHRINE);
    }
    // Cancel any pending pre-transition autosave so next chapter starts clean
    InterlockedExchange(&g_PendingSave, 0);
    // A native shrine save is a live checkpoint; drop any frozen door sequence.
    AbandonDoorSequence("native shrine save");
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

// 3. Runs on every function return in the game (all threads); only acts on the game thread.
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

// 4. Intercepts State 9 Case 3/4 checkpoint load at 0x0016656A (5 bytes replaced)
// Original: E8 11 51 00 00 (call 0x0016B680)
static void __declspec(naked) Hook_Case3_Load_Stub() {
    __asm {
        push dword ptr [esp + 4]
        call Hook_CheckpointLoad_Impl
        add esp, 4
        ret
    }
}

// 5. Intercepts Game Over loop tick at 0x002E08EA (5 bytes replaced)
// Original: E8 01 1E F2 FF (call 0x2026f0)
static void __declspec(naked) Hook_GameOver_Tick_Stub() {
    __asm {
        mov eax, 0x002026F0
        call eax

        cmp g_PendingLoad, 1
        jne CheckAutoloadPending
        cmp g_AutosaveValid, 1
        jne SkipQuickLoad
        cmp byte ptr ds:[g_SlotPath], 0
        je SkipQuickLoad
        jmp TriggerGameOverQuickLoad

    CheckAutoloadPending:
        cmp g_AutoloadPending, 1
        je TriggerGameOverQuickLoad
        jmp SkipQuickLoad

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

    SkipQuickLoad:
        push 0x002E08EF
        ret
    }
}

// 6a. Save game enumeration slot filter at 0x001DA26D (11 bytes replaced)
// Filters out non-numbered saves (e.g. "Autosave") so the native Save Game and Load Game menus
// only see and manage legitimate numbered slots (1..30), avoiding out-of-bounds corruption in 0x001DA500.
// Original: E8 A5 46 19 00 83 C4 0C 8B D8 4B (call 0x36e917; add esp, 0xc; mov ebx, eax; dec ebx)
static void __declspec(naked) Hook_SaveEnum_Filter_Stub() {
    __asm {
        mov eax, 0x0036E917 // wcstol
        call eax
        add esp, 0x0C

        // Check if 1 <= eax && eax <= 30
        mov ecx, eax
        dec ecx
        cmp ecx, 30
        jae skip_invalid_slot

        // Valid slot (0 <= ecx < 30)
        mov ebx, eax
        dec ebx
        push 0x001DA278
        ret

    skip_invalid_slot:
        pop ebx
        pop edi
        pop esi
        xor al, al
        pop ebp
        add esp, 8
        ret 8
    }
}

// 6b. Game Over Continue hook at 0x002E0C9F (7 bytes replaced)
// If a valid quicksave exists, player confirming "Yes" (Continue) recovers directly from the quicksave!
// Original: 80 3D 8A A3 58 00 FF (cmp byte ptr [0x0058A38A], 0xFF)
static void __declspec(naked) Hook_GameOver_Continue_Stub() {
    __asm {
        cmp g_AutosaveValid, 1
        jne NormalContinueCheck
        cmp byte ptr ds:[g_SlotPath], 0
        je NormalContinueCheck

        // Autosave is valid! Arm autoload and continue
        mov g_AutoloadPending, 1
        cmp byte ptr ds:[0x0058A38A], 0xFF
        jne AutoSlotOk
        mov byte ptr ds:[0x0058A38A], 0
    AutoSlotOk:
        mov eax, 0x002E15E0
        call eax
        mov bl, 1
        push 0x002E0BB3
        ret

    NormalContinueCheck:
        cmp byte ptr ds:[0x0058A38A], 0xFF
        jne NormalContinueProceed
        mov bl, 3
        push 0x002E0BB3
        ret

    NormalContinueProceed:
        mov eax, 0x002E15E0
        call eax
        mov bl, 1
        push 0x002E0BB3
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
    Log("[Autosave] [UnpackHook] Stats unpacked: MaxKi=%u, CurKi=%u, EquipNinpo=0x%04X\n",
        maxKi, curKi, liveEquipNinpo);

    // If player has Ninpo equipped/unlocked, but MaxKi or CurKi was zeroed, repair it immediately!
    if (liveEquipNinpo != 0 && liveEquipNinpo != 0xFFFF) {
        if (maxKi < 200) {
            maxKi = 400; // 2 slots
            curKi = 400; // 2 filled slots
            *(WORD*)ADDR_SAVE_MAX_KI = maxKi;
            *(WORD*)ADDR_SAVE_CUR_KI = curKi;
            *(WORD*)ADDR_RYU_CUR_KI  = curKi;
            Log("[Autosave] [UnpackHook] Repaired zeroed stats -> MaxKi=400, CurKi=400 (Ninpo: 0x%04X)\n", liveEquipNinpo);
        } else if (curKi < 200) {
            curKi = maxKi;
            *(WORD*)ADDR_SAVE_CUR_KI = curKi;
            *(WORD*)ADDR_RYU_CUR_KI  = curKi;
            Log("[Autosave] [UnpackHook] Repaired zeroed CurKi -> %u (MaxKi=%u, Ninpo: 0x%04X)\n",
                curKi, maxKi, liveEquipNinpo);
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
    static const BYTE door[7]       = { 0x66, 0x89, 0x1D, 0xC2, 0x9A, 0xDB, 0x00 };
    static const BYTE doorInt[6]    = { 0x80, 0x7E, 0x24, 0x01, 0x75, 0x07 };
    static const BYTE saveEnum[5]   = { 0xE8, 0xA5, 0x46, 0x19, 0x00 };
    static const BYTE goContinue[7] = { 0x80, 0x3D, 0x8A, 0xA3, 0x58, 0x00, 0xFF };
    static const BYTE shrine[1]     = { 0xE8 };
    static const BYTE cookie[6]     = { 0x3B, 0x0D, 0xD8, 0xCC, 0x41, 0x00 };
    static const BYTE case3[5]      = { 0xE8, 0x11, 0x51, 0x00, 0x00 };
    static const BYTE gameOver[5]   = { 0xE8, 0x01, 0x1E, 0xF2, 0xFF };
    static const BYTE spirit[7]     = { 0x66, 0x89, 0x82, 0xCC, 0x01, 0x00, 0x00 };
    static const BYTE unpack[7]     = { 0x66, 0x89, 0x0D, 0x6C, 0xA5, 0x58, 0x00 };
    return BytesMatch(ADDR_HOOK_DOOR, door, 7) &&
           BytesMatch(ADDR_HOOK_DOOR_INTERACT, doorInt, 6) &&
           BytesMatch(ADDR_HOOK_SAVE_ENUM, saveEnum, 5) &&
           BytesMatch(ADDR_HOOK_GAMEOVER_CONTINUE, goContinue, 7) &&
           BytesMatch(ADDR_HOOK_SHRINE_NEW, shrine, 1) &&
           BytesMatch(ADDR_HOOK_SHRINE_OVER, shrine, 1) &&
           BytesMatch(ADDR_COOKIE_CHECK, cookie, 6) &&
           BytesMatch(ADDR_HOOK_CASE3_LOAD, case3, 5) &&
           BytesMatch(ADDR_HOOK_GAMEOVER_TICK, gameOver, 5) &&
           BytesMatch(ADDR_HOOK_USE_SPIRIT, spirit, 7) &&
           BytesMatch(ADDR_HOOK_UNPACK_KI, unpack, 7);
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

    // 1b. Pre-mutation stage trigger activation (0x002DF46E), 6 bytes replaced (5-byte jmp + 1 NOP)
    VirtualProtect((void*)ADDR_HOOK_DOOR_INTERACT, 16, PAGE_EXECUTE_READWRITE, &oldProtect);
    BYTE jmpDoorInt[6] = { 0xE9, 0, 0, 0, 0, 0x90 };
    DWORD relDoorInt = (DWORD)Hook_DoorInteract_Stub - (ADDR_HOOK_DOOR_INTERACT + 5);
    memcpy(&jmpDoorInt[1], &relDoorInt, 4);
    memcpy((void*)ADDR_HOOK_DOOR_INTERACT, jmpDoorInt, 6);
    VirtualProtect((void*)ADDR_HOOK_DOOR_INTERACT, 16, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)ADDR_HOOK_DOOR_INTERACT, 16);

    // 2. Save game enumeration slot filter (0x001DA26D), 11 bytes replaced (5-byte jmp + 6 NOPs)
    VirtualProtect((void*)ADDR_HOOK_SAVE_ENUM, 16, PAGE_EXECUTE_READWRITE, &oldProtect);
    BYTE jmpEnum[11] = { 0xE9, 0, 0, 0, 0, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90 };
    DWORD relEnum = (DWORD)Hook_SaveEnum_Filter_Stub - (ADDR_HOOK_SAVE_ENUM + 5);
    memcpy(&jmpEnum[1], &relEnum, 4);
    memcpy((void*)ADDR_HOOK_SAVE_ENUM, jmpEnum, 11);
    VirtualProtect((void*)ADDR_HOOK_SAVE_ENUM, 16, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)ADDR_HOOK_SAVE_ENUM, 16);

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

    // 6a. Game Over loop tick (0x002E08EA), 5-byte jump
    PatchJump5(ADDR_HOOK_GAMEOVER_TICK, (void*)Hook_GameOver_Tick_Stub);

    // 6b. Game Over Continue hook (0x002E0C9F), 7 bytes replaced (5-byte jmp + 2 NOPs)
    VirtualProtect((void*)ADDR_HOOK_GAMEOVER_CONTINUE, 16, PAGE_EXECUTE_READWRITE, &oldProtect);
    BYTE jmpGOC[7] = { 0xE9, 0, 0, 0, 0, 0x90, 0x90 };
    DWORD relGOC = (DWORD)Hook_GameOver_Continue_Stub - (ADDR_HOOK_GAMEOVER_CONTINUE + 5);
    memcpy(&jmpGOC[1], &relGOC, 4);
    memcpy((void*)ADDR_HOOK_GAMEOVER_CONTINUE, jmpGOC, 7);
    VirtualProtect((void*)ADDR_HOOK_GAMEOVER_CONTINUE, 16, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)ADDR_HOOK_GAMEOVER_CONTINUE, 16);

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

    // 9. Unlock all difficulties (Hard, Very Hard, Master Ninja) via 0x001DB598 jump table
    VirtualProtect((void*)ADDR_UNLOCK_HARD, 12, PAGE_EXECUTE_READWRITE, &oldProtect);
    *(DWORD*)ADDR_UNLOCK_HARD         = ADDR_UNLOCK_TARGET_FUNC;
    *(DWORD*)ADDR_UNLOCK_VERY_HARD    = ADDR_UNLOCK_TARGET_FUNC;
    *(DWORD*)ADDR_UNLOCK_MASTER_NINJA = ADDR_UNLOCK_TARGET_FUNC;
    VirtualProtect((void*)ADDR_UNLOCK_HARD, 12, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)ADDR_UNLOCK_HARD, 12);

    Log("[Autosave] [Verify] door=%02X saveEnum=%02X goCont=%02X shrineNew=%02X shrineOver=%02X pump=%02X case3=%02X gameOver=%02X spirit=%02X unpack=%02X hardUnlock=%08X | PID=%u\n",
        *(BYTE*)ADDR_HOOK_DOOR,
        *(BYTE*)ADDR_HOOK_SAVE_ENUM, *(BYTE*)ADDR_HOOK_GAMEOVER_CONTINUE,
        *(BYTE*)ADDR_HOOK_SHRINE_NEW, *(BYTE*)ADDR_HOOK_SHRINE_OVER,
        *(BYTE*)ADDR_COOKIE_CHECK, *(BYTE*)ADDR_HOOK_CASE3_LOAD, *(BYTE*)ADDR_HOOK_GAMEOVER_TICK,
        *(BYTE*)ADDR_HOOK_USE_SPIRIT, *(BYTE*)ADDR_HOOK_UNPACK_KI,
        *(DWORD*)ADDR_UNLOCK_HARD,
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
    Log("[Autosave] [Stats] hooks fired: Door=%d ChapterStart=%d Encounter=%d ShrineSave=%d | gameTid=%u slotValid=%d pendingSave=%d pendingLoad=%d\n",
        g_HookCount[SRC_DOOR], g_HookCount[SRC_CHAPTER_START], g_HookCount[SRC_ENEMY_ENCOUNTER], g_HookCount[SRC_SHRINE],
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
        if (IsMapped(0x00010000) && IsMapped(ADDR_HOOK_DOOR) &&
            IsMapped(ADDR_HOOK_DOOR_INTERACT) &&
            IsMapped(ADDR_HOOK_SAVE_ENUM) &&
            IsMapped(ADDR_HOOK_GAMEOVER_CONTINUE) && IsMapped(ADDR_UNLOCK_HARD) &&
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
                    InterlockedExchange(&g_PendingSaveSrc, 0);
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
