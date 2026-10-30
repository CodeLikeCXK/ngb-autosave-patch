#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <stdio.h>
#include <stdarg.h>
#include <intrin.h>

// Exports are declared via linker pragmas (no .def, no d3d9.h) so names are exact.
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
typedef void* (WINAPI *PFN_Direct3DCreate9)(UINT SDKVersion);
typedef HRESULT (WINAPI *PFN_Direct3DCreate9Ex)(UINT SDKVersion, void** ppD3D);

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
static volatile LONG g_LogLock = 0;   // tiny spinlock: Log() is called from the worker AND the game thread

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

// Addresses in default.xbe (virtual addresses, XBE is mapped 1:1 in the process)
#define ADDR_SAVE_IMAGE         0x00572F40
#define SIZE_SAVE_IMAGE         0x17460
#define ADDR_FIELD_PACKED_VALID 0x00589753   // byte (1 = mid-stage packed position/room valid)
#define ADDR_FIELD_CHAPTER      0x00589755   // byte (Chapter ID)
#define ADDR_FIELD_STATE_MODE   0x0058975A   // byte (1 = Alive, 2 = Dead/GameOver)
#define ADDR_FIELD_WIPE_FLAG    0x0058975B   // byte (non-zero wipes save image on 0x2ec1c0)
#define ADDR_FIELD_SAVED_ROOM   0x0058975E   // word (Saved Room ID packed by 0x2fbde0)
#define ADDR_FIELD_CHAP_TRANS   0x0058A389   // byte (1 = chapter transition)
#define ADDR_FIELD_SLOT_INDEX   0x0058A38A   // byte (save slot index, 0xFF = none)
#define ADDR_FIELD_SPAWN_POINT  0x0058A38C   // word (Spawn/Checkpoint ID)
#define ADDR_RYU_HP             0x0058A566   // word (Ryu current HP)
#define ADDR_RYU_SPAWNED        0x0058A594   // byte (1 = Ryu actor spawned & active)
#define ADDR_RYU_MATRIX         0x004B4E50   // 4x4 float matrix (Ryu transform)
#define ADDR_RYU_POS            0x004B5710   // vec4 float (Ryu live world position)
#define ADDR_RYU_EVENT_LOCK     0x004B75DE   // byte (non-zero = cutscene, grab, or scripted lock on Ryu)
#define ADDR_RYU_ACTION_ID      0x004B7640   // byte (>= 0x20 = scripted event action)
#define ADDR_ROOM_TRANSITION    0x00D6A11E   // byte (1 = door/room transition in progress)
#define ADDR_LIVE_BGM_TRACK     0x00D5268E   // word (currently playing live BGM track)

#define ADDR_TASK1_STATE        0x007F1B12   // byte (0 = respawn Task 1, 1 = active gameplay, 2 = room load/popup)
#define ADDR_GLOBAL_STATE       0x00DB5A60   // byte (5 = Story Gameplay, 9 = Transition, 0x0C = Mission Gameplay)
#define ADDR_PAUSE_DEPTH        0x00DB5A68   // byte (0 = unpaused, >0 = pause menu open)
#define ADDR_STAGE_SUBSTATE     0x00DB9894   // byte (3 = active room gameplay, 0x80 = Game Over loop)
#define ADDR_CURRENT_ROOM       0x00DB9AC2   // word (current loaded Room ID, 0x0200 = none)
#define ADDR_STATE_TRIGGER      0x00DB9AD6   // byte (3 = stop tasks & trigger reload)
#define ADDR_CUTSCENE_ID        0x00DB9C6E   // word (0xFFFF = no cutscene playing)
#define ADDR_INTERACTION_LOCK   0x00D52B37   // byte (1 = door/chest/safe/shrine interaction active)
#define ADDR_SAVE_POOL          0x00C05FE8   // dword: heap used by the save routines while they run

// Xbox controller internal state in default.xbe
#define ADDR_ACTIVE_PAD_PORT    0x00DB932E   // byte (0..3)
#define ADDR_PAD_BASE           0x00D219A0   // dword buttons at [port * 0x78 + 0x00D219A0]
#define PAD_STRIDE              0x78
#define XBE_BTN_START           0x00000010
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
#define ADDR_HOOK_SHRINE        0x001DA15F   // Dragon statue save call (5 bytes: E8 DC 56 13 00)
#define ADDR_HOOK_CASE3_LOAD    0x0016656A   // State 9 Case 3 checkpoint load: call 0x16b680 (5 bytes: E8 11 51 00 00)
#define ADDR_HOOK_GAMEOVER_TICK 0x002E08EA   // GameOver loop tick: call 0x2026f0 (5 bytes: E8 01 1E F2 FF)

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

// Checks if the game is currently in unpaused, active gameplay where packing & saving Ryu's state is safe.
static BOOL IsSafeToSaveNow() {
    BYTE gstate = *(BYTE*)ADDR_GLOBAL_STATE;
    if (gstate != 5 && gstate != 0x0C) return FALSE;
    if (*(BYTE*)ADDR_TASK1_STATE != 1) return FALSE;          // not in active Task 1 state (e.g. room loading / item popup)
    if (*(BYTE*)ADDR_STAGE_SUBSTATE != 3) return FALSE;       // not in active room frame (e.g. entry frame 1/2 or GameOver 0x80)
    if (*(BYTE*)ADDR_PAUSE_DEPTH != 0) return FALSE;          // pause menu open
    if (*(BYTE*)ADDR_INTERACTION_LOCK != 0) return FALSE;     // door/chest/safe/shrine interaction in progress
    if (*(BYTE*)ADDR_RYU_SPAWNED != 1) return FALSE;          // Ryu actor not spawned
    if (*(WORD*)ADDR_RYU_HP == 0) return FALSE;               // Ryu is dead / dying
    if (*(BYTE*)ADDR_FIELD_STATE_MODE == 2) return FALSE;     // GameOver state mode
    if (*(WORD*)ADDR_CUTSCENE_ID != 0xFFFF) return FALSE;     // cutscene playing

    // Chapter transition in progress
    if (*(BYTE*)ADDR_FIELD_CHAP_TRANS != 0) return FALSE;

    // Room / door transition in progress
    if (*(BYTE*)ADDR_ROOM_TRANSITION != 0) return FALSE;

    // State trigger / reload in progress
    if (*(BYTE*)ADDR_STATE_TRIGGER != 0) return FALSE;

    // Ryu locked in cutscene, grab, or scripted sequence
    if (*(BYTE*)ADDR_RYU_EVENT_LOCK != 0) return FALSE;

    // Ryu in scripted event action
    if (*(BYTE*)ADDR_RYU_ACTION_ID >= 0x20) return FALSE;

    // Grace period after chapter start (8000 ms)
    DWORD now = GetTickCount();
    if (now - g_ChapterStartTick < 8000) return FALSE;

    // Grace period after quickload (3000 ms)
    if (now - g_LastLoadTick < 3000) return FALSE;

    WORD curRoom = *(WORD*)ADDR_CURRENT_ROOM;
    if (curRoom == 0x0200 || curRoom == 0xFFFF) return FALSE; // invalid room

    // Void fall safety check: do not save if Ryu's Y is below -2000.0f
    float py = *(float*)(ADDR_RYU_POS + 4);
    if (py < -2000.0f) return FALSE;

    return TRUE;
}

// Packs Ryu's live world position, rotation matrix, HP, inventory, and room objects into 0x00572F40,
// then writes the save buffer to disk via 0x0030F840. Must run on the game thread.
static BOOL DoAutosave() {
    __try {
        if (!IsSafeToSaveNow()) {
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
        WORD savedRoom = *(WORD*)ADDR_FIELD_SAVED_ROOM;
        float px = *(float*)(ADDR_RYU_POS + 0);
        float py = *(float*)(ADDR_RYU_POS + 4);
        float pz = *(float*)(ADDR_RYU_POS + 8);
        Log("[Autosave] Saving (Chapter %d, Room 0x%04X, Pos [%.1f, %.1f, %.1f], HP %u, BGM 0x%02X)...\n",
            chapter, savedRoom, px, py, pz, *(WORD*)ADDR_RYU_HP, musicIdx);

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

        // CRITICAL FIX: Immediately restore live memory PACKED_VALID = 0!
        // PACKED_VALID = 1 is saved inside the file on disk for autoloading,
        // but live gameplay memory MUST have PACKED_VALID = 0.
        // If left as 1, the game bypasses real-time cutscenes (0x002DF940) and plays wrong BGM (0x002E20A5)!
        *(BYTE*)ADDR_FIELD_PACKED_VALID = 0;

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
    }
    return FALSE;
}

// Intercepts State 9 Case 3 checkpoint file loader (0x0016656A).
// When g_AutoloadPending is armed (via F9 or controller combo), loads our autosave file into 0x00572F40
// and configures mid-stage packed flags. The engine's native State 9 -> State 5 pipeline then handles
// screen fade, archive caching, task creation (including Task 6 renderer and Task 2 camera), and Ryu spawn!
extern "C" int __cdecl Hook_CheckpointLoad_Impl(int slotIdx) {
    if (g_AutoloadPending) {
        if (!g_AutosaveValid || !g_SlotPath[0]) {
            Log("[Autosave] Autoload requested but no valid slot exists\n");
            g_AutoloadPending = 0;
            return 0;
        }
        Log("[Autosave] State 9 Case 3: loading autosave from '%s' into 0x00572F40...\n", g_SlotPath);
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

            // Ensure state mode is Alive
            *(BYTE*)ADDR_FIELD_STATE_MODE   = 1; // Alive
            *(BYTE*)ADDR_FIELD_WIPE_FLAG    = 0;
            *(BYTE*)ADDR_FIELD_SLOT_INDEX   = 0;
            if (wasPacked) {
                *(BYTE*)ADDR_FIELD_PACKED_VALID = 1;
                *(BYTE*)ADDR_FIELD_CHAP_TRANS   = 0;
            }

            // Synchronize checkpoint backup buffer (0x007F1CA0) with the loaded image
            memcpy((void*)0x007F1CA0, (void*)ADDR_SAVE_IMAGE, SIZE_SAVE_IMAGE);

            g_LastLoadTick = GetTickCount();
            g_LastRoomId   = savedRoom;
            g_CurrentChapter = loadedChapter;
            g_AutoloadPending = 0;

            Log("[Autosave] Autoload successful (Chapter %d, Room 0x%04X, Spawn 0x%04X, Packed %d) -> resuming via native State 9 -> State 5\n",
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

    DWORD now = GetTickCount();

    // Suppress saving during chapter start grace period (8000ms)
    if (now - g_ChapterStartTick < 8000) {
        Log("[Autosave] [Hook:%s] suppressed (chapter start grace period, %u ms)\n",
            g_HookName[src & 3], now - g_ChapterStartTick);
        return;
    }

    // Suppress saving during quickload grace period (3000ms)
    if (now - g_LastLoadTick < 3000) {
        Log("[Autosave] [Hook:%s] suppressed (quickload in progress, %u ms ago)\n",
            g_HookName[src & 3], now - g_LastLoadTick);
        return;
    }

    // Suppress if chapter transition flag is active
    if (*(BYTE*)ADDR_FIELD_CHAP_TRANS != 0) {
        Log("[Autosave] [Hook:%s] suppressed (chapter transition active)\n", g_HookName[src & 3]);
        return;
    }

    if (src == SRC_ROOM) {
        // Debounce frequent room transitions
        if (now - g_LastRoomSaveTick < 2000) {
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
    if (g_GameTid == 0 || GetCurrentThreadId() != g_GameTid) return;
    if (g_InPump) return;

    BYTE curChapter = *(BYTE*)ADDR_FIELD_CHAPTER;
    DWORD now = GetTickCount();

    // 1. Chapter Change Detection:
    // If the chapter ID changed (e.g. Chapter 3 -> Chapter 4), clear any pending autosave,
    // synchronize room ID, and start the chapter grace period timer!
    if (g_CurrentChapter == 0) {
        g_CurrentChapter = curChapter;
        g_LastSavedChapter = curChapter;
        g_LastRoomId = *(WORD*)ADDR_CURRENT_ROOM;
        g_ChapterStartTick = now;
    } else if (curChapter != 0 && curChapter != g_CurrentChapter) {
        Log("[Autosave] Chapter transition detected: Chapter %u -> Chapter %u\n", g_CurrentChapter, curChapter);
        g_CurrentChapter = curChapter;
        g_LastSavedChapter = curChapter;
        g_LastRoomId = *(WORD*)ADDR_CURRENT_ROOM;
        InterlockedExchange(&g_PendingSave, 0);
        g_ChapterStartTick = now;
        *(BYTE*)ADDR_FIELD_PACKED_VALID = 0;
    }

    // 2. Room Change Detection:
    // Track room ID changes during active gameplay (catches both non-seamless 0x2DF930 and seamless 0x2EF3F0 doors)
    if (IsSafeToSaveNow()) {
        // Enforce PACKED_VALID is 0 during active gameplay
        if (*(BYTE*)ADDR_FIELD_PACKED_VALID != 0) {
            *(BYTE*)ADDR_FIELD_PACKED_VALID = 0;
        }

        WORD curRoom = *(WORD*)ADDR_CURRENT_ROOM;
        if (g_LastRoomId == 0xFFFF) {
            g_LastRoomId = curRoom;
        } else if (curRoom != g_LastRoomId) {
            WORD prevRoom = g_LastRoomId;
            g_LastRoomId = curRoom;
            Log("[Autosave] Room transition detected: 0x%04X -> 0x%04X\n", prevRoom, curRoom);
            QueueSaveC(SRC_ROOM);
        }
    }

    if (!(g_PendingSave | g_PendingLoad)) return;

    // Never interrupt the game's own save routine (it owns the global pool while running)
    DWORD pool = *(volatile DWORD*)ADDR_SAVE_POOL;
    if (pool != 0) {
        if ((LONG)now - g_PumpBusyLogTick > 2000) {   // throttled
            g_PumpBusyLogTick = (LONG)now;
            Log("[Autosave] [Pump] request pending but save pool busy (0x%08X) - waiting\n", pool);
        }
        return;
    }

    g_InPump = 1;
    if (g_PendingLoad) {
        BYTE subState  = *(BYTE*)ADDR_STAGE_SUBSTATE;
        BYTE gstate    = *(BYTE*)ADDR_GLOBAL_STATE;
        BYTE taskState = *(BYTE*)ADDR_TASK1_STATE;
        BYTE pauseDep  = *(BYTE*)ADDR_PAUSE_DEPTH;
        BYTE stateMode = *(BYTE*)ADDR_FIELD_STATE_MODE;

        if (subState == 0x80) {
            // Inside Game Over screen (0x002E06E0): Hook_GameOver_Tick_Stub (0x002E08EA) will consume
            // g_PendingLoad on the next tick, restore archive 0x647, and trigger State 5 -> State 9 reload.
        } else if ((gstate == 5 || gstate == 0x0C) && taskState == 1 && subState == 3 && pauseDep == 0 && stateMode != 2) {
            // Active gameplay: arm g_AutoloadPending and set [0x00DB9AD6] = 3 so State 5 cleanly stops tasks
            // at the end of the frame (0x00166787) and naturally transitions to State 9 Case 3!
            if (InterlockedCompareExchange(&g_PendingLoad, 0, 1) == 1) {
                InterlockedExchange(&g_PendingSave, 0);
                if (!g_AutosaveValid || !g_SlotPath[0]) {
                    Log("[Autosave] Quickload requested in gameplay, but no valid autosave slot exists.\n");
                } else {
                    g_AutoloadPending = 1;
                    *(BYTE*)ADDR_STATE_TRIGGER = 3;
                    Log("[Autosave] Quickload armed in active gameplay (StateTrigger=3)\n");
                }
            }
        }
    } else if (g_PendingSave) {
        // Wait until any door transition, room load, or item/safe/shrine popup has finished
        // so Ryu's live coordinates and the new room/inventory state are completely settled.
        if (IsSafeToSaveNow()) {
            if (InterlockedCompareExchange(&g_PendingSave, 0, 1) == 1) {
                DoAutosave();
            }
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
        // Must NOT be in chapter transition
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
        // Must be in active Story mode
        cmp byte ptr ds:[0x00DB5A60], 5
        jne SkipItemSave
        // Must NOT be in chapter transition
        cmp byte ptr ds:[0x0058A389], 0
        jne SkipItemSave
        // Ryu must be spawned and active
        cmp byte ptr ds:[0x0058A594], 1
        jne SkipItemSave
        // Ryu must NOT be locked in cutscene / event
        cmp byte ptr ds:[0x004B75DE], 0
        jne SkipItemSave
        // Ryu action ID must be normal gameplay (< 0x20)
        cmp byte ptr ds:[0x004B7640], 0x20
        jae SkipItemSave
        // Cutscene must not be playing
        cmp word ptr ds:[0x00DB9C6E], 0xFFFF
        jne SkipItemSave
        // Room transition must not be active
        cmp byte ptr ds:[0x00D6A11E], 0
        jne SkipItemSave
        // Pause menu must not be open
        cmp byte ptr ds:[0x00DB5A68], 0
        jne SkipItemSave
        // State trigger must not be set
        cmp byte ptr ds:[0x00DB9AD6], 0
        jne SkipItemSave
        // Task 1 must be active gameplay (1)
        cmp byte ptr ds:[0x007F1B12], 1
        jne SkipItemSave
        // Stage substate must be active room (3)
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

// 3. Dragon Statue / Chapter Clear save hook at 0x001DA15F (5 bytes replaced)
// Original: E8 DC 56 13 00 (call 0x0030F840)
// Args to 0x0030F840: edx = esi = pathOut, [esp] = name, [esp+4] = save image, [esp+8] = size
extern "C" void __cdecl Hook_ShrineSave_Callback(int res, const char* pathOut) {
    if (res == 0 && pathOut && pathOut[0]) {
        strcpy_s(g_SlotPath, pathOut);
        g_AutosaveValid = TRUE;
        g_LastSavedChapter = *(BYTE*)ADDR_FIELD_CHAPTER;
        FILE* f = fopen(g_SlotFile, "w");
        if (f) { fprintf(f, "%s\n", g_SlotPath); fclose(f); }
        Log("[Autosave] [NativeSave] Saved to slot '%s' (Chapter %d, Room 0x%04X, ChapTrans %d)\n",
            g_SlotPath, *(BYTE*)ADDR_FIELD_CHAPTER, *(WORD*)ADDR_FIELD_SAVED_ROOM, *(BYTE*)ADDR_FIELD_CHAP_TRANS);
    }
    // Cancel any pending autosave so transition/next chapter starts completely clean
    InterlockedExchange(&g_PendingSave, 0);
    InterlockedIncrement(&g_HookCount[SRC_SHRINE]);
}

static void __declspec(naked) Hook_ShrineSave_Stub() {
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

// 5. Intercepts State 9 Case 3 checkpoint load at 0x0016656A (5 bytes replaced)
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
        // Set edi = 0, ebx = 0, and [esp + 0x18] = 2 ("Yes / Continue"), then jump to 0x002E0B87
        // which stops Game Over tasks/audio, reloads archive 0x647 at 0x002E0BB3, and returns al = 1 to 0x002DF641!
        xor edi, edi
        xor ebx, ebx
        mov dword ptr [esp + 0x18], 2
        push 0x002E0B87
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
    return BytesMatch(ADDR_HOOK_DOOR, door, 7) &&
           BytesMatch(ADDR_HOOK_ITEM, item, 6) &&
           BytesMatch(ADDR_HOOK_SHRINE, shrine, 1) &&
           BytesMatch(ADDR_COOKIE_CHECK, cookie, 6) &&
           BytesMatch(ADDR_HOOK_CASE3_LOAD, case3, 5) &&
           BytesMatch(ADDR_HOOK_GAMEOVER_TICK, gameOver, 5);
}

static BOOL IsMapped(DWORD addr) {
    MEMORY_BASIC_INFORMATION mbi;
    return VirtualQuery((void*)addr, &mbi, sizeof(mbi)) && mbi.State == MEM_COMMIT;
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

    // 3. Shrine save (0x001DA15F), 5-byte call replaced
    VirtualProtect((void*)ADDR_HOOK_SHRINE, 5, PAGE_EXECUTE_READWRITE, &oldProtect);
    BYTE jmpShrine[5] = { 0xE9, 0, 0, 0, 0 };
    DWORD relShrine = (DWORD)Hook_ShrineSave_Stub - (ADDR_HOOK_SHRINE + 5);
    memcpy(&jmpShrine[1], &relShrine, 4);
    memcpy((void*)ADDR_HOOK_SHRINE, jmpShrine, 5);
    VirtualProtect((void*)ADDR_HOOK_SHRINE, 5, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)ADDR_HOOK_SHRINE, 5);

    // 4. Cookie check (0x00379C29): executed constantly by other threads, so patch with one
    //    atomic 8-byte compare-exchange on the aligned block 0x379C28..0x379C2F.
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

    // 5. State 9 Case 3 checkpoint load (0x0016656A), 5 bytes replaced (5-byte call)
    VirtualProtect((void*)ADDR_HOOK_CASE3_LOAD, 8, PAGE_EXECUTE_READWRITE, &oldProtect);
    BYTE callCase3[5] = { 0xE8, 0, 0, 0, 0 };
    DWORD relCase3 = (DWORD)Hook_Case3_Load_Stub - (ADDR_HOOK_CASE3_LOAD + 5);
    memcpy(&callCase3[1], &relCase3, 4);
    memcpy((void*)ADDR_HOOK_CASE3_LOAD, callCase3, 5);
    VirtualProtect((void*)ADDR_HOOK_CASE3_LOAD, 8, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)ADDR_HOOK_CASE3_LOAD, 8);

    // 6. Game Over loop tick (0x002E08EA), 5 bytes replaced
    VirtualProtect((void*)ADDR_HOOK_GAMEOVER_TICK, 8, PAGE_EXECUTE_READWRITE, &oldProtect);
    BYTE jmpGameOver[5] = { 0xE9, 0, 0, 0, 0 };
    DWORD relGameOver = (DWORD)Hook_GameOver_Tick_Stub - (ADDR_HOOK_GAMEOVER_TICK + 5);
    memcpy(&jmpGameOver[1], &relGameOver, 4);
    memcpy((void*)ADDR_HOOK_GAMEOVER_TICK, jmpGameOver, 5);
    VirtualProtect((void*)ADDR_HOOK_GAMEOVER_TICK, 8, oldProtect, &oldProtect);
    FlushInstructionCache(GetCurrentProcess(), (void*)ADDR_HOOK_GAMEOVER_TICK, 8);

    Log("[Autosave] [Verify] door=%02X item=%02X shrine=%02X pump=%02X case3=%02X gameOver=%02X | PID=%u\n",
        *(BYTE*)ADDR_HOOK_DOOR, *(BYTE*)ADDR_HOOK_ITEM, *(BYTE*)ADDR_HOOK_SHRINE,
        *(BYTE*)ADDR_COOKIE_CHECK, *(BYTE*)ADDR_HOOK_CASE3_LOAD, *(BYTE*)ADDR_HOOK_GAMEOVER_TICK,
        GetCurrentProcessId());
    Log("[Autosave] All hooks successfully installed!\n");
}

// Fallback when no auto-save hook has fired yet: sample which thread runs the pump hook the most.
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
static void PollControllerCombos(BOOL* outLoadCombo, BOOL* outSaveCombo) {
    *outLoadCombo = FALSE;
    *outSaveCombo = FALSE;

    // 1. Read internal Xbox controller button state in default.xbe (0x00D219A0, stride 0x78)
    __try {
        for (int port = 0; port < 4; port++) {
            DWORD btns = *(volatile DWORD*)(ADDR_PAD_BASE + port * PAD_STRIDE);
            if (btns == 0) continue;
            // Quick Load: Back + RB (0x0020 | 0x1000) or L3 + R3 (0x0040 | 0x0080)
            if ((btns & (XBE_BTN_BACK | XBE_BTN_BLACK_RB)) == (XBE_BTN_BACK | XBE_BTN_BLACK_RB) ||
                (btns & (XBE_BTN_LTHUMB | XBE_BTN_RTHUMB)) == (XBE_BTN_LTHUMB | XBE_BTN_RTHUMB)) {
                *outLoadCombo = TRUE;
            }
            // Quick Save: Back + LB (0x0020 | 0x2000)
            if ((btns & (XBE_BTN_BACK | XBE_BTN_WHITE_LB)) == (XBE_BTN_BACK | XBE_BTN_WHITE_LB)) {
                *outSaveCombo = TRUE;
            }
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {
    }

    // 2. Also poll XInput directly as a fallback
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
    if (g_pfnXInputGetState) {
        for (DWORD i = 0; i < 4; i++) {
            XINPUT_STATE_MINI st;
            if (g_pfnXInputGetState(i, &st) == 0) {
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
}

// Background thread: waits for the XBE, installs hooks, polls hotkeys & Xbox controller combos
DWORD WINAPI MainWorkerThread(LPVOID lpParam) {
    InitPaths();
    Log("[Autosave] Waiting for XBE mapping at 0x00010000...\n");

    for (;;) {
        if (IsMapped(0x00010000) && IsMapped(ADDR_HOOK_DOOR) && IsMapped(ADDR_HOOK_ITEM) &&
            IsMapped(ADDR_HOOK_SHRINE) && IsMapped(0x00379C28) &&
            IsMapped(ADDR_HOOK_CASE3_LOAD) && IsMapped(ADDR_HOOK_GAMEOVER_TICK) &&
            HookSitesReady()) break;
        Sleep(100);
    }

    Log("[Autosave] XBE detected! Installing hooks in 1 second...\n");
    Sleep(1000);
    if (!HookSitesReady()) {
        Log("[Autosave] Hook sites changed unexpectedly; hooks NOT installed.\n");
        return 0;
    }
    InstallHooks();

    BOOL wasSaveDown = FALSE;
    BOOL wasLoadDown = FALSE;

    for (;;) {
        Sleep(16); // ~60 Hz tick

        if (!IsOurProcessForeground()) {
            wasSaveDown = FALSE;
            wasLoadDown = FALSE;
            continue;
        }

        BOOL padLoad = FALSE, padSave = FALSE;
        PollControllerCombos(&padLoad, &padSave);

        BOOL isSave = ((GetAsyncKeyState(VK_F5) & 0x8000) != 0) || padSave;
        if (isSave && !wasSaveDown) {
            Log("[Autosave] [%s] Manual save requested (game thread id %u)\n",
                padSave ? "Pad:Back+LB" : "F5", g_GameTid);
            LogHookStats();
            if (DetectGameThread()) {
                InterlockedExchange(&g_PendingSave, 1);
            } else {
                Log("[Autosave] Manual save ignored: game thread unknown\n");
            }
        }
        wasSaveDown = isSave;

        BOOL isLoad = ((GetAsyncKeyState(VK_F9) & 0x8000) != 0) || padLoad;
        if (isLoad && !wasLoadDown) {
            Log("[Autosave] [%s] Quickload requested (GameOver state: %d, SubState: 0x%02X)\n",
                padLoad ? "Pad:Back+RB/LS+RS" : "F9",
                *(BYTE*)ADDR_FIELD_STATE_MODE, *(BYTE*)ADDR_STAGE_SUBSTATE);
            LogHookStats();
            if (DetectGameThread()) {
                InterlockedExchange(&g_PendingLoad, 1);
            } else {
                Log("[Autosave] Quickload ignored: game thread unknown\n");
            }
        }
        wasLoadDown = isLoad;
    }
    return 0;
}

// D3D9 Proxy Implementations
void LoadRealD3D9() {
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

extern "C" void* WINAPI Proxy_Direct3DCreate9(UINT SDKVersion) {
    LoadRealD3D9();
    if (g_pfnDirect3DCreate9) {
        return g_pfnDirect3DCreate9(SDKVersion);
    }
    return NULL;
}

extern "C" HRESULT WINAPI Proxy_Direct3DCreate9Ex(UINT SDKVersion, void** ppD3D) {
    LoadRealD3D9();
    if (g_pfnDirect3DCreate9Ex) {
        return g_pfnDirect3DCreate9Ex(SDKVersion, ppD3D);
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
