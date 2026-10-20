> record copy of redregg/work/DELETE-HOST-20261016.md, 2026-10-16; the lane logs stay in redregg

# DELETE-HOST — Host layer deletion dossier (SHORT; cut off by re-tasking to BUILD-HOST)

DISCOVER-HOST, 2026-10-16. Tree: detached main 2c27b08b. Tags: READ = path:line read; DERIVED = computed
by a script over the tree (scripts in the session scratchpad: defs.py, reach.py); ASSUMED = inference.
Stopped partway through when ROOT moved this lane to BUILD-HOST (nanodregg). Sections 3 (consent),
4 (hosting) and 5 (pipeline) were NOT measured beyond the ARCHITECTURE-20261016 figures.

## 1. Host/Main.lean reach (DERIVED; name-match call graph inside the file, comments stripped)

9,163 lines = 222 header/imports (122 imports) + 269 top-level decls (232 def, 26 structure, 10 instance, 1 theorem).

| class | decls | lines |
|---|---|---|
| `run` itself (CLI match + the inline stdio closure) | 1 | 2,856 (6288-9143) |
|   of which the `stdio` arm = inline `fnDispatch` closure | — | 1,147 (6650-7796), 126 opcode arms |
|   of which CLI verb arms | 126 verbs | ~1,700 |
| reached from the session (`stdio`/`codec`) only | 89 | 2,808 |
| reached from session AND from CLI | 136 | 2,233 |
| reached from CLI only | 29 | 862 (biggest: storeBench 230, selectedReleaseFnAck 110, selectedEmptyFnAck 99, selectedReleaseFnLegacyPoll 84, selectedReleaseFnPoll 57) |
| reached from nothing | 2 | `sessionExactConfirmed` :1302 (13, dead: 0 refs in the tree), theorem `fnOwnRCarrierMatches_exact_tail` :3002 (7, 0 refs) |
| instances | 10 | 136 |

## 2. Dispatchers (READ)

Five routing tables + two framing loops for one opcode space:
`serveSession` :2655 (36, framing) → `serveFrame` :2613 (42; streamed ops 26/34/46/76/152/154/164) →
`dispatchSession` :2047 (123; 25 ops; 5 arms only forward to `fnDispatch`) → `fnDispatch` closure inside `run`
:6650-7796 (152 of 184 ops per `protocol/host-operations.json` `receiver`) → `objectKernelOperation` :5961 (73;
210-219) and `launchLifecycleOperatorOp` :6137 (120; 66-71). `serveCodec` :2691 (27) re-implements
`serveSession`'s framing for `pureCodec` :1997 (50; ops 7-11).
Inside `fnDispatch`: 47 hand-written `unless … ≤ maxHostFrameBytes` checks, 37 `splitPair payload`, 9
`decodeSignatures`; 183 `session{Current,Opened,Walked,Confirmed}` calls in the file.
One dispatch over the table deletes: `serveFrame`'s special cases (handler type `payload → Reply` with a streamed
variant), `dispatchSession`'s forwarders, the closure-in-`run` (state becomes the resident's), `serveCodec`
(a storeless resident = the same loop whose Store ops refuse), and the per-arm bound checks (one bound per op
in the table). ASSUMED: ~1,400 of the ~1,650 dispatch lines are this boilerplate.

## 3. CLI verbs (DERIVED: 126 verbs; external callers = grep of native/ scripts/ deploy/ tools/)

| class | verbs | lines | zero external callers |
|---|---|---|---|
| one-shot twin of a session opcode (H4) | 49 | 398 | 22 (all application-lifecycle-*, share-issue submit/lookup/assemble, enroll-key-{plan,submit,lookup}, reserve-birth-*, fn-{selected,empty}-poll-*, fn-frontier-assemble, pay-claim-status) |
| author/inspect kinds (twins of ops 7/8) | 14 | 176 | 0 |
| fn consumer file tooling (`mini host-command` passthrough, `main.rs:2541-2557`: "require direct Host/Main CLI until a typed session opcode exists") | 22 | 746 | 1 |
| authoring/evidence with no session op | 22 | 195 | 1 (`grain-origin-prepare`) |
| operator store life (genesis, bootstrap, audit, store-audit, …) | 10 | 111 | 3 (`store-bench`, `checkpoint-differential`, `diagnose-completion`) |
| ledger/pay tooling | 9 | 66 | 0 |

Each one-shot twin does a full cold open (`NativeHostSession.start` / `NativeHost.openExisting`) for one op.
The Rust client already maps 19 verbs to opcodes when a socket exists (`native/resource-client/src/main.rs:1311-1340`)
and falls back to exec'ing the Host CLI (`local_process` :1245) otherwise: the CLI twins exist for that fallback.

## 4. The opening chain (READ)

`NativeHostSession.Session` (Kernel/NativeHostSession.lean:38) holds THREE verified views of one Store plus a cache:
`opened : Opened` (full: durable `Loaded`, directory, authority, pins, lawful proof; NativeHostContext.lean:439),
`light : NativeHostLight.Light` (checkpoint+suffix `DurableServed.Opening` + `OpenedServed`; used by
renounce/revoke/delegate/install/invoke, NativeHost.lean:3057-3097), `walked : Option Walked` (genesis re-admission
`NativeHostReplay.Verified`, lazily, for lifecycle/dispatch/enrollment/frontier), `openingCache`. Plus a FOURTH,
`CarriedNativeHostSession.Walked`, when a carry registry is configured. `refresh` re-reads and re-validates
both openings after every request (:176-197). Theorems that bind the chain and die with it:
`Session.rememberReadback_{opened,image,stale,newer,openingCache}`, `Session.retainWalked_image`,
`validateLoadedFrom_eq`, `validateServedFrom_eq`, `validateServed_ofLoaded`, `Light.basisVia_restorage`,
`cellsLawful_eq_cached`. Under one Resident with `Represents` = equality none of these is needed.

## 5. Numbers NOW (ratchet seed)

Host/Main.lean 9,163 · CLI verbs 126 · routing tables 5 + framing loops 2 · openings per session 3 (+1 carried) ·
NativeHost* 11,077 lines (NativeHost 3,351, Replay 4,590, Genesis 1,212, Context 778) · consent 2,368 lines over
12 frames, the provider = a second full verifier (`ClientConsentCore.lean:250-297` runs `NativeHostReplay.verifyLoaded`
/ `extendFrom`, i.e. the same code, not a twin) · scripts/pipeline 54 files, scripts/gates 11, scripts/*.sh 42 ·
deploy/ 262 tracked files.

## Three biggest deletions

1. The inline `fnDispatch` + four other routing tables + `serveCodec` → one table-driven dispatch (~1,400 lines).
2. The 63 CLI twins of session ops (574 lines) + the client `local_process` fallback; 22 of them have no caller at all.
3. The Opened/Light/Walked triple-opening and its refresh/revalidate machinery (Session, Light, Served, Context
   validation ≈ 2,400 lines + Compiler/DurableServed 1,081) → one Resident.
