> record copy of redregg/work/DELETE-KERNEL-20261016.md, 2026-10-16; the lane logs stay in redregg

# DELETE-KERNEL — 2026-10-16 (DISCOVER-KERNEL, truncated: ROOT reassigned me to BUILD-KERNEL in ~/dev/nanodregg)

Tree: main 2c27b08b (detached, read-only). Tags: READ = read at path:line; DERIVED = computed by script over `import`
lines (scratchpad dk/graph.py, clos.py, stats.py); ASSUMED = inference. Not finished: per-row reach for each of the 51
`NativeAdmission` ctors (DISCOVER-PROTOCOL's dispatch table is the authority) and per-def theorem-statement greps.

## 6. Numbers NOW (size-ratchet seed, DERIVED)
- Host.Main closure: 776 modules, 320,587 lines (Kernel 405, Compiler 158, Theory 107, Host 87, Selvage 12, Pred 7) = host-closure.pin.
- Theorem/lemma decls: 14,507 in Kernel+Compiler+Host+Theory; 10,139 inside the Host closure.
- Kernel: 558 modules / 204,945 lines; 145 modules (44,568 lines) are in NO exe closure (Host.Main, totality, follower,
  both consent exes, carry-verifier); 57 of them (12,132 lines) have no importer but umbrellas.
- Versioned/legacy names (V\d|Legacy|Historical in Kernel/Host/Compiler): 70 modules, 12,810 lines, 263 theorems.
- `NativeAdmission` ctors: 51 (`Kernel/NativeHostReplay.lean:977-1198`, READ); file is 4,590 lines.
- `partial def`: Kernel 1, Compiler 31, Host 23 (55; +2 Verify, +5 scripts). `#guard`: Kernel 17, Compiler 16, Host 4.
  `native_decide` lines: Kernel 21, Compiler 112, Theory 67.
- `List UInt8` lines vs `ByteArray` lines in the Host closure: 4,269 vs 284. Compiler/Durable*: 312 vs 24.

## Biggest deletions found (in order of size × safety)
1. **The two-state-machine twin (K1/K2/K3)** — `DataSnapshot`/`DataIntent.execute`/`IntentRecord.writes`+`canonicalPostBytes`/
   `ReplayEnvelope` vs `World.admit`. Reach (DERIVED grep, lines): `DataIntent` 286 files/1,345 lines, `DataSnapshot` 85/713,
   `canonicalPostBytes` 85/227, `IntentRecord` 96/547, `image.accepted` 96/515, `ReplayEnvelope` 28/93. `World.admit` is
   called from 5 files only. Fold: the World is the state, the Turn is the log entry, `Represents` disappears (equality),
   `host_submit_is_step` becomes the definition of submit. The bridge modules (TurnOfIntent 1,667, HostRefinesWorldCore
   1,312, HostRefinesWorld 126, DeployedTurnCompact 364, DeployedTurnCodec 197, DurableDataIntent 727, DurableReceiver 387,
   DurableCheckpoint 358, DurableCommitProtocol 945) ≈ 6,100 lines collapse to World + a Turn codec + a log.
2. **Replay-only lifecycle versions** (READ `Host/Main.lean:1369-1376, 1489-1494, 2547-2557`): fresh submits accept only
   Begin V3|V4, Claim V3|V4, Completion V2|V4. Begin v1/V2, Claim v1/V2, Completion v1 are reachable ONLY by replaying
   old Stores (`NativeHostReplay.derive`) and by lookups — on a re-genesised Store they are dead. Deleting them removes
   ≥5 NativeAdmission ctors, `ApplicationLifecycle{Begin,Claim}V2*`, `ApplicationLifecycleV2Lookup` legacy arms,
   `Host/ApplicationLifecycle{Begin,Claim}Operator` (Deployed-only). Old stores refuse by StoreEpoch. Beyond that the whole
   SPK lifecycle V3/V4 family (≈45 modules) is a fold onto OB rebirth (SINS T4–T6), not a pure deletion (m6grain/hermes rows).
3. **Parallel turn carriers + vestigial** (K13): `Kernel/Turn.lean` Hyperedge (120), `TypedCellHyperedge` (503),
   `MultiCellHyperedge` (718), `DurableCommitProtocol` carrier (945) — all in the Host closure, 520 lines mention Hyperedge
   in 64 files; `Kernel/State.lean` (257), `Effects/` (436), `Pred/CoordinationDial` (569) in NO exe closure. Plus the 145
   no-exe Kernel modules (44.6k lines) — each needs its theorem statements checked before deletion.

Also: light-opening twin K11 (NativeHostLight 100, NativeHostServed 257, DurableServed 1,081) → one resident World;
Legacy carries (Compiler/LegacyContentCarry 606, LegacyStoreCarry 268, LegacyStoreCarryChecks 48 orphan, Host Legacy views 160);
`Compiler/MinidreggV1*` (929 lines; V1Artifact keeps Selvage in the Host closure via BinaryTower256Profile).

## Sim reach (READ, gh/lane/turn-log `Host/WorldSim.lean`, 519 lines)
The HP-6 sim generates raw `DataIntent`s / probe `DTurn`s (Kernel/TurnGen.lean) and drives `DurableReceiverIO.load` +
the append path against the follower; it exercises NO receiver. It covers exactly the kernel layer: World.admit, the
durable engine, TurnLog, WorldSystemCodec, crash-restart. THE BAR (scripts/perf/workload.py --births-only) exercises
genesis, `workspace create` (birth), activity `create` (op 212), cadence certify (op 172), reopen.

## turn-log lane (gh/lane/turn-log dbb4f0f4 vs main): 83 files +3485/−1095; adds CellTable (now on main), DeployedCharge,
DeployedRepresentsCheck, SnapRepresents, TurnGen, WorldSim; deletes no file; deletes `Turn.absent`/`absentCheck`/
`admit_ok_absent`/`absent_present_refused` (a0), guard legs + `absentOf` (guards), 377 lines of HostRefinesWorldCore.

The rest of this dossier is superseded by the nanodregg rebuild: the one-state-machine factoring (§4) is what I now build.
