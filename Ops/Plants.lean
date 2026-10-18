/-
# Ops.Plants — backup and restore, planted against the real `host` (ASSEMBLY-ops D6/D7)

A backup is the Store's three files copied in the order `key`, `base.world`, `seg.log`; a restore
is the copy put back and judged by `host check STORE --anchor STEPS:CHAIN`. Each plant below
builds a Store through the real `host genesis`/`host serve` (one record per serve run), copies or
damages it, and asserts the exit code `host check` gives against `Host.Status.code` — the table,
never a literal. The anchor is computed here, independently, by `Receive.submit` of the same
calls on the same genesis World, so the intact plant also checks that the Store's chain IS the
kernel's fold.

The mutation is asserted before the verdict is read (a damaged copy must differ from its source:
"a falsifier that stopped falsifying"). The undecidable cases are rows too: a cut at a frame
boundary, a single foreign last frame and a rollback to an older complete copy all open cleanly
WITHOUT an anchor, and are refused by name WITH one.

The live plants (`live`) run ONE long `host serve` fed calls whose state fills one slot, so the
Store seals real bases (`sealMinBytes` = 1 MiB) while it runs, and interleave the backup with it
deterministically: `key` and `base.world` are copied, the writer is fed until it seals a NEWER
base (polled through `host check`, read-only, with a deadline), and only then is `seg.log` copied.
That is the D7 race at its worst point: the copied base is no longer the Store's base, and the
copy must still open to the height the writer had reached. The finished Store is then the sealed
Store the first plants never had: a history flip before a real base, a segment cut below the base
offset (`segmentShort`), and the WRONG copy order (`seg.log` before a seal, `base.world` after).
Each live plant first asserts that its precondition happened (a seal during the copy, a base past
the origin), or it FAILS instead of passing on a Store that never sealed.

    store-plants HOST_EXE DIR     DIR must not exist; one line per plant, then ALL PASS (exit 0)
-/
import Ops.Founder
import Host.Exit
import Host.Carry
import Host.Check

namespace Nanodregg.Ops.Plants

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Host.Deployed

def name : String := "plants"

structure Run where
  code : UInt32
  out : String

def host (exe : String) (args : List String) (stdin : ByteArray := ByteArray.empty) : IO Run := do
  let child ← IO.Process.spawn
    { cmd := exe, args := args.toArray, stdin := .piped, stdout := .piped, stderr := .piped }
  let (input, child) ← child.takeStdin
  input.write stdin
  input.flush
  let out ← IO.asTask child.stdout.readBinToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  let out ← IO.ofExcept out.get
  -- `serve` answers in binary frames; only text output (check's STATUS line) is shown
  let text := (String.fromUTF8? out).getD s!"<{out.size} bytes>"
  return ⟨code, (text ++ err).trimAsciiEnd.toString⟩

/-- `host` with its stdout kept as bytes (a `serve` reply), and its stderr as text. -/
def hostRaw (exe : String) (args : List String) (stdin : ByteArray) : IO (UInt32 × ByteArray × String) := do
  let child ← IO.Process.spawn
    { cmd := exe, args := args.toArray, stdin := .piped, stdout := .piped, stderr := .piped }
  let (input, child) ← child.takeStdin
  input.write stdin
  input.flush
  let out ← IO.asTask child.stdout.readBinToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  return (code, ← IO.ofExcept out.get, err)

def files : List String := Host.Store.backupOrder

/-- The backup: the Store's files, in `Host.Store.backupOrder`. -/
def backup (src dst : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  for f in files do IO.FS.writeBinFile (dst / f) (← IO.FS.readBinFile (src / f))

/-- The World the Store should open to, and the calls that make it; every call must admit in
process, or the plants refuse to run. -/
def expected (n : Nat) : Except String (List (Call D) × World D) := do
  let w₀ ← (Founder.world name).mapError fun r => s!"genesis refused {r.name}"
  (List.range n).foldlM (fun (cs, w) i =>
    let c := Founder.create w i
    match submit X w c with
    | .ok (_, w') => .ok (cs ++ [c], w')
    | .error _ => .error s!"call {i} does not admit") ([], w₀)

def anchorArg (w : World D) : String := s!"{w.steps}:{w.chain.toHex}"

structure Plant where
  label : String
  /-- the expected status: `eof` means exit 0 -/
  want : Status
  run : IO Run

def judge (p : Plant) : IO Bool := do
  let r ← p.run
  let ok := r.code = p.want.code.toUInt32
  IO.println s!"PLANT {p.label} {if ok then "PASS" else "FAIL"} exit={r.code} want={p.want.name}({p.want.code}) :: {r.out.replace "\n" " "}"
  return ok

/-- Write `bytes` over `dir/seg.log`, refusing a mutation that changed nothing. -/
def damage (dir : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let old ← IO.FS.readBinFile (dir / "seg.log")
  if old == bytes then throw (IO.userError s!"mutation of {dir} is a no-op")
  IO.FS.writeBinFile (dir / "seg.log") bytes

/-- The `i`-th sealed-plant call's one slot (the first state key, `Receive.stateBase`): `slotBytes` deterministic bytes. -/
def slotBytes : Nat := 49152

def bigState (i : Nat) : Slots :=
  [(stateBase, ByteArray.mk ((Array.range slotBytes).map fun j => ((i + j) % 251).toUInt8))]

/-- `host check DIR`'s STATUS fields, or none if it refused. -/
def status (exe : String) (d : System.FilePath) : IO (Option (List (String × String))) := do
  let r ← host exe ["check", d.toString]
  if r.code ≠ 0 then return none
  let some line := (r.out.splitOn "\n").find? (·.startsWith "STATUS ") | return none
  return some ((line.splitOn " ").filterMap fun kv =>
    match kv.splitOn "=" with | [k, v] => some (k, v) | _ => none)

def field (st : List (String × String)) (k : String) : Nat :=
  ((st.lookup k).bind String.toNat?).getD 0

def pollMs : UInt32 := 100
/-- The longest wait for the live writer to reach a height or a seal: 60 s in `pollMs` steps. -/
def pollSteps : Nat := 600

/-- Poll `host check` until `ok` holds of its STATUS fields; none at the deadline. A refusing
check (the writer mid-seal) is polled again. -/
def awaitStatus (exe : String) (d : System.FilePath) (ok : List (String × String) → Bool) :
    IO (Option (List (String × String))) := do
  for _ in [0:pollSteps] do
    if let some st ← status exe d then
      if ok st then return some st
    IO.sleep pollMs
  return none

/-- The live and sealed plants; the number that failed. -/
def live (exe : String) (dir : System.FilePath) : IO Nat := do
  let l := dir / "L"
  let g ← host exe (["genesis", l.toString, name] ++ Founder.genesisArgs)
  unless g.code = 0 do IO.eprintln s!"genesis L: {g.out}"; return 1
  let originSeg ← IO.FS.readBinFile (l / "seg.log")
  -- the calls and their folds, in process; enough bytes for two seals
  let n := 48
  -- anchors[h] is the kernel's own `STEPS:CHAIN` after the first h calls (each admitted: one step)
  let w0 ← match Founder.world name with
    | .ok w => pure w
    | .error r => do IO.eprintln s!"genesis refused {r.name}"; return 1
  let (frames, anchors, _) ← (List.range n).foldlM (init := (#[], #[anchorArg w0], w0))
    fun (cs, as, w) i => do
      let c := Founder.create w i (bigState i)
      match submit X w c with
      | .ok (_, w') => pure (cs.push (Founder.submitFrame c), as.push (anchorArg w'), w')
      | .error v =>
        let why := match v with | .refused r => r.name | .rejected r => r.name
        throw (IO.userError s!"live call {i} does not admit in process: {why}")
  let child ← IO.Process.spawn
    { cmd := exe, args := #["serve", l.toString], stdin := .piped, stdout := .piped, stderr := .piped }
  let (input, child) ← child.takeStdin
  -- the live writer's pipes are drained for its whole run: dedicated threads, or they hold the
  -- task pool and every later `host check`'s own reader task never runs
  let out ← IO.asTask child.stdout.readBinToEnd (prio := .dedicated)
  let err ← IO.asTask child.stderr.readToEnd (prio := .dedicated)
  let feed (lo hi : Nat) : IO Unit := do
    for i in [lo:hi] do input.write frames[i]!
    input.flush
  let mut failed := 0
  let say (label : String) (ok : Bool) (detail : String) : IO Unit :=
    IO.println s!"PLANT {label} {if ok then "PASS" else "FAIL"} :: {detail}"
  -- 1. four calls, durable
  feed 0 4
  let some st0 ← awaitStatus exe l (field · "height" ≥ 4) | IO.eprintln "live writer never reached height 4"; return 1
  let copy := dir / "livecopy"
  IO.FS.createDirAll copy
  IO.FS.writeBinFile (copy / "key") (← IO.FS.readBinFile (l / "key"))
  let baseCopied ← IO.FS.readBinFile (l / "base.world")
  IO.FS.writeBinFile (copy / "base.world") baseCopied
  let wrongOrderSeg ← IO.FS.readBinFile (l / "seg.log")
  -- read after the base copy: the copied base names an index prefix no longer than this
  let indexAtBase ← IO.FS.readBinFile (l / "index.log")
  -- 2. feed until the writer seals a newer base, then copy the segment
  let mut sealed := none
  let mut fed := 4
  while sealed.isNone && fed < n do
    feed fed (fed + 4)
    fed := fed + 4
    sealed ← awaitStatus exe l fun st => field st "height" ≥ fed
    if let some st := sealed then
      if field st "base_steps" ≤ field st0 "base_steps" then sealed := none
  -- the append-only files after the base, in `Host.Store.backupOrder` (HOST-30: index.log first)
  let indexCopied ← IO.FS.readBinFile (l / "index.log")
  IO.FS.writeBinFile (copy / "index.log") indexCopied
  let segCopied ← IO.FS.readBinFile (l / "seg.log")
  IO.FS.writeBinFile (copy / "seg.log") segCopied
  let raced := sealed.isSome && (← IO.FS.readBinFile (l / "base.world")) != baseCopied
  say "live-copy-raced-a-seal" raced
    s!"base_steps {field st0 "base_steps"} at the base copy, {(sealed.map (field · "base_steps")).getD 0} at the segment copy; the copied base is {if raced then "no longer" else "STILL"} the Store's"
  unless raced do failed := failed + 1
  -- 3. the rest, then the writer ends at eof
  feed fed n
  -- the stdin handle is dead after the last feed, so the writer sees eof; bounded wait
  let waited ← IO.asTask child.wait (prio := .dedicated)
  let mut steps := 0
  while !(← IO.hasFinished waited) && steps < pollSteps do
    IO.sleep pollMs
    steps := steps + 1
  unless ← IO.hasFinished waited do
    child.kill
    IO.eprintln "live serve did not end at eof within the deadline; killed (its own Child handle)"
    return failed + 1
  let code ← IO.ofExcept waited.get
  let _ ← IO.ofExcept out.get
  let errText ← IO.ofExcept err.get
  unless code = 0 do IO.eprintln s!"live serve exit {code}: {errText}"; return failed + 1
  let hCopy := (sealed.map (field · "steps")).getD 0
  let anchorAt (h : Nat) : List String := ["--anchor", anchors[h]!]
  let check (d : System.FilePath) (extra : List String := []) : IO Run :=
    host exe (["check", d.toString] ++ extra)
  let plain (label : String) (want : Status) (r : IO Run) : IO Nat := do
    return if ← judge ⟨label, want, r⟩ then 0 else 1
  failed := failed + (← plain "live-copy-anchor-at-segment-copy" .eof (check copy (anchorAt hCopy)))
  -- (a) the live copy holds a stale base and an index.log copied after a newer seal: the entries
  -- past the ones the base counts are orphans, which a reader ignores and the writer's open truncates
  let orphan := indexCopied.size > indexAtBase.size
  say "orphan-index-entries-present" orphan
    s!"index.log {indexAtBase.size} bytes at the base copy, {indexCopied.size} copied after the seal"
  unless orphan do failed := failed + 1
  let ow := dir / "orphan-writer"
  backup copy ow
  let r ← host exe ["serve", ow.toString]
  let after := (← IO.FS.readBinFile (ow / "index.log")).size
  let truncated := r.code = 0 && after ≤ indexAtBase.size
  say "orphan-index-entries-writer-truncates" truncated
    s!"serve exit={r.code}; index.log {indexCopied.size} -> {after} bytes (the base names at most {indexAtBase.size})"
  unless truncated do failed := failed + 1
  failed := failed + (← plain "orphan-index-entries-writer-reopens-at-height" .eof (check ow (anchorAt hCopy)))
  -- the sealed Store: it must have a base past the origin, or the rows below test nothing
  let some stS ← status exe l | IO.eprintln "the finished live Store does not check"; return failed + 1
  let off := field stS "base_offset"
  let hasBase := field stS "base_steps" > 0 && off > originSeg.size
  say "sealed-store-has-a-real-base" hasBase s!"base_steps={field stS "base_steps"} base_offset={off} origin={originSeg.size} seg_bytes={field stS "seg_bytes"}"
  unless hasBase do return failed + 1
  failed := failed + (← plain "sealed-intact-anchor" .eof (check l (anchorAt n)))
  let seg ← IO.FS.readBinFile (l / "seg.log")
  let sealedCopy (label : String) (f : System.FilePath → IO Unit) : IO System.FilePath := do
    let d := dir / label
    backup l d
    f d
    return d
  let short ← sealedCopy "sealed-short" fun d => damage d (seg.extract 0 (off - 1))
  failed := failed + (← plain "sealed-segment-cut-below-base" .segmentShort (check short))
  let at_ := originSeg.size + (off - originSeg.size) / 2
  let flipped ← sealedCopy "sealed-flip" fun d => damage d (seg.set! at_ (seg.get! at_ ^^^ 1))
  failed := failed + (← plain "sealed-flip-history-before-base" .corrupt (check flipped))
  -- the wrong order: seg.log copied before a seal, base.world after it
  let wrong ← sealedCopy "wrong-order" fun d => damage d wrongOrderSeg
  -- (b) index.log copied BEFORE base.world, across seals: the newer base counts entries the copy lacks.
  -- It must refuse `indexShort` by name or open to the writer's height; never open short.
  let finalIndex ← IO.FS.readBinFile (l / "index.log")
  let wrongIdx ← sealedCopy "wrong-order-index" fun d => IO.FS.writeBinFile (d / "index.log") indexAtBase
  let older := indexAtBase.size < finalIndex.size
  let ri ← check wrongIdx (anchorAt n)
  let okIdx := older && (ri.code = Status.indexShort.code.toUInt32 || ri.code = 0)
  say "copy-index-before-base-wrong-order" okIdx
    s!"index.log {indexAtBase.size} of {finalIndex.size} bytes; exit={ri.code} ({if ri.code = 0 then "opened at the anchor" else if ri.code = Status.indexShort.code.toUInt32 then "refused indexShort" else "NEITHER"}) :: {ri.out.replace "\n" " "}"
  unless okIdx do failed := failed + 1
  failed := failed + (← plain "copy-segment-before-base-wrong-order" .segmentShort (check wrong))
  return failed

/-- OPS-2's replay, against the real exe after KERNEL-24: founder 0's first call, signed for the
test World, is served to a second genesis under the same label and founders. Under another nonce
it must not land (height stays 0; the writer answers `wrongWorld`); under the SAME nonce, the
restore case by design, it lands (height 1). The control row keeps the first from passing on a
writer that admits nothing. -/
def replay (exe : String) (dir : System.FilePath) : IO Nat := do
  let w₀ ← match Founder.world name with
    | .ok w => pure w
    | .error r => do IO.eprintln s!"genesis refused {r.name}"; return 1
  let c := Founder.create w₀ 0
  let other := Founder.nonce.set! 0 (Founder.nonce.get! 0 ^^^ 1)
  if other == Founder.nonce then IO.eprintln "the other nonce is the test nonce"; return 1
  let otherArgs := ["--nonce", Protocol.Text.toHex other] ++ Founder.genesisArgs.drop 2
  let mut failed := 0
  for (label, args, want) in [("replay-other-nonce-not-admitted", otherArgs, 0),
                              ("replay-same-nonce-admitted-control", Founder.genesisArgs, 1)] do
    let d := dir / label
    let g ← host exe (["genesis", d.toString, name] ++ args)
    unless g.code = 0 do IO.eprintln s!"genesis {label}: {g.out}"; return failed + 1
    let r ← host exe ["serve", d.toString] (Founder.submitFrame c)
    let h := ((← status exe d).map (field · "height")).getD 1000
    let ok := r.code = 0 && h = want
    IO.println s!"PLANT {label} {if ok then "PASS" else "FAIL"} :: serve exit={r.code} height={h} want={want}"
    unless ok do failed := failed + 1
  return failed

/-- HOST-25's origin check through the real exe's own open (`serve`, not only `check`), on the
genesis-base Store `A` and the sealed Store `L`. A flip inside the origin RECORD (offset 4..35,
not its tag: under a genesis-only base the origin's tag is HOST-18's anchor) is `corrupt`. A
foreign origin is an origin frame that verifies under THIS Store's key but states another World's
genesis chain (the same founders and label, another nonce): it is built here with HOST's own
`Log.frame`, `Keys.ofKey` and `Deployed.originChain` from the copy's key file, as a Store whose
key file was shared would hold it. Over a sealed base it is `foreignOrigin`; over the genesis base
the anchor refuses first, `foreignSegment`. -/
def originPlants (exe : String) (dir : System.FilePath) : IO Nat := do
  let other := Founder.nonce.set! 0 (Founder.nonce.get! 0 ^^^ 1)
  let wOther ← match Receive.genesis X name.toUTF8 other allowanceMax [(Founder.key, nextKeyDigest X Founder.next)] with
    | .ok w => pure w
    | .error r => do IO.eprintln s!"the other genesis refused {r.name}"; return 1
  let mut failed := 0
  for (store, sealed) in [("A", false), ("L", true)] do
    let src := dir / store
    let seg ← IO.FS.readBinFile (src / "seg.log")
    let some key := Codec.Digest.ofBytes? (← IO.FS.readBinFile (src / "key"))
      | IO.eprintln s!"{store}: key file is not a digest"; return failed + 1
    let flipD := dir / s!"origin-flip-{store}"
    backup src flipD
    damage flipD (seg.set! 5 (seg.get! 5 ^^^ 1))
    let r ← host exe ["serve", flipD.toString]
    unless ← judge ⟨s!"origin-record-flip-serve-{store}", .corrupt, pure r⟩ do failed := failed + 1
    let frame := Log.frame (Keys.ofKey key shapes).segment segmentInitial (originChain wOther)
    let fD := dir / s!"foreign-origin-{store}"
    backup src fD
    if frame.size > seg.size then IO.eprintln "the foreign origin frame is longer than the segment"; return failed + 1
    damage fD (frame ++ seg.extract frame.size seg.size)
    let want : Status := if sealed then .foreignOrigin else .foreignSegment
    let r ← host exe ["serve", fD.toString]
    unless ← judge ⟨s!"foreign-origin-serve-{store}", want, pure r⟩ do failed := failed + 1
    unless ← judge ⟨s!"foreign-origin-check-{store}", want, host exe ["check", fD.toString]⟩ do
      failed := failed + 1
  return failed

/-- HOST-31's `indexMoved` (48, restart), live: a writer whose `index.log` grows under it (another
process appended a byte) must refuse its next seal by name, and the restart's open must truncate
the byte as an orphan and reopen at the durable height. The byte is appended after the
writer is serving and before its first seal; the writer is then fed until the seal is due. -/
def indexMovedPlant (exe : String) (dir : System.FilePath) : IO Nat := do
  let m := dir / "M"
  let g ← host exe (["genesis", m.toString, name] ++ Founder.genesisArgs)
  unless g.code = 0 do IO.eprintln s!"genesis M: {g.out}"; return 1
  let w0 ← match Founder.world name with
    | .ok w => pure w
    | .error r => do IO.eprintln s!"genesis refused {r.name}"; return 1
  let n := 24
  let (frames, _) ← (List.range n).foldlM (init := (#[], w0)) fun (fs, w) i => do
    let c := Founder.create w i (bigState i)
    match submit X w c with
    | .ok (_, w') => pure (fs.push (Founder.submitFrame c), w')
    | .error _ => throw (IO.userError s!"indexMoved call {i} does not admit in process")
  let child ← IO.Process.spawn
    { cmd := exe, args := #["serve", m.toString], stdin := .piped, stdout := .piped, stderr := .piped }
  let (input, child) ← child.takeStdin
  let out ← IO.asTask child.stdout.readBinToEnd (prio := .dedicated)
  let err ← IO.asTask child.stderr.readToEnd (prio := .dedicated)
  let waited ← IO.asTask child.wait (prio := .dedicated)
  -- two calls durable, no seal yet
  for i in [0:2] do input.write frames[i]!
  input.flush
  let some st ← awaitStatus exe m (field · "height" ≥ 2) | IO.eprintln "indexMoved writer never reached height 2"; return 1
  let idx0 := (← IO.FS.readBinFile (m / "index.log")).size
  if field st "base_steps" ≠ 0 then IO.eprintln "indexMoved: the writer sealed before the byte"; return 1
  let h ← IO.FS.Handle.mk (m / "index.log") .append
  h.write (ByteArray.mk #[0x5a])
  h.flush
  let idx1 := (← IO.FS.readBinFile (m / "index.log")).size
  -- feed until the seal is due; the writer may stop reading once it refuses
  try
    for i in [2:n] do input.write frames[i]!
    input.flush
  catch _ => pure ()
  let mut steps := 0
  while !(← IO.hasFinished waited) && steps < pollSteps do
    IO.sleep pollMs
    steps := steps + 1
  unless ← IO.hasFinished waited do
    child.kill
    IO.println s!"PLANT index-moved-under-writer FAIL :: the writer did not end within the deadline (killed by its own Child handle)"
    return 1
  let code ← IO.ofExcept waited.get
  let _ ← IO.ofExcept out.get
  let errText ← IO.ofExcept err.get
  let mut failed := 0
  let moved := idx1 = idx0 + 1 && code = Status.indexMoved.code.toUInt32
  IO.println s!"PLANT index-moved-under-writer {if moved then "PASS" else "FAIL"} :: index.log {idx0} -> {idx1} bytes under the writer; exit={code} want=indexMoved({Status.indexMoved.code}) :: {((errText.splitOn "\n").filter (·.startsWith "STATUS seal")).take 1}"
  unless moved do failed := failed + 1
  let durable := field ((← status exe m).getD []) "height"
  let r ← host exe ["serve", m.toString]
  let idx2 := (← IO.FS.readBinFile (m / "index.log")).size
  let some st2 ← status exe m | do IO.println "PLANT index-moved-restart-truncates FAIL :: check refuses after the restart"; return failed + 1
  let ok := r.code = 0 && idx2 = idx0 && field st2 "height" = durable && durable ≥ 2
  IO.println s!"PLANT index-moved-restart-truncates {if ok then "PASS" else "FAIL"} :: restart exit={r.code}; index.log {idx1} -> {idx2} bytes (want {idx0}); height {field st2 "height"} (durable {durable})"
  unless ok do failed := failed + 1
  return failed

/-- HOST-33's moved check, through the real exe on the sealed live Store `L`: a byte flipped in a
MIDDLE `index.log` entry (one the base counts, not the last, which open verifies) still OPENS;
the first `log` page that reads that entry is refused `badIndex` and the writer keeps serving
(exit 0 at eof); `host check` refuses `indexCorrupt` naming the entry. The entry flipped is the
one every page's binary search reads second (`Page.locate`: entry 0, then `total / 2` with total
= the base's count + the tail's records), so the page must read it whatever its start. The
control serves the same signed envelope to the intact copy and must be answered `ok`, so the
refusal is the entry's, not the envelope's. -/
def middleEntryPlant (exe : String) (dir : System.FilePath) : IO Nat := do
  let l := dir / "L"
  let w0 ← match Founder.world name with
    | .ok w => pure w
    | .error r => do IO.eprintln s!"genesis refused {r.name}"; return 1
  let some key := Codec.Digest.ofBytes? (← IO.FS.readBinFile (l / "key"))
    | IO.eprintln "L: key file is not a digest"; return 1
  let eb := entryBytes (Keys.ofKey key shapes)
  let idx ← IO.FS.readBinFile (l / "index.log")
  let some st ← status exe l | IO.eprintln "the sealed Store L does not check"; return 1
  let count := idx.size / eb
  let total := count + field st "records"
  let k := total / 2
  let say (label : String) (ok : Bool) (detail : String) : IO Bool := do
    IO.println s!"PLANT {label} {if ok then "PASS" else "FAIL"} :: {detail}"
    return ok
  -- the precondition: whole entries, and the probed entry a counted one before the last
  let pre := idx.size % eb = 0 && 0 < k && k + 1 < count
  unless ← say "index-middle-entry-is-counted-not-last" pre
      s!"index.log {idx.size} bytes = {count} entries of {eb} (+{idx.size % eb}); tail records {field st "records"}; probe entry {k}" do
    return 1
  let some frame := Founder.logFrame w0.origin 1 | IO.eprintln "the log envelope does not fit its frame"; return 1
  let reply (d : System.FilePath) : IO (UInt32 × UInt8 × String) := do
    let (c, out, _) ← hostRaw exe ["serve", d.toString] frame
    let st8 := if out.size > 8 then out.get! 8 else 255
    return (c, st8, (String.fromUTF8? (out.extract 9 out.size)).getD s!"<{out.size} bytes>")
  let mut failed := 0
  let ctl := dir / "index-middle-control"
  backup l ctl
  let (c0, s0, _) ← reply ctl
  unless ← say "index-middle-log-page-intact-control" (c0 = 0 && s0 = Protocol.Status.ok.code)
      s!"serve exit={c0} reply status={s0} (ok = {Protocol.Status.ok.code})" do
    failed := failed + 1
  let d := dir / "index-middle-flip"
  backup l d
  let at_ := k * eb + eb / 2
  let flipped := idx.set! at_ (idx.get! at_ ^^^ 1)
  if flipped == idx then IO.eprintln "the index flip is a no-op"; return failed + 1
  IO.FS.writeBinFile (d / "index.log") flipped
  let (c1, s1, p1) ← reply d
  unless ← say "index-middle-flip-opens-page-badIndex"
      (c1 = 0 && s1 = Protocol.Status.refused.code && p1 = Page.Fault.name (.badIndex k))
      s!"serve exit={c1} (open ok = 0) reply status={s1} (refused = {Protocol.Status.refused.code}) payload={p1}" do
    failed := failed + 1
  let r ← host exe ["check", d.toString]
  unless ← say "index-middle-flip-check-indexCorrupt-names-entry"
      (r.code = Status.indexCorrupt.code.toUInt32 && (r.out.splitOn s!"indexCorrupt entry {k}").length = 2)
      s!"exit={r.code} want=indexCorrupt({Status.indexCorrupt.code}) entry {k} :: {r.out.replace "\n" " "}" do
    failed := failed + 1
  return failed

/-- The field `k` of a `k VALUE` line of `out`. -/
def lineField (out k : String) : Option String :=
  (out.splitOn "\n").findSome? fun l => match l.splitOn " " with
    | [a, v] => if a == k then some v else none
    | _ => none

/-- Whether `text` contains `part`. -/
def mentions (text part : String) : Bool := (text.splitOn part).length > 1

/-- HOST-35, through the real exe: one Store file removed from a copy of the intact Store (the
removal asserted first) is refused `missing` by code AND names the file on stderr, from `host
check`; and `host serve` over a copy without index.log, or without seg.log (the file the writer
used to re-create through O_CREAT), refuses the same and leaves it absent. -/
def missingPlants (exe : String) (intact dir : System.FilePath) : IO Nat := do
  let mut failed := 0
  let want := Status.missing.code.toUInt32
  for (label, f) in [("missing-key", "key"), ("missing-base", "base.world"),
      ("missing-index", "index.log"), ("missing-segment", "seg.log")] do
    let d := dir / label
    backup intact d
    IO.FS.removeFile (d / f)
    let gone := !(← (d / f).pathExists)
    let r ← host exe ["check", d.toString]
    let ok := gone && r.code = want && mentions r.out s!"refused missing {f}"
    IO.println s!"PLANT {label} {if ok then "PASS" else "FAIL"} removed={gone} exit={r.code} want=missing({want}) :: {r.out.replace "\n" " "}"
    unless ok do failed := failed + 1
  for (label, f) in [("missing-index-serve", "index.log"), ("missing-segment-serve", "seg.log")] do
    let d := dir / label
    backup intact d
    IO.FS.removeFile (d / f)
    let gone := !(← (d / f).pathExists)
    let (code, _, err) ← hostRaw exe ["serve", d.toString] ByteArray.empty
    let still := !(← (d / f).pathExists)
    let ok := gone && code = want && mentions err s!"refused missing {f}" && still
    IO.println s!"PLANT {label} {if ok then "PASS" else "FAIL"} removed={gone} exit={code} want=missing({want}) absent_after={still} :: {err.replace "\n" " "}"
    unless ok do failed := failed + 1
  return failed

/-- OPS-P1 / HOST-28: law 1's state carry through the real exe, from the sealed live Store `L`
(48 calls, real bases). Export reads only; import is refused by name before any Store file for
a missing or wrong digest, a byte flipped in transit, another stamp; a good import keeps the
height under a new origin and chain (checked against KERNEL's `Receive.carry` in process); a call
committed before the export is `lookup` committed after (PROTOCOL-29: the journal is carried);
a call signed for the old origin does not land, one signed for the new origin (as the carried
member) does; two imports are two Worlds. -/
def carryPlants (exe : String) (dir : System.FilePath) : IO Nat := do
  let l := dir / "L"
  let w0 ← match Founder.world name with
    | .ok w => pure w
    | .error r => do IO.eprintln s!"genesis refused {r.name}"; return 1
  let n := 48
  let (calls, wL) ← (List.range n).foldlM (init := (([] : List (Call D)), w0)) fun (cs, w) i => do
    let c := Founder.create w i (bigState i)
    match submit X w c with
    | .ok (_, w') => pure (c :: cs, w')
    | .error _ => throw (IO.userError s!"carry fixture call {i} does not admit in process")
  let mut failed := 0
  let say (label : String) (ok : Bool) (detail : String) : IO Bool := do
    IO.println s!"PLANT {label} {if ok then "PASS" else "FAIL"} :: {detail}"
    return ok
  let snap (d : System.FilePath) : IO (List ByteArray) := Host.Store.backupOrder.mapM fun (f : String) => IO.FS.readBinFile (d / System.FilePath.mk f)
  let before ← snap l
  let out := dir / "L.carried"
  let e ← host exe ["export", l.toString, out.toString]
  let after ← snap l
  let digest := (lineField e.out "carried").getD ""
  let ok1 := e.code = 0 && before == after && lineField e.out "anchor" = some (anchorArg wL) &&
    lineField e.out "from" = some wL.origin.toHex && digest.length = 64
  unless ← say "carry-export-reads-only" ok1 s!"exit={e.code} store unchanged={before == after} :: {e.out.replace "\n" " "}" do
    failed := failed + 1
  unless ← judge ⟨"carry-export-over-existing", .exists, host exe ["export", l.toString, out.toString]⟩ do failed := failed + 1
  let file ← IO.FS.readBinFile out
  let empty (d : System.FilePath) : IO Bool := do
    if !(← d.pathExists) then return true
    return (← d.readDir).isEmpty
  -- refusals before any Store file
  let refusedEmpty (label : String) (want : Status) (args : List String) (d : System.FilePath) : IO Bool := do
    let r ← host exe args
    let ok := r.code = want.code.toUInt32 && (← empty d)
    say label ok s!"exit={r.code} want={want.name}({want.code}) no Store file={← empty d} :: {r.out.replace "\n" " "}"
  let c0 := dir / "carry-refused"
  unless ← refusedEmpty "carry-import-no-digest" .usage ["import", c0.toString, "plants-carry", out.toString] c0 do failed := failed + 1
  unless ← refusedEmpty "carry-import-wrong-digest" .carryMismatch
      ["import", c0.toString, "plants-carry", out.toString, "--digest", String.ofList (List.replicate 64 '0')] c0 do
    failed := failed + 1
  let flipAt := file.size - 7
  let flipped := file.set! flipAt (file.get! flipAt ^^^ 1)
  if flipped == file then IO.eprintln "the in-transit flip is a no-op"; return failed + 1
  let fOut := dir / "flipped.carried"
  IO.FS.writeBinFile fOut flipped
  unless ← refusedEmpty "carry-import-flipped-in-transit" .carryMismatch
      ["import", c0.toString, "plants-carry", fOut.toString, "--digest", digest] c0 do failed := failed + 1
  let stamped := file.set! 0 (file.get! 0 ^^^ 1)
  let sOut := dir / "stamp.carried"
  IO.FS.writeBinFile sOut stamped
  unless ← refusedEmpty "carry-import-other-stamp" .shapeMismatch
      ["import", c0.toString, "plants-carry", sOut.toString, "--digest", (Carry.digestOf stamped).toHex] c0 do
    failed := failed + 1
  -- the good import, under a fixed nonce so KERNEL's carry is rebuilt here
  let nonce2 := Founder.nonce.set! 2 (Founder.nonce.get! 2 ^^^ 1)
  let wC ← match Receive.carry X "plants-carry".toUTF8 nonce2 wL.origin wL.carried with
    | .ok w => pure w
    | .error r => do IO.eprintln s!"the in-process carry refused {r.name}"; return failed + 1
  let c := dir / "C"
  let i ← host exe ["import", c.toString, "plants-carry", out.toString, "--digest", digest,
    "--nonce", Protocol.Text.toHex nonce2]
  let st ← status exe c
  let h := (st.map (field · "height")).getD 0
  let chainC := (st.bind (·.lookup "chain")).getD ""
  let ok2 := i.code = 0 && h = n && chainC = wC.chain.toHex && chainC ≠ wL.chain.toHex &&
    lineField i.out "origin" = some wC.origin.toHex && wC.origin ≠ wL.origin
  unless ← say "carry-import-keeps-height-new-origin" ok2
      s!"exit={i.code} height={h} (want {n}) chain=KERNEL's carry {decide (chainC = wC.chain.toHex)} new {decide (chainC ≠ wL.chain.toHex)} :: {i.out.replace "\n" " "}" do
    failed := failed + 1
  -- PROTOCOL-29: the last call before the export answers `lookup` committed in the new World
  let some last := calls.head? | IO.eprintln "no fixture calls"; return failed + 1
  let (lc, lout, _) ← hostRaw exe ["serve", c.toString] (Founder.lookupFrame last)
  let st8 := if lout.size > 8 then lout.get! 8 else 255
  let ok3 := lc = 0 && st8 = Protocol.Status.ok.code
  unless ← say "carry-lookup-committed-after-import" ok3 s!"serve exit={lc} reply status={st8} (ok = {Protocol.Status.ok.code})" do
    failed := failed + 1
  -- a fresh call signed for the OLD origin does not land; one for the new origin, as the carried member, does
  let old := Founder.create wL n
  -- the control: a call never committed is NOT answered ok, so the row above is not vacuous
  let (_, lout2, _) ← hostRaw exe ["serve", c.toString] (Founder.lookupFrame old)
  let stNo := if lout2.size > 8 then lout2.get! 8 else 255
  unless ← say "carry-lookup-uncommitted-not-ok-control" (stNo ≠ Protocol.Status.ok.code) s!"reply status={stNo}" do
    failed := failed + 1
  let _ ← host exe ["serve", c.toString] (Founder.submitFrame old)
  let h1 := ((← status exe c).map (field · "height")).getD 0
  unless ← say "carry-old-origin-call-not-admitted" (h1 = n) s!"height {h1} (want {n})" do failed := failed + 1
  let me := founderId X wL.origin 0
  let fresh := Founder.createAs me wC n
  let inProc := (submit X wC fresh).isOk
  let _ ← host exe ["serve", c.toString] (Founder.submitFrame fresh)
  let h2 := ((← status exe c).map (field · "height")).getD 0
  unless ← say "carry-new-origin-call-admitted" (inProc && h2 = n + 1)
      s!"in process {inProc}; height {h2} (want {n + 1})" do failed := failed + 1
  -- two imports of one export are two Worlds
  let c2 := dir / "C2"
  let i2 ← host exe ["import", c2.toString, "plants-carry", out.toString, "--digest", digest]
  let o2 := lineField i2.out "origin"
  let ok4 := i2.code = 0 && o2.isSome && o2 ≠ some wC.origin.toHex && o2 ≠ some wL.origin.toHex
  unless ← say "carry-two-imports-two-worlds" ok4 s!"exit={i2.code} origin {o2.getD "?"}" do failed := failed + 1
  return failed

/-- PROTOCOL-42's `host join` through the real exe, as RUNBOOK §2b's install line runs it (the
hosted follower's Store) and as `nd --join` runs it confined (a member's, §2): into a directory
made empty first, from founder 0's invitation (`Founder.invitation`) and the sponsor key as hex.
A forged invitation (one signature byte flipped, the flip asserted) and a key other than the
sponsor's are refused `inviteRefused` (44) by name and the directory stays EMPTY (`join_genesis_iff`
through the files); the honest join prints the writer's origin (as `host genesis` of Store `A` printed it),
the sponsor's member id and the genesis inputs, and `host check` opens it at height 0; a second
join into it is `exists`. Then the follower unit's verb: `host follow` over the refused join's
empty directory ends `missing`, a FATAL class (the rendered unit's RestartPreventExitStatus,
`ofNode_prevent`), so a refused join never becomes a follower that restarts; over the joined Store
it opens (STATUS on stderr) and ends `eof` at the end of its input. -/
def joinPlants (exe : String) (genesisOut : String) (dir : System.FilePath) : IO Nat := do
  let w ← match Founder.world name with
    | .ok w => pure w
    | .error r => do IO.eprintln s!"genesis refused {r.name}"; return 1
  let some inv := Founder.invitation name | IO.eprintln "the test invitation does not fit"; return 1
  let some writerOrigin := lineField genesisOut "origin" | IO.eprintln "genesis printed no origin"; return 1
  let say (label : String) (ok : Bool) (detail : String) : IO Bool := do
    IO.println s!"PLANT {label} {if ok then "PASS" else "FAIL"} :: {detail}"
    return ok
  let empty (d : System.FilePath) : IO Bool := return (← d.readDir).isEmpty
  let hex := Protocol.Text.toHex
  let key := hex Founder.key
  let mut failed := 0
  let refused (label part : String) (inv k : String) : IO Bool := do
    let d := dir / label
    IO.FS.createDirAll d
    let r ← host exe ["join", d.toString, inv, k]
    let e ← empty d
    let ok := r.code = Status.inviteRefused.code.toUInt32 && mentions r.out s!"refused inviteRefused {part}" && e
    say label ok s!"exit={r.code} want=inviteRefused({Status.inviteRefused.code}) empty={e} :: {r.out.replace "\n" " "}"
  let at_ := inv.size - 1
  let forged := inv.set! at_ (inv.get! at_ ^^^ 1)
  if forged == inv then IO.eprintln "the forgery is a no-op"; return 1
  unless ← refused "join-forged-invitation-writes-nothing" "pinMismatch" (hex forged) key do failed := failed + 1
  if Founder.next == Founder.key then IO.eprintln "the other key is the sponsor's"; return failed + 1
  unless ← refused "join-other-key-notSponsor-writes-nothing" "notSponsor" (hex inv) (hex Founder.next) do
    failed := failed + 1
  let j := dir / "join-honest"
  IO.FS.createDirAll j
  let r ← host exe ["join", j.toString, hex inv, key]
  let st ← status exe j
  let origin := lineField r.out "origin"
  let ok := r.code = 0 && origin = some w.origin.toHex && origin = some writerOrigin &&
    lineField r.out "sponsor" = some (founderId X w.origin 0).toHex &&
    lineField r.out "input" = some (hex (Founder.input name)) && (st.map (field · "height")) = some 0
  unless ← say "join-honest-is-the-writers-world" ok
      s!"exit={r.code} origin=writer's {decide (origin = some writerOrigin)} opens={st.isSome} :: {r.out.replace "\n" " "}" do
    failed := failed + 1
  unless ← judge ⟨"join-again-exists", .exists, host exe ["join", j.toString, hex inv, key]⟩ do failed := failed + 1
  let member := (founderId X w.origin 0).toHex
  let grant := (founderGrantId X w.origin 0).toHex
  let d := dir / "join-forged-invitation-writes-nothing"
  let (code, _, err) ← hostRaw exe ["follow", d.toString, member, grant] ByteArray.empty
  let ok := code = Status.missing.code.toUInt32 && Status.missing.cls = .fatal && (← empty d)
  unless ← say "follow-over-refused-join-is-fatal" ok
      s!"exit={code} want=missing({Status.missing.code}, fatal: never restarted) :: {err.replace "\n" " "}" do
    failed := failed + 1
  let (code, _, err) ← hostRaw exe ["follow", j.toString, member, grant] ByteArray.empty
  let ok := code = 0 && mentions err "STATUS"
  unless ← say "follow-opens-the-joined-store" ok s!"exit={code} :: {err.replace "\n" " "}" do
    failed := failed + 1
  return failed
/-- Founder 0 writes one state slot of `obj` (an object it made): a USE whose maker signed it. -/
def selfWrite (w : World D) (obj : D) : Call D :=
  let me := founderId X w.origin 0
  let u : Unsigned D :=
    { world := w.origin, member := me, key := Founder.key, notBefore := 0,
      validUntil := Bounds.windowMax / 2 + 8,
      pins := [(me, pinOf X.env (w.entry X.env me)), (obj, pinOf X.env (w.entry X.env obj))],
      maxCharge := 1 <<< 40, body := .write obj [(stateBase, some "self".toUTF8)] none }
  { unsigned := u, signature := Codec.Ed25519.sign Founder.seed (X.callMessage u) }

/-- `use=` (PROTOCOL-43's count on a real Store, cv 01a14de7-225e), through the real exe and in
process:
* `use-zero-on-creates-only` (a control): `host check` of `intact` (4 creates, no use) reads 0;
* `use-self-use-zero` (the tooth for the member condition): a copy of `intact` where founder 0 also
  WRITES an object it made reads 0 through `host check`; a count that forgot "a member other than
  the maker" reads 1 here (measured by mutating `Protocol.Use.sharedBy`). A positive count needs a
  second member (an invitation and a grant), which row `use` holds;
* `use-reads-every-call` (fidelity, IN PROCESS through `Host.Check.callsAt`, not the exe): the
  calls read back from `intact`'s records are exactly the 4 served calls' bytes, in order.
The number that failed. -/
def usePlants (exe : String) (dir intact : System.FilePath) (calls : List (Call D)) (w4 : World D) :
    IO Nat := do
  let useOf (d : System.FilePath) : IO String := do
    pure (((← status exe d).bind (·.lookup "use")).getD "?")
  let u0 ← useOf intact
  IO.println s!"PLANT use-zero-on-creates-only {if u0 == "0" then "PASS" else "FAIL"} :: host check intact reads use={u0}"
  -- the self-use: the first call's object, written by its maker
  let selfOk ← do
    let .ok w0 := Founder.world name | pure (false, "genesis refused")
    let some c0 := calls.head? | pure (false, "no calls")
    let .ok (t0, _) := submit X w0 c0 | pure (false, "call 0 does not admit")
    let some (obj, _) := t0.creates.head? | pure (false, "call 0 created nothing")
    let c := selfWrite w4 obj
    let .ok _ := submit X w4 c | pure (false, "the self-write does not admit in process")
    let d := dir / "selfuse"
    backup intact d
    let r ← host exe ["serve", d.toString] (Founder.submitFrame c)
    if r.code ≠ 0 then pure (false, s!"serve exit={r.code}") else
    let u ← useOf d
    pure (u == "0", s!"host check selfuse reads use={u}")
  IO.println s!"PLANT use-self-use-zero {if selfOk.1 then "PASS" else "FAIL"} :: {selfOk.2}"
  let opened ← Host.Check.openClean intact.toString
  let readBack ← match opened with
    | .error (s, n) => pure (Except.error s!"{s.name} {n}")
    | .ok (keys, o) => Host.Check.callsAt intact.toString keys o
  let served := calls.map X.callBytes
  let same := match readBack with
    | .ok cs => cs.map X.callBytes == served
    | .error _ => false
  let got := match readBack with
    | .ok cs => s!"{cs.length} read back"
    | .error n => s!"refused {n}"
  IO.println s!"PLANT use-reads-every-call {if same then "PASS" else "FAIL"} :: {served.length} served, {got} (in process)"
  return (if u0 == "0" then 0 else 1) + (if selfOk.1 then 0 else 1) + (if same then 0 else 1)

/-- HOST-43's `host seal STORE` through the real exe, on a copy of the intact Store (height 4,
genesis base). A writer serving it holds the Store's lock: `host seal` is refused `locked` (16)
and every Store file is byte-identical after it; the row asserts the writer was still running before
and after the seal (OPS-4's first draft let the stdin handle go out of use, the writer ended at
eof, and the seal ran on a stopped Store: exit 0, read as a host defect until reproduced by hand). With the writer stopped, one seal: the printed
`sealed steps=S chain=C digest=D` is the World the Store holds, computed HERE by `Receive.submit`
of the same five calls (steps, chain) and the unkeyed `Keys.worldDigest` of its bytes (digest:
the pin an invitation names), and `host check` reads that base (`base_steps` = S). A second
seal at the sealed position writes nothing: the same line, every file byte-identical and
`base.world`'s modification time unchanged. -/
def sealPlants (exe : String) (intact dir : System.FilePath) (w4 : World D) : IO Nat := do
  let s := dir / "seal"
  backup intact s
  let c := Founder.create w4 4
  let w5 ← match submit X w4 c with
    | .ok (_, w) => pure w
    | .error _ => do IO.eprintln "the seal fixture call does not admit in process"; return 1
  let snap : IO (List ByteArray) := Host.Store.backupOrder.mapM fun (f : String) => IO.FS.readBinFile (s / System.FilePath.mk f)
  let say (label : String) (ok : Bool) (detail : String) : IO Bool := do
    IO.println s!"PLANT {label} {if ok then "PASS" else "FAIL"} :: {detail}"
    return ok
  let mut failed := 0
  -- a live writer: fed one call, so its open (and lock) is proved by the height it reaches
  let child ← IO.Process.spawn
    { cmd := exe, args := #["serve", s.toString], stdin := .piped, stdout := .piped, stderr := .piped }
  let (input, child) ← child.takeStdin
  let out ← IO.asTask child.stdout.readBinToEnd (prio := .dedicated)
  let err ← IO.asTask child.stderr.readToEnd (prio := .dedicated)
  let waited ← IO.asTask child.wait (prio := .dedicated)
  input.write (Founder.submitFrame c)
  input.flush
  let some _ ← awaitStatus exe s (field · "height" ≥ 5) | do
    child.kill; IO.println "PLANT seal-live-writer-locked FAIL :: the writer never reached height 5"; return 1
  let before ← snap
  let liveBefore := !(← IO.hasFinished waited)
  let r ← host exe ["seal", s.toString]
  let after ← snap
  let liveAfter := !(← IO.hasFinished waited)
  unless ← say "seal-live-writer-locked" (liveBefore && liveAfter && r.code = Status.locked.code.toUInt32 && before == after)
      s!"writer serving before={liveBefore} after={liveAfter}; exit={r.code} want=locked({Status.locked.code}) files unchanged={before == after} :: {r.out.replace "\n" " "}" do
    failed := failed + 1
  -- stop the writer: end of its input (the handle is used up to here, so it is not freed before the
  -- seal ran: a dropped stdin closes the pipe and the writer ends at eof), a bounded wait, its own
  -- Child handle if it overstays
  input.flush
  let (_, child) ← child.takeStdin
  let mut steps := 0
  while !(← IO.hasFinished waited) && steps < pollSteps do
    IO.sleep pollMs
    steps := steps + 1
  unless ← IO.hasFinished waited do
    child.kill
    IO.println "PLANT seal-base-is-the-pin FAIL :: the writer did not end at eof within the deadline (killed by its own Child handle)"
    return failed + 1
  let _ ← IO.ofExcept waited.get
  let _ ← IO.ofExcept out.get
  let _ ← IO.ofExcept err.get
  let want := s!"sealed steps={w5.steps} chain={w5.chain.toHex} digest={Protocol.Text.toHex (Codec.Hash.digest domBaseDigest (Host.Deployed.world.bytes w5)).bytes}"
  let r1 ← host exe ["seal", s.toString]
  let line1 := ((r1.out.splitOn "\n").find? (·.startsWith "sealed ")).getD ""
  let st ← status exe s
  let based := (st.map (field · "base_steps")) = some w5.steps && (st.map (field · "height")) = some 5
  unless ← say "seal-base-is-the-pin" (r1.code = 0 && line1 = want && based)
      s!"exit={r1.code} line=in-process {decide (line1 = want)} base_steps={(st.map (field · "base_steps")).getD 0} (want {w5.steps}) :: {line1}" do
    failed := failed + 1
  let b0 ← snap
  let m0 ← (s / "base.world").metadata
  let r2 ← host exe ["seal", s.toString]
  let line2 := ((r2.out.splitOn "\n").find? (·.startsWith "sealed ")).getD ""
  let b1 ← snap
  let m1 ← (s / "base.world").metadata
  let same := b0 == b1 && m0.modified == m1.modified
  unless ← say "seal-again-idempotent" (r2.code = 0 && line2 = line1 && !line1.isEmpty && same)
      s!"exit={r2.code} same line={decide (line2 = line1)} files and base.world mtime unchanged={same}" do
    failed := failed + 1
  return failed

def run (exe : String) (dir : System.FilePath) (control : Bool := false) : IO UInt32 := do
  if ← dir.pathExists then IO.eprintln s!"store-plants: {dir} exists"; return 2
  IO.FS.createDirAll dir
  let a := dir / "A"
  let g ← host exe (["genesis", a.toString, name] ++ Founder.genesisArgs)
  unless g.code = 0 do IO.eprintln s!"genesis: {g.out}"; return 1
  let origin := (← IO.FS.readBinFile (a / "seg.log")).size
  if origin = 0 then IO.eprintln "genesis wrote an empty segment (no origin frame)"; return 1
  let .ok (calls, w4) := expected 4 | IO.eprintln "a fixture call does not admit in process"; return 1
  let .ok (_, w2) := expected 2 | return 1
  -- one record per serve run, so record boundaries are known
  let mut sizes : Array Nat := #[]
  for c in calls do
    let r ← host exe ["serve", a.toString] (Founder.submitFrame c)
    unless r.code = 0 do IO.eprintln s!"serve: {r.out}"; return 1
    sizes := sizes.push (← IO.FS.readBinFile (a / "seg.log")).size
    if sizes.size = 2 then backup a (dir / "old2")
  let seg ← IO.FS.readBinFile (a / "seg.log")
  let at_ (i : Nat) : Nat := sizes[i]!
  -- another history under the same key: a copy at height 2 that admits two other calls
  let b := dir / "B"
  backup (dir / "old2") b
  let mut wb := w2
  let mut wb3 := w2
  for i in [4, 5] do
    let c := Founder.create wb i
    let r ← host exe ["serve", b.toString] (Founder.submitFrame c)
    unless r.code = 0 do IO.eprintln s!"serve B: {r.out}"; return 1
    match submit X wb c with
    | .ok (_, w') =>
      wb := w'
      if w'.height = 3 then wb3 := w'
    | .error _ => IO.eprintln s!"B's call {i} does not admit in process"; return 1
  let anchor := ["--anchor", anchorArg w4]
  let check (d : System.FilePath) (extra : List String := []) : IO Run :=
    host exe (["check", d.toString] ++ extra)
  let copy (label : String) (f : System.FilePath → IO Unit := fun _ => pure ()) : IO System.FilePath := do
    let d := dir / label
    backup a d
    f d
    return d
  let intact ← copy "intact"
  let cut ← copy "cut" fun d => damage d (seg.extract 0 (at_ 2))
  let torn ← copy "torn" fun d => damage d (seg.extract 0 ((at_ 2 + at_ 3) / 2))
  let drop ← copy "drop" fun d => damage d (seg.extract 0 (at_ 0) ++ seg.extract (at_ 1) seg.size)
  let foreign ← copy "foreign" fun d => do
    let bseg ← IO.FS.readBinFile (b / "seg.log")
    damage d (seg.extract 0 (at_ 2) ++ bseg.extract (at_ 2) bseg.size)
  -- the origin frame is genesis's whole segment and sits before the base (HOST-18)
  let o := origin / 2
  let flip ← copy "flip" fun d => damage d (seg.set! o (seg.get! o ^^^ 1))
  let t := at_ 0 + (at_ 1 - at_ 0) / 2
  let flipTail ← copy "fliptail" fun d => damage d (seg.set! t (seg.get! t ^^^ 1))
  let wrongKey ← copy "wrongkey" fun d => IO.FS.writeBinFile (d / "key") (ByteArray.mk (Array.replicate 32 0))
  let plants : List Plant :=
    [⟨"intact-copy-anchor", .eof, check intact anchor⟩,
     ⟨"cut-at-frame-no-anchor", .eof, check cut⟩,
     ⟨"cut-at-frame-anchor", .behindAnchor, check cut anchor⟩,
     ⟨"cut-mid-frame-anchor", .behindAnchor, check torn anchor⟩,
     ⟨"splice-drop-middle-record", .corrupt, check drop⟩,
     ⟨"splice-foreign-last-frame-no-anchor", .eof, check foreign⟩,
     ⟨"splice-foreign-last-frame-anchor", .behindAnchor, check foreign anchor⟩,
     ⟨"flip-byte-origin-frame-before-base", .corrupt, check flip⟩,
     ⟨"flip-byte-second-record", .corrupt, check flipTail⟩,
     ⟨"wrong-key", .baseCorrupt, check wrongKey⟩,
     ⟨"rollback-older-copy-no-anchor", .eof, check (dir / "old2")⟩,
     ⟨"rollback-older-copy-anchor", .behindAnchor, check (dir / "old2") anchor⟩,
     ⟨"other-history-same-height-anchor", .chainMismatch, check b anchor⟩,
     ⟨"past-height-anchor", .eof, check intact ["--anchor", anchorArg w2]⟩,
     ⟨"past-height-other-history-anchor", .chainMismatch, check intact ["--anchor", anchorArg wb3]⟩,
     ⟨"missing-store", .io, check (dir / "absent")⟩]
  let mut failed := 0
  -- `--harness-control` (GATES-15): the intact copy judged as if it had to be refused `corrupt`, a
  -- plant nothing meets, on the ordinary judge path: the run must read `PLANT harness-control FAIL`.
  -- It proves `judge`, the failed count and the exit; the rows that print through their own `say`
  -- predicates (live, carry, join, seal, use) are covered by their own measured teeth, not by this.
  let plants := plants ++ (if control then [⟨"harness-control", .corrupt, check intact anchor⟩] else [])
  for p in plants do
    unless ← judge p do failed := failed + 1
  failed := failed + (← usePlants exe dir intact calls w4)
  -- `check` writes nothing: the torn copy still holds its torn bytes
  let tornNow := (← IO.FS.readBinFile (torn / "seg.log")).size
  let ro := tornNow = (at_ 2 + at_ 3) / 2
  IO.println s!"PLANT check-writes-nothing {if ro then "PASS" else "FAIL"} torn seg.log {tornNow} bytes"
  unless ro do failed := failed + 1
  failed := failed + (← live exe dir)
  failed := failed + (← replay exe dir)
  failed := failed + (← originPlants exe dir)
  failed := failed + (← middleEntryPlant exe dir)
  failed := failed + (← indexMovedPlant exe dir)
  failed := failed + (← carryPlants exe dir)
  failed := failed + (← missingPlants exe intact dir)
  failed := failed + (← joinPlants exe g.out dir)
  failed := failed + (← sealPlants exe intact dir w4)
  if failed = 0 then IO.println "ALL PASS"; return 0
  IO.println s!"FAIL {failed} of {plants.length}"; return 1

def main : List String → IO UInt32
  | [exe, dir] => run exe dir
  | [exe, dir, "--harness-control"] => run exe dir true
  | _ => do IO.eprintln "usage: store-plants HOST_EXE DIR [--harness-control]"; return 2

end Nanodregg.Ops.Plants
