/-
# Ops.Plants — backup and restore, planted against the real `host` (ASSEMBLY-ops D6/D7)

A backup is the Store's three files copied in the order `key`, `base.world`, `seg.log`; a restore
is the copy put back and judged by `host check STORE --anchor HEIGHT:CHAIN`. Each plant below
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

def anchorArg (w : World D) : String := s!"{w.height}:{w.chain.toHex}"

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
  -- anchors[h] is the kernel's own `HEIGHT:CHAIN` after the first h calls
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
  -- 2. feed until the writer seals a newer base, then copy the segment
  let mut sealed := none
  let mut fed := 4
  while sealed.isNone && fed < n do
    feed fed (fed + 4)
    fed := fed + 4
    sealed ← awaitStatus exe l fun st => field st "height" ≥ fed
    if let some st := sealed then
      if field st "base_height" ≤ field st0 "base_height" then sealed := none
  -- the append-only files after the base, in `Host.Store.backupOrder` (HOST-30: index.log first)
  IO.FS.writeBinFile (copy / "index.log") (← IO.FS.readBinFile (l / "index.log"))
  let segCopied ← IO.FS.readBinFile (l / "seg.log")
  IO.FS.writeBinFile (copy / "seg.log") segCopied
  let raced := sealed.isSome && (← IO.FS.readBinFile (l / "base.world")) != baseCopied
  say "live-copy-raced-a-seal" raced
    s!"base_height {field st0 "base_height"} at the base copy, {(sealed.map (field · "base_height")).getD 0} at the segment copy; the copied base is {if raced then "no longer" else "STILL"} the Store's"
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
  let hCopy := (sealed.map (field · "height")).getD 0
  let anchorAt (h : Nat) : List String := ["--anchor", anchors[h]!]
  let check (d : System.FilePath) (extra : List String := []) : IO Run :=
    host exe (["check", d.toString] ++ extra)
  let plain (label : String) (want : Status) (r : IO Run) : IO Nat := do
    return if ← judge ⟨label, want, r⟩ then 0 else 1
  failed := failed + (← plain "live-copy-anchor-at-segment-copy" .eof (check copy (anchorAt hCopy)))
  -- the sealed Store: it must have a base past the origin, or the rows below test nothing
  let some stS ← status exe l | IO.eprintln "the finished live Store does not check"; return failed + 1
  let off := field stS "base_offset"
  let hasBase := field stS "base_height" > 0 && off > originSeg.size
  say "sealed-store-has-a-real-base" hasBase s!"base_height={field stS "base_height"} base_offset={off} origin={originSeg.size} seg_bytes={field stS "seg_bytes"}"
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

def run (exe : String) (dir : System.FilePath) : IO UInt32 := do
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
  for p in plants do
    unless ← judge p do failed := failed + 1
  -- `check` writes nothing: the torn copy still holds its torn bytes
  let tornNow := (← IO.FS.readBinFile (torn / "seg.log")).size
  let ro := tornNow = (at_ 2 + at_ 3) / 2
  IO.println s!"PLANT check-writes-nothing {if ro then "PASS" else "FAIL"} torn seg.log {tornNow} bytes"
  unless ro do failed := failed + 1
  failed := failed + (← live exe dir)
  failed := failed + (← replay exe dir)
  failed := failed + (← originPlants exe dir)
  if failed = 0 then IO.println "ALL PASS"; return 0
  IO.println s!"FAIL {failed} of {plants.length}"; return 1

def main : List String → IO UInt32
  | [exe, dir] => run exe dir
  | _ => do IO.eprintln "usage: store-plants HOST_EXE DIR"; return 2

end Nanodregg.Ops.Plants
