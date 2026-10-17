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

def files : List String := ["key", "base.world", "seg.log"]

/-- The backup: the three files, in order. -/
def backup (src dst : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  for f in files do IO.FS.writeBinFile (dst / f) (← IO.FS.readBinFile (src / f))

/-- The World the Store should open to, and the calls that make it; every call must admit in
process, or the plants refuse to run. -/
def expected (n : Nat) : Except Nat (List (Call D) × World D) :=
  (List.range n).foldlM (fun (cs, w) i =>
    let c := Founder.create name w i
    match submit X w c with
    | .ok (_, w') => .ok (cs ++ [c], w')
    | .error _ => .error i) ([], Founder.world name)

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
    let c := Founder.create name wb i
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
  if failed = 0 then IO.println "ALL PASS"; return 0
  IO.println s!"FAIL {failed} of {plants.length}"; return 1

def main : List String → IO UInt32
  | [exe, dir] => run exe dir
  | _ => do IO.eprintln "usage: store-plants HOST_EXE DIR"; return 2

end Nanodregg.Ops.Plants
