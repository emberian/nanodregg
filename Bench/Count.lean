/-
# Bench.Count — `bench-count STORE SCRATCH [--harness-control]` (PERF-3, ROOT-ruled 2026-10-18)

THE BAR's work counted at deployed parameters, from THE BAR's own Store: the Store the deployed
`host serve` wrote (scripts/bar.sh hands it over), opened read-only exactly as a follower reopens
(`openAt`, the one open), but with every record re-derived as a follower re-derives it at follow time:
`Receive.rederiveStep` (decode each logged step's event and re-derive it as `host follow` does,
`Receive.rederive`: a Turn by `submit`, a refusal by `judge` or `cancel`; require the very same
step), under the deployed `Ctx` with two marks added:
every trie-domain hash (KERNEL-36's `countingEnv`, `#`) and every signature verify (`@`). The marks
go to stderr, which this process captures and counts, as kernel-sim's `report` does. Nothing in the
deployed path changes and no deployed module names this one: the host counts nothing (law 3), this
replays the bytes it wrote.

The count is of the real workload or it is refused:
- the replay must reach, record by record, the roots each record states (`Record.step`'s check), and
  at the end the very World the host's own reopen (`foldStep`) reaches: the same steps, chain and
  roots digest. A mismatch is `FAIL replay …`, never a count;
- PLANT toy-store: SCRATCH/toy is made a Store by the Sim's toy genesis (u64 digest, FNV sealers,
  the toy codec) and opened the same way; it must be refused, by name, before anything is counted.
  A counter that would count a toy Store's work as THE BAR's is FAIL;
- `--harness-control` (GATES-15): one expectation nothing meets, judged on the ordinary path: the
  replayed chain must equal the host's chain with its first byte flipped. It reads
  `FAIL harness-control …`.

Prints `COUNT …` lines, `WASTE bar trie-hashes-per-required R` (the trie hashes counted ÷ those the
replayed steps require, `Kernel.Sim.Required`: exact on every draw, rounded up; a count below the
requirement, or a requirement refused, is `FAIL required …`), `WASTE bar audit-verifies-per-step R`
(per step of the tail the open replays: the steps past the newest base), and `BENCH-COUNT PASS`.
-/
import Host.Deployed
import Host.Sim.File
import Kernel.Receive.Rederive
import Kernel.Sim.Gen

namespace Nanodregg.Bench.Count

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Host.Deployed

/-- The deployed `Ctx` with its trie hashes (`#`, `countingEnv`) and signature verifies (`@`)
marked on stderr. Every answer is the deployed one: the marks change no value. -/
def countingX : Ctx D :=
  { X with
    env := Kernel.Sim.Gen.countingEnv X.env
    verify := fun k m s => dbgTrace "@" fun _ => X.verify k m s }

/-- What step `w → w'` requires of trie hashes (cv 01a14afe-7380): the transition's
(`Kernel.Sim.Required.step`, read off the tries it built, uncounted) and the record's roots check of
`w'` (one shared empty digest when one of its four roots is empty, `Required.emptyRoots`), marked `%`
once per hash; `?` when the requirement is refused (a replay that does not reach `w'`). -/
def markRequired (w : World D) (s : Step D) (w' : World D) : Except (Verdict D) (World D) :=
  match Kernel.Sim.Required.step X.env w s w' with
  | .ok n => dbgTrace ("".pushn '%' (n + Kernel.Sim.Required.emptyRoots w')) fun _ => .ok w'
  | .error _ => dbgTrace "?" fun _ => .ok w'

/-- A follower's re-derivation of one record (`rederiveStep` per step), its stated roots checked; each
recorded refusal it re-judges is marked `!`, so a verify count is read against its Turns and refusals;
each step's requirement is marked beside it (`markRequired`). -/
def rederiveRecord (w : World D) (r : ByteArray) : Except (Record.Fault (Verdict D)) (World D) :=
  Record.step Codec.Deployed.digestCodec
    (fun w s =>
      let res := match s with
        | .refusal _ => dbgTrace "!" fun _ => rederiveStep countingX w s
        | _ => rederiveStep countingX w s
      match res with
      | .ok w' => markRequired w s w'
      | .error e => .error e)
    (World.roots countingX.env) w r

/-- Run `act` with stderr captured; its result and the captured text. -/
def captured {α : Type} (act : IO α) : IO (α × String) := do
  let buf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let old ← IO.setStderr (IO.FS.Stream.ofBuffer buf)
  let a ← try act finally discard <| IO.setStderr old
  return (a, String.fromUTF8! (← buf.get).data)

def marks (s : String) (ch : Char) : Nat := (s.toList.filter (· == ch)).length

/-- PLANT toy-store: a toy Store under `dir`, opened by the counting open; `none` when it is refused
(the refusal's name printed), `some why` when the plant fails. -/
def toyPlant (dir : System.FilePath) : IO (Option String) := do
  if ← dir.pathExists then return some s!"{dir} exists (SCRATCH must be fresh)"
  let key ← Host.Sim.File.newKey
  let made ← (Host.genesis dir key (Host.Sim.File.fileKeys key) Host.Sim.cadence Host.Sim.world
    Host.Sim.recorder.mark Host.Sim.genesis : IO (Except Host.Sim.File.Fault Unit))
  if let .error e := made then return some s!"the toy genesis failed ({e.name})"
  match ← (readKey dir : IO (Except (StoreFault (Record.Fault (Verdict D))) D)) with
  | .error e => IO.println s!"PLANT toy-store refused {e.text}"; return none
  | .ok k =>
    match ← (·.map Prod.fst) <$> openAt dir (Keys.ofKey k shapes) c world recorder.mark originChain rederiveRecord with
    | .error e => IO.println s!"PLANT toy-store refused {e.text}"; return none
    | .ok _ => return some "a toy Store opened as THE BAR's: its work would be counted"

def ratio (n d : Nat) : String :=
  let m := (n * 1000 + d / 2) / d
  s!"{m / 1000}.{(toString (m % 1000 + 1000)).drop 1}"

/-- `ratio` rounded UP: an exact row reads above 1.000 at a single extra hash. -/
def ratioUp (n d : Nat) : String :=
  let m := (n * 1000 + d - 1) / d
  s!"{m / 1000}.{(toString (m % 1000 + 1000)).drop 1}"

def count (args : List String) : IO UInt32 := do
  let (store, scratch, control) ← match args with
    | [s, t] => pure (s, t, false)
    | [s, t, "--harness-control"] => pure (s, t, true)
    | _ => do IO.eprintln "usage: bench-count STORE SCRATCH [--harness-control]"; return 2
  if let some why ← toyPlant (System.FilePath.mk scratch / "toy") then
    IO.println s!"FAIL plant toy-store: {why}"; return 1
  -- the host's own reopen: the World the count must reach
  let host ← match ← (readKey store : IO (Except (StoreFault (Record.Fault (Reject D))) D)) with
    | .error e => IO.println s!"FAIL open: {e.text}"; return 1
    | .ok k =>
      match ← (·.map Prod.fst) <$> openAt store (Keys.ofKey k shapes) c world recorder.mark originChain foldStep with
      | .error e => IO.println s!"FAIL open: {e.text}"; return 1
      | .ok o => pure o
  let key ← match ← (readKey store : IO (Except (StoreFault (Record.Fault (Verdict D))) D)) with
    | .error e => IO.println s!"FAIL open: {e.text}"; return 1
    | .ok k => pure k
  let (r, err) ← captured ((·.map Prod.fst) <$> openAt store (Keys.ofKey key shapes) c world recorder.mark originChain rederiveRecord)
  let o ← match r with
    | .error e => IO.println s!"FAIL replay: the re-derivation refused {e.text}"; return 1
    | .ok o => pure o
  let (hw, rw) := (host.opened.world, o.opened.world)
  unless hw.steps == rw.steps && hw.chain.toHex == rw.chain.toHex
      && (World.roots X.env hw).toHex == (World.roots X.env rw).toHex do
    IO.println s!"FAIL replay: reached steps={rw.steps} chain={rw.chain.toHex}, the host steps={hw.steps} chain={hw.chain.toHex}"
    return (1 : UInt32)
  if control then
    let b := hw.chain.bytes
    let planted := b.set! 0 (b.get! 0 ^^^ 1)
    unless rw.chain.bytes == planted do
      IO.println s!"FAIL harness-control: the replayed chain {rw.chain.toHex} is not the planted one"
      return 1
  let steps := rw.steps - o.sealed.steps
  if steps == 0 then IO.println "FAIL count: no step past the base to count"; return 1
  let (h, v, rf) := (marks err '#', marks err '@', marks err '!')
  let (q, refusedReq) := (marks err '%', marks err '?')
  if refusedReq > 0 then
    IO.println s!"FAIL required: {refusedReq} steps whose requirement was refused (a replay did not reach the World the step reached)"
    return 1
  if h < q then
    IO.println s!"FAIL required: {h} trie hashes counted, below the {q} the steps require (the design changed: re-derive Kernel.Sim.Required)"
    return 1
  IO.println s!"COUNT steps {steps} (past the base at step {o.sealed.steps}, offset {o.sealed.offset}) trie-hashes {h} required {q} verifies {v}"
  IO.println s!"COUNT kinds turns {steps - rf} refusals {rf} (recorded refusals re-judged in the tail)"
  IO.println s!"COUNT trie-hashes-per-step {ratio h steps} (draw-dependent: the trie's shape follows the run's ids; the row is per required hash)"
  IO.println s!"WASTE bar trie-hashes-per-required {ratioUp h q}"
  IO.println s!"WASTE bar audit-verifies-per-step {ratio v steps}"
  IO.println "BENCH-COUNT PASS"
  return 0

/-- `count`, with an IO error (an absent STORE path, an unreadable file) refused by name, never an
uncaught exception. -/
def run (args : List String) : IO UInt32 := do
  try count args
  catch e =>
    IO.println s!"FAIL io: {e}"
    return (1 : UInt32)

end Nanodregg.Bench.Count
