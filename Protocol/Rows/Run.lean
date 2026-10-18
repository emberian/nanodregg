/-
# Protocol.Rows.Run — the row runner (`lake exe rows [NAME…]`, which `rows/run` is)

Runs every row of `Protocol.rows` (or the named ones) and prints one line per row,
`ROW <name> PASS`, `ROW <name> FAIL <why>` or `ROW <name> PENDING <why>`, then a last line:
`ALL PASS` (exit 0), `FAIL <n> of <m>` (exit 1) or `INCOMPLETE <n> pending` (exit 3; no row failed,
some have no driver yet). An unknown row name is refused before anything runs (exit 2).

The runner moves processes and bytes; `Protocol.Rows.Judge.judge` decides. An `exe` row is
`lake exe NAME ARGS` with stdin closed, waited for by polling under a deadline (killed past it;
the runner holds the child's handle, so the kill names exactly the process it started). A
`members` row runs in process (`Protocol.Rows.Loopback`: HOST's loop on its own thread, each actor's
follow machine and custody, every step through the wire codecs), under the deadline the same way;
then, if it passed, once more under its plant, which must be caught at its line by its outcome.
`--times N` scales every repeated line (THE BAR: `rows --times 1000 bar`).
-/
import Protocol.Rows.Judge
import Protocol.Rows.Loopback

namespace Nanodregg.Protocol.Rows

open Nanodregg.Protocol

def pollMs : UInt32 := 50
/-- One `exe` row's wall-clock deadline. -/
def rowDeadlineMs : Nat := 300000

/-- Poll a child until it exits, at most `n` times, sleeping `pollMs` between polls. -/
def waitFor {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) : Nat → IO (Option UInt32)
  | 0 => pure none
  | n + 1 => do
      match ← child.tryWait with
      | some code => pure (some code)
      | none => IO.sleep pollMs; waitFor child n

def lastLine (out : String) : String :=
  ((out.splitOn "\n").filter (· ≠ "")).getLast?.getD ""

/-- What one row's run produced: a verdict input, or why it could not run. -/
inductive Ran
  | observed (o : Observed) (transcript : String)
  | broken (why : String)
  | pending (why : String)

def runExe (name : String) (args : List String) : IO Ran := do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["exe", name] ++ args.toArray,
      stdin := .null, stdout := .piped, stderr := .piped }
  let out ← IO.asTask child.stdout.readToEnd
  let err ← IO.asTask child.stderr.readToEnd
  match ← waitFor child (rowDeadlineMs / pollMs.toNat) with
  | none =>
      child.kill
      let _ ← child.wait
      pure (.broken s!"past its {rowDeadlineMs} ms deadline; killed")
  | some code =>
      let o ← IO.ofExcept (← IO.wait out)
      let e ← IO.ofExcept (← IO.wait err)
      pure (.observed { exit := code, last := lastLine o } (o ++ e))

/-- Run a member row in a task, polling it under the row's deadline. -/
def runMembers (m : Option Mutation) (ls : List Line) (times : Option Nat) :
    IO (Except String Loopback.Result) := do
  let t ← IO.asTask (prio := .dedicated) (Loopback.run m ls times)
  let rec poll : Nat → IO Bool
    | 0 => pure false
    | n + 1 => do
        if ← IO.hasFinished t then pure true else IO.sleep pollMs; poll n
  if !(← poll (rowDeadlineMs / pollMs.toNat)) then
    return .error s!"past its {rowDeadlineMs} ms deadline"
  match ← IO.wait t with
  | .ok r => pure (.ok r)
  | .error e => pure (.error (toString e))

def p99 (ns : List Nat) : Nat :=
  let a := (ns.toArray.qsort (· < ·))
  a.getD ((a.size * 99) / 100) 0 |>.min (a.back?.getD 0)

/-- The machine's load, beside every timing it judges (memory: measure on a quiet machine). -/
def load : IO String := do
  try
    let o ← IO.Process.output { cmd := "sysctl", args := #["-n", "vm.loadavg"] }
    if o.exitCode = 0 then return o.stdout.trimAscii.toString
    return (← IO.FS.readFile "/proc/loadavg").trimAscii.toString
  catch _ => return "unknown"

/-- `a ÷ b` with three decimals, rounded (`b = 0` prints `a`: no division hidden). -/
def ratio (a b : Nat) : String :=
  if b = 0 then toString a else
  let m := (a * 1000 + b / 2) / b
  let frac := toString (m % 1000)
  s!"{m / 1000}.{"".pushn '0' (3 - frac.length)}{frac}"

/-- The plants' ratios on THE BAR's workload, stated: a plant is a tooth only while it bites by
exactly this much (both above the waste.tsv ceiling 1.546). -/
def plantAppStated : String := "1.885"
def plantExtractStated : String := "2.154"

/-- Nanoseconds as milliseconds with three decimals. -/
def ms (ns : Nat) : String :=
  let f := toString ((ns / 1000) % 1000)
  s!"{ns / 1000000}.{"".pushn '0' (3 - f.length)}{f}"

/-- THE BAR's record lines and its WASTE lines; an error if the invokes went unmeasured (a WASTE line
over no calls would read as zero cost and pass the ratchet: a fail-open). -/
def barLines (r : Row) (res : Loopback.Result) : IO (Option String) := do
  let timed := res.times.toList.filter fun t => (r.lines[t.line]?.bind (·.withinMs)).isSome
  let writes := (timed.filter fun t => match r.lines[t.line]? with
    | some { act := .cmd _, .. } => true | _ => false).flatMap (·.ns)
  IO.println s!"BAR write-n {writes.length}"
  IO.println s!"BAR write-p99-ms {ms (p99 writes)}"
  for ns in res.reopenNs do
    IO.println s!"BAR reopen-ms {ms ns}"
  IO.println s!"BAR load {← load}"
  -- the deterministic measures (pinned in gates/waste.tsv): over the invokes, the machine ticks
  -- per step the program requires (the size of its reference derivation, LANG's `requiredOf`) and
  -- the packages loaded and re-checked per call. Sums over sums, never a mean of ratios.
  if let some e := res.invokes.toList.findSome? fun | .error e => some e | .ok _ => none then
    return some s!"bar: an invoke's required count failed: {e}"
  let ms := res.invokes.toList.filterMap fun | .ok m => some m | .error _ => none
  let n := ms.length
  let ticks := ms.foldl (· + ·.ticks) 0
  let required := ms.foldl (· + ·.required) 0
  let planted := ms.foldl (· + ·.planted) 0
  if n = 0 then return some "bar: no invoke was measured"
  if required = 0 then return some "bar: the invokes required no steps (a ratio over nothing)"
  IO.println s!"WASTE invoke ticks-per-required-step {ratio ticks required}"
  IO.println s!"WASTE invoke packages-checked-per-call {ratio (ms.foldl (· + ·.pkgs) 0) n}"
  -- the ratio's teeth, each at its STATED value (a plant whose waste shrank is red, MOVED) and above
  -- the honest ratio (BLIND): two needless transitions per application (waste-app), and extraction
  -- run twice on the same value (waste-extract, cv 01a14abb-aa73)
  let extracted := ms.foldl (· + ·.extracted) 0
  for (name, total, stated) in [("waste-app", planted, plantAppStated),
      ("waste-extract", extracted, plantExtractStated)] do
    IO.println s!"PLANT {name} ticks-per-required-step {ratio total required}"
    if ratio total required ≠ stated then
      return some s!"bar: plant {name} MOVED {ratio total required}≠{stated}"
    if total * 1000 / required ≤ ticks * 1000 / required then
      return some s!"bar: plant {name} BLIND: {ratio total required} is not above {ratio ticks required}"
  return none

def drive (r : Row) (times : Option Nat) (control : Bool := false) : IO Ran :=
  if let some why := r.blockedOn then pure (.pending s!"blocked on {why}") else
  match r.drive with
  | .exe name args _ => runExe name args
  | .members ls => do
      match ← runMembers none ls times with
      | .error e => pure (.broken e)
      | .ok res =>
          if r.name = "bar" then
            if let some e ← barLines r res then return .broken e
          let t := String.intercalate "\n" res.log.toList
          match judge r res.observed, r.plant with
          | .pass, .caught m line got =>
              match ← runMembers (some m) ls times with
              | .error e => pure (.broken s!"plant {repr m}: {e}")
              | .ok pr =>
                  -- `--harness-control` (GATES-15): the plant is read at a line the row does not
                  -- have, a plant line that never fires; the runner must call it BLIND
                  let line := if control then r.lines.length else line
                  if caught r pr.observed line got then pure (.observed res.observed t)
                  else pure (.broken s!"plant {repr m} BLIND: line {line} expected to get {got.text}, \
                    outcomes {repr pr.observed.outcomes}{if control then " (harness-control)" else ""}")
          | _, _ => pure (.observed res.observed t)

/-- The last lines of a transcript, indented, for a failing row. -/
def tail (t : String) : String :=
  let ls := (t.splitOn "\n").filter (· ≠ "")
  String.intercalate "\n" ((ls.drop (ls.length - 40)).map ("  | " ++ ·))

/-- Run the rows; the exit code is the runner's verdict. -/
def runAll (selected : List Row) (times : Option Nat) (verbose : Bool) (control : Bool := false) : IO UInt32 := do
  let mut failed := 0
  let mut pending := 0
  let mut hung := 0
  for r in selected do
    match ← drive r times control with
    | .pending why =>
        pending := pending + 1
        IO.println s!"ROW {r.name} PENDING {why}"
    | .broken why =>
        failed := failed + 1
        IO.println s!"ROW {r.name} FAIL {why}"
    | .observed o t =>
        match judge r o with
        | .pass =>
            IO.println s!"ROW {r.name} PASS{match r.plant with
              | .caught m l g => s!" (plant {repr m} caught at line {l}: {g.text})"
              | .internal _ => ""}"
            if verbose then IO.println (tail t)
        | .fail why =>
            failed := failed + 1
            IO.println s!"ROW {r.name} FAIL {why}"
            IO.println (tail t)
        | .hang why =>
            hung := hung + 1
            IO.println s!"ROW {r.name} HANG {why} (a liveness deadline missed: not a verdict)"
            IO.println (tail t)
  if failed > 0 then
    IO.println s!"FAIL {failed} of {selected.length}"; pure 1
  else if pending + hung > 0 then
    IO.println s!"INCOMPLETE {pending} pending{if hung > 0 then s!", {hung} hang" else ""}"; pure 3
  else
    IO.println "ALL PASS"; pure 0

/-- `rows [-v] [--times N] [--harness-control] [ROW…]`. `--harness-control` (GATES-15) reads every
plant at a line its row does not have, so every planted row must read `FAIL … BLIND … (harness-control)`:
the known-red control gates/runs.py runs before reading a verdict. -/
def main (args : List String) : IO UInt32 := do
  let control := args.contains "--harness-control"
  let args := args.filter (· != "--harness-control")
  let (verbose, args) := match args with
    | "-v" :: rest => (true, rest)
    | _ => (false, args)
  let (times, args) := match args with
    | "--times" :: n :: rest => (n.toNat?, rest)
    | _ => (none, args)
  let unknown := args.filter fun a => !rows.any (·.name == a)
  if !unknown.isEmpty then
    IO.eprintln s!"rows: no such row: {String.intercalate " " unknown}"
    return 2
  runAll (if args.isEmpty then rows else rows.filter fun r => args.contains r.name) times verbose control

end Nanodregg.Protocol.Rows
