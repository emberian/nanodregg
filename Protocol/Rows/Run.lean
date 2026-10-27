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

`--deployed` runs every member row (and its plant) at the DEPLOYED parameters
(`Rows.Params.deployed`: `host`'s own `Ctx`, World codec and KMAC256 sealers, custody's Ed25519
keys) instead of the toy's; it selects the parameters the harness instantiates the one pipeline
with, never a mode inside admission (PROTOCOL-50). Before any row, the run measures its parameters'
widths (`Params.atDeployed`: a 32-byte digest, an Ed25519 key and signature, a 32-byte base digest
and tag) and requires the toy's to FAIL that check by name (`digest 8≠32`): the plant that the
check reads the parameters at all. Each row prints its cost in deterministic units beside the
verdict: `COST <row> frames <frames sent on either socket> steps <the writer's World steps>`.
-/
import Protocol.Rows.Judge
import Protocol.Rows.Loopback
import Protocol.Rows.Deployed

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
def runMembers {D : Type} [Ord D] [DecidableEq D] (R : Params D) (m : Option Mutation) (ls : List Line)
    (times : Option Nat) (budget : Option Nat := none) : IO (Except String Loopback.Result) := do
  let t ← IO.asTask (prio := .dedicated) (Loopback.run R m ls times budget)
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

/-- THE BAR's deterministic per-unit counts (PROTOCOL-53), each a numerator and its unit of work:
frames sent on either socket and the writer's steps, per write command run (every `.cmd` line but
`read`, each repetition counted); the segment bytes the measured reopens read, per byte past the
newest base they had to read. What bench-count measures on THE BAR's own Store (trie hashes per
required hash, verifies per step) is not counted here: a second instrument of one quantity. -/
def rowbarCounts (r : Row) (res : Loopback.Result) : Except String (List (String × Nat × Nat)) := do
  let writes := res.times.toList.foldl (fun n t => match r.lines[t.line]? with
    | some { act := .cmd (v :: _), .. } => if v = "read" then n else n + t.ns.length
    | _ => n) 0
  if writes = 0 then throw "bar: no write command ran (a ratio over nothing)"
  let (read, need) := res.reopenReads.foldl (fun (a, b) (x, y, _) => (a + x, b + y)) (0, 0)
  if need = 0 then
    throw s!"bar: no reopen with bytes past a base was measured (a ratio over nothing; the measured reopens' (read, past-base) bytes: {res.reopenReads.map fun (x, y, _) => (x, y)})"
  pure [("frames-per-write", res.frames, writes), ("steps-per-write", res.steps, writes),
    ("reopen-bytes-per-byte-past-base", read, need)]

/-- Each rowbar plant's ratio on THE BAR's workload, stated: a tooth only while it bites by exactly
this much, above the honest ratio. -/
def rowbarStated : List (Mutation × String × String) :=
  [(.twiceEach, "frames-per-write", "21.871"), (.twiceEach, "steps-per-write", "1.977"),
   -- 6.069 since KERNEL-68 (a Turn record 40 bytes larger; THE BAR's measured tail is 20 invokes,
   -- not 23, to stay under the seal floor): the stale base reads the whole segment over a shorter tail;
   -- 6.070 since LANG-89 (a package is one node larger: the grades child)
   -- 6.083 since KERNEL-70 (the occasion sum prints retire, every Std law carries a retire arm); 6.119 since
   -- KERNEL-76 (Req.caller: every package carries the request type in its text, the base grew)
   -- 6.120 since LANG-93 (the three-byte empty claims section, in the ROM cell and the signed install event)
   (.staleBase, "reopen-bytes-per-byte-past-base", "6.120")]

/-- THE BAR under each rowbar plant: its counts must move to their stated values, above the honest
ones, and the mutation must have happened (`staleBase`: a measured reopen was handed an older base). -/
def rowbarPlants {D : Type} [Ord D] [DecidableEq D] (R : Params D) (r : Row) (ls : List Line)
    (times : Option Nat) (honest : List (String × Nat × Nat)) : IO (Option String) := do
  for m in [Mutation.twiceEach, .staleBase] do
    let p ← match ← runMembers R (some m) ls times with
      | .error e => return some s!"bar: plant {repr m}: {e}"
      | .ok p => pure p
    if m = .staleBase && !p.reopenReads.any (·.2.2) then
      return some s!"bar: plant {repr m} did not happen: no measured reopen was handed an older base"
    let counts ← match rowbarCounts r p with
      | .error e => return some s!"bar: plant {repr m}: {e}"
      | .ok c => pure c
    for (pm, metric, stated) in rowbarStated do
      if pm ≠ m then continue
      let some (_, n, d) := counts.find? (·.1 = metric) | return some s!"bar: plant {repr m}: no {metric}"
      let some (_, hn, hd) := honest.find? (·.1 = metric) | return some s!"bar: no honest {metric}"
      IO.println s!"PLANT {repr m} {metric} {ratio n d}"
      if ratio n d ≠ stated then return some s!"bar: plant {repr m} {metric} MOVED {ratio n d}≠{stated}"
      if n * hd ≤ hn * d then
        return some s!"bar: plant {repr m} {metric} BLIND: {ratio n d} is not above {ratio hn hd}"
  return none

/-- Nanoseconds as milliseconds with three decimals. -/
def ms (ns : Nat) : String :=
  let f := toString ((ns / 1000) % 1000)
  s!"{ns / 1000000}.{"".pushn '0' (3 - f.length)}{f}"

/-- The row's liveness timings (`LIVE`: toy parameters, in process; never THE BAR, which is
`scripts/bar.sh` over real processes) and its WASTE lines; an error if the invokes went unmeasured (a WASTE line
over no calls would read as zero cost and pass the ratchet: a fail-open). -/
def barLines (r : Row) (res : Loopback.Result) : IO (Option String) := do
  let timed := res.times.toList.filter fun t => (r.lines[t.line]?.bind (·.withinMs)).isSome
  let writes := (timed.filter fun t => match r.lines[t.line]? with
    | some { act := .cmd _, .. } => true | _ => false).flatMap (·.ns)
  IO.println s!"LIVE write-n {writes.length}"
  IO.println s!"LIVE write-p99-ms {ms (p99 writes)}"
  for ns in res.reopenNs do
    IO.println s!"LIVE reopen-ms {ms ns}"
  IO.println s!"LIVE load {← load}"
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
  match rowbarCounts r res with
  | .error e => return some e
  | .ok cs => for (metric, n, d) in cs do IO.println s!"WASTE rowbar {metric} {ratio n d}"
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

/-- Drive one row under the parameters `R`. `measures`: print THE BAR row's LIVE and WASTE lines
(the toy run's; the deployed run prints none, so a WASTE measure is collected once). -/
def drive {D : Type} [Ord D] [DecidableEq D] (R : Params D) (r : Row) (times : Option Nat)
    (control : Bool := false) (measures : Bool := true) : IO Ran :=
  if let some why := r.blockedOn then pure (.pending s!"blocked on {why}") else
  match r.drive with
  | .exe name args _ => runExe name args
  | .members ls => do
      match ← runMembers R none ls times r.pageBudget with
      | .error e => pure (.broken e)
      | .ok res =>
          IO.println s!"COST {r.name} frames {res.frames} steps {res.steps}"
          if r.name = "bar" && measures then
            if let some e ← barLines r res then return .broken e
            match rowbarCounts r res with
            | .error e => return .broken e
            | .ok cs => if let some e ← rowbarPlants R r ls times cs then return .broken e
          let t := String.intercalate "\n" res.log.toList
          match judge r res.observed, r.plant with
          | .pass, .caught m line got =>
              match ← runMembers R (some m) ls times r.pageBudget with
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
def runAll {D : Type} [Ord D] [DecidableEq D] (R : Params D) (selected : List Row) (times : Option Nat)
    (verbose : Bool) (control : Bool := false) (measures : Bool := true) : IO UInt32 := do
  let mut failed := 0
  let mut pending := 0
  let mut hung := 0
  for r in selected do
    -- Expand the bar's total once: --times N still means N births and N invokes,
    -- rather than N executions of each side of its explicit checkpoint.
    let (r, times) := if r.name == "bar" then (barWithCount (times.getD 64), none) else (r, times)
    match ← drive R r times control measures with
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
              | .internal _ => ""
              | .measured w => s!" (no plant; measured before its fix: {w})"}"
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

/-- The deployed run's parameter check, before any row: the deployed parameters measure the deployed
widths, and the toy's are refused by name (the plant: a check that passed the toy would not be
reading the widths). An error names what is wrong. -/
def checkDeployed : Except String Unit := do
  match Params.atDeployed Params.deployed with
  | .error e => throw s!"the deployed parameters are not at the deployed widths: {e}"
  | .ok () => pure ()
  match Params.atDeployed Params.toy with
  | .ok () => throw "plant toyWidths BLIND: the toy parameters pass the deployed-width check"
  | .error e =>
    if (e.splitOn " ").head? ≠ some "digest" then throw s!"plant toyWidths MOVED: refused {e}, not digest"

/-- `rows [--deployed] [-v] [--times N] [--harness-control] [ROW…]`. `--harness-control` (GATES-15)
reads every plant at a line its row does not have, so every planted row must read
`FAIL … BLIND … (harness-control)`: the known-red control gates/runs.py runs before reading a
verdict. `--deployed` runs at the deployed parameters (above). -/
def main (args : List String) : IO UInt32 := do
  let control := args.contains "--harness-control"
  let deployed := args.contains "--deployed"
  let args := args.filter fun a => a != "--harness-control" && a != "--deployed"
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
  let selected := if args.isEmpty then rows else rows.filter fun r => args.contains r.name
  if deployed then
    if let .error e := checkDeployed then
      IO.println s!"PARAMS {e}"
      IO.println "FAIL 1 of 1"
      return 1
    IO.println s!"PARAMS {Params.deployed.name}: {repr Params.deployed.widths}"
    IO.println s!"PLANT toyWidths caught: {match Params.atDeployed Params.toy with | .error e => e | .ok () => "-"}"
    -- the Lean-internal rows run their own executables, whose parameters are their own
    runAll Params.deployed (selected.filter fun r => r.drive matches .members _) times verbose control false
  else
    runAll Params.toy selected times verbose control

end Nanodregg.Protocol.Rows
