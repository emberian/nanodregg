/-
# Protocol.Rows.Run — the row runner (`lake exe rows [NAME…]`, which `rows/run` is)

Runs every row of `Protocol.rows` (or the named ones) and prints one line per row,
`ROW <name> PASS`, `ROW <name> FAIL <why>` or `ROW <name> PENDING <why>`, then a last line:
`ALL PASS` (exit 0), `FAIL <n> of <m>` (exit 1) or `INCOMPLETE <n> pending` (exit 3; no row failed,
some have no driver yet). An unknown row name is refused before anything runs (exit 2).

The runner moves processes and bytes; `Protocol.Rows.Judge.judge` decides. An `exe` row is
`lake exe NAME ARGS` with stdin closed, waited for by polling under a deadline (killed past it;
the runner holds the child's handle, so the kill names exactly the process it started). A
`members` row is PENDING until its driver exists: in-process through `Protocol.Command` with a
loopback client, then over the sockets through `nd` once `host serve`/`host follow` exist.
-/
import Protocol.Rows.Judge

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

def drive (r : Row) : IO Ran :=
  match r.drive with
  | .exe name args _ => runExe name args
  | .members _ => pure (.pending "no member driver yet (Protocol.Command loopback; then nd over host serve/follow)")

/-- The last lines of a transcript, indented, for a failing row. -/
def tail (t : String) : String :=
  let ls := (t.splitOn "\n").filter (· ≠ "")
  String.intercalate "\n" ((ls.drop (ls.length - 20)).map ("  | " ++ ·))

/-- Run the rows; the exit code is the runner's verdict. -/
def runAll (selected : List Row) : IO UInt32 := do
  let mut failed := 0
  let mut pending := 0
  for r in selected do
    match ← drive r with
    | .pending why =>
        pending := pending + 1
        IO.println s!"ROW {r.name} PENDING {why}"
    | .broken why =>
        failed := failed + 1
        IO.println s!"ROW {r.name} FAIL {why}"
    | .observed o t =>
        match judge r o with
        | .pass => IO.println s!"ROW {r.name} PASS"
        | .fail why =>
            failed := failed + 1
            IO.println s!"ROW {r.name} FAIL {why}"
            IO.println (tail t)
  if failed > 0 then
    IO.println s!"FAIL {failed} of {selected.length}"; pure 1
  else if pending > 0 then
    IO.println s!"INCOMPLETE {pending} pending"; pure 3
  else
    IO.println "ALL PASS"; pure 0

def main (args : List String) : IO UInt32 := do
  let unknown := args.filter fun a => !rows.any (·.name == a)
  if !unknown.isEmpty then
    IO.eprintln s!"rows: no such row: {String.intercalate " " unknown}"
    return 2
  runAll (if args.isEmpty then rows else rows.filter fun r => args.contains r.name)

end Nanodregg.Protocol.Rows
