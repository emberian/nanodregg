import Protocol.Rows.Run

/-!
# Emit.Traces — the member rows' conversations with nd, as files Rust replays (DESIGN-QA Q5)

`emit-traces client/tests/traces/ROW.trace` runs the member row ROW at the DEPLOYED parameters
(`Rows.Params.deployed`: Ed25519 custody, so nd's own custody signs the same bytes) with the trace
recording (`Protocol.Rows.Loopback`'s `tracing`) and writes what it recorded. The row must pass its
judge first: a trace is the expected behaviour only of a run the rows call correct.
`emit-traces --check PATH` exits 1 if PATH differs (gates/generated.tsv holds one line per trace).

The file, one line each (hex fields, `-` for empty bytes):

* `custody NAME CURRENT NEXT PENDING`: the actor's key-file seeds of generations 0, 1 and 2;
* `run N NAME ARG…`: nd run N, by actor NAME, handed ARG… (each in hex);
* `follow N OP REQUEST STATUS REPLY`: run N sent follow `OP ‖ REQUEST` and read `STATUS ‖ REPLY`;
* `host N OP REQUEST STATUS REPLY` or `host N OP REQUEST lost`: the same on the Host's socket, or no
  reply read at all;
* `end N EXIT STDOUT STDERR`, or `end N error`: what run N ended with.

Lines of different runs interleave only where one actor's run happens inside another's (a race).
-/

namespace Nanodregg.Emit.Traces

open Nanodregg.Protocol Nanodregg.Protocol.Rows

/-- The trace file of member row `name`, or why there is none. -/
def text (name : String) : IO (Except String String) := do
  let some r := rows.find? (·.name == name) | return .error s!"no such row: {name}"
  let .members ls := r.drive | return .error s!"{name} is not a member row"
  let res ← Loopback.run Params.deployed none ls none r.pageBudget (tracing := true)
  match judge r res.observed with
  | .pass => pure (.ok (String.join ((#[s!"# row {name} at the deployed parameters; regenerate: lake exe emit-traces PATH"] ++
      res.trace).toList.map (· ++ "\n"))))
  | .fail why => pure (.error s!"row {name} does not pass: {why}")
  | .hang why => pure (.error s!"row {name} hangs: {why}")

/-- The row a trace path names: its file name without `.trace`. -/
def rowOf (path : String) : String :=
  let base := ((path.splitOn "/").getLast?.getD path)
  (base.dropSuffix? ".trace").map (·.toString) |>.getD base

/-- `emit-traces PATH` writes the trace; `emit-traces --check PATH` exits 1 if PATH differs. -/
def run (args : List String) : IO UInt32 := do
  let (check, path) ← match args with
    | [p] => pure (false, p)
    | ["--check", p] => pure (true, p)
    | _ => IO.eprintln "usage: emit-traces [--check] client/tests/traces/ROW.trace"; return 2
  match ← text (rowOf path) with
  | .error e => IO.eprintln s!"emit-traces: {e}"; return 2
  | .ok t =>
    if !check then IO.FS.writeFile path t; return 0
    if (← IO.FS.readFile path) == t then return 0
    IO.eprintln s!"emit-traces: {path} differs from what row {rowOf path} does; regenerate it"
    return 1

end Nanodregg.Emit.Traces
