/-
# Hosting.Sim.Run — `hosting-sim`: the grain journey (`Hosting.Sim.Journey`) and the allowance
journey (`Hosting.Sim.Allowance`), each with its text gate, ending `ALL PASS` or RED
-/
import Hosting.Sim.Journey
import Hosting.Sim.Allowance

namespace Nanodregg.Hosting.Sim

def runAll (args : List String) : IO UInt32 := do
  if args == ["--write-text"] then
    let some t := lifecycle.bind Lang.Print.package | IO.eprintln "no text"; return 1
    IO.FS.createDirAll (textPath.parent.getD ".")
    IO.FS.writeFile textPath t
    IO.println s!"wrote {textPath}"
    unless ← Allowance.writeText do IO.eprintln "no allowance text"; return 1
    return 0
  -- standing runs every `*-sim` as `EXE SEED`. These journeys have no generator, so the seed selects
  -- nothing; it is accepted (a natural, said so on the first line) and anything else is refused.
  match args with
  | [] => pure ()
  | [seed] =>
    match seed.toNat? with
    | some n => IO.println s!"seed {n}: the hosting journey is deterministic; the seed selects nothing"
    | none => IO.eprintln s!"usage: hosting-sim [SEED | --write-text] (got {seed})"; return 2
  | _ => IO.eprintln "usage: hosting-sim [SEED | --write-text]"; return 2
  let (l0, ok0) ← textLine
  IO.println s!"{if ok0 then "ok  " else "FAIL"} {l0}"
  let (la, oka) ← Allowance.textLine
  IO.println s!"{if oka then "ok  " else "FAIL"} {la}"
  let some lc := lifecycle
    | IO.println "FAIL the grain package is not built (Std refused its inputs)"; return 1
  let runs := [journey .none lc, journey .skipJudge lc, Allowance.journey]
  for r in runs do for l in r.log do IO.println l
  let bad := runs.foldl (· + ·.bad) ((if ok0 then 0 else 1) + (if oka then 0 else 1))
  IO.println (if bad = 0 then "ALL PASS" else s!"hosting-sim: RED ({bad})")
  return if bad = 0 then 0 else 1

end Nanodregg.Hosting.Sim
