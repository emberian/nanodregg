import Host.Sim.Run
import Host.Sim.Join

def main (args : List String) : IO UInt32 := do
  let rc ← if args == ["--join-only"] then pure 0 else Nanodregg.Host.Sim.run args
  let checks ← Nanodregg.Host.Sim.Join.checks
  for (name, ok) in checks do
    IO.println s!"{if ok then "PASS" else "FAIL"} {name}"
  let ok := rc == 0 && checks.all Prod.snd
  IO.println (if ok then "ALL PASS" else "FAILED")
  return if ok then 0 else 1
