import Lang.Journey.ContextualCycle
import Lang.Journey.ContextualWire
import Lang.Journey.Head
import Lang.Journey.Offer
import Lang.Journey.OfferEscrow
import Lang.Journey.Claims
import Lang.Journey.Doc

open Nanodregg.Lang.Journey

def main (args : List String) : IO UInt32 := do
  if args == ["--contextual-checks"] then
    let rows := Contextual.boundaryRows ++ Contextual.gateRows ++ Contextual.wireRows
    for (name, ok) in rows do IO.println s!"{if ok then "ok  " else "FAIL"} LP {name}"
    let bad := rows.filter (fun row => !row.2) |>.length
    IO.println s!"contextual-checks: {if bad = 0 then "GREEN" else s!"RED ({bad})"}"
    return if bad = 0 then 0 else 1
  if args == ["--contextual"] then
    let runs := [contextualSession, cycleSession, p8Session, holeObservationJourney true]
    for r in runs do
      for line in r.log do IO.println line
    let bad := runs.foldl (fun n r => n + r.bad) 0
    IO.println s!"contextual-journey: {if bad = 0 then "GREEN" else s!"RED ({bad})"}"
    return if bad = 0 then 0 else 1
  if let ["--write", d] := args then return ← Doc.write d
  let accept ← try IO.FS.readFile acceptSourcePath catch _ => pure ""
  let timelock ← try IO.FS.readFile timelockSourcePath catch _ => pure ""
  let shipped ← Doc.readShipped
  runAll args [offerSession, offerEscrowSession, headSession accept timelock, Doc.session shipped, claimSession]
