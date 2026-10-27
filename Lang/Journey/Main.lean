import Lang.Journey.ContextualCycle
import Lang.Journey.ContextualWire
import Lang.Journey.Gen
import Lang.Journey.Head
import Lang.Journey.Offer
import Lang.Journey.OfferEscrow
import Lang.Journey.Claims
import Lang.Journey.Doc
import Lang.Journey.ContextualLaw
import Lang.Journey.Inbox
import Lang.Journey.Effect
import Lang.Journey.Retire
import Lang.Journey.Holds

open Nanodregg.Lang.Journey

/-- `lang-journey [--harness-control | --hole-omitted-blocker-pin-admits | --contextual |
--contextual-checks | --write DIR]`. The sessions are the registry's (`Journey.register`: one line at
the end of each session module); this file only imports them, and adds no line per session. -/
def main (args : List String) : IO UInt32 := do
  if let ["--write", d] := args then return ← Doc.write d
  runAll args
