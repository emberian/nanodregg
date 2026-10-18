/-
# Protocol.Settle — which reply to a submit is final (PROTOCOL-41)

The Host judges a signed call once (`Receive.judge`): admitted, refused and RECORDED, or refused and
not recorded (`declined`). The attempt store decides by the reply's status byte (PROTOCOL-17), so the
status must say whether the verdict is final. This function is the one rule; `Host.Serve` calls it.

* admitted: no refusal reply (the Host answers `ok` with the receipt);
* recorded now: `refused NAME`, final (`Kernel.Receive.judge_recorded_final`);
* the call's transaction id already holds a recorded refusal: `refused NAME` with the RECORDED name
  (`codeName`), final; this is the resubmit and the A→B→A case, answered without re-deriving;
* the call's window has passed (`validUntil ≤ height`): `refused NAME`, final by height (no later
  height admits it);
* otherwise `declined NAME`, NOT final: an unauthenticated code, an early `outsideWindow`, or
  `refusalBudget`. Nothing is recorded, and the same bytes may still be admitted later.

Finality is read from the World (the record, the height), not from the verdict's name. A resubmit of
a recorded call leaves `judge` as `declined (refusedFinal code)`, and a late call can be refused by any
name. Theorems: `Protocol.Proofs.Settle` (`final_iff_recorded`, the rule restated as a spec;
`final_recorded`, which carries finality to the kernel's record; `declined_open`).
-/
import Kernel.Receive.Submit
import Protocol.Table

namespace Nanodregg.Protocol.Settle

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- The reply a refused submit travels as, or `none` when it was admitted. -/
def verdictReply (X : Ctx D) (w : World D) (c : Call D) : Outcome D → Option (Status × String)
  | .admitted _ _ => none
  | .recorded v _ _ => some (.refused, v.name)
  | .declined v =>
      match refusedAnswer X w c with
      | some code => some (.refused, (codeName code).getD v.name)
      | none =>
          if c.unsigned.validUntil ≤ w.height then some (.refused, v.name)
          else some (.declined, v.name)

/-- The World the Host keeps after the outcome. -/
def keptWorld (w : World D) : Outcome D → World D
  | .admitted _ w' => w'
  | .recorded _ _ w' => w'
  | .declined _ => w

def recordedNow : Outcome D → Bool
  | .recorded .. => true
  | _ => false

end Nanodregg.Protocol.Settle
