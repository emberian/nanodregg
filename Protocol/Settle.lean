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
import Protocol.Receipt

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

/-! ## The member's settlement (PROTOCOL-46)

The Host's reply HINTS (`verdictReply` above drives the attempt loop); the member's own follow
SETTLES. Follow catches up, builds the receipt for the call from its own World (`Receipt.build`)
and decides it here:

* `committed h td`: the journal holds it; final;
* `refused code`: the refusals hold its recorded refusal, and the call's window closes before the
  record can be pruned (`validUntil ≤ h + 2 · windowMax`); final. Otherwise the answer is `open`,
  the safe side. On a World follow absorbed from a genesis that `open` is dead: the kernel records
  only a window no wider than `windowMax` (`checkRefusedBounds`, 8ad3982), and follow takes a
  refusal only as its own `judge` records it, so the member's own call refused at `h` closes by
  `h + windowMax`, unless follow's own log carries a different call under the member's id (a
  hash collision, or a call outside the codec's domain) (`settle_refused_absorbed`). A World carried from a base keeps only
  `(h, code)` per refusal, so there this check is what keeps the arm safe, and it stays: it also
  keeps `settle_final_never_admits` free of any absorption premise;
* `expired`: absent, and the head is at or past the call's `validUntil`; final (no later World
  admits it: the kernel's window);
* `refused stale` (KERNEL-54): absent while the window is live, and follow's own fold says the
  member's call is stale BEHIND (`behind`, `Command.staleBehind`): the member's own call, planned on
  a World of follow's fold (its `notBefore` at most follow's height), whose pins follow's World now
  refuses `stale`. A pin observed on the fold and stale now is stale at every World the fold reaches
  (`Kernel.stale_behind_forever`), so the call never lands; final without a record (the writer
  declines a stale, never records it). AHEAD (a planning height follow has not reached) or a call
  follow did not plan is not `behind`: it settles `open`;
* `open`: absent while the window is live. NOT final: whoever holds the signed bytes (the Host,
  any relay) may still land them;
* `forgotten`: absent past `journalForgets`: absence no longer says the call did not land.

Theorems: `Protocol.Proofs.Settle` (`settle_committed`, `settle_final_never_admits`,
`settle_open_not_final`, `settle_refused_absorbed`, `settle_refused_final`, `absorbed_windowedIn`,
`settle_final_reached`) and
`Protocol.Proofs.Receipt` (`check_build`, `check_build_reached`).
-/

/-- What follow says happened to a call. -/
inductive Verdict (D : Type)
  | committed (height : Nat) (turn : D)
  | refused (code : Nat)
  | expired
  | «open»
  | forgotten
  deriving DecidableEq

/-- THE settlement: a receipt's answer at a head of height `height`, for a call valid until
`validUntil`; `forgets` is `journalForgets height notBefore`; `behind` is follow's own fold saying
the call is stale BEHIND (`Command.staleBehind`, KERNEL-54; a holder of a head but no World passes
`false`). -/
def ofReceipt (forgets behind : Bool) (height validUntil : Nat) : Receipt.Answer D → Verdict D
  | .committed h td => .committed h td
  | .refused h code _ => if validUntil ≤ h + 2 * Kernel.Bounds.windowMax then .refused code else .open
  | .absent =>
      if forgets then .forgotten
      else if validUntil ≤ height then .expired
      else if behind then .refused staleCode
      else .open

/-- The `settle` line follow prints (`settle_seen` reads its first word). -/
def Verdict.text (dbytes : D → ByteArray) : Verdict D → String
  | .committed h td => s!"committed {h} {Text.toHex (dbytes td)}"
  | .refused code => s!"refused {code}"
  | .expired => "expired"
  | .open => "open"
  | .forgotten => "forgotten"

end Nanodregg.Protocol.Settle
