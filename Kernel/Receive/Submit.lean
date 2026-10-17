/-
# Kernel.Receive.Submit — the Host's whole decision for one signed call

A retry is recognised before anything is derived: the transaction id is the digest of the signed
call, so a call already in the journal is `replayed` at its height whatever the World is now
(a retried rotation must not be re-judged against the key it already rotated). Otherwise:
derive (`receive`), then admit (`World.admit`). The Host commits exactly the returned World.
-/
import Kernel.Receive.Derive

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

/-- Why a submission did not commit: the receive layer refused, or the kernel rejected. -/
inductive Verdict (D : Type)
  | refused (r : Refusal D)
  | rejected (r : Reject D)
  deriving DecidableEq, Repr

variable {D : Type} [Ord D] [DecidableEq D]

def submit (X : Ctx D) (w : World D) (c : Call D) : Except (Verdict D) (Turn D × World D) :=
  match w.journalAt X.env (txIdOf X c) with
  | some (h, _) => .error (.rejected (.replayed h))
  | none =>
      match receive X w c with
      | .error r => .error (.refused r)
      | .ok t =>
          match World.admit X.env w t with
          | .error r => .error (.rejected r)
          | .ok w' => .ok (t, w')

end Nanodregg.Kernel.Receive
