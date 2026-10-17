/-
# Protocol.Proofs.Envelope — the read gate, and its refusal names
-/
import Protocol.Envelope

namespace Nanodregg.Protocol

open Nanodregg.Kernel Nanodregg.Kernel.Receive

theorem ReadRefusal.name_injective : ∀ a b : ReadRefusal, a.name = b.name → a = b := by
  intro a b; cases a <;> cases b <;> simp [ReadRefusal.name]

variable {D : Type} [Ord D] [DecidableEq D]

/-- The Host serves a read exactly when the member's current key signed the envelope, it has not
expired, and the member's follow grant is live to a root. -/
theorem Envelope.check_ok_iff (X : Ctx D) (w : World D) (e : Envelope D) :
    Envelope.check X w e = .ok () ↔
      currentKey w e.member = some e.key ∧
      X.verify e.key (Envelope.message X e.member e.grant e.start e.validUntil) e.signature = true ∧
      w.height ≤ e.validUntil ∧ mayFollow X w e.member e.grant = true := by
  simp only [Envelope.check, bind, Except.bind, req]
  by_cases h1 : currentKey w e.member = some e.key <;>
  by_cases h2 : X.verify e.key (Envelope.message X e.member e.grant e.start e.validUntil) e.signature = true <;>
  by_cases h3 : w.height ≤ e.validUntil <;>
  by_cases h4 : mayFollow X w e.member e.grant = true <;>
  simp [h1, h2, h3, h4]

end Nanodregg.Protocol
