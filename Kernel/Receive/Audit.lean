/-
# Kernel.Receive.Audit — the follower re-derives every Turn from its event

`World.fold` trusts the writer's derivations; `audit` does not. For each logged Turn it decodes
the event (the signed call), runs `receive` on its own World, and requires the very same Turn
(`rederive`, PROTOCOL-4) before admitting it. A disagreement is refused by name at its index
(`Kernel.Proofs.Audit`): `undecodableEvent`, `eventMismatch`, the receiver's own refusal, or the
kernel's rejection, in the one `Verdict` shape `submit` uses.
-/
import Kernel.Receive.Submit

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- The logged Turn `t` is exactly what its own event derives on `w`. -/
def rederive (X : Ctx D) (w : World D) (t : Turn D) : Except (Refusal D) Unit :=
  match X.decodeCall t.event with
  | none => .error .undecodableEvent
  | some c =>
      match receive X w c with
      | .error r => .error r
      | .ok t' => if t' = t then .ok () else .error .eventMismatch

def auditStep (X : Ctx D) (w : World D) (t : Turn D) : Except (Verdict D) (World D) :=
  match rederive X w t with
  | .error r => .error (.refused r)
  | .ok () =>
      match World.admit X.env w t with
      | .ok w' => .ok w'
      | .error r => .error (.rejected r)

def audit (X : Ctx D) (w : World D) : List (Turn D) → Except (Nat × Verdict D) (World D)
  | [] => .ok w
  | t :: rest =>
      match auditStep X w t with
      | .ok w' =>
          match audit X w' rest with
          | .ok w'' => .ok w''
          | .error (i, f) => .error (i + 1, f)
      | .error f => .error (0, f)

end Nanodregg.Kernel.Receive
