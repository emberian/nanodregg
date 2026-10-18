/-
# Kernel.Receive.Audit — the follower re-derives every step from its event

`World.fold` trusts the writer's derivations; `audit` does not. For each logged Turn it decodes
the event (the signed call), runs `receive` on its own World, and requires the very same Turn
(`rederive`, PROTOCOL-4) before admitting it. A disagreement is refused by name at its index
(`Kernel.Proofs.Audit`): `undecodableEvent`, `eventMismatch`, the receiver's own refusal, or the
kernel's rejection, in the one `Verdict` shape `submit` uses. For each recorded refusal it decodes
the call and requires `judge` to record the same refusal (`auditRefusal`).
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

def auditTurn (X : Ctx D) (w : World D) (t : Turn D) : Except (Verdict D) (World D) :=
  match rederive X w t with
  | .error r => .error (.refused r)
  | .ok () =>
      match World.admit X.env w t with
      | .ok w' => .ok w'
      | .error r => .error (.rejected r)

/-- A logged refusal is exactly what its own event is judged to on `w` (KERNEL-44): the call decodes,
`judge` records it, and records this very refusal (its id, signer, window and code). A Host that
invents a refusal or records the wrong code is caught here exactly as one that invents a Turn. A
refusal the Host answered but never logged is no step at all, so no audit sees it; what binds the
Host to it is a proof of the record against a head it served (open: a refusal inclusion theorem). -/
def auditRefusal (X : Ctx D) (w : World D) (r : Refused D) : Except (Verdict D) (World D) :=
  match X.decodeCall r.event with
  | none => .error (.refused .undecodableEvent)
  | some c =>
      match judge X w c with
      | .recorded _ r' w' => if r' = r then .ok w' else .error (.refused .eventMismatch)
      | _ => .error (.refused .eventMismatch)

def auditStep (X : Ctx D) (w : World D) : Step D → Except (Verdict D) (World D)
  | .turn t => auditTurn X w t
  | .refusal r => auditRefusal X w r

def audit (X : Ctx D) (w : World D) : List (Step D) → Except (Nat × Verdict D) (World D)
  | [] => .ok w
  | t :: rest =>
      match auditStep X w t with
      | .ok w' =>
          match audit X w' rest with
          | .ok w'' => .ok w''
          | .error (i, f) => .error (i + 1, f)
      | .error f => .error (0, f)

end Nanodregg.Kernel.Receive
