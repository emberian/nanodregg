/-
# Kernel.Receive.Audit — the follower re-derives every Turn from its event

`World.fold` trusts the writer's derivations; `audit` does not. For each logged Turn it decodes
the event (the signed call), runs `receive` on its own World, and requires the very same Turn
before admitting it. A disagreement is refused naming the index (`Kernel.Proofs.Audit`).
-/
import Kernel.Receive.Derive

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

/-- Why an audited log is refused at an index. -/
inductive AuditFault (D : Type)
  | undecodable
  | refused (r : Refusal D)
  /-- the writer logged a Turn other than the one its event derives -/
  | mismatch
  | rejected (r : Reject D)
  deriving DecidableEq, Repr

variable {D : Type} [Ord D] [DecidableEq D]

def auditStep (X : Ctx D) (w : World D) (t : Turn D) : Except (AuditFault D) (World D) :=
  match X.decodeCall t.event with
  | none => .error .undecodable
  | some c =>
      match receive X w c with
      | .error r => .error (.refused r)
      | .ok t' =>
          if t' = t then
            match World.admit X.env w t with
            | .ok w' => .ok w'
            | .error r => .error (.rejected r)
          else .error .mismatch

def audit (X : Ctx D) (w : World D) : List (Turn D) → Except (Nat × AuditFault D) (World D)
  | [] => .ok w
  | t :: rest =>
      match auditStep X w t with
      | .ok w' =>
          match audit X w' rest with
          | .ok w'' => .ok w''
          | .error (i, f) => .error (i + 1, f)
      | .error f => .error (0, f)

/-- A log every Turn of which is exactly what `receive` derives from its own event, on the World
before it: a log in which the writer decided nothing. -/
def Honest (X : Ctx D) : World D → List (Turn D) → Prop
  | _, [] => True
  | w, t :: rest => ∃ c, X.decodeCall t.event = some c ∧ receive X w c = .ok t ∧
      ∀ w', World.admit X.env w t = .ok w' → Honest X w' rest

end Nanodregg.Kernel.Receive
