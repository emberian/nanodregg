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

/-- Who re-judges a logged refusal of call `c` (KERNEL-60): `judge` for a judged refusal (no cancel
signature), `cancel` with the record's signature for a cancel. -/
def recordedBy (X : Ctx D) (w : World D) (c : Call D) (r : Refused D) : Outcome D :=
  if r.cancel.size = 0 then judge X w c else cancel X w c r.cancel

/-- The name a logged refusal its re-judge does not reproduce is refused with: `eventMismatch` for a
judged refusal, `cancelForged` for a cancel. -/
def forgedName (r : Refused D) : Refusal D :=
  if r.cancel.size = 0 then .eventMismatch else .cancelForged

/-- A logged refusal is exactly what its own event is judged to on `w` (KERNEL-44): the call decodes,
`judge` records it, and records this very refusal (its id, signer, window and code). A Host that
invents a refusal or records the wrong code is caught here exactly as one that invents a Turn. A
refusal the Host answered but never logged is no step at all, so no audit sees it; what binds the
Host to it is a proof of the record against a head it served (open: a refusal inclusion theorem). A recorded stale is refused by name before anything is decoded
(`staleRecorded`, KERNEL-54: `judge` never records one). A record carrying a cancel signature is
re-judged as a cancel (KERNEL-60): `cancel` on this World must record exactly it, or the log is
refused `cancelForged` (the signature does not verify under the member's key here, or the record is
not the cancel of its own event). -/
def auditRefusal (X : Ctx D) (w : World D) (r : Refused D) : Except (Verdict D) (World D) :=
  if r.code = staleCode then .error (.refused .staleRecorded) else
  match X.decodeCall r.event with
  | none => .error (.refused .undecodableEvent)
  | some c =>
      match recordedBy X w c r with
      | .recorded _ r' w' => if r' = r then .ok w' else .error (.refused (forgedName r))
      | _ => .error (.refused (forgedName r))

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
