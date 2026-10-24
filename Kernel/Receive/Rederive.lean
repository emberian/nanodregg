/-
# Kernel.Receive.Rederive — the follower re-derives every step from its event

`World.fold` trusts the writer's derivations; a follower does not. A log page carries each step's
EVENT (`Step.event`: the signed call, and a cancel's signature), never the writer's record, and the
follower re-derives the step from it by the Host's own decision functions (`rederive`, PROTOCOL-4):
a Turn by `submit` (receive, then admit), a judged refusal by `judge`, which must record it, a
cancel by `cancel` under the event's signature, which must record it. This is the ONE re-deriver:
`host follow` runs it on every page event (`Protocol.Command.absorbStep`), and every runtime
auditor that holds the writer's steps (kernel-sim, the journeys, the benches) runs it on each
step's event and requires the very step (`rederiveStep`, `rederiveLog`). What it decides of an
honest folded log, both ways, is `Kernel.Proofs.Rederive` (`rederiveLog_iff`).

A step that does not re-derive is refused in the one `Verdict` shape `submit` uses: the kernel's
rejection of a derived Turn by its own name (a writer that admits a call it recorded refused is
`refusedFinal`); a well-formed cancel `cancel` does not record by `cancelForged`; anything else
(an event that does not decode, a Turn the receiver refuses, a refusal `judge` does not record, a
step other than the one its event derives) is `eventMismatch`.

`recordedBy` is `Honest`'s re-judge of a logged refusal (`Kernel.Proofs.Rederive`): `judge` or
`cancel`, by the step's event. It decides nothing at runtime.
-/
import Kernel.Receive.Submit

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- Who re-judges a logged refusal of call `c` (KERNEL-60), by its event (`Step.event`): `cancel`
with the record's signature for a cancel, `judge` otherwise. -/
def recordedBy (X : Ctx D) (w : World D) (c : Call D) (r : Refused D) : Outcome D :=
  match (Step.refusal r).event with
  | .cancel sig _ => cancel X w c sig
  | _ => judge X w c

/-- **The re-derivation of one logged event** on the follower's World `w`: the step it derives and
the World that step reaches, or the name it is refused by. -/
def rederive (X : Ctx D) (w : World D) : Event → Except (Verdict D) (Step D × World D)
  | .turn b =>
      match X.decodeCall b with
      | none => .error (.refused .eventMismatch)
      | some c =>
          match submit X w c with
          | .ok (t, w') => .ok (.turn t, w')
          | .error (.rejected r) => .error (.rejected r)
          | .error (.refused _) => .error (.refused .eventMismatch)
  | .refusal b =>
      match X.decodeCall b with
      | none => .error (.refused .eventMismatch)
      | some c =>
          match judge X w c with
          | .recorded _ r w' => .ok (.refusal r, w')
          | _ => .error (.refused .eventMismatch)
  | .cancel sig b =>
      match X.decodeCall b with
      | none => .error (.refused .eventMismatch)
      | some c =>
          match cancel X w c sig with
          | .recorded _ r w' => .ok (.refusal r, w')
          | _ => .error (.refused .cancelForged)

/-- A logged step `s` is exactly what its own event re-derives on `w` (`rederive` of `s.event`):
the World it reaches, or the name it is refused by (`eventMismatch` when the event derives another
step). What a holder of the writer's steps checks; a follower holds only the events, and its chain
check binds the steps it derived. -/
def rederiveStep (X : Ctx D) (w : World D) (s : Step D) : Except (Verdict D) (World D) :=
  match rederive X w s.event with
  | .ok (s', w') => if s' = s then .ok w' else .error (.refused .eventMismatch)
  | .error v => .error v

/-- `rederiveStep` along a log: the World it reaches, or the first step that does not re-derive, at
its index. -/
def rederiveLog (X : Ctx D) (w : World D) : List (Step D) → Except (Nat × Verdict D) (World D)
  | [] => .ok w
  | s :: rest =>
      match rederiveStep X w s with
      | .ok w' =>
          match rederiveLog X w' rest with
          | .ok w'' => .ok w''
          | .error (i, f) => .error (i + 1, f)
      | .error f => .error (0, f)

end Nanodregg.Kernel.Receive
