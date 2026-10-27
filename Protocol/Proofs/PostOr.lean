/-
# Protocol.Proofs.PostOr — the reply-shape algebra of `postOr` (PROTOCOL-75)

`Command.postOr` applies a page's self-head verdict to the reply the page arm of `step` would give
(`forkedPost` or `forkedCertified` with the page kept, else the reply unchanged). It is `@[irreducible]`, so no proof over
`step` unifies through it; every reply-shape statement (`Proofs.Incoming`, `Proofs.Command`,
`Hosting.Proofs.Socket*`) reads it by `postOr_cases` and the elims here, one per reply constructor a
proof matches: a continuation, a signature request, a host step, a submit, an `ok` end each survive
`postOr` only when no post fired (a refusal carries none of them).
-/
import Protocol.Command.Machine

namespace Nanodregg.Protocol.Command

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- `postOr` read by the proofs: the reply it was given, or a fork verdict (`forkRefused`) of the
first faulty post (`Head.pagePostFault`) or of the writer's certificate (`Head.forkedCertified`). -/
theorem postOr_cases (X : Ctx D) (w : World D) (ts : List (Kernel.Step D × D)) (w' : World D)
    (b : ByteArray) (r : Reply) : postOr X w ts w' b r = r ∨
      (∃ p, Head.pagePostFault X w w' ts = some (.forked, p) ∧
        postOr X w ts w' b r = forkRefused (D := D) (.forkedPost p.steps (X.env.bytes p.member))) ∨
      (∃ p, Head.pagePostFault X w w' ts = some (.beyond, p) ∧
        postOr X w ts w' b r = forkRefused (D := D) (.postBeyondPage p.steps p.pos (X.env.bytes p.member))) ∨
      (∃ s, Head.pagePostFault X w w' ts = none ∧ Head.forkedCertified X w ts b = some s ∧
        postOr X w ts w' b r = forkRefused (D := D) (.forkedCertified s)) ∨
      (∃ why, Head.pagePostFault X w w' ts = none ∧ Head.forkedCertified X w ts b = none ∧
        Head.pageUncertified X w b = some why ∧
        postOr X w ts w' b r = forkRefused (D := D) (.uncertifiedPage why)) := by
  unfold postOr
  cases hf : Head.pagePostFault X w w' ts with
  | some q =>
    obtain ⟨k, p⟩ := q
    cases k
    · exact .inr (.inl ⟨p, rfl, rfl⟩)
    · exact .inr (.inr (.inl ⟨p, rfl, rfl⟩))
  | none =>
    cases hc : Head.forkedCertified X w ts b with
    | none =>
      cases hu : Head.pageUncertified X w b with
      | none => exact .inl rfl
      | some why => exact .inr (.inr (.inr (.inr ⟨why, rfl, rfl, rfl, rfl⟩)))
    | some s => exact .inr (.inr (.inr (.inl ⟨s, rfl, rfl, rfl⟩)))

/-- A reply `postOr` hands back that is not a refused end is the reply it was given. -/
theorem postOr_eq_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)} {w' : World D}
    {b : ByteArray} {r r' : Reply} (h : postOr X w ts w' b r = r')
    (hne : ∀ o e, r' ≠ .done CommandExit.refused.code.toUInt8 o e) : postOr X w ts w' b r = r ∧ r = r' := by
  rcases postOr_cases X w ts w' b r with hp | ⟨_, -, hp⟩ | ⟨_, -, hp⟩ | ⟨_, -, -, hp⟩ | ⟨_, -, -, -, hp⟩
  · exact ⟨hp, hp ▸ h⟩
  all_goals (rw [hp] at h; exact absurd h.symm (hne _ _))

/-- A continuation survives `postOr` only when no post fired (a refusal carries none). -/
theorem postOr_cont_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)} {w' : World D}
    {b : ByteArray} {r : Reply} {k : ByteArray} (hk : (postOr X w ts w' b r).cont = some k) :
    postOr X w ts w' b r = r ∧ r.cont = some k := by
  rcases postOr_cases X w ts w' b r with hp | ⟨_, -, hp⟩ | ⟨_, -, hp⟩ | ⟨_, -, -, hp⟩ | ⟨_, -, -, -, hp⟩
  · rw [hp] at hk; exact ⟨hp, hk⟩
  all_goals (rw [hp] at hk; simp [forkRefused, Reply.cont] at hk)

/-- The same, as a rewrite. -/
theorem postOr_cont_some {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)} {w' : World D}
    {b : ByteArray} {r : Reply} {k : ByteArray} :
    (postOr X w ts w' b r).cont = some k ↔ postOr X w ts w' b r = r ∧ r.cont = some k :=
  ⟨postOr_cont_elim, fun ⟨h, hk⟩ => by rw [h]; exact hk⟩

theorem postOr_sign_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)} {w' : World D}
    {b : ByteArray} {r : Reply} {m k : ByteArray} (h : postOr X w ts w' b r = .sign m k) : r = .sign m k :=
  (postOr_eq_elim h (by intro _ _ e; cases e)).2

theorem postOr_signIncoming_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)}
    {w' : World D} {b : ByteArray} {r : Reply} {m k : ByteArray} (h : postOr X w ts w' b r = .signIncoming m k) :
    r = .signIncoming m k :=
  (postOr_eq_elim h (by intro _ _ e; cases e)).2

theorem postOr_signNext_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)}
    {w' : World D} {b : ByteArray} {r : Reply} {m k : ByteArray} (h : postOr X w ts w' b r = .signNext m k) :
    r = .signNext m k :=
  (postOr_eq_elim h (by intro _ _ e; cases e)).2

theorem postOr_host_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)} {w' : World D}
    {b : ByteArray} {r : Reply} {op : Op} {p k : ByteArray} (h : postOr X w ts w' b r = .host op p k) :
    r = .host op p k :=
  (postOr_eq_elim h (by intro _ _ e; cases e)).2

theorem postOr_submit_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)} {w' : World D}
    {b : ByteArray} {r : Reply} {c k : ByteArray} (h : postOr X w ts w' b r = .submit c k) : r = .submit c k :=
  (postOr_eq_elim h (by intro _ _ e; cases e)).2

theorem postOr_precommit_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)}
    {w' : World D} {b : ByteArray} {r : Reply} {k : ByteArray} (h : postOr X w ts w' b r = .precommit k) :
    r = .precommit k :=
  (postOr_eq_elim h (by intro _ _ e; cases e)).2

/-- An `ok` end survives `postOr` only when no post fired (a refusal ends `refused`). -/
theorem postOr_done_ok_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)}
    {w' : World D} {b : ByteArray} {r : Reply} {o e : ByteArray}
    (h : postOr X w ts w' b r = .done CommandExit.ok.code.toUInt8 o e) :
    r = .done CommandExit.ok.code.toUInt8 o e :=
  (postOr_eq_elim h (by intro _ _ e; simp [CommandExit.code] at e)).2

end Nanodregg.Protocol.Command
