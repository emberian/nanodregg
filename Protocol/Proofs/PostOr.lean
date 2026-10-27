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

/-- `postOr` read by the proofs: the reply it was given, the `forkedPost` refusal
`Head.forkedSelfPost` names, or the `forkedCertified` refusal `Head.forkedCertified` names. -/
theorem postOr_cases (X : Ctx D) (w : World D) (ts : List (Kernel.Step D × D)) (w' : World D)
    (b : ByteArray) (r : Reply) : postOr X w ts w' b r = r ∨ (∃ s m, Head.forkedSelfPost X w ts w' = some (s, m) ∧
      postOr X w ts w' b r = refused (D := D) (.forkedPost s m)) ∨
      (∃ s, Head.forkedSelfPost X w ts w' = none ∧ Head.forkedCertified X w ts b = some s ∧
      postOr X w ts w' b r = refused (D := D) (.forkedCertified s)) := by
  unfold postOr
  cases hf : Head.forkedSelfPost X w ts w' with
  | some sm => obtain ⟨s, m⟩ := sm; exact .inr (.inl ⟨s, m, rfl, rfl⟩)
  | none =>
    cases hc : Head.forkedCertified X w ts b with
    | none => exact .inl rfl
    | some s => exact .inr (.inr ⟨s, rfl, rfl, rfl⟩)

/-- A reply `postOr` hands back that is not a refusal is the reply it was given. -/
theorem postOr_eq_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)} {w' : World D}
    {b : ByteArray} {r r' : Reply} (h : postOr X w ts w' b r = r')
    (hne : ∀ e : Refusal D, r' ≠ refused (D := D) e) : postOr X w ts w' b r = r ∧ r = r' := by
  rcases postOr_cases X w ts w' b r with hp | ⟨s, m, -, hp⟩ | ⟨s, -, -, hp⟩
  · exact ⟨hp, hp ▸ h⟩
  · exact absurd (h ▸ hp) (hne _)
  · exact absurd (h ▸ hp) (hne _)

/-- A continuation survives `postOr` only when no post fired (a refusal carries none). -/
theorem postOr_cont_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)} {w' : World D}
    {b : ByteArray} {r : Reply} {k : ByteArray} (hk : (postOr X w ts w' b r).cont = some k) :
    postOr X w ts w' b r = r ∧ r.cont = some k := by
  rcases postOr_cases X w ts w' b r with hp | ⟨s, m, -, hp⟩ | ⟨s, -, -, hp⟩
  · rw [hp] at hk; exact ⟨hp, hk⟩
  · rw [hp] at hk; simp [refused, Reply.cont] at hk
  · rw [hp] at hk; simp [refused, Reply.cont] at hk

/-- The same, as a rewrite. -/
theorem postOr_cont_some {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)} {w' : World D}
    {b : ByteArray} {r : Reply} {k : ByteArray} :
    (postOr X w ts w' b r).cont = some k ↔ postOr X w ts w' b r = r ∧ r.cont = some k :=
  ⟨postOr_cont_elim, fun ⟨h, hk⟩ => by rw [h]; exact hk⟩

theorem postOr_sign_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)} {w' : World D}
    {b : ByteArray} {r : Reply} {m k : ByteArray} (h : postOr X w ts w' b r = .sign m k) : r = .sign m k :=
  (postOr_eq_elim h (by intro _ e; simp [refused] at e)).2

theorem postOr_signIncoming_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)}
    {w' : World D} {b : ByteArray} {r : Reply} {m k : ByteArray} (h : postOr X w ts w' b r = .signIncoming m k) :
    r = .signIncoming m k :=
  (postOr_eq_elim h (by intro _ e; simp [refused] at e)).2

theorem postOr_signNext_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)}
    {w' : World D} {b : ByteArray} {r : Reply} {m k : ByteArray} (h : postOr X w ts w' b r = .signNext m k) :
    r = .signNext m k :=
  (postOr_eq_elim h (by intro _ e; simp [refused] at e)).2

theorem postOr_host_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)} {w' : World D}
    {b : ByteArray} {r : Reply} {op : Op} {p k : ByteArray} (h : postOr X w ts w' b r = .host op p k) :
    r = .host op p k :=
  (postOr_eq_elim h (by intro _ e; simp [refused] at e)).2

theorem postOr_submit_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)} {w' : World D}
    {b : ByteArray} {r : Reply} {c k : ByteArray} (h : postOr X w ts w' b r = .submit c k) : r = .submit c k :=
  (postOr_eq_elim h (by intro _ e; simp [refused] at e)).2

theorem postOr_precommit_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)}
    {w' : World D} {b : ByteArray} {r : Reply} {k : ByteArray} (h : postOr X w ts w' b r = .precommit k) :
    r = .precommit k :=
  (postOr_eq_elim h (by intro _ e; simp [refused] at e)).2

/-- An `ok` end survives `postOr` only when no post fired (a refusal ends `refused`). -/
theorem postOr_done_ok_elim {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)}
    {w' : World D} {b : ByteArray} {r : Reply} {o e : ByteArray}
    (h : postOr X w ts w' b r = .done CommandExit.ok.code.toUInt8 o e) :
    r = .done CommandExit.ok.code.toUInt8 o e :=
  (postOr_eq_elim h (by intro _ e; simp [refused, CommandExit.code] at e)).2

end Nanodregg.Protocol.Command
