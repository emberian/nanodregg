/-
# Hosting.Proofs.ContextualNano — nano's free program over effects is an open protocol (lane PROTOCOL)

Moved out of `Lang.Proofs.Contextual.Protocol` (HYGIENE): the theory of open protocols is Lang's;
the instance at the resident's `Prog` reads `Hosting`, which sits above Lang, so it lives here.
`nano_runs_iff`, `nano_interp_agrees`, `nano_interp_runs` keep their names (same namespace).
-/
import Lang.Proofs.Contextual.Protocol
import Hosting.Contextual.NanoBridge
import Hosting.Proofs.ResidentRun

namespace Nanodregg.Lang.Contextual.Protocol

/-! ## Nano's free program over effects is an open protocol with a trivial index and no holes

`Hosting.Resident.Prog` (`cmd | keep | forget | ask | say`, a continuation per result) is the
instance `Ix := Unit`, `Hole := Empty` (the embedding is `Hosting.Contextual.NanoBridge`). -/

namespace Nano

open Nanodregg.Hosting Nanodregg.Hosting.Resident

theorem runs_of_nano {α : Type} {p : Prog α} {es : List Ev} {a : α}
    (h : Proofs.ResidentRun.Runs p es a) : ∃ tr, Runs (ofProg p) tr () a ∧ tr.map toEv = es := by
  induction h with
  | done a => exact ⟨[], Runs.ret (S := sig) (Hole := fun _ => Empty) (A := fun _ => α) (i := ()) a, rfl⟩
  | @cmd c k es a x _ ih =>
    obtain ⟨tr, h, e⟩ := ih
    exact ⟨⟨(), NOp.cmd c, x⟩ :: tr, Runs.call (S := sig) (op := NOp.cmd c) x h, by simp [toEv, e]⟩
  | @keep r t k es a b _ ih =>
    obtain ⟨tr, h, e⟩ := ih
    exact ⟨⟨(), NOp.keep r t, b⟩ :: tr, Runs.call (S := sig) (op := NOp.keep r t) b h,
      by simp [toEv, e]⟩
  | @forget k es a b _ ih =>
    obtain ⟨tr, h, e⟩ := ih
    exact ⟨⟨(), NOp.forget, b⟩ :: tr, Runs.call (S := sig) (op := NOp.forget) b h,
      by simp [toEv, e]⟩
  | @ask r q k es a x _ ih =>
    obtain ⟨tr, h, e⟩ := ih
    exact ⟨⟨(), NOp.ask r q, x⟩ :: tr, Runs.call (S := sig) (op := NOp.ask r q) x h,
      by simp [toEv, e]⟩
  | @say s k es a _ ih =>
    obtain ⟨tr, h, e⟩ := ih
    exact ⟨⟨(), NOp.say s, ()⟩ :: tr, Runs.call (S := sig) (op := NOp.say s) () h,
      by simp [toEv, e]⟩

theorem nano_of_runs {α : Type} (p : Prog α) {tr : Trace sig} {a : α}
    (h : Runs (ofProg p) tr () a) : Proofs.ResidentRun.Runs p (tr.map toEv) a := by
  induction p generalizing tr with
  | done b =>
    cases h
    exact .done _
  | cmd c k ih =>
    cases h with
    | call x h => exact .cmd x (ih x h)
  | keep r t k ih =>
    cases h with
    | call b h => exact .keep b (ih b h)
  | forget k ih =>
    cases h with
    | call b h => exact .forget b (ih b h)
  | ask r q k ih =>
    cases h with
    | call x h => exact .ask x (ih x h)
  | say s k ih =>
    cases h with
    | call u h => exact .say (ih h)

/-- **Nano's paths are protocol paths**: `Hosting.Proofs.ResidentRun.Runs p es a` is exactly a
`Runs` path of the protocol `ofProg p`, read through `toEv`. -/
theorem nano_runs_iff {α : Type} (p : Prog α) (es : List Ev) (a : α) :
    Proofs.ResidentRun.Runs p es a ↔ ∃ tr, Runs (ofProg p) tr () a ∧ tr.map toEv = es :=
  ⟨runs_of_nano, fun ⟨_, h, e⟩ => e ▸ nano_of_runs p h⟩

/-- **The interpreters agree**: nano's `Prog.interp` at its recording handler computes what this
module's `interpret` computes at the recording oracle environment: the same value, the same
counter, and the trace read through `toEv`. -/
theorem nano_interp_agrees (o : Oracle) {α : Type} (p : Prog α) (n : Nat) (es : List Ev)
    (tr₀ : Trace sig) :
    ∃ a n' tr, interpret (record (oracleH o)) (ofProg p) (n, tr₀) = .done () a (n', tr₀ ++ tr) ∧
      (p.interp (recorder o)).run (n, es) = (a, (n', es ++ tr.map toEv)) := by
  induction p generalizing n es tr₀ with
  | done a => exact ⟨a, n, [], by simp [interpret, fold, execAlgebra, ofProg], by simp [Prog.interp]; rfl⟩
  | cmd c k ih =>
    obtain ⟨a, n', tr, h1, h2⟩ := ih (o.cmd n) (n + 1) (es ++ [.cmd c (o.cmd n)])
      (tr₀ ++ [⟨(), NOp.cmd c, o.cmd n⟩])
    exact ⟨a, n', ⟨(), NOp.cmd c, o.cmd n⟩ :: tr, by simpa [interpret, fold, execAlgebra, record, ofProg, oracleH] using h1,
      by simpa [Prog.interp, recorder, toEv] using h2⟩
  | keep r t k ih =>
    obtain ⟨a, n', tr, h1, h2⟩ := ih (o.keep n) (n + 1) (es ++ [.keep r t (o.keep n)])
      (tr₀ ++ [⟨(), NOp.keep r t, o.keep n⟩])
    exact ⟨a, n', ⟨(), NOp.keep r t, o.keep n⟩ :: tr, by simpa [interpret, fold, execAlgebra, record, ofProg, oracleH] using h1,
      by simpa [Prog.interp, recorder, toEv] using h2⟩
  | forget k ih =>
    obtain ⟨a, n', tr, h1, h2⟩ := ih (o.forget n) (n + 1) (es ++ [.forget (o.forget n)])
      (tr₀ ++ [⟨(), NOp.forget, o.forget n⟩])
    exact ⟨a, n', ⟨(), NOp.forget, o.forget n⟩ :: tr, by simpa [interpret, fold, execAlgebra, record, ofProg, oracleH] using h1,
      by simpa [Prog.interp, recorder, toEv] using h2⟩
  | ask r q k ih =>
    obtain ⟨a, n', tr, h1, h2⟩ := ih (o.ask n) (n + 1) (es ++ [.ask r q (o.ask n)])
      (tr₀ ++ [⟨(), NOp.ask r q, o.ask n⟩])
    exact ⟨a, n', ⟨(), NOp.ask r q, o.ask n⟩ :: tr, by simpa [interpret, fold, execAlgebra, record, ofProg, oracleH] using h1,
      by simpa [Prog.interp, recorder, toEv] using h2⟩
  | say s k ih =>
    obtain ⟨a, n', tr, h1, h2⟩ := ih (n + 1) (es ++ [.say s]) (tr₀ ++ [⟨(), NOp.say s, ()⟩])
    exact ⟨a, n', ⟨(), NOp.say s, ()⟩ :: tr, by simpa [interpret, fold, execAlgebra, record, ofProg, oracleH] using h1,
      by simpa [Prog.interp, recorder, toEv] using h2⟩

/-- **`interp_runs`, recovered**: nano's theorem (the interpreter performs exactly a path, for
every oracle) follows from this module's `interpret_record`, the agreement of the interpreters,
and `nano_runs_iff`. -/
theorem nano_interp_runs (o : Oracle) {α : Type} (p : Prog α) (n : Nat) (es : List Ev) :
    ∃ es', ((p.interp (recorder o)).run (n, es)).2.2 = es ++ es' ∧
      Proofs.ResidentRun.Runs p es' ((p.interp (recorder o)).run (n, es)).1 := by
  obtain ⟨a, n', tr, h1, h2⟩ := nano_interp_agrees o p n es []
  have hr := interpret_record (oracleH o) (ofProg p) n []
  rw [h1] at hr
  obtain ⟨tr', htr, hrun⟩ := hr
  simp only [List.nil_append] at htr
  subst htr
  rw [h2]
  exact ⟨tr.map toEv, rfl, nano_of_runs p hrun⟩

end Nano

end Nanodregg.Lang.Contextual.Protocol
