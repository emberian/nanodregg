/-
P11a: a refuted completion game is lost with recorded nogoods.
Köhler et al. (2013), PDF pp3–4; de Kleer (1986), printed pp144–145.
-/
import Lang.Contextual.NogoodGames
import Lang.Proofs.Contextual.Games
import Lang.Proofs.Contextual.P5

namespace Nanodregg.Lang.Contextual.P5.NogoodGames
open Games

/-- Köhler et al., PDF p4: a successful candidate is a winning move in the
question game, independently of any search list or certificate. -/
theorem accepted_wins {A : Type} {p : Problem A} {a : A}
    (ha : a ∈ p.domain) (hyes : p.accepts a = true) :
    Solved (moves p) true .question := by
  refine .win (y := .candidate a) ?_ (.lose ?_)
  · exact List.mem_map.mpr ⟨a, ha, rfl⟩
  · intro y hy
    simp [moves, hyes] at hy

/-- Köhler et al., PDF p4: exhausting the DECLARED question by checked exclusions
is losing. Exhausting a retained search list alone supplies no such derivation. -/
theorem excluded_loses {A : Type} {p : Problem A}
    (hno : ∀ a ∈ p.domain, p.accepts a = false) :
    Solved (moves p) false .question := by
  apply Solved.lose
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  refine .win (y := .terminal) ?_ (.lose ?_)
  · simp [moves, hno a ha]
  · intro y hy
    cases hy

/-- de Kleer, printed p145: every covered candidate has a recorded nogood
subset of its actual assumptions, and is rejected by the current question. -/
theorem checkCertificate_sound {A : Type} [DecidableEq A] {p : Problem A}
    {supports : A → List Token} {nogoods : List (List Token)} {c : Certificate A}
    (h : checkCertificate p supports nogoods c = true) :
    ∀ a ∈ p.domain, ∃ n, (a, n) ∈ c ∧ n ∈ nogoods ∧
      (∀ t ∈ n, t ∈ supports a) ∧ p.accepts a = false := by
  simp only [checkCertificate, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  intro a ha
  obtain ⟨⟨a', n⟩, hrow, he⟩ := h.1 a ha
  dsimp at he
  subst a'
  have hc := h.2 (a, n) hrow
  exact ⟨n, hrow, hc.1.1, hc.1.2, hc.2⟩

/-- de Kleer, printed p145; Köhler et al., PDF p4: a refuted result identifies
the submitted certificate and replays coverage, record identity, assumptions and rejection. -/
theorem refuted_recorded {A : Type} [DecidableEq A] {p : Problem A}
    {retained : List A} {supports : A → List Token} {nogoods : List (List Token)}
    {certificate : Option (Certificate A)} {limit : Option Limit} {c : Certificate A}
    (h : judge p retained supports nogoods certificate limit = .refuted c) :
    certificate = some c ∧ ∀ a ∈ p.domain, ∃ n, (a, n) ∈ c ∧ n ∈ nogoods ∧
      (∀ t ∈ n, t ∈ supports a) ∧ p.accepts a = false := by
  unfold judge at h
  split at h
  · cases h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i hc
        cases h
        exact ⟨rfl, checkCertificate_sound hc⟩
      · cases h

/-- Köhler et al., PDF p4; de Kleer, printed p145: the actual refuted status
implies loss in the independent game semantics, together with recorded explanations.
Loss is derived from replayed coverage, not used as a premise or stored proof field. -/
theorem refuted_is_lost {A : Type} [DecidableEq A] {p : Problem A}
    {retained : List A} {supports : A → List Token} {nogoods : List (List Token)}
    {certificate : Option (Certificate A)} {limit : Option Limit} {c : Certificate A}
    (h : judge p retained supports nogoods certificate limit = .refuted c) :
    Solved (moves p) false .question ∧
      ∀ a ∈ p.domain, ∃ n ∈ nogoods, (a, n) ∈ c ∧ ∀ t ∈ n, t ∈ supports a := by
  have hc := (refuted_recorded h).2
  constructor
  · apply excluded_loses
    intro a ha
    obtain ⟨_, _, _, _, hn⟩ := hc a ha
    exact hn
  · intro a ha
    obtain ⟨n, hm, hn, hs, _⟩ := hc a ha
    exact ⟨n, hn, hm, hs⟩

/-- Köhler et al., PDF p4: the wrapper preserves the landed judge's positive
soundness; nogood records cannot override a checked witness. -/
theorem witnessed_is_won {A : Type} [DecidableEq A] {p : Problem A}
    {retained : List A} {supports : A → List Token} {nogoods : List (List Token)}
    {certificate : Option (Certificate A)} {limit : Option Limit} {a : A}
    (h : judge p retained supports nogoods certificate limit = .witnessed a) :
    a ∈ p.domain ∧ p.accepts a = true ∧ Solved (moves p) true .question := by
  unfold judge at h
  split at h
  · rename_i b hb
    cases h
    have hw := P5.witnessed_sound hb
    exact ⟨hw.1, hw.2, accepted_wins hw.1 hw.2⟩
  · cases h
  · split at h
    · cases h
    · split at h <;> cases h

/-- de Kleer, printed p145: a nonempty question can be refuted by a named,
recorded nogood. This inhabits the generic coverage and replay premises. -/
theorem recorded_loss_example :
    judge (⟨[0], fun _ => false⟩ : Problem Nat) [] (fun _ => [⟨1, 0⟩])
      [[⟨1, 0⟩]] (some [(0, [⟨1, 0⟩])]) = .refuted [(0, [⟨1, 0⟩])] := by decide

/-- de Kleer, printed p145: an unrecorded explanation never refutes. -/
theorem unrecorded_refused :
    judge (⟨[0], fun _ => false⟩ : Problem Nat) [] (fun _ => [⟨1, 0⟩])
      [] (some [(0, [⟨1, 0⟩])]) = .open .invalidRefutation [] := by decide

/-- de Kleer, printed p145: a record about assumptions the candidate does not
use cannot refute it, even if the independent acceptance test currently fails. -/
theorem unrelated_record_refused :
    judge (⟨[0], fun _ => false⟩ : Problem Nat) [] (fun _ => [⟨2, 0⟩])
      [[⟨1, 0⟩]] (some [(0, [⟨1, 0⟩])]) = .open .invalidRefutation [] := by decide

/-- de Kleer, printed pp144–145: incomplete records leave the full question open. -/
theorem uncovered_candidate_refused :
    judge (⟨[0, 1], fun _ => false⟩ : Problem Nat) [] (fun _ => [⟨1, 0⟩])
      [[⟨1, 0⟩]] (some [(0, [⟨1, 0⟩])]) = .open .invalidRefutation [] := by decide

/-- Köhler et al., PDF p4; de Kleer, printed p145: stale or erroneous recorded
nogoods cannot refute a currently accepted but unretained candidate. -/
theorem stale_record_refused :
    judge (⟨[0], fun _ => true⟩ : Problem Nat) [] (fun _ => [⟨1, 0⟩])
      [[⟨1, 0⟩]] (some [(0, [⟨1, 0⟩])]) = .open .invalidRefutation [] := by decide

end Nanodregg.Lang.Contextual.P5.NogoodGames
