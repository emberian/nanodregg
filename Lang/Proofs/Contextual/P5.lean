/- P5 proofs: logical status soundness and alternating simulation. -/
import Lang.Contextual.P5
import Lang.Proofs.Contextual.Protocol

namespace Nanodregg.Lang.Contextual.P5
variable {A : Type} [DecidableEq A]

/-- Refutation covers the declared question, not merely the retained candidates. -/
theorem checkRefutation_sound {p : Problem A} {r : Refutation A}
    (h : checkRefutation p r = true) : ∀ a ∈ p.domain, p.accepts a = false := by
  simp only [checkRefutation, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, Bool.not_eq_true'] at h
  exact fun a ha => h.2 a (h.1 a ha)

theorem witnessed_sound {p : Problem A} {cs : List A} {r : Option (Refutation A)}
    {limit : Option Limit} {a : A} (h : judge p cs r limit = .witnessed a) :
    a ∈ p.domain ∧ p.accepts a = true := by
  unfold judge at h
  split at h
  · cases h
  · split at h
    · rename_i b hb
      cases h
      simpa [Problem.valid] using List.find?_some hb
    · split at h
      · cases h
      · split at h <;> cases h

theorem refuted_sound {p : Problem A} {cs : List A} {r : Option (Refutation A)}
    {limit : Option Limit} {e : Refutation A} (h : judge p cs r limit = .refuted e) :
    ∀ a ∈ p.domain, p.accepts a = false := by
  unfold judge at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i hr
          cases h
          exact checkRefutation_sound hr
        · cases h

/-- Search exhaustion is never checked impossibility without a certificate. -/
theorem no_certificate_never_refuted (p : Problem A) (cs : List A)
    (limit : Option Limit) (r : Refutation A) : judge p cs none limit ≠ .refuted r := by
  cases limit <;> simp only [judge]
  · split <;> simp
  · simp

theorem exhausted_is_open {p : Problem A} {cs : List A}
    (h : cs.find? p.valid = none) : judge p cs none = .open .searchRemaining [] := by
  simp [judge, h]

/-- The four constructors have distinct logical meanings even with identical payload types. -/
theorem refuted_ne_outside {W R O L : Type} (r : R) (l : L) :
    (LogicalStatus.refuted r : LogicalStatus W R O L) ≠ .outsideThisProcedure l := by
  intro h; cases h

theorem not_unfilled_suspends (env : Nat → Option Bool) (n : Nat) (h : env n = none) :
    evaluate env (.neg (.atom n)) = .suspended n [] := by
  simp [evaluate, h, Evaluation.neg]

theorem negation_preserves_suspension {env : Nat → Option Bool} {f : Formula}
    {n : Nat} {ns : List Nat} (h : evaluate env f = .suspended n ns) :
    evaluate env (.neg f) = .suspended n ns := by
  simp [evaluate, h, Evaluation.neg]

/-- Refinement matches SPEC inputs forward, IMPLEMENTATION outputs backward.
The relation is on states, so successor obligations cannot be discharged by label inclusion alone. -/
structure AlternatingSimulation {SI SS I O : Type} (impl : Machine SI I O)
    (spec : Machine SS I O) (R : SI → SS → Prop) : Prop where
  inputs : ∀ si ss, R si ss → ∀ i ss', spec.receive ss i = some ss' →
    ∃ si', impl.receive si i = some si' ∧ R si' ss'
  outputs : ∀ si ss, R si ss → ∀ o si', (o, si') ∈ impl.emit si →
    ∃ ss', (o, ss') ∈ spec.emit ss ∧ R si' ss'

def Refines {SI SS I O : Type} (impl : Machine SI I O) (si : SI)
    (spec : Machine SS I O) (ss : SS) : Prop :=
  ∃ R, R si ss ∧ AlternatingSimulation impl spec R

theorem refines_refl {S I O : Type} (m : Machine S I O) (s : S) : Refines m s m s := by
  refine ⟨Eq, rfl, ?_⟩
  constructor
  · intro si ss h i ss' hi
    subst h; exact ⟨ss', hi, rfl⟩
  · intro si ss h o si' ho
    subst h; exact ⟨si', ho, rfl⟩

theorem refines_trans {S1 S2 S3 I O : Type} {a : Machine S1 I O} {b : Machine S2 I O}
    {c : Machine S3 I O} {s1 : S1} {s2 : S2} {s3 : S3}
    (hab : Refines a s1 b s2) (hbc : Refines b s2 c s3) : Refines a s1 c s3 := by
  obtain ⟨R, hr, hR⟩ := hab
  obtain ⟨T, ht, hT⟩ := hbc
  refine ⟨fun x z => ∃ y, R x y ∧ T y z, ⟨s2, hr, ht⟩, ?_⟩
  constructor
  · rintro x z ⟨y, hxy, hyz⟩ i z' hz
    obtain ⟨y', hy', ht'⟩ := hT.inputs y z hyz i z' hz
    obtain ⟨x', hx', hr'⟩ := hR.inputs x y hxy i y' hy'
    exact ⟨x', hx', y', hr', ht'⟩
  · rintro x z ⟨y, hxy, hyz⟩ o x' hx
    obtain ⟨y', hy', hr'⟩ := hR.outputs x y hxy o x' hx
    obtain ⟨z', hz', ht'⟩ := hT.outputs y z hyz o y' hy'
    exact ⟨z', hz', y', hr', ht'⟩

/-- Every legal finite peer input session survives replacement. -/
theorem simulation_receives {SI SS I O : Type} {impl : Machine SI I O}
    {spec : Machine SS I O} {R : SI → SS → Prop}
    (hsim : AlternatingSimulation impl spec R) (is : List I) {si : SI} {ss ss' : SS}
    (hr : R si ss) (h : receiveAll spec ss is = some ss') :
    ∃ si', receiveAll impl si is = some si' ∧ R si' ss' := by
  induction is generalizing si ss with
  | nil =>
    cases h; exact ⟨si, rfl, hr⟩
  | cons i is ih =>
    simp only [receiveAll] at h ⊢
    cases he : spec.receive ss i with
    | none => simp [he] at h
    | some mid =>
      obtain ⟨mid', hm, hr'⟩ := hsim.inputs si ss hr i mid he
      rw [hm]
      exact ih hr' (by simpa [he] using h)

/-- A receiver narrowing even one legal input is not a refinement; that peer breaks immediately. -/
theorem narrowing_breaks_peer {SI SS I O : Type} {impl : Machine SI I O}
    {spec : Machine SS I O} {si : SI} {ss ss' : SS} {i : I}
    (hlegal : spec.receive ss i = some ss') (hbreak : impl.receive si i = none) :
    ¬ Refines impl si spec ss := by
  rintro ⟨R, hr, hs⟩
  obtain ⟨si', hi, _⟩ := hs.inputs si ss hr i ss' hlegal
  rw [hbreak] at hi; cases hi

/-- Labeled transitions use the same ours/theirs polarity as LANG-67. -/
def Moves {S I O : Type} (m : Machine S I O) (s : S) (a : Action I O) (s' : S) : Prop :=
  match a with
  | .input i => m.receive s i = some s'
  | .output o => (o, s') ∈ m.emit s

/-- Peer's moves match from spec to implementation, our moves in the opposite direction. -/
theorem polarized_matching {SI SS I O : Type} {impl : Machine SI I O}
    {spec : Machine SS I O} {R : SI → SS → Prop}
    (hsim : AlternatingSimulation impl spec R) {si : SI} {ss : SS} (hr : R si ss) :
    (∀ a, a.owner = .theirs → ∀ ss', Moves spec ss a ss' →
      ∃ si', Moves impl si a si' ∧ R si' ss') ∧
    (∀ a, a.owner = .ours → ∀ si', Moves impl si a si' →
      ∃ ss', Moves spec ss a ss' ∧ R si' ss') := by
  constructor
  · intro a hp ss' h
    cases a with
    | input i => exact hsim.inputs si ss hr i ss' h
    | output o => cases hp
  · intro a hp si' h
    cases a with
    | input i => cases hp
    | output o => exact hsim.outputs si ss hr o si' h

/-- Bounded compatibility with an adversarial peer. At either side's output choice the
receiver must accept, and the successor pair owes the remaining safety horizon.
This is absence of refused interactions, not a deadlock-freedom or liveness claim. -/
def SafeFor {S P I O : Type} (m : Machine S I O) (peer : Machine P O I) :
    Nat → S → P → Prop
  | 0, _, _ => True
  | n + 1, s, p =>
    (∀ i p', (i, p') ∈ peer.emit p →
      ∃ s', m.receive s i = some s' ∧ SafeFor m peer n s' p') ∧
    (∀ o s', (o, s') ∈ m.emit s →
      ∃ p', peer.receive p o = some p' ∧ SafeFor m peer n s' p')

/-- Alternating simulation preserves compatibility for arbitrarily long mixed sessions,
including successors after both input and output transitions. -/
theorem simulation_preserves_safety {SI SS P I O : Type} {impl : Machine SI I O}
    {spec : Machine SS I O} {R : SI → SS → Prop}
    (hsim : AlternatingSimulation impl spec R) (peer : Machine P O I)
    (n : Nat) {si : SI} {ss : SS} {p : P} (hr : R si ss)
    (hsafe : SafeFor spec peer n ss p) : SafeFor impl peer n si p := by
  induction n generalizing si ss p with
  | zero => trivial
  | succ n ih =>
    constructor
    · intro i p' hp
      obtain ⟨ss', hs', hrest⟩ := hsafe.1 i p' hp
      obtain ⟨si', hi', hr'⟩ := hsim.inputs si ss hr i ss' hs'
      exact ⟨si', hi', ih hr' hrest⟩
    · intro o si' hi
      obtain ⟨ss', hs', hr'⟩ := hsim.outputs si ss hr o si' hi
      obtain ⟨p', hp', hrest⟩ := hsafe.2 o ss' hs'
      exact ⟨p', hp', ih hr' hrest⟩

/-- More accepted prices and fewer possible replies are a genuine stateful refinement. -/
theorem price_refines {small large : Nat} (hcap : small ≤ large) {outs outs' : List Bool}
    (hout : ∀ b ∈ outs', b ∈ outs) (s : Bool) :
    Refines (priceReceiver large outs') s (priceReceiver small outs) s := by
  refine ⟨Eq, rfl, ?_⟩
  constructor
  · intro si ss he i ss' hi
    subst he
    simp only [priceReceiver] at hi ⊢
    split at hi
    · rename_i hg
      have hg' : si = false ∧ i ≤ large := ⟨hg.1, Nat.le_trans hg.2 hcap⟩
      cases hi
      exact ⟨true, if_pos hg', rfl⟩
    · cases hi
  · intro si ss he o si' ho
    subst he
    cases si with
    | false => simp [priceReceiver] at ho
    | true =>
      change (o, si') ∈ outs'.map (fun b => (b, false)) at ho
      obtain ⟨b, hb, heq⟩ := List.mem_map.mp ho
      cases heq
      exact ⟨false, by simp [priceReceiver, hout o hb], rfl⟩

theorem price_seven_breaks :
    receiveAll (priceReceiver 10 [true, false]) false [7] = some true ∧
    receiveAll (priceReceiver 5 [true]) false [7] = none := by decide

theorem price_seven_not_refinement :
    ¬ Refines (priceReceiver 5 [true]) false (priceReceiver 10 [true, false]) false :=
  narrowing_breaks_peer (i := 7) (ss' := true) (by decide) (by decide)

theorem price_reply_expansion_not_refinement :
    ¬ Refines (priceReceiver 10 [true, false]) true (priceReceiver 10 [true]) true := by
  rintro ⟨R, hr, hs⟩
  obtain ⟨ss', ho, _⟩ := hs.outputs true true hr false false (by simp [priceReceiver])
  simp [priceReceiver] at ho

/-- A concrete revision session visits all four statuses; failed search precedes a real witness. -/
theorem four_status_session :
    runSession statusSession =
      [.open .searchRemaining [], .witnessed 1, .refuted ⟨[0, 1]⟩,
       .outsideThisProcedure .unsupportedFragment] := by decide

theorem incomplete_certificate_refused :
    judge (⟨[0, 1], fun n => n == 1⟩ : Problem Nat) [0] (some ⟨[0]⟩) =
      .open .invalidRefutation [] := by decide

theorem positive_candidate_refutes_certificate :
    judge (⟨[0, 1], fun n => n == 1⟩ : Problem Nat) [] (some ⟨[0, 1]⟩) =
      .open .invalidRefutation [] := by decide

theorem out_of_domain_witness_refused :
    judge (⟨[0], fun _ => true⟩ : Problem Nat) [1] none =
      .open .searchRemaining [] := by decide

/-- The new status judge asks about one uniform filling against BOTH peer responses.
LANG-67 no_foresight is the independent impossibility theorem over all substitutions. -/
theorem uniform_coin_problem_refuted :
    judge (⟨[false, true], fun c =>
      Protocol.Coin.wins false (Protocol.subst (Protocol.Coin.answer c) Protocol.Coin.planHole) () &&
      Protocol.Coin.wins true (Protocol.subst (Protocol.Coin.answer c) Protocol.Coin.planHole) ()⟩)
      [false, true] (some ⟨[false, true]⟩) = .refuted ⟨[false, true]⟩ := by decide

end Nanodregg.Lang.Contextual.P5
