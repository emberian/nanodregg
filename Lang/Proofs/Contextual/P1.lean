/- P1 proofs: finite interaction sets, completed repair, and the non-null revision sessions. -/
import Lang.Contextual.P1
import Lang.Proofs.Contextual.P5
import Lang.Proofs.Contextual.Judge

namespace Nanodregg.Lang.Contextual.P1
variable {A : Type}

/-- Behavioral orthogonality alone admits the daimon; completion is a separate judgment. -/
def OrthogonalTo (tests : List (Interaction A)) (d : Design A) : Prop :=
  ∀ t ∈ tests, orthogonal d t = true

def Eligible (admissible : Design A → Bool) (tests : List (Interaction A)) (d : Design A) : Prop :=
  admissible d = true ∧ OrthogonalTo tests d

theorem eligible_iff (admissible : Design A → Bool) (tests : List (Interaction A)) (d : Design A) :
    eligible admissible tests d = true ↔ Eligible admissible tests d := by
  simp [eligible, Eligible, OrthogonalTo, List.all_eq_true]

/-- F(T + t) = F(T) intersect {t} perpendicular. -/
theorem adding_obligation (admissible : Design A → Bool) (tests : List (Interaction A))
    (t : Interaction A) (d : Design A) :
    Eligible admissible (tests ++ [t]) d ↔
      Eligible admissible tests d ∧ orthogonal d t = true := by
  constructor
  · rintro ⟨ha, ht⟩
    exact ⟨⟨ha, fun u hu => ht u (List.mem_append_left _ hu)⟩,
      ht t (List.mem_append_right _ (by simp))⟩
  · rintro ⟨⟨ha, ht⟩, hu⟩
    refine ⟨ha, fun u hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact ht u hm
    · have he := List.mem_singleton.mp hm
      subst he
      exact hu

/-- Required perpendicular is contained in tested perpendicular; the converse needs completeness. -/
theorem required_implies_tested {tested required : List (Interaction A)}
    (hsub : ∀ t ∈ tested, t ∈ required) {d : Design A} (h : OrthogonalTo required d) :
    OrthogonalTo tested d :=
  fun t ht => h t (hsub t ht)

theorem eligible_antitone (admissible : Design A → Bool)
    {tested required : List (Interaction A)} (hsub : ∀ t ∈ tested, t ∈ required)
    {d : Design A} (h : Eligible admissible required d) : Eligible admissible tested d :=
  ⟨h.1, required_implies_tested hsub h.2⟩

/-- The verified filling really answers every member of the EXACT returned interaction family.
This is soundness of inspect, not an assumption about caller-supplied status records. -/
theorem inspect_witnessed {hole : Nat} {admissible : Design A → Bool}
    {tests : List (Interaction A)} {d : Design A} {a : A}
    (h : (inspect hole admissible tests d).status = .witnessed a) :
    d = .complete a ∧ admissible (.complete a) = true ∧
      ∀ t ∈ (inspect hole admissible tests d).against, t.run a = true := by
  cases d with
  | gaveUp => cases h
  | complete b =>
    simp only [inspect] at h ⊢
    split at h
    · rename_i hadm
      split at h
      · cases h
      · rename_i hfind
        cases h
        refine ⟨rfl, hadm, ?_⟩
        have hall := List.find?_eq_none.mp hfind
        simpa using hall
    · cases h

/-- Witnesses from completion search answer every interaction in the returned scope. -/
theorem analyze_witnessed [DecidableEq A] {admissible : A → Bool}
    {tests : List (Interaction A)} {domain retained : List A}
    {cert : Option (P5.Refutation A)} {limit : Option P5.Limit} {a : A}
    (h : (analyze admissible tests domain retained cert limit).status = .witnessed a) :
    a ∈ domain ∧ admissible a = true ∧
      ∀ t ∈ (analyze admissible tests domain retained cert limit).against, t.run a = true := by
  obtain ⟨hm, ha⟩ := P5.witnessed_sound h
  have hb : admissible a = true ∧ guard tests a = true := by simpa only [Bool.and_eq_true] using ha
  exact ⟨hm, hb.1, List.all_eq_true.mp hb.2⟩

/-- Refuted search is a universal negative over the explicitly declared domain and tests. -/
theorem analyze_refuted [DecidableEq A] {admissible : A → Bool}
    {tests : List (Interaction A)} {domain retained : List A}
    {cert : Option (P5.Refutation A)} {limit : Option P5.Limit} {r : P5.Refutation A}
    (h : (analyze admissible tests domain retained cert limit).status = .refuted r) :
    ¬ ∃ a ∈ domain, admissible a = true ∧ guard tests a = true := by
  obtain hr := P5.refuted_sound h
  rintro ⟨a, ha, hadm, ht⟩
  have hf := hr a ha
  simp [hadm, ht] at hf

/-- Absence of a retained repair does not refute the whole interaction problem. -/
theorem analyze_no_certificate [DecidableEq A] (admissible : A → Bool)
    (tests : List (Interaction A)) (domain retained : List A) (r : P5.Refutation A) :
    (analyze admissible tests domain retained none).status ≠ .refuted r :=
  P5.no_certificate_never_refuted
    (⟨domain, fun a => admissible a && guard tests a⟩ : P5.Problem A) retained none r

theorem gaveUp_never_verified (hole : Nat) (admissible : Design A → Bool)
    (tests : List (Interaction A)) (a : A) :
    (inspect hole admissible tests .gaveUp).status ≠ .witnessed a := by
  simp [inspect]

/-- Even perfect behavioral compatibility cannot turn giving up into a repair. -/
theorem daimon_distinction (hole : Nat) (tests : List (Interaction A)) :
    OrthogonalTo tests (.gaveUp : Design A) ∧
      (inspect hole (fun _ => true) tests (.gaveUp : Design A)).status = .open (.gaveUp hole) [] :=
  ⟨fun _ _ => rfl, rfl⟩

/-- The landed predicate guard is exactly the singleton-interaction case, including all
non-verified verdicts (typing, support, pruning and budget). -/
theorem singleton_judge {D : CalculusData} {E : Type}
    (I : Iface D E) (w : World E) (c : Candidate D) :
    Nanodregg.Lang.Contextual.judge (withInteractions I (singleton I)) w c =
      Nanodregg.Lang.Contextual.judge I w c := by
  have hi : withInteractions I (singleton I) = I := by
    have hg : (fun e a => guard (singleton I e) a) = I.guard := by
      funext e a; simp [guard, singleton]
    simp [withInteractions, hg]
  rw [hi]

/-- Many interactions have the same typing/support/budget requirements as the old judge;
the guard conjunct now explicitly quantifies over the selected family. -/
theorem interaction_judge_verified_iff {D : CalculusData} {E : Type}
    (I : Iface D E) (tests : E → List (Interaction D.Tm)) (w : World E) (c : Candidate D) :
    Nanodregg.Lang.Contextual.judge (withInteractions I tests) w c = .verified ↔
      D.check I.ctx c.filling I.ty = true ∧
      (∀ t ∈ tests w.env, t.run c.filling = true) ∧
      (∀ b ∈ c.blockers, w.live b = false) ∧
      (∀ t ∈ effSupports I c, w.live t = true) ∧ c.cost ≤ I.budget := by
  rw [judge_verified_iff]
  simp [withInteractions, guard, List.all_eq_true, effSupports]

/-- Hole and world indices select the obligations actually used by the judgment. -/
theorem judgeAt_verified_iff {D : CalculusData} {E : Type}
    (I : Iface D E) (family : Family D.Tm E) (w : World E) (c : Candidate D) :
    judgeAt I family w c = .verified ↔
      D.check I.ctx c.filling I.ty = true ∧
      (∀ t ∈ family I.name w, t.run c.filling = true) ∧
      (∀ b ∈ c.blockers, w.live b = false) ∧
      (∀ t ∈ effSupports I c, w.live t = true) ∧ c.cost ≤ I.budget :=
  interaction_judge_verified_iff I (fun _ => family I.name w) w c

namespace Nullable

theorem tested_can_miss_required :
    (inspect 0 (fun _ => true) [nonNull] (.complete .unchecked)).status = .witnessed .unchecked ∧
    (inspect 0 (fun _ => true) [nonNull, null] (.complete .unchecked)).status =
      .open (.interaction 1) [] ∧
    ((inspect 0 (fun _ => true) [nonNull] (.complete .unchecked)).against.map Interaction.name) = [0] ∧
    ((inspect 0 (fun _ => true) [nonNull, null] (.complete .unchecked)).against.map Interaction.name) = [0, 1] := by
  decide

theorem withdrawal_suspends :
    observation before = some ([[.verified]], some 0, []) ∧
    observation (before ++ [withdrawNonNull]) =
      some ([[.conflict .guardFails]], some 0, [.refill 0]) := by decide

theorem withdrawal_tolerated :
    observation (before ++ [withdrawNonNull, .propose 0 (candidate .tolerate), .select 1 0 1]) =
      some ([[.conflict .guardFails, .verified]], some 1, []) := by decide

theorem withdrawal_checked :
    observation (before ++ [withdrawNonNull, .propose 0 (candidate .check), .select 1 0 1]) =
      some ([[.conflict .guardFails, .verified]], some 1, []) := by decide

theorem explicit_reprecondition :
    observation (before ++ [withdrawNonNull, .edit (.setEnv true), .select 1 0 0]) =
      some ([[.verified]], some 0, []) := by decide

theorem inadmissible_filling_refused :
    (inspect 0 (fun _ => false) [nonNull] (.complete .tolerate)).status =
      .open .admission [] := by decide

theorem daimon_empty_tests_still_open :
    (inspect 0 (fun _ => true) ([] : List (Interaction Handler)) .gaveUp).status =
      .open (.gaveUp 0) [] := by decide

/-- Failed retained search is OPEN while a completion outside the retained list succeeds. -/
theorem unretained_repair_exists :
    (analyze (fun _ => true) (required false) [.unchecked, .tolerate, .check] [.unchecked] none).status =
      .open .searchRemaining [] ∧
    (analyze (fun _ => true) (required false) [.unchecked, .tolerate, .check] [.tolerate] none).status =
      .witnessed .tolerate := by decide

end Nullable

/-- Uniform hole fillings cannot verify both peer interactions: the LANG-67 no-foresight
obstruction survives the interaction-set judge. The quantifier is over ALL substitutions. -/
theorem coin_interaction_obstruction
    (θ : Protocol.Subst Protocol.Coin.sig Protocol.Coin.HoleN Protocol.Coin.Res) :
    guard [⟨0, fun σ => Protocol.Coin.wins false (Protocol.subst σ Protocol.Coin.planHole) ()⟩,
           ⟨1, fun σ => Protocol.Coin.wins true (Protocol.subst σ Protocol.Coin.planHole) ()⟩] θ ≠ true := by
  intro h
  have hp : Protocol.Coin.wins false (Protocol.subst θ Protocol.Coin.planHole) () = true ∧
      Protocol.Coin.wins true (Protocol.subst θ Protocol.Coin.planHole) () = true := by
    simpa [guard] using h
  apply Protocol.Coin.no_foresight.2
  exact ⟨θ, fun b => by cases b; exact hp.1; exact hp.2⟩

end Nanodregg.Lang.Contextual.P1
