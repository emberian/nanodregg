/- Guarded contextual closure: Operations. Moved without statement changes from Closure. -/
import Lang.Proofs.Contextual.Repair

namespace Nanodregg.Lang.Contextual

variable {D : CalculusData} {E : Type}
  {HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop}


/-! ## The operations: frames -/

theorem update_at {cl : Closure D E} {u v : Nat} {s : Slot D} :
    cl.update u s v = if v = u then s else cl.slot v := rfl

theorem propose_ok {w : World E} {u : Nat} {c : Candidate D} {cl : Closure D E}
    {r : Closure D E × Nat} (h : propose w u c cl = .ok r) :
    ∃ I, cl.find u = some I ∧ r.2 = (cl.slot u).cands.length ∧ r.1.tpl = cl.tpl ∧
      r.1.owed = cl.owed ∧ r.1.hist = cl.hist ++ [.proposed u (cl.slot u).cands.length] ∧
      r.1.slot = cl.update u ⟨(cl.slot u).cands ++ [{ c with status := judge I w c }],
        (cl.slot u).selected, (cl.slot u).accepted⟩ := by
  unfold propose at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i I hf
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨I, hf, rfl, rfl, rfl, rfl, rfl⟩

theorem select_ok {w : World E} {p : Party} {u i : Nat} {cl cl' : Closure D E}
    (h : select w p u i cl = .ok cl') :
    ∃ I c, cl.find u = some I ∧ p = I.chooser ∧ (cl.slot u).accepted = false ∧
      (cl.slot u).cands[i]? = some c ∧ judge I w c = .verified ∧
      cl'.tpl = cl.tpl ∧ cl'.owed = cl.owed ∧ cl'.hist = cl.hist ++ [.selected u i] ∧
      cl'.slot = cl.update u ⟨(cl.slot u).cands.set i { c with status := .verified },
        some i, (cl.slot u).accepted⟩ := by
  unfold select at h
  dsimp only at h
  split at h
  · simp at h
  rename_i I hf
  split at h
  · simp at h
  rename_i hp
  split at h
  · simp at h
  rename_i hacc
  split at h
  · simp at h
  rename_i c hc
  split at h
  · rename_i hv
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨I, c, hf, by simpa using hp, by simpa using hacc, hc, hv, rfl, rfl, rfl, ?_⟩
    simp only [hv]
  · simp at h

theorem deselect_ok {p : Party} {u : Nat} {cl cl' : Closure D E} (h : deselect p u cl = .ok cl') :
    ∃ I, cl.find u = some I ∧ p = I.chooser ∧ (cl.slot u).accepted = false ∧
      cl'.tpl = cl.tpl ∧ cl'.owed = cl.owed ∧ cl'.hist = cl.hist ++ [.deselected u] ∧
      cl'.slot = cl.update u ⟨(cl.slot u).cands, none, (cl.slot u).accepted⟩ := by
  unfold deselect at h
  dsimp only at h
  split at h
  · simp at h
  rename_i I hf
  split at h
  · simp at h
  rename_i hp
  split at h
  · simp at h
  rename_i hacc
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨I, hf, by simpa using hp, by simpa using hacc, rfl, rfl, rfl, rfl⟩

theorem accept_ok {w : World E} {p : Party} {u : Nat} {cl cl' : Closure D E}
    (h : accept w p u cl = .ok cl') :
    ∃ I i c, cl.find u = some I ∧ p = I.acceptor ∧ (cl.slot u).accepted = false ∧
      (cl.slot u).selected = some i ∧ (cl.slot u).cands[i]? = some c ∧ judge I w c = .verified ∧
      cl'.tpl = cl.tpl ∧ cl'.owed = cl.owed ++ [.settle u i] ∧
      cl'.hist = cl.hist ++ [.accepted u i] ∧
      cl'.slot = cl.update u ⟨(cl.slot u).cands, (cl.slot u).selected, true⟩ := by
  unfold accept at h
  dsimp only at h
  split at h
  · simp at h
  rename_i I hf
  split at h
  · simp at h
  rename_i hp
  split at h
  · simp at h
  rename_i hacc
  split at h
  · simp at h
  rename_i i hsel
  split at h
  · simp at h
  rename_i c hc
  split at h
  · rename_i hv
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨I, i, c, hf, by simpa using hp, by simpa using hacc, hsel, hc, hv, rfl, rfl, rfl, rfl⟩
  · simp at h

theorem prune_ok {w : World E} {p : Party} {u i : Nat} {r : Token} {cl cl' : Closure D E}
    (h : prune w p u i r cl = .ok cl') :
    ∃ I c, cl.find u = some I ∧ p = I.chooser ∧
      ¬ ((cl.slot u).accepted = true ∧ (cl.slot u).selected = some i) ∧
      (cl.slot u).cands[i]? = some c ∧
      cl'.tpl = cl.tpl ∧ cl'.owed = cl.owed ∧ cl'.hist = cl.hist ++ [.pruned u i] ∧
      cl'.slot = cl.update u ⟨(cl.slot u).cands.set i
          { c with blockers := c.blockers ++ [r],
                   status := judge I w { c with blockers := c.blockers ++ [r] } },
        (cl.slot u).selected, (cl.slot u).accepted⟩ := by
  unfold prune at h
  dsimp only at h
  split at h
  · simp at h
  rename_i I hf
  split at h
  · simp at h
  rename_i hp
  split at h
  · simp at h
  rename_i hacc
  split at h
  · simp at h
  rename_i c hc
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨I, c, hf, by simpa using hp, hacc, hc, rfl, rfl, rfl, rfl⟩

theorem rejudge_eq (w : World E) (u i : Nat) (cl : Closure D E) :
    rejudge w u i cl = cl ∨ ∃ I c, cl.find u = some I ∧ (cl.slot u).cands[i]? = some c ∧
      (rejudge w u i cl).tpl = cl.tpl ∧ (rejudge w u i cl).owed = cl.owed ∧
      (rejudge w u i cl).hist = cl.hist ∧
      (rejudge w u i cl).slot = cl.update u ⟨(cl.slot u).cands.set i { c with status := judge I w c },
        (cl.slot u).selected, (cl.slot u).accepted⟩ := by
  unfold rejudge
  split
  · exact Or.inl rfl
  · rename_i I hf
    dsimp only
    split
    · exact Or.inl rfl
    · rename_i c hc
      exact Or.inr ⟨I, c, hf, hc, rfl, rfl, rfl, rfl⟩

theorem fill_ok {w : World E} {p : Party} {u : Nat} {c : Candidate D} {cl cl' : Closure D E}
    (h : fill w p u c cl = .ok cl') :
    ∃ cl₁ i, propose w u c cl = .ok (cl₁, i) ∧ select w p u i cl₁ = .ok cl' := by
  unfold fill at h
  split at h
  · simp at h
  · rename_i cl₁ i hp
    exact ⟨cl₁, i, hp, h⟩

/-- The common frame of every operation: the template never changes, the history and the owed
obligations only grow at the end. -/
structure Grows (cl cl' : Closure D E) : Prop where
  tpl : cl'.tpl = cl.tpl
  hist : ∃ sfx, cl'.hist = cl.hist ++ sfx
  owed : ∃ sfx, cl'.owed = cl.owed ++ sfx

theorem Grows.trans {a b c : Closure D E} (h₁ : Grows a b) (h₂ : Grows b c) : Grows a c := by
  obtain ⟨t1, ⟨s1, h1⟩, ⟨o1, p1⟩⟩ := h₁
  obtain ⟨t2, ⟨s2, h2⟩, ⟨o2, p2⟩⟩ := h₂
  exact ⟨t2.trans t1, ⟨s1 ++ s2, by rw [h2, h1, List.append_assoc]⟩,
    ⟨o1 ++ o2, by rw [p2, p1, List.append_assoc]⟩⟩

theorem repair_grows (w : World E) (e : Edit E) (cl : Closure D E) : Grows cl (repair w e cl).1 :=
  ⟨rfl, ⟨_, rfl⟩, ⟨[], by simp [repair]⟩⟩

theorem propose_grows {w : World E} {u : Nat} {c : Candidate D} {cl : Closure D E}
    {r : Closure D E × Nat} (h : propose w u c cl = .ok r) : Grows cl r.1 := by
  obtain ⟨I, -, -, ht, ho, hh, -⟩ := propose_ok h
  exact ⟨ht, ⟨_, hh⟩, ⟨[], by simp [ho]⟩⟩

theorem select_grows {w : World E} {p : Party} {u i : Nat} {cl cl' : Closure D E}
    (h : select w p u i cl = .ok cl') : Grows cl cl' := by
  obtain ⟨I, c, -, -, -, -, -, ht, ho, hh, -⟩ := select_ok h
  exact ⟨ht, ⟨_, hh⟩, ⟨[], by simp [ho]⟩⟩

/-- **The history is a prefix.** Every operation appends to the accepted history and to the owed
obligations; nothing earlier moves; the template is never rewritten. -/
theorem history_is_prefix {w : World E} {op : Op D E} {cl cl' : Closure D E}
    (h : op.run w cl = .ok cl') : Grows cl cl' := by
  cases op with
  | propose u c =>
    simp only [Op.run] at h
    cases hp : propose w u c cl with
    | error r => rw [hp] at h; simp [Except.map] at h
    | ok r =>
      rw [hp] at h
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      exact propose_grows hp
  | select p u i => exact select_grows h
  | fill p u c =>
    obtain ⟨cl₁, i, hp, hs⟩ := fill_ok h
    exact (propose_grows hp).trans (select_grows hs)
  | deselect p u =>
    obtain ⟨I, -, -, -, ht, ho, hh, -⟩ := deselect_ok h
    exact ⟨ht, ⟨_, hh⟩, ⟨[], by simp [ho]⟩⟩
  | accept p u =>
    obtain ⟨I, i, c, -, -, -, -, -, -, ht, ho, hh, -⟩ := accept_ok h
    exact ⟨ht, ⟨_, hh⟩, ⟨_, ho⟩⟩
  | prune p u i r =>
    obtain ⟨I, c, -, -, -, -, ht, ho, hh, -⟩ := prune_ok h
    exact ⟨ht, ⟨_, hh⟩, ⟨[], by simp [ho]⟩⟩
  | rejudge u i =>
    simp only [Op.run, Except.ok.injEq] at h
    subst h
    rcases rejudge_eq w u i cl with h | ⟨I, c, -, -, ht, ho, hh, -⟩
    · rw [h]; exact ⟨rfl, ⟨[], by simp⟩, ⟨[], by simp⟩⟩
    · exact ⟨ht, ⟨[], by simp [hh]⟩, ⟨[], by simp [ho]⟩⟩
  | edit e =>
    simp only [Op.run, Except.ok.injEq] at h
    subst h
    exact repair_grows w e cl


end Nanodregg.Lang.Contextual
