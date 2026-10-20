/- Certified acyclic provenance: independent finite derivations and exact unrolling. -/
import Lang.Contextual.Acyclic
import Lang.Proofs.Contextual.Judge

namespace Nanodregg.Lang.Contextual.Acyclic

variable {n : Nat} {E : Type}

def Holds (w : World E) (p : Polynomial) : Prop :=
  ∃ m ∈ p, Monomial.holds w m

def Ranked (g : Graph n) : Prop :=
  ∀ i j, j ∈ (g.body i).refs → g.rank j < g.rank i

/-- Independent proof-tree semantics: hole use unfolds its body, without a fuel cutoff.
No rule assumes the compiler or successful validation. -/
inductive Derives (g : Graph n) (w : World E) : Expr n → Prop where
  | tokens {p : Polynomial} : Holds w p → Derives g w (.tokens p)
  | hole {i : Fin n} : Derives g w (g.body i) → Derives g w (.hole i)
  | left {a b : Expr n} : Derives g w a → Derives g w (.alt a b)
  | right {a b : Expr n} : Derives g w b → Derives g w (.alt a b)
  | joint {a b : Expr n} : Derives g w a → Derives g w b → Derives g w (.joint a b)

/-- Nonempty dependency reachability, in consumer-to-dependency order. -/
inductive Depends (g : Graph n) : Fin n → Fin n → Prop where
  | edge {i j : Fin n} : j ∈ (g.body i).refs → Depends g i j
  | trans {i j k : Fin n} : Depends g i j → Depends g j k → Depends g i k

theorem holds_product (w : World E) (p q : Polynomial) :
    Holds w (product p q) ↔ Holds w p ∧ Holds w q := by
  simp only [Holds, product, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, h⟩
    exact ⟨⟨a, ha, fun t ht => h.1 t (List.mem_append_left _ ht),
      fun t ht => h.2 t (List.mem_append_left _ ht)⟩,
      ⟨b, hb, fun t ht => h.1 t (List.mem_append_right _ ht),
      fun t ht => h.2 t (List.mem_append_right _ ht)⟩⟩
  · rintro ⟨⟨a, ha, hap, han⟩, ⟨b, hb, hbp, hbn⟩⟩
    refine ⟨_, ⟨a, ha, b, hb, rfl⟩, ?_, ?_⟩
    · intro t ht
      exact (List.mem_append.mp ht).elim (hap t) (hbp t)
    · intro t ht
      exact (List.mem_append.mp ht).elim (han t) (hbn t)

theorem holds_append (w : World E) (p q : Polynomial) :
    Holds w (p ++ q) ↔ Holds w p ∨ Holds w q := by
  simp [Holds, List.mem_append, or_and_right, exists_or]

theorem mem_edges (g : Graph n) (i j : Fin n) :
    (i, j) ∈ g.edges ↔ j ∈ (g.body i).refs := by
  simp [Graph.edges]

/-- Executable witness checking is exactly strict descent on every actual reference. -/
theorem validate_iff (g : Graph n) : validate g = none ↔ Ranked g := by
  simp only [validate, Option.map_eq_none_iff, List.find?_eq_none]
  constructor
  · intro h i j hij
    have := h (i, j) ((mem_edges g i j).mpr hij)
    simpa using this
  · intro h e he
    have := h e.1 e.2 ((mem_edges g e.1 e.2).mp he)
    simpa using this

theorem depends_rank {g : Graph n} (h : Ranked g) {i j : Fin n}
    (d : Depends g i j) : g.rank j < g.rank i := by
  induction d with
  | edge e => exact h _ _ e
  | trans _ _ h1 h2 => exact Nat.lt_trans h2 h1

/-- The boundary includes indirect self-dependency, regardless of token truth or roots. -/
theorem cycles_not_ranked {g : Graph n} {i : Fin n} (d : Depends g i i) :
    ¬ Ranked g := fun h => Nat.lt_irrefl _ (depends_rank h d)

/-- A finite expansion never invents a proof tree, even for an invalid graph. -/
theorem expand_sound {g : Graph n} {w : World E} {lookup : Fin n → Polynomial}
    (h : ∀ i, Holds w (lookup i) → Derives g w (.hole i)) (e : Expr n) :
    Holds w (e.expand lookup) → Derives g w e := by
  induction e with
  | tokens p => exact Derives.tokens
  | hole i => exact h i
  | alt a b ia ib =>
    intro he
    rcases (holds_append w _ _).mp he with ha | hb
    · exact .left (ia ha)
    · exact .right (ib hb)
  | joint a b ia ib =>
    intro he
    obtain ⟨ha, hb⟩ := (holds_product w _ _).mp he
    exact .joint (ia ha) (ib hb)

theorem unroll_sound {g : Graph n} {w : World E} (fuel : Nat) (i : Fin n) :
    Holds w (unroll g fuel i) → Derives g w (.hole i) := by
  induction fuel generalizing i with
  | zero => simp [unroll, Holds]
  | succ k ih => exact fun h => .hole (expand_sound ih (g.body i) h)

/-- Completeness of expression expansion given completeness at its referenced holes. -/
theorem expand_complete {g : Graph n} {w : World E} {lookup : Fin n → Polynomial}
    (e : Expr n)
    (h : ∀ i ∈ e.refs, Derives g w (.hole i) → Holds w (lookup i)) :
    Derives g w e → Holds w (e.expand lookup) := by
  induction e with
  | tokens p => intro d; cases d with | tokens hp => exact hp
  | hole i => exact h i (by simp [Expr.refs])
  | alt a b ia ib =>
    intro d
    apply (holds_append w _ _).mpr
    cases d with
    | left da => exact Or.inl (ia (fun i hi => h i (by simp [Expr.refs, hi])) da)
    | right db => exact Or.inr (ib (fun i hi => h i (by simp [Expr.refs, hi])) db)
  | joint a b ia ib =>
    intro d
    apply (holds_product w _ _).mpr
    cases d with
    | joint da db => exact ⟨ia (fun i hi => h i (by simp [Expr.refs, hi])) da,
        ib (fun i hi => h i (by simp [Expr.refs, hi])) db⟩

/-- Rank is the sufficient unrolling bound, not an assumed derivation-height bound. -/
theorem unroll_complete {g : Graph n} {w : World E} (h : Ranked g)
    (fuel : Nat) (i : Fin n) (hi : g.rank i < fuel) :
    Derives g w (.hole i) → Holds w (unroll g fuel i) := by
  induction fuel generalizing i with
  | zero => omega
  | succ k ih =>
    intro d
    cases d with
    | hole db =>
      apply expand_complete (g.body i) _ db
      intro j hj dj
      have hjlt := h i j hj
      exact ih j (by omega) dj

/-- The returned carrier is exact for independent proof trees, with no caller acyclicity premise. -/
theorem adapt_correct {g : Graph n} {i : Fin n} {p : Polynomial}
    (h : adapt g i = .ok p) (w : World E) :
    Holds w p ↔ Derives g w (.hole i) := by
  unfold adapt at h
  split at h
  · cases h
  · rename_i hv
    cases h
    exact ⟨unroll_sound _ _, unroll_complete ((validate_iff g).mp hv) _ _ (by omega)⟩

/-- Every represented graph has no nonempty path back to any hole, even an undemanded one. -/
theorem adapt_acyclic {g : Graph n} {root : Fin n} {p : Polynomial}
    (h : adapt g root = .ok p) (i : Fin n) : ¬ Depends g i i := by
  unfold adapt at h
  split at h
  · cases h
  · rename_i hv
    exact fun d => cycles_not_ranked d ((validate_iff g).mp hv)

/-- Cyclic inputs return an explicit refusal, never a truncated successful polynomial. -/
theorem cycle_refused {g : Graph n} {i : Fin n} (d : Depends g i i) (root : Fin n) :
    ∃ reason, adapt g root = .error reason := by
  have hn : validate g ≠ none := fun h => cycles_not_ranked d ((validate_iff g).mp h)
  cases hv : validate g with
  | none => exact False.elim (hn hv)
  | some reason => exact ⟨reason, by simp [adapt, hv]⟩

/-- Every refusal identifies an actual nondecreasing reference, with exact endpoint
names. A bad supplied rank is reported as such, not mislabelled as a proven cycle. -/
theorem refusal_explained {g : Graph n} {root : Fin n} {reason : Refusal}
    (h : adapt g root = .error reason) :
    ∃ i j, j ∈ (g.body i).refs ∧ g.rank i ≤ g.rank j ∧
      reason = if i = j then .fixedPointDependency i.val
        else .rankNotDecreasing i.val j.val := by
  cases hf : g.edges.find? (fun e => decide (g.rank e.1 ≤ g.rank e.2)) with
  | none => simp [adapt, validate, hf] at h
  | some e =>
    refine ⟨e.1, e.2, (mem_edges g e.1 e.2).mp (List.mem_of_find?_eq_some hf), ?_, ?_⟩
    · simpa using List.find?_some hf
    · simpa [adapt, validate, hf] using h.symm

/-- Every independently valid rank witness is accepted. -/
theorem ranked_accepted {g : Graph n} (h : Ranked g) (i : Fin n) :
    adapt g i = .ok (unroll g (g.rank i + 1) i) := by
  simp [adapt, (validate_iff g).mpr h]

/-- Expression expansion reads exactly its syntactic hole occurrences. -/
theorem expand_congr (e : Expr n) (f f' : Fin n → Polynomial)
    (h : ∀ j ∈ e.refs, f j = f' j) : e.expand f = e.expand f' := by
  induction e with
  | tokens p => rfl
  | hole i => exact h i (by simp [Expr.refs])
  | alt a b ia ib =>
    simp only [Expr.expand]
    rw [ia (fun j hj => h j (by simp [Expr.refs, hj])),
      ib (fun j hj => h j (by simp [Expr.refs, hj]))]
  | joint a b ia ib =>
    simp only [Expr.expand]
    rw [ia (fun j hj => h j (by simp [Expr.refs, hj])),
      ib (fun j hj => h j (by simp [Expr.refs, hj]))]

/-- Once the rank bound is exceeded, even order and multiplicity stop changing. -/
theorem unroll_stable {g : Graph n} (h : Ranked g) (k m : Nat) (i : Fin n)
    (hk : g.rank i < k) (hm : g.rank i < m) : unroll g k i = unroll g m i := by
  induction k generalizing m i with
  | zero => omega
  | succ k ih =>
    cases m with
    | zero => omega
    | succ m =>
      apply expand_congr
      intro j hj
      have hd := h i j hj
      exact ih m j (by omega) (by omega)

/-- The computed polynomials satisfy every graph equation exactly. Stage zero cannot
silently drop a dependency on any accepted graph. This is finite unrolling, not a
claim that cyclic fixed-point equations have the same finite-carrier semantics. -/
theorem unroll_equation {g : Graph n} (h : Ranked g) (i : Fin n) :
    unroll g (g.rank i + 1) i =
      (g.body i).expand (fun j => unroll g (g.rank j + 1) j) := by
  apply expand_congr
  intro j hj
  exact unroll_stable h _ _ j (h i j hj) (by omega)

end Nanodregg.Lang.Contextual.Acyclic
