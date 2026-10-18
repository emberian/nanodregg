/-
# Lang.Proofs.StdRun — a generated machine method, run: it lands where its edge says (LANG-53)

`Lang.Proofs.Std` proves what an admitted machine LAW implies and that `stepTo`'s target lookup takes
every declared edge (`stepTo_takes_every_edge`). This module runs the generated METHOD as the
receiver runs it (`apply4 g ℓm` over rows, state, argument and request, the env `runSetup` builds) over
the reference semantics: `stepTo_moves` (the state field lands at the edge's target), `stepTo_keeps`
(every other field kept), `stepTo_stays` (off every edge the field stays, and `machine_invoke` then
refuses), `stepTo_run_moves` (the CEK machine returns exactly that). Its own module so that the
reference-semantics completeness (`Lang.Proofs.Complete`) and `Lang.Program` do not widen the import
cone of every consumer of `Lang.Proofs.Std`. Teeth at the end: kernel-evaluated machine runs.
-/
import Lang.Proofs.Std
import Lang.Proofs.Complete
import Lang.Proofs.Row
import Lang.Program

namespace Nanodregg.Lang.Std

open Nanodregg.Lang

variable {lib : List Term}

/-! ## The machine's method, run: `stepTo` moves the field along the edge (cv 01a14b36-6da2) -/

/-- Selecting a field of record data put into the machine (`toVal`) means the field's data. -/
theorem sel_toVal {d x : Data} {ℓ : Label} (h : d.field ℓ = some x) : Sel lib d.toVal ℓ (.ok x.toVal) := by
  cases d with
  | record fs =>
    simp only [Data.field] at h
    simp only [Data.toVal]
    have hf : ∀ {fs : List (Label × Data)}, Row.find? ℓ fs = some x →
        Row.find? ℓ (Data.rowToVal fs) = some (.var 0, [x.toVal]) := by
      intro fs
      induction fs with
      | nil => simp [Row.find?]
      | cons p fs ih =>
        obtain ⟨k, e⟩ := p
        intro hp
        simp only [Data.rowToVal, Row.find?] at hp ⊢
        split at hp
        · cases hp; rw [if_pos ‹_›]
        · rw [if_neg ‹_›]; exact ih hp
    exact .field (hf h) (.var rfl)
  | nat _ | bool _ | bytes _ | digest _ | inj _ _ => simp [Data.field] at h

/-- A row whose every value is a function of its key finds, at a present key, that key's value. -/
theorem find_keyed {β : Type} {α : Type} (F : Label → β) {x : Label} :
    ∀ {l : List (Label × α)}, x ∈ l.map (·.1) → Row.find? x (l.map fun p => (p.1, F p.1)) = some (F x)
  | [], h => by simp at h
  | (k, a) :: l, h => by
    simp only [List.map_cons, Row.find?]
    by_cases hk : x = k
    · subst hk; simp
    · rw [if_neg hk]
      simp only [List.map_cons, List.mem_cons] at h
      exact find_keyed F (h.resolve_left hk)

/-- The method `stepLaw` builds, applied as the receiver applies a method (`apply4`: rows,
state, argument, request bound as `var 3 … var 0`) from wherever its closure came (`M`, closing over
any `cenv`): the result's state field `f` means the target of `f`'s current state `x`. -/
theorem stepLaw_moves {row : List (Label × Ty)} {f : Label} {states : List Label} {i : Nat}
    {es : List (Label × Nat × Label)} {x : Label} {sd u : Data} {rws ad rq : Val} {E cenv : Env}
    {M b : Term} (hb : stepLaw (.record row) f states i es = .lam (.record []) b)
    (hM : BigStep lib (rq :: ad :: sd.toVal :: rws :: E) M (.ok (.clo b cenv)))
    (hf : f ∈ row.map (·.1)) (hx : x ∈ states) (hs : sd.field f = some (.inj x u)) :
    BigStep lib (rq :: ad :: sd.toVal :: rws :: E)
      (.get (.get (.app (.app (.app (.app M (.var 3)) (.var 2)) (.var 1)) (.var 0)) "state") f)
      (.ok (.inj (stepTarget es i x) (.record []))) := by
  simp only [stepLaw, Term.lam.injEq, true_and] at hb
  subst hb
  generalize hN : Term.case (.get (.var 2) f) _ = next at hM
  generalize hF : row.map (fun p => (p.1, if p.1 = f then next else Term.get (.var 2) p.1)) = fields at hM
  generalize hE : rq :: ad :: sd.toVal :: rws :: cenv = E1
  have hst : BigStep lib (rq :: ad :: sd.toVal :: rws :: E)
      (.get (.app (.app (.app (.app M (.var 3)) (.var 2)) (.var 1)) (.var 0)) "state")
      (.ok (.record (suspend E1 fields))) := by
    subst hE hF
    exact .get (.app (.app (.app (.app hM (.var rfl) .lam) (.var rfl) .lam) (.var rfl) .lam) (.var rfl) .record)
      (.field (by simp [suspend, Row.find?]) .record)
  refine .get hst (.field (find_suspend (t := next) ?_) ?_)
  · subst hF
    simpa using find_keyed (fun k => if k = f then next else Term.get (.var 2) k) hf
  · subst hN hE
    have hsel : Sel lib sd.toVal f (.ok (.inj x u.toVal)) := sel_toVal hs
    have hmem : x ∈ (Row.sort (states.map fun x => (x, ()))).map (·.1) := by
      rw [((Row.sort_perm _).map _).mem_iff]; simpa using hx
    have hrec : ∀ env : Env, BigStep lib env (.record []) (.ok (.record [])) := fun _ => .record
    refine .case (.get (.var rfl) hsel) ?_ (.inj (A := stateTy states) (hrec _))
    simpa using find_keyed (fun k => Term.inj (stateTy states) (stepTarget es i k) (.record [])) hmem

/-- And every other field of the state is kept. -/
theorem stepLaw_keeps {row : List (Label × Ty)} {f ℓ : Label} {states : List Label} {i : Nat}
    {es : List (Label × Nat × Label)} {sd z : Data} {rws ad rq : Val} {E cenv : Env}
    {M b : Term} (hb : stepLaw (.record row) f states i es = .lam (.record []) b)
    (hM : BigStep lib (rq :: ad :: sd.toVal :: rws :: E) M (.ok (.clo b cenv)))
    (hl : ℓ ∈ row.map (·.1)) (hne : ℓ ≠ f) (hs : sd.field ℓ = some z) :
    BigStep lib (rq :: ad :: sd.toVal :: rws :: E)
      (.get (.get (.app (.app (.app (.app M (.var 3)) (.var 2)) (.var 1)) (.var 0)) "state") ℓ)
      (.ok z.toVal) := by
  simp only [stepLaw, Term.lam.injEq, true_and] at hb
  subst hb
  generalize hN : Term.case (.get (.var 2) f) _ = next at hM
  generalize hF : row.map (fun p => (p.1, if p.1 = f then next else Term.get (.var 2) p.1)) = fields at hM
  generalize hE : rq :: ad :: sd.toVal :: rws :: cenv = E1
  have hst : BigStep lib (rq :: ad :: sd.toVal :: rws :: E)
      (.get (.app (.app (.app (.app M (.var 3)) (.var 2)) (.var 1)) (.var 0)) "state")
      (.ok (.record (suspend E1 fields))) := by
    subst hE hF
    exact .get (.app (.app (.app (.app hM (.var rfl) .lam) (.var rfl) .lam) (.var rfl) .lam) (.var rfl) .record)
      (.field (by simp [suspend, Row.find?]) .record)
  refine .get hst (.field (find_suspend (t := .get (.var 2) ℓ) ?_) ?_)
  · subst hF
    simpa [hne] using find_keyed (fun k => if k = f then next else Term.get (.var 2) k) hl
  · subst hE
    exact .get (.var rfl) (sel_toVal hs)

theorem mapM_ok_each {ε α β : Type} {g : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM g = .ok l' → ∀ a ∈ l, ∃ b ∈ l', g a = .ok b
  | [], _, _, a, ha => by simp at ha
  | c :: l, l', h, a, ha => by
    rw [List.mapM_cons] at h
    cases hc : g c with
    | error e => rw [hc] at h; cases h
    | ok b =>
      rw [hc] at h
      cases hl : l.mapM g with
      | error e => simp [hl, bind, Except.bind] at h
      | ok bs =>
        simp only [hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [List.mem_cons] at ha ⊢
        rcases ha with rfl | ha
        · exact ⟨b, .inl rfl, hc⟩
        · obtain ⟨b', hb', hg⟩ := mapM_ok_each hl a ha
          exact ⟨b', .inr hb', hg⟩

/-- A resolved edge: `resolveEdges` resolves every label edge to its method's index, and names only
states it knows. -/
theorem resolveEdges_mem {states methods : List Label} {x m y : Label} {i : Nat}
    {edges : List (Label × Label × Label)} {es : List (Label × Nat × Label)}
    (h : resolveEdges states methods edges = .ok es) (he : (x, m, y) ∈ edges)
    (hi : methodIndex methods m = some i) : (x, i, y) ∈ es ∧ x ∈ states := by
  obtain ⟨b, hb, hg⟩ := mapM_ok_each h _ he
  simp only [need, bind, Except.bind, pure, Except.pure, hi] at hg
  by_cases hx : states.contains x = true
  · by_cases hy : states.contains y = true
    · rw [if_pos hx, if_pos hy] at hg
      simp only [Except.ok.injEq] at hg
      subst hg
      exact ⟨hb, by simpa using hx⟩
    · rw [if_pos hx, if_neg hy] at hg
      cases hg
  · rw [if_neg hx] at hg
    cases hg

/-- A package body (`lib[g]`, a record) whose field `ℓm` is the method `t`: the receiver's
`apply4 g ℓm` selects it, and the selection means `t`'s closure over the empty environment. -/
theorem sel_method {g : Nat} {ℓm : Label} {fs : List (Label × Term)} {A : Ty} {b : Term} {env : Env}
    (hg : lib[g]? = some (.record fs)) (hm : Row.find? ℓm fs = some (.lam A b)) :
    BigStep lib env (.get (.ref g) ℓm) (.ok (.clo b [])) :=
  .get (.ref hg .record) (.field (find_suspend hm) .lam)

/-- **A generated machine method moves its field along the edge it names** (cv 01a14b36-6da2): for a
method `stepTo` generates, installed as field `ℓm` of the package body at `lib[g]` and run as the
receiver runs it (`apply4 g ℓm` over rows, state, argument and request), from a state whose field
`f` is `x`, every declared edge `(x, m, y)` lands: the result's state field `f` means `y`. With
`stepTo_takes_every_edge` (the law admits exactly these moves) the machine law and the generated
methods agree at run level. -/
theorem stepTo_moves {S : Ty} {f : Label} {states methods : List Label} {m : Label}
    {edges : List (Label × Label × Label)} {t : Term} {row : List (Label × Ty)} {x y : Label}
    {g : Nat} {ℓm : Label} {fs : List (Label × Term)} {sd u : Data} {rws ad rq : Val} {E : Env}
    (h : stepTo S f states methods m edges = .ok t) (hS : S = .record row) (hf : f ∈ row.map (·.1))
    (he : (x, m, y) ∈ edges) (hs : sd.field f = some (.inj x u))
    (hg : lib[g]? = some (.record fs)) (hm : Row.find? ℓm fs = some t) :
    BigStep lib (rq :: ad :: sd.toVal :: rws :: E) (.get (.get (apply4 g ℓm) "state") f)
      (.ok (.inj y (.record []))) := by
  obtain ⟨i, es, hi, hes, rfl, hedge⟩ := stepTo_takes_every_edge h
  obtain ⟨hmem, hx⟩ := resolveEdges_mem hes he hi
  subst hS
  rw [← hedge x y hmem]
  exact stepLaw_moves rfl (sel_method hg hm) hf hx hs

/-- **And every other field is kept.** -/
theorem stepTo_keeps {S : Ty} {f ℓ : Label} {states methods : List Label} {m : Label}
    {edges : List (Label × Label × Label)} {t : Term} {row : List (Label × Ty)}
    {g : Nat} {ℓm : Label} {fs : List (Label × Term)} {sd z : Data} {rws ad rq : Val} {E : Env}
    (h : stepTo S f states methods m edges = .ok t) (hS : S = .record row) (hl : ℓ ∈ row.map (·.1))
    (hne : ℓ ≠ f) (hs : sd.field ℓ = some z)
    (hg : lib[g]? = some (.record fs)) (hm : Row.find? ℓm fs = some t) :
    BigStep lib (rq :: ad :: sd.toVal :: rws :: E) (.get (.get (apply4 g ℓm) "state") ℓ)
      (.ok z.toVal) := by
  obtain ⟨i, es, -, -, rfl, -⟩ := stepTo_takes_every_edge h
  subst hS
  exact stepLaw_keeps rfl (sel_method hg hm) hl hne hs

/-- **The machine runs it there.** The CEK machine, run on the same selection, returns `y` under
every large enough stack bound and tick budget, and returns no other value under any. "Large
enough" is `bigStep_run`'s existential: this does not say the deployed `Bounds.stackMax` and tick
budget are large enough (the receiver's own run of the method is what meters that). -/
theorem stepTo_run_moves {S : Ty} {f : Label} {states methods : List Label} {m : Label}
    {edges : List (Label × Label × Label)} {t : Term} {row : List (Label × Ty)} {x y : Label}
    {g : Nat} {ℓm : Label} {fs : List (Label × Term)} {sd u : Data} {rws ad rq : Val} {E : Env}
    (h : stepTo S f states methods m edges = .ok t) (hS : S = .record row) (hf : f ∈ row.map (·.1))
    (he : (x, m, y) ∈ edges) (hs : sd.field f = some (.inj x u))
    (hg : lib[g]? = some (.record fs)) (hm : Row.find? ℓm fs = some t) :
    let T := Term.get (.get (apply4 g ℓm) "state") f
    let env := rq :: ad :: sd.toVal :: rws :: E
    (∃ D n, ∀ cap fuel, D ≤ cap → n < fuel → ∃ used,
        run lib cap fuel 0 (State.init T env) = .value (.inj y (.record [])) used) ∧
      ∀ cap fuel used v, run lib cap fuel 0 (State.init T env) = .value v used → v = .inj y (.record []) := by
  have hb := stepTo_moves (rws := rws) (ad := ad) (rq := rq) (E := E) h hS hf he hs hg hm
  refine ⟨bigStep_run hb, fun cap fuel used v hr => ?_⟩
  have := bigStep_deterministic (run_bigStep hr) hb
  cases this; rfl

theorem mapM_ok_back {ε α β : Type} {g : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM g = .ok l' → ∀ b ∈ l', ∃ a ∈ l, g a = .ok b
  | [], l', h, b, hb => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp at hb
  | c :: l, l', h, b, hb => by
    rw [List.mapM_cons] at h
    cases hc : g c with
    | error e => rw [hc] at h; cases h
    | ok b0 =>
      rw [hc] at h
      cases hl : l.mapM g with
      | error e => simp [hl, bind, Except.bind] at h
      | ok bs =>
        simp only [hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact ⟨c, by simp, hc⟩
        · obtain ⟨a, ha, hg⟩ := mapM_ok_back hl b hb
          exact ⟨a, by simp [ha], hg⟩

theorem methodIndex_go_ge : ∀ {xs : List Label} {j i : Nat} {m : Label},
    methodIndex.go m xs j = some i → j ≤ i
  | [], _, _, _, h => by simp [methodIndex.go] at h
  | x :: xs, j, i, m, h => by
    simp only [methodIndex.go] at h
    split at h
    · cases h; exact Nat.le_refl _
    · exact Nat.le_of_succ_le (methodIndex_go_ge h)

theorem methodIndex_go_inj : ∀ {xs : List Label} {j i : Nat} {m m' : Label},
    methodIndex.go m xs j = some i → methodIndex.go m' xs j = some i → m = m'
  | [], _, _, _, _, h, _ => by simp [methodIndex.go] at h
  | x :: xs, j, i, m, m', h, h' => by
    simp only [methodIndex.go] at h h'
    split at h <;> split at h'
    · subst_vars; rfl
    · cases h; have := methodIndex_go_ge h'; omega
    · cases h'; have := methodIndex_go_ge h; omega
    · exact methodIndex_go_inj h h'

/-- Two method labels with one index are one label. -/
theorem methodIndex_inj {methods : List Label} {m m' : Label} {i : Nat}
    (h : methodIndex methods m = some i) (h' : methodIndex methods m' = some i) : m = m' :=
  methodIndex_go_inj h h'

/-- Every resolved edge came from a label edge, by its method's index. -/
theorem resolveEdges_mem_back {states methods : List Label} {a b : Label} {k : Nat}
    {edges : List (Label × Label × Label)} {es : List (Label × Nat × Label)}
    (h : resolveEdges states methods edges = .ok es) (he : (a, k, b) ∈ es) :
    ∃ m, (a, m, b) ∈ edges ∧ methodIndex methods m = some k := by
  obtain ⟨⟨x, m, y⟩, hm, hg⟩ := mapM_ok_back h _ he
  simp only [need, bind, Except.bind, pure, Except.pure] at hg
  by_cases hx : states.contains x = true
  · by_cases hy : states.contains y = true
    · rw [if_pos hx, if_pos hy] at hg
      cases hi : methodIndex methods m with
      | none => rw [hi] at hg; cases hg
      | some i =>
        rw [hi] at hg
        simp only [Except.ok.injEq, Prod.mk.injEq] at hg
        obtain ⟨rfl, rfl, rfl⟩ := hg
        exact ⟨m, hm, hi⟩
    · rw [if_pos hx, if_neg hy] at hg; cases hg
  · rw [if_neg hx] at hg; cases hg

/-- **Off every edge, the generated method keeps the field** (then `machine` refuses the invoke,
`machine_invoke`): from a state `x` that no edge of method `m` leaves, the result's state field `f`
means `x` again. -/
theorem stepTo_stays {S : Ty} {f : Label} {states methods : List Label} {m : Label}
    {edges : List (Label × Label × Label)} {t : Term} {row : List (Label × Ty)} {x : Label}
    {g : Nat} {ℓm : Label} {fs : List (Label × Term)} {sd u : Data} {rws ad rq : Val} {E : Env}
    (h : stepTo S f states methods m edges = .ok t) (hS : S = .record row) (hf : f ∈ row.map (·.1))
    (hno : ∀ y, (x, m, y) ∉ edges) (hx : x ∈ states) (hs : sd.field f = some (.inj x u))
    (hg : lib[g]? = some (.record fs)) (hm : Row.find? ℓm fs = some t) :
    BigStep lib (rq :: ad :: sd.toVal :: rws :: E) (.get (.get (apply4 g ℓm) "state") f)
      (.ok (.inj x (.record []))) := by
  obtain ⟨i, es, hi, hes, rfl, -⟩ := stepTo_takes_every_edge h
  have hnone : es.find? (fun (a, k, _) => a = x && k = i) = none := by
    rw [List.find?_eq_none]
    rintro ⟨a, k, b⟩ hmem hak
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hak
    obtain ⟨rfl, rfl⟩ := hak
    obtain ⟨m', hm', hi'⟩ := resolveEdges_mem_back hes hmem
    exact hno b (methodIndex_inj hi' hi ▸ hm')
  have htgt : stepTarget es i x = x := by simp [stepTarget, hnone]
  subst hS
  rw [← htgt]
  exact stepLaw_moves rfl (sel_method hg hm) hf hx hs

end Nanodregg.Lang.Std

namespace Nanodregg.Lang.Std.RunTeeth

open Nanodregg.Lang Nanodregg.Lang.Std

/-! ## stepTo, run by the machine: the method moves its field along its edge (cv 01a14b36-6da2)

`Lang.Proofs.Std.stepTo_run_moves` / `stepTo_stays` say it in general; these run the CEK machine on
the selection the theorems name (`apply4` over the package body at `lib[0]`). `flip` has edges
`a → b` and `b → a` by `go`, so the moved field is not a constant; `backOnly` has only `b → a`, and
from `c` (no edge leaves it, and it is no edge's target) the method keeps `c`; `fork` has two methods leaving `a`,
`go` to `b` and `stop` to `c`, so the edge taken is the invoked method's. -/

private def MS2 : Ty := .record [("n", .nat), ("phase", stateTy ["a", "b", "c"])]
private def gen (m : Label) (edges : List (Label × Label × Label)) : Option Term :=
  (stepTo MS2 "phase" ["a", "b", "c"] ["go", "stop"] m edges).toOption
private def flip : List (Label × Label × Label) := [("a", "go", "b"), ("b", "go", "a")]
private def backOnly : List (Label × Label × Label) := [("b", "go", "a")]
private def fork : List (Label × Label × Label) := [("a", "go", "b"), ("a", "stop", "c")]
/-- Method `m` of the machine over `edges`, installed beside its sibling in the package body
`{go, stop}` at `lib[0]` and run as the receiver runs it (`apply4 0 m`) from `n = 7`, `phase = p`:
the result's state field `ℓ`. -/
private def stepRun (edges : List (Label × Label × Label)) (m ℓ p : Label) : Option Val := do
  let go ← gen "go" edges
  let stop ← gen "stop" edges
  let sd : Data := .record [("n", .nat 7), ("phase", .inj p (.record []))]
  match run [.record [("go", go), ("stop", stop)]] 64 10000 0
      (State.init (.get (.get (apply4 0 m) "state") ℓ) [.record [], .record [], sd.toVal, .record []]) with
  | .value v _ => some v
  | .fault _ _ => none
private def isInj (ℓ : Label) : Option Val → Bool
  | some (.inj m (.record [])) => m == ℓ
  | _ => false
private def isNat (n : Nat) : Option Val → Bool
  | some (.nat k) => k == n
  | _ => false

theorem stepTo_runs_edge : isInj "b" (stepRun flip "go" "phase" "a") = true := by decide +kernel
theorem stepTo_runs_back : isInj "a" (stepRun flip "go" "phase" "b") = true := by decide +kernel
theorem stepTo_runs_keeps : isNat 7 (stepRun flip "go" "n" "a") = true := by decide +kernel
theorem stepTo_off_edge_stays : isInj "c" (stepRun backOnly "go" "phase" "c") = true := by decide +kernel
theorem stepTo_runs_go : isInj "b" (stepRun fork "go" "phase" "a") = true := by decide +kernel
theorem stepTo_runs_stop : isInj "c" (stepRun fork "stop" "phase" "a") = true := by decide +kernel

end Nanodregg.Lang.Std.RunTeeth
