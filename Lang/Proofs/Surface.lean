/-
# Lang.Proofs.Surface — the authoring surface reinterprets no core text, a layer keeps its super's
laws, and a bounded argument is refused by its name (LANG-50)

* `read_print_surface`: every text the one printer writes is read by the surface exactly as the
  core reader reads it, so the surface is a superset that never re-reads a core package. (The other
  direction, a surface text lowering to EXACTLY a shipped core, is per text: the sims' G0s, A0s and
  E0s rows, each with a plant, and the journey's LT0s.)
* `layer_keeps_laws`: a layer that lowers has every law of its super, imports exactly the super,
  shares its state and relations, and its body is `extend (ref 0) fs` with no field named like a
  super's law; `layer_law_is_super`: so the law field of the extended record IS the super's.
* `boundCheck_in` / `boundCheck_out` / `Bound.cond_nat` / `Bound.cond_bytes`: the check before a
  method's body passes exactly the in-bound arguments to the body, and refuses the first field out
  of its bound by the name `"f lo..hi"` (law 7).
-/
import Lang.Surface
import Lang.Proofs.Print
import Lang.Proofs.BigStep

namespace Nanodregg.Lang.Surface

open Read (SExp)
open Print

/-! ## The surface reads every printed core text as the core reader does -/

theorem read_print_surface {p : Package} {s : String} (h : Print.package p = some s) :
    readPackage s = liftR (Read.readPackage s) := by
  simp only [Print.package, bind, Option.bind_eq_some_iff] at h
  obtain ⟨xs, hxs, h⟩ := h
  split at h
  · rename_i hf
    obtain ⟨hn, hw⟩ := fitsB_iff.mp hf
    simp only [pure, Option.some.injEq] at h; subst h
    simp only [sectionsSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hxs
    obtain ⟨xS, hS, xI, hI, xm, hm, xl, hlw, xR, hR, xB, hB, rfl⟩ := hxs
    have hok : OkL (atom "package" :: [list (atom "imports" :: p.imports.map fun i => .str 0 (hex i)),
        list [atom "state", xS], list [atom "iface", xI], list (atom "methods" :: xm),
        list (atom "laws" :: xl), list (atom "rels" :: xR), list [atom "body", xB]]) :=
      .cons (kw_ok _) (.cons (.list (.cons (kw_ok _) (imports_ok _)))
        (.cons (.list (.cons (kw_ok _) (.cons (tySx_ok _ hS) .nil)))
        (.cons (.list (.cons (kw_ok _) (.cons (tySx_ok _ hI) .nil)))
        (.cons (.list (.cons (kw_ok _) (labels_ok _ hm)))
        (.cons (.list (.cons (kw_ok _) (labels_ok _ hlw)))
        (.cons (.list (.cons (kw_ok _) (rels_ok _ hR)))
        (.cons (.list (.cons (kw_ok _) (.cons (termSx_ok _ 0 hB) .nil))) .nil)))))))
    obtain ⟨ys, hy, hsame⟩ := parse_layout (sep := ['\n', ' ', ' ']) ⟨by decide, by decide⟩ hok hn hw
    obtain ⟨y0, ys', rfl, h0, hl⟩ := sameL_cons hsame
    obtain ⟨y1, ys'', rfl, h1, _⟩ := sameL_cons hl
    obtain ⟨r0, rfl⟩ := same_atom h0
    obtain ⟨q1, zs, rfl, hz⟩ := same_list h1
    obtain ⟨z0, zs', rfl, hz0, _⟩ := sameL_cons hz
    obtain ⟨r1, rfl⟩ := same_atom hz0
    have hc : isCore (.list 0 (.atom r0 "package" :: .list q1 (.atom r1 "imports" :: zs') :: ys'')) = true := rfl
    simp only [readPackage, readWith, Read.readPackage, hy, liftR, bind, Except.bind, readSExpWith, hc, if_true]
    cases Read.package (.list 0 (.atom r0 "package" :: .list q1 (.atom r1 "imports" :: zs') :: ys'')) <;> rfl
  · cases h

/-! ## A layer keeps its super's laws -/

theorem checkAdds_ok {posOf : Label → Nat} {sup : Package} :
    ∀ {adds : List (Label × Ty × Term)}, checkAdds posOf sup adds = .ok () →
      ∀ a ∈ adds, a.1 ∉ sup.laws ∧ ∀ r ∈ sup.rels, r.2.guard ≠ some a.1
  | [], _, a, ha => by simp at ha
  | (ℓ, T, t) :: rest, h, a, ha => by
    unfold checkAdds at h
    split at h
    · cases h
    · rename_i hl
      split at h
      · cases h
      · rename_i hg
        have hl' : ℓ ∉ sup.laws := by simpa using hl
        have hg' : ∀ r ∈ sup.rels, r.2.guard ≠ some ℓ := by
          intro r hr he; exact hg (List.any_eq_true.mpr ⟨r, hr, by simp [he]⟩)
        have hrest : checkAdds posOf sup rest = .ok () := by
          split at h
          · split at h
            · exact h
            · cases h
          · exact h
        rcases List.mem_cons.1 ha with rfl | ha
        · exact ⟨hl', hg'⟩
        · exact checkAdds_ok hrest a ha

theorem find?_none {α : Type} {ℓ : Label} : ∀ {xs : List (Label × α)}, (∀ e ∈ xs, e.1 ≠ ℓ) → Row.find? ℓ xs = none
  | [], _ => rfl
  | (k, a) :: rest, h => by
    have hk : k ≠ ℓ := h (k, a) (List.mem_cons_self ..)
    simp only [Row.find?, show ¬ ℓ = k from fun e => hk e.symm, if_false]
    exact find?_none fun e he => h e (List.mem_cons_of_mem _ he)

theorem find?_put_ne {α : Type} {ℓ k : Label} {a : α} (hk : ℓ ≠ k) :
    ∀ xs : List (Label × α), Row.find? ℓ (Row.put k a xs) = Row.find? ℓ xs
  | [] => by simp [Row.put, Row.find?, hk]
  | (j, b) :: rest => by
    unfold Row.put
    split
    · simp [Row.find?, hk]
    · split
      · rename_i e; subst e; simp [Row.find?, hk]
      · by_cases hj : ℓ = j
        · simp [Row.find?, hj]
        · simp [Row.find?, hj, find?_put_ne hk rest]

theorem find?_merge_ne {α : Type} {ℓ : Label} :
    ∀ (base over : List (Label × α)), (∀ e ∈ over, e.1 ≠ ℓ) → Row.find? ℓ (Row.merge base over) = Row.find? ℓ base
  | base, [], _ => rfl
  | base, (k, a) :: rest, h => by
    have hk : ℓ ≠ k := fun e => h (k, a) (List.mem_cons_self ..) e.symm
    simp only [Row.merge]
    rw [find?_merge_ne _ rest (fun e he => h e (List.mem_cons_of_mem _ he)), find?_put_ne hk]

/-- A layer that lowers keeps every law of its super, imports exactly the super, shares its state
and relations, and adds no field named like a super's law: its body extends the super's with
fields `fs` none of which is a super law. -/
theorem layer_keeps_laws {posOf : Label → Nat} {sid : ByteArray} {sup : Package}
    {adds : List (Label × Ty × Term)} {addLaws addMethods : List Label} {p : Package}
    (h : layerOf posOf sid sup adds addLaws addMethods = .ok p) :
    (∀ ℓ ∈ sup.laws, ℓ ∈ p.laws) ∧ p.imports = [sid] ∧ p.state = sup.state ∧ p.rels = sup.rels ∧
      ∃ fs, p.body = .extend (.ref 0) fs ∧ ∀ ℓ ∈ sup.laws, ∀ e ∈ fs, e.1 ≠ ℓ := by
  unfold layerOf at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i u hc
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hadds := checkAdds_ok hc
    refine ⟨?_, rfl, rfl, rfl, _, rfl, ?_⟩
    · intro ℓ hℓ
      have hm : (ℓ, ()) ∈ Row.sort ((sup.laws ++ addLaws).map (·, ())) :=
        (Row.sort_perm _).mem_iff.mpr (List.mem_map.mpr ⟨ℓ, List.mem_append_left _ hℓ, rfl⟩)
      exact List.mem_map.mpr ⟨(ℓ, ()), hm, rfl⟩
    · intro ℓ hℓ e he heq
      have he' := (Row.sort_perm _).mem_iff.mp he
      obtain ⟨⟨k, T, t⟩, hk, rfl⟩ := List.mem_map.mp he'
      exact (hadds _ hk).1 (heq ▸ hℓ)

/-- What `extend (ref 0) fs` makes of the super's record `gs` (the `Ext` rule): its law field is
the super's own, whatever the layer added. -/
theorem layer_law_is_super {posOf : Label → Nat} {sid : ByteArray} {sup : Package}
    {adds : List (Label × Ty × Term)} {addLaws addMethods : List Label} {p : Package}
    (h : layerOf posOf sid sup adds addLaws addMethods = .ok p) {ℓ : Label} (hℓ : ℓ ∈ sup.laws) :
    ∃ fs, p.body = .extend (.ref 0) fs ∧
      ∀ (gs : List (Label × (Term × Env))) (env : Env), Row.find? ℓ (Row.merge gs (suspend env fs)) = Row.find? ℓ gs := by
  obtain ⟨-, -, -, -, fs, hb, hfs⟩ := layer_keeps_laws h
  refine ⟨fs, hb, fun gs env => find?_merge_ne gs _ ?_⟩
  intro e he
  simp only [suspend, List.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  exact hfs ℓ hℓ f hf

/-- A layer keeps its super's method INDICES: the super's methods are a prefix of the layer's, so
an invoke of method `i` of the super is method `i` of the layer, and a super law that names a
method by index (`machine`, `(index m)`) still judges the same method. -/
theorem layer_keeps_indices {posOf : Label → Nat} {sid : ByteArray} {sup : Package}
    {adds : List (Label × Ty × Term)} {addLaws addMethods : List Label} {p : Package}
    (h : layerOf posOf sid sup adds addLaws addMethods = .ok p) : ∃ xs, p.methods = sup.methods ++ xs := by
  unfold layerOf at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨_, rfl⟩

/-- No super guard is overridden either. -/
theorem layer_keeps_guards {posOf : Label → Nat} {sid : ByteArray} {sup : Package}
    {adds : List (Label × Ty × Term)} {addLaws addMethods : List Label} {p : Package}
    (h : layerOf posOf sid sup adds addLaws addMethods = .ok p) :
    ∃ fs, p.body = .extend (.ref 0) fs ∧ ∀ r ∈ sup.rels, ∀ e ∈ fs, r.2.guard ≠ some e.1 := by
  unfold layerOf at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i u hc
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨_, rfl, fun r hr e he => ?_⟩
    have he' := (Row.sort_perm _).mem_iff.mp he
    obtain ⟨⟨k, T, t⟩, hk, rfl⟩ := List.mem_map.mp he'
    exact (checkAdds_ok hc _ hk).2 r hr

/-- The evaluator's form (M3 of the vacuity read; `ext_sel_go` is its recursion): extending ANY value (a record, or a knot, which
`Ext` unrolls) by fields none of which is `ℓ` leaves the selection of `ℓ` exactly as it was. So the
super's law, selected from the layer's body, means what it meant in the super. -/
theorem ext_sel_go {lib : List Term} {ℓ : Label} :
    ∀ {v : Val} {fs : List (Label × Term)} {env : Env} {o : Except Fault Val}, Ext lib v fs env o →
      ∀ {w : Val}, o = .ok w → (∀ e ∈ fs, e.1 ≠ ℓ) → ∀ {r : Except Fault Val}, (Sel lib w ℓ r ↔ Sel lib v ℓ r)
  | .record gs, fs, env, _, .record, w, ho, hfs, r => by
    cases ho
    have hf : Row.find? ℓ (Row.merge gs (suspend env fs)) = Row.find? ℓ gs := by
      refine find?_merge_ne gs _ ?_
      intro e he
      simp only [suspend, List.mem_map] at he
      obtain ⟨f, hf, rfl⟩ := he
      exact hfs f hf
    constructor
    · intro h; cases h with
      | field hfind hb => exact .field (hf ▸ hfind) hb
    · intro h; cases h with
      | field hfind hb => exact .field (hf.symm ▸ hfind) hb
  | .knot b kenv, fs, env, _, .knot hb hx, w, ho, hfs, r => by
    have ih := ext_sel_go hx ho hfs (r := r)
    constructor
    · intro h; exact .knot hb (ih.mp h)
    · intro h; cases h with
      | knot hb' hs => cases bigStep_deterministic hb hb'; exact ih.mpr hs
      | knotE hb' => cases bigStep_deterministic hb hb'
  | .knot _ _, _, _, _, .knotE _, _, ho, _, _ => by cases ho

theorem ext_sel_untouched {lib : List Term} {ℓ : Label} {v : Val} {fs : List (Label × Term)} {env : Env} {w : Val}
    (hx : Ext lib v fs env (.ok w)) (hfs : ∀ e ∈ fs, e.1 ≠ ℓ) {r : Except Fault Val} :
    Sel lib w ℓ r ↔ Sel lib v ℓ r :=
  ext_sel_go hx rfl hfs

/-! ## A bounded argument is refused by its name -/

/-- The first bound holds: the check goes on to the next. -/
theorem boundCheck_in {lib : List Term} {env : Env} {res : Ty} {b : Bound} {bs : List Bound} {body : Term}
    {r : Except Fault Val} (hc : BigStep lib env b.cond (.ok (.bool true))) :
    BigStep lib env (boundCheck res (b :: bs) body) r ↔ BigStep lib env (boundCheck res bs body) r := by
  simp only [boundCheck]
  constructor
  · intro h
    cases h with
    | iteT _ ha => exact ha
    | iteF hf _ => cases bigStep_deterministic hc hf
    | iteE he => cases bigStep_deterministic hc he
  · exact fun h => .iteT hc h

/-- The first bound fails: the run is refused by exactly its name, and nothing else. -/
theorem boundCheck_out {lib : List Term} {env : Env} {res : Ty} {b : Bound} {bs : List Bound} {body : Term}
    {r : Except Fault Val} (hc : BigStep lib env b.cond (.ok (.bool false))) :
    BigStep lib env (boundCheck res (b :: bs) body) r ↔ r = .error (.refused b.name.toUTF8) := by
  simp only [boundCheck]
  constructor
  · intro h
    cases h with
    | iteT ht _ => cases bigStep_deterministic hc ht
    | iteF _ hb => exact bigStep_refuse_iff.mp hb
    | iteE he => cases bigStep_deterministic hc he
  · intro h; subst h; exact .iteF hc .refuse

/-- With every bound holding, the check is the body. -/
theorem boundCheck_all_in {lib : List Term} {env : Env} {res : Ty} {body : Term} {r : Except Fault Val} :
    ∀ (bs : List Bound), (∀ b ∈ bs, BigStep lib env b.cond (.ok (.bool true))) →
      (BigStep lib env (boundCheck res bs body) r ↔ BigStep lib env body r)
  | [], _ => Iff.rfl
  | b :: rest, h => (boundCheck_in (h b (List.mem_cons_self ..))).trans
      (boundCheck_all_in rest fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

/-- A natural bound means `lo ≤ n ≤ hi` of the field's value. -/
theorem Bound.cond_nat {lib : List Term} {env : Env} {b : Bound} {n : Nat} (hb : b.isBytes = false)
    (hx : BigStep lib env (pathT b.path) (.ok (.nat n))) :
    BigStep lib env b.cond (.ok (.bool (decide (b.lo ≤ n ∧ n ≤ b.hi)))) := by
  simp only [Bound.cond, hb, Bool.false_eq_true, if_false]
  by_cases hlo : b.lo ≤ n
  · have h1 : BigStep lib env (.prim .le (.nat b.lo) (pathT b.path)) (.ok (.bool true)) := by
      have := BigStep.prim (p := .le) (BigStep.nat (n := b.lo)) hx (by simp [primEval])
      simpa [primEval, hlo] using this
    have h2 : BigStep lib env (.prim .le (pathT b.path) (.nat b.hi)) (.ok (.bool (decide (n ≤ b.hi)))) := by
      have := BigStep.prim (p := .le) hx (BigStep.nat (n := b.hi)) (by simp [primEval])
      simpa [primEval] using this
    have := BigStep.iteT (b := .bool false) h1 h2
    simpa [hlo] using this
  · have h1 : BigStep lib env (.prim .le (.nat b.lo) (pathT b.path)) (.ok (.bool false)) := by
      have := BigStep.prim (p := .le) (BigStep.nat (n := b.lo)) hx (by simp [primEval])
      simpa [primEval, hlo] using this
    have := BigStep.iteF (a := .prim .le (pathT b.path) (.nat b.hi)) h1 (BigStep.bool (b := false))
    simpa [hlo] using this

/-- A byte-string bound means `lo ≤ size ≤ hi` of the field's value. -/
theorem Bound.cond_bytes {lib : List Term} {env : Env} {b : Bound} {a : ByteArray} (hb : b.isBytes = true)
    (hx : BigStep lib env (pathT b.path) (.ok (.bytes a))) :
    BigStep lib env b.cond (.ok (.bool (decide (b.lo ≤ a.size ∧ a.size ≤ b.hi)))) := by
  have lenLe (m : Nat) : BigStep lib env (.prim .lenLe (pathT b.path) (.nat m)) (.ok (.bool (decide (a.size ≤ m)))) := by
    have := BigStep.prim (p := .lenLe) hx (BigStep.nat (n := m)) (by simp [primEval])
    simpa [primEval] using this
  simp only [Bound.cond, hb, if_true]
  by_cases h0 : b.lo = 0
  · simp only [h0, if_true]
    simpa using lenLe b.hi
  · simp only [h0, if_false]
    by_cases hs : a.size ≤ b.lo - 1
    · have h1 := lenLe (b.lo - 1)
      simp only [hs, decide_true] at h1
      have := BigStep.iteT (b := .prim .lenLe (pathT b.path) (.nat b.hi)) h1 (BigStep.bool (b := false))
      have : ¬ b.lo ≤ a.size := by omega
      simpa [this] using ‹BigStep lib env (.ite _ (.bool false) _) _›
    · have h1 := lenLe (b.lo - 1)
      simp only [hs, decide_false] at h1
      have := BigStep.iteF (a := .bool false) h1 (lenLe b.hi)
      have hl : b.lo ≤ a.size := by omega
      simpa [hl] using this

end Nanodregg.Lang.Surface
