/-
# Lang.Proofs.Rel — a method's edits and rows, as `Lang.Rel` builds them (LANG-49)

* `editOf_spec`: an edit `editOf` accepts is exactly one of its three shapes, under the object:
  its relation's index and declaration, its key's bytes, and its act.
* `editsOf_parent`, `editsOf_under`: every row act a run returns is under the run's own object
  (the kernel's `rowParent` assertion, held by construction on the Lang side, as `callsOf_callable`
  is for `notCallable`).
* `editOf_amt`: an insert's or upsert's `amt` is `amtOf` of a value whose encoding is the row's
  bytes; `editOf_retract_allowed`: a retract comes only from a relation declared `retract`.
* `relReads_points`: the point slots of a relation's reads hold exactly the caller's pins under
  `(self, i)`, in pin order, and `none` after them.
* `keyOf_keyBytes`: a key's bytes read back to the key (`keyOf_keyBytes_fields` without premises:
  to the key's declared fields, sorted).
* `guard_never_stuck`, `guardEdits_never_stuck`: the guard `guardEdits` runs on each edit never
  ends `stuck`, as `runLaw_never_stuck` for laws: the guard field is typed `guardTy` at install
  (`checkRel`) and the edit data conforms to the relation's edit type (`editsOf_conforms`).
-/
import Lang.Proofs.LawRun
import Lang.Proofs.Check
import Lang.Rel

namespace Nanodregg.Lang

open Nanodregg.Kernel Nanodregg.Kernel.Receive

section
variable {D : Type}

/-! ## One edit -/

/-- **What `editOf` accepts**: the edit names relation `x.label` (its index `x.rel`, its declaration
`x.decl`), its slot is the row under `self` at its key's bytes, and it is an insert or an upsert of
a value with bytes (`amt` that value's sum column), or a retract of a relation declared
`retract`. -/
theorem editOf_spec {rels : List (Label × RelDecl)} {self : D} {s : Label} {e : Data} {x : Edit D}
    (h : editOf rels self s e = .ok x) :
    e = .inj x.label x.data ∧ relIndex rels x.label = some x.rel ∧ Row.find? x.label rels = some x.decl ∧
    ∃ key k, keyBytes x.decl key = some k ∧ x.slot = .row ⟨self, x.rel, k⟩ ∧
      ((∃ v b, x.data = .inj "insert" (.record [("key", key), ("val", v)]) ∧
          Wire.encodeData x.decl.val v = some b ∧ x.act = .insert (amtOf x.decl v) b) ∨
       (∃ v b, x.data = .inj "upsert" (.record [("key", key), ("val", v)]) ∧
          Wire.encodeData x.decl.val v = some b ∧ x.act = .upsert (amtOf x.decl v) b) ∨
       (x.data = .inj "retract" (.record [("key", key)]) ∧ x.decl.retract = true ∧ x.act = .retract)) := by
  unfold editOf at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals
    cases h
    first
      | (rename_i hk _ _ hv
         split at hk <;> cases hk
         split at hv <;> cases hv
         first
           | exact ⟨rfl, ‹_›, ‹_›, _, _, ‹_›, rfl, .inl ⟨_, _, rfl, ‹_›, rfl⟩⟩
           | exact ⟨rfl, ‹_›, ‹_›, _, _, ‹_›, rfl, .inr (.inl ⟨_, _, rfl, ‹_›, rfl⟩)⟩)
      | (rename_i hk
         split at hk <;> cases hk
         exact ⟨rfl, ‹_›, ‹_›, _, _, ‹_›, rfl, .inr (.inr ⟨rfl, ‹_›, rfl⟩)⟩)

/-- **An insert's or upsert's `amt` is its value's sum column** (LANG-49): the row's bytes are the
data encoding, at the relation's value type, of a value whose `amtOf` is the act's `amt`. -/
theorem editOf_amt {rels : List (Label × RelDecl)} {self : D} {s : Label} {e : Data} {x : Edit D}
    {amt : Nat} {b : ByteArray} (h : editOf rels self s e = .ok x)
    (ha : x.act = .insert amt b ∨ x.act = .upsert amt b) :
    ∃ v, Wire.encodeData x.decl.val v = some b ∧ amt = amtOf x.decl v := by
  obtain ⟨_, _, _, _, _, _, _, hc⟩ := editOf_spec h
  rcases hc with ⟨v, b', -, hb, hact⟩ | ⟨v, b', -, hb, hact⟩ | ⟨-, -, hact⟩ <;>
    rcases ha with ha | ha <;> rw [hact] at ha <;> cases ha
  · exact ⟨v, hb, rfl⟩
  · exact ⟨v, hb, rfl⟩

/-- **A retract comes only from a relation declared `retract`** (LANG-49): an insert-only relation's
rows are never retracted by a method (`editOf_retract_refused` is the refusal). -/
theorem editOf_retract_allowed {rels : List (Label × RelDecl)} {self : D} {s : Label} {e : Data} {x : Edit D}
    (h : editOf rels self s e = .ok x) (ha : x.act = .retract) : x.decl.retract = true := by
  obtain ⟨_, _, _, _, _, _, _, hc⟩ := editOf_spec h
  rcases hc with ⟨v, b', -, -, hact⟩ | ⟨v, b', -, -, hact⟩ | ⟨-, hr, -⟩
  · rw [hact] at ha; cases ha
  · rw [hact] at ha; cases ha
  · exact hr

/-! ## The edits row -/

theorem editsOf_go_mem {rels : List (Label × RelDecl)} {self : D} :
    ∀ {fs : List (Label × Data)} {es : List (Edit D)}, editsOf.go rels self fs = .ok es →
      ∀ x ∈ es, ∃ s o, (s, Data.inj "some" o) ∈ fs ∧ editOf rels self s o = .ok x
  | [], es, h => by
    simp only [editsOf.go, Except.ok.injEq] at h; subst h; simp
  | (ℓ, o) :: fs, es, h => by
    simp only [editsOf.go] at h
    split at h
    · intro x hx
      obtain ⟨s, o', hm, he⟩ := editsOf_go_mem h x hx
      exact ⟨s, o', List.mem_cons_of_mem _ hm, he⟩
    · simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i y hy
        split at h
        · cases h
        · rename_i ys hys
          cases h
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ⟨ℓ, _, by simp, hy⟩
          · obtain ⟨s, o', hm, he⟩ := editsOf_go_mem hys x hx
            exact ⟨s, o', List.mem_cons_of_mem _ hm, he⟩
    · cases h

/-- Every edit of an edits row is one `editOf` accepted, from a `some` slot of the row. -/
theorem editsOf_mem {rels : List (Label × RelDecl)} {self : D} {e : Data} {es : List (Edit D)}
    (h : editsOf rels self e = .ok es) :
    ∀ x ∈ es, ∃ fs s o, e = .record fs ∧ (s, Data.inj "some" o) ∈ fs ∧ editOf rels self s o = .ok x := by
  unfold editsOf at h
  split at h
  · intro x hx
    obtain ⟨s, o, hm, he⟩ := editsOf_go_mem h x hx
    exact ⟨_, s, o, rfl, hm, he⟩
  · cases h

/-- **Every edit a run returns is under its own object** (LANG-49): `editsOf rels self` writes
each edit at the row slot `⟨self, x.rel, k⟩`, so its parent is `self`. The Lang side of the
kernel's `rowParent` assertion, as `callsOf_callable` is of `notCallable`. -/
theorem editsOf_parent {rels : List (Label × RelDecl)} {self : D} {e : Data} {es : List (Edit D)}
    (h : editsOf rels self e = .ok es) : ∀ x ∈ es, ∃ k, x.slot = .row ⟨self, x.rel, k⟩ := by
  intro x hx
  obtain ⟨-, s, o, -, -, hx'⟩ := editsOf_mem h x hx
  obtain ⟨-, -, -, -, k, -, hs, -⟩ := editOf_spec hx'
  exact ⟨k, hs⟩

/-- The kernel's form: every row act of a Lang run's edits passes `rowParent` at the run's
object (`deriveInvoke`'s check `e.1.under.1 = obj`, with `obj = r.self`). -/
theorem editsOf_under {rels : List (Label × RelDecl)} {self : D} {e : Data} {es : List (Edit D)}
    (h : editsOf rels self e = .ok es) : ∀ y ∈ es.map (fun x => (x.slot, x.act)), y.1.under.1 = self := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  obtain ⟨k, hk⟩ := editsOf_parent h x hx
  simp [hk, RowSlot.under]

theorem rowConforms_mem : ∀ {fs : List (Label × Data)} {row : List (Label × Ty)} {s : Label} {w : Data},
    RowConforms fs row → (s, w) ∈ fs → ∃ T, (s, T) ∈ row ∧ Conforms w T
  | _, _, _, _, .nil, hm => by simp at hm
  | _, _, _, _, .cons hd hr, hm => by
    rcases List.mem_cons.1 hm with he | hm
    · cases he; exact ⟨_, by simp, hd⟩
    · obtain ⟨T, hT, hc⟩ := rowConforms_mem hr hm
      exact ⟨T, List.mem_cons_of_mem _ hT, hc⟩

theorem find_map_rel (f : RelDecl → Ty) (ℓ : Label) :
    ∀ rels : List (Label × RelDecl), Row.find? ℓ (rels.map fun r => (r.1, f r.2)) = (Row.find? ℓ rels).map f
  | [] => rfl
  | (k, d) :: rels => by
    simp only [List.map_cons, Row.find?]
    split <;> simp [find_map_rel f ℓ rels]

/-- **The edit data a guard sees is a value of its relation's edit type**: an edits row of its
declared type (`e0 …`, each an option over `editTy rels`) reads into edits whose relation is
declared and whose data conforms to `relEditTy` of it. -/
theorem editsOf_conforms {rels : List (Label × RelDecl)} {self : D} {m : Nat} {e : Data}
    {es : List (Edit D)}
    (hc : Conforms e (.record ((slotLabels "e" m).map fun l => (l, optTy (editTy rels)))))
    (h : editsOf rels self e = .ok es) :
    ∀ x ∈ es, Row.find? x.label rels = some x.decl ∧ Conforms x.data (relEditTy x.decl) := by
  intro x hx
  obtain ⟨fs, s, o, rfl, hm, hx'⟩ := editsOf_mem h x hx
  obtain ⟨he, -, hd, -⟩ := editOf_spec hx'
  refine ⟨hd, ?_⟩
  cases hc with
  | record hr =>
    obtain ⟨T, hT, hw⟩ := rowConforms_mem hr hm
    obtain ⟨l, -, hl⟩ := List.mem_map.1 hT
    cases hl
    cases hw with
    | inj hf ho =>
      simp [Row.find?] at hf
      subst hf
      subst he
      cases ho with
      | inj hf' hdata =>
        have hm := find_map_rel relEditTy x.label rels
        rw [hd] at hm
        rw [hm] at hf'
        cases hf'
        exact hdata

/-! ## A relation's point reads -/

/-- The datum a point slot holds for one pin, as `relReads` builds it (its digest checks aside):
the pinned key read back, and the row's value if the pin holds a row. `none`: the pin is refused. -/
private def pinD (d : RelDecl) (p : ByteArray × Option RowLeaf) : Option Data :=
  match keyOf d d.key.length p.1 with
  | .error _ => none
  | .ok k =>
    match p.2 with
    | none => some (.record [("key", k), ("val", optD none)])
    | some (.row _ b) =>
      match Wire.decodeData d.val b with
      | .ok w => some (.record [("key", k), ("val", optD (some w))])
      | .error _ => none
    | some (.head ..) => none

/-- The first `n` slots of a record, in order. -/
private def pointSlots (n : Nat) : Data → List Data
  | .record fs => (fs.take n).map (·.2)
  | _ => []

theorem mapM_except_option {α β ε : Type} {f : α → Except ε β} {g : α → Option β}
    (hfg : ∀ a y, f a = .ok y → g a = some y) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → xs.mapM g = some ys
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i y hy
      split at h
      · cases h
      · rename_i ys' hys
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [List.mapM_cons, hfg x y hy, mapM_except_option hfg hys]

theorem zipIdx_snd {g : Nat → Data} :
    ∀ (L : List Label) (k : Nat),
      ((L.zipIdx k).map fun p => (p.1, g p.2)).map (·.2) = (List.range' k L.length).map g
  | [], _ => rfl
  | l :: L, k => by
    simp only [List.zipIdx_cons, List.map_cons, List.length_cons, List.range'_succ]
    rw [zipIdx_snd L (k + 1)]

theorem slotsD_snd (c : String) (n : Nat) (xs : List Data) :
    (slotsD c n xs).map (·.2) = (List.range n).map fun j => optD xs[j]? := by
  have h := zipIdx_snd (g := fun j => optD xs[j]?) (slotLabels c n) 0
  simp only [slotLabels, List.length_map, List.length_range] at h
  simp only [slotsD, slotLabels]
  rw [← List.range_eq_range'] at h
  exact h

theorem length_slotsD (c : String) (n : Nat) (xs : List Data) : (slotsD c n xs).length = n := by
  simp [slotsD, slotLabels]

theorem valOf_decodes {digestOf : ByteArray → Option D} {d : RelDecl} {what : String} {b : ByteArray}
    {v : Data} (h : valOf digestOf d what b = .ok v) : Wire.decodeData d.val b = .ok v := by
  unfold valOf at h
  split at h
  · rename_i v' hv; rw [checked_eq h]; exact hv
  · cases h

/-- **A relation's point slots hold exactly the caller's pins** (LANG-49): on success, the pins
under `(self, i)` fit the method's `x.points` slots, each pin reads (`pinD`: its key `keyOf` of the
pinned key bytes, its value decoded from the row's bytes), and slot `j` holds pin `j` in pin order
and `none` past the last pin. -/
theorem relReads_points {digestOf : ByteArray → Option D} {rv : RowView D} {self : D} {i : Nat}
    {ℓ : Label} {d : RelDecl} {x : RelRead} {v : Data}
    (h : relReads digestOf rv self i ℓ d x = .ok v) :
    (rv.points self i).length ≤ x.points ∧
    ∃ ps, (rv.points self i).mapM (pinD d) = some ps ∧
      pointSlots x.points v = (List.range x.points).map fun j => optD ps[j]? := by
  unfold relReads at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals
    cases h
    refine ⟨‹(rv.points self i).length ≤ x.points›, _,
      mapM_except_option (fun p y hy => ?_) ‹List.mapM _ (rv.points self i) = Except.ok _›, ?_⟩
    · repeat' split at hy
      all_goals first | (cases hy; done) | skip
      all_goals
        cases hy
        simp only [pinD, liftS_eq ‹liftS _ _ = _›, checked_eq ‹checked _ _ _ = _›]
        first
          | (simp_all; done)
          | (obtain ⟨u, hu, hs⟩ := map_some_ok ‹(some <$> valOf digestOf d _ _) = Except.ok _›
             cases hs
             simp_all [valOf_decodes hu])
    · simp only [pointSlots]
      rw [List.take_append_of_le_length (by simp [length_slotsD]), List.take_of_length_le (by simp [length_slotsD]),
        slotsD_snd]

/-! ## A key's bytes read back -/

theorem mapM_field_eq {k : Data} :
    ∀ {key : List (Label × Ty)} {vs : List (Label × Data)},
      key.mapM (fun f => (k.field f.1).map fun v => (f.1, v)) = some vs →
      vs = key.map fun f => (f.1, (k.field f.1).getD (.nat 0))
  | [], vs, h => by simp at h; subst h; rfl
  | f :: key, vs, h => by
    rw [List.mapM_cons] at h
    cases hf : k.field f.1 with
    | none => simp only [hf, Option.map, bind, Option.bind] at h; cases h
    | some w =>
      simp only [hf, Option.map, bind, Option.bind] at h
      split at h
      · cases h
      · rename_i ws hk
        simp only [pure, Option.some.injEq] at h
        subst h
        simp [hf, mapM_field_eq hk]

theorem zipIdx_mapM_wire {k : Data} :
    ∀ (key : List (Label × Ty)) (n : Nat) {ws : List (Label × Data)},
      (key.zipIdx n).mapM (fun p => (k.field p.1.1).map fun v => ("k" ++ toString p.2, v)) = some ws →
      ∃ vs, key.mapM (fun f => (k.field f.1).map fun v => (f.1, v)) = some vs ∧
        (key.zip ws).map (fun p => (p.1.1, p.2.2)) = vs
  | [], _, ws, h => by simp at h; subst h; exact ⟨[], rfl, rfl⟩
  | f :: key, n, ws, h => by
    rw [List.zipIdx_cons, List.mapM_cons] at h
    cases hf : k.field f.1 with
    | none => simp only [hf, Option.map, bind, Option.bind] at h; cases h
    | some w =>
      simp only [hf, Option.map, bind, Option.bind] at h
      split at h
      · cases h
      · rename_i ws' hk
        simp only [pure, Option.some.injEq] at h
        subst h
        obtain ⟨vs, hvs, hz⟩ := zipIdx_mapM_wire key (n + 1) hk
        refine ⟨(f.1, w) :: vs, ?_, ?_⟩
        · simp [List.mapM_cons, hf, hvs]
        · simp [hz]

/-- **A key's bytes read back to its declared fields** (LANG-49), with no premise: if `keyBytes`
writes key `k` of relation `d` (every declared field present), `keyOf` at the full key reads the
bytes back to the record of those fields' values, labels sorted (`Row.sort`). -/
theorem keyOf_keyBytes_fields {d : RelDecl} {k : Data} {b : ByteArray} (h : keyBytes d k = some b) :
    ∃ vs, d.key.mapM (fun f => (k.field f.1).map fun v => (f.1, v)) = some vs ∧
      keyOf d d.key.length b = .ok (.record (Row.sort vs)) := by
  unfold keyBytes keyToWire at h
  cases hw : d.key.zipIdx.mapM (fun p => (k.field p.1.1).map fun v => ("k" ++ toString p.2, v)) with
  | none => rw [hw] at h; cases h
  | some ws =>
    rw [hw] at h
    have hdec := Wire.decodeData_eq_ok_iff.2 h
    obtain ⟨vs, hvs, hz⟩ := zipIdx_mapM_wire d.key 0 hw
    refine ⟨vs, hvs, ?_⟩
    unfold keyOf
    rw [hdec, List.take_length]
    dsimp only
    rw [hz]

theorem conforms_fields : ∀ {fs : List (Label × Data)} {r : List (Label × Ty)},
    RowConforms fs r → Row.ascending r = true →
    r.map (fun f => (f.1, ((Data.record fs).field f.1).getD (.nat 0))) = fs
  | _, _, .nil, _ => rfl
  | (ℓ, v) :: fs, (_, T) :: r, .cons hd hr, ha => by
    have ih := conforms_fields hr (Wire.ascending_tail ha)
    simp only [List.map_cons, Data.field, Row.find?, if_true, Option.getD_some]
    congr 1
    refine Eq.trans ?_ ih
    apply List.map_congr_left
    intro f hf
    have hlt : ℓ < f.1 := by
      have := Wire.ascending_lt_of_find (ℓ := f.1) (A := f.2) ha (find_of_mem_asc (Wire.ascending_tail ha) hf)
      exact this
    have hne : f.1 ≠ ℓ := fun he => String.lt_irrefl ℓ (he ▸ hlt)
    simp [Data.field, hne]
where
  find_of_mem_asc : ∀ {r : List (Label × Ty)} {f : Label × Ty}, Row.ascending r = true → f ∈ r →
      Row.find? f.1 r = some f.2
    | [], _, _, hf => by simp at hf
    | (k, t) :: r, f, ha, hf => by
      rcases List.mem_cons.1 hf with rfl | hf
      · simp [Row.find?]
      · have hrest := find_of_mem_asc (Wire.ascending_tail ha) hf
        have hlt : k < f.1 := Wire.ascending_lt_of_find ha hrest
        have hne : f.1 ≠ k := fun he => String.lt_irrefl k (he ▸ hlt)
        simp [Row.find?, hne, hrest]

/-- **A key's bytes read back to the key** (LANG-49): for a well-formed key of the relation (a
record at `keyTy d`, which is canonical: `checkRel` checks `(keyTy d).wf`), `keyOf` at the full key
reads `keyBytes`' bytes back to exactly that key. So the key an edit writes is the key a later
point read of the same bytes hands the method. Tooth: `keyOf_keyBytes_unsorted`. -/
theorem keyOf_keyBytes {d : RelDecl} {k : Data} {b : ByteArray} (hwf : (keyTy d).wf = true)
    (hk : Conforms k (keyTy d)) (h : keyBytes d k = some b) : keyOf d d.key.length b = .ok k := by
  obtain ⟨vs, hvs, hb⟩ := keyOf_keyBytes_fields h
  rw [hb, mapM_field_eq hvs]
  have hasc : Row.ascending (Row.sort d.key) = true := by
    simp only [keyTy, Ty.wf, Bool.and_eq_true] at hwf; exact hwf.1
  cases hk with
  | record hr =>
    rename_i fs
    rw [← Row.sort_map (fun f => (f.1, ((Data.record fs).field f.1).getD (.nat 0))) (fun _ => rfl),
      conforms_fields hr hasc]

/-! ## The guard `guardEdits` runs is never stuck -/

theorem rowFind_mem {α : Type} {ℓ : Label} {a : α} : ∀ {r : List (Label × α)}, Row.find? ℓ r = some a → (ℓ, a) ∈ r
  | [], h => by simp [Row.find?] at h
  | (k, b) :: r, h => by
    simp only [Row.find?] at h
    split at h
    · rename_i he; cases h; subst he; simp
    · exact List.mem_cons_of_mem _ (rowFind_mem h)

theorem checkRel_guard {S : Ty} {row : List (Label × Ty)} {r : Label × RelDecl} (h : checkRel S row r = .ok ())
    {gl : Label} (hg : r.2.guard = some gl) : Row.find? gl row = some (guardTy S r.2) := by
  obtain ⟨ℓ, d⟩ := r
  simp only at hg
  unfold checkRel at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals simp_all

theorem checkFields_guard {p : Package} (h : p.checkFields = .ok ()) {ℓ gl : Label} {dl : RelDecl}
    (hrel : Row.find? ℓ p.rels = some dl) (hg : dl.guard = some gl) :
    Row.find? gl (recordRow p.iface) = some (guardTy p.state dl) := by
  unfold Package.checkFields at h
  split at h
  · rename_i row hrow
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i hrels
      unfold checkRels at hrels
      simp only [bind, Except.bind, pure, Except.pure] at hrels
      repeat' split at hrels
      all_goals first | (cases hrels; done) | skip
      rename_i v hfor
      cases v
      have hall := forIn_yield_ok (fun r => ∀ gl, r.2.guard = some gl → Row.find? gl row = some (guardTy p.state r.2))
        _ _ (fun r u s hs => by
          split at hs
          · cases hs
          · rename_i hc; cases hs; exact ⟨rfl, fun gl hg => checkRel_guard hc hg⟩) hfor
      rw [hrow]
      exact hall (ℓ, dl) (rowFind_mem hrel) gl hg
  · cases h

/-- The machine run inside a guard's `runLaw`: on a loaded package's declared guard, the state
before the run (read at its row), a request in bounds and an edit of the relation's edit type, it
ends with a value of `verdictTy` or a named budget/arithmetic fault (`guardTy`, checked at install
by `checkRel`, types the application). -/
theorem guard_run_ok {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat} {p : Package}
    {ℓ gl : Label} {dl : RelDecl} {old : Slots} {od e : Data} {r : Req D} {ticks : Nat}
    (hload : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p) (hrel : Row.find? ℓ p.rels = some dl) (hg : dl.guard = some gl)
    (hold : readState digestOf (recordRow p.state) old = .ok od)
    (hr : reqOk bytesOf r = true) (he : Conforms e (relEditTy dl)) :
    RunOK L.ifaces verdictTy
      (run L.lib Bounds.stackMax ticks 0
        (State.init (apply3 g gl) [e.toVal, (reqData bytesOf r).toVal, od.toVal])) := by
  obtain ⟨hlib, _⟩ := load_libTy hload
  obtain ⟨hshape, hfields, _⟩ := load_checked hload g p hp
  have hrec := checkShape_state hshape
  have ho := readState_conforms hold
  rw [← hrec] at ho
  obtain ⟨row, hrow, hfind⟩ := recordRow_find (checkFields_guard hfields hrel hg)
  have href : HasType (Loaded.ifaces L) [relEditTy dl, reqTy, p.state] (.ref g) (.record row) :=
    .ref (by rw [← hrow]; simp [Loaded.ifaces, hp])
  have ht : HasType (Loaded.ifaces L) [relEditTy dl, reqTy, p.state] (apply3 g gl) verdictTy :=
    .app (.app (.app (.get href hfind) (.var rfl)) (.var rfl)) (.var rfl)
  exact run_sound hlib _ _ _ (.eval (.cons (toVal_typed he)
    (.cons (toVal_typed (reqOk_conforms hr)) (.cons (toVal_typed ho) .nil))) ht .nil)

/-- **A relation's guard is never stuck** (LANG-49): `runLaw` on a loaded package's declared guard,
over the state before the run, a request in bounds and an edit of the relation's edit type,
returns a verdict or a named budget/arithmetic fault, never `stuck`. Mirrors
`runLaw_never_stuck`; teeth: `caseGuard_nat_stuck` (an edit of another shape IS stuck, so `he`
is used) and `runLaw_nat_stuck` (an untyped guard body). -/
theorem guard_never_stuck {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat} {p : Package}
    {ℓ gl : Label} {dl : RelDecl} {old : Slots} {od e : Data} {r : Req D}
    (hload : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p) (hrel : Row.find? ℓ p.rels = some dl) (hg : dl.guard = some gl)
    (hold : readState digestOf (recordRow p.state) old = .ok od)
    (hr : reqOk bytesOf r = true) (he : Conforms e (relEditTy dl)) :
    runLaw L.lib (.get (.ref g) gl) od (reqData bytesOf r) e ≠ .error .stuck := by
  have hrun := guard_run_ok (ticks := lawTicks) hload hp hrel hg hold hr he
  have hlib := (load_libTy hload).1
  have happ : applyAt (.get (.ref g) gl) = apply3 g gl := rfl
  unfold runLaw
  rw [happ]
  split
  · rename_i f used hf
    rw [hf] at hrun
    intro h; cases h; exact hrun rfl
  · rename_i v used hv
    rw [hv] at hrun
    split
    · simp
    · simp
    · rename_i x h1 h2 hx
      exfalso
      obtain ⟨d, left⟩ := x
      rcases verdict_shape (extract_conforms (m := ⟨L.lib⟩) hlib verdictTy hrun hx) with rfl | ⟨why, rfl⟩
      · exact h1 _ _ rfl
      · exact h2 _ _ rfl
    · rename_i f hx
      intro h; cases h
      exact extract_progress (m := ⟨L.lib⟩) hlib verdictTy (by decide) hrun hx rfl

/-- **The guards a method run's edits meet are never stuck** (LANG-49): past extraction, for every
edit `editsOf` reads from the run's edits row and every guard its relation declares, the `runLaw`
`guardEdits` makes (over the run's state, its request and the edit's data) is not `stuck`. -/
theorem guardEdits_never_stuck {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {S : RunSetup} {budget used fuel left : Nat} {v : Val} {c e st : Data}
    {es : List (Edit D)}
    (hS : runSetup bytesOf digestOf look rv pkg state method args r = .ok S)
    (hrun : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty fuel v = .ok (.record [("calls", c), ("edits", e), ("state", st)], left))
    (hes : editsOf S.rels r.self e = .ok es) :
    ∀ x ∈ es, ∀ gl, x.decl.guard = some gl →
      runLaw S.lib (.get (.ref S.g) gl) S.state (reqData bytesOf r) x.data ≠ .error .stuck := by
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, hr0, hl, hp, hres, hst, hargs, -, hrows, rfl⟩ := runSetup_spec hS
  obtain ⟨mty, hm, hA⟩ := resolveMethod_spec hres
  have hok := invoke_never_stuck (ticks := budget) hl hp hm hA hst hargs hrows hr0
  simp only at hrun hx hes ⊢
  rw [hrun] at hok
  have hcf := extract_conforms (load_libTy hl).1 (resultTy p.state sg.calls (editTy p.rels) sg.edits) hok hx
  intro x hx' gl hg
  cases hcf with
  | record hrow =>
    cases hrow with
    | cons _ hrest =>
      cases hrest with
      | cons hed _ =>
        obtain ⟨hd, hc⟩ := editsOf_conforms hed hes x hx'
        exact guard_never_stuck hl hp hd hg hst hr0 hc

end

/-! ## Teeth -/

private def tRel : RelDecl :=
  { key := [("a", .nat)], val := .nat, limit := 4, sum := none, cap := 0, retract := false, guard := none }

private def tRelR : RelDecl := { tRel with retract := true }

private def tRelSum : RelDecl :=
  { key := [("a", .nat)], val := .record [("n", .nat)], limit := 4, sum := some "n", cap := 100,
    retract := false, guard := none }

/-- `editsOf_parent` is not about an empty list: a one-edit row reads to one insert, at relation 0,
under the object `7`. -/
theorem editsOf_parent_witness :
    (match editsOf (D := Nat) [("t", tRel)] 7
        (.record [("e0", .inj "some" (.inj "t" (.inj "insert"
          (.record [("key", .record [("a", .nat 1)]), ("val", .nat 5)]))))]) with
     | .ok [x] => decide (x.rel = 0) && (match x.slot with | .row k => decide (k.parent = 7) | _ => false)
     | _ => false) = true := by decide

/-- `editOf_amt` at a relation with a sum column: the insert's `amt` is the value's `n` field. -/
theorem editOf_amt_witness :
    (match editOf (D := Nat) [("t", tRelSum)] 7 "e0" (.inj "t" (.inj "insert"
        (.record [("key", .record [("a", .nat 1)]), ("val", .record [("n", .nat 9)])]))) with
     | .ok x => (match x.act with | .insert 9 _ => true | _ => false)
     | _ => false) = true := by decide

/-- The tooth of `editOf_retract_allowed`: an insert-only relation's retract is refused. -/
theorem editOf_retract_refused :
    (match editOf (D := Nat) [("t", tRel)] 7 "e0" (.inj "t" (.inj "retract" (.record [("key", .record [("a", .nat 1)])]))) with
     | .error _ => true
     | .ok _ => false) = true := by decide

/-- ... and the same retract is accepted once the relation declares `retract`. -/
theorem editOf_retract_admitted :
    (match editOf (D := Nat) [("t", tRelR)] 7 "e0" (.inj "t" (.inj "retract" (.record [("key", .record [("a", .nat 1)])]))) with
     | .ok x => (match x.act with | .retract => true | _ => false)
     | .error _ => false) = true := by decide

private def twoPins : RowView Nat :=
  { points := fun _ _ => [(ByteArray.empty, none), (ByteArray.empty, none)], ranges := fun _ _ => .ok [] }

private def onePin : RowView Nat :=
  { points := fun _ _ => [((keyBytes tRel (.record [("a", .nat 1)])).getD .empty, none)],
    ranges := fun _ _ => .ok [] }

/-- The tooth of `relReads_points`' bound: a view with one more pin than the method's slots is
refused. -/
theorem relReads_pins_past_slots :
    (match relReads (fun _ => none) twoPins 7 0 "t" tRel ⟨1, none⟩ with
     | .error _ => true
     | .ok _ => false) = true := by decide

/-- `relReads_points` is not about a refusal: one pin into two slots reads to the pinned key, then
an empty slot. -/
theorem relReads_points_witness :
    (match relReads (fun _ => none) onePin 7 0 "t" tRel ⟨2, none⟩ with
     | .ok v =>
       (match pointSlots 2 v with
        | [.inj "some" (.record [("key", .record [("a", .nat 1)]), ("val", .inj "none" (.record []))]),
           .inj "none" (.record [])] => true
        | _ => false)
     | .error _ => false) = true := by decide

private def tRel2 : RelDecl :=
  { key := [("b", .nat), ("a", .nat)], val := .nat, limit := 4, sum := none, cap := 0, retract := false,
    guard := none }

/-- The tooth of `keyOf_keyBytes`' conformance premise: a key record with its labels descending
(not at `keyTy`, which is ascending) has bytes, and reads back as a DIFFERENT record (sorted). -/
theorem keyOf_keyBytes_unsorted :
    (match keyBytes tRel2 (.record [("b", .nat 1), ("a", .nat 2)]) with
     | some b =>
       (match keyOf tRel2 2 b with
        | .ok (.record [("a", .nat 2), ("b", .nat 1)]) => true
        | _ => false)
     | none => false) = true := by decide

/-- `keyOf_keyBytes` at a well-formed two-field key: the bytes read back to the key. -/
theorem keyOf_keyBytes_witness :
    (match keyBytes tRel2 (.record [("a", .nat 2), ("b", .nat 1)]) with
     | some b =>
       (match keyOf tRel2 2 b with
        | .ok (.record [("a", .nat 2), ("b", .nat 1)]) => true
        | _ => false)
     | none => false) = true := by decide

private def okT : Term := .inj verdictTy "ok" (.record [])

/-- A guard that cases on its edit (insert or upsert). -/
private def caseGuard : Term :=
  .lam (.record []) (.lam reqTy (.lam (relEditTy tRel) (.case (.var 0) [("insert", okT), ("upsert", okT)])))

/-- The tooth of `guard_never_stuck`'s edit-typing premise: the same guard on data that is not an
edit IS stuck. -/
theorem caseGuard_nat_stuck :
    (match runLaw [] caseGuard (.record []) (.record []) (.nat 5) with
      | .error .stuck => true
      | _ => false) = true := by decide

/-- ... and on an edit of the relation's edit type it returns its verdict. -/
theorem caseGuard_edit_ok :
    (match runLaw [] caseGuard (.record []) (.record [])
        (.inj "insert" (.record [("key", .record [("a", .nat 1)]), ("val", .nat 5)])) with
      | .ok (.ok ()) => true
      | _ => false) = true := by decide

/-! ## The row edits `Lang.program` hands KERNEL are its own object's (cv 01a14e16-78ac)

`runMeasured` reads a run's edits with `editsOf rels r.self`, so every row act is under the run's
`self`. With `invokeRun`'s request (`self` = the invoked object), KERNEL's `rowParent` assertion in
`invoke` (`e.1.under.1 = obj`, `Kernel.Proofs.Tree.invoke_ok`) never fires on a Lang method: it stays
as KERNEL's own check where row edits enter, since `Program` is abstract to it, as `run_calls` is
for `notCallable`. -/

theorem runMeasured_rows_under {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {method : Nat} {args : ByteArray} {r : Kernel.Receive.Req D} {budget : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t n : Nat}
    (h : runMeasured bytesOf digestOf look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∀ e ∈ rows, e.1.under.1 = r.self := by
  unfold runMeasured at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, -, rfl, -, -⟩ := h
  exact editsOf_under ‹editsOf _ _ _ = .ok _›

/-- **The rows `Lang.program` hands KERNEL**: every row act is under the run's own object. -/
theorem run_rows_under {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {method : Nat} {args : ByteArray} {r : Kernel.Receive.Req D} {budget : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t : Nat}
    (h : (program bytesOf digestOf).run look rv pkg state method args r budget = .ok (s, calls, rows, t)) :
    ∀ e ∈ rows, e.1.under.1 = r.self := by
  simp only [program, Except.map] at h
  split at h
  · cases h
  · rename_i x hx
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl, -⟩ := h
    exact runMeasured_rows_under hx

/-- **A prefix of every field is the key** (PROTOCOL-51): `preBytes` at the key's full length is
`keyBytes`, so a range's prefix and an edit's key are one encoding. -/
theorem preBytes_full (d : RelDecl) (k : Data) : preBytes d d.key.length k = keyBytes d k := by
  unfold preBytes keyBytes keyToWire
  rw [List.take_length]
  cases d.key.zipIdx.mapM (fun p => (k.field p.1.1).map fun x => ("k" ++ toString p.2, x)) <;> rfl

end Nanodregg.Lang
