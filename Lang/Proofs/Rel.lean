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
* `receipt_column_authenticated`, `receipt_row_authenticated` (E5): on a `(receipt)` read, a pinned
  point's and a signed range row's `receipt` field is what the run's `ReceiptCheck` showed for the
  head object that slot's key names, through the caller's pinned view, and the method's own
  `receipt` argument.
* `keyOf_keyBytes`: a key's bytes read back to the key (`keyOf_keyBytes_fields` without premises:
  to the key's declared fields, sorted).
* `guard_never_stuck`, `guardEdits_never_stuck`: the guard `guardEdits` runs on each edit never
  ends `stuck`, as `runLaw_never_stuck` for laws: the guard field is typed `guardTy` at install
  (`checkRel`), the edit data conforms to the relation's edit type (`editsOf_conforms`) and its
  old row to the option of the value type (`guardOld_conforms`, LANG-59).
* `guardOld_unpinned`, `guardEdits_unpinned`: an upsert or retract with no pin is refused
  `rowUnpinned` with the receiver's key, and `guardEdits` refuses it, at that edit's key, before any
  guard runs.
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
private def pinD (digestOf : ByteArray → Option D) (rc : ReceiptCheck) (look : Pinned D) (d : RelDecl)
    (live receipt : Bool) (args : Data) (p : ByteArray × Option RowLeaf) : Option Data :=
  match keyOf d d.key.length p.1 with
  | .error _ => none
  | .ok k =>
    let val : Option Data := match p.2 with
      | none => some (optD none)
      | some (.row _ b _) =>
        match Wire.decodeData d.val b with
        | .ok w => some (optD (some w))
        | .error _ => none
      | some (.head ..) => none
    val.bind fun val =>
      if receipt then
        match keyCell k with
        | none => none
        | some b => (digestOf b).bind fun g =>
          match look g, args.field "receipt" with
          | .ok (some c), some (.bytes rb) =>
            match rc c rb with
            | .ok s =>
              if seenFits s && (seenData s).digests.all (fun b => (digestOf b).isSome) then
                some (.record ([("key", k)] ++ (if live then [("live", .bool (cellLive look g))] else []) ++
                  [("receipt", seenData s), ("val", val)]))
              else none
            | .error _ => none
          | _, _ => none
      else if live then
        match keyCell k with
        | none => none
        | some b => (digestOf b).bind fun g =>
          match look g with
          | .ok _ => some (.record [("key", k), ("live", .bool (cellLive look g)), ("val", val)])
          | .error _ => none
      else some (.record [("key", k), ("val", val)])

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
pinned key bytes, its value decoded from the row's bytes, and on a live read (E1) its key's cell
liveness `cellLive look g` read through the caller's pinned view), and slot `j` holds pin `j` in pin
order and `none` past the last pin. -/
theorem relReads_points {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck} {look : Pinned D} {rv : RowView D} {self : D} {i : Nat}
    {ℓ : Label} {d : RelDecl} {x : RelRead} {args : Data} {v : Data}
    (h : relReads digestOf rc look rv self i ℓ d x args = .ok v) :
    (rv.points self i).length ≤ x.points ∧
    ∃ ps, (rv.points self i).mapM (pinD digestOf rc look d x.live x.receipt args) = some ps ∧
      pointSlots x.points v = (List.range x.points).map fun j => optD ps[j]? := by
  unfold relReads at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals
    cases h
    refine ⟨‹(rv.points self i).length ≤ x.points›, _,
      mapM_except_option (fun p y hy => ?_) ‹List.mapM _ (rv.points self i) = Except.ok _›, ?_⟩
    · split at hy
      · cases hy
      · rename_i kv hkv
        obtain ⟨k, val⟩ := kv
        obtain ⟨k0, h1, h2, hv⟩ := readPoint_ok hkv
        have hk := liftS_eq h1
        have hkk := checked_eq h2
        subst hkk
        rcases hv with ⟨rfl, hp2⟩ | ⟨v', b', ver, w, hp2, hw, rfl⟩
        · rcases pointData_ok hy with ⟨hr, hl, rfl⟩ | ⟨hr, hl, b, g, c, hb, hg, hc, rfl⟩ |
              ⟨hr, b, g, c, rb, sn, hb, hg, hc, ha, hs, hok, rfl⟩
          · simp [pinD, hk, hp2, hl, hr]
          · simp [pinD, hk, hp2, hl, hr, hb, hg, hc]
          · simp [pinD, hk, hp2, hr, hb, hg, hc, ha, hs, hok]
            intro y hy hn; have := (List.all_eq_true.mp hok.2) y hy; rw [hn] at this; cases this
        · rcases pointData_ok hy with ⟨hr, hl, rfl⟩ | ⟨hr, hl, b, g, c, hb, hg, hc, rfl⟩ |
              ⟨hr, b, g, c, rb, sn, hb, hg, hc, ha, hs, hok, rfl⟩
          · simp [pinD, hk, hp2, hl, hr, valOf_decodes hw]
          · simp [pinD, hk, hp2, hl, hr, hb, hg, hc, valOf_decodes hw]
          · simp [pinD, hk, hp2, hr, hb, hg, hc, ha, hs, hok, valOf_decodes hw]
            intro y hy hn; have := (List.all_eq_true.mp hok.2) y hy; rw [hn] at this; cases this
    · simp only [pointSlots]
      rw [List.take_append_of_le_length (by simp [length_slotsD]), List.take_of_length_le (by simp [length_slotsD]),
        slotsD_snd]

/-! ## The live read (E1, LANG-75.1) -/

/-- **One liveness** (E1): `cellLive` is exactly "the caller pinned `g` and the World holds a live
cell there" (`pinned` returns `World.live`, which is `none` at a tombstone or an absence). -/
theorem cellLive_iff {look : Pinned D} {g : D} :
    cellLive look g = true ↔ ∃ c, look g = .ok (some c) := by
  unfold cellLive
  split <;> simp_all

theorem mapM_ok_getElem {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      ∃ hl : ys.length = xs.length, ∀ j (hj : j < ys.length), f xs[j] = .ok ys[j]
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨rfl, fun j hj => absurd hj (by simp)⟩
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
        obtain ⟨hl, hj⟩ := mapM_ok_getElem hys
        refine ⟨by simp [hl], fun j hj' => ?_⟩
        cases j with
        | zero => simpa using hy
        | succ j => simpa using hj j (by simpa using hj')

/-- **The live column is authenticated** (E1, LANG-75.1; sibling of `holeRow_authenticated`): on a
live read, slot `j` of the rows argument is the caller's `j`-th pinned point, its key read back from
the pinned key bytes, and its `live` bit is `cellLive look g` for the kernel cell `g` that key
names — the caller's pinned view of THAT cell, never a field a method or a poster wrote. -/
theorem cited_authenticated {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck} {look : Pinned D} {rv : RowView D}
    {self : D} {i : Nat} {ℓ : Label} {d : RelDecl} {x : RelRead} {args : Data} {v : Data}
    (h : relReads digestOf rc look rv self i ℓ d x args = .ok v) (hl : x.live = true) :
    ∃ ps rest, v = .record (slotsD "p" x.points ps ++ rest) ∧
      ∃ hlen : ps.length = (rv.points self i).length,
      ∀ j (hj : j < ps.length), ∃ k b g val col,
        keyOf d d.key.length ((rv.points self i)[j]'(hlen ▸ hj)).1 = .ok k ∧
        keyCell k = some b ∧ digestOf b = some g ∧
        ps[j] = .record ([("key", k), ("live", .bool (cellLive look g))] ++ col ++ [("val", val)]) ∧
        (x.receipt = false → col = []) := by
  unfold relReads at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals
    cases h
    obtain ⟨hlen, hget⟩ := mapM_ok_getElem ‹List.mapM _ (rv.points self i) = Except.ok _›
    refine ⟨_, _, rfl, hlen, fun j hj => ?_⟩
    have hq := hget j hj
    split at hq
    · cases hq
    · rename_i kv hkv
      obtain ⟨k, val⟩ := kv
      obtain ⟨k0, h1, h2, -⟩ := readPoint_ok hkv
      have hk := liftS_eq h1
      have hkk := checked_eq h2
      subst hkk
      rcases pointData_ok hq with ⟨-, hf, -⟩ | ⟨hr, -, b, g, c, hb, hg, -, he⟩ |
          ⟨hr, b, g, c, rb, sn, hb, hg, -, -, -, -, he⟩
      · rw [hl] at hf; cases hf
      · exact ⟨_, b, g, _, [], hk, hb, hg, by simpa using he, fun _ => rfl⟩
      · refine ⟨_, b, g, _, [("receipt", seenData sn)], hk, hb, hg, by simpa [hl] using he, ?_⟩
        intro hx; rw [hx] at hr; cases hr

/-- **The receipt column is authenticated** (E5, L1; sibling of `cited_authenticated`): on a receipt
read, slot `j` of the rows argument is the caller's `j`-th pinned point, and its `receipt` field is
what the run's `ReceiptCheck` showed for the head object THAT key names, read through the caller's
pinned view (live: `look g = .ok (some c)`), and the method's own `receipt` argument: never the
receipt's stated answer, never a field a method or a poster wrote. -/
theorem receipt_column_authenticated {digestOf : ByteArray → Option D} {rc : ReceiptCheck} {look : Pinned D}
    {rv : RowView D} {self : D} {i : Nat} {ℓ : Label} {d : RelDecl} {x : RelRead} {args : Data} {v : Data}
    (h : relReads digestOf rc look rv self i ℓ d x args = .ok v) (hx : x.receipt = true) :
    ∃ ps rest, v = .record (slotsD "p" x.points ps ++ rest) ∧
      ∃ hlen : ps.length = (rv.points self i).length,
      ∀ j (hj : j < ps.length), ∃ k b g c rb s val,
        keyOf d d.key.length ((rv.points self i)[j]'(hlen ▸ hj)).1 = .ok k ∧
        keyCell k = some b ∧ digestOf b = some g ∧ look g = .ok (some c) ∧
        args.field "receipt" = some (.bytes rb) ∧ rc c rb = .ok s ∧
        ps[j] = .record ([("key", k)] ++ (if x.live then [("live", .bool (cellLive look g))] else []) ++
          [("receipt", seenData s), ("val", val)]) := by
  unfold relReads at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals
    cases h
    obtain ⟨hlen, hget⟩ := mapM_ok_getElem ‹List.mapM _ (rv.points self i) = Except.ok _›
    refine ⟨_, _, rfl, hlen, fun j hj => ?_⟩
    have hq := hget j hj
    split at hq
    · cases hq
    · rename_i kv hkv
      obtain ⟨k, val⟩ := kv
      obtain ⟨k0, h1, h2, -⟩ := readPoint_ok hkv
      have hk := liftS_eq h1
      have hkk := checked_eq h2
      subst hkk
      rcases pointData_ok hq with ⟨hr, -⟩ | ⟨hr, -⟩ | ⟨-, b, g, c, rb, sn, hb, hg, hc, ha, hs, -, he⟩
      · rw [hx] at hr; cases hr
      · rw [hx] at hr; cases hr
      · exact ⟨_, b, g, c, rb, sn, _, hk, hb, hg, hc, ha, hs, he⟩

/-- What a range read's listed row becomes (`rangeRowData`, row by row): the `j`-th datum is the
`j`-th listed row, its key read back at the key and its value at the value type. -/
theorem rangeRowData_getElem {digestOf : ByteArray → Option D} {ℓ : Label} {d : RelDecl}
    {rows : List (RowSlot D × RowLeaf)} {ds : List Data} (h : rangeRowData digestOf ℓ d rows = .ok ds) :
    ∃ hl : ds.length = rows.length, ∀ j (hj : j < ds.length), ∃ key amt vb ver k val,
      rows[j]'(hl ▸ hj) = (.row key, .row amt vb ver) ∧ keyOf d d.key.length key.k = .ok k ∧
      valOf digestOf d s!"rows: {ℓ}" vb = .ok val ∧ ds[j] = .record [("key", k), ("val", val)] := by
  unfold rangeRowData at h
  obtain ⟨hl, hget⟩ := mapM_ok_getElem h
  refine ⟨hl, fun j hj => ?_⟩
  have hq := hget j hj
  generalize rows[j] = r at hq ⊢
  obtain ⟨sl, lf⟩ := r
  cases sl with
  | head => cases lf <;> cases hq
  | row key =>
    cases lf with
    | head => cases hq
    | row amt vb ver =>
      simp only [bind, Except.bind, pure, Except.pure] at hq
      split at hq
      · cases hq
      rename_i k0 hk0
      split at hq
      · cases hq
      rename_i k hk
      split at hq
      · cases hq
      rename_i val hv
      simp only [Except.ok.injEq] at hq
      exact ⟨key, amt, vb, ver, k, val, rfl, by rw [checked_eq hk]; exact liftS_eq hk0, hv, hq.symm⟩


/-- **A range row's receipt column is authenticated** (E5, CX-PROMO-8; the range twin of
`receipt_column_authenticated`, the arm the deployed acceptor reads, `(heads (range 1 1) (receipt))`):
on a receipt read with a range, the rows argument's `range` is built from the caller's ONE signed
listing of that relation, and its row `j` is the listing's `j`-th row (its key read back at the key,
its value at the value type) whose `receipt` field is what the run's `ReceiptCheck` showed for the
head object THAT row's key names, read through the caller's pinned view (live:
`look g = .ok (some c)`), and the method's own `receipt` argument. -/
theorem receipt_row_authenticated {digestOf : ByteArray → Option D} {rc : ReceiptCheck} {look : Pinned D}
    {rv : RowView D} {self : D} {i : Nat} {ℓ : Label} {d : RelDecl} {x : RelRead} {args : Data} {v : Data}
    {m n : Nat} (h : relReads digestOf rc look rv self i ℓ d x args = .ok v) (hx : x.receipt = true)
    (hr : x.range = some (m, n)) :
    ∃ ps pre most rows p rs, rv.ranges self i = .ok [(pre, most, rows)] ∧
      v = .record (slotsD "p" x.points ps ++ [("range", .record [("pre", p), ("rows", .record (slotsD "r" n rs))])]) ∧
      ∃ hlen : rs.length = rows.length,
      ∀ j (hj : j < rs.length), ∃ key amt vb ver k val b g c rb s,
        rows[j]'(hlen ▸ hj) = (.row key, .row amt vb ver) ∧
        keyOf d d.key.length key.k = .ok k ∧ valOf digestOf d s!"rows: {ℓ}" vb = .ok val ∧
        keyCell k = some b ∧ digestOf b = some g ∧ look g = .ok (some c) ∧
        args.field "receipt" = some (.bytes rb) ∧ rc c rb = .ok s ∧
        rs[j] = .record ([("key", k)] ++ (if x.live then [("live", .bool (cellLive look g))] else []) ++
          [("receipt", seenData s), ("val", val)]) := by
  unfold relReads at h
  rw [hr] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals
    simp only [Except.ok.injEq] at h
    subst h
    have hrange := ‹rv.ranges self i = Except.ok _›
    have hrd := ‹rangeRowData digestOf ℓ d _ = Except.ok _›
    have hcr := ‹columnRows digestOf rc look ℓ x.live x.receipt args _ = Except.ok _›
    rw [hx] at hcr
    unfold columnRows at hcr
    rw [if_pos (by simp)] at hcr
    obtain ⟨hl1, hg1⟩ := rangeRowData_getElem hrd
    obtain ⟨hl2, hg2⟩ := mapM_ok_getElem hcr
    refine ⟨_, _, _, _, _, _, hrange, rfl, hl2.trans hl1, fun j hj => ?_⟩
    obtain ⟨key, amt, vb, ver, k, val, hrow, hk, hv, hd⟩ := hg1 j (hl2 ▸ hj)
    have hq := hg2 j hj
    rw [hd] at hq
    unfold columnRow at hq
    cases hcs : keyColumns digestOf rc look ℓ x.live true args k with
    | error e => simp [hcs] at hq
    | ok cs =>
      simp only [hcs, Except.ok.injEq] at hq
      rcases keyColumns_ok hcs with ⟨hr, -⟩ | ⟨hr, -⟩ | ⟨-, b, g, c, rb, s, hb, hg, hc, ha, hs, -, rfl⟩
      · cases hr
      · cases hr
      · exact ⟨key, amt, vb, ver, k, val, b, g, c, rb, s, hrow, hk, hv, hb, hg, hc, ha, hs,
          by rw [← hq]; simp [List.append_assoc]⟩

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
before the run (read at its row), a request in bounds and a guard input at `guardInTy`, it ends
with a value of `verdictTy` or a named budget/arithmetic fault (`guardTy`, checked at install
by `checkRel`, types the application). -/
theorem guard_run_ok {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat} {p : Package}
    {ℓ gl : Label} {dl : RelDecl} {old : Slots} {od e : Data} {r : Req D} {ticks : Nat}
    (hload : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p) (hrel : Row.find? ℓ p.rels = some dl) (hg : dl.guard = some gl)
    (hold : readState digestOf (recordRow p.state) old = .ok od)
    (hr : reqOk bytesOf r = true) (he : Conforms e (guardInTy dl)) :
    RunOK L.ifaces verdictTy
      (run L.lib Bounds.stackMax ticks 0
        (State.init (apply3 g gl) [e.toVal, (reqData bytesOf r).toVal, od.toVal])) := by
  obtain ⟨hlib, _⟩ := load_libTy hload
  obtain ⟨hshape, hfields, _⟩ := load_checked hload g p hp
  have hrec := checkShape_state hshape
  have ho := readState_conforms hold
  rw [← hrec] at ho
  obtain ⟨row, hrow, hfind⟩ := recordRow_find (checkFields_guard hfields hrel hg)
  have href : HasType (Loaded.ifaces L) [guardInTy dl, reqTy, p.state] (.ref g) (.record row) :=
    .ref (by rw [← hrow]; simp [Loaded.ifaces, hp])
  have ht : HasType (Loaded.ifaces L) [guardInTy dl, reqTy, p.state] (apply3 g gl) verdictTy :=
    .app (.app (.app (.get href hfind) (.var rfl)) (.var rfl)) (.var rfl)
  exact run_sound hlib _ _ _ (.eval (.cons (toVal_typed he)
    (.cons (toVal_typed (reqOk_conforms hr)) (.cons (toVal_typed ho) .nil))) ht .nil)

/-- **A relation's guard is never stuck** (LANG-49): `runLaw` on a loaded package's declared guard,
over the state before the run, a request in bounds and a guard input at `guardInTy` (the edit
and its old row), returns a verdict or a named budget/arithmetic fault, never `stuck`. Mirrors
`runLaw_never_stuck`; teeth: `caseGuard_nat_stuck` (an edit of another shape IS stuck, so `he`
is used) and `runLaw_nat_stuck` (an untyped guard body). -/
theorem guard_never_stuck {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat} {p : Package}
    {ℓ gl : Label} {dl : RelDecl} {old : Slots} {od e : Data} {r : Req D}
    (hload : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p) (hrel : Row.find? ℓ p.rels = some dl) (hg : dl.guard = some gl)
    (hold : readState digestOf (recordRow p.state) old = .ok od)
    (hr : reqOk bytesOf r = true) (he : Conforms e (guardInTy dl)) :
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

theorem except_map_ok {α β ε : Type} {f : α → β} {e : Except ε α} {b : β} (h : e.map f = .ok b) :
    ∃ a, e = .ok a ∧ b = f a := by
  cases e with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, by simp only [Except.map, Except.ok.injEq] at h; exact h.symm⟩

/-- The old row `guardOld` finds is a value of the option of the relation's value type. -/
theorem guardOld_conforms {digestOf : ByteArray → Option D} {rv : RowView D} {self : D} {x : Edit D}
    {o : Data} (h : guardOld digestOf rv self x = .ok o) : Conforms o (optTy x.decl.val) := by
  unfold guardOld at h
  rcases hp : pinAt rv self x with _ | ⟨k, _ | l⟩
  · simp only [hp] at h
    split at h
    · cases h; exact optD_conforms (by simp)
    · cases h
  · simp only [hp] at h; cases h; exact optD_conforms (by simp)
  · cases l with
    | head => simp only [hp] at h; cases h
    | row a v n =>
      simp only [hp] at h
      obtain ⟨w, hw, rfl⟩ := except_map_ok h
      exact optD_conforms fun y hy => by cases hy; exact valOf_conforms hw

theorem guardIn_conforms {d : RelDecl} {e o : Data} (he : Conforms e (relEditTy d))
    (ho : Conforms o (optTy d.val)) : Conforms (guardIn e o) (guardInTy d) :=
  .record (.cons he (.cons ho .nil))

theorem mapM_zip_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ p ∈ xs.zip ys, f p.1 = .ok p.2
  | [], ys, _ => by simp
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
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hy
        · exact mapM_zip_ok hys q hq

/-- **The guards a method run's edits meet are never stuck** (LANG-49, LANG-59): past extraction,
for every edit `editsOf` reads from the run's edits row, paired with the old row `guardEdits`
found for it (every `guardOld` succeeded: `olds`), and every guard its relation declares, the
`runLaw` `guardEdits` makes (over the run's state, its request and `guardIn` of the edit's data
and its old row) is not `stuck`. -/
theorem guardEdits_never_stuck {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {S : RunSetup} {budget used fuel left : Nat} {v : Val} {c e st : Data}
    {es : List (Edit D)} {olds : List Data}
    (hS : runSetup bytesOf digestOf rc look rv pkg state method args r = .ok S)
    (hrun : run S.lib Bounds.stackMax budget 0 (State.init S.term S.env) = .value v used)
    (hx : (Machine.mk S.lib).extract S.ty fuel v = .ok (.record [("calls", c), ("edits", e), ("state", st)], left))
    (hes : editsOf S.rels r.self e = .ok es)
    (hol : es.mapM (guardOld digestOf rv r.self) = .ok olds) :
    ∀ q ∈ es.zip olds, ∀ gl, q.1.decl.guard = some gl →
      runLaw S.lib (.get (.ref S.g) gl) S.state (reqData bytesOf r) (guardIn q.1.data q.2) ≠ .error .stuck := by
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, hr0, hl, hp, hres, hst, hargs, -, hrows, rfl⟩ := runSetup_spec hS
  obtain ⟨mty, hm, hA⟩ := resolveMethod_spec hres
  have hok := invoke_never_stuck (ticks := budget) hl hp hm hA hst hargs hrows hr0
  simp only at hrun hx hes ⊢
  rw [hrun] at hok
  have hcf := extract_conforms (load_libTy hl).1 (resultTy p.state sg.calls (editTy p.rels) sg.edits) hok hx
  intro q hq gl hg
  have hx' : q.1 ∈ es := (List.of_mem_zip hq).1
  have ho := guardOld_conforms (mapM_zip_ok hol q hq)
  cases hcf with
  | record hrow =>
    cases hrow with
    | cons _ hrest =>
      cases hrest with
      | cons hed _ =>
        obtain ⟨hd, hc⟩ := editsOf_conforms hed hes q.1 hx'
        exact guard_never_stuck hl hp hd hg hst hr0 (guardIn_conforms hc ho)

/-- **An unpinned upsert or retract has no old row** (LANG-59): with no pin at its slot, an edit
whose act needs one is refused `rowUnpinned` with its parent, relation and key, the refusal and
key `rowTouchesOf` gives (`Kernel.Proofs.Rederive`). -/
theorem guardOld_unpinned {digestOf : ByteArray → Option D} {rv : RowView D} {self : D} {x : Edit D}
    (hp : pinAt rv self x = none) (ha : x.act.unpinned = false) :
    guardOld digestOf rv self x = .error (.rowUnpinned x.slot.under.1 x.slot.under.2 x.slot.keyBytes) := by
  unfold guardOld
  rw [hp]
  simp [ha]

theorem mapM_prefix_error {α β ε : Type} {f : α → Except ε β} {x : α} {e : ε} (hx : f x = .error e) :
    ∀ (pre post : List α), (∀ y ∈ pre, ∃ b, f y = .ok b) → (pre ++ x :: post).mapM f = .error e
  | [], post, _ => by simp [List.mapM_cons, hx, bind, Except.bind]
  | y :: pre, post, h => by
    obtain ⟨b, hb⟩ := h y (by simp)
    have ih := mapM_prefix_error hx pre post (fun z hz => h z (by simp [hz]))
    simp [List.mapM_cons, hb, bind, Except.bind, ih]

/-- **`guardEdits` finds every old row before it runs a guard** (LANG-59): when an edit `x` is an
unpinned upsert or retract and every edit before it has its old row, `guardEdits` refuses
`rowUnpinned` with `x`'s own parent, relation and key, whatever any guard (of `x`, of an earlier
edit, or of a later one) would say. -/
theorem guardEdits_unpinned {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {S : RunSetup} {rv : RowView D} {pkg : D} {r : Req D} {pre post : List (Edit D)} {x : Edit D}
    (hpre : ∀ y ∈ pre, ∃ o, guardOld digestOf rv r.self y = .ok o)
    (hp : pinAt rv r.self x = none) (ha : x.act.unpinned = false) :
    guardEdits bytesOf digestOf S rv pkg r (pre ++ x :: post) =
      .error (.rowUnpinned x.slot.under.1 x.slot.under.2 x.slot.keyBytes) := by
  have hm := mapM_prefix_error (guardOld_unpinned (digestOf := digestOf) hp ha) pre post hpre
  simp [guardEdits, hm, bind, Except.bind]

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
    (match relReads (fun _ => none) noReceipts (fun g => .error (.unpinned g)) twoPins 7 0 "t" tRel ⟨1, none, false, false⟩ (.record []) with
     | .error _ => true
     | .ok _ => false) = true := by decide

/-- `relReads_points` is not about a refusal: one pin into two slots reads to the pinned key, then
an empty slot. -/
theorem relReads_points_witness :
    (match relReads (fun _ => none) noReceipts (fun g => .error (.unpinned g)) onePin 7 0 "t" tRel ⟨2, none, false, false⟩ (.record []) with
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
  .lam (.record []) (.lam reqTy (.lam (guardInTy tRel)
    (.case (.get (.var 0) "edit") [("insert", okT), ("upsert", okT)])))

/-- The tooth of `guard_never_stuck`'s edit-typing premise: the same guard on data that is not an
edit IS stuck. -/
theorem caseGuard_nat_stuck :
    (match runLaw [] caseGuard (.record []) (.record []) (.nat 5) with
      | .error .stuck => true
      | _ => false) = true := by decide

/-- ... and on a guard input it returns its verdict. -/
theorem caseGuard_edit_ok :
    (match runLaw [] caseGuard (.record []) (.record [])
        (guardIn (.inj "insert" (.record [("key", .record [("a", .nat 1)]), ("val", .nat 5)])) (optD none)) with
      | .ok (.ok ()) => true
      | _ => false) = true := by decide

/-- A guard that admits an upsert over an absent row and refuses one over a present row: it reads
only `old`. -/
private def freshGuard : Term :=
  .lam (.record []) (.lam reqTy (.lam (guardInTy tRel)
    (.case (.get (.var 0) "old") [("none", okT), ("some", .inj verdictTy "refused" (.bytes ⟨#[116]⟩))])))

private def upsert15 : Data := .inj "upsert" (.record [("key", .record [("a", .nat 1)]), ("val", .nat 5)])

/-- The tooth that `old` reaches the guard (LANG-59): ONE edit, two old rows, two verdicts. A guard
that saw only the edit could not tell these apart. -/
theorem freshGuard_reads_old :
    (match runLaw [] freshGuard (.record []) (.record []) (guardIn upsert15 (optD none)),
           runLaw [] freshGuard (.record []) (.record []) (guardIn upsert15 (optD (some (.nat 4)))) with
      | .ok (.ok ()), .ok (.error _) => true
      | _, _ => false) = true := by decide

private def tEditU : Edit Nat :=
  { rel := 0, label := "t", decl := tRelR, data := upsert15,
    slot := .row ⟨7, 0, (keyBytes tRel (.record [("a", .nat 1)])).getD .empty⟩, act := .upsert 0 .empty }

/-- `guardOld_unpinned` is not about an empty view only: with the row pinned absent, the same
upsert's old row is `none`. -/
theorem guardOld_pinned_absent :
    (match guardOld (fun _ => none) onePin 7 tEditU with
     | .ok (.inj "none" (.record [])) => true
     | _ => false) = true := by decide

private def rowPin5 : RowView Nat :=
  { points := fun _ _ => [((keyBytes tRel (.record [("a", .nat 1)])).getD .empty,
      some (.row 0 ((Wire.encodeData tRel.val (.nat 5)).getD .empty) 0))],
    ranges := fun _ _ => .ok [] }

/-- ... and with the slot pinned holding a row of value 5, its old row is `some 5`: the value read
back from the row's bytes. -/
theorem guardOld_pinned_row :
    (match guardOld (fun _ => none) rowPin5 7 tEditU with
     | .ok (.inj "some" (.nat 5)) => true
     | _ => false) = true := by decide

/-- ... and with no pin at all it is refused `rowUnpinned` at the edit's key. -/
theorem guardOld_unpinned_witness :
    (match guardOld (fun _ => none) ⟨fun _ _ => [], fun _ _ => .ok []⟩ 7 tEditU with
     | .error (.rowUnpinned 7 0 k) => decide (k = (keyBytes tRel (.record [("a", .nat 1)])).getD .empty)
     | _ => false) = true := by decide

/-! ## The row edits `Lang.program` hands KERNEL are its own object's (cv 01a14e16-78ac)

`runMeasured` reads a run's edits with `editsOf rels r.self`, so every row act is under the run's
`self`. With `invokeRun`'s request (`self` = the invoked object), KERNEL's `rowParent` assertion in
`invoke` (`e.1.under.1 = obj`, `Kernel.Proofs.Tree.invoke_ok`) never fires on a Lang method: it stays
as KERNEL's own check where row edits enter, since `Program` is abstract to it, as `run_calls` is
for `notCallable`. -/

theorem runMeasuredWith_rows_under {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {setup : Kernel.Receive.Pinned D → Kernel.Receive.RowView D → D → Kernel.Slots → Nat → ByteArray → Kernel.Receive.Req D → Except (Kernel.Receive.Refusal D) RunSetup}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {method : Nat} {args : ByteArray} {r : Kernel.Receive.Req D} {budget : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t n : Nat}
    (h : runMeasuredWith bytesOf digestOf setup look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∀ e ∈ rows, e.1.under.1 = r.self := by
  unfold runMeasuredWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, -, rfl, -, -⟩ := h
  exact editsOf_under ‹editsOf _ _ _ = .ok _›

theorem runMeasured_rows_under {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {method : Nat} {args : ByteArray} {r : Kernel.Receive.Req D} {budget : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t n : Nat}
    (h : runMeasured bytesOf digestOf rc look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∀ e ∈ rows, e.1.under.1 = r.self := by
  exact runMeasuredWith_rows_under (setup := runSetup bytesOf digestOf rc) h

/-- **The rows `Lang.program` hands KERNEL**: every row act is under the run's own object. -/
theorem run_rows_under {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {method : Nat} {args : ByteArray} {r : Kernel.Receive.Req D} {budget : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t : Nat}
    (h : (program bytesOf digestOf rc).run look rv pkg state method args r budget = .ok (s, calls, rows, t)) :
    ∀ e ∈ rows, e.1.under.1 = r.self := by
  simp only [program, Except.map] at h
  split at h
  · cases h
  · rename_i x hx
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl, -⟩ := h
    exact runMeasuredWith_rows_under (setup := runSetupLive bytesOf digestOf rc) hx

/-- **A prefix of every field is the key** (PROTOCOL-51): `preBytes` at the key's full length is
`keyBytes`, so a range's prefix and an edit's key are one encoding. -/
theorem preBytes_full (d : RelDecl) (k : Data) : preBytes d d.key.length k = keyBytes d k := by
  unfold preBytes keyBytes keyToWire
  rw [List.take_length]
  cases d.key.zipIdx.mapM (fun p => (k.field p.1.1).map fun x => ("k" ++ toString p.2, x)) <;> rfl

/-! ### The live read's install rule (E1, LANG-75.1; READ-E1-grok condition 1) -/

private def liveRel (key : Ty) : RelDecl :=
  { key := [("k", key)], val := .nat, limit := 4, sum := none, cap := 0, retract := false, guard := none }

/-- A one-method package reading relation `r` (keyed by `key`) with its keys' cell liveness. -/
private def liveReader (key : Ty) : Package :=
  { imports := [], state := .record [], body := .record [], methods := ["m"], laws := [],
    rels := [("r", liveRel key)],
    iface := .record [("m", methodTy (.record []) (.record []) []
      (readsTy [("r", liveRel key)] [("r", ⟨1, none, true, false⟩)]) (editTy [("r", liveRel key)]) 0)] }

/-- A live read of a relation that is NOT cell-keyed is refused at install by its own name,
`liveNotCellKeyed`, never as a generic `badMethod`. -/
theorem live_read_not_cell_keyed_refused :
    (match (liveReader .nat).checkFields with
     | .error e => decide (e = .liveNotCellKeyed "m")
     | .ok _ => false) = true := by decide

/-- The control: the same read of a relation keyed by one digest installs. -/
theorem live_read_cell_keyed_admitted :
    (match (liveReader .digest).checkFields with | .ok _ => true | .error _ => false) = true := by decide

/-- A one-method package reading relation `r` (keyed by `key`) by a RANGE only, live (CLIENT-35). -/
private def liveRangeReader (key : Ty) : Package :=
  { imports := [], state := .record [], body := .record [], methods := ["m"], laws := [],
    rels := [("r", liveRel key)],
    iface := .record [("m", methodTy (.record []) (.record []) []
      (readsTy [("r", liveRel key)] [("r", ⟨0, some (1, 2), true, false⟩)]) (editTy [("r", liveRel key)]) 0)] }

/-- **A live RANGE read keeps its `(live)` when its type is read back** (CLIENT-35): its rows carry the
`live` column (`rangeRowTy`), so a range-only live read's type is not the plain one and `relReadOf`
returns the live read. Before, the two types were equal and the read came back non-live: `(live)` on
a range was dropped without a refusal. -/
theorem live_range_read_kept :
    relReadOf (liveRel .digest) (relReadTy (liveRel .digest) ⟨0, some (1, 2), true, false⟩) =
      some ⟨0, some (1, 2), true, false⟩ := by decide

/-- The control: the live range read's type is not the plain range read's. -/
theorem live_range_read_typed :
    relReadTy (liveRel .digest) ⟨0, some (1, 2), true, false⟩ ≠
      relReadTy (liveRel .digest) ⟨0, some (1, 2), false, false⟩ := by decide

/-- A live range read of a relation that is not cell-keyed is refused at install by name,
`liveNotCellKeyed` (before CLIENT-35 it installed as a plain range read). -/
theorem live_range_not_cell_keyed_refused :
    (match (liveRangeReader .nat).checkFields with
     | .error e => decide (e = .liveNotCellKeyed "m")
     | .ok _ => false) = true := by decide

/-- The control: the live range read of a relation keyed by one digest installs. -/
theorem live_range_cell_keyed_admitted :
    (match (liveRangeReader .digest).checkFields with | .ok _ => true | .error _ => false) = true := by decide

/-! ## An admitted run's edits passed their guards (PROT-4, LANG-75.9)

`runMeasured_past_extraction` and `program_run_past_extraction` (`Lang.Proofs.Provenance`) rewrite a run
that got past extraction to the do-block whose last bind is `guardEdits`: they connect a run to the
guard CALL. The converse below inverts that do-block under `= .ok`: a run that RETURNED had every one
of its edits' old rows found and every guard its relation declares said `ok`. Nothing landed before
said so (`guardEdits_never_stuck` is "not stuck", `guardEdits_unpinned` a refusal). A plant that
accepts a guard's refusal inside `guardEdits` reds `guardEdits_ok` and no landed theorem (LANG-75.9). -/

private theorem mapM_zip_forM_ok {α β ε : Type} {f : α → Except ε β} {g : α × β → Except ε Unit} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → (xs.zip ys).forM g = .ok () →
      ∀ x ∈ xs, ∃ y, f x = .ok y ∧ g (x, y) = .ok ()
  | [], _, _, _ => by simp
  | x :: xs, ys, h, hg => by
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
        rw [List.zip_cons_cons] at hg
        unfold List.forM at hg
        simp only [bind, Except.bind] at hg
        split at hg
        · cases hg
        · rename_i u hu
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact ⟨y, hy, by cases u; exact hu⟩
          · exact mapM_zip_forM_ok hys hg z hz

/-- **`guardEdits` accepting means every edit's guard accepted**: each edit's old row was found
(`guardOld`), and every guard its relation declares, run as `guardEdits` runs it (`runLaw` on field
`gl` of the closure body, over the state before the run, the request and the edit with its old row),
returned `ok`. -/
theorem guardEdits_ok {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {S : RunSetup} {rv : Kernel.Receive.RowView D} {pkg : D} {r : Kernel.Receive.Req D} {es : List (Edit D)}
    (h : guardEdits bytesOf digestOf S rv pkg r es = .ok ()) :
    ∀ x ∈ es, ∃ o, guardOld digestOf rv r.self x = .ok o ∧ ∀ gl, x.decl.guard = some gl →
      runLaw S.lib (.get (.ref S.g) gl) S.state (reqData bytesOf r) (guardIn x.data o) = .ok (.ok ()) := by
  unfold guardEdits at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i olds hol
  intro x hx
  obtain ⟨o, ho, hg⟩ := mapM_zip_forM_ok hol h x hx
  refine ⟨o, ho, fun gl hgl => ?_⟩
  simp only [hgl] at hg
  split at hg
  · assumption
  · cases hg
  · cases hg

/-- **The do-block of a run, inverted** (the converse of `runMeasured_past_extraction`): a run that
returned had its setup, a machine run within the budget left after preparation, an extraction at the
result type, its edits read from the edits row, and `guardEdits` accepting them; its rows are those
edits' slots and acts. -/
theorem runMeasuredWith_ok {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {setup : Kernel.Receive.Pinned D → Kernel.Receive.RowView D → D → Kernel.Slots → Nat → ByteArray → Kernel.Receive.Req D → Except (Kernel.Receive.Refusal D) RunSetup}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {method : Nat} {args : ByteArray} {r : Kernel.Receive.Req D} {budget : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t n : Nat}
    (h : runMeasuredWith bytesOf digestOf setup look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∃ S v used c e ds left es, setup look rv pkg state method args r = .ok S ∧
      run S.lib Bounds.stackMax (budget - S.preparation) 0 (State.init S.term S.env) = .value v used ∧
      (Machine.mk S.lib).extract S.ty (budget - S.preparation - used) v =
        .ok (.record [("calls", c), ("edits", e), ("state", .record ds)], left) ∧
      editsOf S.rels r.self e = .ok es ∧ guardEdits bytesOf digestOf S rv pkg r es = .ok () ∧
      rows = es.map (fun x => (x.slot, x.act)) := by
  unfold runMeasuredWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i S hS
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i v used hrun
  split at h
  all_goals first | (simp at h; done) | skip
  rename_i c e ds left hx
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, -, rfl, -, -⟩ := h
  exact ⟨S, v, used, c, e, ds, left, _, hS, hrun, hx, ‹editsOf _ _ _ = .ok _›, ‹guardEdits _ _ _ _ _ _ _ = .ok _›, rfl⟩

/-- **An admitted run's edits passed their guards** (`run_edits_guarded`, PROT-4's first half): when a
method run returns, its rows are the slots and acts of the edits it returned, each edit's old row
was found, and every guard the edit's relation declares accepted the edit over that old row, the
state before the run and the run's request. For every setup (`runMeasured`, `runMeasuredLive`, and
so `Lang.program`'s `run`). -/
theorem run_edits_guarded {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {setup : Kernel.Receive.Pinned D → Kernel.Receive.RowView D → D → Kernel.Slots → Nat → ByteArray → Kernel.Receive.Req D → Except (Kernel.Receive.Refusal D) RunSetup}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {method : Nat} {args : ByteArray} {r : Kernel.Receive.Req D} {budget : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t n : Nat}
    (h : runMeasuredWith bytesOf digestOf setup look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∃ S, ∃ es : List (Edit D), setup look rv pkg state method args r = .ok S ∧ rows = es.map (fun x => (x.slot, x.act)) ∧
      ∀ x ∈ es, ∃ o, guardOld digestOf rv r.self x = .ok o ∧ ∀ gl, x.decl.guard = some gl →
        runLaw S.lib (.get (.ref S.g) gl) S.state (reqData bytesOf r) (guardIn x.data o) = .ok (.ok ()) := by
  obtain ⟨S, -, -, -, -, -, -, es, hS, -, -, -, hg, rfl⟩ := runMeasuredWith_ok h
  exact ⟨S, es, hS, rfl, guardEdits_ok hg⟩

end Nanodregg.Lang
