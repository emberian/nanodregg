/-
# Lang.Proofs.Invoke — what a receiver decodes from cells is typed, so neither an invoked method
nor a judging law ever gets stuck

Composes `readState_conforms`/`decodeData_conforms` (decoded data has its type), `toVal_typed` and
`method_run_sound`: for the run `Program.run` performs — a loaded package's method on the state read
from the object's slots, the arguments decoded from the call, and the request — the outcome is a
value of the package's state type or a named non-`stuck` fault, at every tick budget.
`law_never_stuck` is its twin for `Program.judge`: every law a loaded package declares, run on the
old and new states read from the slots, ends with a verdict or a named non-`stuck` fault. Neither
takes a premise about the package beyond its having loaded (load re-checks it); the only premise
left about the request is `reqOk`, the very bound `Program.run`/`judge` assert before running
(KERNEL's `checkBounds` bounds the window only at admission, after the receivers ran).
-/
import Lang.Proofs.Load
import Lang.Proofs.Data
import Lang.Proofs.Canon
import Lang.Proofs.Read

namespace Nanodregg.Lang

open Nanodregg.Kernel Nanodregg.Kernel.Receive

theorem readState_go_conforms {D : Type} {digestOf : ByteArray → Option D} {s : Slots} :
    ∀ (row : List (Label × Ty)) (i : Nat) {d : Data}, readState.go digestOf s row i = .ok d →
      Conforms d (.record row)
  | [], _, d, h => by
    unfold readState.go at h; simp only [Except.ok.injEq] at h; subst h; exact .record .nil
  | (ℓ, t) :: row, i, d, h => by
    unfold readState.go at h
    split at h
    · simp at h
    · rename_i b _
      split at h
      · rename_i d1 ds hd hr
        split at h
        · cases h
          have h2 := readState_go_conforms row (i + 1) hr
          cases h2 with
          | record hrow => exact .record (.cons (decodeData_conforms hd) hrow)
        · simp at h
      all_goals simp at h

theorem readState_conforms {D : Type} {digestOf : ByteArray → Option D} {row : List (Label × Ty)} {s : Slots}
    {d : Data} (h : readState digestOf row s = .ok d) : Conforms d (.record row) :=
  readState_go_conforms row 0 h

/-- `readState` reads slots only by key: two slot lists that agree at every key read as one state. -/
theorem readState_get {D : Type} {digestOf : ByteArray → Option D} {row : List (Label × Ty)} {a b : Slots}
    (h : ∀ k, a.get k = b.get k) : readState digestOf row a = readState digestOf row b := by
  unfold readState
  generalize 0 = i
  induction row generalizing i with
  | nil => rfl
  | cons x row ih => obtain ⟨ℓ, t⟩ := x; simp only [readState.go, h, ih]

theorem reqOk_conforms {D : Type} {bytesOf : D → ByteArray} {r : Req D} (h : reqOk bytesOf r = true) :
    Conforms (reqData bytesOf r) reqTy := by
  simp only [reqOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨ha, hp⟩, hs⟩, hnb⟩, hvu⟩, ho⟩ := h
  refine .record (.cons (.digest ha) (.cons (.nat hnb) (.cons ?_ (.cons (.digest hp) (.cons (.digest hs)
    (.cons (.nat hvu) .nil))))))
  cases hr : r.occasion with
  | birth => exact .inj rfl (.record .nil)
  | write => exact .inj rfl (.record .nil)
  | relaw ls =>
    rw [hr] at ho; simp only [occasionOk, decide_eq_true_eq] at ho
    exact .inj rfl (.bytes ho)
  | adopt ls =>
    rw [hr] at ho; simp only [occasionOk, decide_eq_true_eq] at ho
    exact .inj rfl (.bytes ho)
  | invoke m =>
    rw [hr] at ho; simp only [occasionOk, decide_eq_true_eq] at ho
    exact .inj rfl (.nat ho)

theorem checkShape_ok {p : Package} (h : p.checkShape = .ok ()) :
    isRecordData p.state = true ∧ p.iface.wf = true := by
  unfold Package.checkShape at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h <;> try (simp at h; done)
  split at h <;> try (simp at h; done)
  split at h <;> try (simp at h; done)
  split at h <;> try (simp at h; done)
  split at h <;> try (simp at h; done)
  simp_all

theorem checkShape_state {p : Package} (h : p.checkShape = .ok ()) :
    p.state = .record (recordRow p.state) := by
  have hr := (checkShape_ok h).1
  cases hs : p.state <;> simp_all [isRecordData, recordRow]

/-- What `runMethod` decodes is at types with a data codec: every state field's type and every
method's argument type is `wf` and carried by the wire (`state_fields_dataTy`, `methodArg_dataTy`),
so `decodeData` passes its type gate (`decodeData_of_dataTy`) and reads with the type's stream. -/
theorem state_fields_wf {p : Package} (h : p.checkShape = .ok ()) : Ty.rowWf (recordRow p.state) = true := by
  have hr := (checkShape_ok h).1
  cases hs : p.state <;> simp_all [isRecordData, recordRow, Ty.wf]

theorem methodArg_wf {p : Package} {ℓ : Label} {mty A : Ty} (h : p.checkShape = .ok ())
    (hm : Row.find? ℓ (recordRow p.iface) = some mty) (hA : methodArg p.state p.rels mty = some A) :
    A.wf = true := by
  have hw := (checkShape_ok h).2
  obtain ⟨row, hrow, hf⟩ := recordRow_find hm
  rw [hrow] at hw
  simp only [Ty.wf, Bool.and_eq_true] at hw
  have := rowWf_find hw.2 hf
  obtain ⟨ks, rs, es, hks⟩ := methodArg_spec hA
  rw [hks] at this
  simp only [methodTy, Ty.wf, Bool.and_eq_true] at this
  exact this.2.2.1

theorem tyRowWire_iff : ∀ {r : List (Label × Ty)},
    Wire.tyRowWire r = true ↔ ∀ e ∈ r, Wire.labelOk e.1 = true ∧ Wire.tyWire e.2 = true
  | [] => by simp [Wire.tyRowWire]
  | (_, t) :: r => by simp [Wire.tyRowWire, tyRowWire_iff (r := r), and_assoc]

theorem tyRowWire_find {ℓ : Label} {t : Ty} {row : List (Label × Ty)} (hw : Wire.tyRowWire row = true)
    (h : Row.find? ℓ row = some t) : Wire.tyWire t = true := by
  induction row with
  | nil => simp [Row.find?] at h
  | cons e row ih =>
    obtain ⟨k, u⟩ := e
    simp only [Wire.tyRowWire, Bool.and_eq_true] at hw
    simp only [Row.find?] at h
    split at h
    · cases h; exact hw.1.2
    · exact ih hw.2 h

/-- Every state field of a loaded package has a data codec. -/
theorem state_fields_dataTy {p : Package} (h : p.checkShape = .ok ()) (hw : Wire.packageWire p = true) :
    ∀ e ∈ recordRow p.state, Wire.dataTy e.2 = true := by
  have hs := (checkShape_ok h).1
  simp only [Wire.packageWire, Bool.and_eq_true] at hw
  have hws := hw.1.1.1.1.1.1.2
  intro e he
  cases hst : p.state with
  | record row =>
    rw [hst] at hs hws he
    simp only [isRecordData, Ty.wf, Bool.and_eq_true] at hs
    simp only [Wire.tyWire, Bool.and_eq_true] at hws
    simp only [recordRow] at he
    simp only [Wire.dataTy, Bool.and_eq_true]
    exact ⟨rowWf_iff.mp hs.1.2 e he, (tyRowWire_iff.mp hws.2 e he).2⟩
  | _ => rw [hst] at he; simp [recordRow] at he

/-- Every method argument type of a loaded package has a data codec. -/
theorem methodArg_dataTy {p : Package} {ℓ : Label} {mty A : Ty} (h : p.checkShape = .ok ())
    (hpw : Wire.packageWire p = true)
    (hm : Row.find? ℓ (recordRow p.iface) = some mty) (hA : methodArg p.state p.rels mty = some A) :
    Wire.dataTy A = true := by
  simp only [Wire.packageWire, Bool.and_eq_true] at hpw
  have hwi := hpw.1.1.1.1.1.2
  obtain ⟨row, hrow, hf⟩ := recordRow_find hm
  rw [hrow] at hwi
  simp only [Wire.tyWire, Bool.and_eq_true] at hwi
  have ht := tyRowWire_find hwi.2 hf
  obtain ⟨ks, rs, es, hks⟩ := methodArg_spec hA
  rw [hks] at ht
  simp only [methodTy, Wire.tyWire, Bool.and_eq_true] at ht
  simp only [Wire.dataTy, Bool.and_eq_true]
  exact ⟨methodArg_wf h hm hA, ht.2.2.1⟩

/-- At a `dataTy` type the decoder is the type's stream: its type gate is passed. -/
theorem decodeData_of_dataTy {T : Ty} (h : Wire.dataTy T = true) (b : ByteArray) :
    Wire.decodeData T b = ((Wire.dataStream T).decode b).map (Wire.toData T) := by
  simp [Wire.decodeData, h]

theorem checkLaws_find {S : Ty} {row : List (Label × Ty)} :
    ∀ {ls : List Label}, checkLaws S row ls = .ok () → ∀ ℓ ∈ ls, Row.find? ℓ row = some (lawTy S)
  | [], _, ℓ, hl => by simp at hl
  | k :: ls, h, ℓ, hl => by
    unfold checkLaws at h
    split at h
    · simp at h
    · rename_i t ht
      split at h
      · rename_i he
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl
        · rw [ht, he]
        · exact checkLaws_find h ℓ hl
      · simp at h

theorem checkFields_law {p : Package} (h : p.checkFields = .ok ()) {ℓ : Label} (hl : ℓ ∈ p.laws) :
    Row.find? ℓ (recordRow p.iface) = some (lawTy p.state) := by
  unfold Package.checkFields at h
  split at h
  · rename_i row hrow
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rw [hrow]; exact checkLaws_find h ℓ hl
  · simp at h

/-! ## A method's rows argument is a value of its declared rows type (LANG-49) -/

theorem rowConforms_of_rel : ∀ {ds : List (Label × Data)} {r : List (Label × Ty)},
    Row.Rel Conforms ds r → RowConforms ds r
  | _, _, .nil => .nil
  | _, _, .cons h hr => .cons h (rowConforms_of_rel hr)

theorem rowConforms_append : ∀ {a b : List (Label × Data)} {r s : List (Label × Ty)},
    RowConforms a r → RowConforms b s → RowConforms (a ++ b) (r ++ s)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h1 h2, h => .cons h1 (rowConforms_append h2 h)

theorem optD_conforms {T : Ty} : ∀ {o : Option Data}, (∀ x, o = some x → Conforms x T) →
    Conforms (optD o) (optTy T)
  | none, _ => .inj (by simp [Row.find?]) (.record .nil)
  | some x, h => .inj (by simp [Row.find?]) (h x rfl)

theorem zipIdx_slots_conforms {T : Ty} {xs : List Data} (hx : ∀ x ∈ xs, Conforms x T) :
    ∀ (L : List Label) (k : Nat),
      RowConforms ((L.zipIdx k).map fun p => (p.1, optD xs[p.2]?)) (L.map fun l => (l, optTy T))
  | [], _ => .nil
  | l :: L, k => by
    simp only [List.zipIdx_cons, List.map_cons]
    exact .cons (optD_conforms fun x hx' => hx x (List.mem_of_getElem? hx')) (zipIdx_slots_conforms hx L (k + 1))

theorem slotsD_conforms {T : Ty} {xs : List Data} (hx : ∀ x ∈ xs, Conforms x T) (c : String) (n : Nat) :
    RowConforms (slotsD c n xs) ((slotLabels c n).map fun l => (l, optTy T)) :=
  zipIdx_slots_conforms hx _ 0

theorem zip_rel : ∀ (l : List (Label × Ty)) (n : Nat) (fs : List (Label × Data)) (f : Nat → Label),
    RowConforms fs ((l.zipIdx n).map fun p => (f p.2, p.1.2)) →
    Row.Rel Conforms ((l.zip fs).map fun p => (p.1.1, p.2.2)) l
  | [], _, fs, _, h => by cases h; exact .nil
  | (ℓ, T) :: l, n, fs, f, h => by
    simp only [List.zipIdx_cons, List.map_cons] at h
    cases h with
    | cons hd hr =>
      simp only [List.zip_cons_cons, List.map_cons]
      exact .cons hd (zip_rel l (n + 1) _ f hr)

/-- A key read back from its bytes is a value of the prefix's record type. -/
theorem keyOf_conforms {d : RelDecl} {m : Nat} {b : ByteArray} {k : Data} (h : keyOf d m b = .ok k) :
    Conforms k (preTy d m) := by
  unfold keyOf at h
  split at h
  · rename_i fs hfs
    cases h
    have hc : Conforms (.record fs) (.record _) := decodeData_conforms hfs
    cases hc with
    | record hr =>
      exact .record (rowConforms_of_rel (Row.Rel.sort (zip_rel (d.key.take m) 0 fs (fun i => "k" ++ toString i) hr)))
  · cases h
  · cases h

theorem keyOf_conforms_key {d : RelDecl} {b : ByteArray} {k : Data} (h : keyOf d d.key.length b = .ok k) :
    Conforms k (keyTy d) := by
  have := keyOf_conforms h
  rwa [preTy, List.take_length] at this

theorem checked_eq {D : Type} {digestOf : ByteArray → Option D} {what : String} {d d' : Data}
    (h : checked digestOf what d = .ok d') : d' = d := by
  unfold checked at h; split at h <;> simp_all

theorem liftS_eq {D α : Type} {what : String} {e : Except String α} {a : α}
    (h : liftS (D := D) what e = .ok a) : e = .ok a := by
  unfold liftS at h; split at h <;> simp_all

theorem valOf_conforms {D : Type} {digestOf : ByteArray → Option D} {d : RelDecl} {what : String}
    {b : ByteArray} {v : Data} (h : valOf digestOf d what b = .ok v) : Conforms v d.val := by
  unfold valOf at h
  split at h
  · rename_i v' hv; rw [checked_eq h]; exact decodeData_conforms hv
  · cases h

theorem mapM_ok_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
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
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨x, by simp, hy⟩
        · obtain ⟨w, hw, hf⟩ := mapM_ok_mem hys z hz
          exact ⟨w, by simp [hw], hf⟩

theorem map_some_ok {ε : Type} {e : Except ε Data} {o : Option Data} (h : (some <$> e) = .ok o) :
    ∃ v, e = .ok v ∧ o = some v := by
  cases e with
  | error _ => cases h
  | ok v => simp only [Functor.map, Except.map, Except.ok.injEq] at h; exact ⟨v, rfl, h.symm⟩

theorem key_conf {D : Type} {digestOf : ByteArray → Option D} {d : RelDecl} {w w' : String}
    {b : ByteArray} {k0 k : Data} (h2 : checked digestOf w' k0 = .ok k)
    (h1 : liftS (D := D) w (keyOf d d.key.length b) = .ok k0) : Conforms k (keyTy d) := by
  rw [checked_eq h2]; exact keyOf_conforms_key (liftS_eq h1)

theorem pre_conf {D : Type} {digestOf : ByteArray → Option D} {d : RelDecl} {m : Nat} {w w' : String}
    {b : ByteArray} {k0 k : Data} (h2 : checked digestOf w' k0 = .ok k)
    (h1 : liftS (D := D) w (keyOf d m b) = .ok k0) : Conforms k (preTy d m) := by
  rw [checked_eq h2]; exact keyOf_conforms (liftS_eq h1)

theorem mapM_ok_length {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ys.length = xs.length
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i ys' hys
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [mapM_ok_length hys]

/-- **A range read's rows are rows of the relation** (LANG-49, PROTOCOL-51): every datum
`rangeRowData` builds is a value of `rowTy d`, its key at the key type and its value at the value
type. -/
theorem rangeRowData_conforms {D : Type} {digestOf : ByteArray → Option D} {ℓ : Label} {d : RelDecl}
    {rows : List (RowSlot D × RowLeaf)} {ds : List Data} (h : rangeRowData digestOf ℓ d rows = .ok ds) :
    ∀ y ∈ ds, Conforms y (rowTy d) := by
  unfold rangeRowData at h
  intro y hy
  obtain ⟨q, -, hq⟩ := mapM_ok_mem h y hy
  simp only [bind, Except.bind, pure, Except.pure] at hq
  repeat' split at hq
  all_goals first | cases hq | skip
  all_goals exact .record (.cons (key_conf ‹_› ‹_›) (.cons (valOf_conforms ‹_›) .nil))

/-- **One datum per listed row** (PROTOCOL-51): `rangeRowData` drops no row of the listing and adds
none. -/
theorem rangeRowData_length {D : Type} {digestOf : ByteArray → Option D} {ℓ : Label} {d : RelDecl}
    {rows : List (RowSlot D × RowLeaf)} {ds : List Data} (h : rangeRowData digestOf ℓ d rows = .ok ds) :
    ds.length = rows.length := by
  unfold rangeRowData at h
  exact mapM_ok_length h

theorem relReads_conforms {D : Type} {digestOf : ByteArray → Option D} {rv : RowView D} {self : D}
    {i : Nat} {ℓ : Label} {d : RelDecl} {x : RelRead} {v : Data}
    (h : relReads digestOf rv self i ℓ d x = .ok v) : Conforms v (relReadTy d x) := by
  unfold relReads at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | cases h | skip
  all_goals
    simp only [relReadTy, ‹x.range = _›]
    refine .record (rowConforms_append (slotsD_conforms ?pts "p" _) ?rng)
    case pts =>
      intro y hy
      obtain ⟨q, -, hq⟩ := mapM_ok_mem ‹List.mapM _ (rv.points self i) = Except.ok _› y hy
      repeat' split at hq
      all_goals first | cases hq | skip
      all_goals
        refine .record (.cons (key_conf ‹_› ‹_›) (.cons ?_ .nil))
        exact optD_conforms (fun w hw => by
          first
            | (cases hw; done)
            | (cases hw
               obtain ⟨u, hu, hs⟩ := map_some_ok ‹(some <$> valOf digestOf d _ _) = Except.ok _›
               cases hs; exact valOf_conforms hu))
    case rng =>
      first
        | exact .nil
        | rename_i rs hrows
          exact .cons (.record (.cons (pre_conf ‹_› ‹_›)
            (.cons (.record (slotsD_conforms (rangeRowData_conforms hrows) "r" _)) .nil))) .nil

theorem mapM_rowConforms {α ε : Type} {f : α → Except ε (Label × Data)} {g : α → Option (Label × Ty)}
    (hf : ∀ a y, f a = .ok y → ∃ t, g a = some t ∧ y.1 = t.1 ∧ Conforms y.2 t.2) :
    ∀ {xs : List α} {ys : List (Label × Data)}, xs.mapM f = .ok ys → RowConforms ys (xs.filterMap g)
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; exact .nil
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
        obtain ⟨t, hg, h1, h2⟩ := hf x y hy
        obtain ⟨ℓ, v⟩ := y
        obtain ⟨ℓ', T⟩ := t
        simp only at h1 h2
        subst h1
        rw [List.filterMap_cons, hg]
        exact .cons h2 (mapM_rowConforms hf hys)

/-- **The rows a run reads are a value of the method's declared rows type** (LANG-49): what
`readsData` builds from the caller's row view is data at `readsTy`, whatever the view holds. -/
theorem readsData_conforms {D : Type} {digestOf : ByteArray → Option D} {rels : List (Label × RelDecl)}
    {rv : RowView D} {self : D} {rs : List (Label × RelRead)} {v : Data}
    (h : readsData digestOf rels rv self rs = .ok v) : Conforms v (readsTy rels rs) := by
  unfold readsData at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i fs hfs
    cases h
    refine .record (mapM_rowConforms (fun a y hy => ?_) hfs)
    repeat' split at hy
    all_goals first | cases hy | skip
    exact ⟨_, by rw [‹Row.find? _ rels = some _›]; rfl, rfl, relReads_conforms ‹_›⟩

/-- The run inside `Program.run`, on what it decoded, never reaches `stuck`: it ends with a value
of the method's result type (its calls and its new state) or a named non-`stuck` fault. -/
theorem invoke_never_stuck {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat} {p : Package}
    {rv : RowView D} {ℓ : Label} {mty : Ty} {sg : Sig} {state : Slots} {args : ByteArray}
    {sd ad wd : Data} {r : Req D} {ticks : Nat}
    (hload : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p)
    (hm : Row.find? ℓ (recordRow p.iface) = some mty) (hA : methodSig p.state p.rels mty = some sg)
    (hstate : readState digestOf (recordRow p.state) state = .ok sd)
    (hargs : Wire.decodeData sg.arg args = .ok ad)
    (hrows : readsData digestOf p.rels rv r.self sg.reads = .ok wd)
    (hr : reqOk bytesOf r = true) :
    RunOK L.ifaces (resultTy p.state sg.calls (editTy p.rels) sg.edits)
      (run L.lib Bounds.stackMax ticks 0
        (State.init (apply4 g ℓ) [(reqData bytesOf r).toVal, ad.toVal, sd.toVal, wd.toVal])) := by
  have hs := readState_conforms hstate
  rw [← checkShape_state ((load_checked hload g p hp).1)] at hs
  exact method_run_sound hload hp hm hA (toVal_typed hs) (toVal_typed (decodeData_conforms hargs))
    (toVal_typed (reqOk_conforms hr)) (toVal_typed (readsData_conforms hrows))

/-- The twin for laws: every law of a loaded package, run in `Program.judge` on the old and new states
it decoded from the slots and the request, never reaches `stuck`: it ends with a value of
`verdictTy` or a named budget/arithmetic fault, at every tick budget. -/
theorem law_never_stuck {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat} {p : Package}
    {ℓ : Label} {old new : Slots} {od nd : Data} {r : Req D} {ticks : Nat}
    (hload : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p) (hl : ℓ ∈ p.laws)
    (hold : readState digestOf (recordRow p.state) old = .ok od)
    (hnew : readState digestOf (recordRow p.state) new = .ok nd)
    (hr : reqOk bytesOf r = true) :
    RunOK L.ifaces verdictTy
      (run L.lib Bounds.stackMax ticks 0
        (State.init (apply3 g ℓ) [(reqData bytesOf r).toVal, nd.toVal, od.toVal])) := by
  obtain ⟨hlib, _⟩ := load_libTy hload
  obtain ⟨hshape, hfields, _⟩ := load_checked hload g p hp
  have hrec := checkShape_state hshape
  have ho := readState_conforms hold
  have hnw := readState_conforms hnew
  rw [← hrec] at ho hnw
  obtain ⟨row, hrow, hfind⟩ := recordRow_find (checkFields_law hfields hl)
  have href : HasType (Loaded.ifaces L) [reqTy, p.state, p.state] (.ref g) (.record row) :=
    .ref (by rw [← hrow]; simp [Loaded.ifaces, hp])
  have ht : HasType (Loaded.ifaces L) [reqTy, p.state, p.state] (apply3 g ℓ) verdictTy :=
    .app (.app (.app (.get href hfind) (.var rfl)) (.var rfl)) (.var rfl)
  exact run_sound hlib _ _ _ (.eval (.cons (toVal_typed (reqOk_conforms hr))
    (.cons (toVal_typed hnw) (.cons (toVal_typed ho) .nil))) ht .nil)

/-! ## The resident readers -/

/-- What `argsOf` produces decodes, at the argument type `resolveMethod` gives the package, to the
data the text read to: so the run (`runMeasured`, which resolves the same method) decodes a
planned call's arguments. -/
theorem argsOf_decodes {D : Type} [DecidableEq D] {digestOf : ByteArray → Option D} {look : Pinned D}
    {pkg : D} {method : Nat} {text : String} {b : ByteArray} (h : argsOf digestOf look pkg method text = .ok b) :
    ∃ p ℓ sg d, readPackage look pkg = .ok p ∧ resolveMethod (D := D) p method = .ok (ℓ, sg) ∧
      readAt digestOf sg.arg text = .ok d ∧ Wire.decodeData sg.arg b = .ok d := by
  unfold argsOf at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · cases h
    · rename_i la hr
      obtain ⟨ℓ, sg⟩ := la
      split at h
      · cases h
      · rename_i d hd
        split at h
        · rename_i b' he
          cases h
          exact ⟨p, ℓ, sg, d, hp, hr, hd, Wire.decodeData_eq_ok_iff.mpr he⟩
        · cases h

theorem lookup_append_of_lt {pre t : Slots} {k : Nat} (h : ∀ e ∈ pre, e.1 < k) :
    (pre ++ t).lookup k = t.lookup k := by
  induction pre with
  | nil => rfl
  | cons e pre ih =>
    have he : e.1 ≠ k := Nat.ne_of_lt (h e (by simp))
    have hk : (k == e.1) = false := by simp; exact fun h' => he h'.symm
    simp only [List.cons_append, List.lookup, hk]
    exact ih fun x hx => h x (by simp [hx])

/-- The state slots `stateSlots` writes read back, through `readState`'s own loop, to the data they
were written from. -/
theorem readState_go_stateSlots {D : Type} {digestOf : ByteArray → Option D} :
    ∀ (row : List (Label × Ty)) (ds : List (Label × Data)) (i : Nat)
    (t pre : Slots), RowConforms ds row → stateSlots row ds i = some t →
      (∀ e ∈ pre, e.1 < stateBase + i) → digestsOk digestOf (Data.rowDigests ds) = true →
      readState.go digestOf (pre ++ t) row i = .ok (.record ds)
  | [], [], i, t, pre, _, ht, _, _ => by
    simp only [stateSlots, Option.some.injEq] at ht
    subst ht
    simp [readState.go]
  | (ℓ, T) :: r, (ℓ', d) :: ds, i, t, pre, hc, ht, hpre, hdg => by
    simp only [Data.rowDigests, digestsOk, List.all_append, Bool.and_eq_true] at hdg
    cases hc with
    | cons hd0 hr0 =>
    unfold stateSlots at ht
    split at ht
    · rename_i b s he hs
      cases ht
      have hl : (pre ++ (stateBase + i, b) :: s).lookup (stateBase + i) = some b := by
        rw [lookup_append_of_lt hpre]; simp [List.lookup]
      have hd : Wire.decodeData T b = .ok d := Wire.decodeData_eq_ok_iff.mpr he
      have hrest : readState.go digestOf (pre ++ (stateBase + i, b) :: s) r (i + 1) = .ok (.record ds) := by
        have := readState_go_stateSlots r ds (i + 1) s (pre ++ [(stateBase + i, b)]) hr0 hs (by
          intro e he'
          simp only [List.mem_append, List.mem_singleton] at he'
          rcases he' with he' | rfl
          · have := hpre e he'; omega
          · simp) (by simpa [digestsOk] using hdg.2)
        simpa using this
      have hd1 : digestsOk digestOf d.digests = true := by simpa [digestsOk] using hdg.1
      unfold readState.go
      simp only [Slots.get] at hl ⊢
      rw [hl]
      simp only [hd, hrest, hd1, if_true]
    · cases ht
  | [], _ :: _, _, _, _, hc, _, _, _ => by cases hc
  | _ :: _, [], _, _, _, hc, _, _, _ => by cases hc

theorem readData_record {T : Ty} {text : String} {ds : List (Label × Data)}
    (h : Read.readData T text = .ok (.record ds)) : ∃ row, T = .record row ∧ RowConforms ds row := by
  unfold Read.readData at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · have hc := Read.dataAt_conforms _ _ _ h
    cases hc with
    | record hrow => exact ⟨_, rfl, hrow⟩

/-- What `seedOf` produces reads back, at the package's state type, to the data the text read to:
a seed object's state is the resident's text, and nothing else. -/
theorem seedOf_reads {D : Type} [DecidableEq D] {digestOf : ByteArray → Option D} {look : Pinned D}
    {pkg : D} {text : String} {s : Slots} (h : seedOf digestOf look pkg text = .ok s) :
    ∃ p d, readPackage look pkg = .ok p ∧ readAt digestOf p.state text = .ok d ∧
      readState digestOf (recordRow p.state) s = .ok d := by
  unfold seedOf at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · cases h
    · rename_i d hd
      split at h
      · rename_i ds
        split at h
        · rename_i t ht
          cases h
          refine ⟨p, .record ds, hp, hd, ?_⟩
          have hr : Read.readData p.state text = .ok (.record ds) ∧
              digestsOk digestOf (Data.rowDigests ds) = true := by
            unfold readAt at hd
            split at hd
            · rename_i d' h'
              split at hd
              · rename_i hok
                cases hd
                exact ⟨h', by simpa [Data.digests] using hok⟩
              · cases hd
            · cases hd
          obtain ⟨row, hrow, hc⟩ := readData_record hr.1
          rw [hrow] at ht ⊢
          simpa [readState, recordRow] using readState_go_stateSlots row ds 0 _ [] hc ht (by simp) hr.2
        · cases h
      · cases h

end Nanodregg.Lang
