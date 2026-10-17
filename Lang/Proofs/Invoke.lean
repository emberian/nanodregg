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

theorem readState_go_conforms {s : Slots} :
    ∀ (row : List (Label × Ty)) (i : Nat) {d : Data}, readState.go s row i = .ok d →
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
        cases h
        have h2 := readState_go_conforms row (i + 1) hr
        cases h2 with
        | record hrow => exact .record (.cons (decodeData_conforms hd) hrow)
      all_goals simp at h

theorem readState_conforms {row : List (Label × Ty)} {s : Slots} {d : Data}
    (h : readState row s = .ok d) : Conforms d (.record row) :=
  readState_go_conforms row 0 h

theorem reqOk_conforms {D : Type} {bytesOf : D → ByteArray} {r : Req D} (h : reqOk bytesOf r = true) :
    Conforms (reqData bytesOf r) reqTy := by
  simp only [reqOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨ha, hp⟩, hnb⟩, hvu⟩, ho⟩ := h
  refine .record (.cons (.bytes ha) (.cons (.nat hnb) (.cons ?_ (.cons (.bytes hp) (.cons (.nat hvu) .nil)))))
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
    (hm : Row.find? ℓ (recordRow p.iface) = some mty) (hA : methodArg p.state mty = some A) :
    A.wf = true := by
  have hw := (checkShape_ok h).2
  obtain ⟨row, hrow, hf⟩ := recordRow_find hm
  rw [hrow] at hw
  simp only [Ty.wf, Bool.and_eq_true] at hw
  have := rowWf_find hw.2 hf
  rw [methodArg_spec hA] at this
  simp only [methodTy, Ty.wf, Bool.and_eq_true] at this
  exact this.2.1

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
  have hws := hw.1.1.1.1.2
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
    (hm : Row.find? ℓ (recordRow p.iface) = some mty) (hA : methodArg p.state mty = some A) :
    Wire.dataTy A = true := by
  simp only [Wire.packageWire, Bool.and_eq_true] at hpw
  have hwi := hpw.1.1.1.2
  obtain ⟨row, hrow, hf⟩ := recordRow_find hm
  rw [hrow] at hwi
  simp only [Wire.tyWire, Bool.and_eq_true] at hwi
  have ht := tyRowWire_find hwi.2 hf
  rw [methodArg_spec hA] at ht
  simp only [methodTy, Wire.tyWire, Bool.and_eq_true] at ht
  simp only [Wire.dataTy, Bool.and_eq_true]
  exact ⟨methodArg_wf h hm hA, ht.2.1⟩

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
    · rw [hrow]; exact checkLaws_find h ℓ hl
  · simp at h

/-- The run inside `Program.run`, on what it decoded, never reaches `stuck`. -/
theorem invoke_never_stuck {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat} {p : Package}
    {ℓ : Label} {mty A : Ty} {state : Slots} {args : ByteArray} {sd ad : Data} {r : Req D}
    {ticks : Nat}
    (hload : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p)
    (hm : Row.find? ℓ (recordRow p.iface) = some mty) (hA : methodArg p.state mty = some A)
    (hstate : readState (recordRow p.state) state = .ok sd)
    (hargs : Wire.decodeData A args = .ok ad)
    (hr : reqOk bytesOf r = true) :
    RunOK L.ifaces p.state
      (run L.lib Bounds.stackMax ticks 0
        (State.init (apply3 g ℓ) [(reqData bytesOf r).toVal, ad.toVal, sd.toVal])) := by
  have hs := readState_conforms hstate
  rw [← checkShape_state ((load_checked hload g p hp).1)] at hs
  exact method_run_sound hload hp hm hA (toVal_typed hs) (toVal_typed (decodeData_conforms hargs))
    (toVal_typed (reqOk_conforms hr))

/-- The twin for laws: every law of a loaded package, run in `Program.judge` on the old and new states
it decoded from the slots and the request, never reaches `stuck`: it ends with a value of
`verdictTy` or a named budget/arithmetic fault, at every tick budget. -/
theorem law_never_stuck {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat} {p : Package}
    {ℓ : Label} {old new : Slots} {od nd : Data} {r : Req D} {ticks : Nat}
    (hload : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p) (hl : ℓ ∈ p.laws)
    (hold : readState (recordRow p.state) old = .ok od)
    (hnew : readState (recordRow p.state) new = .ok nd)
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
theorem argsOf_decodes {D : Type} [DecidableEq D] {look : Pinned D} {pkg : D} {method : Nat}
    {text : String} {b : ByteArray} (h : argsOf look pkg method text = .ok b) :
    ∃ p ℓ A d, readPackage look pkg = .ok p ∧ resolveMethod (D := D) p method = .ok (ℓ, A) ∧
      readAt (D := D) A text = .ok d ∧ Wire.decodeData A b = .ok d := by
  unfold argsOf at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · cases h
    · rename_i la hr
      obtain ⟨ℓ, A⟩ := la
      split at h
      · cases h
      · rename_i d hd
        split at h
        · rename_i b' he
          cases h
          exact ⟨p, ℓ, A, d, hp, hr, hd, Wire.decodeData_eq_ok_iff.mpr he⟩
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
theorem readState_go_stateSlots : ∀ (row : List (Label × Ty)) (ds : List (Label × Data)) (i : Nat)
    (t pre : Slots), RowConforms ds row → stateSlots row ds i = some t →
      (∀ e ∈ pre, e.1 < stateBase + i) → readState.go (pre ++ t) row i = .ok (.record ds)
  | [], [], i, t, pre, _, ht, _ => by
    simp only [stateSlots, Option.some.injEq] at ht
    subst ht
    simp [readState.go]
  | (ℓ, T) :: r, (ℓ', d) :: ds, i, t, pre, hc, ht, hpre => by
    cases hc with
    | cons hd0 hr0 =>
    unfold stateSlots at ht
    split at ht
    · rename_i b s he hs
      cases ht
      have hl : (pre ++ (stateBase + i, b) :: s).lookup (stateBase + i) = some b := by
        rw [lookup_append_of_lt hpre]; simp [List.lookup]
      have hd : Wire.decodeData T b = .ok d := Wire.decodeData_eq_ok_iff.mpr he
      have hrest : readState.go (pre ++ (stateBase + i, b) :: s) r (i + 1) = .ok (.record ds) := by
        have := readState_go_stateSlots r ds (i + 1) s (pre ++ [(stateBase + i, b)]) hr0 hs (by
          intro e he'
          simp only [List.mem_append, List.mem_singleton] at he'
          rcases he' with he' | rfl
          · have := hpre e he'; omega
          · simp)
        simpa using this
      unfold readState.go
      simp only [Slots.get] at hl ⊢
      rw [hl]
      simp only [hd, hrest]
    · cases ht
  | [], _ :: _, _, _, _, hc, _, _ => by cases hc
  | _ :: _, [], _, _, _, hc, _, _ => by cases hc

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
theorem seedOf_reads {D : Type} [DecidableEq D] {look : Pinned D} {pkg : D} {text : String}
    {s : Slots} (h : seedOf look pkg text = .ok s) :
    ∃ p d, readPackage look pkg = .ok p ∧ readAt (D := D) p.state text = .ok d ∧
      readState (recordRow p.state) s = .ok d := by
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
          have hr : Read.readData p.state text = .ok (.record ds) := by
            unfold readAt at hd
            split at hd
            · rename_i d' h'
              cases hd
              exact h'
            · cases hd
          obtain ⟨row, hrow, hc⟩ := readData_record hr
          rw [hrow] at ht ⊢
          simpa [readState, recordRow] using readState_go_stateSlots row ds 0 _ [] hc ht (by simp)
        · cases h
      · cases h

end Nanodregg.Lang
