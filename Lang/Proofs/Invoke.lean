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
left about the World is the request's own bounds (digests fit a slot, the window fits u64).
-/
import Lang.Proofs.Load
import Lang.Proofs.Data

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

theorem reqData_conforms {D : Type} (bytesOf : D → ByteArray) (r : Req D)
    (ha : (bytesOf r.agent).size ≤ Bounds.bytesMax) (hp : (bytesOf r.principal).size ≤ Bounds.bytesMax)
    (hn : r.notBefore < Bounds.natLimit) (hv : r.validUntil < Bounds.natLimit) :
    Conforms (reqData bytesOf r) reqTy :=
  .record (.cons (.bytes ha) (.cons (.nat hn) (.cons (.bytes hp) (.cons (.nat hv) .nil))))

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

theorem rowWf_find {ℓ : Label} {t : Ty} :
    ∀ {row : List (Label × Ty)}, Ty.rowWf row = true → Row.find? ℓ row = some t → t.wf = true
  | [], _, h => by simp [Row.find?] at h
  | (k, u) :: row, hw, h => by
    simp only [Ty.rowWf, Bool.and_eq_true] at hw
    simp only [Row.find?] at h
    split at h
    · cases h; exact hw.1
    · exact rowWf_find hw.2 h

/-- What `runMethod` decodes is at canonical types: every state field's type and every method's
argument type is `wf`, so `decodeData` passes its canonical-type gate (`decodeData_of_wf`) and reads
with the type's stream. -/
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

theorem decodeData_of_wf {T : Ty} (h : T.wf = true) (b : ByteArray) :
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
    (ha : (bytesOf r.agent).size ≤ Bounds.bytesMax) (hpr : (bytesOf r.principal).size ≤ Bounds.bytesMax)
    (hn : r.notBefore < Bounds.natLimit) (hv : r.validUntil < Bounds.natLimit) :
    RunOK L.ifaces p.state
      (run L.lib Bounds.stackMax ticks 0
        (State.init (apply3 g ℓ) [(reqData bytesOf r).toVal, ad.toVal, sd.toVal])) := by
  have hs := readState_conforms hstate
  rw [← checkShape_state ((load_checked hload g p hp).1)] at hs
  exact method_run_sound hload hp hm hA (toVal_typed hs) (toVal_typed (decodeData_conforms hargs))
    (toVal_typed (reqData_conforms bytesOf r ha hpr hn hv))

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
    (ha : (bytesOf r.agent).size ≤ Bounds.bytesMax) (hpr : (bytesOf r.principal).size ≤ Bounds.bytesMax)
    (hn : r.notBefore < Bounds.natLimit) (hv : r.validUntil < Bounds.natLimit) :
    RunOK L.ifaces verdictTy
      (run L.lib Bounds.stackMax ticks 0
        (State.init (apply3 g ℓ) [(reqData bytesOf r).toVal, nd.toVal, od.toVal])) := by
  obtain ⟨hlib, _⟩ := load_libTy hload
  obtain ⟨hshape, hfields⟩ := load_checked hload g p hp
  have hrec := checkShape_state hshape
  have ho := readState_conforms hold
  have hnw := readState_conforms hnew
  rw [← hrec] at ho hnw
  obtain ⟨row, hrow, hfind⟩ := recordRow_find (checkFields_law hfields hl)
  have href : HasType (Loaded.ifaces L) [reqTy, p.state, p.state] (.ref g) (.record row) :=
    .ref (by rw [← hrow]; simp [Loaded.ifaces, hp])
  have ht : HasType (Loaded.ifaces L) [reqTy, p.state, p.state] (apply3 g ℓ) verdictTy :=
    .app (.app (.app (.get href hfind) (.var rfl)) (.var rfl)) (.var rfl)
  exact run_sound hlib _ _ _ (.eval (.cons (toVal_typed (reqData_conforms bytesOf r ha hpr hn hv))
    (.cons (toVal_typed hnw) (.cons (toVal_typed ho) .nil))) ht .nil)

end Nanodregg.Lang
