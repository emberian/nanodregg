/-
# Lang.Proofs.Invoke — what a receiver decodes from cells is typed, so an invoked method never
gets stuck

Composes `readState_conforms`/`decodeData_conforms` (decoded data has its type), `toVal_typed` and
`method_run_sound`: for the run `Program.run` performs — a loaded package's method on the state read
from the object's slots, the arguments decoded from the call, and the request — the outcome is a
value of the package's state type or a named non-`stuck` fault, at every tick budget. The only
premise left about the World is the request's own bounds (digests fit a slot, the window fits u64).
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

/-- The run inside `Program.run`, on what it decoded, never reaches `stuck`. -/
theorem invoke_never_stuck {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat} {p : Package}
    {ℓ : Label} {mty A : Ty} {state : Slots} {args : ByteArray} {sd ad : Data} {r : Req D}
    {ticks : Nat}
    (hload : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p)
    (hm : Row.find? ℓ (recordRow p.iface) = some mty) (hA : methodArg p.state mty = some A)
    (hstate : readState (recordRow p.state) state = .ok sd)
    (hstateRec : p.state = .record (recordRow p.state))
    (hargs : Wire.decodeData A args = .ok ad)
    (ha : (bytesOf r.agent).size ≤ Bounds.bytesMax) (hpr : (bytesOf r.principal).size ≤ Bounds.bytesMax)
    (hn : r.notBefore < Bounds.natLimit) (hv : r.validUntil < Bounds.natLimit) :
    RunOK L.ifaces p.state
      (run L.lib Bounds.stackMax ticks 0
        (State.init (apply3 g ℓ) [(reqData bytesOf r).toVal, ad.toVal, sd.toVal])) := by
  have hs := readState_conforms hstate
  rw [← hstateRec] at hs
  exact method_run_sound hload hp hm hA (toVal_typed hs) (toVal_typed (decodeData_conforms hargs))
    (toVal_typed (reqData_conforms bytesOf r ha hpr hn hv))

end Nanodregg.Lang
