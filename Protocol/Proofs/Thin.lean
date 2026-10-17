/-
# Protocol.Proofs.Thin — an adopted base is the pinned one

`accept_done`: whatever the writer served, a World `accept` adopts re-encodes (under a canonical
World codec) to bytes whose digest is the pin's, at the pinned height. So the only trust a thin member
places is in its pin; a forged base is never adopted unless it collides with the pin's digest.
-/
import Protocol.Thin

namespace Nanodregg.Protocol.Thin

theorem Refusal.name_injective (a b : Refusal) (h : a.name = b.name) : a.tag = b.tag := by
  cases a <;> cases b <;> simp_all [Refusal.name, Refusal.tag]

variable {W : Type}

theorem finish_done {B : Base W} {pin : Pin} {got : ByteArray} {w : W}
    (canonical : ∀ b v, B.world.decode b = .ok v → B.world.bytes v = b)
    (h : finish B pin got = .ok (.done w)) :
    B.digest (B.world.bytes w) = pin.digest ∧ B.heightOf w = pin.height := by
  unfold finish at h
  split at h
  · cases h
  · rename_i hd
    split at h
    · cases h
    · rename_i v hv
      split at h
      · cases h
      · rename_i hh
        cases h
        exact ⟨by rw [canonical _ _ hv]; exact Classical.not_not.mp hd, Classical.not_not.mp hh⟩

/-- An adopted World is the pinned one: its canonical bytes hash to the pin's digest and it is at
the pin's height, whatever the pages stated. `canonical` is the World codec's one-pass canonicity
(CODEC's `eq_bytes_of_world_decode`). -/
theorem accept_done {B : Base W} {pin : Pin} {dl : Option Download} {p : Page} {w : W}
    (canonical : ∀ b v, B.world.decode b = .ok v → B.world.bytes v = b)
    (h : accept B pin dl p = .ok (.done w)) :
    B.digest (B.world.bytes w) = pin.digest ∧ B.heightOf w = pin.height := by
  unfold accept at h
  dsimp only at h
  repeat' (split at h; · cases h)
  exact finish_done canonical h

/-- A page that states another height than the pin is never adopted, whatever its bytes. -/
theorem accept_moved {B : Base W} {pin : Pin} {dl : Option Download} {p : Page}
    (h : p.height ≠ pin.height) : accept B pin dl p = .error (.baseMoved p.height) := by
  unfold accept
  exact if_pos h

end Nanodregg.Protocol.Thin
