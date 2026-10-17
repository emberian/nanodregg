/-
# Kernel.Proofs.Bytes — when two concatenations are equal
-/
namespace Nanodregg.Kernel

theorem bytes_append_inj {x y x' y' : ByteArray} (h : x ++ y = x' ++ y') (hs : x.size = x'.size) :
    x = x' ∧ y = y' := by
  have hd : x.data ++ y.data = x'.data ++ y'.data := by
    rw [← ByteArray.data_append, ← ByteArray.data_append, h]
  obtain ⟨h₁, h₂⟩ := Array.append_inj hd hs
  exact ⟨ByteArray.ext h₁, ByteArray.ext h₂⟩

end Nanodregg.Kernel
