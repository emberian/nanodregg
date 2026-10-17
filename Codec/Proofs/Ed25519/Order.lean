import Codec.Proofs.Ladder
import Codec.Proofs.Ed25519Stage

/-!
# The base point has order L (CODEC-23 part 3, the group order)

`[L] B` is the identity. The ladder over the 253 bits of `L` is computed in four kernel-checked chunks
through literal intermediate points (`Ed25519Stage.mul2_of_chunks`, the CODEC-20 memory shape), and
`mul2_spec` turns the deployed ladder into `[L] B`. Tooth `B_not_small`: `[8] B` is not the identity, so the
cofactor in `verify` does not kill `B`.
-/

namespace Nanodregg.Codec.Ed25519

private def O1 : Point := ⟨⟨35767846, 2741912, 15626709, 10951416, 31695163, 9014075, 40545260, 6162975, 5053671, 2820373⟩, ⟨44017081, 7506262, 28176246, 14805940, 49644571, 10911307, 9027049, 9689879, 30624876, 12921248⟩, ⟨65359857, 5752868, 43969662, 6347709, 15529166, 11118020, 26443615, 11922001, 10258690, 398246⟩, ⟨36299019, 10490643, 56392155, 8927325, 16048021, 25238144, 1717852, 32315903, 14328370, 7246117⟩⟩
private def O2 : Point := ⟨⟨45473367, 27265434, 21740649, 15784074, 5633220, 13967560, 25910349, 31393949, 36742419, 20668905⟩, ⟨51184446, 23538262, 64772475, 18661511, 26389226, 6263832, 30709820, 6582074, 46248851, 31882813⟩, ⟨62147462, 27189685, 13778675, 8739336, 44910373, 309750, 29194479, 21491018, 46970350, 3993147⟩, ⟨26122100, 24499337, 49004817, 25527012, 5385993, 5232874, 34512938, 22062747, 2117405, 28585096⟩⟩
private def O3 : Point := ⟨⟨13714712, 17718394, 7094536, 8634986, 30761095, 14468365, 54819929, 33336161, 33957432, 28976811⟩, ⟨33568103, 14719064, 62664767, 11883124, 17305828, 16445151, 18256290, 31788650, 12103343, 5913617⟩, ⟨16728993, 32401175, 61198431, 9647471, 46433310, 31915649, 49426746, 15115594, 1937258, 28219519⟩, ⟨51916362, 6685123, 14565538, 4916307, 66669720, 20254717, 38461662, 20326492, 57576751, 20671881⟩⟩
private def O4 : Point := ⟨⟨67108845, 33554431, 67108863, 33554431, 67108863, 33554431, 67108863, 33554431, 67108863, 33554431⟩, ⟨20709445, 4123787, 64414044, 32586068, 7802700, 27989886, 37739855, 4833037, 25954877, 25117026⟩, ⟨20709445, 4123787, 64414044, 32586068, 7802700, 27989886, 37739855, 4833037, 25954877, 25117026⟩, ⟨67108845, 33554431, 67108863, 33554431, 67108863, 33554431, 67108863, 33554431, 67108863, 33554431⟩⟩

private theorem O1_eq : Point.ladder B B (B.add B) Point.zero (L >>> 192) (0 >>> 192) 61 = O1 := by
  decide +kernel
private theorem O2_eq : Point.ladder B B (B.add B) O1 (L >>> 128) (0 >>> 128) 64 = O2 := by
  decide +kernel
private theorem O3_eq : Point.ladder B B (B.add B) O2 (L >>> 64) (0 >>> 64) 64 = O3 := by
  decide +kernel
private theorem O4_eq : Point.ladder B B (B.add B) O3 L 0 64 = O4 := by
  decide +kernel
private theorem O4_zero : O4.eq Point.zero = true := by decide +kernel

/-- **`[L] B = 0`**: the base point's order divides `L`, which is prime (RFC 8032 §5.1). -/
theorem B_order : Point.Same (Nat.repeat (·.add B) L Point.zero) Point.zero := by
  have hBB := point_add_proper B_proper B_proper
  have m := mul2_spec B_proper B_proper (same_refl hBB) (a := L) (b := 0) (n := 253) L_lt (by decide)
  rw [mul2_of_chunks (n := 61) rfl O1_eq O2_eq O3_eq O4_eq,
    show Nat.repeat (·.add B) 0 Point.zero = Point.zero from rfl] at m
  have z : Point.Same O4 Point.zero := ⟨m.left, point_zero_proper, O4_zero⟩
  exact same_trans (same_symm (same_add_zero (rep_proper B_proper L))) (same_trans (same_symm m) z)

private theorem B8_ne : B.double.double.double.eq Point.zero = false := by decide +kernel

/-- Tooth: `[8] B` is not the identity. `B` is not a small-order point, so `B_order` is not the cofactor
speaking. -/
theorem B_not_small : ¬ Point.Same (Nat.repeat (·.add B) 8 Point.zero) Point.zero := fun h => by
  have e := (same_trans (same_d3 B_proper) h).eq
  rw [B8_ne] at e
  exact Bool.false_ne_true e

end Nanodregg.Codec.Ed25519
