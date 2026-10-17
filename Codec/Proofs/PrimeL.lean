import Codec.Proofs.Prime
import Codec.Ed25519

/-!
# The group order L is prime (CODEC-23)

`Ed25519.L = 2^252 + 27742317777372353535851937790883648493`, the order of `B` (`Codec.Proofs.Ed25519.Order.
B_order`), is prime, by a Pratt certificate in core Lean (`Prime.pratt_check`, as `p_prime`). The factors of
`L − 1` (2², 3, 11, a 108-bit prime and a 138-bit prime) and each node's witness were computed offline
with sympy (scratch `cas4/genL.py`). They are checked here node by node by `decide +kernel`, not trusted.
Nodes `Codec.Proofs.Prime` already proves (for `p`) are reused by name. The certificate's tooth is
`fermat_alone_is_not_prime` there.
-/

namespace Nanodregg.Codec.Prime

theorem primeL_34123 : IsPrime 34123 :=
  pratt_check (a := 2) [2, 3, 11, 11, 47]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_11, prime_11, prime_47, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_409477 : IsPrime 409477 :=
  pratt_check (a := 2) [2, 2, 3, 34123]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_3, primeL_34123, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_14741173 : IsPrime 14741173 :=
  pratt_check (a := 2) [2, 2, 3, 3, 409477]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_3, prime_3, primeL_409477, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_58964693 : IsPrime 58964693 :=
  pratt_check (a := 2) [2, 2, 14741173]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, primeL_14741173, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_30703 : IsPrime 30703 :=
  pratt_check (a := 3) [2, 3, 7, 17, 43]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_7, prime_17, prime_43, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_79 : IsPrime 79 :=
  pratt_check (a := 3) [2, 3, 13]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_13, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_41081 : IsPrime 41081 :=
  pratt_check (a := 3) [2, 2, 2, 5, 13, 79]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_5, prime_13, primeL_79, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_82163 : IsPrime 82163 :=
  pratt_check (a := 2) [2, 41081]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, primeL_41081, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_67 : IsPrime 67 :=
  pratt_check (a := 2) [2, 3, 11]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_11, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_22111 : IsPrime 22111 :=
  pratt_check (a := 6) [2, 3, 5, 11, 67]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_5, prime_11, primeL_67, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_132667 : IsPrime 132667 :=
  pratt_check (a := 5) [2, 3, 22111]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, primeL_22111, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_17231 : IsPrime 17231 :=
  pratt_check (a := 13) [2, 5, 1723]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_5, prime_1723, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_137849 : IsPrime 137849 :=
  pratt_check (a := 3) [2, 2, 2, 17231]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, primeL_17231, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_3044861653679985063343 : IsPrime 3044861653679985063343 :=
  pratt_check (a := 5) [2, 3, 11, 30703, 82163, 132667, 137849]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_11, primeL_30703, primeL_82163, primeL_132667, primeL_137849, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_198211423230930754013084525763697 : IsPrime 198211423230930754013084525763697 :=
  pratt_check (a := 5) [2, 2, 2, 2, 3, 23, 58964693, 3044861653679985063343]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_two, prime_3, prime_23, primeL_58964693, primeL_3044861653679985063343, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_269 : IsPrime 269 :=
  pratt_check (a := 2) [2, 2, 67]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, primeL_67, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_73 : IsPrime 73 :=
  pratt_check (a := 5) [2, 2, 2, 3, 3]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_3, prime_3, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_307 : IsPrime 307 :=
  pratt_check (a := 5) [2, 3, 3, 17]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_3, prime_17, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_113 : IsPrime 113 :=
  pratt_check (a := 3) [2, 2, 2, 2, 7]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_two, prime_7, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_2939 : IsPrime 2939 :=
  pratt_check (a := 2) [2, 13, 113]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_13, primeL_113, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_5879 : IsPrime 5879 :=
  pratt_check (a := 11) [2, 2939]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, primeL_2939, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_292386187 : IsPrime 292386187 :=
  pratt_check (a := 2) [2, 3, 3, 3, 3, 307, 5879]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_3, prime_3, prime_3, primeL_307, primeL_5879, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_213441916511 : IsPrime 213441916511 :=
  pratt_check (a := 13) [2, 5, 73, 292386187]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_5, primeL_73, primeL_292386187, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_1361 : IsPrime 1361 :=
  pratt_check (a := 3) [2, 2, 2, 2, 5, 17]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_two, prime_5, prime_17, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_2851 : IsPrime 2851 :=
  pratt_check (a := 2) [2, 3, 5, 5, 19]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_5, prime_5, prime_19, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_3797 : IsPrime 3797 :=
  pratt_check (a := 2) [2, 2, 13, 73]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_13, primeL_73, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_531581 : IsPrime 531581 :=
  pratt_check (a := 2) [2, 2, 5, 7, 3797]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_5, prime_7, primeL_3797, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_2551 : IsPrime 2551 :=
  pratt_check (a := 6) [2, 3, 5, 5, 17]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_5, prime_5, prime_17, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_1224481 : IsPrime 1224481 :=
  pratt_check (a := 13) [2, 2, 2, 2, 2, 3, 5, 2551]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_two, prime_two, prime_3, prime_5, primeL_2551, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_1257559732178653 : IsPrime 1257559732178653 :=
  pratt_check (a := 2) [2, 2, 3, 7, 23, 531581, 1224481]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_3, prime_7, prime_23, primeL_531581, primeL_1224481, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_4434155615661930479 : IsPrime 4434155615661930479 :=
  pratt_check (a := 17) [2, 41, 43, 1257559732178653]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_41, prime_43, primeL_1257559732178653, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_172054593956031949258510691 : IsPrime 172054593956031949258510691 :=
  pratt_check (a := 2) [2, 5, 1361, 2851, 4434155615661930479]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_5, primeL_1361, primeL_2851, primeL_4434155615661930479, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_19757330305831588566944191468367130476339 : IsPrime 19757330305831588566944191468367130476339 :=
  pratt_check (a := 2) [2, 269, 213441916511, 172054593956031949258510691]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, primeL_269, primeL_213441916511, primeL_172054593956031949258510691, fun _ h => nomatch h⟩) (by decide +kernel)

theorem primeL_276602624281642239937218680557139826668747 : IsPrime 276602624281642239937218680557139826668747 :=
  pratt_check (a := 2) [2, 7, 19757330305831588566944191468367130476339]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_7, primeL_19757330305831588566944191468367130476339, fun _ h => nomatch h⟩) (by decide +kernel)

theorem L_prime : IsPrime Ed25519.L :=
  pratt_check (a := 2) [2, 2, 3, 11, 198211423230930754013084525763697, 276602624281642239937218680557139826668747]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_3, prime_11, primeL_198211423230930754013084525763697, primeL_276602624281642239937218680557139826668747, fun _ h => nomatch h⟩) (by decide +kernel)

end Nanodregg.Codec.Prime
