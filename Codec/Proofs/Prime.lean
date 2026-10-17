import Codec.Prime

/-!
# Pratt certificates: a number whose `n − 1` is fully factored and that has an element of order `n − 1`
is prime (CODEC-23)

* `IsPrime n`: `2 ≤ n` and its only divisors are `1` and `n`.
* `powMod_spec`: square-and-multiply computes `b ^ e % m`.
* `pratt`: if `qs` are primes whose product is `n − 1`, `a ^ (n − 1) ≡ 1` and `a ^ ((n − 1)/q) ≢ 1` for
  every `q ∈ qs`, then `n` is prime — and (`pratt_powers`) every nonzero residue is a power of `a`, so
  (`pratt_fermat`) `x ^ (n − 1) ≡ 1` for every `x` not divisible by `n` (Fermat).
* `p_prime`, `p_fermat`: the Ed25519 field prime `2^255 − 19`, by a 52-node certificate tree, each node
  checked by `decide +kernel` through `powMod`.
The proof: `a` has order exactly `n − 1` (a smaller order divides `n − 1/q` for a prime `q`), so its
`n − 1` powers are distinct nonzero residues, hence ALL of them (`card_lt`), so every proper divisor `m`
of `n` is a unit mod `n`, and a unit dividing `n` is `1`.
-/

namespace Nanodregg.Codec.Prime

/-- `n` is prime. -/
def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

/-! ## Square-and-multiply -/

theorem powMod_spec (b m : Nat) : ∀ (n e : Nat), e < 2 ^ n → powMod b e m n = b ^ e % m
  | 0, e, h => by
    rw [Nat.pow_zero] at h
    have : e = 0 := by omega
    subst this; simp [powMod]
  | n + 1, e, h => by
    have hsh : e >>> 1 = e / 2 := by simp [Nat.shiftRight_eq_div_pow]
    have hs : e / 2 < 2 ^ n := by rw [Nat.pow_succ] at h; omega
    have ih := powMod_spec b m n (e / 2) hs
    have key : b ^ e = b ^ (e / 2) * b ^ (e / 2) * b ^ (e % 2) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    simp only [powMod, hsh, ih]
    split
    · rename_i h1
      rw [key, h1, Nat.pow_one, ← Nat.mul_mod, Nat.mod_mul_mod]
    · rename_i h1
      have h0 : e % 2 = 0 := by omega
      rw [key, h0, Nat.pow_zero, Nat.mul_one, ← Nat.mul_mod]

/-! ## Counting -/

theorem card_le : ∀ (M : Nat) {l : List Nat}, l.Nodup → (∀ x ∈ l, x < M) → l.length ≤ M
  | 0, l, _, h => by
    cases l with
    | nil => simp
    | cons x _ => exact absurd (h x (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | M + 1, l, hn, h => by
    by_cases hm : M ∈ l
    · have hl := List.length_erase_of_mem hm
      have := card_le M (hn.erase M) (fun x hx => by
        have ⟨hne, hxl⟩ := (hn.mem_erase_iff).mp hx
        have := h x hxl; omega)
      have : 0 < l.length := List.length_pos_of_mem hm
      omega
    · have := card_le M hn (fun x hx => by
        have := h x hx
        have : x ≠ M := fun e => hm (e ▸ hx)
        omega)
      omega

theorem card_lt : ∀ (M : Nat) {l : List Nat} {r : Nat}, l.Nodup → (∀ x ∈ l, x < M) → r < M → r ∉ l →
    l.length < M
  | 0, _, _, _, _, hr, _ => absurd hr (Nat.not_lt_zero _)
  | M + 1, l, r, hn, h, hr, hrl => by
    by_cases hm : M ∈ l
    · have hl := List.length_erase_of_mem hm
      have hrM : r ≠ M := fun e => hrl (e ▸ hm)
      have := card_lt M (hn.erase M) (r := r) (fun x hx => by
        have ⟨hne, hxl⟩ := (hn.mem_erase_iff).mp hx
        have := h x hxl; omega) (by omega) (fun hx => hrl ((hn.mem_erase_iff).mp hx).2)
      have : 0 < l.length := List.length_pos_of_mem hm
      omega
    · have := card_le M hn (fun x hx => by
        have := h x hx
        have : x ≠ M := fun e => hm (e ▸ hx)
        omega)
      omega

/-! ## Divisibility -/

theorem IsPrime.dvd_mul {q a b : Nat} (hq : IsPrime q) (h : q ∣ a * b) : q ∣ a ∨ q ∣ b := by
  rcases hq.2 _ (Nat.gcd_dvd_left q a) with h1 | h1
  · exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left h1 h)
  · exact Or.inl (h1 ▸ Nat.gcd_dvd_right q a)

theorem mem_of_dvd_prod {r : Nat} (hr : IsPrime r) :
    ∀ {qs : List Nat}, (∀ q ∈ qs, IsPrime q) → r ∣ qs.foldr (· * ·) 1 → r ∈ qs
  | [], _, h => by
    simp only [List.foldr_nil] at h
    have := Nat.eq_one_of_dvd_one h
    have := hr.1; omega
  | q :: qs, hqs, h => by
    simp only [List.foldr_cons] at h
    rcases hr.dvd_mul h with h1 | h1
    · rcases (hqs q (List.mem_cons_self ..)).2 r h1 with e | e
      · have := hr.1; omega
      · exact e ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_dvd_prod hr (fun x hx => hqs x (List.mem_cons_of_mem _ hx)) h1)

theorem exists_prime_dvd : ∀ (m : Nat), 2 ≤ m → ∃ r, IsPrime r ∧ r ∣ m
  | m, hm => by
    by_cases hp : IsPrime m
    · exact ⟨m, hp, Nat.dvd_refl m⟩
    · have : ∃ d, d ∣ m ∧ d ≠ 1 ∧ d ≠ m := by
        apply Classical.byContradiction
        intro hne
        exact hp ⟨hm, fun d hd => by
          apply Classical.byContradiction
          intro h'
          exact hne ⟨d, hd, fun e => h' (Or.inl e), fun e => h' (Or.inr e)⟩⟩
      obtain ⟨d, hd, h1, h2⟩ := this
      have hd0 : d ≠ 0 := by rintro rfl; simp at hd; omega
      have hle := Nat.le_of_dvd (by omega) hd
      obtain ⟨r, hr, hrd⟩ := exists_prime_dvd d (by omega)
      exact ⟨r, hr, Nat.dvd_trans hrd hd⟩
termination_by m => m
decreasing_by omega

theorem exists_least {P : Nat → Prop} : ∀ N, P N → ∃ k, P k ∧ ∀ j < k, ¬P j
  | N, h => by
    by_cases hj : ∃ j < N, P j
    · obtain ⟨j, hjN, hP⟩ := hj
      exact exists_least j hP
    · exact ⟨N, h, fun j hjN hP => hj ⟨j, hjN, hP⟩⟩
termination_by N => N

/-! ## Powers mod n -/

theorem pow_mod_cycle {a n k : Nat} (hn : 1 < n) (hk : a ^ k % n = 1) (t r : Nat) :
    a ^ (k * t + r) % n = a ^ r % n := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, hk, Nat.one_pow, Nat.mod_eq_of_lt hn, Nat.one_mul,
    Nat.mod_mod]

theorem pow_cancel {a n N i j : Nat} (hN : a ^ N % n = 1) (hij : i ≤ j) (hjN : i ≤ N)
    (h : a ^ i % n = a ^ j % n) : a ^ (j - i) % n = 1 := by
  have e1 : a ^ (j - i) * a ^ N = a ^ j * a ^ (N - i) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have e2 : a ^ i * a ^ (N - i) = a ^ N := by rw [← Nat.pow_add]; congr 1; omega
  have : a ^ (j - i) % n = a ^ (j - i) * a ^ N % n := by
    rw [Nat.mul_mod, hN, Nat.mul_one, Nat.mod_mod]
  rw [this, e1, Nat.mul_mod, ← h, ← Nat.mul_mod, e2, hN]

/-! ## Pratt -/

section Pratt
variable {n a : Nat} {qs : List Nat}

/-- Under a Pratt certificate, the order of `a` mod `n` is exactly `n − 1`: no smaller positive power is 1. -/
theorem pratt_order (hn : 2 ≤ n) (hqs : ∀ q ∈ qs, IsPrime q) (hprod : qs.foldr (· * ·) 1 = n - 1)
    (ha : a ^ (n - 1) % n = 1) (hq : ∀ q ∈ qs, a ^ ((n - 1) / q) % n ≠ 1) :
    ∀ j, 0 < j → j < n - 1 → a ^ j % n ≠ 1 := by
  obtain ⟨k, ⟨hk0, hk⟩, hmin⟩ := exists_least (P := fun j => 0 < j ∧ a ^ j % n = 1) (n - 1) ⟨by omega, ha⟩
  have hdvd : ∀ j, a ^ j % n = 1 → k ∣ j := by
    intro j hj
    have := pow_mod_cycle (by omega) hk (j / k) (j % k)
    rw [Nat.div_add_mod] at this
    rw [hj] at this
    apply Nat.dvd_of_mod_eq_zero
    apply Classical.byContradiction
    intro h0
    exact hmin (j % k) (Nat.mod_lt _ hk0) ⟨by omega, this.symm⟩
  have hkN : k = n - 1 := by
    obtain ⟨m, hm⟩ := hdvd (n - 1) ha
    apply Classical.byContradiction
    intro hne
    have hm2 : 2 ≤ m := by
      rcases m with _ | _ | m
      · omega
      · omega
      · omega
    obtain ⟨r, hr, hrm⟩ := exists_prime_dvd m hm2
    have hrq : r ∈ qs := mem_of_dvd_prod hr hqs (hprod ▸ hm ▸ Nat.dvd_trans hrm (Nat.dvd_mul_left m k))
    obtain ⟨s, hs⟩ := hrm
    have hdiv : (n - 1) / r = k * s := by
      rw [hm, hs, ← Nat.mul_assoc, Nat.mul_comm k r, Nat.mul_assoc,
        Nat.mul_div_cancel_left _ (by have := hr.1; omega)]
    apply hq r hrq
    rw [hdiv]
    have := pow_mod_cycle (by omega) hk s 0
    simpa [Nat.pow_zero, Nat.mod_eq_of_lt (show 1 < n by omega)] using this
  intro j hj0 hjN h
  exact hmin j (hkN ▸ hjN) ⟨hj0, h⟩

/-- Under a Pratt certificate, every nonzero residue is a power of `a`. -/
theorem pratt_powers (hn : 2 ≤ n) (hqs : ∀ q ∈ qs, IsPrime q) (hprod : qs.foldr (· * ·) 1 = n - 1)
    (ha : a ^ (n - 1) % n = 1) (hq : ∀ q ∈ qs, a ^ ((n - 1) / q) % n ≠ 1) :
    ∀ m, 0 < m → m < n → ∃ i, i < n - 1 ∧ a ^ i % n = m := by
  have hord := pratt_order hn hqs hprod ha hq
  intro m hm0 hmn
  apply Classical.byContradiction
  intro hno
  let L := (List.range (n - 1)).map (fun i => a ^ i % n)
  have hnd : L.Nodup := by
    apply List.pairwise_map.mpr
    refine List.pairwise_lt_range.imp_of_mem ?_
    intro i j _ hj hij heq
    have hj := List.mem_range.mp hj
    exact hord (j - i) (by omega) (by omega) (pow_cancel ha (by omega) (by omega) heq)
  have h0 : 0 ∉ L := by
    intro h
    obtain ⟨i, hi, he⟩ := List.mem_map.mp h
    have hi := List.mem_range.mp hi
    have e : a ^ (n - 1) = a ^ i * a ^ (n - 1 - i) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e, Nat.mul_mod, he] at ha
    simp at ha
  have hmL : m ∉ L := fun h => by
    obtain ⟨i, hi, he⟩ := List.mem_map.mp h
    exact hno ⟨i, List.mem_range.mp hi, he⟩
  have hlt := card_lt n (l := 0 :: L) (r := m) (List.nodup_cons.mpr ⟨h0, hnd⟩)
    (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        exact Nat.mod_lt _ (by omega))
    hmn (fun hx => by
      rcases List.mem_cons.mp hx with e | hx
      · omega
      · exact hmL hx)
  simp only [List.length_cons, L, List.length_map, List.length_range] at hlt
  omega

/-- A Pratt certificate proves `n` prime. -/
theorem pratt (hn : 2 ≤ n) (hqs : ∀ q ∈ qs, IsPrime q) (hprod : qs.foldr (· * ·) 1 = n - 1)
    (ha : a ^ (n - 1) % n = 1) (hq : ∀ q ∈ qs, a ^ ((n - 1) / q) % n ≠ 1) : IsPrime n := by
  have hpow := pratt_powers hn hqs hprod ha hq
  refine ⟨hn, fun m hm => ?_⟩
  by_cases h1 : m = 1
  · exact Or.inl h1
  by_cases h2 : m = n
  · exact Or.inr h2
  have hm0 : 0 < m := Nat.pos_of_ne_zero (fun e => by subst e; rw [Nat.zero_dvd] at hm; omega)
  have hmn : m < n := Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hm) h2
  obtain ⟨i, hi, he⟩ := hpow m hm0 hmn
  have e : a ^ (n - 1) = a ^ i * a ^ (n - 1 - i) := by rw [← Nat.pow_add]; congr 1; omega
  have hx : m * a ^ (n - 1 - i) % n = 1 := by
    rw [← he, Nat.mod_mul_mod, ← e, ha]
  have h3 := Nat.mod_mod_of_dvd (m * a ^ (n - 1 - i)) hm
  rw [hx, Nat.mul_mod_right] at h3
  exact absurd (Nat.eq_one_of_dvd_one (Nat.dvd_of_mod_eq_zero h3)) h1

/-- Fermat, from the certificate: every `x` not divisible by `n` has `x ^ (n − 1) ≡ 1`. -/
theorem pratt_fermat (hn : 2 ≤ n) (hqs : ∀ q ∈ qs, IsPrime q) (hprod : qs.foldr (· * ·) 1 = n - 1)
    (ha : a ^ (n - 1) % n = 1) (hq : ∀ q ∈ qs, a ^ ((n - 1) / q) % n ≠ 1) :
    ∀ x, x % n ≠ 0 → x ^ (n - 1) % n = 1 := by
  intro x hx
  obtain ⟨i, _, he⟩ := pratt_powers hn hqs hprod ha hq (x % n) (Nat.pos_of_ne_zero hx) (Nat.mod_lt _ (by omega))
  rw [Nat.pow_mod, ← he, ← Nat.pow_mod, ← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul, Nat.pow_mod, ha, Nat.one_pow,
    Nat.mod_eq_of_lt (by omega)]

end Pratt

/-- The certificate as one kernel-checked Boolean: `n < 2^256`, the product, and the powers by `powMod`. -/
theorem pratt_check {n a : Nat} (qs : List Nat) (hqs : ∀ q ∈ qs, IsPrime q)
    (h : (decide (2 ≤ n) && decide (n < 2 ^ 256) && qs.foldr (· * ·) 1 == n - 1 &&
      powMod a (n - 1) n 256 == 1 && qs.all (fun q => powMod a ((n - 1) / q) n 256 != 1)) = true) :
    IsPrime n := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h2, hlt⟩, hprod⟩, ha⟩, hq⟩ := h
  have hs : ∀ e, e ≤ n - 1 → powMod a e n 256 = a ^ e % n := fun e he => powMod_spec a n 256 e (by omega)
  refine pratt (a := a) h2 hqs hprod ?_ ?_
  · rw [← hs _ (Nat.le_refl _)]; exact ha
  · intro q hq'
    rw [← hs _ (Nat.div_le_self _ _)]
    exact hq q hq'

/-- The same certificate gives Fermat: every `x` not divisible by `n` has `x ^ (n − 1) ≡ 1`. -/
theorem pratt_check_fermat {n a : Nat} (qs : List Nat) (hqs : ∀ q ∈ qs, IsPrime q)
    (h : (decide (2 ≤ n) && decide (n < 2 ^ 256) && qs.foldr (· * ·) 1 == n - 1 &&
      powMod a (n - 1) n 256 == 1 && qs.all (fun q => powMod a ((n - 1) / q) n 256 != 1)) = true) :
    ∀ x, x % n ≠ 0 → x ^ (n - 1) % n = 1 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h2, hlt⟩, hprod⟩, ha⟩, hq⟩ := h
  have hs : ∀ e, e ≤ n - 1 → powMod a e n 256 = a ^ e % n := fun e he => powMod_spec a n 256 e (by omega)
  refine pratt_fermat (a := a) h2 hqs hprod ?_ ?_
  · rw [← hs _ (Nat.le_refl _)]; exact ha
  · intro q hq'
    rw [← hs _ (Nat.div_le_self _ _)]
    exact hq q hq'

/-- The tooth: Fermat's condition alone is not a certificate. `341 = 11 · 31` passes `2^340 ≡ 1`, and is
refused by the order condition (`2^(340/2) ≡ 1` too), so `pratt`'s `hq` premise carries content. -/
theorem fermat_alone_is_not_prime :
    powMod 2 340 341 256 = 1 ∧ powMod 2 (340 / 2) 341 256 = 1 ∧ ¬IsPrime 341 := by
  refine ⟨by decide +kernel, by decide +kernel, fun h => ?_⟩
  rcases h.2 11 ⟨31, rfl⟩ with e | e <;> omega

theorem prime_two : IsPrime 2 := by
  refine ⟨Nat.le_refl 2, fun m hm => ?_⟩
  have := Nat.le_of_dvd (by decide) hm
  have : m ≠ 0 := by rintro rfl; rw [Nat.zero_dvd] at hm; omega
  omega

/-! ## The Ed25519 field prime: a Pratt tree, every node kernel-checked -/

theorem prime_3 : IsPrime 3 :=
  pratt_check (a := 2) [2]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_17 : IsPrime 17 :=
  pratt_check (a := 3) [2, 2, 2, 2]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_two, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_7 : IsPrime 7 :=
  pratt_check (a := 3) [2, 3]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_239 : IsPrime 239 :=
  pratt_check (a := 7) [2, 7, 17]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_7, prime_17, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_479 : IsPrime 479 :=
  pratt_check (a := 13) [2, 239]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_239, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_32573 : IsPrime 32573 :=
  pratt_check (a := 2) [2, 2, 17, 479]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_17, prime_479, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_65147 : IsPrime 65147 :=
  pratt_check (a := 2) [2, 32573]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_32573, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_5 : IsPrime 5 :=
  pratt_check (a := 2) [2, 2]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_11 : IsPrime 11 :=
  pratt_check (a := 2) [2, 5]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_5, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_353 : IsPrime 353 :=
  pratt_check (a := 3) [2, 2, 2, 2, 2, 11]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_two, prime_two, prime_11, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_29 : IsPrime 29 :=
  pratt_check (a := 2) [2, 2, 7]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_7, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_59 : IsPrime 59 :=
  pratt_check (a := 2) [2, 29]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_29, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_487 : IsPrime 487 :=
  pratt_check (a := 3) [2, 3, 3, 3, 3, 3]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_3, prime_3, prime_3, prime_3, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_57467 : IsPrime 57467 :=
  pratt_check (a := 2) [2, 59, 487]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_59, prime_487, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_13 : IsPrime 13 :=
  pratt_check (a := 2) [2, 2, 3]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_3, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_131 : IsPrime 131 :=
  pratt_check (a := 2) [2, 5, 13]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_5, prime_13, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_132049 : IsPrime 132049 :=
  pratt_check (a := 26) [2, 2, 2, 2, 3, 3, 7, 131]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_two, prime_3, prime_3, prime_7, prime_131, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_43 : IsPrime 43 :=
  pratt_check (a := 3) [2, 3, 7]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_7, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_23 : IsPrime 23 :=
  pratt_check (a := 5) [2, 11]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_11, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_3727 : IsPrime 3727 :=
  pratt_check (a := 3) [2, 3, 3, 3, 3, 23]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_3, prime_3, prime_3, prime_23, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_1923133 : IsPrime 1923133 :=
  pratt_check (a := 2) [2, 2, 3, 43, 3727]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_3, prime_43, prime_3727, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_31 : IsPrime 31 :=
  pratt_check (a := 3) [2, 3, 5]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_5, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_53 : IsPrime 53 :=
  pratt_check (a := 2) [2, 2, 13]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_13, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_107 : IsPrime 107 :=
  pratt_check (a := 2) [2, 53]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_53, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_37 : IsPrime 37 :=
  pratt_check (a := 2) [2, 2, 3, 3]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_3, prime_3, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_223 : IsPrime 223 :=
  pratt_check (a := 3) [2, 3, 37]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_37, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_173 : IsPrime 173 :=
  pratt_check (a := 2) [2, 2, 43]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_43, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_4153 : IsPrime 4153 :=
  pratt_check (a := 5) [2, 2, 2, 3, 173]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_3, prime_173, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_41 : IsPrime 41 :=
  pratt_check (a := 6) [2, 2, 2, 5]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_5, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_1723 : IsPrime 1723 :=
  pratt_check (a := 3) [2, 3, 7, 41]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_7, prime_41, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_430751 : IsPrime 430751 :=
  pratt_check (a := 17) [2, 5, 5, 5, 1723]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_5, prime_5, prime_5, prime_1723, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_31757755568855353 : IsPrime 31757755568855353 :=
  pratt_check (a := 10) [2, 2, 2, 3, 31, 107, 223, 4153, 430751]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_3, prime_31, prime_107, prime_223, prime_4153, prime_430751, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_19 : IsPrime 19 :=
  pratt_check (a := 2) [2, 3, 3]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_3, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_83 : IsPrime 83 :=
  pratt_check (a := 2) [2, 41]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_41, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_9463 : IsPrime 9463 :=
  pratt_check (a := 3) [2, 3, 19, 83]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_19, prime_83, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_37853 : IsPrime 37853 :=
  pratt_check (a := 2) [2, 2, 9463]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_9463, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_75707 : IsPrime 75707 :=
  pratt_check (a := 2) [2, 37853]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_37853, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_2437 : IsPrime 2437 :=
  pratt_check (a := 2) [2, 2, 3, 7, 29]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_3, prime_7, prime_29, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_97 : IsPrime 97 :=
  pratt_check (a := 5) [2, 2, 2, 2, 2, 3]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_two, prime_two, prime_3, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_419 : IsPrime 419 :=
  pratt_check (a := 2) [2, 11, 19]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_11, prime_19, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_569003 : IsPrime 569003 :=
  pratt_check (a := 2) [2, 7, 97, 419]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_7, prime_97, prime_419, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_2773320623 : IsPrime 2773320623 :=
  pratt_check (a := 5) [2, 2437, 569003]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_2437, prime_569003, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_72106336199 : IsPrime 72106336199 :=
  pratt_check (a := 7) [2, 13, 2773320623]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_13, prime_2773320623, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_47 : IsPrime 47 :=
  pratt_check (a := 5) [2, 23]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_23, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_127 : IsPrime 127 :=
  pratt_check (a := 3) [2, 3, 3, 7]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_3, prime_7, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_103 : IsPrime 103 :=
  pratt_check (a := 5) [2, 3, 17]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_17, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_991 : IsPrime 991 :=
  pratt_check (a := 6) [2, 3, 3, 5, 11]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_3, prime_5, prime_11, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_8574133 : IsPrime 8574133 :=
  pratt_check (a := 2) [2, 2, 3, 7, 103, 991]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_3, prime_7, prime_103, prime_991, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_1919519569386763 : IsPrime 1919519569386763 :=
  pratt_check (a := 2) [2, 3, 7, 19, 47, 47, 127, 8574133]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_7, prime_19, prime_47, prime_47, prime_127, prime_8574133, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_75445702479781427272750846543864801 : IsPrime 75445702479781427272750846543864801 :=
  pratt_check (a := 7) [2, 2, 2, 2, 2, 3, 3, 5, 5, 75707, 72106336199, 1919519569386763]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_two, prime_two, prime_two, prime_3, prime_3, prime_5, prime_5, prime_75707, prime_72106336199, prime_1919519569386763, fun _ h => nomatch h⟩) (by decide +kernel)

theorem prime_74058212732561358302231226437062788676166966415465897661863160754340907 : IsPrime 74058212732561358302231226437062788676166966415465897661863160754340907 :=
  pratt_check (a := 2) [2, 3, 353, 57467, 132049, 1923133, 31757755568855353, 75445702479781427272750846543864801]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_3, prime_353, prime_57467, prime_132049, prime_1923133, prime_31757755568855353, prime_75445702479781427272750846543864801, fun _ h => nomatch h⟩) (by decide +kernel)

theorem p_prime : IsPrime 57896044618658097711785492504343953926634992332820282019728792003956564819949 :=
  pratt_check (a := 2) [2, 2, 3, 65147, 74058212732561358302231226437062788676166966415465897661863160754340907]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_3, prime_65147, prime_74058212732561358302231226437062788676166966415465897661863160754340907, fun _ h => nomatch h⟩) (by decide +kernel)

theorem p_fermat : ∀ x, x % 57896044618658097711785492504343953926634992332820282019728792003956564819949 ≠ 0 →
    x ^ (57896044618658097711785492504343953926634992332820282019728792003956564819949 - 1) %
      57896044618658097711785492504343953926634992332820282019728792003956564819949 = 1 :=
  pratt_check_fermat (a := 2) [2, 2, 3, 65147, 74058212732561358302231226437062788676166966415465897661863160754340907]
    (by simp only [List.forall_mem_cons]; exact ⟨prime_two, prime_two, prime_3, prime_65147, prime_74058212732561358302231226437062788676166966415465897661863160754340907, fun _ h => nomatch h⟩) (by decide +kernel)

end Nanodregg.Codec.Prime
