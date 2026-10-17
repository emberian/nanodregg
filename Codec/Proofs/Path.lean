import Codec.Path

/-!
# The path spelling is canonical: `split` inverts `join` over clean components

* `split_join`: clean components survive the round trip; `join_split`: every byte string is the join of
  its split. Together: on clean paths, `join` is injective and the wire has one spelling per path.
* `split_join_needs_clean`: the tooth — a component holding a `/` does not come back.
Proved over the bytes' lists (`b.data.toList`), the one place lists appear.
-/

namespace Nanodregg.Codec.Path

private theorem toList_inj {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.toList_inj.mp h)

private theorem toList_append (a b : ByteArray) : (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

private theorem toList_extract (b : ByteArray) (s e : Nat) :
    (b.extract s e).data.toList = (b.data.toList.drop s).take (e - s) := by
  simp [ByteArray.data_extract, Array.toList_extract]

private theorem size_toList (b : ByteArray) : b.data.toList.length = b.size := by
  simp [ByteArray.size_data]

private theorem map_inj : ∀ {l₁ l₂ : List ByteArray},
    l₁.map (·.data.toList) = l₂.map (·.data.toList) → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [toList_inj h.1, map_inj h.2]

/-- The list-level split: `acc` is the component being read. -/
private def lsplit (acc : List UInt8) : List UInt8 → List (List UInt8)
  | [] => [acc]
  | x :: xs => if x = 47 then acc :: lsplit [] xs else lsplit (acc ++ [x]) xs

private def ljoin : List (List UInt8) → List UInt8
  | [] => []
  | [c] => c
  | c :: cs => c ++ [47] ++ ljoin cs

private theorem lsplit_ne_nil : ∀ (acc l : List UInt8), lsplit acc l ≠ []
  | _, [] => by simp [lsplit]
  | acc, x :: xs => by
      simp only [lsplit]; split
      · simp
      · exact lsplit_ne_nil _ xs

private theorem ljoin_cons_ne {c : List UInt8} {cs : List (List UInt8)} (h : cs ≠ []) :
    ljoin (c :: cs) = c ++ [47] ++ ljoin cs := by
  cases cs with
  | nil => exact absurd rfl h
  | cons d ds => rfl

private theorem ljoin_lsplit : ∀ (acc l : List UInt8), ljoin (lsplit acc l) = acc ++ l
  | acc, [] => by simp [lsplit, ljoin]
  | acc, x :: xs => by
      simp only [lsplit]; split
      · rename_i hx; subst hx
        rw [ljoin_cons_ne (lsplit_ne_nil _ _), ljoin_lsplit [] xs]; simp
      · rw [ljoin_lsplit (acc ++ [x]) xs]; simp

private theorem lsplit_append_free : ∀ (c : List UInt8), (∀ x ∈ c, x ≠ 47) →
    ∀ (acc r : List UInt8), lsplit acc (c ++ r) = lsplit (acc ++ c) r
  | [], _, acc, r => by simp
  | x :: xs, h, acc, r => by
      have hx : x ≠ 47 := h x (by simp)
      simp only [List.cons_append, lsplit, if_neg hx]
      rw [lsplit_append_free xs (fun y hy => h y (by simp [hy])) (acc ++ [x]) r]; simp

private theorem lsplit_ljoin : ∀ (cs : List (List UInt8)), cs ≠ [] → (∀ c ∈ cs, ∀ x ∈ c, x ≠ 47) →
    lsplit [] (ljoin cs) = cs
  | [], h, _ => absurd rfl h
  | [c], _, hf => by
      have := lsplit_append_free c (hf c (by simp)) [] []
      simp only [List.append_nil, List.nil_append] at this
      simp [ljoin, this, lsplit]
  | c :: d :: ds, _, hf => by
      rw [ljoin_cons_ne (by simp), List.append_assoc,
        lsplit_append_free c (hf c (by simp)) [] _]
      simp only [List.nil_append, List.cons_append, lsplit, ↓reduceIte]
      rw [lsplit_ljoin (d :: ds) (by simp) (fun c' hc' => hf c' (by simp [hc']))]

private theorem toList_join : ∀ (p : List ByteArray), (join p).data.toList = ljoin (p.map (·.data.toList))
  | [] => rfl
  | [c] => rfl
  | c :: d :: ds => by
      simp only [join, List.map_cons]
      rw [ljoin_cons_ne (by simp), toList_append, toList_append, toList_join (d :: ds)]
      rfl

private theorem splitFrom_spec (b : ByteArray) : ∀ (n start i : Nat), i + n = b.size → start ≤ i →
    (splitFrom b start i n).map (·.data.toList) =
      lsplit ((b.data.toList.drop start).take (i - start)) (b.data.toList.drop i)
  | 0, start, i, hn, _ => by
      have : b.data.toList.drop i = [] := List.drop_eq_nil_of_le (by rw [size_toList]; omega)
      simp [splitFrom, this, lsplit]
  | n + 1, start, i, hn, hs => by
      have hi : i < b.size := by omega
      have hl : i < b.data.toList.length := by rw [size_toList]; exact hi
      have hget : b[i] = b.data.toList[i] := by simp [ByteArray.getElem_eq_getElem_data]
      rw [List.drop_eq_getElem_cons hl]
      simp only [splitFrom, dif_pos hi, lsplit, sep]
      by_cases h47 : b.data.toList[i] = 47
      · rw [if_pos (by simp only [beq_iff_eq]; exact hget.trans h47), if_pos h47, List.map_cons,
          splitFrom_spec b n (i + 1) (i + 1) (by omega) (Nat.le_refl _)]
        simp
      · rw [if_neg (by simp only [beq_iff_eq]; exact fun he => h47 (hget.symm.trans he)), if_neg h47, splitFrom_spec b n start (i + 1) (by omega) (by omega)]
        congr 1
        rw [show i + 1 - start = (i - start) + 1 by omega, List.take_add_one]
        simp only [List.getElem?_drop, show start + (i - start) = i by omega, List.getElem?_eq_getElem hl,
          Option.toList_some]

private theorem split_spec (b : ByteArray) :
    (split b).map (·.data.toList) = if b.size = 0 then [] else lsplit [] b.data.toList := by
  unfold split
  split
  · rfl
  · rw [splitFrom_spec b b.size 0 0 (by omega) (Nat.le_refl _)]; simp

/-- Every byte string is the join of its split. -/
theorem join_split (b : ByteArray) : join (split b) = b := by
  apply toList_inj
  rw [toList_join, split_spec]
  split
  · rename_i h
    have : b.data.toList = [] := List.eq_nil_of_length_eq_zero (by rw [size_toList]; exact h)
    rw [this]; rfl
  · rw [ljoin_lsplit]; rfl

private theorem freeFrom_spec (c : ByteArray) : ∀ (n i : Nat), freeFrom c i n = true →
    ∀ j, i ≤ j → j < i + n → (h : j < c.size) → c[j] ≠ 47 ∧ c[j] ≠ 0
  | 0, _, _, j, h1, h2, _ => by omega
  | n + 1, i, hf, j, h1, h2, hj => by
      simp only [freeFrom, Bool.and_eq_true] at hf
      by_cases hji : j = i
      · subst hji
        have := hf.1; rw [dif_pos hj] at this
        simp [forbidden, sep, nul] at this
        exact this
      · exact freeFrom_spec c n (i + 1) hf.2 j (by omega) (by omega) hj

/-- A clean component is nonempty and holds neither `/` nor NUL. -/
theorem clean_free {c : ByteArray} (h : clean c = true) :
    c.size ≠ 0 ∧ ∀ x ∈ c.data.toList, x ≠ 47 ∧ x ≠ 0 := by
  simp only [clean, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  refine ⟨h.1.1.1.1, fun x hx => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have hj' : j < c.size := by rw [← size_toList]; exact hj
  have := freeFrom_spec c c.size 0 h.2 j (by omega) (by omega) hj'
  simpa [ByteArray.getElem_eq_getElem_data] using this

/-- Clean components come back from their join. -/
theorem split_join {p : List ByteArray} (hp : ∀ c ∈ p, clean c = true) : split (join p) = p := by
  apply map_inj
  rw [split_spec]
  cases p with
  | nil => rfl
  | cons c cs =>
      have hc := clean_free (hp c (by simp))
      have hne : (join (c :: cs)).size ≠ 0 := by
        intro h0
        have : (join (c :: cs)).data.toList = [] := List.eq_nil_of_length_eq_zero (by rw [size_toList]; exact h0)
        rw [toList_join] at this
        have hcl : c.data.toList ≠ [] := fun he => hc.1 (by rw [← size_toList, he]; rfl)
        cases cs with
        | nil => exact hcl this
        | cons d ds =>
            rw [List.map_cons, ljoin_cons_ne (by simp)] at this; simp at this
      rw [if_neg hne, toList_join]
      exact lsplit_ljoin _ (by simp) (fun c' hc' x hx => by
        obtain ⟨c'', hc'', rfl⟩ := List.mem_map.mp hc'
        exact ((clean_free (hp c'' hc'')).2 x hx).1)

/-- The tooth: a component holding a `/` does not survive (so `split_join`'s premise is needed). -/
theorem split_join_needs_clean : split (join ["a/b".toUTF8]) ≠ ["a/b".toUTF8] := by decide

end Nanodregg.Codec.Path
