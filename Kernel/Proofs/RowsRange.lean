/-
# Kernel.Proofs.RowsRange — a range read lists exactly the rows under its prefix, in key order

ROOT's condition (a), KERNEL-46/48:

* `takeList_eq`: `takeList n` is `T.toList` cut at `n`.
* `under_eq`: on a routed trie of canonical shape routed by its keys' bytes, `under` is the listing
  filtered by `startsWith pre`, cut at `n`, given that a key whose bits agree with `pre`'s is at
  least `pre.size` long. The descent reads only the branching bits; the bits a path skips are
  checked once, against the `rep` of the first node branching past the prefix, which in a canonical
  shape is a key of that subtree and agrees with all of them below its branching bit.
  `under_needs_long`: the length premise is needed; `under_needs_rep`: the `rep` check is (without
  it a row that does not start with the prefix is listed); `under_needs_shape`: the canonical shape
  is (a routed tree whose `rep` is not one of its keys misses rows). `range_prefix_long` discharges
  the length premise for the range prefix from one digest size and `pre.size ≤ width` (no bound on
  the width: cv 01a14f7e);
  `under_rows` is the instance.
* `range_rows_exact` ((i) exactly the rows under the prefix, (ii) strictly ascending key bytes,
  (iii) at most `most`), with `range_rows_none` (refused iff more than `most`), and the admitted form
  `admit_range_exact`: the listing whose pin the signer gave is the World's rows under the prefix.
* Teeth: `rangePinBytes_erase_ne` (a dropped row moves the pin), `range_rows_erase_not_exact`
  ((i) refutes a dropped listing), `range_seal_tooth` (an arg-max seal changes when its row is
  dropped), `range_rows_satisfiable` (every premise holds, and the conclusions are not trivial, on a
  concrete trie).
-/
import Kernel.Proofs.Lawful
import Kernel.Proofs.Bytes
import Kernel.Proofs.TrieOrder
import Kernel.Proofs.Admit
import Kernel.Proofs.TrieMap

namespace Nanodregg.Kernel

attribute [local irreducible] rowPath

variable {D : Type}

/-! ## `takeList` -/

theorem takeList_eq {K V : Type} : ∀ (n : Nat) (t : Trie.T K V D), takeList n t = t.toList.take n
  | _, .empty => by simp [takeList, Trie.T.toList]
  | _, .leaf _ kvs => by simp [takeList, Trie.T.toList]
  | n, .node _ _ _ l r => by
      unfold takeList
      split
      · subst_vars; simp
      · simp only [Trie.T.toList, List.take_append, takeList_eq n l, takeList_eq _ r, List.length_take]
        congr 2
        omega

/-! ## Bits and bytes -/

private theorem startsWith_iff {pre b : ByteArray} :
    startsWith pre b = true ↔ pre.size ≤ b.size ∧ ∀ j (h1 : j < pre.size) (h2 : j < b.size), b[j] = pre[j] := by
  unfold startsWith
  rw [decide_eq_true_iff]
  constructor
  · intro h
    have hs : pre.size ≤ b.size := by
      have := congrArg ByteArray.size h
      simp at this; omega
    refine ⟨hs, fun j h1 h2 => ?_⟩
    have hd : b.data.extract 0 pre.size = pre.data := by simpa using congrArg ByteArray.data h
    have e := congrArg (fun x : Array UInt8 => x[j]?) hd
    simp only at e
    rw [Array.getElem?_extract_of_lt (by simp; omega)] at e
    have h1' : j < pre.data.size := by simpa using h1
    rw [Array.getElem?_eq_getElem h1', Option.some.injEq] at e
    simpa [ByteArray.getElem_eq_getElem_data] using e
  · rintro ⟨hs, h⟩
    apply ByteArray.ext
    apply Array.ext
    · simp; omega
    · intro j h1 h2
      simp only [ByteArray.data_extract, Array.getElem_extract, Nat.zero_add]
      have h2' : j < pre.size := by simpa using h2
      have := h j h2' (by omega)
      simpa [ByteArray.getElem_eq_getElem_data] using this

/-- A string that starts with `pre` agrees with it on `pre`'s bits. -/
private theorem bits_of_startsWith {pre b : ByteArray} (h : startsWith pre b = true) {i : Nat}
    (hi : i < 8 * pre.size) : byteBit b i = byteBit pre i := by
  obtain ⟨hs, he⟩ := startsWith_iff.mp h
  have h1 : i / 8 < pre.size := by omega
  rw [byteBit_of_lt (Nat.lt_of_lt_of_le h1 hs), byteBit_of_lt h1, he _ h1]

/-- A string at least as long as `pre` that agrees with it on `pre`'s bits starts with it. -/
private theorem startsWith_of_bits {pre b : ByteArray} (hs : pre.size ≤ b.size)
    (h : ∀ i, i < 8 * pre.size → byteBit b i = byteBit pre i) : startsWith pre b = true :=
  startsWith_iff.mpr ⟨hs, fun j h1 h2 => byte_eq_of_bits h2 h1 fun t ht => h _ (by omega)⟩

/-! ## `under` is the filtered listing -/

section Under
variable {K V : Type} (S : Trie.Spec K V D)

/-- **`under` lists the entries under the prefix, in trie order, cut at `n`**, on a routed trie of
canonical shape routed by its keys' bytes, from a depth `d` below which its keys all agree. The
descent follows the prefix's bit at each node's branching bit and checks no skipped bit; at the
first node branching past the prefix, its `rep` (a key of the subtree, by the shape) agrees with
every key below on every bit below the branching bit, so on the whole prefix, and one `startsWith`
on it decides the subtree. The one premise beyond routing and shape (`hlong`) is what a byte prefix
needs of the encoding: a key whose bits agree with `pre`'s is at least `pre.size` bytes long (a
shorter key reads its missing bits as 0; `under_needs_long`). -/
theorem under_eq (hbit : ∀ k i, S.bit k i = byteBit (S.kbytes k) i) (pre : ByteArray) (n : Nat) :
    ∀ (d : Nat) (t : Trie.T K V D), Trie.Routed S d t → Trie.Shape S d t →
      (∀ p ∈ t.toList, ∀ q ∈ t.toList, ∀ i, i < d → S.bit p.1 i = S.bit q.1 i) →
      (∀ p ∈ t.toList, (∀ i, i < 8 * pre.size → byteBit (S.kbytes p.1) i = byteBit pre i) →
        pre.size ≤ (S.kbytes p.1).size) →
      under S pre n t = (t.toList.filter fun p => startsWith pre (S.kbytes p.1)).take n
  | _, .empty, _, _, _, _ => by simp [under, Trie.T.toList]
  | _, .leaf _ kvs, _, _, _, _ => by simp [under, Trie.T.toList]
  | d, .node h b rep l r, hr, hs, hagree, hlong => by
      obtain ⟨-, hrep, hl, hrt, hrl, hrr⟩ := hr
      obtain ⟨-, -, hfirst, -, hsl, hsr⟩ := hs
      have inL : ∀ p ∈ l.toList, p ∈ l.toList ++ r.toList := fun p hp => List.mem_append_left _ hp
      have inR : ∀ p ∈ r.toList, p ∈ l.toList ++ r.toList := fun p hp => List.mem_append_right _ hp
      -- every two keys of the subtree agree below `b`: below `d` by `hagree`, on `[d, b)` through `rep`
      have hall : ∀ p ∈ l.toList ++ r.toList, ∀ q ∈ l.toList ++ r.toList, ∀ i, i < b →
          S.bit p.1 i = S.bit q.1 i := by
        intro p hp q hq i hi
        by_cases hid : i < d
        · exact hagree p hp q hq i hid
        · rw [hrep p hp i (by omega) hi, hrep q hq i (by omega) hi]
      unfold under
      split
      · rename_i hb
        have hside : ∀ (s : Trie.T K V D) (c : Bool), (∀ p ∈ s.toList, S.bit p.1 b = c) →
            c ≠ byteBit pre b → s.toList.filter (fun p => startsWith pre (S.kbytes p.1)) = [] := by
          intro s c hc hne
          refine List.filter_eq_nil_iff.mpr fun p hp hst => hne ?_
          rw [← hc p hp, hbit, bits_of_startsWith hst hb]
        have hsub : ∀ (s : Trie.T K V D), (∀ p ∈ s.toList, p ∈ l.toList ++ r.toList) →
            (∀ p ∈ s.toList, ∀ q ∈ s.toList, S.bit p.1 b = S.bit q.1 b) →
            ∀ p ∈ s.toList, ∀ q ∈ s.toList, ∀ i, i < b + 1 → S.bit p.1 i = S.bit q.1 i := by
          intro s hs' hsb p hp q hq i hi
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
          · exact hall p (hs' p hp) q (hs' q hq) i hlt
          · exact hsb p hp q hq
        cases hpb : byteBit pre b
        · simp only [Bool.false_eq_true, if_false]
          rw [under_eq hbit pre n (b + 1) l hrl hsl
            (hsub l inL fun p hp q hq => by rw [hl p hp, hl q hq])
            (fun p hp => hlong p (inL p hp))]
          simp only [Trie.T.toList, List.filter_append, hside r true hrt (by rw [hpb]; decide), List.append_nil]
        · simp only [if_true]
          rw [under_eq hbit pre n (b + 1) r hrr hsr
            (hsub r inR fun p hp q hq => by rw [hrt p hp, hrt q hq])
            (fun p hp => hlong p (inR p hp))]
          simp only [Trie.T.toList, List.filter_append, hside l false hl (by rw [hpb]; decide), List.nil_append]
      · rename_i hb
        -- the shape makes `rep` a key of the subtree (its first)
        obtain ⟨x, hx, hxr⟩ : ∃ x ∈ l.toList ++ r.toList, x.1 = rep := by
          cases hlt : l.toList with
          | nil => rw [hlt] at hfirst; cases hfirst
          | cons y ys => rw [hlt] at hfirst; exact ⟨y, by simp, by simpa using hfirst⟩
        have hagx : ∀ p ∈ l.toList ++ r.toList, ∀ i, i < 8 * pre.size →
            byteBit (S.kbytes p.1) i = byteBit (S.kbytes rep) i := by
          intro p hp i hi
          rw [← hbit, ← hbit, ← hxr]; exact hall p hp x hx i (by omega)
        split
        · rename_i hst
          rw [takeList_eq]
          congr 1
          symm
          refine List.filter_eq_self.mpr fun p hp => ?_
          have hbits : ∀ i, i < 8 * pre.size → byteBit (S.kbytes p.1) i = byteBit pre i :=
            fun i hi => (hagx p hp i hi).trans (bits_of_startsWith hst hi)
          exact startsWith_of_bits (hlong p hp hbits) hbits
        · rename_i hst
          have hnil : (l.toList ++ r.toList).filter (fun p => startsWith pre (S.kbytes p.1)) = [] := by
            refine List.filter_eq_nil_iff.mpr fun p hp hps => hst ?_
            have hbits : ∀ i, i < 8 * pre.size → byteBit (S.kbytes x.1) i = byteBit pre i := fun i hi => by
              rw [hxr, ← hagx p hp i hi]; exact bits_of_startsWith hps hi
            rw [← hxr]; exact startsWith_of_bits (hlong x hx hbits) hbits
          simp only [Trie.T.toList, hnil, List.take_nil]

end Under

/-- A trie of byte strings routed by their own bits (the teeth's witness). -/
private def bytesSpec : Trie.Spec ByteArray Unit UInt8 where
  bit k := byteBit k
  depth := 64
  depth_lt := by decide
  hash _ := 0
  dbytes d := ⟨#[d]⟩
  kbytes k := k
  vdigest _ := 0

private def shortLong : Trie.T ByteArray Unit UInt8 :=
  (Trie.T.empty.insert bytesSpec ⟨#[0]⟩ ()).insert bytesSpec ⟨#[0, 0, 1]⟩ ()

/-- **`under_eq`'s length premise is needed**: on a canonical trie holding `[0]` and `[0, 0, 1]`,
`under` at prefix `[0, 0]` lists nothing, although `[0, 0, 1]` starts with `[0, 0]`: the short key
reads its missing bits as zero, so it agrees with the prefix's bits, is the subtree's first key (its
`rep`), and fails the prefix check that decides the whole subtree. This is the case `checkRanges`'s
`pre.size ≤ width` refusal (`keyWidth`) excludes for rows. -/
theorem under_needs_long :
    Trie.Canon bytesSpec 0 shortLong ∧
    under bytesSpec ⟨#[0, 0]⟩ 5 shortLong ≠
      (shortLong.toList.filter fun p => startsWith ⟨#[0, 0]⟩ (bytesSpec.kbytes p.1)).take 5 :=
  ⟨Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _ (Trie.canon_empty _ 0)), by decide⟩

/-- `under` with its `rep` check removed: past the prefix, a subtree's first `n`, whatever its keys
(the descent alone, which reads only branching bits). -/
private def underNoRep {K V : Type} (S : Trie.Spec K V D) (pre : ByteArray) (n : Nat) :
    Trie.T K V D → List (K × V)
  | .empty => []
  | .leaf _ kvs => (kvs.filter fun p => startsWith pre (S.kbytes p.1)).take n
  | .node h b rep l r =>
      if b < 8 * pre.size then (if byteBit pre b then underNoRep S pre n r else underNoRep S pre n l)
      else takeList n (.node h b rep l r)

/-- `[0x80, 0]` and `[0x80, 1]`: one node branching at bit 15, past a one-byte prefix, its bits
`0..14` skipped. -/
private def skipped : Trie.T ByteArray Unit UInt8 :=
  (Trie.T.empty.insert bytesSpec ⟨#[0x80, 0]⟩ ()).insert bytesSpec ⟨#[0x80, 1]⟩ ()

/-- **`under`'s `rep` check is needed**: on a canonical trie whose one node branches past the prefix
`[0]` and whose keys both start `0x80`, `under` lists exactly the (no) entries under `[0]`, and the
same descent without the check lists `[0x80, 0]`, which does not start with `[0]`: the descent
never reads the skipped bits, and bit 0 is one of them. -/
theorem under_needs_rep :
    Trie.Canon bytesSpec 0 skipped ∧
    under bytesSpec ⟨#[0]⟩ 5 skipped =
      (skipped.toList.filter fun p => startsWith ⟨#[0]⟩ (bytesSpec.kbytes p.1)).take 5 ∧
    ∃ p ∈ underNoRep bytesSpec ⟨#[0]⟩ 5 skipped, startsWith ⟨#[0]⟩ (bytesSpec.kbytes p.1) = false :=
  ⟨Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _ (Trie.canon_empty _ 0)), by decide,
    ⟨(⟨#[0x80, 0]⟩, ()), by
      rw [show underNoRep bytesSpec ⟨#[0]⟩ 5 skipped = [(⟨#[0x80, 0]⟩, ()), (⟨#[0x80, 1]⟩, ())] by decide]
      simp, by decide⟩⟩

/-- A routed tree whose inner node's `rep` is not one of its keys: the root branches at bit 0; its
left child holds `[0, 0]` and `[0, 1]` (branching at bit 15) under the `rep` `[0x80, 0]`, which
agrees with them on the bits routing checks there (`[1, 15)`) and not on bit 0. -/
private def badRep : Trie.T ByteArray Unit UInt8 :=
  .node 0 0 ⟨#[0, 0]⟩ (.node 0 15 ⟨#[0x80, 0]⟩ (.leaf 0 [(⟨#[0, 0]⟩, ())]) (.leaf 0 [(⟨#[0, 1]⟩, ())]))
    (.leaf 0 [(⟨#[0x80, 5]⟩, ())])

/-- **`under_eq`'s shape premise is needed**: `badRep` is routed, and `under` at prefix `[0]` lists
nothing although two of its keys start with `[0]`: routing constrains an inner `rep` only on the
bits below its node's own depth, so a `rep` outside the subtree can fail the prefix the keys
pass. -/
theorem under_needs_shape :
    Trie.Routed bytesSpec 0 badRep ∧ under bytesSpec ⟨#[0]⟩ 5 badRep = [] ∧
    (badRep.toList.filter fun p => startsWith ⟨#[0]⟩ (bytesSpec.kbytes p.1)).length = 2 := by
  refine ⟨?_, by decide, by decide⟩
  have agree : ∀ (L : List (ByteArray × Unit)) (rep : ByteArray) (d b : Nat),
      (∀ p ∈ L, ∀ i, i < b → d ≤ i → bytesSpec.bit p.1 i = bytesSpec.bit rep i) →
      ∀ p ∈ L, ∀ i, d ≤ i → i < b → bytesSpec.bit p.1 i = bytesSpec.bit rep i :=
    fun L rep d b h p hp i h1 h2 => h p hp i h2 h1
  refine ⟨Nat.le_refl 0, agree _ _ _ _ (by decide), by decide, by decide,
    ⟨by decide, agree _ _ _ _ (by decide), by decide, by decide, by simp [Trie.Routed],
      by simp [Trie.Routed]⟩, by simp [Trie.Routed]⟩


/-! ## Bytes as lists -/

private theorem getElem_toList {b : ByteArray} {j : Nat} (h : j < b.size) :
    b[j] = b.data.toList[j]'(by rw [Array.length_toList]; exact h) := by
  rw [ByteArray.getElem_eq_getElem_data, Array.getElem_toList]; rfl

/-- Bits that agree on `8 * m` give bytes that agree below `m`, where both strings have them. -/
private theorem byte_of_bits {a b : ByteArray} {m j : Nat} (hj : j < m) (ha : j < a.size) (hb : j < b.size)
    (h : ∀ i, i < 8 * m → byteBit a i = byteBit b i) :
    a.data.toList[j]'(by simpa using ha) = b.data.toList[j]'(by simpa using hb) := by
  rw [← getElem_toList ha, ← getElem_toList hb]
  exact byte_eq_of_bits ha hb fun t ht => h _ (by omega)

section Rows

/-- **What a key against a range prefix is** (cv 01a14f7e): with every digest `n` bytes, if a rows
key's bytes followed by `Y` are the range prefix followed by `X`, the key is a row of that relation at
that width, under a parent with the parent's bytes, and its own bytes followed by `Y` are `pre`
followed by `X`. A head is told apart by its tag byte; the relation and the width by `natBytes` being
prefix-free (`natBytes_append_inj`), for every relation and width. -/
theorem rowKey_against_prefix (E : Env D) {n : Nat} (hsize : ∀ d, (E.bytes d).size = n)
    {parent : D} {rel width : Nat} {pre : ByteArray} {s : RowSlot D} {X Y : ByteArray}
    (h : rowKeyBytes E s ++ Y = rowsPrefix E parent rel width ++ pre ++ X) :
    ∃ p k, s = .row ⟨p, rel, k⟩ ∧ E.bytes p = E.bytes parent ∧ k.size = width ∧ k ++ Y = pre ++ X := by
  cases s with
  | head p r =>
      exfalso
      simp only [rowKeyBytes, rowsPrefix, ByteArray.append_assoc] at h
      obtain ⟨-, h1⟩ := bytes_append_inj h (by rw [hsize, hsize])
      obtain ⟨-, h2⟩ := natBytes_append_inj h1
      exact absurd (Nanodregg.Codec.head_inj h2).1 (by decide)
  | row key =>
      obtain ⟨p, r, k⟩ := key
      simp only [rowKeyBytes, rowsPrefix, ByteArray.append_assoc] at h
      obtain ⟨hp, h1⟩ := bytes_append_inj h (by rw [hsize, hsize])
      obtain ⟨hr, h2⟩ := natBytes_append_inj h1
      obtain ⟨-, h3⟩ := Nanodregg.Codec.head_inj h2
      obtain ⟨hl, h4⟩ := natBytes_append_inj h3
      exact ⟨p, k, by rw [hr], hp, hl, h4⟩

/-- Bits that agree below `8 * b.size` make the shorter string a byte prefix of the longer. -/
private theorem prefix_of_bits {a b : ByteArray} (hab : a.size ≤ b.size)
    (h : ∀ i, i < 8 * b.size → byteBit a i = byteBit b i) : a.data.toList <+: b.data.toList := by
  rw [List.prefix_iff_getElem]
  refine ⟨by simpa using hab, fun j hj => ?_⟩
  have hja : j < a.size := by simpa using hj
  exact byte_of_bits (m := b.size) (by omega) hja (by omega) h

/-- **The range prefix is long enough** (`under_eq`'s premise, discharged): with every digest `n`
bytes and `pre.size ≤ width`, a rows key whose bits agree with the range prefix's is at least as
long. A shorter one would be a byte prefix of it (`prefix_of_bits`), so a row of the relation at that
width (`rowKey_against_prefix`) whose `width` key bytes are a proper prefix of `pre`: longer than
`width`. No bound on the width (cv 01a14f7e: under the one-byte length it needed `width < 256`). -/
theorem range_prefix_long (E : Env D) {n : Nat} (hsize : ∀ d, (E.bytes d).size = n) {parent : D}
    {rel width : Nat} {pre : ByteArray} (hw : pre.size ≤ width) (s : RowSlot D)
    (h : ∀ i, i < 8 * (rowsPrefix E parent rel width ++ pre).size →
      byteBit (rowKeyBytes E s) i = byteBit (rowsPrefix E parent rel width ++ pre) i) :
    (rowsPrefix E parent rel width ++ pre).size ≤ (rowKeyBytes E s).size := by
  refine Nat.le_of_not_lt fun hlt => ?_
  obtain ⟨t, ht⟩ := prefix_of_bits (Nat.le_of_lt hlt) h
  have he : rowKeyBytes E s ++ ⟨t.toArray⟩ = rowsPrefix E parent rel width ++ pre ++ ByteArray.empty := by
    apply ba_eq_of_toList
    simpa [ByteArray.data_append] using ht
  have hsz := congrArg ByteArray.size he
  obtain ⟨p, k, rfl, -, hk, hkp⟩ := rowKey_against_prefix E hsize he
  have hkp' := congrArg ByteArray.size hkp
  simp only [ByteArray.size_append, ByteArray.size_empty] at hsz hkp' hlt
  omega

/-- **The listing lemma for a range read**: on a canonical rows trie (every digest `n` bytes,
`pre.size ≤ width`), `under` at the range prefix is the trie's listing filtered by the prefix,
cut at `m`. -/
theorem under_rows (E : Env D) {n : Nat} (hsize : ∀ d, (E.bytes d).size = n) {r : Rows D}
    (hc : Trie.Canon (rowSpec E) 0 r) {parent : D} {rel width : Nat} {pre : ByteArray}
    (hw : pre.size ≤ width) (m : Nat) :
    under (rowSpec E) (rowsPrefix E parent rel width ++ pre) m r =
      (r.toList.filter fun p => startsWith (rowsPrefix E parent rel width ++ pre) (rowKeyBytes E p.1)).take m :=
  under_eq (rowSpec E) (fun _ _ => rfl) _ m 0 r hc.1 hc.2.2 (fun _ _ _ _ _ hi => absurd hi (Nat.not_lt_zero _))
    (fun p _ hb => range_prefix_long E hsize hw p.1 hb)

end Rows

/-! ## The trie's listing is in bit order -/

section Order
variable {K V : Type} (S : Trie.Spec K V D)

/-- `BitLt` from a deeper depth `e`, with the keys agreeing on `[d, e)`, is `BitLt` from `d`. -/
private theorem bitLt_of_agree {d e : Nat} {k k' : K} (h : BitLt S e k k') (hde : d ≤ e)
    (he : ∀ j, d ≤ j → j < e → S.bit k j = S.bit k' j) : BitLt S d k k' := by
  obtain ⟨i, hi, hid, hpre, h1, h2⟩ := h
  refine ⟨i, by omega, hid, fun j hj hji => ?_, h1, h2⟩
  by_cases hje : j < e
  · exact he j hj hje
  · exact hpre j (by omega) hji

/-- On a canonical subtree whose keys share their first `d` bits, the listing filtered by `Q` is in
bit order, given that two distinct keys `Q` keeps differ above the trie's depth. -/
private theorem filter_pairwise (Q : K × V → Bool) : ∀ (d : Nat) (t : Trie.T K V D),
    Trie.Routed S d t → Trie.Shape S d t →
    (∀ p ∈ t.toList, ∀ q ∈ t.toList, ∀ j, j < d → S.bit p.1 j = S.bit q.1 j) →
    (∀ p ∈ t.toList, ∀ q ∈ t.toList, Q p = true → Q q = true → p.1 ≠ q.1 →
      ∃ i, i < S.depth ∧ S.bit p.1 i ≠ S.bit q.1 i) →
    (t.toList.filter Q).Pairwise (fun a b => BitLt S d a.1 b.1)
  | _, .empty, _, _, _, _ => by simp [Trie.T.toList]
  | d, .leaf _ kvs, hr, hs, hpath, hsep => by
      simp only [Trie.T.toList] at hpath hsep ⊢
      simp only [Trie.Routed] at hr
      simp only [Trie.Shape] at hs
      have hnd : ((kvs.filter Q).map Prod.fst).Nodup := hr.sublist (List.filter_sublist.map _)
      have hlen : (kvs.filter Q).length ≤ kvs.length := List.length_filter_le _ _
      rcases hf : kvs.filter Q with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · exact List.Pairwise.nil
      · exact List.pairwise_singleton _ _
      · exfalso
        rw [hf] at hnd hlen
        have ha : a ∈ kvs.filter Q := by rw [hf]; simp
        have hb : b ∈ kvs.filter Q := by rw [hf]; simp
        rw [List.mem_filter] at ha hb
        have hne : a.1 ≠ b.1 := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
        obtain ⟨i, hi, hbit⟩ := hsep a ha.1 b hb.1 ha.2 hb.2 hne
        by_cases hid : i < d
        · exact hbit (hpath a ha.1 b hb.1 i hid)
        · simp at hlen
          exact hbit (hs.2 (by omega) a ha.1 b hb.1 i (by omega) hi)
  | d, .node _ b rep l r, hr, hs, hpath, hsep => by
      obtain ⟨hdb, hrep, hl, hrt, hrl, hrr⟩ := hr
      obtain ⟨-, hbd, -, -, hsl, hsr⟩ := hs
      have inL : ∀ p ∈ l.toList, p ∈ l.toList ++ r.toList := fun p hp => List.mem_append_left _ hp
      have inR : ∀ p ∈ r.toList, p ∈ l.toList ++ r.toList := fun p hp => List.mem_append_right _ hp
      simp only [Trie.T.toList] at hpath hsep
      -- two keys of the subtree agree on `[d, b)`, through `rep`
      have hmid : ∀ p ∈ l.toList ++ r.toList, ∀ q ∈ l.toList ++ r.toList, ∀ j, d ≤ j → j < b →
          S.bit p.1 j = S.bit q.1 j := fun p hp q hq j h1 h2 => by
        rw [hrep p hp j h1 h2, hrep q hq j h1 h2]
      have hside : ∀ (s : Trie.T K V D), (∀ p ∈ s.toList, p ∈ l.toList ++ r.toList) →
          (∀ p ∈ s.toList, ∀ q ∈ s.toList, S.bit p.1 b = S.bit q.1 b) →
          (s.toList.filter Q).Pairwise (fun x y => BitLt S (b + 1) x.1 y.1) →
          (s.toList.filter Q).Pairwise (fun x y => BitLt S d x.1 y.1) := by
        intro s hs' hsb hp
        refine List.Pairwise.imp_of_mem (fun ha hc h => bitLt_of_agree S h (by omega) fun j h1 h2 => ?_) hp
        have ha' := (List.mem_filter.mp ha).1
        have hc' := (List.mem_filter.mp hc).1
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h2) with hlt | rfl
        · exact hmid _ (hs' _ ha') _ (hs' _ hc') j h1 hlt
        · exact hsb _ ha' _ hc'
      have hsub : ∀ (s : Trie.T K V D), (∀ p ∈ s.toList, p ∈ l.toList ++ r.toList) →
          (∀ p ∈ s.toList, ∀ q ∈ s.toList, S.bit p.1 b = S.bit q.1 b) →
          ∀ p ∈ s.toList, ∀ q ∈ s.toList, ∀ j, j < b + 1 → S.bit p.1 j = S.bit q.1 j := by
        intro s hs' hsb p hp q hq j hj
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
        · by_cases hjd : j < d
          · exact hpath p (hs' p hp) q (hs' q hq) j hjd
          · exact hmid p (hs' p hp) q (hs' q hq) j (by omega) hlt
        · exact hsb p hp q hq
      have hbl : ∀ p ∈ l.toList, ∀ q ∈ l.toList, S.bit p.1 b = S.bit q.1 b := fun p hp q hq => by
        rw [hl p hp, hl q hq]
      have hbr : ∀ p ∈ r.toList, ∀ q ∈ r.toList, S.bit p.1 b = S.bit q.1 b := fun p hp q hq => by
        rw [hrt p hp, hrt q hq]
      simp only [Trie.T.toList, List.filter_append, List.pairwise_append]
      refine ⟨hside l inL hbl (filter_pairwise Q (b + 1) l hrl hsl (hsub l inL hbl)
          (fun p hp q hq => hsep p (inL p hp) q (inL q hq))),
        hside r inR hbr (filter_pairwise Q (b + 1) r hrr hsr (hsub r inR hbr)
          (fun p hp q hq => hsep p (inR p hp) q (inR q hq))), ?_⟩
      intro a ha c hc
      have ha' := inL _ (List.mem_filter.mp ha).1
      have hc' := inR _ (List.mem_filter.mp hc).1
      exact ⟨b, hdb, hbd, fun j h1 h2 => hmid _ ha' _ hc' j h1 h2,
        hl _ (List.mem_filter.mp ha).1, hrt _ (List.mem_filter.mp hc).1⟩

end Order

/-! ## The first differing bit decides `compare` -/

/-- Two different strings of one size differ at a bit inside them. -/
private theorem bit_diff {a b : ByteArray} (hs : a.size = b.size) (hne : a ≠ b) :
    ∃ i, i < 8 * a.size ∧ byteBit a i ≠ byteBit b i :=
  Classical.byContradiction fun hno => hne (byteBit_ext hs fun i hi =>
    Classical.byContradiction fun h => hno ⟨i, hi, h⟩)

/-! ## The rows a range read lists -/

section Range
variable [DecidableEq D]

private theorem prefix_of_startsWith {pre b : ByteArray} (h : startsWith pre b = true) :
    pre.data.toList <+: b.data.toList := by
  obtain ⟨hs, he⟩ := startsWith_iff.mp h
  rw [List.prefix_iff_getElem]
  refine ⟨by simpa using hs, fun i hi => ?_⟩
  have hi' : i < pre.size := by simpa using hi
  have := he i hi' (by omega)
  rw [getElem_toList, getElem_toList] at this
  exact this.symm

omit [DecidableEq D] in
private theorem fits_row {key : RowKey D} {v : RowLeaf} (h : rowFits (.row key) v = true) :
    key.rel < 256 ∧ key.k.size ≤ Bounds.keyBytesMax := by
  cases v <;> simp_all [rowFits]

omit [DecidableEq D] in
/-- **A key under a range prefix**, with every digest `n` bytes: a row of that relation at that width,
under a parent with the parent's bytes, for every key (cv 01a14f7e: under the one-byte encoding the
relation and the width were read mod 256, and only for keys that fit). -/
theorem key_under_prefix (E : Env D) {n : Nat} (hsize : ∀ d, (E.bytes d).size = n) {parent : D}
    {rel width : Nat} {pre : ByteArray} {s : RowSlot D}
    (hs : startsWith (rowsPrefix E parent rel width ++ pre) (rowKeyBytes E s) = true) :
    ∃ p k, s = .row ⟨p, rel, k⟩ ∧ E.bytes p = E.bytes parent ∧ k.size = width := by
  obtain ⟨t, ht⟩ := prefix_of_startsWith hs
  have he : rowKeyBytes E s ++ ByteArray.empty = rowsPrefix E parent rel width ++ pre ++ ⟨t.toArray⟩ := by
    apply ba_eq_of_toList
    simpa [ByteArray.data_append] using ht.symm
  obtain ⟨p, k, hk, hp, hw, -⟩ := rowKey_against_prefix E hsize he
  exact ⟨p, k, hk, hp, hw⟩

omit [DecidableEq D] in
/-- **What a listed key is**: with every digest `n` bytes and `E.bytes` injective, a rows key that
starts with the range prefix is a row of that parent and relation whose key has the relation's width
(`key_under_prefix`). -/
theorem listed_key (E : Env D) {n : Nat} (hsize : ∀ d, (E.bytes d).size = n)
    (hinj : Function.Injective E.bytes) {parent : D} {rel width : Nat} {pre : ByteArray} {s : RowSlot D}
    (hs : startsWith (rowsPrefix E parent rel width ++ pre) (rowKeyBytes E s) = true) :
    ∃ k : ByteArray, s = .row ⟨parent, rel, k⟩ ∧ k.size = width := by
  obtain ⟨p, k, rfl, hp, hk⟩ := key_under_prefix E hsize hs
  exact ⟨k, by rw [hinj hp], hk⟩

omit [DecidableEq D] in
/-- The rows under a range prefix: the trie's listing, filtered by the prefix. -/
private theorem rangeRows_some {E : Env D} {n : Nat} (hsize : ∀ d, (E.bytes d).size = n) {r : Rows D}
    (hc : Trie.Canon (rowSpec E) 0 r) {parent : D} {rel width : Nat} {pre : ByteArray}
    (hw : pre.size ≤ width) {most : Nat} {l : List (RowSlot D × RowLeaf)}
    (h : rangeRows E r parent rel width pre most = some l) :
    l = r.toList.filter (fun p => startsWith (rowsPrefix E parent rel width ++ pre) (rowKeyBytes E p.1)) ∧
      l.length ≤ most := by
  unfold rangeRows at h
  simp only at h
  rw [under_rows E hsize hc hw] at h
  split at h
  · rename_i hle
    cases h
    refine ⟨?_, hle⟩
    rw [List.length_take] at hle
    exact List.take_of_length_le (by omega)
  · cases h

omit [DecidableEq D] in
/-- **(iii) A range read is refused exactly when more than `most` rows are under its prefix.** -/
theorem range_rows_none {E : Env D} {n : Nat} (hsize : ∀ d, (E.bytes d).size = n) {r : Rows D}
    (hc : Trie.Canon (rowSpec E) 0 r) {parent : D} {rel width : Nat} {pre : ByteArray}
    (hw : pre.size ≤ width) (most : Nat) :
    rangeRows E r parent rel width pre most = none ↔
      most < (r.toList.filter fun p =>
        startsWith (rowsPrefix E parent rel width ++ pre) (rowKeyBytes E p.1)).length := by
  unfold rangeRows
  simp only
  rw [under_rows E hsize hc hw, List.length_take]
  split <;> simp <;> omega

/-- **(i) The rows a range read lists are exactly the rows under its prefix.** -/
theorem range_rows_mem {E : Env D} {n : Nat} (hsize : ∀ d, (E.bytes d).size = n) {r : Rows D}
    (hc : Trie.Canon (rowSpec E) 0 r) {parent : D} {rel width : Nat} {pre : ByteArray}
    (hw : pre.size ≤ width) {most : Nat} {l : List (RowSlot D × RowLeaf)}
    (h : rangeRows E r parent rel width pre most = some l) (s : RowSlot D) (v : RowLeaf) :
    (s, v) ∈ l ↔ rowAt E r s = some v ∧
      startsWith (rowsPrefix E parent rel width ++ pre) (rowKeyBytes E s) = true := by
  rw [(rangeRows_some hsize hc hw h).1, List.mem_filter, Trie.mem_toList (rowSpec E) 0 r hc.1]
  rfl

omit [DecidableEq D] in
/-- **(ii) A range read lists its rows in strictly ascending key-byte order** (`compare` on the key
bytes, the codec's order). Beyond (i)'s premises: the trie is canonical, `E.bytes` is injective with
digests of at most 32 bytes, and every entry of the rows fits (`rowFits`, what admission keeps). -/
theorem range_rows_sorted {E : Env D} {n : Nat} (hsize : ∀ d, (E.bytes d).size = n) (hn : n ≤ 32)
    (hinj : Function.Injective E.bytes) {r : Rows D} (hc : Trie.Canon (rowSpec E) 0 r)
    (hfit : ∀ p ∈ r.toList, rowFits p.1 p.2 = true) {parent : D} {rel width : Nat} {pre : ByteArray}
    (hw : pre.size ≤ width) {most : Nat} {l : List (RowSlot D × RowLeaf)}
    (h : rangeRows E r parent rel width pre most = some l) :
    l.Pairwise fun a b => compare (rowKeyBytes E a.1).data (rowKeyBytes E b.1).data = .lt := by
  rw [(rangeRows_some hsize hc hw h).1]
  have hkey : ∀ p ∈ r.toList,
      startsWith (rowsPrefix E parent rel width ++ pre) (rowKeyBytes E p.1) = true →
      ∃ k : ByteArray, p.1 = .row ⟨parent, rel, k⟩ ∧ k.size = width ∧ k.size ≤ Bounds.keyBytesMax ∧
        rel < 256 ∧ (rowKeyBytes E p.1).size = n + (natBytes rel).size + 1 + (natBytes width).size + k.size := by
    intro p hp hs
    obtain ⟨k, hk, hks⟩ := listed_key E hsize hinj hs
    have hf := fits_row (v := p.2) (by rw [← hk]; exact hfit p hp)
    refine ⟨k, hk, hks, hf.2, hf.1, ?_⟩
    rw [hk]; simp only [rowKeyBytes, rowsPrefix, ByteArray.size_append, hsize, byte8_size, hks]
  have hpw := filter_pairwise (rowSpec E)
    (fun p => startsWith (rowsPrefix E parent rel width ++ pre) (rowKeyBytes E p.1)) 0 r hc.1 hc.2.2
    (fun _ _ _ _ _ hj => absurd hj (Nat.not_lt_zero _))
    (fun p hp q hq hps hqs hne => by
      obtain ⟨k, hk, hks, hkm, hrel, hsz⟩ := hkey p hp hps
      obtain ⟨k', hk', hks', -, -, hsz'⟩ := hkey q hq hqs
      have hb : rowKeyBytes E p.1 ≠ rowKeyBytes E q.1 := by
        intro he
        apply hne
        rw [hk, hk'] at he ⊢
        simp only [rowKeyBytes, hks, hks'] at he
        rw [ByteArray.append_right_inj] at he
        rw [he]
      obtain ⟨i, hi, hd⟩ := bit_diff (by rw [hsz, hsz', hks, hks']) hb
      refine ⟨i, ?_, hd⟩
      show i < Bounds.rowDepth
      have h1 := natBytes_size_le_two hrel
      have h2 := natBytes_size_le_two (r := width) (by simp [Bounds.keyBytesMax] at hkm; omega)
      simp [Bounds.rowDepth, Bounds.keyBytesMax] at hkm ⊢
      omega)
  refine List.Pairwise.imp_of_mem (fun ha hb hab => ?_) hpw
  obtain ⟨i, -, -, hpre, h1, h2⟩ := hab
  obtain ⟨k, -, hks, -, -, hsz⟩ := hkey _ (List.mem_filter.mp ha).1 (List.mem_filter.mp ha).2
  obtain ⟨k', -, hks', -, -, hsz'⟩ := hkey _ (List.mem_filter.mp hb).1 (List.mem_filter.mp hb).2
  exact compare_lt_of_bits (by rw [hsz, hsz', hks, hks']) (fun j hj => hpre j (Nat.zero_le j) hj) h1 h2


/-- `range_rows_exact` at the `Env` fields it uses: one digest size `n ≤ 32`, injective bytes. -/
theorem range_rows_exact_of {E : Env D} {n : Nat} (hsize : ∀ d, (E.bytes d).size = n) (hn : n ≤ 32)
    (hinj : Function.Injective E.bytes) {r : Rows D}
    (hc : Trie.Canon (rowSpec E) 0 r) (hfit : ∀ p ∈ r.toList, rowFits p.1 p.2 = true) {parent : D}
    {rel width : Nat} {pre : ByteArray} (hw : pre.size ≤ width) {most : Nat}
    {l : List (RowSlot D × RowLeaf)} (h : rangeRows E r parent rel width pre most = some l) :
    (∀ s v, (s, v) ∈ l ↔ rowAt E r s = some v ∧
      startsWith (rowsPrefix E parent rel width ++ pre) (rowKeyBytes E s) = true) ∧
    l.Pairwise (fun a b => compare (rowKeyBytes E a.1).data (rowKeyBytes E b.1).data = .lt) ∧
    l.length ≤ most :=
  ⟨range_rows_mem hsize hc hw h, range_rows_sorted hsize hn hinj hc hfit hw h,
    (rangeRows_some hsize hc hw h).2⟩

/-- **`range_rows_exact`** (ROOT's condition (a), KERNEL-46/48): over a lawful `Env`, on canonical rows
whose entries fit, a range read at `pre.size ≤ width` that is not refused lists (i) exactly
the rows whose key starts with the range prefix, (ii) in strictly ascending key-byte order, (iii)
at most `most` of them; and it is refused (`none`) exactly when more than `most` rows are under the
prefix (`range_rows_none`). -/
theorem range_rows_exact [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) {r : Rows D}
    (hc : Trie.Canon (rowSpec E) 0 r) (hfit : ∀ p ∈ r.toList, rowFits p.1 p.2 = true) {parent : D}
    {rel width : Nat} {pre : ByteArray} (hw : pre.size ≤ width) {most : Nat}
    {l : List (RowSlot D × RowLeaf)} (h : rangeRows E r parent rel width pre most = some l) :
    (∀ s v, (s, v) ∈ l ↔ rowAt E r s = some v ∧
      startsWith (rowsPrefix E parent rel width ++ pre) (rowKeyBytes E s) = true) ∧
    l.Pairwise (fun a b => compare (rowKeyBytes E a.1).data (rowKeyBytes E b.1).data = .lt) ∧
    l.length ≤ most :=
  range_rows_exact_of hE.size hE.n_le hE.bytes_inj hc hfit hw h

omit [DecidableEq D] in
/-- The `hfit` premise is what a decoded base already checks: `rowsFits` (CODEC-9's
`kernel/rows`) gives it for every entry of the listing. -/
theorem rowFits_of_rowsFits {E : Env D} {l : List (RowSlot D × RowLeaf)} (h : rowsFits E l = true) :
    ∀ p ∈ l, rowFits p.1 p.2 = true := by
  unfold rowsFits at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  exact h.2

omit [DecidableEq D] in
private theorem headOf_some {E : Env D} [DecidableEq D] {r : Rows D} {parent : D} {rel c s lim cap width : Nat}
    {rt : Bool} (h : headOf E r parent rel = some (c, s, lim, cap, width, rt)) :
    rowAt E r (.head parent rel) = some (.head c s lim cap width rt (headFloor E r parent rel)) := by
  unfold headOf at h
  split at h
  · rename_i f heq
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    simp only [headFloor, heq]
  · cases h

/-- `admit_range_exact` at the `Env` fields it uses: one digest size `n ≤ 32`, injective bytes. -/
theorem admit_range_exact_of [Ord D] {E : Env D} {n : Nat} (hsize : ∀ d, (E.bytes d).size = n) (hn : n ≤ 32)
    (hinj : Function.Injective E.bytes) {w w' : World D} {t : Turn D}
    (hc : Trie.Canon (rowSpec E) 0 w.rows) (hfit : ∀ p ∈ w.rows.toList, rowFits p.1 p.2 = true)
    (h : World.admit E w t = .ok w') :
    ∀ q ∈ t.ranges, ∃ c s lim cap width rt l,
      headOf E w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) ∧ q.pre.size ≤ width ∧
      rangeRows E w.rows q.parent q.rel width q.pre q.most = some l ∧
      rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l = q.seen ∧
      (∀ s v, (s, v) ∈ l ↔ rowAt E w.rows s = some v ∧
        startsWith (rowsPrefix E q.parent q.rel width ++ q.pre) (rowKeyBytes E s) = true) ∧
      l.Pairwise (fun a b => compare (rowKeyBytes E a.1).data (rowKeyBytes E b.1).data = .lt) := by
  obtain ⟨_, hk, _⟩ := admit_ok h
  intro q hq
  have hq' := (forEx_ok.mp hk.ranges) q hq
  simp only [except_bind_ok] at hq'
  obtain ⟨⟨⟩, -, hq'⟩ := hq'
  split at hq'
  · simp at hq'
  · rename_i c s lim cap width rt hh
    simp only [except_bind_ok] at hq'
    obtain ⟨⟨⟩, hpw, hq'⟩ := hq'
    have hpw' : q.pre.size ≤ width := of_decide_eq_true (req_ok.mp hpw)
    split at hq'
    · simp at hq'
    · rename_i l hl
      obtain ⟨hi, hii, -⟩ := range_rows_exact_of hsize hn hinj hc hfit hpw' hl
      exact ⟨c, s, lim, cap, width, rt, l, hh, hpw', hl, of_decide_eq_true (req_ok.mp hq'), hi, hii⟩

/-- **The admitted form**: for an admitted turn on canonical rows whose entries fit, over a lawful
`Env`, every range read's relation has a head of some `width ≥ pre.size`, and the listing whose pin
the signer gave (`q.seen`) lists exactly the World's rows under the prefix, in ascending key order. -/
theorem admit_range_exact [Ord D] {E : Env D} {n : Nat} (hE : E.Lawful n) {w w' : World D} {t : Turn D}
    (hc : Trie.Canon (rowSpec E) 0 w.rows) (hfit : ∀ p ∈ w.rows.toList, rowFits p.1 p.2 = true)
    (h : World.admit E w t = .ok w') :
    ∀ q ∈ t.ranges, ∃ c s lim cap width rt l,
      headOf E w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) ∧ q.pre.size ≤ width ∧
      rangeRows E w.rows q.parent q.rel width q.pre q.most = some l ∧
      rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l = q.seen ∧
      (∀ s v, (s, v) ∈ l ↔ rowAt E w.rows s = some v ∧
        startsWith (rowsPrefix E q.parent q.rel width ++ q.pre) (rowKeyBytes E s) = true) ∧
      l.Pairwise (fun a b => compare (rowKeyBytes E a.1).data (rowKeyBytes E b.1).data = .lt) :=
  admit_range_exact_of hE.size hE.n_le hE.bytes_inj hc hfit h

/-! ## The tooth: a listing with a dropped row -/

omit [DecidableEq D] in
private theorem nat32_ne_pred {m : Nat} (hm : 0 < m) :
    Nanodregg.Codec.Stream.nat32.bytes (m - 1) ≠ Nanodregg.Codec.Stream.nat32.bytes m := by
  intro he
  rw [Nanodregg.Codec.Stream.nat32_bytes, Nanodregg.Codec.Stream.nat32_bytes] at he
  have := congrArg UInt32.toNat (Nanodregg.Codec.Stream.u32_lawful.on.bytes_injective trivial trivial he)
  simp at this
  omega

/-- **(a) The range pin sees a dropped row**: the listing with one of its rows erased has another
pin preimage (its length field differs: `m - 1` and `m` differ mod 2^32 for every `m ≥ 1`, so no
bound on the listing is needed). -/
theorem rangePinBytes_erase_ne (E : Env D) (parent : D) (rel width : Nat) (pre : ByteArray) (floor : Nat)
    {l : List (RowSlot D × RowLeaf)} {p : RowSlot D × RowLeaf} (hp : p ∈ l) :
    rangePinBytes E parent rel width pre floor (l.erase p) ≠ rangePinBytes E parent rel width pre floor l := by
  intro he
  unfold rangePinBytes at he
  simp only [ByteArray.append_assoc, ByteArray.append_right_inj] at he
  have h4 : ∀ m, (Nanodregg.Codec.Stream.nat32.bytes m).size = 4 := fun m =>
    (Nanodregg.Codec.Stream.nat32_lawfulOn.size_eq m).symm
  have := bytes_append_inj he (by rw [h4, h4])
  rw [List.length_erase_of_mem hp] at this
  exact nat32_ne_pred (List.length_pos_of_mem hp) this.1

/-- **(b) Exactness refutes a listing with a dropped row**: for a range read's listing `l` (premises
of (i)) and a row `p` of it, `l.erase p` does NOT list exactly the rows under the prefix: `p` is one
of them and it is gone. -/
theorem range_rows_erase_not_exact {E : Env D} {n : Nat} (hsize : ∀ d, (E.bytes d).size = n) {r : Rows D}
    (hc : Trie.Canon (rowSpec E) 0 r) {parent : D} {rel width : Nat} {pre : ByteArray}
    (hw : pre.size ≤ width) {most : Nat} {l : List (RowSlot D × RowLeaf)}
    (h : rangeRows E r parent rel width pre most = some l) {p : RowSlot D × RowLeaf} (hp : p ∈ l) :
    ¬ ∀ s v, (s, v) ∈ l.erase p ↔ rowAt E r s = some v ∧
      startsWith (rowsPrefix E parent rel width ++ pre) (rowKeyBytes E s) = true := by
  intro hx
  have hnd : l.Nodup := by
    rw [(rangeRows_some hsize hc hw h).1]
    exact (Trie.nodup_of_map_fst (Trie.toList_nodup (rowSpec E) 0 r hc.1)).filter _
  have hin := (hx p.1 p.2).mpr ((range_rows_mem hsize hc hw h p.1 p.2).mp hp)
  rw [hnd.mem_erase_iff] at hin
  exact hin.1 rfl

/-- The amount column of a rows leaf. -/
private def amtOf : RowLeaf → Nat
  | .row a _ _ => a
  | .head .. => 0

/-- A seal a method might compute from a listing: the first row with the greatest amount. -/
private def argMaxAmt (l : List (RowSlot D × RowLeaf)) : Option (RowSlot D) :=
  (l.foldl (fun best p => match best with
    | none => some (p.1, amtOf p.2)
    | some (s, a) => if a < amtOf p.2 then some (p.1, amtOf p.2) else some (s, a)) none).map Prod.fst

end Range

/-! ## The premises are satisfiable, and the conclusions bite, on a concrete trie

A toy `Env` over one-byte digests (`bytes d = [d]`: one size, injective) and the rows trie made by
four inserts: the head of relation 3 under parent 7 (width 2) and three rows, two of them under the
key prefix `[1]`. The trie is canonical (`Trie.canon_insert`), every entry fits, and the range read
at prefix `[1]` lists the two rows under it, in key order, and not the third. -/

private def toyEnv : Env UInt8 where
  hash _ _ := 0
  bytes d := ⟨#[d]⟩
  turnBytes _ := ByteArray.empty
  cellBytes _ := ByteArray.empty

private def toyS1 : RowSlot UInt8 := .row ⟨7, 3, ⟨#[1, 2]⟩⟩
private def toyS2 : RowSlot UInt8 := .row ⟨7, 3, ⟨#[1, 9]⟩⟩
private def toyS3 : RowSlot UInt8 := .row ⟨7, 3, ⟨#[4, 4]⟩⟩

private def toyRows : Rows UInt8 :=
  (((Trie.T.empty.insert (rowSpec toyEnv) toyS2 (.row 9 ByteArray.empty 0)).insert (rowSpec toyEnv) toyS3
    (.row 1 ByteArray.empty 0)).insert (rowSpec toyEnv) toyS1 (.row 5 ByteArray.empty 0)).insert (rowSpec toyEnv)
    (.head 7 3) (.head 3 15 10 100 2 false 0)

private def toyListing : List (RowSlot UInt8 × RowLeaf) :=
  [(toyS1, .row 5 ByteArray.empty 0), (toyS2, .row 9 ByteArray.empty 0)]

private theorem toy_size (d : UInt8) : (toyEnv.bytes d).size = 1 := rfl

private theorem toy_inj : Function.Injective toyEnv.bytes := by
  intro a b h
  have := congrArg (fun x : ByteArray => x.data[0]!) h
  simpa [toyEnv] using this

private theorem toy_canon : Trie.Canon (rowSpec toyEnv) 0 toyRows :=
  Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _
    (Trie.canon_insert _ _ _ (Trie.canon_empty _ 0))))

private theorem toy_fit : ∀ p ∈ toyRows.toList, rowFits p.1 p.2 = true := by decide

private theorem toy_range : rangeRows toyEnv toyRows 7 3 2 ⟨#[1]⟩ 5 = some toyListing := by decide

/-- **The range theorems are not vacuous**: on a concrete canonical rows trie whose entries fit,
under an `Env` with one digest size and injective bytes, at `pre.size = 1 ≤ width = 2`, the
range read lists two rows — not every row of the trie (`toyS3` is in it and not listed) — and (i),
(ii) and the length bound hold of that listing. -/
theorem range_rows_satisfiable :
    ∃ (E : Env UInt8) (r : Rows UInt8) (l : List (RowSlot UInt8 × RowLeaf)),
      (∀ d, (E.bytes d).size = 1) ∧ Function.Injective E.bytes ∧ Trie.Canon (rowSpec E) 0 r ∧
      (∀ p ∈ r.toList, rowFits p.1 p.2 = true) ∧ rangeRows E r 7 3 2 ⟨#[1]⟩ 5 = some l ∧
      l.length = 2 ∧ (∃ p ∈ r.toList, p ∉ l) ∧
      (∀ s v, (s, v) ∈ l ↔ rowAt E r s = some v ∧
        startsWith (rowsPrefix E 7 3 2 ++ ⟨#[1]⟩) (rowKeyBytes E s) = true) ∧
      l.Pairwise (fun a b => compare (rowKeyBytes E a.1).data (rowKeyBytes E b.1).data = .lt) :=
  ⟨toyEnv, toyRows, toyListing, toy_size, toy_inj, toy_canon, toy_fit, toy_range, rfl,
    ⟨(toyS3, .row 1 ByteArray.empty 0), by decide, by decide⟩,
    range_rows_mem toy_size toy_canon (by decide) toy_range,
    range_rows_sorted toy_size (by decide) toy_inj toy_canon toy_fit (by decide) toy_range⟩

/-- **(c) The seal tooth**: on that listing, the arg-max seal is `toyS2`; drop its row and the seal
a method computes is `toyS1` — and `range_rows_erase_not_exact` refutes the dropped listing, and its
range pin differs (`rangePinBytes_erase_ne`). -/
theorem range_seal_tooth :
    argMaxAmt toyListing = some toyS2 ∧
    argMaxAmt (toyListing.erase (toyS2, .row 9 ByteArray.empty 0)) = some toyS1 ∧
    (¬ ∀ s v, (s, v) ∈ toyListing.erase (toyS2, .row 9 ByteArray.empty 0) ↔ rowAt toyEnv toyRows s = some v ∧
      startsWith (rowsPrefix toyEnv 7 3 2 ++ ⟨#[1]⟩) (rowKeyBytes toyEnv s) = true) ∧
    rangePinBytes toyEnv 7 3 2 ⟨#[1]⟩ 0 (toyListing.erase (toyS2, .row 9 ByteArray.empty 0)) ≠
      rangePinBytes toyEnv 7 3 2 ⟨#[1]⟩ 0 toyListing :=
  ⟨by decide, by decide,
    range_rows_erase_not_exact toy_size toy_canon (by decide) toy_range (by decide),
    rangePinBytes_erase_ne _ _ _ _ _ _ (by decide)⟩

/-! ## A turn with a range read is admitted (the admitted form is not vacuous)

A toy `Env` whose hash is the input's length (so a pin over a listing with a dropped row differs),
one-byte digests; a World with one live cell 7, its relation 3 declared (width 2) and three rows,
two under the key prefix `[1]`; and a turn that keeps cell 7 and reads the range at `[1]`, pinned at
the listing the World holds. -/

private def admEnv : Env UInt8 where
  hash _ b := UInt8.ofNat b.size
  bytes d := ⟨#[d]⟩
  turnBytes _ := ByteArray.empty
  cellBytes _ := ByteArray.empty

private def admCell : Cell := { kind := 0, discipline := .ram, slots := [] }

private def admRows : Rows UInt8 :=
  (((Trie.T.empty.insert (rowSpec admEnv) (.head 7 3) (.head 3 15 10 100 2 false 0)).insert (rowSpec admEnv) toyS1
    (.row 5 ByteArray.empty 0)).insert (rowSpec admEnv) toyS2 (.row 9 ByteArray.empty 0)).insert (rowSpec admEnv) toyS3
    (.row 1 ByteArray.empty 0)

private def admWorld : World UInt8 where
  trie := Trie.T.empty.insert (trieSpec admEnv) (.cell 7) (.entry (.live admCell 0))
  journal := .empty
  refusals := .empty
  rows := admRows
  height := 0
  steps := 0
  chain := 0
  allowance := 1000000
  origin := 0

private def admRange (l : List (RowSlot UInt8 × RowLeaf)) : RangeRead UInt8 :=
  { parent := 7, rel := 3, pre := ⟨#[1]⟩, most := 5, seen := rangePin admEnv 7 3 2 ⟨#[1]⟩ 0 l }

private def admTurn0 (l : List (RowSlot UInt8 × RowLeaf)) : Turn UInt8 :=
  { txId := 1, notBefore := 0, validUntil := 1, touches := [⟨7, pinOf admEnv (some (.live admCell 0)), .keep⟩],
    creates := [], nullifiers := [], charge := 0, event := ByteArray.empty, ranges := [admRange l], member := 0 }

private def admTurn (l : List (RowSlot UInt8 × RowLeaf)) : Turn UInt8 :=
  { admTurn0 l with charge := (admTurn0 l).weight }

/-- Whether a result is the refusal `e` (`World` has no decidable equality; `Reject` has). -/
private def refusedWith {α : Type} : Except (Reject UInt8) α → Reject UInt8 → Bool
  | .error r, e => decide (r = e)
  | .ok _, _ => false

private theorem error_of_refusedWith {α : Type} {x : Except (Reject UInt8) α} {e : Reject UInt8}
    (h : refusedWith x e = true) : x = .error e := by
  cases x with
  | error r => simp only [refusedWith, decide_eq_true_eq] at h; rw [h]
  | ok _ => cases h

private theorem adm_ok : (World.admit admEnv admWorld (admTurn toyListing)).isOk = true := by decide

private theorem adm_stale :
    World.admit admEnv admWorld { admTurn toyListing with
      ranges := [admRange (toyListing.erase (toyS2, .row 9 ByteArray.empty 0))] } = .error (.stale 7) :=
  error_of_refusedWith (by decide)

/-- **A turn with a range read is admitted, and what the admitted form says of it is not trivial.**
On a concrete World (cell 7 live, relation 3 under it declared at width 2, three rows) the turn that
keeps cell 7 and reads relation 3 at prefix `[1]`, pinned at the World's own listing, is admitted;
`admit_range_exact_of` then gives its listing, which holds `toyS1`'s row and not `toyS3`'s; and the
same turn (same charge) pinned at the listing with `toyS2`'s row dropped is refused `stale` at cell 7. -/
theorem range_admit_satisfiable :
    ∃ (E : Env UInt8) (w w' : World UInt8) (t : Turn UInt8) (q : RangeRead UInt8),
      w.live E q.parent = some admCell ∧ t.touches = [⟨q.parent, pinOf E (some (.live admCell 0)), .keep⟩] ∧
      t.ranges = [q] ∧ World.admit E w t = .ok w' ∧
      (∃ width l, rangeRows E w.rows q.parent q.rel width q.pre q.most = some l ∧
        rangePin E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l = q.seen ∧
        (toyS1, .row 5 ByteArray.empty 0) ∈ l ∧ (toyS3, .row 1 ByteArray.empty 0) ∉ l) ∧
      (World.admit E w { t with ranges := [RangeRead.mk q.parent q.rel q.pre q.most
        (rangePin E q.parent q.rel 2 q.pre (headFloor E w.rows q.parent q.rel) (toyListing.erase (toyS2, .row 9 ByteArray.empty 0)))] }) =
        .error (.stale q.parent) := by
  have hc : Trie.Canon (rowSpec admEnv) 0 admRows :=
    Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _
      (Trie.canon_insert _ _ _ (Trie.canon_empty _ 0))))
  have hfit : ∀ p ∈ admRows.toList, rowFits p.1 p.2 = true := by decide
  have hinj : Function.Injective admEnv.bytes := by
    intro a b h
    have := congrArg (fun x : ByteArray => x.data[0]!) h
    simpa [admEnv] using this
  cases hw : World.admit admEnv admWorld (admTurn toyListing) with
  | error e => have h0 := adm_ok; rw [hw] at h0; cases h0
  | ok w' =>
    refine ⟨admEnv, admWorld, w', admTurn toyListing, admRange toyListing, by decide, rfl, rfl, hw, ?_, adm_stale⟩
    obtain ⟨c, s, lim, cap, width, rt, l, hh, -, hl, hp, hi, -⟩ :=
      admit_range_exact_of (n := 1) (fun _ => rfl) (by decide) hinj hc hfit hw (admRange toyListing)
        (by simp [admTurn, admTurn0])
    have hh' : headOf admEnv admRows 7 3 = some (3, 15, 10, 100, 2, false) := by decide
    have hwd : width = 2 := by
      have := hh.symm.trans hh'
      simp only [Option.some.injEq, Prod.mk.injEq] at this
      exact this.2.2.2.2.1
    subst hwd
    refine ⟨2, l, hl, hp, (hi _ _).mpr ⟨by decide, by decide⟩, fun hm => ?_⟩
    have := ((hi _ _).mp hm).2
    revert this
    decide

end Nanodregg.Kernel
