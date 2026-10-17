import Codec.Stream

/-! # Stream laws — every codec is canonical

`Lawful c` says three things about `c`:

* `put_eq`: writing appends exactly `bytes v` to the buffer;
* `get_of_occurs`: wherever `bytes v` occurs in an input, reading there yields `v`
  and the offset just past it (so `decode ∘ bytes = ok`);
* `occurs_of_get`: whenever reading succeeds with `v`, the bytes it consumed are
  exactly `bytes v` (so the only input that decodes to `v` is `bytes v`).

The last is canonicity: no second spelling of any value is accepted, so no caller
ever re-encodes to check. `decode_eq_ok_iff` is the whole-input statement. -/

namespace Nanodregg.Codec.Stream

variable {α β : Type}

/-- `w` occurs in `b` at offset `i`. -/
def OccursAt (b : ByteArray) (i : Nat) (w : ByteArray) : Prop :=
  i + w.size ≤ b.size ∧ b.extract i (i + w.size) = w

structure Lawful (c : Stream α) : Prop where
  put_eq : ∀ v buf, c.put v buf = buf ++ c.bytes v
  size_eq : ∀ v, c.size v = (c.bytes v).size
  get_of_occurs : ∀ v b i, OccursAt b i (c.bytes v) → c.get b i = .ok (v, i + (c.bytes v).size)
  occurs_of_get : ∀ {b i v j}, c.get b i = .ok (v, j) →
    j = i + (c.bytes v).size ∧ OccursAt b i (c.bytes v)

/-! ## Occurrence -/

theorem occursAt_self (w : ByteArray) : OccursAt w 0 w :=
  ⟨by omega, by simp⟩

theorem occursAt_append {b x y : ByteArray} {i : Nat} :
    OccursAt b i (x ++ y) ↔ OccursAt b i x ∧ OccursAt b (i + x.size) y := by
  simp only [OccursAt, ByteArray.size_append]
  constructor
  · rintro ⟨hs, he⟩
    have hx : b.extract i (i + x.size) = x := by
      have := congrArg (fun a => a.extract 0 x.size) he
      simp only [ByteArray.extract_extract] at this
      rw [ByteArray.extract_append_eq_left rfl] at this
      simpa [Nat.add_zero, Nat.min_eq_left (by omega : i + x.size ≤ i + (x.size + y.size))] using this
    have hy : b.extract (i + x.size) (i + x.size + y.size) = y := by
      have := congrArg (fun a => a.extract x.size (x.size + y.size)) he
      simp only [ByteArray.extract_extract] at this
      rw [ByteArray.extract_append_eq_right rfl rfl] at this
      simpa [Nat.add_assoc, Nat.min_self] using this
    exact ⟨⟨by omega, hx⟩, ⟨by omega, hy⟩⟩
  · rintro ⟨⟨hs, hx⟩, ⟨hs', hy⟩⟩
    refine ⟨by omega, ?_⟩
    rw [ByteArray.extract_eq_extract_append_extract (i + x.size) (by omega) (by omega), hx,
      ← Nat.add_assoc, hy]

theorem eq_of_occursAt_zero {b w : ByteArray} (h : OccursAt b 0 w) (hs : w.size = b.size) : b = w := by
  have := h.2
  rw [Nat.zero_add, hs, ByteArray.extract_zero_size] at this
  exact this

theorem occursAt_iff_getElem {b w : ByteArray} {i : Nat} :
    OccursAt b i w ↔ ∃ hs : i + w.size ≤ b.size, ∀ k (hk : k < w.size), b[i + k] = w[k] := by
  constructor
  · rintro ⟨hs, he⟩
    refine ⟨hs, fun k hk => ?_⟩
    have hk' : k < (b.extract i (i + w.size)).size := by
      simp [ByteArray.size_extract]; omega
    rw [← ByteArray.getElem_extract hk']
    simp only [he]
  · rintro ⟨hs, hk⟩
    refine ⟨hs, ByteArray.ext_getElem (by simp [ByteArray.size_extract]; omega) fun k h1 h2 => ?_⟩
    rw [ByteArray.getElem_extract]
    exact hk k h2

/-! ## Whole-input decode -/

/-- The bytes of a value decode to it. -/
theorem decode_bytes {c : Stream α} (hc : Lawful c) (v : α) : c.decode (c.bytes v) = .ok v := by
  unfold decode
  rw [hc.get_of_occurs v _ 0 (occursAt_self _), Nat.zero_add]
  simp

/-- Canonicity: an input that decodes to `v` is exactly `bytes v`. -/
theorem eq_bytes_of_decode {c : Stream α} (hc : Lawful c) {b : ByteArray} {v : α}
    (h : c.decode b = .ok v) : b = c.bytes v := by
  unfold decode at h
  split at h
  · rename_i w j hget
    split at h
    · rename_i hj
      cases h
      obtain ⟨hj', hocc⟩ := hc.occurs_of_get hget
      exact eq_of_occursAt_zero hocc (by omega)
    · cases h
  · cases h

theorem decode_eq_ok_iff {c : Stream α} (hc : Lawful c) {b : ByteArray} {v : α} :
    c.decode b = .ok v ↔ b = c.bytes v :=
  ⟨eq_bytes_of_decode hc, fun h => h ▸ decode_bytes hc v⟩

theorem bytes_injective {c : Stream α} (hc : Lawful c) {v w : α} (h : c.bytes v = c.bytes w) : v = w := by
  have := decode_bytes hc v
  rw [h, decode_bytes hc w] at this
  cases this; rfl

/-! ## Byte-level helpers -/

@[simp] theorem size_mk (a : Array UInt8) : (ByteArray.mk a).size = a.size := rfl
@[simp] theorem getElem_mk (a : Array UInt8) (k : Nat) (h : k < (ByteArray.mk a).size) :
    (ByteArray.mk a)[k] = a[k]'h := rfl

theorem push_eq_append (buf : ByteArray) (x : UInt8) : buf.push x = buf ++ ⟨#[x]⟩ := by
  apply ByteArray.ext
  simp only [ByteArray.data_append, ByteArray.data_push, ← Array.append_singleton]

theorem bytes_of_put_eq {c : Stream α} (h : ∀ v buf, c.put v buf = buf ++ c.bytes v) (v : α) (buf : ByteArray) :
    c.put v buf = buf ++ c.bytes v := h v buf

/-! ## Fixed-width integers -/

theorem ofLE32_split (v : UInt32) :
    ofLE32 v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8 = v := by
  apply UInt32.toNat_inj.mp
  simp only [ofLE32, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_shiftRight, UInt32.toNat_toUInt8,
    UInt8.toNat_toUInt32, Nat.shiftRight_eq_div_pow]
  have := v.toNat_lt
  simp
  omega

theorem split_ofLE32 (a b c d : UInt8) :
    (ofLE32 a b c d).toUInt8 = a ∧ (ofLE32 a b c d >>> 8).toUInt8 = b ∧
    (ofLE32 a b c d >>> 16).toUInt8 = c ∧ (ofLE32 a b c d >>> 24).toUInt8 = d := by
  have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
  simp only [← UInt8.toNat_inj, ofLE32, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_shiftRight,
    UInt32.toNat_toUInt8, UInt8.toNat_toUInt32, Nat.shiftRight_eq_div_pow]
  simp
  omega

theorem ofLE64_split (v : UInt64) :
    ofLE64 v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8
      (v >>> 32).toUInt8 (v >>> 40).toUInt8 (v >>> 48).toUInt8 (v >>> 56).toUInt8 = v := by
  apply UInt64.toNat_inj.mp
  simp only [ofLE64, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_shiftRight, UInt64.toNat_toUInt8,
    UInt8.toNat_toUInt64, Nat.shiftRight_eq_div_pow]
  have := v.toNat_lt
  simp
  omega

theorem split_ofLE64 (a b c d e f g h : UInt8) :
    (ofLE64 a b c d e f g h).toUInt8 = a ∧ (ofLE64 a b c d e f g h >>> 8).toUInt8 = b ∧
    (ofLE64 a b c d e f g h >>> 16).toUInt8 = c ∧ (ofLE64 a b c d e f g h >>> 24).toUInt8 = d ∧
    (ofLE64 a b c d e f g h >>> 32).toUInt8 = e ∧ (ofLE64 a b c d e f g h >>> 40).toUInt8 = f ∧
    (ofLE64 a b c d e f g h >>> 48).toUInt8 = g ∧ (ofLE64 a b c d e f g h >>> 56).toUInt8 = h := by
  have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
  have he := e.toNat_lt; have hf := f.toNat_lt; have hg := g.toNat_lt; have hh := h.toNat_lt
  simp only [← UInt8.toNat_inj, ofLE64, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_shiftRight,
    UInt64.toNat_toUInt8, UInt8.toNat_toUInt64, Nat.shiftRight_eq_div_pow]
  simp
  omega

/-! ## Primitives are lawful -/

theorem unit_lawful : Lawful unit where
  put_eq _ buf := by simp [unit, bytes, ByteArray.append_empty]
  size_eq _ := rfl
  get_of_occurs _ b i h := by
    have := h.1
    simp only [unit, bytes, ByteArray.size_empty, Nat.add_zero] at this ⊢
    simp [this]
  occurs_of_get {b i v j} h := by
    simp only [unit] at h
    split at h
    · cases h
      exact ⟨by simp [bytes, unit], by simp [bytes, unit]; omega, by simp [bytes, unit, ByteArray.extract_same]⟩
    · cases h

@[simp] theorem u8_bytes (v : UInt8) : u8.bytes v = ⟨#[v]⟩ := rfl

theorem u8_lawful : Lawful u8 where
  put_eq v buf := push_eq_append buf v
  size_eq _ := rfl
  get_of_occurs v b i h := by
    obtain ⟨hs, hk⟩ := occursAt_iff_getElem.mp h
    have hs' : i < b.size := hs
    have h0 : b[i + 0] = v := hk 0 (by show 0 < 1; decide)
    simp only [u8, hs', ↓reduceDIte]
    rw [show b[i] = v from h0]
    rfl
  occurs_of_get {b i v j} h := by
    simp only [u8] at h
    split at h
    · rename_i hi
      cases h
      refine ⟨rfl, occursAt_iff_getElem.mpr ⟨hi, fun k hk => ?_⟩⟩
      have hk' : k < 1 := hk
      rcases k with _ | k
      · rfl
      · omega
    · cases h

@[simp] theorem u8_size (v : UInt8) : (u8.bytes v).size = 1 := rfl
@[simp] theorem u32_size (v : UInt32) : (u32.bytes v).size = 4 := rfl
@[simp] theorem u64_size (v : UInt64) : (u64.bytes v).size = 8 := rfl

@[simp] theorem u32_bytes (v : UInt32) :
    u32.bytes v = ⟨#[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]⟩ := rfl

theorem u32_lawful : Lawful u32 where
  put_eq v buf := by
    simp only [u32, push_eq_append, ByteArray.append_assoc]
    rfl
  size_eq _ := rfl
  get_of_occurs v b i h := by
    obtain ⟨hs, hk⟩ := occursAt_iff_getElem.mp h
    have hs' : i + 4 ≤ b.size := hs
    have h0 : b[i + 0] = v.toUInt8 := hk 0 (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_eq (u32_size v).symm))
    have h1 : b[i + 1] = (v >>> 8).toUInt8 := hk 1 (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_eq (u32_size v).symm))
    have h2 : b[i + 2] = (v >>> 16).toUInt8 := hk 2 (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_eq (u32_size v).symm))
    have h3 : b[i + 3] = (v >>> 24).toUInt8 := hk 3 (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_eq (u32_size v).symm))
    have h0' : b[i] = v.toUInt8 := h0
    simp only [u32, hs', ↓reduceDIte, h0', h1, h2, h3]
    rw [ofLE32_split]
    rfl
  occurs_of_get {b i v j} h := by
    simp only [u32] at h
    split at h
    · rename_i hi
      cases h
      obtain ⟨e0, e1, e2, e3⟩ := split_ofLE32 b[i] b[i+1] b[i+2] b[i+3]
      refine ⟨rfl, occursAt_iff_getElem.mpr ⟨hi, fun k hk => ?_⟩⟩
      have hk' : k < 4 := hk
      rcases k with _ | _ | _ | _ | k
      · exact e0.symm
      · exact e1.symm
      · exact e2.symm
      · exact e3.symm
      · omega
    · cases h

@[simp] theorem u64_bytes (v : UInt64) :
    u64.bytes v = ⟨#[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8,
      (v >>> 32).toUInt8, (v >>> 40).toUInt8, (v >>> 48).toUInt8, (v >>> 56).toUInt8]⟩ := rfl

theorem u64_lawful : Lawful u64 where
  put_eq v buf := by
    simp only [u64, push_eq_append, ByteArray.append_assoc]
    rfl
  size_eq _ := rfl
  get_of_occurs v b i h := by
    obtain ⟨hs, hk⟩ := occursAt_iff_getElem.mp h
    have hs' : i + 8 ≤ b.size := hs
    have h0 : b[i + 0] = v.toUInt8 := hk 0 (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_eq (u64_size v).symm))
    have h1 : b[i + 1] = (v >>> 8).toUInt8 := hk 1 (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_eq (u64_size v).symm))
    have h2 : b[i + 2] = (v >>> 16).toUInt8 := hk 2 (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_eq (u64_size v).symm))
    have h3 : b[i + 3] = (v >>> 24).toUInt8 := hk 3 (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_eq (u64_size v).symm))
    have h4 : b[i + 4] = (v >>> 32).toUInt8 := hk 4 (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_eq (u64_size v).symm))
    have h5 : b[i + 5] = (v >>> 40).toUInt8 := hk 5 (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_eq (u64_size v).symm))
    have h6 : b[i + 6] = (v >>> 48).toUInt8 := hk 6 (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_eq (u64_size v).symm))
    have h7 : b[i + 7] = (v >>> 56).toUInt8 := hk 7 (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_eq (u64_size v).symm))
    have h0' : b[i] = v.toUInt8 := h0
    simp only [u64, hs', ↓reduceDIte, h0', h1, h2, h3, h4, h5, h6, h7]
    rw [ofLE64_split]
    rfl
  occurs_of_get {b i v j} h := by
    simp only [u64] at h
    split at h
    · rename_i hi
      cases h
      obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := split_ofLE64 b[i] b[i+1] b[i+2] b[i+3] b[i+4] b[i+5] b[i+6] b[i+7]
      refine ⟨rfl, occursAt_iff_getElem.mpr ⟨hi, fun k hk => ?_⟩⟩
      have hk' : k < 8 := hk
      rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
      · exact e0.symm
      · exact e1.symm
      · exact e2.symm
      · exact e3.symm
      · exact e4.symm
      · exact e5.symm
      · exact e6.symm
      · exact e7.symm
      · omega
    · cases h

@[simp] theorem digest_bytes (d : Digest) : digest.bytes d = d.bytes := by
  simp [bytes, digest, ByteArray.empty_append]

theorem digest_lawful : Lawful digest where
  put_eq d buf := by rw [digest_bytes]; rfl
  size_eq d := by rw [digest_bytes, d.size_eq]; rfl
  get_of_occurs d b i h := by
    obtain ⟨hs, he⟩ := h
    simp only [digest_bytes, d.size_eq] at hs he ⊢
    simp only [digest, hs, ↓reduceDIte]
    cases d; simp_all
  occurs_of_get {b i v j} h := by
    simp only [digest] at h
    split at h
    · rename_i hs
      cases h
      have : (b.extract i (i + 32)).size = 32 := by simp [ByteArray.size_extract]; omega
      exact ⟨by simp [this], by simp [this]; omega, by simp [this]⟩
    · cases h

/-! ## Combinators preserve lawfulness -/

theorem product_bytes {a : Stream α} {c : Stream β} (hc : Lawful c) (v : α × β) :
    (product a c).bytes v = a.bytes v.1 ++ c.bytes v.2 := by
  simp only [bytes, product]
  rw [hc.put_eq, ← bytes, ← bytes]

theorem product_lawful {a : Stream α} {c : Stream β} (ha : Lawful a) (hc : Lawful c) :
    Lawful (product a c) where
  put_eq v buf := by
    rw [product_bytes hc]
    simp only [product]
    rw [hc.put_eq, ha.put_eq, ByteArray.append_assoc]
  size_eq v := by rw [product_bytes hc, ByteArray.size_append, ← ha.size_eq, ← hc.size_eq]; rfl
  get_of_occurs v b i h := by
    rw [product_bytes hc] at h ⊢
    obtain ⟨h1, h2⟩ := occursAt_append.mp h
    simp only [product, ha.get_of_occurs _ _ _ h1, hc.get_of_occurs _ _ _ h2, ByteArray.size_append,
      Nat.add_assoc]
  occurs_of_get {b i v j} h := by
    simp only [product] at h
    split at h
    · cases h
    · rename_i x k hx
      split at h
      · rename_i y m hy
        cases h
        obtain ⟨rfl, ox⟩ := ha.occurs_of_get hx
        obtain ⟨rfl, oy⟩ := hc.occurs_of_get hy
        rw [product_bytes hc]
        exact ⟨by simp [ByteArray.size_append, Nat.add_assoc], occursAt_append.mpr ⟨ox, oy⟩⟩
      · cases h

theorem refine_bytes (name : String) (c : Stream α) (accept : α → Option β) (back : β → α) (v : β) :
    (refine name c accept back).bytes v = c.bytes (back v) := rfl

theorem refine_lawful {c : Stream α} (hc : Lawful c) (name : String) {accept : α → Option β} {back : β → α}
    (accept_back : ∀ y, accept (back y) = some y) (back_accept : ∀ x y, accept x = some y → back y = x) :
    Lawful (refine name c accept back) where
  put_eq v buf := by simp only [refine]; exact hc.put_eq _ _
  size_eq v := hc.size_eq (back v)
  get_of_occurs v b i h := by
    rw [refine_bytes] at h ⊢
    simp [refine, hc.get_of_occurs _ _ _ h, accept_back]
  occurs_of_get {b i v j} h := by
    simp only [refine] at h
    split at h
    · cases h
    · rename_i x k hx
      split at h
      · rename_i y hy
        cases h
        rw [refine_bytes, back_accept _ _ hy]
        exact hc.occurs_of_get hx
      · cases h

theorem oneOf_lawful (codes : Array UInt8) : Lawful (oneOf codes) where
  put_eq v buf := push_eq_append buf v.val
  size_eq _ := rfl
  get_of_occurs v b i h := by
    have g := u8_lawful.get_of_occurs v.val b i h
    simp only [oneOf, g, v.2, ↓reduceDIte]
    rfl
  occurs_of_get {b i v j} h := by
    simp only [oneOf] at h
    split at h
    · cases h
    · rename_i t k hk
      split at h
      · cases h
        exact u8_lawful.occurs_of_get hk
      · cases h

theorem within_lawful {c : Stream α} (hc : Lawful c) (limit : Nat) : Lawful (within limit c) where
  put_eq v buf := hc.put_eq v.val buf
  size_eq v := hc.size_eq v.val
  get_of_occurs v b i h := by
    have g := hc.get_of_occurs v.val b i h
    simp only [within, g, v.2, ↓reduceDIte]
    rfl
  occurs_of_get {b i v j} h := by
    simp only [within] at h
    split at h
    · cases h
    · rename_i x k hx
      split at h
      · cases h
        exact hc.occurs_of_get hx
      · cases h

theorem bool_lawful : Lawful bool :=
  refine_lawful u8_lawful "bool" (fun y => by cases y <;> rfl) (fun x y h => by
    by_cases h0 : x = 0
    · simp [h0] at h; subst h; simp [h0]
    · by_cases h1 : x = 1
      · simp [h1] at h; subst h; simp [h1]
      · simp [h0, h1] at h)

theorem framed_bytes {c : Stream α} (hc : Lawful c) (tag : Digest) (v : α) :
    (framed tag c).bytes v = tag.bytes ++ c.bytes v := by
  simp only [bytes, framed]
  rw [hc.put_eq, ByteArray.empty_append, ← bytes]

theorem framed_lawful {c : Stream α} (hc : Lawful c) (tag : Digest) : Lawful (framed tag c) where
  put_eq v buf := by
    rw [framed_bytes hc]
    simp only [framed]
    rw [hc.put_eq, ByteArray.append_assoc]
  size_eq v := by rw [framed_bytes hc, ByteArray.size_append, tag.size_eq, ← hc.size_eq]; rfl
  get_of_occurs v b i h := by
    rw [framed_bytes hc] at h ⊢
    obtain ⟨⟨hs, he⟩, h2⟩ := occursAt_append.mp h
    rw [tag.size_eq] at hs he h2
    simp only [framed, hs, he, ↓reduceIte, hc.get_of_occurs _ _ _ h2, ByteArray.size_append, tag.size_eq,
      Nat.add_assoc]
  occurs_of_get {b i v j} h := by
    simp only [framed] at h
    split at h
    · rename_i hs
      split at h
      · rename_i he
        obtain ⟨rfl, oc⟩ := hc.occurs_of_get h
        rw [framed_bytes hc]
        refine ⟨by simp [ByteArray.size_append, tag.size_eq, Nat.add_assoc], occursAt_append.mpr ⟨?_, ?_⟩⟩
        · exact ⟨by rw [tag.size_eq]; exact hs, by rw [tag.size_eq]; exact he⟩
        · rw [tag.size_eq]; exact oc
      · cases h
    · cases h

theorem option_bytes_none (c : Stream α) : (option c).bytes none = u8.bytes 0 := rfl

theorem option_bytes_some {c : Stream α} (hc : Lawful c) (v : α) :
    (option c).bytes (some v) = u8.bytes 1 ++ c.bytes v := by
  simp only [bytes, option]
  rw [hc.put_eq]; rfl

theorem option_lawful {c : Stream α} (hc : Lawful c) : Lawful (option c) where
  put_eq v buf := by
    cases v with
    | none => rw [option_bytes_none]; exact u8_lawful.put_eq 0 buf
    | some v =>
      rw [option_bytes_some hc]
      simp only [option]
      rw [hc.put_eq, push_eq_append, ByteArray.append_assoc]; rfl
  size_eq v := by
    cases v with
    | none => rfl
    | some v => rw [option_bytes_some hc, ByteArray.size_append, ← hc.size_eq]; rfl
  get_of_occurs v b i h := by
    cases v with
    | none =>
      rw [option_bytes_none] at h ⊢
      simp [option, u8_lawful.get_of_occurs _ _ _ h]
    | some v =>
      rw [option_bytes_some hc] at h ⊢
      obtain ⟨h1, h2⟩ := occursAt_append.mp h
      have h2' : OccursAt b (i + 1) (c.bytes v) := h2
      simp [option, u8_lawful.get_of_occurs _ _ _ h1, hc.get_of_occurs _ _ _ h2', ByteArray.size_append,
        Nat.add_assoc]
  occurs_of_get {b i v j} h := by
    simp only [option] at h
    split at h
    · cases h
    · rename_i k hk
      cases h
      obtain ⟨rfl, o⟩ := u8_lawful.occurs_of_get hk
      exact ⟨rfl, o⟩
    · rename_i k hk
      split at h
      · rename_i w m hw
        cases h
        obtain ⟨rfl, o1⟩ := u8_lawful.occurs_of_get hk
        obtain ⟨rfl, o2⟩ := hc.occurs_of_get hw
        rw [option_bytes_some hc]
        exact ⟨by simp [ByteArray.size_append, Nat.add_assoc], occursAt_append.mpr ⟨o1, o2⟩⟩
      · cases h
    · cases h

theorem sum_bytes_inl {a : Stream α} {c : Stream β} (ha : Lawful a) (v : α) :
    (sum a c).bytes (.inl v) = u8.bytes 0 ++ a.bytes v := by
  simp only [bytes, sum]
  rw [ha.put_eq]; rfl

theorem sum_bytes_inr {a : Stream α} {c : Stream β} (hc : Lawful c) (v : β) :
    (sum a c).bytes (.inr v) = u8.bytes 1 ++ c.bytes v := by
  simp only [bytes, sum]
  rw [hc.put_eq]; rfl

theorem sum_lawful {a : Stream α} {c : Stream β} (ha : Lawful a) (hc : Lawful c) : Lawful (sum a c) where
  put_eq v buf := by
    cases v with
    | inl v =>
      rw [sum_bytes_inl ha]
      simp only [sum]
      rw [ha.put_eq, push_eq_append, ByteArray.append_assoc]; rfl
    | inr v =>
      rw [sum_bytes_inr hc]
      simp only [sum]
      rw [hc.put_eq, push_eq_append, ByteArray.append_assoc]; rfl
  size_eq v := by
    cases v with
    | inl v => rw [sum_bytes_inl ha, ByteArray.size_append, ← ha.size_eq]; rfl
    | inr v => rw [sum_bytes_inr hc, ByteArray.size_append, ← hc.size_eq]; rfl
  get_of_occurs v b i h := by
    cases v with
    | inl v =>
      rw [sum_bytes_inl ha] at h ⊢
      obtain ⟨h1, h2⟩ := occursAt_append.mp h
      have h2' : OccursAt b (i + 1) (a.bytes v) := h2
      simp [sum, u8_lawful.get_of_occurs _ _ _ h1, ha.get_of_occurs _ _ _ h2', ByteArray.size_append,
        Nat.add_assoc]
    | inr v =>
      rw [sum_bytes_inr hc] at h ⊢
      obtain ⟨h1, h2⟩ := occursAt_append.mp h
      have h2' : OccursAt b (i + 1) (c.bytes v) := h2
      simp [sum, u8_lawful.get_of_occurs _ _ _ h1, hc.get_of_occurs _ _ _ h2', ByteArray.size_append,
        Nat.add_assoc]
  occurs_of_get {b i v j} h := by
    simp only [sum] at h
    split at h
    · cases h
    · rename_i k hk
      split at h
      · rename_i w m hw
        cases h
        obtain ⟨rfl, o1⟩ := u8_lawful.occurs_of_get hk
        obtain ⟨rfl, o2⟩ := ha.occurs_of_get hw
        rw [sum_bytes_inl ha]
        exact ⟨by simp [ByteArray.size_append, Nat.add_assoc], occursAt_append.mpr ⟨o1, o2⟩⟩
      · cases h
    · rename_i k hk
      split at h
      · rename_i w m hw
        cases h
        obtain ⟨rfl, o1⟩ := u8_lawful.occurs_of_get hk
        obtain ⟨rfl, o2⟩ := hc.occurs_of_get hw
        rw [sum_bytes_inr hc]
        exact ⟨by simp [ByteArray.size_append, Nat.add_assoc], occursAt_append.mpr ⟨o1, o2⟩⟩
      · cases h
    · cases h

theorem bytesOf_bytes (max : Nat) (fits : max < 2 ^ 32) (v : Bytes max) :
    (bytesOf max fits).bytes v = u32.bytes (UInt32.ofNat v.val.size) ++ v.val := by
  show u32.put _ ByteArray.empty ++ v.val = _
  rw [u32_lawful.put_eq, ByteArray.empty_append]

theorem bytesOf_lawful (max : Nat) (fits : max < 2 ^ 32) : Lawful (bytesOf max fits) where
  put_eq v buf := by
    rw [bytesOf_bytes]
    simp only [bytesOf]
    rw [u32_lawful.put_eq, ByteArray.append_assoc]
  size_eq v := by rw [bytesOf_bytes, ByteArray.size_append]; rfl
  get_of_occurs v b i h := by
    rw [bytesOf_bytes] at h ⊢
    obtain ⟨h1, ⟨hs, he⟩⟩ := occursAt_append.mp h
    have hn : (UInt32.ofNat v.val.size).toNat = v.val.size :=
      UInt32.toNat_ofNat_of_lt' (by have := v.2; simp only [UInt32.size]; omega)
    rw [u32_size] at hs he
    have hget := u32_lawful.get_of_occurs _ _ _ h1
    rw [u32_size] at hget
    simp only [bytesOf, hget, hn, v.2, ↓reduceDIte, ByteArray.size_append, u32_size, ← Nat.add_assoc, hs, he]
  occurs_of_get {b i v j} h := by
    simp only [bytesOf] at h
    split at h
    · cases h
    · rename_i n k hk
      split at h
      · rename_i hmax
        split at h
        · rename_i hb
          cases h
          obtain ⟨rfl, o1⟩ := u32_lawful.occurs_of_get hk
          simp only [u32_size] at hb ⊢
          have hsz : (b.extract (i + 4) (i + 4 + n.toNat)).size = n.toNat := by
            rw [ByteArray.size_extract]; omega
          rw [bytesOf_bytes]
          simp only [hsz, UInt32.ofNat_toNat]
          refine ⟨by simp [ByteArray.size_append, hsz]; omega, occursAt_append.mpr ⟨o1, ?_⟩⟩
          simp only [u32_size]
          exact ⟨by rw [hsz]; exact hb, by rw [hsz]⟩
        · cases h
      · cases h

theorem foldl_put {c : Stream α} (hc : Lawful c) (l : List α) (buf : ByteArray) :
    l.foldl (fun out x => c.put x out) buf = buf ++ manyBytes c l := by
  induction l generalizing buf with
  | nil => simp [manyBytes, ByteArray.append_empty]
  | cons x l ih =>
    simp only [manyBytes, List.foldl_cons]
    rw [ih, ih (c.put x ByteArray.empty), hc.put_eq, hc.put_eq, ByteArray.empty_append,
      ByteArray.append_assoc]

theorem manyBytes_cons {c : Stream α} (hc : Lawful c) (x : α) (l : List α) :
    manyBytes c (x :: l) = c.bytes x ++ manyBytes c l := by
  simp only [manyBytes, List.foldl_cons]
  rw [foldl_put hc]; rfl

theorem getMany_of_occurs {c : Stream α} (hc : Lawful c) (l : List α) (b : ByteArray) (i : Nat)
    (acc : Array α) (h : OccursAt b i (manyBytes c l)) :
    getMany c b l.length i acc = .ok (acc ++ l.toArray, i + (manyBytes c l).size) := by
  induction l generalizing i acc with
  | nil => simp [getMany, manyBytes]
  | cons x l ih =>
    rw [manyBytes_cons hc] at h ⊢
    obtain ⟨h1, h2⟩ := occursAt_append.mp h
    simp only [getMany, hc.get_of_occurs _ _ _ h1]
    rw [ih _ _ h2]
    simp [ByteArray.size_append, Nat.add_assoc]

theorem occurs_of_getMany {c : Stream α} (hc : Lawful c) (n : Nat) (b : ByteArray) (i : Nat)
    (acc a : Array α) (k : Nat) (hi : i ≤ b.size) (h : getMany c b n i acc = .ok (a, k)) :
    ∃ l : List α, l.length = n ∧ a = acc ++ l.toArray ∧ k = i + (manyBytes c l).size ∧
      OccursAt b i (manyBytes c l) := by
  induction n generalizing i acc with
  | zero =>
    simp only [getMany, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, by simp, by simp [manyBytes],
      ⟨by simp [manyBytes]; omega, by simp [manyBytes, ByteArray.extract_same]⟩⟩
  | succ n ih =>
    simp only [getMany] at h
    split at h
    · rename_i x j hx
      obtain ⟨rfl, o1⟩ := hc.occurs_of_get hx
      obtain ⟨l, hl, rfl, rfl, o2⟩ := ih _ _ (by have := o1.1; omega) h
      refine ⟨x :: l, by simp [hl], by simp, ?_, ?_⟩
      · rw [manyBytes_cons hc, ByteArray.size_append, Nat.add_assoc]
      · rw [manyBytes_cons hc]; exact occursAt_append.mpr ⟨o1, o2⟩
    · cases h

theorem foldl_size {c : Stream α} (hc : Lawful c) (l : List α) (k : Nat) :
    l.foldl (fun n x => n + c.size x) k = k + (manyBytes c l).size := by
  induction l generalizing k with
  | nil => simp [manyBytes]
  | cons x l ih => rw [List.foldl_cons, ih, manyBytes_cons hc, ByteArray.size_append, hc.size_eq, Nat.add_assoc]

theorem array_bytes {c : Stream α} (hc : Lawful c) (max : Nat) (fits : max < 2 ^ 32) (v : Bounded max α) :
    (array max c fits).bytes v = u32.bytes (UInt32.ofNat v.val.size) ++ manyBytes c v.val.toList := by
  show v.val.foldl _ (u32.put _ ByteArray.empty) = _
  rw [← Array.foldl_toList, foldl_put hc, u32_lawful.put_eq, ByteArray.empty_append]

theorem array_lawful {c : Stream α} (hc : Lawful c) (max : Nat) (fits : max < 2 ^ 32) :
    Lawful (array max c fits) where
  put_eq v buf := by
    rw [array_bytes hc]
    show v.val.foldl _ (u32.put _ buf) = _
    rw [← Array.foldl_toList, foldl_put hc, u32_lawful.put_eq, ByteArray.append_assoc]
  size_eq v := by
    rw [array_bytes hc, ByteArray.size_append, u32_size, ← foldl_size hc]
    show Array.foldl _ 4 v.val = _
    rw [← Array.foldl_toList]
  get_of_occurs v b i h := by
    rw [array_bytes hc] at h ⊢
    obtain ⟨h1, h2⟩ := occursAt_append.mp h
    have hn : (UInt32.ofNat v.val.size).toNat = v.val.toList.length := by
      rw [Array.length_toList]
      exact UInt32.toNat_ofNat_of_lt' (by have := v.2; simp only [UInt32.size]; omega)
    have hget := u32_lawful.get_of_occurs _ _ _ h1
    rw [u32_size] at hget h2
    have hmax : v.val.toList.length ≤ max := by rw [Array.length_toList]; exact v.2
    have hmany := getMany_of_occurs hc v.val.toList b (i + 4) (Array.emptyWithCapacity v.val.toList.length) h2
    simp only [Array.emptyWithCapacity_eq, Array.empty_append, Array.toArray_toList] at hmany
    simp only [array, hget, hn, hmax, ↓reduceIte, Array.emptyWithCapacity_eq, hmany, v.2, ↓reduceDIte,
      ByteArray.size_append, u32_size, Nat.add_assoc]
  occurs_of_get {b i v j} h := by
    simp only [array] at h
    split at h
    · cases h
    · rename_i n k hk
      split at h
      · rename_i hmax
        split at h
        · rename_i a m hm
          split at h
          · rename_i ha
            cases h
            obtain ⟨rfl, o1⟩ := u32_lawful.occurs_of_get hk
            obtain ⟨l, hl, rfl, rfl, o2⟩ := occurs_of_getMany hc _ _ _ _ _ _ (by have := o1.1; omega) hm
            simp only [Array.emptyWithCapacity_eq, Array.empty_append] at ha ⊢
            rw [array_bytes hc]
            have hsz : UInt32.ofNat l.toArray.size = n := by
              simp only [List.size_toArray, hl, UInt32.ofNat_toNat]
            simp only [hsz]
            exact ⟨by simp [ByteArray.size_append, Nat.add_assoc], occursAt_append.mpr ⟨o1, o2⟩⟩
          · cases h
        · cases h
      · cases h

theorem tagged_bytes {σ : Type} {F : σ → Type} {all : List σ} {code : σ → UInt8}
    {ofCode? : UInt8 → Option σ} {c : (s : σ) → Stream (F s)} (hc : ∀ s, Lawful (c s))
    (v : (s : σ) × F s) :
    (tagged all code ofCode? c).bytes v = u8.bytes (code v.1) ++ (c v.1).bytes v.2 := by
  simp only [bytes, tagged]
  rw [(hc v.1).put_eq]; rfl

theorem tagged_lawful {σ : Type} {F : σ → Type} (all : List σ) {code : σ → UInt8}
    {ofCode? : UInt8 → Option σ} {c : (s : σ) → Stream (F s)} (hc : ∀ s, Lawful (c s))
    (of_code : ∀ s, ofCode? (code s) = some s) (code_of : ∀ t s, ofCode? t = some s → code s = t) :
    Lawful (tagged all code ofCode? c) where
  put_eq v buf := by
    rw [tagged_bytes hc]
    simp only [tagged]
    rw [(hc v.1).put_eq, push_eq_append, ByteArray.append_assoc]; rfl
  size_eq v := by rw [tagged_bytes hc, ByteArray.size_append, ← (hc v.1).size_eq]; rfl
  get_of_occurs v b i h := by
    rw [tagged_bytes hc] at h ⊢
    obtain ⟨h1, h2⟩ := occursAt_append.mp h
    have h2' : OccursAt b (i + 1) ((c v.1).bytes v.2) := h2
    simp [tagged, u8_lawful.get_of_occurs _ _ _ h1, of_code, (hc v.1).get_of_occurs _ _ _ h2',
      ByteArray.size_append, Nat.add_assoc]
  occurs_of_get {b i v j} h := by
    simp only [tagged] at h
    split at h
    · cases h
    · rename_i t k hk
      split at h
      · cases h
      · rename_i s hs
        split at h
        · rename_i w m hw
          cases h
          obtain ⟨rfl, o1⟩ := u8_lawful.occurs_of_get hk
          obtain ⟨rfl, o2⟩ := (hc s).occurs_of_get hw
          rw [tagged_bytes hc]
          simp only [code_of _ _ hs]
          exact ⟨by simp [ByteArray.size_append, Nat.add_assoc], occursAt_append.mpr ⟨o1, o2⟩⟩
        · cases h

theorem finOf?_finCode {n : Nat} (hn : n ≤ 256) (s : Fin n) : finOf? n (finCode s) = some s := by
  have h : (UInt8.ofNat s.val).toNat = s.val := UInt8.toNat_ofNat_of_lt' (by have := s.isLt; simp only [UInt8.size]; omega)
  simp [finOf?, finCode, h]

theorem finCode_of {n : Nat} (t : UInt8) (s : Fin n) (h : finOf? n t = some s) : finCode s = t := by
  unfold finOf? at h
  split at h
  · cases h; simp [finCode]
  · cases h

theorem choice_lawful (n : Nat) (hn : n ≤ 256) {F : Fin n → Type} {c : (s : Fin n) → Stream (F s)}
    (hc : ∀ s, Lawful (c s)) : Lawful (choice n c) :=
  tagged_lawful _ hc (finOf?_finCode hn) finCode_of

end Nanodregg.Codec.Stream
