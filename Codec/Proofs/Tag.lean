import Codec.Tag
import Codec.Proofs.Varint

/-! # A shape's bytes determine the shape

`Shape.put` appends (`Shape.put_eq`) and is prefix-free (`Shape.put_prefix`): if two shapes' bytes,
each followed by anything, are equal, the shapes are equal and so are the remainders. So two
different shapes never share bytes, and two different codecs share a `Tag.of` only through a cSHAKE256
collision (`Tag.of_inj`). -/

namespace Nanodregg.Codec

open Stream

theorem head_inj {a c : UInt8} {u v : ByteArray} (h : (ByteArray.mk #[a]) ++ u = (ByteArray.mk #[c]) ++ v) :
    a = c ∧ u = v := by
  have hl := ByteArray.append_inj_left h rfl
  refine ⟨?_, (ByteArray.append_right_inj _).mp (hl ▸ h)⟩
  have := congrArg (fun b : ByteArray => b.data) hl
  simpa using this

theorem split_sized {u v x y : ByteArray} (hs : u.size = v.size) (h : u ++ x = v ++ y) : u = v ∧ x = y := by
  have hl := ByteArray.append_inj_left h hs
  exact ⟨hl, (ByteArray.append_right_inj _).mp (hl ▸ h)⟩

theorem varint_prefix : ∀ (m n : Nat) (x y : ByteArray), Stream.varint.bytes m ++ x = Stream.varint.bytes n ++ y → m = n ∧ x = y := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro n x y h
    by_cases hm : m < 128 <;> by_cases hn : n < 128
    · rw [varint_bytes_small hm, varint_bytes_small hn] at h
      obtain ⟨hb, hx⟩ := head_inj h
      refine ⟨?_, hx⟩
      have := congrArg UInt8.toNat hb
      rwa [UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega), UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega)] at this
    · rw [varint_bytes_small hm, varint_bytes_large hn, ByteArray.append_assoc] at h
      have := congrArg UInt8.toNat (head_inj h).1
      rw [UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega), UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega)] at this
      omega
    · rw [varint_bytes_large hm, varint_bytes_small hn, ByteArray.append_assoc] at h
      have := congrArg UInt8.toNat (head_inj h).1
      rw [UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega), UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega)] at this
      omega
    · rw [varint_bytes_large hm, varint_bytes_large hn, ByteArray.append_assoc, ByteArray.append_assoc] at h
      obtain ⟨hb, hr⟩ := head_inj h
      have := congrArg UInt8.toNat hb
      rw [UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega), UInt8.toNat_ofNat_of_lt' (by simp [UInt8.size]; omega)] at this
      obtain ⟨hq, hx⟩ := ih (m / 128) (by omega) (n / 128) x y hr
      exact ⟨by omega, hx⟩

mutual
theorem Shape.put_eq : ∀ (s : Shape) (b : ByteArray), s.put b = b ++ s.put ByteArray.empty
  | .unit, b | .u8, b | .u32, b | .u64, b | .varint, b | .digest, b | .u16, b => by
    simp only [Shape.put, push_eq_append, ByteArray.empty_append]
  | .bytes max, b | .oneOf _, b | .bytes8 max, b => by
    simp only [Shape.put]
    rw [putVarint_eq _ (b.push _), putVarint_eq _ (ByteArray.empty.push _), push_eq_append, push_eq_append,
      ByteArray.empty_append]
    simp only [ByteArray.append_assoc]
  | .tree max depth, b => by
    simp only [Shape.put]
    rw [putVarint_eq depth, putVarint_eq max (b.push _), putVarint_eq depth (putVarint max _),
      putVarint_eq max (ByteArray.empty.push _), push_eq_append, push_eq_append, ByteArray.empty_append]
    simp only [ByteArray.append_assoc]
  | .option s, b => by
    simp only [Shape.put]; rw [Shape.put_eq s, Shape.put_eq s (ByteArray.empty.push _), push_eq_append,
      push_eq_append, ByteArray.empty_append, ByteArray.append_assoc]
  | .product x y, b | .sum x y, b => by
    simp only [Shape.put]
    rw [Shape.put_eq y, Shape.put_eq x, Shape.put_eq y (Shape.put x _), Shape.put_eq x (ByteArray.empty.push _),
      push_eq_append, push_eq_append, ByteArray.empty_append]
    simp only [ByteArray.append_assoc]
  | .array max s, b | .within max s, b => by
    simp only [Shape.put]
    rw [Shape.put_eq s, Shape.put_eq s (putVarint _ _), putVarint_eq _ (b.push _),
      putVarint_eq _ (ByteArray.empty.push _), push_eq_append, push_eq_append, ByteArray.empty_append]
    simp only [ByteArray.append_assoc]
  | .refine name s, b => by
    simp only [Shape.put]
    rw [Shape.put_eq s, Shape.put_eq s (putVarint _ _ ++ _), putVarint_eq _ (b.push _),
      putVarint_eq _ (ByteArray.empty.push _), push_eq_append, push_eq_append, ByteArray.empty_append]
    simp only [ByteArray.append_assoc]
  | .framed tag s, b => by
    simp only [Shape.put]
    rw [Shape.put_eq s, Shape.put_eq s (ByteArray.empty.push _ ++ _), push_eq_append, push_eq_append,
      ByteArray.empty_append]
    simp only [ByteArray.append_assoc]
  | .tagged cases, b => by
    simp only [Shape.put]
    rw [Shape.putCases_eq cases, Shape.putCases_eq cases (putVarint _ _), putVarint_eq _ (b.push _),
      putVarint_eq _ (ByteArray.empty.push _), push_eq_append, push_eq_append, ByteArray.empty_append]
    simp only [ByteArray.append_assoc]

theorem Shape.putCases_eq : ∀ (cases : List (UInt8 × Shape)) (b : ByteArray),
    Shape.putCases cases b = b ++ Shape.putCases cases ByteArray.empty
  | [], b => by simp [Shape.putCases, ByteArray.append_empty]
  | (code, s) :: rest, b => by
    simp only [Shape.putCases]
    rw [Shape.putCases_eq rest, Shape.putCases_eq rest (s.put _), Shape.put_eq s, Shape.put_eq s (ByteArray.empty.push _),
      push_eq_append, push_eq_append, ByteArray.empty_append]
    simp only [ByteArray.append_assoc]
end

/-! ## Prefix-freeness -/

private def Shape.code : Shape → UInt8
  | .unit => 0 | .u8 => 1 | .u32 => 2 | .u64 => 3 | .varint => 4 | .digest => 5 | .bytes _ => 6
  | .option _ => 7 | .product _ _ => 8 | .sum _ _ => 9 | .array _ _ => 10 | .refine _ _ => 11
  | .framed _ _ => 12 | .tagged _ => 13 | .tree _ _ => 14 | .oneOf _ => 15 | .within _ _ => 16
  | .bytes8 _ => 17 | .u16 => 18

private def Shape.tail : Shape → ByteArray
  | .bytes m | .bytes8 m => Stream.varint.bytes m
  | .option s => s.put ByteArray.empty
  | .product x y | .sum x y => x.put ByteArray.empty ++ y.put ByteArray.empty
  | .array m s | .within m s => Stream.varint.bytes m ++ s.put ByteArray.empty
  | .refine name s => Stream.varint.bytes name.toUTF8.size ++ name.toUTF8 ++ s.put ByteArray.empty
  | .framed tag s => tag.bytes ++ s.put ByteArray.empty
  | .tagged cs => Stream.varint.bytes cs.length ++ Shape.putCases cs ByteArray.empty
  | .tree m d => Stream.varint.bytes m ++ Stream.varint.bytes d
  | .oneOf codes => Stream.varint.bytes codes.size ++ ⟨codes⟩
  | _ => ByteArray.empty

private theorem Shape.put_cons (s : Shape) : s.put ByteArray.empty = ⟨#[s.code]⟩ ++ s.tail := by
  have pv : ∀ n b, putVarint n b = b ++ Stream.varint.bytes n := fun n b => putVarint_eq n b
  have e1 : ∀ k : UInt8, ByteArray.empty.push k = ⟨#[k]⟩ := fun k => rfl
  cases s with
  | unit | u8 | u32 | u64 | varint | digest | u16 => rfl
  | bytes m | bytes8 m => simp only [Shape.put, Shape.code, Shape.tail, pv, e1]
  | option x => simp only [Shape.put, Shape.code, Shape.tail, e1]; rw [Shape.put_eq]
  | product x y | sum x y =>
    simp only [Shape.put, Shape.code, Shape.tail, e1]; rw [Shape.put_eq y, Shape.put_eq x, ByteArray.append_assoc]
  | array m x | within m x =>
    simp only [Shape.put, Shape.code, Shape.tail, e1]; rw [Shape.put_eq x, pv, ByteArray.append_assoc]
  | refine name x =>
    simp only [Shape.put, Shape.code, Shape.tail, e1]; rw [Shape.put_eq x, pv]; simp only [ByteArray.append_assoc]
  | framed tag x => simp only [Shape.put, Shape.code, Shape.tail, e1]; rw [Shape.put_eq x, ByteArray.append_assoc]
  | tagged cs => simp only [Shape.put, Shape.code, Shape.tail, e1]; rw [Shape.putCases_eq, pv, ByteArray.append_assoc]
  | tree m d => simp only [Shape.put, Shape.code, Shape.tail, e1]; rw [pv, pv, ByteArray.append_assoc]
  | oneOf codes => simp only [Shape.put, Shape.code, Shape.tail, e1]; rw [pv, ByteArray.append_assoc]

private theorem putCases_cons (c : UInt8) (s : Shape) (cs : List (UInt8 × Shape)) :
    Shape.putCases ((c, s) :: cs) ByteArray.empty =
      ⟨#[c]⟩ ++ s.put ByteArray.empty ++ Shape.putCases cs ByteArray.empty := by
  simp only [Shape.putCases]
  rw [Shape.putCases_eq, Shape.put_eq]; rfl

private theorem digest_ext {a b : Digest} (h : a.bytes = b.bytes) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

mutual
theorem Shape.put_prefix : ∀ (s t : Shape) (x y : ByteArray),
    s.put ByteArray.empty ++ x = t.put ByteArray.empty ++ y → s = t ∧ x = y
  | s, t, x, y, h => by
    rw [Shape.put_cons s, Shape.put_cons t, ByteArray.append_assoc, ByteArray.append_assoc] at h
    obtain ⟨hc, hr⟩ := head_inj h
    cases s <;> cases t <;> (try (exfalso; simp only [Shape.code] at hc; revert hc; decide)) <;>
      simp only [Shape.tail, ByteArray.empty_append, ByteArray.append_assoc] at hr
    -- unit u8 u32 u64 varint digest
    any_goals (exact ⟨rfl, hr⟩)
    -- bytes
    · obtain ⟨rfl, hx⟩ := varint_prefix _ _ _ _ hr; exact ⟨rfl, hx⟩
    -- option
    · obtain ⟨rfl, hx⟩ := Shape.put_prefix _ _ _ _ hr; exact ⟨rfl, hx⟩
    -- product
    · obtain ⟨rfl, h2⟩ := Shape.put_prefix _ _ _ _ hr
      obtain ⟨rfl, hx⟩ := Shape.put_prefix _ _ _ _ h2; exact ⟨rfl, hx⟩
    -- sum
    · obtain ⟨rfl, h2⟩ := Shape.put_prefix _ _ _ _ hr
      obtain ⟨rfl, hx⟩ := Shape.put_prefix _ _ _ _ h2; exact ⟨rfl, hx⟩
    -- array
    · obtain ⟨rfl, h2⟩ := varint_prefix _ _ _ _ hr
      obtain ⟨rfl, hx⟩ := Shape.put_prefix _ _ _ _ h2; exact ⟨rfl, hx⟩
    -- refine
    · rename_i n1 s1 n2 s2
      obtain ⟨hl, h2⟩ := varint_prefix _ _ _ _ hr
      obtain ⟨hn, h3⟩ := split_sized hl h2
      obtain ⟨rfl, hx⟩ := Shape.put_prefix _ _ _ _ h3
      exact ⟨by rw [String.toByteArray_inj.mp hn], hx⟩
    -- framed
    · rename_i t1 s1 t2 s2
      obtain ⟨ht, h2⟩ := split_sized (by rw [t1.size_eq, t2.size_eq]) hr
      obtain ⟨rfl, hx⟩ := Shape.put_prefix _ _ _ _ h2
      exact ⟨by rw [digest_ext ht], hx⟩
    -- tagged
    · obtain ⟨hl, h2⟩ := varint_prefix _ _ _ _ hr
      obtain ⟨rfl, hx⟩ := Shape.putCases_prefix _ _ _ _ hl h2; exact ⟨rfl, hx⟩
    -- tree
    · obtain ⟨rfl, h2⟩ := varint_prefix _ _ _ _ hr
      obtain ⟨rfl, hx⟩ := varint_prefix _ _ _ _ h2; exact ⟨rfl, hx⟩
    -- oneOf
    · rename_i c1 c2
      obtain ⟨hl, h2⟩ := varint_prefix _ _ _ _ hr
      obtain ⟨hcs, hx⟩ := split_sized (u := ⟨c1⟩) (v := ⟨c2⟩) hl h2
      exact ⟨by cases hcs; rfl, hx⟩
    -- within
    · obtain ⟨rfl, h2⟩ := varint_prefix _ _ _ _ hr
      obtain ⟨rfl, hx⟩ := Shape.put_prefix _ _ _ _ h2; exact ⟨rfl, hx⟩
    -- bytes8
    · obtain ⟨rfl, hx⟩ := varint_prefix _ _ _ _ hr; exact ⟨rfl, hx⟩

theorem Shape.putCases_prefix : ∀ (cs ds : List (UInt8 × Shape)) (x y : ByteArray), cs.length = ds.length →
    Shape.putCases cs ByteArray.empty ++ x = Shape.putCases ds ByteArray.empty ++ y → cs = ds ∧ x = y
  | [], [], x, y, _, h => by simp only [Shape.putCases, ByteArray.empty_append] at h; exact ⟨rfl, h⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | (c, s) :: cs, (d, t) :: ds, x, y, hl, h => by
    rw [putCases_cons, putCases_cons, ByteArray.append_assoc, ByteArray.append_assoc, ByteArray.append_assoc,
      ByteArray.append_assoc] at h
    obtain ⟨rfl, h1⟩ := head_inj h
    obtain ⟨rfl, h2⟩ := Shape.put_prefix _ _ _ _ h1
    obtain ⟨rfl, hx⟩ := Shape.putCases_prefix cs ds x y (by simpa using hl) h2
    exact ⟨rfl, hx⟩
end

/-- Different shapes have different bytes. -/
theorem Shape.put_injective {s t : Shape} (h : s.put ByteArray.empty = t.put ByteArray.empty) : s = t :=
  (Shape.put_prefix s t ByteArray.empty ByteArray.empty (by rw [ByteArray.append_empty, ByteArray.append_empty, h])).1

/-- A tag's message determines the label and the shape: two codecs share a tag only if they share
both, or cSHAKE256 collides on two different messages. -/
theorem Tag.message_injective {l l' : String} {s s' : Shape} (h : Tag.message l s = Tag.message l' s') :
    l = l' ∧ s = s' := by
  unfold Tag.message at h
  rw [Shape.put_eq, Shape.put_eq _ (_ ++ _), putVarint_eq, putVarint_eq, ByteArray.empty_append,
    ByteArray.empty_append, ByteArray.append_assoc, ByteArray.append_assoc] at h
  obtain ⟨hl, h2⟩ := varint_prefix _ _ _ _ h
  obtain ⟨hu, h3⟩ := split_sized hl h2
  exact ⟨String.toByteArray_inj.mp hu, Shape.put_injective h3⟩

theorem Tag.of_eq {α β : Type} {l l' : String} {c : Stream α} {c' : Stream β} (h : Tag.of l c = Tag.of l' c') :
    (l = l' ∧ c.shape = c'.shape) ∨
      (Tag.message l c.shape ≠ Tag.message l' c'.shape ∧
        Hash.digest "nanodregg/codec/tag/v1" (Tag.message l c.shape) =
          Hash.digest "nanodregg/codec/tag/v1" (Tag.message l' c'.shape)) := by
  by_cases hm : Tag.message l c.shape = Tag.message l' c'.shape
  · exact .inl (Tag.message_injective hm)
  · exact .inr ⟨hm, h⟩

end Nanodregg.Codec
