import Codec.Kernel
import Codec.Proofs.Raw
import Codec.Proofs.Varint

/-!
# The rows codecs (KERNEL-46/48): lawful, and the kernel's own byte functions ARE their bytes

* `rowKey_lawfulOn`, `rowLeaf_lawfulOn` (the World's leaf, version and floor as u64 varints),
  `rowLeafHashed_lawfulOn` (the row pin's preimage), `rowAct_lawfulOn`, `rowTouch_lawfulOn`, `rangeRead_lawfulOn`,
  `rangePinWire_lawfulOn`: each rows codec is lawful on the values within KERNEL's wire bounds (a
  relation below 256, a key and a prefix of at most `Bounds.keyBytesMax` bytes, a value of at most
  `Bounds.valueBytesMax`, counters below 2^64).
* `rowKeyBytes_eq`, `rowLeafBytes_eq`, `rangePinBytes_eq`: KERNEL's `rowKeyBytes` (what the rows trie
  routes by), `rowLeafBytes` (what a row pin hashes) and `rangePinBytes` (what a range pin hashes) are
  the bytes of `rowKey`, `rowLeafHashed` and `rangePinWire`, at any digest codec that writes `E.bytes`.
* So each kernel function is injective on its domain and reads back (`rowKeyBytes_inj`,
  `rowKeyBytes_decode`, `rowLeafBytes_inj`, `rowLeafBytes_decode`, `rangePinBytes_inj`,
  `rangePinBytes_decode`): two rows keys with one routing are one key, two leaves with one pin preimage
  are one leaf, and two range reads with one pin preimage name one relation, width, prefix and listing
  (each row's key and leaf digest).
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Codec.Stream

variable {D : Type}

/-! ## Bytes of composite codecs over domains -/

theorem product_bytesOn {α β : Type} {Pc : β → Prop} {a : Stream α} {c : Stream β} (hc : LawfulOn Pc c)
    (x : α) (y : β) : (product a c).bytes (x, y) = a.bytes x ++ c.bytes y := by
  show c.put y (a.put x ByteArray.empty) = _
  rw [hc.put_eq]; rfl

theorem choice_bytesOn {n : Nat} {F : Fin n → Type} {c : (s : Fin n) → Stream (F s)} {P : (s : Fin n) → F s → Prop}
    (hc : ∀ s, LawfulOn (P s) (c s)) (s : Fin n) (v : F s) :
    (choice n c).bytes ⟨s, v⟩ = ⟨#[finCode s]⟩ ++ (c s).bytes v := by
  show (c s).put v (ByteArray.empty.push (finCode s)) = _
  rw [(hc s).put_eq]; rfl

/-! ## Keys -/

/-- A rows key within the wire's bounds: its parent in the digest codec's domain, its relation
below 256, a row's key at most `Bounds.keyBytesMax` bytes (KERNEL's `RowSlot.InDomain`, at `PD`). -/
def RowSlot.Fits (PD : D → Prop) : RowSlot D → Prop
  | .head p rel => PD p ∧ rel < 256
  | .row key => PD key.parent ∧ key.rel < 256 ∧ key.k.size ≤ Bounds.keyBytesMax

abbrev RowKindWireFits : (s : Fin 2) → RowKindF s → Prop
  | 0 => fun _ => True
  | 1 => fun k => k.size ≤ Bounds.keyBytesMax

theorem rowKindWire_lawfulOn : ∀ s, LawfulOn (RowKindWireFits s) (rowKindWire s)
  | 0 => unit_lawful.on
  | 1 => bytes8_lawfulOn _ (by decide)

theorem rowKey_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (RowSlot.Fits PD) (rowKey dc) := by
  unfold rowKey
  refine (refine_lawfulOn (product_lawfulOn hd (product_lawfulOn nat8_lawfulOn
    (choice_lawfulOn 2 (by decide) rowKindWire_lawfulOn))) "kernel/row-key" ?_ ?_).mono ?_ ?_
  · intro y _; cases y <;> rfl
  · intro x y h
    obtain ⟨p, rel, s, v⟩ := x
    match s, v, h with
    | 0, (), h => simp at h; subst h; rfl
    | 1, k, h => simp at h; subst h; rfl
  · intro y h
    cases y with
    | head p rel => exact ⟨h.1, h.2.1⟩
    | row k => exact ⟨h.1, h.2.1, h.2.2⟩
  · intro y h
    cases y with
    | head p rel => exact ⟨h.1, h.2, trivial⟩
    | row k => exact ⟨h.1, h.2.1, h.2.2⟩

/-- **`rowKeyBytes` is `rowKey`'s bytes**, at any digest codec that writes `E.bytes`. -/
theorem rowKeyBytes_eq {dc : Stream D} {E : Env D}
    (hb : ∀ d, dc.bytes d = E.bytes d) (s : RowSlot D) : rowKeyBytes E s = (rowKey dc).bytes s := by
  have hk := choice_bytesOn rowKindWire_lawfulOn (n := 2)
  cases s with
  | head p rel =>
    unfold rowKey; rw [refine_bytes]; dsimp only
    rw [product_bytesOn (product_lawfulOn nat8_lawfulOn (choice_lawfulOn 2 (by decide) rowKindWire_lawfulOn)),
      product_bytesOn (choice_lawfulOn 2 (by decide) rowKindWire_lawfulOn), hk, hb]
    simp only [rowKeyBytes, byte8, nat8_bytes, u8_bytes, ByteArray.append_assoc]
    rfl
  | row key =>
    unfold rowKey; rw [refine_bytes]; dsimp only
    rw [product_bytesOn (product_lawfulOn nat8_lawfulOn (choice_lawfulOn 2 (by decide) rowKindWire_lawfulOn)),
      product_bytesOn (choice_lawfulOn 2 (by decide) rowKindWire_lawfulOn), hk, hb]
    simp only [rowKeyBytes, rowsPrefix, byte8, nat8_bytes, u8_bytes, rowKindWire, ByteArray.append_assoc]
    rfl

/-- **`rowKeyBytes` is injective on the rows keys within bounds** (what the rows trie's separation
needs): two keys with one routing are one key. -/
theorem rowKeyBytes_inj {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {E : Env D}
    (hb : ∀ d, dc.bytes d = E.bytes d) {s s' : RowSlot D} (hs : RowSlot.Fits PD s) (hs' : RowSlot.Fits PD s')
    (h : rowKeyBytes E s = rowKeyBytes E s') : s = s' :=
  (rowKey_lawfulOn hd).bytes_injective hs hs' (by rw [← rowKeyBytes_eq hb, ← rowKeyBytes_eq hb, h])

/-- **A rows key's bytes read back as the key**, and only bytes of a key within bounds read as one. -/
theorem rowKeyBytes_decode {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {E : Env D}
    (hb : ∀ d, dc.bytes d = E.bytes d) {b : ByteArray} {s : RowSlot D} :
    (rowKey dc).decode b = .ok s ↔ RowSlot.Fits PD s ∧ b = rowKeyBytes E s := by
  rw [rowKeyBytes_eq hb]; exact (rowKey_lawfulOn hd).decode_eq_ok_iff

/-! ## Leaves -/

/-- A rows leaf within the wire's bounds: every counter below 2^64 (a head's floor and a row's version
included, KERNEL-54), a value of at most `Bounds.valueBytesMax` bytes. -/
def RowLeaf.Fits : RowLeaf → Prop
  | .head c s l k w _ f => c < 2 ^ 64 ∧ s < 2 ^ 64 ∧ l < 2 ^ 64 ∧ k < 2 ^ 64 ∧ w < 2 ^ 64 ∧ f < 2 ^ 64
  | .row a v u => a < 2 ^ 64 ∧ v.size ≤ Bounds.valueBytesMax ∧ u < 2 ^ 64

/-- A leaf's wire fields within bounds (the same for the World's wire and the pin's preimage: only the
spelling of the floor and the version differs). -/
abbrev RowLeafWireFits : (s : Fin 2) → RowLeafF s → Prop
  | 0 => fun v => v.1 < 2 ^ 64 ∧ v.2.1 < 2 ^ 64 ∧ v.2.2.1 < 2 ^ 64 ∧ v.2.2.2.1 < 2 ^ 64 ∧ v.2.2.2.2.1 < 2 ^ 64 ∧
      True ∧ v.2.2.2.2.2.2 < 2 ^ 64
  | 1 => fun v => v.1 < 2 ^ 64 ∧ v.2.1 < 2 ^ 64 ∧ v.2.2.size ≤ Bounds.valueBytesMax

theorem rowLeafWire_lawfulOn : ∀ s, LawfulOn (RowLeafWireFits s) (rowLeafWire s)
  | 0 => product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn
      (product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn (product_lawfulOn bool_lawful.on
        varint64_lawfulOn)))))
  | 1 => product_lawfulOn nat64_lawfulOn (product_lawfulOn varint64_lawfulOn (rawBytes_lawfulOn _ (by decide)))

theorem rowLeafHashedWire_lawfulOn : ∀ s, LawfulOn (RowLeafWireFits s) (rowLeafHashedWire s)
  | 0 => product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn
      (product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn (product_lawfulOn bool_lawful.on
        nat64_lawfulOn)))))
  | 1 => product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn (rawBytes_lawfulOn _ (by decide)))

theorem rowLeafOfWire_toWire (y : RowLeaf) : rowLeafOfWire (rowLeafToWire y) = some y := by
  cases y <;> rfl

theorem rowLeafToWire_of {x : (s : Fin 2) × RowLeafF s} {y : RowLeaf} (h : rowLeafOfWire x = some y) :
    rowLeafToWire y = x := by
  obtain ⟨s, v⟩ := x
  match s, v, h with
  | 0, (_, _, _, _, _, _, _), h => simp only [rowLeafOfWire, Option.some.injEq] at h; subst h; rfl
  | 1, (_, _, _), h => simp only [rowLeafOfWire, Option.some.injEq] at h; subst h; rfl

theorem rowLeafToWire_fits (y : RowLeaf) : RowLeafWireFits (rowLeafToWire y).1 (rowLeafToWire y).2 ↔ RowLeaf.Fits y := by
  cases y with
  | head c s l k w r f =>
    simp only [rowLeafToWire, RowLeafWireFits, RowLeaf.Fits, true_and]
  | row a v u =>
    simp only [rowLeafToWire, RowLeafWireFits, RowLeaf.Fits]
    exact ⟨fun h => ⟨h.1, h.2.2, h.2.1⟩, fun h => ⟨h.1, h.2.2, h.2.1⟩⟩

/-- **The World's rows leaf codec is lawful on the leaves within bounds**: a floor or a version is read
back only from its shortest varint, so every leaf has one spelling on the World wire. -/
theorem rowLeaf_lawfulOn : LawfulOn RowLeaf.Fits rowLeaf := by
  unfold rowLeaf
  refine (refine_lawfulOn (choice_lawfulOn 2 (by decide) rowLeafWire_lawfulOn) "kernel/row-leaf"
    (fun y _ => rowLeafOfWire_toWire y) (fun _ _ h => rowLeafToWire_of h)).mono ?_ ?_
  · intro y h; exact (rowLeafToWire_fits y).mp h
  · intro y h; exact (rowLeafToWire_fits y).mpr h

/-- **Canonicity, exact**, for the World's rows leaf. -/
theorem rowLeaf_decode_iff {b : ByteArray} {l : RowLeaf} :
    rowLeaf.decode b = .ok l ↔ RowLeaf.Fits l ∧ b = rowLeaf.bytes l :=
  rowLeaf_lawfulOn.decode_eq_ok_iff

theorem rowLeafHashed_lawfulOn : LawfulOn RowLeaf.Fits rowLeafHashed := by
  unfold rowLeafHashed
  refine (refine_lawfulOn (choice_lawfulOn 2 (by decide) rowLeafHashedWire_lawfulOn) "kernel/row-leaf-hashed"
    (fun y _ => rowLeafOfWire_toWire y) (fun _ _ h => rowLeafToWire_of h)).mono ?_ ?_
  · intro y h; exact (rowLeafToWire_fits y).mp h
  · intro y h; exact (rowLeafToWire_fits y).mpr h

/-- **`rowLeafBytes` is `rowLeafHashed`'s bytes**, for every leaf. -/
theorem rowLeafBytes_eq (l : RowLeaf) : rowLeafBytes l = rowLeafHashed.bytes l := by
  have hk := choice_bytesOn rowLeafHashedWire_lawfulOn (n := 2)
  have n64 := @nat64_lawfulOn
  cases l with
  | head c s lim k w r f =>
    unfold rowLeafHashed; rw [refine_bytes]; simp only [rowLeafToWire]
    rw [hk]; simp only [rowLeafHashedWire]
    rw [product_bytesOn (product_lawfulOn n64 (product_lawfulOn n64 (product_lawfulOn n64
        (product_lawfulOn n64 (product_lawfulOn bool_lawful.on n64))))),
      product_bytesOn (product_lawfulOn n64 (product_lawfulOn n64 (product_lawfulOn n64
        (product_lawfulOn bool_lawful.on n64)))),
      product_bytesOn (product_lawfulOn n64 (product_lawfulOn n64 (product_lawfulOn bool_lawful.on n64))),
      product_bytesOn (product_lawfulOn n64 (product_lawfulOn bool_lawful.on n64)),
      product_bytesOn (product_lawfulOn bool_lawful.on n64), product_bytesOn n64]
    cases r <;> simp only [rowLeafBytes, byte8, Stream.bool, ByteArray.append_assoc] <;> rfl
  | row a v u =>
    unfold rowLeafHashed; rw [refine_bytes]; simp only [rowLeafToWire]
    rw [hk]; simp only [rowLeafHashedWire]
    rw [product_bytesOn (product_lawfulOn n64 (rawBytes_lawfulOn _ (by decide))),
      product_bytesOn (rawBytes_lawfulOn _ (by decide))]
    simp only [rowLeafBytes, byte8, ByteArray.append_assoc]
    rfl

/-- **`rowLeafBytes` is injective on the leaves within bounds**: a row pin (`rowDigest`) binds one leaf,
its floor or version included, up to a collision of its hash. -/
theorem rowLeafBytes_inj {l l' : RowLeaf} (hl : RowLeaf.Fits l) (hl' : RowLeaf.Fits l')
    (h : rowLeafBytes l = rowLeafBytes l') : l = l' :=
  rowLeafHashed_lawfulOn.bytes_injective hl hl' (by rw [← rowLeafBytes_eq, ← rowLeafBytes_eq, h])

/-- **A leaf's pin preimage reads back as the leaf**, and only bytes of a leaf within bounds read as one. -/
theorem rowLeafBytes_decode {b : ByteArray} {l : RowLeaf} :
    rowLeafHashed.decode b = .ok l ↔ RowLeaf.Fits l ∧ b = rowLeafBytes l := by
  rw [rowLeafBytes_eq]; exact rowLeafHashed_lawfulOn.decode_eq_ok_iff

/-! ## Acts, touches, range reads -/

def RowAct.Fits : RowAct → Prop
  | .insert a v | .upsert a v => a < 2 ^ 64 ∧ v.size ≤ Bounds.valueBytesMax
  | .declare l c w _ => l < 2 ^ 64 ∧ c < 2 ^ 64 ∧ w < 2 ^ 64
  | _ => True

abbrev RowActWireFits : (s : Fin 5) → RowActF s → Prop
  | 0 => fun _ => True
  | 1 => fun v => v.1 < 2 ^ 64 ∧ v.2.size ≤ Bounds.valueBytesMax
  | 2 => fun v => v.1 < 2 ^ 64 ∧ v.2.size ≤ Bounds.valueBytesMax
  | 3 => fun _ => True
  | 4 => fun v => v.1 < 2 ^ 64 ∧ v.2.1 < 2 ^ 64 ∧ v.2.2.1 < 2 ^ 64 ∧ True

theorem rowActWire_lawfulOn : ∀ s, LawfulOn (RowActWireFits s) (rowActWire s)
  | 0 => unit_lawful.on
  | 1 => product_lawfulOn nat64_lawfulOn (rawBytes_lawfulOn _ (by decide))
  | 2 => product_lawfulOn nat64_lawfulOn (rawBytes_lawfulOn _ (by decide))
  | 3 => unit_lawful.on
  | 4 => product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn bool_lawful.on))

theorem rowAct_lawfulOn : LawfulOn RowAct.Fits rowAct := by
  unfold rowAct
  refine (refine_lawfulOn (choice_lawfulOn 5 (by decide) rowActWire_lawfulOn) "kernel/row-act" ?_ ?_).mono ?_ ?_
  · intro y _; cases y <;> rfl
  · intro x y h
    obtain ⟨s, v⟩ := x
    match s, v, h with
    | 0, (), h => simp at h; subst h; rfl
    | 1, (_, _), h => simp at h; subst h; rfl
    | 2, (_, _), h => simp at h; subst h; rfl
    | 3, (), h => simp at h; subst h; rfl
    | 4, (_, _, _, _), h => simp at h; subst h; rfl
  · intro y h; cases y <;> simp_all [RowAct.Fits, RowActWireFits]
  · intro y h; cases y <;> simp_all [RowAct.Fits, RowActWireFits]

def RowTouch.Fits (PD : D → Prop) (x : RowTouch D) : Prop :=
  RowSlot.Fits PD x.slot ∧ OptionFits PD x.seen ∧ RowAct.Fits x.act

theorem rowTouch_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (RowTouch.Fits PD) (rowTouch dc) := by
  unfold rowTouch
  refine (refine_lawfulOn (product_lawfulOn (rowKey_lawfulOn hd) (product_lawfulOn (option_lawfulOn hd) rowAct_lawfulOn))
    "kernel/row-touch" ?_ ?_).mono ?_ ?_
  · intro y _; rfl
  · intro x y h; simp at h; subst h; rfl
  · intro y h; exact h
  · intro y h; exact h

def RangeRead.Fits (PD : D → Prop) (q : RangeRead D) : Prop :=
  PD q.parent ∧ q.rel < 256 ∧ q.pre.size ≤ Bounds.keyBytesMax ∧ q.most < 2 ^ 64 ∧ PD q.seen

theorem rangeRead_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (RangeRead.Fits PD) (rangeRead dc) := by
  unfold rangeRead
  refine (refine_lawfulOn (product_lawfulOn hd (product_lawfulOn nat8_lawfulOn
    (product_lawfulOn (bytes8_lawfulOn _ (by decide)) (product_lawfulOn nat64_lawfulOn hd))))
    "kernel/range-read" ?_ ?_).mono ?_ ?_
  · intro y _; rfl
  · intro x y h; simp at h; subst h; rfl
  · intro y h; exact h
  · intro y h; exact h

/-! ## The range pin's hash input -/

/-- A range pin's input within bounds: the parent and every leaf digest in the digest codec's domain,
the relation and the width below 256, the prefix at most `Bounds.keyBytesMax` bytes, at most
`Bounds.rowsPerRelationMax` rows, each key within bounds. -/
def RangePinWire.Fits (PD : D → Prop) (x : RangePinWire D) : Prop :=
  PD x.1 ∧ x.2.1 < 256 ∧ x.2.2.1 < 256 ∧ x.2.2.2.1.size ≤ Bounds.keyBytesMax ∧ x.2.2.2.2.1 < 2 ^ 64 ∧
    (x.2.2.2.2.2.length ≤ Bounds.rowsPerRelationMax ∧ ∀ p ∈ x.2.2.2.2.2, RowSlot.Fits PD p.1 ∧ PD p.2)

theorem rangePinWire_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (RangePinWire.Fits PD) (rangePinWire dc) := by
  unfold rangePinWire
  refine (refine_lawfulOn (product_lawfulOn hd (product_lawfulOn nat8_lawfulOn (product_lawfulOn (oneOf_lawful _).on
    (product_lawfulOn nat8_lawfulOn (product_lawfulOn (bytes8_lawfulOn _ (by decide)) (product_lawfulOn nat64_lawfulOn
      (rawList_lawfulOn (product_lawfulOn (rowKey_lawfulOn hd) hd) _ (by decide))))))))
    "kernel/range-pin" ?_ ?_).mono ?_ ?_
  · intro y _; rfl
  · intro x y h
    obtain ⟨p, rel, ⟨t, ht⟩, w, pre, f, l⟩ := x
    simp at h; subst h
    have : t = 1 := by simpa using ht
    subst this; rfl
  · intro y h; exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  · intro y h; exact ⟨h.1, h.2.1, trivial, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem foldl_pin {E : Env D} {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc)
    (hb : ∀ d, dc.bytes d = E.bytes d) : ∀ (l : List (RowSlot D × RowLeaf)) (acc : ByteArray),
    l.foldl (fun acc p => acc ++ rowKeyBytes E p.1 ++ E.bytes (rowDigest E p.2)) acc =
      acc ++ manyBytes (product (rowKey dc) dc) (l.map fun q => (q.1, rowDigest E q.2))
  | [], acc => by simp [manyBytes, ByteArray.append_empty]
  | p :: l, acc => by
    rw [List.foldl_cons, foldl_pin hd hb l, List.map_cons, manyBytes_consOn (product_lawfulOn (rowKey_lawfulOn hd) hd),
      product_bytesOn hd, ← rowKeyBytes_eq hb, hb]
    simp only [ByteArray.append_assoc]

/-- **`rangePinBytes` is `rangePinWire`'s bytes**, the listing taken as each row's key and leaf digest. -/
theorem rangePinBytes_eq {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {E : Env D}
    (hb : ∀ d, dc.bytes d = E.bytes d) (parent : D) (rel width : Nat) (pre : ByteArray) (floor : Nat)
    (l : List (RowSlot D × RowLeaf)) :
    rangePinBytes E parent rel width pre floor l =
      (rangePinWire dc).bytes (parent, rel, width, pre, floor, l.map fun q => (q.1, rowDigest E q.2)) := by
  have hl := rawList_lawfulOn (product_lawfulOn (rowKey_lawfulOn hd) hd) Bounds.rowsPerRelationMax (by decide)
  have h6 := product_lawfulOn nat64_lawfulOn hl
  have h5 := product_lawfulOn (bytes8_lawfulOn Bounds.keyBytesMax (by decide)) h6
  have h4 := product_lawfulOn nat8_lawfulOn h5
  have h3 := product_lawfulOn (oneOf_lawful #[1]).on h4
  have h2 := product_lawfulOn nat8_lawfulOn h3
  unfold rangePinWire
  rw [refine_bytes, product_bytesOn h2, product_bytesOn h3, product_bytesOn h4, product_bytesOn h5, product_bytesOn h6,
    product_bytesOn hl, rawList_bytes (product_lawfulOn (rowKey_lawfulOn hd) hd), bytes8_bytes, hb]
  simp only [rangePinBytes, rowsPrefix, byte8, nat8_bytes, u8_bytes, nat32_bytes, List.length_map]
  rw [foldl_pin hd hb, ByteArray.empty_append]
  simp only [ByteArray.append_assoc]
  rfl

/-- **`rangePinBytes` is injective on range reads within bounds**: one pin preimage names one parent,
relation, width and prefix, and one listing of (key, leaf digest). -/
theorem rangePinBytes_inj {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {E : Env D}
    (hb : ∀ d, dc.bytes d = E.bytes d) {p p' : D} {rel rel' w w' : Nat} {pre pre' : ByteArray}
    {f f' : Nat} {l l' : List (RowSlot D × RowLeaf)}
    (hx : RangePinWire.Fits PD (p, rel, w, pre, f, l.map fun q => (q.1, rowDigest E q.2)))
    (hx' : RangePinWire.Fits PD (p', rel', w', pre', f', l'.map fun q => (q.1, rowDigest E q.2)))
    (h : rangePinBytes E p rel w pre f l = rangePinBytes E p' rel' w' pre' f' l') :
    p = p' ∧ rel = rel' ∧ w = w' ∧ pre = pre' ∧ f = f' ∧
      l.map (fun q => (q.1, rowDigest E q.2)) = l'.map (fun q => (q.1, rowDigest E q.2)) := by
  have := (rangePinWire_lawfulOn hd).bytes_injective hx hx'
    (by rw [← rangePinBytes_eq hd hb, ← rangePinBytes_eq hd hb, h])
  simp only [Prod.mk.injEq] at this
  exact this

/-- **A range pin's input reads back**, and only an input within bounds reads as one. -/
theorem rangePinBytes_decode {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {E : Env D}
    (hb : ∀ d, dc.bytes d = E.bytes d) (parent : D) (rel width : Nat) (pre : ByteArray) (floor : Nat)
    (l : List (RowSlot D × RowLeaf))
    (hx : RangePinWire.Fits PD (parent, rel, width, pre, floor, l.map fun q => (q.1, rowDigest E q.2))) :
    (rangePinWire dc).decode (rangePinBytes E parent rel width pre floor l) =
      .ok (parent, rel, width, pre, floor, l.map fun q => (q.1, rowDigest E q.2)) := by
  rw [rangePinBytes_eq hd hb]; exact (rangePinWire_lawfulOn hd).decode_bytes hx

end Nanodregg.Codec.Kernel
