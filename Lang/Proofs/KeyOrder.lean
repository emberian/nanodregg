import Codec.Proofs.Order
import Lang.Proofs.Rel
import Kernel.Proofs.RowsRange

/-!
# Lang.Proofs.KeyOrder — a relation's keys list in their declared order (LANG-57)

* `dataCmp`: at a key field's type (`keyFixed`), the data encoding of two values, each followed by
  anything, compares as `keyCmp` of the values and then the rest. A natural is `u64be`
  (`Codec.Stream.u64be_compare`); a digest's four little-endian length bytes are order-preserving
  because a digest is at most 32 < 256 bytes (shorter first); an enumeration is its arm's tag byte
  (arms ascend, so arm order is label order); a record is its fields' encodings in row order.
* `keyBytes_compare`: two keys' bytes compare exactly as the keys do in DECLARED field order
  (`keyOrder`), for any relation whose key fields are fixed-width (`checkRel` checks it at install:
  `keyBytes_compare_installed`).
* `keyBytes_keyOf`: the converse of `keyOf_keyBytes`: a key `keyOf` reads is written back by
  `keyBytes` as the same bytes (at a canonical key type, as `checkRel` requires).
* `range_keys_ascend`: a range read (`Kernel.rangeRows`, on `range_rows_exact_of`'s premises) lists
  its rows strictly ascending in declared key order; `range_keys_ascend_read`: the same for the keys the
  reader (`keyOf`, `rangeRowData`'s path) decodes, for an installed relation.
* Teeth: `key_order_1_256` (the key `(n 1)` before `(n 256)`) against `Codec.Stream.u64_misorders`
  (the little-endian wire puts 256 first); `key_order_declared_first` (declared order, not label
  order); `key_order_digest_shortlex` (a shorter digest first); on a concrete rows trie
  `queue_lists_1_first` (ring 256 written first, ring 1 listed first) against `le_queue_lists_256_first`
  (the old little-endian key bytes list 256 first); `queue_key_bytes_1_256` (bytes computed directly);
  `range_keys_ascend_read_satisfiable` (every premise met on that trie).
-/

namespace Nanodregg.Lang

open Nanodregg.Codec Nanodregg.Codec.Stream Nanodregg.Kernel

/-! ## Rows and enumerations -/

private theorem ascending_lt_mem : ∀ {k : Label} {t : Ty} {r : List (Label × Ty)},
    Row.ascending ((k, t) :: r) = true → ∀ p ∈ r, k < p.1
  | _, _, [], _, p, hp => by simp at hp
  | k, t, (k2, t2) :: r, ha, p, hp => by
    simp only [Row.ascending, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ha.1
    · exact String.lt_trans ha.1 (ascending_lt_mem ha.2 p hp)

/-- An arm of an enumeration writes no payload, and its data names a label whose first index is the
arm's. -/
private theorem arm_unit : ∀ (r : List (Label × Ty)), Row.ascending r = true → (∀ a ∈ r, a.2 = .record []) →
    ∀ (i : Fin r.length) (x : Wire.ArmAt r i),
      (Wire.armStream r i).bytes x = ByteArray.empty ∧
      ∃ ℓ, (∃ A, (ℓ, A) ∈ r) ∧ Wire.armToData r i x = .inj ℓ (.record []) ∧ r.findIdx (·.1 == ℓ) = i.val
  | [], _, _, i, _ => Fin.elim0 i
  | (k, t) :: r, ha, hall, ⟨0, _⟩, x => by
    have ht : t = .record [] := hall (k, t) (List.mem_cons_self ..)
    subst ht
    refine ⟨rfl, k, ⟨_, List.mem_cons_self ..⟩, rfl, ?_⟩
    simp [List.findIdx_cons]
  | (k, t) :: r, ha, hall, ⟨i + 1, hi⟩, x => by
    obtain ⟨hb, ℓ, ⟨A, hm⟩, hd, hf⟩ := arm_unit r (Wire.ascending_tail ha)
      (fun a h => hall a (List.mem_cons_of_mem _ h)) ⟨i, Nat.lt_of_succ_lt_succ hi⟩ x
    refine ⟨hb, ℓ, ⟨A, List.mem_cons_of_mem _ hm⟩, hd, ?_⟩
    have hlt : k < ℓ := ascending_lt_mem ha (ℓ, A) hm
    have hne : (k == ℓ) = false := by
      rw [beq_eq_false_iff_ne]; intro he; subst he; exact String.lt_irrefl _ hlt
    simp [List.findIdx_cons, hne, hf]

private theorem digest_len (n : Nat) (hn : n < 256) :
    (u32.bytes (UInt32.ofNat n)).data.toList.map UInt8.toNat = [n, 0, 0, 0] := by
  simp only [u32_bytes, List.map_cons, List.map_nil, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    UInt32.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have h1 : n % 2 ^ 32 = n := Nat.mod_eq_of_lt (by omega)
  simp [h1]
  omega

/-! ## The encoding is order-preserving at a key field's type -/

mutual
theorem dataCmp : ∀ (T : Ty), keyFixed T = true → Wire.tyWire T = true → T.wf = true →
    ∀ (x y : Wire.DataAt T) (s t : List UInt8),
      compare (((Wire.dataStream T).bytes x).data.toList ++ s) (((Wire.dataStream T).bytes y).data.toList ++ t) =
        (keyCmp T (Wire.toData T x) (Wire.toData T y)).then (compare s t)
  | .nat, _, _, _, x, y, s, t => by
    show compare ((u64be.bytes x).data.toList ++ s) ((u64be.bytes y).data.toList ++ t) = _
    rw [compare_append (by simp), ← Array.compare_eq_compare_toList, u64be_compare, u64_compare_toNat]
    rfl
  | .bool, _, _, _, x, y, s, t => by
    cases x <;> cases y <;> rfl
  | .digest, _, _, _, x, y, s, t => by
    show compare (((bytesOf Bounds.digestBytesMax (by decide)).bytes x).data.toList ++ s)
      (((bytesOf Bounds.digestBytesMax (by decide)).bytes y).data.toList ++ t) = _
    have hx : x.val.size < 256 := Nat.lt_of_le_of_lt x.2 (by decide)
    have hy : y.val.size < 256 := Nat.lt_of_le_of_lt y.2 (by decide)
    rw [bytesOf_bytes, bytesOf_bytes, ByteArray.data_append, ByteArray.data_append, Array.toList_append,
      Array.toList_append, List.append_assoc, List.append_assoc, compare_append (by simp), u8_list_compare
        (u32.bytes _).data.toList, digest_len _ hx, digest_len _ hy]
    show _ = ((compare x.val.size y.val.size).then (compare x.val.data y.val.data)).then (compare s t)
    by_cases he : x.val.size = y.val.size
    · rw [he, List.compare_cons_cons]
      simp only [Std.ReflCmp.compare_self, Ordering.then]
      rw [compare_append (by simpa using he), Array.compare_eq_compare_toList]
      rfl
    · have hne : compare x.val.size y.val.size ≠ .eq := by
        rw [Ne, Nat.compare_eq_eq]; exact he
      rw [List.compare_cons_cons, then_assoc, then_of_ne hne, then_of_ne hne, then_of_ne hne]
  | .fn _ _, h, _, _, _, _, _, _ => by revert h; simp [keyFixed]
  | .bytes, h, _, _, _, _, _, _ => by revert h; simp [keyFixed]
  | .record r, hf, hw, hwf, x, y, s, t => by
    simp only [keyFixed] at hf
    simp only [Wire.tyWire, Bool.and_eq_true] at hw
    simp only [Ty.wf, Bool.and_eq_true] at hwf
    exact rowCmp r hf hw.2 hwf.2 x y s t
  | .sum r, hf, hw, hwf, ⟨i, x⟩, ⟨j, y⟩, s, t => by
    simp only [keyFixed, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hf
    simp only [Wire.tyWire, Bool.and_eq_true, decide_eq_true_eq] at hw
    simp only [Ty.wf, Bool.and_eq_true] at hwf
    have hl := Wire.armStream_lawful r hw.2
    obtain ⟨hbx, ℓ, -, hdx, hfx⟩ := arm_unit r hwf.1 hf.2 i x
    obtain ⟨hby, ℓ', -, hdy, hfy⟩ := arm_unit r hwf.1 hf.2 j y
    show compare (((Stream.choice r.length (Wire.armStream r)).bytes ⟨i, x⟩).data.toList ++ s)
      (((Stream.choice r.length (Wire.armStream r)).bytes ⟨j, y⟩).data.toList ++ t) =
      (keyCmp (.sum r) (Wire.armToData r i x) (Wire.armToData r j y)).then (compare s t)
    rw [Stream.choice, tagged_bytes hl, tagged_bytes hl, hbx, hby, hdx, hdy]
    simp only [keyCmp, hfx, hfy, u8_bytes, ByteArray.append_empty]
    show compare (finCode i :: s) (finCode j :: t) = _
    rw [List.compare_cons_cons, u8_compare_toNat]
    have hi : i.val < 256 := by have := i.2; simp [Wire.rowMax] at hw; omega
    have hj : j.val < 256 := by have := j.2; simp [Wire.rowMax] at hw; omega
    simp [finCode, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]

theorem rowCmp : ∀ (r : List (Label × Ty)), keyRowFixed r = true → Wire.tyRowWire r = true → Ty.rowWf r = true →
    ∀ (x y : Wire.RowAt r) (s t : List UInt8),
      compare (((Wire.rowStream r).bytes x).data.toList ++ s) (((Wire.rowStream r).bytes y).data.toList ++ t) =
        (keyRowCmp r (Wire.rowToData r x) (Wire.rowToData r y)).then (compare s t)
  | [], _, _, _, (), (), s, t => rfl
  | (ℓ, T) :: r, hf, hw, hwf, (x, xr), (y, yr), s, t => by
    simp only [keyRowFixed, Bool.and_eq_true] at hf
    simp only [Wire.tyRowWire, Bool.and_eq_true] at hw
    simp only [Ty.rowWf, Bool.and_eq_true] at hwf
    show compare (((Stream.product (Wire.dataStream T) (Wire.rowStream r)).bytes (x, xr)).data.toList ++ s)
      (((Stream.product (Wire.dataStream T) (Wire.rowStream r)).bytes (y, yr)).data.toList ++ t) =
      ((keyCmp T (Wire.toData T x) (Wire.toData T y)).then
        (keyRowCmp r (Wire.rowToData r xr) (Wire.rowToData r yr))).then (compare s t)
    rw [product_bytes (Wire.rowStream_lawful r hw.2), product_bytes (Wire.rowStream_lawful r hw.2),
      ByteArray.data_append, ByteArray.data_append, Array.toList_append, Array.toList_append,
      List.append_assoc, List.append_assoc]
    dsimp only
    rw [dataCmp T hf.1 hw.1.2 hwf.1, rowCmp r hf.2 hw.2 hwf.2, then_assoc]
end

/-! ## A key's bytes are its declared order -/

private theorem wire_fixed : ∀ (l : List (Label × Ty)) (n : Nat), l.all (fun f => keyFixed f.2) = true →
    keyRowFixed ((l.zipIdx n).map fun p => ("k" ++ toString p.2, p.1.2)) = true
  | [], _, _ => rfl
  | f :: l, n, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.zipIdx_cons, List.map_cons, keyRowFixed, Bool.and_eq_true]
    exact ⟨h.1, wire_fixed l (n + 1) h.2⟩

private theorem wire_order {k k' : Data} : ∀ (l : List (Label × Ty)) (n : Nat) {ws ws' : List (Label × Data)},
    (l.zipIdx n).mapM (fun p => (k.field p.1.1).map fun v => ("k" ++ toString p.2, v)) = some ws →
    (l.zipIdx n).mapM (fun p => (k'.field p.1.1).map fun v => ("k" ++ toString p.2, v)) = some ws' →
    keyRowCmp ((l.zipIdx n).map fun p => ("k" ++ toString p.2, p.1.2)) ws ws' = keyOrder l k k'
  | [], _, ws, ws', h, h' => by
    simp at h h'; subst h; subst h'; rfl
  | f :: l, n, ws, ws', h, h' => by
    rw [List.zipIdx_cons, List.mapM_cons] at h h'
    cases hf : k.field f.1 with
    | none => simp only [hf, Option.map, bind, Option.bind] at h; cases h
    | some a =>
      cases hf' : k'.field f.1 with
      | none => simp only [hf', Option.map, bind, Option.bind] at h'; cases h'
      | some b =>
        simp only [hf, hf', Option.map, bind, Option.bind] at h h'
        split at h
        · cases h
        · rename_i us hu
          split at h'
          · cases h'
          · rename_i us' hu'
            simp only [pure, Option.some.injEq] at h h'
            subst h; subst h'
            simp only [List.zipIdx_cons, List.map_cons, keyRowCmp, keyOrder, hf, hf', wire_order l (n + 1) hu hu']

private theorem keyBytes_parts {d : RelDecl} {k : Data} {b : ByteArray} (h : keyBytes d k = some b) :
    ∃ ws x, d.key.zipIdx.mapM (fun p => (k.field p.1.1).map fun v => ("k" ++ toString p.2, v)) = some ws ∧
      Wire.dataTy (keyWireTy d d.key.length) = true ∧
      Wire.ofData (keyWireTy d d.key.length) (.record ws) = some x ∧
      (Wire.dataStream (keyWireTy d d.key.length)).bytes x = b := by
  unfold keyBytes keyToWire at h
  cases hw : d.key.zipIdx.mapM (fun p => (k.field p.1.1).map fun v => ("k" ++ toString p.2, v)) with
  | none => rw [hw] at h; cases h
  | some ws =>
    rw [hw] at h
    simp only [Option.map_some, Option.bind_some, Wire.encodeData] at h
    split at h
    · rename_i hdt
      cases hx : Wire.ofData (keyWireTy d d.key.length) (.record ws) with
      | none => rw [hx] at h; cases h
      | some x => rw [hx] at h; cases h; exact ⟨ws, x, rfl, hdt, hx, rfl⟩
    · cases h

/-- **A key's bytes compare as the key does in its declared field order** (LANG-57): for a relation
whose key fields are fixed-width (`checkRel` requires it), two keys `keyBytes` writes compare, as
byte strings, exactly as `keyOrder` compares them: field by field in declared order, a natural by
value, `false` first, an enumeration by arm, a digest shorter first then bytewise. So the kernel's
"ascending key bytes" (`Kernel.range_rows_exact` (ii)) is ascending declared order. -/
theorem keyBytes_compare {d : RelDecl} (hfix : d.key.all (fun f => keyFixed f.2) = true) {k k' : Data}
    {b b' : ByteArray} (h : keyBytes d k = some b) (h' : keyBytes d k' = some b') :
    compare b.data b'.data = keyOrder d.key k k' := by
  obtain ⟨ws, x, hw, hdt, hx, rfl⟩ := keyBytes_parts h
  obtain ⟨ws', x', hw', -, hx', rfl⟩ := keyBytes_parts h'
  simp only [Wire.dataTy, Bool.and_eq_true] at hdt
  have hfx : keyFixed (keyWireTy d d.key.length) = true := by
    simp only [keyWireTy, keyFixed, List.take_length]; exact wire_fixed d.key 0 hfix
  have e := dataCmp _ hfx hdt.2 hdt.1 x x' [] []
  rw [List.append_nil, List.append_nil, Wire.toData_ofData _ hx, Wire.toData_ofData _ hx'] at e
  rw [Array.compare_eq_compare_toList, e, List.compare_nil_nil, then_eq_right]
  simp only [keyWireTy, List.take_length, keyCmp]
  exact wire_order d.key 0 hw hw'

/-- The installed form: `checkRel` (install's check of each relation) gives the fixed-width premise. -/
theorem keyBytes_compare_installed {S : Ty} {row : List (Label × Ty)} {ℓ : Label} {d : RelDecl}
    (hc : checkRel S row (ℓ, d) = .ok ()) {k k' : Data} {b b' : ByteArray} (h : keyBytes d k = some b)
    (h' : keyBytes d k' = some b') : compare b.data b'.data = keyOrder d.key k k' := by
  refine keyBytes_compare ?_ h h'
  unfold checkRel at hc
  simp only [bind, Except.bind] at hc
  split at hc
  · rename_i hk
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true] at hk
    simp only [List.all_eq_true]
    exact fun f hf => (hk.1.1.2 f hf).2
  · cases hc

/-! ## The reader's keys: `keyOf` reads exactly the bytes `keyBytes` writes -/

private theorem rowToData_labels : ∀ (r : List (Label × Ty)) (x : Wire.RowAt r),
    (Wire.rowToData r x).map (·.1) = r.map (·.1)
  | [], () => rfl
  | (_, _) :: r, (_, y) => by simp [Wire.rowToData, rowToData_labels r y]

private theorem asc_lt_mem {α : Type} : ∀ {k : Label} {t : α} {r : List (Label × α)},
    Row.ascending ((k, t) :: r) = true → ∀ p ∈ r, k < p.1
  | _, _, [], _, p, hp => by simp at hp
  | k, t, (k2, t2) :: r, ha, p, hp => by
    simp only [Row.ascending, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ha.1
    · exact String.lt_trans ha.1 (asc_lt_mem ha.2 p hp)

private theorem ascending_nodup {α : Type} : ∀ {l : List (Label × α)}, Row.ascending l = true → (l.map (·.1)).Nodup
  | [], _ => List.nodup_nil
  | (k, t) :: l, h => by
    have ht : Row.ascending l = true := by
      cases l with
      | nil => rfl
      | cons e l => simp only [Row.ascending, Bool.and_eq_true] at h; exact h.2
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ascending_nodup ht⟩
    rintro ⟨p, hp, he⟩
    have := asc_lt_mem h p hp
    rw [he] at this
    exact String.lt_irrefl _ this

private theorem find_of_mem_nodup {α : Type} : ∀ {l : List (Label × α)} {ℓ : Label} {a : α},
    (l.map (·.1)).Nodup → (ℓ, a) ∈ l → Row.find? ℓ l = some a
  | [], _, _, _, h => by simp at h
  | (k, b) :: l, ℓ, a, hn, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 h with he | h
    · cases he; simp [Row.find?]
    · have hne : ℓ ≠ k := fun e => hn.1 (e ▸ List.mem_map_of_mem (f := (·.1)) h)
      simp [Row.find?, hne, find_of_mem_nodup hn.2 h]

private theorem wire_mapM {look : Label → Option Data} : ∀ (K : List (Label × Ty)) (n : Nat) (fs : List (Label × Data)),
    fs.map (·.1) = (K.zipIdx n).map (fun p => "k" ++ toString p.2) →
    (∀ p ∈ K.zip fs, look p.1.1 = some p.2.2) →
    (K.zipIdx n).mapM (fun p => (look p.1.1).map fun v => ("k" ++ toString p.2, v)) = some fs
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, hl, _ => by simp at hl
  | _ :: _, _, [], hl, _ => by simp at hl
  | f :: K, n, (l, v) :: fs, hl, hv => by
    simp only [List.zipIdx_cons, List.map_cons, List.cons.injEq] at hl
    have h1 : look f.1 = some v := hv (f, (l, v)) (by simp)
    have ih := wire_mapM K (n + 1) fs hl.2 (fun p hp => hv p (List.mem_cons_of_mem _ hp))
    rw [List.zipIdx_cons, List.mapM_cons, h1, ih, hl.1]
    rfl

/-- **`keyOf` reads only bytes `keyBytes` writes** (LANG-57; the converse of `keyOf_keyBytes`): at a
canonical key type (`checkRel` checks `(keyTy d).wf`, so the declared labels are distinct), a key `keyOf`
reads from bytes `b` is written back by `keyBytes` as exactly `b`. -/
theorem keyBytes_keyOf {d : RelDecl} (hwf : (keyTy d).wf = true) {b : ByteArray} {k : Data}
    (h : keyOf d d.key.length b = .ok k) : keyBytes d k = some b := by
  unfold keyOf at h
  split at h
  · rename_i fs hd
    cases h
    have he := Wire.decodeData_eq_ok_iff.1 hd
    have he' := he
    unfold Wire.encodeData at he'
    split at he'
    · cases hx : Wire.ofData (keyWireTy d d.key.length) (.record fs) with
      | none => rw [hx] at he'; cases he'
      | some x =>
        have hfs := Wire.toData_ofData _ hx
        simp only [keyWireTy, List.take_length] at hfs x
        simp only [Wire.toData, Data.record.injEq] at hfs
        have hl : fs.map (·.1) = (d.key.zipIdx).map (fun p => "k" ++ toString p.2) := by
          rw [← hfs, rowToData_labels, List.map_map, List.take_length]; rfl
        have hlen : d.key.length ≤ fs.length := by
          have := congrArg List.length hl; simp at this; omega
        have hasc : Row.ascending (Row.sort d.key) = true := by
          simp only [keyTy, Ty.wf, Bool.and_eq_true] at hwf; exact hwf.1
        have hnd : ((Row.sort ((d.key.zip fs).map fun p => (p.1.1, p.2.2))).map (·.1)).Nodup := by
          rw [((Row.sort_perm _).map _).nodup_iff, List.map_map]
          have e : ((fun x : Label × Data => x.1) ∘ fun p : (Label × Ty) × (Label × Data) => (p.1.1, p.2.2)) =
              (fun x : Label × Ty => x.1) ∘ Prod.fst := rfl
          rw [e, ← List.map_map, List.map_fst_zip hlen, ← ((Row.sort_perm d.key).map _).nodup_iff]
          exact ascending_nodup hasc
        unfold keyBytes keyToWire
        simp only [List.take_length]
        rw [wire_mapM d.key 0 fs hl (fun p hp => ?_)]
        · simp only [Option.map, Option.bind]; exact he
        · show Row.find? p.1.1 _ = some p.2.2
          exact find_of_mem_nodup hnd ((Row.sort_perm _).mem_iff.2 (List.mem_map_of_mem hp))
    · cases he'
  · cases h
  · cases h

/-! ## A range read lists its rows in declared key order -/

/-- Two rows under one range prefix share the bytes before their keys: what differs is the key. -/
private theorem listed_prefix {D : Type} {E : Kernel.Env D} {n : Nat} (hsize : ∀ d, (E.bytes d).size = n) {parent : D}
    {rel width : Nat} {pre : ByteArray} {key : RowKey D}
    (hs : startsWith (rowsPrefix E parent rel width ++ pre) (rowKeyBytes E (.row key)) = true) :
    (rowKeyBytes E (.row key)).data.toList =
      (rowsPrefix E parent rel width).data.toList ++ key.k.data.toList := by
  obtain ⟨p, k, hk, hp, hw⟩ := key_under_prefix E hsize hs
  cases hk
  simp only [rowKeyBytes, rowsPrefix, ByteArray.data_append, Array.toList_append, hp, hw]

/-- **A range read lists its rows in the relation's declared key order** (LANG-57): on the kernel's
own premises for `range_rows_exact` (one digest size `n ≤ 32`, injective digest bytes, a canonical
rows trie whose entries fit, `pre.size ≤ width`), for a relation whose key fields are
fixed-width, any two rows the read lists, the earlier first, whose key bytes are `keyBytes` of keys
`k` and `k'`, have `k` strictly before `k'` in declared order. -/
theorem range_keys_ascend {D : Type} [DecidableEq D] {E : Kernel.Env D} {n : Nat}
    (hsize : ∀ d, (E.bytes d).size = n) (hn : n ≤ 32) (hinj : Function.Injective E.bytes)
    {r : Rows D} (hc : Trie.Canon (rowSpec E) 0 r) (hfit : ∀ p ∈ r.toList, rowFits p.1 p.2 = true)
    {parent : D} {rel width : Nat} {pre : ByteArray} (hw : pre.size ≤ width) {most : Nat}
    {l : List (RowSlot D × RowLeaf)} (h : rangeRows E r parent rel width pre most = some l)
    {d : RelDecl} (hfix : d.key.all (fun f => keyFixed f.2) = true) :
    l.Pairwise fun a b => ∀ (ka kb : RowKey D) (k k' : Data), a.1 = .row ka → b.1 = .row kb →
      keyBytes d k = some ka.k → keyBytes d k' = some kb.k → keyOrder d.key k k' = .lt := by
  obtain ⟨hmem, hsort, -⟩ := range_rows_exact_of hsize hn hinj hc hfit hw h
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) hsort
  intro ka kb k k' hka hkb hk hk'
  have hsa := ((hmem a.1 a.2).1 ha).2
  have hsb := ((hmem b.1 b.2).1 hb).2
  rw [hka] at hsa hab
  rw [hkb] at hsb hab
  rw [Array.compare_eq_compare_toList, listed_prefix hsize hsa, listed_prefix hsize hsb,
    compare_append rfl, Std.ReflCmp.compare_self (cmp := compare), ← Array.compare_eq_compare_toList] at hab
  rw [← keyBytes_compare hfix hk hk']
  exact hab

/-- **The keys a range read's reader decodes are ascending** (LANG-57, the queue's statement, on
`rangeRowData`'s path): for an installed relation (`checkRel`), any two listed rows, the earlier first,
whose key bytes `keyOf` reads as `k` and `k'`, have `k` strictly before `k'` in declared order. A row
whose key bytes do not decode is outside the statement (and `rangeRowData` refuses the whole read on
it). `keyBytes_keyOf` turns the reader's keys into the writer's bytes. -/
theorem range_keys_ascend_read {D : Type} [DecidableEq D] {E : Kernel.Env D} {n : Nat}
    (hsize : ∀ d, (E.bytes d).size = n) (hn : n ≤ 32) (hinj : Function.Injective E.bytes)
    {r : Rows D} (hc : Trie.Canon (rowSpec E) 0 r) (hfit : ∀ p ∈ r.toList, rowFits p.1 p.2 = true)
    {parent : D} {rel width : Nat} {pre : ByteArray} (hw : pre.size ≤ width) {most : Nat}
    {l : List (RowSlot D × RowLeaf)} (h : rangeRows E r parent rel width pre most = some l)
    {S : Ty} {row : List (Label × Ty)} {ℓ : Label} {d : RelDecl} (hd : checkRel S row (ℓ, d) = .ok ()) :
    l.Pairwise fun a b => ∀ (ka kb : RowKey D) (k k' : Data), a.1 = .row ka → b.1 = .row kb →
      keyOf d d.key.length ka.k = .ok k → keyOf d d.key.length kb.k = .ok k' → keyOrder d.key k k' = .lt := by
  have hfix : d.key.all (fun f => keyFixed f.2) = true := by
    unfold checkRel at hd
    simp only [bind, Except.bind] at hd
    split at hd
    · rename_i hk
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true] at hk
      simp only [List.all_eq_true]
      exact fun f hf => (hk.1.1.2 f hf).2
    · cases hd
  have hwf : (keyTy d).wf = true := by
    unfold checkRel at hd
    simp only [bind, Except.bind] at hd
    split at hd
    · rename_i hk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      exact hk.1.2
    · cases hd
  refine (range_keys_ascend hsize hn hinj hc hfit hw h hfix).imp ?_
  intro a b hab ka kb k k' hka hkb hk hk'
  exact hab ka kb k k' hka hkb (keyBytes_keyOf hwf hk) (keyBytes_keyOf hwf hk')

/-! ## Teeth -/

/-- The queue's relation: one natural key field. -/
private def queueDecl : RelDecl :=
  { key := [("n", .nat)], val := .record [], limit := 8, sum := none, cap := 0, retract := false, guard := none }

/-- **Tooth**: `(n 1)` is written before `(n 256)`, by bytes and by declared order. Under the old
little-endian wire the same two keys' bytes compare the other way (`Codec.Stream.u64_misorders`). -/
private theorem key_order_1_256 :
    ∃ b b', keyBytes queueDecl (.record [("n", .nat 1)]) = some b ∧
      keyBytes queueDecl (.record [("n", .nat 256)]) = some b' ∧ compare b.data b'.data = .lt ∧
      keyOrder queueDecl.key (.record [("n", .nat 1)]) (.record [("n", .nat 256)]) = .lt := by
  refine ⟨_, _, rfl, rfl, ?_, by decide⟩
  rw [keyBytes_compare (d := queueDecl) (k := .record [("n", .nat 1)]) (k' := .record [("n", .nat 256)])
    (by decide) rfl rfl]
  decide

/-- A key declared `(b nat) (a nat)`: its order is the DECLARED one, `b` first, not the label order. -/
private def pairDecl : RelDecl :=
  { key := [("b", .nat), ("a", .nat)], val := .record [], limit := 8, sum := none, cap := 0, retract := false,
    guard := none }

/-- **Tooth**: `b` decides although `a` disagrees: `{a 9, b 1}` before `{a 0, b 2}`, in bytes and in
declared order (label order would put it after). -/
private theorem key_order_declared_first :
    ∃ b b', keyBytes pairDecl (.record [("a", .nat 9), ("b", .nat 1)]) = some b ∧
      keyBytes pairDecl (.record [("a", .nat 0), ("b", .nat 2)]) = some b' ∧ compare b.data b'.data = .lt ∧
      keyCmp (.nat) (.nat 9) (.nat 0) = .gt := by
  refine ⟨_, _, rfl, rfl, ?_, by decide⟩
  rw [keyBytes_compare (d := pairDecl) (k := .record [("a", .nat 9), ("b", .nat 1)])
    (k' := .record [("a", .nat 0), ("b", .nat 2)]) (by decide) rfl rfl]
  decide

/-- A key of one digest. -/
private def digestDecl : RelDecl :=
  { key := [("d", .digest)], val := .record [], limit := 8, sum := none, cap := 0, retract := false, guard := none }

/-- **Tooth**: a digest is shorter-first: one byte `ff` before two bytes `00 00`, though `ff > 00`. -/
private theorem key_order_digest_shortlex :
    ∃ b b', keyBytes digestDecl (.record [("d", .digest ⟨#[0xff]⟩)]) = some b ∧
      keyBytes digestDecl (.record [("d", .digest ⟨#[0, 0]⟩)]) = some b' ∧ compare b.data b'.data = .lt := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  rw [keyBytes_compare (d := digestDecl) (k := .record [("d", .digest ⟨#[0xff]⟩)])
    (k' := .record [("d", .digest ⟨#[0, 0]⟩)]) (by decide) rfl rfl]
  decide

/-! ### A queue on a concrete rows trie: 256 written first, 1 listed first -/

/-- One-byte digests, `bytes d = [d]`: one size, injective. -/
private def queueEnv : Kernel.Env UInt8 where
  hash _ _ := 0
  bytes d := ⟨#[d]⟩
  turnBytes _ := ByteArray.empty
  cellBytes _ := ByteArray.empty

private def queueKey (n : Nat) : ByteArray := (keyBytes queueDecl (.record [("n", .nat n)])).getD ByteArray.empty

private def queueSlot (n : Nat) : RowSlot UInt8 := .row ⟨7, 3, queueKey n⟩

/-- The queue's rows: its head (width 8), ring 256 inserted, then ring 1. -/
private def queueRows : Rows UInt8 :=
  ((Trie.T.empty.insert (rowSpec queueEnv) (queueSlot 256) (.row 0 ByteArray.empty 0)).insert (rowSpec queueEnv)
    (queueSlot 1) (.row 0 ByteArray.empty 0)).insert (rowSpec queueEnv) (.head 7 3) (.head 2 0 8 0 8 false 0)

/-- The same trie written with the OLD little-endian key bytes. -/
private def leRows : Rows UInt8 :=
  ((Trie.T.empty.insert (rowSpec queueEnv) (.row ⟨7, 3, Stream.u64.bytes 256⟩) (.row 0 ByteArray.empty 0)).insert
    (rowSpec queueEnv) (.row ⟨7, 3, Stream.u64.bytes 1⟩) (.row 0 ByteArray.empty 0)).insert (rowSpec queueEnv)
    (.head 7 3) (.head 2 0 8 0 8 false 0)

private theorem queue_lists_1_first :
    rangeRows queueEnv queueRows 7 3 8 ByteArray.empty 5 =
      some [(queueSlot 1, .row 0 ByteArray.empty 0), (queueSlot 256, .row 0 ByteArray.empty 0)] := by decide

/-- **Tooth, the old wire at the key level**: under little-endian key bytes the same queue lists ring 256
before ring 1. -/
private theorem le_queue_lists_256_first :
    rangeRows queueEnv leRows 7 3 8 ByteArray.empty 5 =
      some [(.row ⟨7, 3, Stream.u64.bytes 256⟩, .row 0 ByteArray.empty 0),
        (.row ⟨7, 3, Stream.u64.bytes 1⟩, .row 0 ByteArray.empty 0)] := by decide

/-- **`range_keys_ascend_read` is not vacuous**: every premise holds on the concrete queue (an
installed relation, a canonical trie whose entries fit, one injective digest size), the read lists two
rows, and the keys its reader decodes, ring 1 then ring 256, come out `.lt` from the theorem. -/
private theorem range_keys_ascend_read_satisfiable :
    keyOrder queueDecl.key (.record [("n", .nat 1)]) (.record [("n", .nat 256)]) = .lt := by
  have hinj : Function.Injective queueEnv.bytes := by
    intro a b h
    have := congrArg (fun x : ByteArray => x.data[0]!) h
    simpa [queueEnv] using this
  have hc : Trie.Canon (rowSpec queueEnv) 0 queueRows :=
    Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _ (Trie.canon_empty _ 0)))
  have hfit : ∀ p ∈ queueRows.toList, rowFits p.1 p.2 = true := by decide
  have hd : checkRel (.record []) [] ("rings", queueDecl) = .ok () := rfl
  have hp := range_keys_ascend_read (fun _ => rfl) (by decide) hinj hc hfit (by decide)
    queue_lists_1_first hd
  exact (List.pairwise_pair.1 hp) _ _ _ _ rfl rfl rfl rfl

/-- **Tooth, bytes computed directly** (not through `keyBytes_compare`): the bytes `keyBytes` writes for
ring 1 compare below ring 256's. -/
private theorem queue_key_bytes_1_256 : compare (queueKey 1).data (queueKey 256).data = .lt := by
  rw [Array.compare_eq_compare_toList, u8_list_compare]
  decide

/-! ## Distinct key labels have one source: `(keyTy d).wf` -/

/-- **An installed relation's key labels are distinct** (ROOT's ruling on the always-true length check,
2026-10-19): `checkRel` refuses `relKey` unless `keyTy d` (the key's fields, sorted) is canonical, and a
canonical row strictly ascends, so no label repeats. The one check is `wf`; tooth
`checkRel_refuses_dup_key_label`. -/
theorem checkRel_key_nodup {S : Ty} {row : List (Label × Ty)} {ℓ : Label} {d : RelDecl}
    (hd : checkRel S row (ℓ, d) = .ok ()) : (d.key.map (·.1)).Nodup := by
  have hwf : (keyTy d).wf = true := by
    unfold checkRel at hd
    simp only [bind, Except.bind] at hd
    split at hd
    · rename_i hk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      exact hk.1.2
    · cases hd
  have hasc : Row.ascending (Row.sort d.key) = true := by
    simp only [keyTy, Ty.wf, Bool.and_eq_true] at hwf; exact hwf.1
  exact ((Row.sort_perm d.key).map _).nodup_iff.1 (ascending_nodup hasc)

/-- A key declaring the label `n` twice. -/
private def dupDecl : RelDecl :=
  { key := [("n", .nat), ("n", .bool)], val := .record [], limit := 8, sum := none, cap := 0, retract := false,
    guard := none }

/-- **Tooth**: two key fields of one label are refused `relKey`, by name, through `wf` alone. -/
private theorem checkRel_refuses_dup_key_label :
    checkRel (.record []) [] ("r", dupDecl) = .error (.relKey "r") := rfl

/-- Its twin: the same key with distinct labels installs. -/
private theorem checkRel_admits_distinct_key_labels :
    checkRel (.record []) [] ("r", { dupDecl with key := [("m", .nat), ("n", .bool)] }) = .ok () := rfl

end Nanodregg.Lang
