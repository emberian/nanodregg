/-
# Lang.Proofs.Wire — one package, one tree, one byte string

`tyOf`/`termOf`/`packageOf` read back exactly what `tyTree`/`termTree`/`packageTree` write for a
representable value (`*_of_tree`), and whatever they accept is the tree of what they return, which
is representable (`tree_of_*`). With `Codec.Stream.tree_lawful` that is canonicity of the package
codec: `decodePackage_eq_ok_iff : decodePackage b = .ok p ↔ encodePackage p = some b`.
-/
import Lang.Package
import Codec.Proofs.Tree

namespace Nanodregg.Lang.Wire

open Nanodregg.Codec

/-! ## Leaves -/

theorem fromUTF8_toByteArray (ℓ : Label) : String.fromUTF8? ℓ.toByteArray = some ℓ := by
  unfold String.fromUTF8?
  exact dif_pos ℓ.isValidUTF8

theorem labelOf_toUTF8 {ℓ : Label} (h : labelOk ℓ = true) : labelOf ℓ.toByteArray = some ℓ := by
  simp only [labelOk, Bool.and_eq_true, decide_eq_true_eq, String.toUTF8_eq_toByteArray] at h
  unfold labelOf
  rw [if_pos h.2, fromUTF8_toByteArray]
  simp only [h.1, if_true]

theorem labelOf_some {p : ByteArray} {ℓ : Label} (h : labelOf p = some ℓ) :
    ℓ.toByteArray = p ∧ labelOk ℓ = true := by
  unfold labelOf at h
  split at h
  · rename_i hs
    split at h
    · rename_i ℓ' hf
      split at h
      · rename_i ha
        cases h
        unfold String.fromUTF8? at hf
        split at hf
        · cases hf
          refine ⟨rfl, ?_⟩
          simp only [labelOk, ha, Bool.true_and, decide_eq_true_eq, String.toUTF8_eq_toByteArray]
          exact hs
        · simp at hf
      · simp at h
    · simp at h
  · simp at h

theorem u32Of_bytes {n : Nat} (h : n < 2 ^ 32) : u32Of (u32Bytes n) = some n := by
  simp only [u32Of, u32Bytes, Stream.decode_bytes Stream.u32_lawful, UInt32.toNat_ofNat_of_lt' h]

theorem u32Of_some {p : ByteArray} {n : Nat} (h : u32Of p = some n) : u32Bytes n = p ∧ n < 2 ^ 32 := by
  unfold u32Of at h
  split at h
  · rename_i v hv
    cases h
    refine ⟨?_, v.toNat_lt⟩
    simp only [u32Bytes, UInt32.ofNat_toNat]
    exact (Stream.eq_bytes_of_decode Stream.u32_lawful hv).symm
  · simp at h

theorem u64Of_bytes {n : Nat} (h : n < 2 ^ 64) : u64Of (u64Bytes n) = some n := by
  simp only [u64Of, u64Bytes, Stream.decode_bytes Stream.u64_lawful, UInt64.toNat_ofNat_of_lt' h]

theorem u64Of_some {p : ByteArray} {n : Nat} (h : u64Of p = some n) : u64Bytes n = p ∧ n < 2 ^ 64 := by
  unfold u64Of at h
  split at h
  · rename_i v hv
    cases h
    refine ⟨?_, v.toNat_lt⟩
    simp only [u64Bytes, UInt64.ofNat_toNat]
    exact (Stream.eq_bytes_of_decode Stream.u64_lawful hv).symm
  · simp at h

theorem boolOf_bytes (v : Bool) : boolOf (Stream.bool.bytes v) = some v := by
  simp only [boolOf, Stream.decode_bytes Stream.bool_lawful]

theorem boolOf_some {p : ByteArray} {v : Bool} (h : boolOf p = some v) : Stream.bool.bytes v = p := by
  unfold boolOf at h
  split at h
  · rename_i w hw; cases h; exact (Stream.eq_bytes_of_decode Stream.bool_lawful hw).symm
  · simp at h

theorem primOf_code (op : Prim) : primOf (primCode op) = some op := by cases op <;> rfl

theorem primOfBytes_bytes (op : Prim) : primOfBytes (Stream.u8.bytes (primCode op)) = some op := by
  simp only [primOfBytes, Stream.decode_bytes Stream.u8_lawful, primOf_code]

theorem code_primOf {c : UInt8} {op : Prim} (h : primOf c = some op) : primCode op = c := by
  unfold primOf at h
  split at h <;> first | (simp at h; done) | (cases h; rfl)

theorem primOfBytes_some {p : ByteArray} {op : Prim} (h : primOfBytes p = some op) :
    Stream.u8.bytes (primCode op) = p := by
  unfold primOfBytes at h
  split at h
  · rename_i c hc; rw [code_primOf h]; exact (Stream.eq_bytes_of_decode Stream.u8_lawful hc).symm
  · simp at h

/-! ## Types -/

mutual
theorem tyOf_tyTree : (T : Ty) → tyWire T = true → tyOf (tyTree T) = some T
  | .nat, _ | .bool, _ | .bytes, _ | .digest, _ => by simp [tyTree, tyOf]
  | .fn a c, h => by
    simp only [tyWire, Bool.and_eq_true] at h
    simp [tyTree, tyOf, tyOf_tyTree a h.1, tyOf_tyTree c h.2]
  | .record r, h => by
    simp only [tyWire, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [tyTree, tyOf, tyRowTree_length, h.1, tyRowOf_tyRowTree r h.2]
  | .sum r, h => by
    simp only [tyWire, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [tyTree, tyOf, tyRowTree_length, h.1, tyRowOf_tyRowTree r h.2]

theorem tyRowOf_tyRowTree : (r : List (Label × Ty)) → tyRowWire r = true → tyRowOf (tyRowTree r) = some r
  | [], _ => by simp [tyRowTree, tyRowOf]
  | (ℓ, t) :: r, h => by
    simp only [tyRowWire, Bool.and_eq_true] at h
    simp only [tyRowTree, tyRowOf, String.toUTF8_eq_toByteArray, labelOf_toUTF8 h.1.1, tyOf_tyTree t h.1.2, tyRowOf_tyRowTree r h.2]

theorem tyRowTree_length : (r : List (Label × Ty)) → (tyRowTree r).length = r.length
  | [] => rfl
  | _ :: r => by simp [tyRowTree, tyRowTree_length r]
end

theorem tyOf_inv (n : Nat) :
    (∀ (t : Tree), sizeOf t < n → ∀ {T : Ty}, tyOf t = some T → tyTree T = t ∧ tyWire T = true) ∧
    (∀ (cs : List Tree), sizeOf cs < n → ∀ {r : List (Label × Ty)}, tyRowOf cs = some r →
      tyRowTree r = cs ∧ tyRowWire r = true) := by
  induction n with
  | zero => exact ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨ihT, ihR⟩ := ih
    refine ⟨?_, ?_⟩
    · intro t hs T h
      obtain ⟨tag, p, cs⟩ := t
      unfold tyOf at h
      split at h
      all_goals first
        | (simp at h; done)
        | (rename_i heq; rw [heq] at hs ⊢; simp at hs)
      all_goals first
        | (split at h
           · cases h; simp_all [tyTree, tyWire]
           · simp at h
           done)
        | skip
      · rename_i a c
        split at h
        · rename_i hp
          split at h
          · rename_i a1 c1 ha hc
            cases h
            obtain ⟨ea, wa⟩ := ihT a (by omega) ha
            obtain ⟨ec, wc⟩ := ihT c (by omega) hc
            simp [tyTree, tyWire, ea, ec, wa, wc, hp]
          · simp at h
        · simp at h
      · rename_i cs
        split at h
        · rename_i hc
          cases e : tyRowOf cs with
          | none => simp [e] at h
          | some r =>
            simp only [e, Option.map_some, Option.some.injEq] at h
            subst h
            obtain ⟨er, wr⟩ := ihR cs (by omega) e
            refine ⟨by simp [tyTree, er, hc.1], ?_⟩
            have hl : r.length ≤ rowMax := by rw [← tyRowTree_length, er]; exact hc.2
            simp [tyWire, hl, wr]
        · simp at h
      · rename_i cs
        split at h
        · rename_i hc
          cases e : tyRowOf cs with
          | none => simp [e] at h
          | some r =>
            simp only [e, Option.map_some, Option.some.injEq] at h
            subst h
            obtain ⟨er, wr⟩ := ihR cs (by omega) e
            refine ⟨by simp [tyTree, er, hc.1], ?_⟩
            have hl : r.length ≤ rowMax := by rw [← tyRowTree_length, er]; exact hc.2
            simp [tyWire, hl, wr]
        · simp at h
    · intro cs hs r h
      unfold tyRowOf at h
      split at h
      · cases h; simp [tyRowTree, tyRowWire]
      · rename_i p c cs
        split at h
        · rename_i ℓ t r' hl ht hr
          cases h
          simp at hs
          obtain ⟨el, wl⟩ := labelOf_some hl
          obtain ⟨et, wt⟩ := ihT c (by omega) ht
          obtain ⟨er, wr⟩ := ihR cs (by omega) hr
          simp [tyRowTree, tyRowWire, el, wl, et, wt, er, wr]
        · simp at h
      · simp at h

theorem tree_of_tyOf {t : Tree} {T : Ty} (h : tyOf t = some T) : tyTree T = t ∧ tyWire T = true :=
  (tyOf_inv (sizeOf t + 1)).1 t (Nat.lt_succ_self _) h

/-! ## Terms -/

mutual
theorem termOf_termTree : (t : Term) → termWire t = true → termOf (termTree t) = some t
  | .var i, h => by
    simp only [termWire, decide_eq_true_eq] at h
    simp [termTree, termOf, u32Of_bytes h]
  | .ref i, h => by
    simp only [termWire, decide_eq_true_eq] at h
    simp [termTree, termOf, u32Of_bytes h]
  | .nat n, h => by
    simp only [termWire, decide_eq_true_eq] at h
    simp [termTree, termOf, u64Of_bytes h]
  | .bool v, _ => by simp [termTree, termOf, boolOf_bytes]
  | .bytes s, _ => by simp [termTree, termOf]
  | .digest s, _ => by simp [termTree, termOf]
  | .lam a b, h => by
    simp only [termWire, Bool.and_eq_true] at h
    simp [termTree, termOf, tyOf_tyTree a h.1, termOf_termTree b h.2]
  | .app f a, h => by
    simp only [termWire, Bool.and_eq_true] at h
    simp [termTree, termOf, termOf_termTree f h.1, termOf_termTree a h.2]
  | .fix t, h => by
    simp only [termWire] at h
    simp [termTree, termOf, termOf_termTree t h]
  | .prim op a b, h => by
    simp only [termWire, Bool.and_eq_true] at h
    simp only [termTree, termOf, primOfBytes_bytes, termOf_termTree a h.1, termOf_termTree b h.2]
  | .record fs, h => by
    simp only [termWire, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [termTree, termOf, fieldsTree_length, h.1, fieldsOf_fieldsTree fs h.2]
  | .get t ℓ, h => by
    simp only [termWire, Bool.and_eq_true] at h
    simp only [termTree, termOf, String.toUTF8_eq_toByteArray, labelOf_toUTF8 h.1, termOf_termTree t h.2]
  | .extend t fs, h => by
    simp only [termWire, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [termTree, termOf, fieldsTree_length, h.1.2, termOf_termTree t h.1.1, fieldsOf_fieldsTree fs h.2]
  | .inj a ℓ t, h => by
    simp only [termWire, Bool.and_eq_true] at h
    simp only [termTree, termOf, String.toUTF8_eq_toByteArray, labelOf_toUTF8 h.1.2, tyOf_tyTree a h.1.1,
      termOf_termTree t h.2]
  | .case t arms, h => by
    simp only [termWire, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [termTree, termOf, fieldsTree_length, h.1.2, termOf_termTree t h.1.1, fieldsOf_fieldsTree arms h.2]
  | .ite c t e, h => by
    simp only [termWire, Bool.and_eq_true] at h
    simp [termTree, termOf, termOf_termTree c h.1.1, termOf_termTree t h.1.2, termOf_termTree e h.2]

theorem fieldsOf_fieldsTree : (fs : List (Label × Term)) → fieldsWire fs = true →
    fieldsOf (fieldsTree fs) = some fs
  | [], _ => by simp [fieldsTree, fieldsOf]
  | (ℓ, t) :: fs, h => by
    simp only [fieldsWire, Bool.and_eq_true] at h
    simp only [fieldsTree, fieldsOf, String.toUTF8_eq_toByteArray, labelOf_toUTF8 h.1.1,
      termOf_termTree t h.1.2, fieldsOf_fieldsTree fs h.2]

theorem fieldsTree_length : (fs : List (Label × Term)) → (fieldsTree fs).length = fs.length
  | [] => rfl
  | _ :: fs => by simp [fieldsTree, fieldsTree_length fs]
end

theorem termOf_inv (n : Nat) :
    (∀ (t : Tree), sizeOf t < n → ∀ {x : Term}, termOf t = some x → termTree x = t ∧ termWire x = true) ∧
    (∀ (cs : List Tree), sizeOf cs < n → ∀ {fs : List (Label × Term)}, fieldsOf cs = some fs →
      fieldsTree fs = cs ∧ fieldsWire fs = true) := by
  induction n with
  | zero => exact ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨ihT, ihR⟩ := ih
    refine ⟨?_, ?_⟩
    · intro t hs x h
      obtain ⟨tag, p, cs⟩ := t
      unfold termOf at h
      split at h
      all_goals first
        | (simp at h; done)
        | (rename_i heq; rw [heq] at hs ⊢; simp at hs)
      · rename_i q
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨i, hi, rfl⟩ := h
        obtain ⟨e, w⟩ := u32Of_some hi
        simp [termTree, termWire, e, w]
      · rename_i q a b
        split at h
        · rename_i hq
          split at h
          · rename_i a1 b1 ha hb
            cases h
            obtain ⟨ea, wa⟩ := tree_of_tyOf ha
            obtain ⟨eb, wb⟩ := ihT b (by omega) hb
            simp [termTree, termWire, ea, eb, wa, wb, hq]
          · simp at h
        · simp at h
      · rename_i q f a
        split at h
        · rename_i hq
          split at h
          · rename_i f1 a1 hf ha
            cases h
            obtain ⟨ef, wf⟩ := ihT f (by omega) hf
            obtain ⟨ea, wa⟩ := ihT a (by omega) ha
            simp [termTree, termWire, ef, ea, wf, wa, hq]
          · simp at h
        · simp at h
      · rename_i q t
        split at h
        · rename_i hq
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨t1, ht, rfl⟩ := h
          obtain ⟨et, wt⟩ := ihT t (by omega) ht
          simp [termTree, termWire, et, wt, hq]
        · simp at h
      · rename_i q
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨i, hi, rfl⟩ := h
        obtain ⟨e, w⟩ := u64Of_some hi
        simp [termTree, termWire, e, w]
      · rename_i q
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        simp [termTree, termWire, boolOf_some hv]
      · cases h; simp [termTree, termWire]
      · cases h; simp [termTree, termWire]
      · rename_i q a b
        split at h
        · rename_i op a1 b1 hop ha hb
          cases h
          obtain ⟨ea, wa⟩ := ihT a (by omega) ha
          obtain ⟨eb, wb⟩ := ihT b (by omega) hb
          simp [termTree, termWire, ea, eb, wa, wb, primOfBytes_some hop]
        · simp at h
      · rename_i q fs
        split at h
        · rename_i hq
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨fs1, hf, rfl⟩ := h
          obtain ⟨ef, wf⟩ := ihR fs (by omega) hf
          have hl : fs1.length ≤ rowMax := by rw [← fieldsTree_length, ef]; exact hq.2
          simp [termTree, termWire, ef, wf, hq.1, hl]
        · simp at h
      · rename_i q t
        split at h
        · rename_i ℓ t1 hl ht
          cases h
          obtain ⟨el, wl⟩ := labelOf_some hl
          obtain ⟨et, wt⟩ := ihT t (by omega) ht
          simp [termTree, termWire, el, wl, et, wt]
        · simp at h
      · rename_i q t fs
        split at h
        · rename_i hq
          split at h
          · rename_i t1 fs1 ht hf
            cases h
            obtain ⟨et, wt⟩ := ihT t (by omega) ht
            obtain ⟨ef, wf⟩ := ihR fs (by omega) hf
            have hl : fs1.length ≤ rowMax := by rw [← fieldsTree_length, ef]; exact hq.2
            simp [termTree, termWire, et, wt, ef, wf, hq.1, hl]
          · simp at h
        · simp at h
      · rename_i q a t
        split at h
        · rename_i ℓ a1 t1 hl ha ht
          cases h
          obtain ⟨el, wl⟩ := labelOf_some hl
          obtain ⟨ea, wa⟩ := tree_of_tyOf ha
          obtain ⟨et, wt⟩ := ihT t (by omega) ht
          simp [termTree, termWire, el, wl, ea, wa, et, wt]
        · simp at h
      · rename_i q t fs
        split at h
        · rename_i hq
          split at h
          · rename_i t1 fs1 ht hf
            cases h
            obtain ⟨et, wt⟩ := ihT t (by omega) ht
            obtain ⟨ef, wf⟩ := ihR fs (by omega) hf
            have hl : fs1.length ≤ rowMax := by rw [← fieldsTree_length, ef]; exact hq.2
            simp [termTree, termWire, et, wt, ef, wf, hq.1, hl]
          · simp at h
        · simp at h
      · rename_i q c t e
        split at h
        · rename_i hq
          split at h
          · rename_i c1 t1 e1 hc ht he
            cases h
            obtain ⟨ec, wc⟩ := ihT c (by omega) hc
            obtain ⟨et, wt⟩ := ihT t (by omega) ht
            obtain ⟨ee, we⟩ := ihT e (by omega) he
            simp [termTree, termWire, ec, wc, et, wt, ee, we, hq]
          · simp at h
        · simp at h
      · rename_i q
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨i, hi, rfl⟩ := h
        obtain ⟨e, w⟩ := u32Of_some hi
        simp [termTree, termWire, e, w]
    · intro cs hs fs h
      unfold fieldsOf at h
      split at h
      · cases h; simp [fieldsTree, fieldsWire]
      · rename_i p c cs
        split at h
        · rename_i ℓ t fs' hl ht hf
          cases h
          simp at hs
          obtain ⟨el, wl⟩ := labelOf_some hl
          obtain ⟨et, wt⟩ := ihT c (by omega) ht
          obtain ⟨ef, wf⟩ := ihR cs (by omega) hf
          simp [fieldsTree, fieldsWire, el, wl, et, wt, ef, wf]
        · simp at h
      · simp at h

theorem tree_of_termOf {t : Tree} {x : Term} (h : termOf t = some x) : termTree x = t ∧ termWire x = true :=
  (termOf_inv (sizeOf t + 1)).1 t (Nat.lt_succ_self _) h

/-! ## Packages -/

theorem labelsOf_map : (ls : List Label) → ls.all labelOk = true → labelsOf (ls.map labelLeaf) = some ls
  | [], _ => rfl
  | ℓ :: ls, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, labelLeaf, labelsOf, String.toUTF8_eq_toByteArray, labelOf_toUTF8 h.1,
      labelsOf_map ls h.2]

theorem map_of_labelsOf : (ts : List Tree) → ∀ {ls : List Label}, labelsOf ts = some ls →
    ls.map labelLeaf = ts ∧ ls.all labelOk = true
  | [], ls, h => by simp only [labelsOf, Option.some.injEq] at h; subst h; simp
  | t :: ts, ls, h => by
    unfold labelsOf at h
    split at h
    · simp_all
    · rename_i p ts' heq
      injection heq with h1 h2
      subst h1 h2
      split at h
      · rename_i ℓ ls' hl hs
        cases h
        obtain ⟨el, wl⟩ := labelOf_some hl
        obtain ⟨es, ws⟩ := map_of_labelsOf ts hs
        simp [labelLeaf, el, wl, es, ws]
      · simp at h
    · simp at h

theorem importsOf_map : (ds : List ByteArray) → ds.all (fun d => decide (d.size ≤ importBytesMax)) = true →
    importsOf (ds.map fun d => .node 0 d []) = some ds
  | [], _ => rfl
  | d :: ds, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [importsOf, h.1, importsOf_map ds h.2]

theorem map_of_importsOf : (ts : List Tree) → ∀ {ds : List ByteArray}, importsOf ts = some ds →
    ds.map (fun d => Tree.node 0 d []) = ts ∧ ds.all (fun d => decide (d.size ≤ importBytesMax)) = true
  | [], ds, h => by simp only [importsOf, Option.some.injEq] at h; subst h; simp
  | t :: ts, ds, h => by
    unfold importsOf at h
    split at h
    · simp_all
    · rename_i p ts' heq
      injection heq with h1 h2
      subst h1 h2
      split at h
      · rename_i hp
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨ds', hd, rfl⟩ := h
        obtain ⟨e, w⟩ := map_of_importsOf ts hd
        simp [e, w, hp]
      · simp at h
    · simp at h

theorem packageOf_packageTree {p : Package} (h : packageWire p = true) :
    packageOf (packageTree p) = some p := by
  simp only [packageWire, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hi, hs⟩, hf⟩, hb⟩, hm⟩, hl⟩ := h
  simp only [packageTree, packageOf, and_self, if_true, importsOf_map _ hi, tyOf_tyTree _ hs,
    tyOf_tyTree _ hf, termOf_termTree _ hb, labelsOf_map _ hm, labelsOf_map _ hl]

theorem tree_of_packageOf {t : Tree} {p : Package} (h : packageOf t = some p) :
    packageTree p = t ∧ packageWire p = true := by
  unfold packageOf at h
  split at h
  · rename_i e ei is s i b em ms el ls
    split at h
    · rename_i he
      split at h
      · rename_i imports state iface body methods laws hi hs hf hb hm hl
        cases h
        obtain ⟨ei', wi⟩ := map_of_importsOf is hi
        obtain ⟨es, ws⟩ := tree_of_tyOf hs
        obtain ⟨ef, wf⟩ := tree_of_tyOf hf
        obtain ⟨eb, wb⟩ := tree_of_termOf hb
        obtain ⟨em', wm⟩ := map_of_labelsOf ms hm
        obtain ⟨el', wl⟩ := map_of_labelsOf ls hl
        obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        simp [packageTree, packageWire, ei', es, ef, eb, em', el', wi, ws, wf, wb, wm, wl]
      · simp at h
    · simp at h
  · simp at h

/-- The package codec is canonical: a package has exactly one byte string, and those bytes decode
to it and to nothing else. -/
theorem decodePackage_eq_ok_iff {b : ByteArray} {p : Package} :
    decodePackage b = .ok p ↔ encodePackage p = some b := by
  constructor
  · intro h
    unfold decodePackage at h
    cases ht : packageStream.decode b with
    | error _ => simp [ht] at h
    | ok t =>
      cases hq : packageOf t.val with
      | none => simp [ht, hq] at h
      | some q =>
        simp only [ht, hq, Except.ok.injEq] at h
        subst h
        obtain ⟨et, wt⟩ := tree_of_packageOf hq
        have hb := (Stream.decode_eq_ok_iff (Stream.tree_lawful nodeMax depthMax (by decide))).mp ht
        have hfit : (packageTree q).fits nodeMax depthMax = true := et ▸ t.2
        have htq : (⟨packageTree q, hfit⟩ : Tree.Fitting nodeMax depthMax) = t := Subtype.ext et
        simp only [encodePackage, wt, if_true, dif_pos hfit, htq, hb]
        rfl
  · intro h
    unfold encodePackage at h
    split at h
    · rename_i hw
      split at h
      · rename_i hfit
        cases h
        unfold decodePackage
        rw [packageStream, Stream.decode_bytes (Stream.tree_lawful nodeMax depthMax (by decide))]
        simp only [packageOf_packageTree hw]
      · simp at h
    · simp at h

end Nanodregg.Lang.Wire
