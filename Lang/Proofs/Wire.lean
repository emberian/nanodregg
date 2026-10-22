/-
# Lang.Proofs.Wire — one package, one tree, one byte string

`tyOf`/`termOf`/`packageOf` read back exactly what `tyTree`/`termTree`/`packageTree` write for a
representable value (`*_of_tree`), and whatever they accept is the tree of what they return, which
is representable (`tree_of_*`). With `Codec.Stream.tree_lawful` that is canonicity of the package
codec: `decodePackage_eq_ok_iff : decodePackage b = .ok p ↔ encodePackage p = some b`.
-/
import Lang.Package
import Codec.Proofs.Tree
import Codec.Proofs.Raw

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
  simp only [u64Of, u64Bytes, Stream.decode_bytes Stream.u64be_lawful, UInt64.toNat_ofNat_of_lt' h]

theorem u64Of_some {p : ByteArray} {n : Nat} (h : u64Of p = some n) : u64Bytes n = p ∧ n < 2 ^ 64 := by
  unfold u64Of at h
  split at h
  · rename_i v hv
    cases h
    refine ⟨?_, v.toNat_lt⟩
    simp only [u64Bytes, UInt64.ofNat_toNat]
    exact (Stream.eq_bytes_of_decode Stream.u64be_lawful hv).symm
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
  | .refuse a w, h => by
    simp only [termWire] at h
    simp [termTree, termOf, tyOf_tyTree a h]
  | .hole n σ, h => by
    simp only [termWire, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [termTree, termOf, termsTree_length, h.1.2, u32Of_bytes h.1.1, termsOf_termsTree σ h.2]

theorem termsOf_termsTree : (ts : List Term) → termsWire ts = true →
    termsOf (termsTree ts) = some ts
  | [], _ => by simp [termsTree, termsOf]
  | t :: ts, h => by
    simp only [termsWire, Bool.and_eq_true] at h
    simp [termsTree, termsOf, termOf_termTree t h.1, termsOf_termsTree ts h.2]

theorem termsTree_length : (ts : List Term) → (termsTree ts).length = ts.length
  | [] => rfl
  | _ :: ts => by simp [termsTree, termsTree_length ts]

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

theorem termOf_inv_all (n : Nat) :
    (∀ (t : Tree), sizeOf t < n → ∀ {x : Term}, termOf t = some x → termTree x = t ∧ termWire x = true) ∧
    (∀ (cs : List Tree), sizeOf cs < n → ∀ {fs : List (Label × Term)}, fieldsOf cs = some fs →
      fieldsTree fs = cs ∧ fieldsWire fs = true) ∧
    (∀ (cs : List Tree), sizeOf cs < n → ∀ {ts : List Term}, termsOf cs = some ts →
      termsTree ts = cs ∧ termsWire ts = true) := by
  induction n with
  | zero => exact ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨ihT, ihR, ihL⟩ := ih
    refine ⟨?_, ?_, ?_⟩
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
      · rename_i q a
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨a1, ha, rfl⟩ := h
        obtain ⟨ea, wa⟩ := tree_of_tyOf ha
        simp [termTree, termWire, ea, wa]
      · rename_i q cs
        split at h
        · rename_i hc
          split at h
          · rename_i n ts hn ht
            cases h
            obtain ⟨en, wn⟩ := u32Of_some hn
            obtain ⟨et, wt⟩ := ihL cs (by omega) ht
            have hl : ts.length ≤ rowMax := by rw [← termsTree_length, et]; exact hc
            simp [termTree, termWire, en, wn, et, wt, hl]
          · simp at h
        · simp at h
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

    · intro cs hs ts h
      cases cs with
      | nil => simp only [termsOf, Option.some.injEq] at h; subst ts; simp [termsTree, termsWire]
      | cons c cs =>
        simp only [termsOf] at h
        split at h
        · rename_i t ts' ht hts
          cases h
          simp at hs
          obtain ⟨et, wt⟩ := ihT c (by omega) ht
          obtain ⟨es, ws⟩ := ihL cs (by omega) hts
          simp [termsTree, termsWire, et, wt, es, ws]
        · simp at h

theorem termOf_inv (n : Nat) :
    (∀ (t : Tree), sizeOf t < n → ∀ {x : Term}, termOf t = some x → termTree x = t ∧ termWire x = true) ∧
    (∀ (cs : List Tree), sizeOf cs < n → ∀ {fs : List (Label × Term)}, fieldsOf cs = some fs →
      fieldsTree fs = cs ∧ fieldsWire fs = true) := by
  exact ⟨(termOf_inv_all n).1, (termOf_inv_all n).2.1⟩

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

theorem optLabelOf_leaf : (o : Option Label) → o.all labelOk = true → optLabelOf (optLabelLeaf o) = some o
  | none, _ => by simp [optLabelLeaf, optLabelOf]
  | some ℓ, h => by
    simp only [Option.all_some] at h
    simp [optLabelLeaf, optLabelOf, String.toUTF8_eq_toByteArray, labelOf_toUTF8 h]

theorem tree_of_optLabelOf {t : Tree} {o : Option Label} (h : optLabelOf t = some o) :
    optLabelLeaf o = t ∧ o.all labelOk = true := by
  unfold optLabelOf at h
  split at h
  · split at h
    · rename_i he; cases h; subst he; simp [optLabelLeaf]
    · simp at h
  · rename_i p
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨ℓ, hl, rfl⟩ := h
    obtain ⟨el, wl⟩ := labelOf_some hl
    simp [optLabelLeaf, String.toUTF8_eq_toByteArray, el, wl]
  · simp at h

theorem keyFieldsOf_map : (fs : List (Label × Ty)) → fs.all (fun f => labelOk f.1 && tyWire f.2) = true →
    keyFieldsOf (fs.map fun f => .node 6 f.1.toByteArray [tyTree f.2]) = some fs
  | [], _ => rfl
  | (ℓ, T) :: fs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, keyFieldsOf, labelOf_toUTF8 h.1.1, tyOf_tyTree T h.1.2,
      keyFieldsOf_map fs h.2]

theorem map_of_keyFieldsOf : (ts : List Tree) → ∀ {fs : List (Label × Ty)}, keyFieldsOf ts = some fs →
    fs.map (fun f => Tree.node 6 f.1.toByteArray [tyTree f.2]) = ts ∧
      fs.all (fun f => labelOk f.1 && tyWire f.2) = true
  | [], fs, h => by simp only [keyFieldsOf, Option.some.injEq] at h; subst h; simp
  | t :: ts, fs, h => by
    unfold keyFieldsOf at h
    split at h
    · simp_all
    · rename_i p t' ts' heq
      injection heq with h1 h2
      subst h1 h2
      split at h
      · rename_i ℓ T fs' hl ht hs
        cases h
        obtain ⟨el, wl⟩ := labelOf_some hl
        obtain ⟨et, wt⟩ := tree_of_tyOf ht
        obtain ⟨es, ws⟩ := map_of_keyFieldsOf ts hs
        simp [el, wl, et, wt, es, ws]
      · simp at h
    · simp at h

theorem relOf_relTree (r : Label × RelDecl) (h : relWire r = true) : relOf (relTree r) = some r := by
  obtain ⟨ℓ, ⟨key, val, limit, sum, cap, retract, guard⟩⟩ := r
  simp only [relWire, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hl, hk⟩, hv⟩, hlim⟩, hcap⟩, hsu⟩, hg⟩ := h
  cases retract <;>
    simp [relTree, relOf, String.toUTF8_eq_toByteArray, labelOf_toUTF8 hl, keyFieldsOf_map _ hk,
      tyOf_tyTree _ hv, u64Of_bytes hlim, u64Of_bytes hcap, optLabelOf_leaf _ hsu, optLabelOf_leaf _ hg]

theorem tree_of_relOf {t : Tree} {r : Label × RelDecl} (h : relOf t = some r) :
    relTree r = t ∧ relWire r = true := by
  unfold relOf at h
  split at h
  · rename_i p ek ks v lim su ca rt er gu
    split at h
    · rename_i hc
      split at h
      · rename_i ℓ key val limit sum cap guard hl hk hv hlim hsu hca hg
        cases h
        obtain ⟨el, wl⟩ := labelOf_some hl
        obtain ⟨ek', wk⟩ := map_of_keyFieldsOf ks hk
        obtain ⟨ev, wv⟩ := tree_of_tyOf hv
        obtain ⟨elim, wlim⟩ := u64Of_some hlim
        obtain ⟨esu, wsu⟩ := tree_of_optLabelOf hsu
        obtain ⟨eca, wca⟩ := u64Of_some hca
        obtain ⟨eg, wg⟩ := tree_of_optLabelOf hg
        obtain ⟨rfl, rfl, hrt⟩ := hc
        rcases hrt with rfl | rfl <;>
          simp [relTree, relWire, String.toUTF8_eq_toByteArray, el, wl, ek', wk, ev, wv, elim, wlim,
            esu, wsu, eca, wca, eg, wg]
      · simp at h
    · simp at h
  · simp at h

theorem relsOf_map : (rs : List (Label × RelDecl)) → rs.all relWire = true → relsOf (rs.map relTree) = some rs
  | [], _ => rfl
  | r :: rs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, relsOf, relOf_relTree r h.1, relsOf_map rs h.2]

theorem map_of_relsOf : (ts : List Tree) → ∀ {rs : List (Label × RelDecl)}, relsOf ts = some rs →
    rs.map relTree = ts ∧ rs.all relWire = true
  | [], rs, h => by simp only [relsOf, Option.some.injEq] at h; subst h; simp
  | t :: ts, rs, h => by
    simp only [relsOf] at h
    split at h
    · rename_i r rs' hr hs
      cases h
      obtain ⟨e1, w1⟩ := tree_of_relOf hr
      obtain ⟨e2, w2⟩ := map_of_relsOf ts hs
      simp [e1, w1, e2, w2]
    · simp at h

/-! ### Contextual ROM declarations (version 4; cell pins since version 5) -/

theorem mapM_encoded {α β : Type} (enc : α → β) (dec : β → Option α) (ok : α → Bool)
    (law : ∀ a, ok a = true → dec (enc a) = some a) :
    ∀ (xs : List α), xs.all ok = true → (xs.map enc).mapM dec = some xs
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      simp [law x h.1, mapM_encoded enc dec ok law xs h.2]

theorem mapM_decoded {α β : Type} (enc : α → β) (dec : β → Option α) (ok : α → Bool)
    (law : ∀ b a, dec b = some a → enc a = b ∧ ok a = true) :
    ∀ (bs : List β) (xs : List α), bs.mapM dec = some xs → xs.map enc = bs ∧ xs.all ok = true
  | [], xs, h => by simp at h; subst xs; simp
  | b :: bs, xs, h => by
      simp only [List.mapM_cons, bind, Option.bind] at h
      cases hd : dec b with
      | none => simp [hd] at h
      | some x =>
        cases hs : bs.mapM dec with
        | none => simp [hd, hs] at h
        | some ys =>
          simp [hd, hs] at h
          subst xs
          obtain ⟨he, hw⟩ := law b x hd
          obtain ⟨hes, hws⟩ := mapM_decoded enc dec ok law bs ys hs
          simp [he, hw, hes, hws]

theorem supportPinOf_tree {p : SupportPin} (h : supportPinWire p = true) :
    supportPinOf (supportPinTree p) = some p := by
  cases p with
  | row rel key ver =>
    simp only [supportPinWire, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [supportPinTree, supportPinOf, u32Of_bytes h.1, u64Of_bytes h.2]
  | cell id => rfl

theorem tree_of_supportPinOf {t : Tree} {p : SupportPin} (h : supportPinOf t = some p) :
    supportPinTree p = t ∧ supportPinWire p = true := by
  unfold supportPinOf at h
  split at h
  · split at h
    · rename_i r v hr hv
      cases h
      obtain ⟨er, wr⟩ := u32Of_some hr
      obtain ⟨ev, wv⟩ := u64Of_some hv
      simp [supportPinTree, supportPinWire, er, ev, wr, wv]
    · simp at h
  · cases h
    simp [supportPinTree, supportPinWire]
  · simp at h

theorem supportOptPinOf_tree {p : Option SupportPin} (h : p.all supportPinWire = true) :
    supportOptPinOf (supportOptPinTree p) = some p := by
  cases p with
  | none => rfl
  | some p => simp [supportOptPinTree, supportOptPinOf, supportPinOf_tree h]

theorem tree_of_supportOptPinOf {t : Tree} {p : Option SupportPin} (h : supportOptPinOf t = some p) :
    supportOptPinTree p = t ∧ p.all supportPinWire = true := by
  unfold supportOptPinOf at h
  split at h
  · split at h
    · rename_i he
      cases h
      simp [supportOptPinTree, he]
    · simp at h
  · split at h
    · rename_i he
      rename_i ep tp
      cases hd : supportPinOf tp with
      | none => simp [hd] at h
      | some q =>
        simp [hd] at h
        subst p
        obtain ⟨eq, wq⟩ := tree_of_supportPinOf hd
        simp [supportOptPinTree, he, eq, wq]
    · simp at h
  · simp at h

theorem holeCodeOf_tree {c : HoleCode} (h : holeCodeWire c = true) :
    holeCodeOf (holeCodeTree c) = some c := by
  simp only [holeCodeWire, Bool.and_eq_true] at h
  simp [holeCodeTree, holeCodeOf, termOf_termTree _ h.1,
    mapM_encoded supportPinTree supportPinOf supportPinWire (fun _ => supportPinOf_tree) _ h.2]

theorem tree_of_holeCodeOf {t : Tree} {c : HoleCode} (h : holeCodeOf t = some c) :
    holeCodeTree c = t ∧ holeCodeWire c = true := by
  unfold holeCodeOf at h
  split at h
  · split at h
    · rename_i he
      split at h
      · rename_i b ps hb hp
        cases h
        obtain ⟨eb, wb⟩ := tree_of_termOf hb
        obtain ⟨ep, wp⟩ := mapM_decoded supportPinTree supportPinOf supportPinWire
          (fun _ _ => tree_of_supportPinOf) _ _ hp
        obtain ⟨rfl, rfl⟩ := he
        simp [holeCodeTree, holeCodeWire, eb, wb, ep, wp]
      · simp at h
    · simp at h
  · simp at h

theorem holeROMOf_tree {r : HoleROM} (h : holeROMWire r = true) :
    holeROMOf (holeROMTree r) = some r := by
  simp only [holeROMWire, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hn, hc⟩, ht⟩, hk⟩, hr⟩, hh⟩, hp⟩, hg⟩ := h
  simp [holeROMTree, holeROMOf, u32Of_bytes hn, u32Of_bytes hr,
    mapM_encoded tyTree tyOf tyWire tyOf_tyTree _ hc, tyOf_tyTree _ ht,
    mapM_encoded holeCodeTree holeCodeOf holeCodeWire (fun _ => holeCodeOf_tree) _ hk,
    mapM_encoded supportOptPinTree supportOptPinOf (Option.all supportPinWire) (fun _ => supportOptPinOf_tree) _ hh,
    supportOptPinOf_tree hp, termOf_termTree _ hg]

theorem tree_of_holeROMOf {t : Tree} {r : HoleROM} (h : holeROMOf t = some r) :
    holeROMTree r = t ∧ holeROMWire r = true := by
  unfold holeROMOf at h
  split at h
  · split at h
    · rename_i he
      split at h
      · rename_i n cs ty ks sr hs gp g hn hc ht hk hr hh hp hg
        cases h
        obtain ⟨en, wn⟩ := u32Of_some hn
        obtain ⟨ec, wc⟩ := mapM_decoded tyTree tyOf tyWire (fun _ _ => tree_of_tyOf) _ _ hc
        obtain ⟨et, wt⟩ := tree_of_tyOf ht
        obtain ⟨ek, wk⟩ := mapM_decoded holeCodeTree holeCodeOf holeCodeWire
          (fun _ _ => tree_of_holeCodeOf) _ _ hk
        obtain ⟨er, wr⟩ := u32Of_some hr
        obtain ⟨eh, wh⟩ := mapM_decoded supportOptPinTree supportOptPinOf (Option.all supportPinWire)
          (fun _ _ => tree_of_supportOptPinOf) _ _ hh
        obtain ⟨ep, wp⟩ := tree_of_supportOptPinOf hp
        obtain ⟨eg, wg⟩ := tree_of_termOf hg
        obtain ⟨rfl, rfl, rfl⟩ := he
        simp [holeROMTree, holeROMWire, en, wn, ec, wc, et, wt, ek, wk, er, wr, eh, wh, ep, wp, eg, wg]
      · simp at h
    · simp at h
  · simp at h

theorem packageOf_packageTree {p : Package} (h : packageWire p = true) :
    packageOf (packageTree p) = some p := by
  simp only [packageWire, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hd, hi⟩, hs⟩, hf⟩, hb⟩, hm⟩, hl⟩, hr⟩, hh⟩ := h
  simp only [packageTree, packageOf, hd, and_self, if_true, importsOf_map _ hi, tyOf_tyTree _ hs,
    tyOf_tyTree _ hf, termOf_termTree _ hb, labelsOf_map _ hm, labelsOf_map _ hl, relsOf_map _ hr,
    mapM_encoded holeROMTree holeROMOf holeROMWire (fun _ => holeROMOf_tree) _ hh]

theorem tree_of_packageOf {t : Tree} {p : Package} (h : packageOf t = some p) :
    packageTree p = t ∧ packageWire p = true := by
  unfold packageOf at h
  split at h
  · rename_i e ei is s i b em ms el ls er rs doc eh hs
    split at h
    · rename_i he
      split at h
      · rename_i imports state iface body methods laws rels holes hi hs hf hb hm hl hr hh
        cases h
        obtain ⟨ei', wi⟩ := map_of_importsOf is hi
        obtain ⟨es, ws⟩ := tree_of_tyOf hs
        obtain ⟨ef, wf⟩ := tree_of_tyOf hf
        obtain ⟨eb, wb⟩ := tree_of_termOf hb
        obtain ⟨em', wm⟩ := map_of_labelsOf ms hm
        obtain ⟨el', wl⟩ := map_of_labelsOf ls hl
        obtain ⟨er', wr⟩ := map_of_relsOf rs hr
        obtain ⟨eh', wh⟩ := mapM_decoded holeROMTree holeROMOf holeROMWire
          (fun _ _ => tree_of_holeROMOf) _ _ hh
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, hd⟩ := he
        simp [packageTree, packageWire, ei', es, ef, eb, em', el', er', wi, ws, wf, wb, wm, wl, wr, hd, eh', wh]
      · simp at h
    · simp at h
  · simp at h

/-! ### The version byte (LANG-60) -/

/-- **The package codec's label is `lang/package/N` at version N**: bumping `packageWireVersion` without
moving the label (or the reverse) fails here, so the vectors' tag moves with every version (a
refine's shape carries its name, not its accept function). -/
theorem packageCodec_label :
    ∃ s, packageCodec.shape = .refine s!"lang/package/{Bounds.packageWireVersion.toNat}" s := ⟨_, rfl⟩

/-- No version is 0: 0 is the first byte of every unversioned package. -/
theorem packageWireVersion_ne_zero : Bounds.packageWireVersion ≠ 0 := by decide

/-- **`lang/package-version/5` reads exactly the one byte `packageWireVersion`.** -/
theorem packageVersion_lawful : Stream.Lawful packageVersion :=
  Stream.refine_lawful Stream.u8_lawful "lang/package-version/5" (fun y => by cases y; exact if_pos rfl)
    (fun x _ h => by
      split at h
      · rename_i hx; exact hx.symm
      · cases h)

theorem treeStream_lawful : Stream.Lawful treeStream := Stream.tree_lawful nodeMax depthMax (by decide)

theorem packageStream_lawful : Stream.Lawful packageStream :=
  Stream.product_lawful packageVersion_lawful treeStream_lawful

/-- A package's bytes begin with the version byte. -/
theorem packageStream_bytes (t : Tree.Fitting nodeMax depthMax) :
    packageStream.bytes ((), t) = ByteArray.mk #[Bounds.packageWireVersion] ++ treeStream.bytes t := by
  rw [packageStream, Stream.product_bytes treeStream_lawful]; rfl

/-- **A byte other than `packageWireVersion` where a package starts is refused `lang/package-version/5` by
name**, before any tree is read. -/
theorem packageStream_get_wrong_version {b : ByteArray} {i : Nat} (hi : i < b.size)
    (hv : b[i] ≠ Bounds.packageWireVersion) :
    packageStream.get b i = .error (.rejected i "lang/package-version/5") := by
  simp [packageStream, Stream.product, packageVersion, Stream.refine, Stream.u8, hi, hv]

/-- **Bytes at the wrong version are never a package**: `decodePackage` refuses them
`lang/package-version/5`, so bytes written under an earlier package wire are refused, never reinterpreted. -/
theorem decodePackage_wrong_version {b : ByteArray} (h0 : 0 < b.size)
    (hv : b[0] ≠ Bounds.packageWireVersion) :
    decodePackage b = .error (.rejected 0 "lang/package-version/5") := by
  simp [decodePackage, Stream.decode, packageStream_get_wrong_version h0 hv]

/-- Every package written before LANG-60 was `treeStream.bytes` of a node-0 root: its first byte is 0. -/
theorem treeStream_bytes_node0 {e : ByteArray} {cs : List Tree} (h : (Tree.node 0 e cs).fits nodeMax depthMax = true) :
    ∃ h0 : 0 < (treeStream.bytes ⟨.node 0 e cs, h⟩).size, (treeStream.bytes ⟨.node 0 e cs, h⟩)[0] = 0 := by
  have hb : treeStream.bytes ⟨.node 0 e cs, h⟩ = Tree.putD (1023 + 1) (.node 0 e cs) ByteArray.empty := rfl
  rw [hb, Tree.putD_node]
  refine ⟨by simp [ByteArray.size_append, Stream.u8, Stream.bytes]; omega, ?_⟩
  simp [ByteArray.append_assoc, Stream.u8, Stream.bytes, ByteArray.getElem_append_left]
  rfl

/-- **Every unversioned package is refused `lang/package-version/5`**: the bytes of any node-0 package
tree as `lang/package` and `lang/package/2` wrote them (no version byte) are never decoded, so no
package of an earlier wire is read as a different one. -/
theorem unversioned_package_refused {e : ByteArray} {cs : List Tree}
    (h : (Tree.node 0 e cs).fits nodeMax depthMax = true) :
    decodePackage (treeStream.bytes ⟨.node 0 e cs, h⟩) = .error (.rejected 0 "lang/package-version/5") := by
  obtain ⟨h0, hb⟩ := treeStream_bytes_node0 h
  exact decodePackage_wrong_version h0 (by rw [hb]; exact packageWireVersion_ne_zero.symm)

theorem decodePackage_wrong_version_not_ok {b : ByteArray} (h0 : 0 < b.size)
    (hv : b[0] ≠ Bounds.packageWireVersion) (p : Package) : decodePackage b ≠ .ok p := by
  rw [decodePackage_wrong_version h0 hv]; simp

/-- The codec refuses them by the same name. -/
theorem packageCodec_wrong_version {b : ByteArray} (h0 : 0 < b.size)
    (hv : b[0] ≠ Bounds.packageWireVersion) :
    packageCodec.decode b = .error (.rejected 0 "lang/package-version/5") := by
  simp [packageCodec, Stream.decode, Stream.refine, packageStream_get_wrong_version h0 hv]

private theorem packageFit_eq {p : Package} (h : (packageTree p).fits nodeMax depthMax = true) :
    packageFit p = ⟨packageTree p, h⟩ := by
  simp [packageFit, h]

private theorem packageCodec_bytes {p : Package} (h : (packageTree p).fits nodeMax depthMax = true) :
    packageCodec.bytes p = packageStream.bytes ((), ⟨packageTree p, h⟩) := by
  show packageStream.put ((), packageFit p) ByteArray.empty = _
  rw [packageFit_eq h]; rfl

/-- **Every package's bytes begin with the current version** (the twin of
`decodePackage_wrong_version`: what `encodePackage` writes is never refused `lang/package-version/5`). -/
theorem encodePackage_version {p : Package} {b : ByteArray} (h : encodePackage p = some b) :
    ∃ h0 : 0 < b.size, b[0] = Bounds.packageWireVersion := by
  unfold encodePackage at h
  split at h
  · split at h
    · rename_i hfit
      cases h
      rw [packageCodec_bytes hfit, packageStream_bytes]
      refine ⟨by simp [ByteArray.size_append]; omega, ?_⟩
      simp [ByteArray.getElem_append_left]
    · cases h
  · cases h

/-- **`lang/package/5` is lawful on exactly the packages that have a tree in bounds** (`packageWire` and
`fits`): those round-trip, and whatever it reads is one of them, spelled one way, at the current
version. -/
theorem packageCodec_lawfulOn :
    Stream.LawfulOn (fun p => packageWire p = true ∧ (packageTree p).fits nodeMax depthMax = true) packageCodec := by
  refine (Stream.refine_lawfulOn_where packageStream_lawful.on "lang/package/5"
    (Q := fun p => packageWire p = true ∧ (packageTree p).fits nodeMax depthMax = true) ?_ ?_ ?_).mono
    (fun _ h => h.2) (fun _ h => ⟨trivial, h⟩)
  · intro y _ hq
    show packageOf (packageFit y).val = some y
    rw [packageFit_eq hq.2]
    exact packageOf_packageTree hq.1
  · intro x y h
    obtain ⟨et, -⟩ := tree_of_packageOf h
    have hfit : (packageTree y).fits nodeMax depthMax = true := et ▸ x.2.2
    show ((), packageFit y) = x
    rw [packageFit_eq hfit]
    exact Prod.ext rfl (Subtype.ext et)
  · intro x y h
    obtain ⟨et, wt⟩ := tree_of_packageOf h
    exact ⟨wt, et ▸ x.2.2⟩

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
      cases hq : packageOf t.2.val with
      | none => simp [ht, hq] at h
      | some q =>
        simp only [ht, hq, Except.ok.injEq] at h
        subst h
        obtain ⟨et, wt⟩ := tree_of_packageOf hq
        have hb := (Stream.decode_eq_ok_iff packageStream_lawful).mp ht
        have hfit : (packageTree q).fits nodeMax depthMax = true := et ▸ t.2.2
        have htq : (((), ⟨packageTree q, hfit⟩) : Unit × Tree.Fitting nodeMax depthMax) = t :=
          Prod.ext rfl (Subtype.ext et)
        simp only [encodePackage, wt, if_true, hfit, packageCodec_bytes hfit, htq, hb]
  · intro h
    unfold encodePackage at h
    split at h
    · rename_i hw
      split at h
      · rename_i hfit
        cases h
        unfold decodePackage
        rw [packageCodec_bytes hfit, Stream.decode_bytes packageStream_lawful]
        simp only [packageOf_packageTree hw]
      · simp at h
    · simp at h


/-- `decodePackage` accepts exactly what the `lang/package/5` codec reads (they differ only in which
refusal names an input that is both a non-package tree and followed by trailing bytes). -/
theorem decodePackage_eq_codec {b : ByteArray} {p : Package} :
    decodePackage b = .ok p ↔ packageCodec.decode b = .ok p := by
  rw [decodePackage_eq_ok_iff, packageCodec_lawfulOn.decode_eq_ok_iff]
  unfold encodePackage
  constructor
  · intro h
    split at h
    · rename_i hw
      split at h
      · rename_i hfit; cases h; exact ⟨⟨hw, hfit⟩, rfl⟩
      · cases h
    · cases h
  · rintro ⟨⟨hw, hfit⟩, rfl⟩
    simp [hw, hfit]

/-- A package tree around a body tree (the teeth below). -/
private def bodyTree (body : Tree) : Tree :=
  .node 0 .empty [.node 0 .empty [], tyTree (.record []), tyTree (.record []), body, .node 1 .empty [],
    .node 1 .empty [], .node 2 .empty [], .node 0 .empty [], .node 3 .empty []]

/-- `decodePackage`'s refusal of a tree that is no package carries the codec's label, `lang/package/N`
at version N, like `packageCodec_label`: the decoder's spelling of the name moves with the version too. -/
theorem decodePackage_refused_label {b : ByteArray} {t : Unit × Tree.Fitting nodeMax depthMax}
    (h : packageStream.decode b = .ok t) (hn : packageOf t.2.val = none) :
    decodePackage b = .error (.rejected 0 s!"lang/package/{Bounds.packageWireVersion.toNat}") := by
  simp only [decodePackage, h, hn]; rfl

/-- **`lang/package/5` refuses by name every tree `packageOf` does not read.** -/
theorem packageCodec_get_refused {b : ByteArray} {i j : Nat} {t : Unit × Tree.Fitting nodeMax depthMax}
    (h : packageStream.get b i = .ok (t, j)) (hn : packageOf t.2.val = none) :
    packageCodec.get b i = .error (.rejected i "lang/package/5") := by
  simp [packageCodec, Stream.refine, h, hn]

/-- The plant: a body node of term tag 19 (no term has it) is no package, so `lang/package/5` refuses it
(`packageCodec_get_refused`; the codec vectors' boundary row is a tree of the same layout). -/
theorem package_refuses_unknown_term_tag : (packageOf (bodyTree (.node 19 .empty []))).isNone = true := by
  decide +kernel

/-- `lang/package/5`'s domain is inhabited: the empty package has a tree in bounds. -/
theorem empty_package_fits :
    packageWire ⟨[], .record [], .record [], .record [], [], [], [], .empty, []⟩ = true ∧
      (packageTree ⟨[], .record [], .record [], .record [], [], [], [], .empty, []⟩).fits nodeMax depthMax = true := by
  decide +kernel

/-- A doc holding a control character (a line feed) or bytes that are not UTF-8 is no doc. -/
theorem newline_doc_refused : Bounds.docOk ⟨#[0x61, 0x0a, 0x62]⟩ = false := by decide +kernel
theorem nonUtf8_doc_refused : Bounds.docOk ⟨#[0x61, 0xff]⟩ = false := by decide +kernel

/-- A package tree around a doc leaf (the decoder's doc teeth). -/
private def docTree (doc : ByteArray) : Tree :=
  .node 0 .empty [.node 0 .empty [], tyTree (.record []), tyTree (.record []), termTree (.record []),
    .node 1 .empty [], .node 1 .empty [], .node 2 .empty [], .node 0 doc [], .node 3 .empty []]

/-- The decoder refuses a tree whose doc holds a line feed or is not UTF-8; its twin with a plain doc
reads. -/
theorem package_refuses_newline_doc : (packageOf (docTree ⟨#[0x61, 0x0a, 0x62]⟩)).isNone = true := by
  decide +kernel
theorem package_refuses_nonUtf8_doc : (packageOf (docTree ⟨#[0x61, 0xff]⟩)).isNone = true := by
  decide +kernel
theorem package_reads_plain_doc : (packageOf (docTree ⟨#[0x61, 0x62]⟩)).isSome = true := by
  decide +kernel

/-- The twin: the same package with the body `record []` reads. -/
theorem package_reads_known_term_tag : (packageOf (bodyTree (termTree (.record [])))).isSome = true := by
  decide +kernel

end Nanodregg.Lang.Wire
