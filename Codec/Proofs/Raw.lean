import Codec.Raw
import Codec.Proofs.Stream

/-! # Lawful on a domain

`LawfulOn P c` is `Lawful c` with the read-back law restricted to values satisfying `P`, and with
every value read back proved to satisfy `P`. The canonicity half (`occurs_of_get`) is unrestricted:
whatever is read was spelled exactly one way. `Lawful c` is `LawfulOn (fun _ => True) c`
(`Lawful.on`). -/

namespace Nanodregg.Codec.Stream

variable {α β : Type}

structure LawfulOn (P : α → Prop) (c : Stream α) : Prop where
  put_eq : ∀ v buf, c.put v buf = buf ++ c.bytes v
  size_eq : ∀ v, c.size v = (c.bytes v).size
  get_of_occurs : ∀ v b i, P v → OccursAt b i (c.bytes v) → c.get b i = .ok (v, i + (c.bytes v).size)
  occurs_of_get : ∀ {b i v j}, c.get b i = .ok (v, j) →
    P v ∧ j = i + (c.bytes v).size ∧ OccursAt b i (c.bytes v)

theorem Lawful.on {c : Stream α} (h : Lawful c) : LawfulOn (fun _ => True) c where
  put_eq := h.put_eq
  size_eq := h.size_eq
  get_of_occurs v b i _ o := h.get_of_occurs v b i o
  occurs_of_get g := ⟨trivial, h.occurs_of_get g⟩

theorem LawfulOn.mono {P Q : α → Prop} {c : Stream α} (h : LawfulOn P c) (hpq : ∀ v, P v → Q v)
    (hqp : ∀ v, Q v → P v) : LawfulOn Q c where
  put_eq := h.put_eq
  size_eq := h.size_eq
  get_of_occurs v b i hq o := h.get_of_occurs v b i (hqp v hq) o
  occurs_of_get g := let ⟨hp, r⟩ := h.occurs_of_get g; ⟨hpq _ hp, r⟩

/-! ## Whole input -/

theorem LawfulOn.decode_bytes {P : α → Prop} {c : Stream α} (h : LawfulOn P c) {v : α} (hv : P v) :
    c.decode (c.bytes v) = .ok v := by
  unfold decode
  rw [h.get_of_occurs v _ 0 hv (occursAt_self _), Nat.zero_add]
  simp

theorem LawfulOn.eq_bytes_of_decode {P : α → Prop} {c : Stream α} (h : LawfulOn P c) {b : ByteArray}
    {v : α} (hd : c.decode b = .ok v) : P v ∧ b = c.bytes v := by
  unfold decode at hd
  split at hd
  · rename_i w j hget
    split at hd
    · rename_i hj
      cases hd
      obtain ⟨hp, hj', hocc⟩ := h.occurs_of_get hget
      exact ⟨hp, eq_of_occursAt_zero hocc (by omega)⟩
    · cases hd
  · cases hd

theorem LawfulOn.decode_eq_ok_iff {P : α → Prop} {c : Stream α} (h : LawfulOn P c) {b : ByteArray}
    {v : α} : c.decode b = .ok v ↔ P v ∧ b = c.bytes v :=
  ⟨h.eq_bytes_of_decode, fun ⟨hp, hb⟩ => hb ▸ h.decode_bytes hp⟩

theorem LawfulOn.bytes_injective {P : α → Prop} {c : Stream α} (h : LawfulOn P c) {v w : α}
    (hv : P v) (hw : P w) (hb : c.bytes v = c.bytes w) : v = w := by
  have := h.decode_bytes hv
  rw [hb, h.decode_bytes hw] at this
  cases this; rfl

/-! ## Primitives -/

theorem nat64_bytes (n : Nat) : nat64.bytes n = u64.bytes (UInt64.ofNat n) := rfl
theorem nat32_bytes (n : Nat) : nat32.bytes n = u32.bytes (UInt32.ofNat n) := rfl

theorem nat64_lawfulOn : LawfulOn (· < 2 ^ 64) nat64 where
  put_eq n buf := u64_lawful.put_eq _ buf
  size_eq _ := rfl
  get_of_occurs n b i hn o := by
    rw [nat64_bytes] at o ⊢
    have g := u64_lawful.get_of_occurs _ b i o
    simp only [nat64, g]
    rw [UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hn)]
  occurs_of_get {b i v j} g := by
    simp only [nat64] at g
    split at g
    · rename_i w k hw
      cases g
      obtain ⟨rfl, o⟩ := u64_lawful.occurs_of_get hw
      rw [nat64_bytes, UInt64.ofNat_toNat]
      exact ⟨w.toNat_lt, rfl, o⟩
    · cases g

theorem nat32_lawfulOn : LawfulOn (· < 2 ^ 32) nat32 where
  put_eq n buf := u32_lawful.put_eq _ buf
  size_eq _ := rfl
  get_of_occurs n b i hn o := by
    rw [nat32_bytes] at o ⊢
    have g := u32_lawful.get_of_occurs _ b i o
    simp only [nat32, g]
    rw [UInt32.toNat_ofNat_of_lt' (by simpa [UInt32.size] using hn)]
  occurs_of_get {b i v j} g := by
    simp only [nat32] at g
    split at g
    · rename_i w k hw
      cases g
      obtain ⟨rfl, o⟩ := u32_lawful.occurs_of_get hw
      rw [nat32_bytes, UInt32.ofNat_toNat]
      exact ⟨w.toNat_lt, rfl, o⟩
    · cases g

theorem rawBytes_bytes (max : Nat) (v : ByteArray) :
    (rawBytes max).bytes v = u32.bytes (UInt32.ofNat v.size) ++ v := by
  show u32.put _ ByteArray.empty ++ v = _
  rw [u32_lawful.put_eq, ByteArray.empty_append]

theorem rawBytes_lawfulOn (max : Nat) (fits : max < 2 ^ 32) : LawfulOn (·.size ≤ max) (rawBytes max) where
  put_eq v buf := by
    rw [rawBytes_bytes]
    show u32.put _ buf ++ v = _
    rw [u32_lawful.put_eq, ByteArray.append_assoc]
  size_eq v := by rw [rawBytes_bytes, ByteArray.size_append]; rfl
  get_of_occurs v b i hv h := by
    rw [rawBytes_bytes] at h ⊢
    obtain ⟨h1, ⟨hs, he⟩⟩ := occursAt_append.mp h
    have hn : (UInt32.ofNat v.size).toNat = v.size :=
      UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)
    rw [u32_size] at hs he
    have hget := u32_lawful.get_of_occurs _ _ _ h1
    rw [u32_size] at hget
    simp only [rawBytes, hget, hn, hv, ↓reduceIte, hs, ByteArray.size_append, u32_size,
      ← Nat.add_assoc, he]
  occurs_of_get {b i v j} h := by
    simp only [rawBytes] at h
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
          rw [rawBytes_bytes]
          simp only [hsz, UInt32.ofNat_toNat]
          refine ⟨by omega, by simp [ByteArray.size_append, hsz]; omega, occursAt_append.mpr ⟨o1, ?_⟩⟩
          simp only [u32_size]
          exact ⟨by rw [hsz]; exact hb, by rw [hsz]⟩
        · cases h
      · cases h

/-! ## Combinators on domains -/

theorem product_lawfulOn {Pa : α → Prop} {Pc : β → Prop} {a : Stream α} {c : Stream β}
    (ha : LawfulOn Pa a) (hc : LawfulOn Pc c) : LawfulOn (fun v => Pa v.1 ∧ Pc v.2) (product a c) where
  put_eq v buf := by
    have hb : (product a c).bytes v = a.bytes v.1 ++ c.bytes v.2 := by
      simp only [bytes, product]; rw [hc.put_eq, ← bytes, ← bytes]
    rw [hb]; simp only [product]; rw [hc.put_eq, ha.put_eq, ByteArray.append_assoc]
  size_eq v := by
    have hb : (product a c).bytes v = a.bytes v.1 ++ c.bytes v.2 := by
      simp only [bytes, product]; rw [hc.put_eq, ← bytes, ← bytes]
    rw [hb, ByteArray.size_append, ← ha.size_eq, ← hc.size_eq]; rfl
  get_of_occurs v b i hv h := by
    have hb : (product a c).bytes v = a.bytes v.1 ++ c.bytes v.2 := by
      simp only [bytes, product]; rw [hc.put_eq, ← bytes, ← bytes]
    rw [hb] at h ⊢
    obtain ⟨h1, h2⟩ := occursAt_append.mp h
    simp only [product, ha.get_of_occurs _ _ _ hv.1 h1, hc.get_of_occurs _ _ _ hv.2 h2,
      ByteArray.size_append, Nat.add_assoc]
  occurs_of_get {b i v j} h := by
    simp only [product] at h
    split at h
    · cases h
    · rename_i x k hx
      split at h
      · rename_i y m hy
        cases h
        obtain ⟨px, rfl, ox⟩ := ha.occurs_of_get hx
        obtain ⟨py, rfl, oy⟩ := hc.occurs_of_get hy
        have hb : (product a c).bytes (x, y) = a.bytes x ++ c.bytes y := by
          simp only [bytes, product]; rw [hc.put_eq, ← bytes, ← bytes]
        rw [hb]
        exact ⟨⟨px, py⟩, by simp [ByteArray.size_append, Nat.add_assoc], occursAt_append.mpr ⟨ox, oy⟩⟩
      · cases h

theorem refine_lawfulOn {P : α → Prop} {c : Stream α} (hc : LawfulOn P c) (name : String)
    {accept : α → Option β} {back : β → α}
    (accept_back : ∀ y, P (back y) → accept (back y) = some y)
    (back_accept : ∀ x y, accept x = some y → back y = x) :
    LawfulOn (fun y => P (back y)) (refine name c accept back) where
  put_eq v buf := by simp only [refine]; exact hc.put_eq _ _
  size_eq v := hc.size_eq (back v)
  get_of_occurs v b i hv h := by
    rw [refine_bytes] at h ⊢
    simp [refine, hc.get_of_occurs _ _ _ hv h, accept_back _ hv]
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

theorem tagged_lawfulOn {σ : Type} {F : σ → Type} (all : List σ) {code : σ → UInt8}
    {ofCode? : UInt8 → Option σ} {c : (s : σ) → Stream (F s)} {P : (s : σ) → F s → Prop}
    (hc : ∀ s, LawfulOn (P s) (c s))
    (of_code : ∀ s, ofCode? (code s) = some s) (code_of : ∀ t s, ofCode? t = some s → code s = t) :
    LawfulOn (fun v => P v.1 v.2) (tagged all code ofCode? c) where
  put_eq v buf := by
    have hb : (tagged all code ofCode? c).bytes v = u8.bytes (code v.1) ++ (c v.1).bytes v.2 := by
      simp only [bytes, tagged]; rw [(hc v.1).put_eq]; rfl
    rw [hb]; simp only [tagged]
    rw [(hc v.1).put_eq, push_eq_append, ByteArray.append_assoc]; rfl
  size_eq v := by
    have hb : (tagged all code ofCode? c).bytes v = u8.bytes (code v.1) ++ (c v.1).bytes v.2 := by
      simp only [bytes, tagged]; rw [(hc v.1).put_eq]; rfl
    rw [hb, ByteArray.size_append, ← (hc v.1).size_eq]; rfl
  get_of_occurs v b i hv h := by
    have hb : (tagged all code ofCode? c).bytes v = u8.bytes (code v.1) ++ (c v.1).bytes v.2 := by
      simp only [bytes, tagged]; rw [(hc v.1).put_eq]; rfl
    rw [hb] at h ⊢
    obtain ⟨h1, h2⟩ := occursAt_append.mp h
    have h2' : OccursAt b (i + 1) ((c v.1).bytes v.2) := h2
    simp [tagged, u8_lawful.get_of_occurs _ _ _ h1, of_code, (hc v.1).get_of_occurs _ _ _ hv h2',
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
          obtain ⟨pw, rfl, o2⟩ := (hc s).occurs_of_get hw
          have hb : (tagged all code ofCode? c).bytes ⟨s, w⟩ = u8.bytes (code s) ++ (c s).bytes w := by
            simp only [bytes, tagged]; rw [(hc s).put_eq]; rfl
          rw [hb]
          simp only [code_of _ _ hs]
          exact ⟨pw, by simp [ByteArray.size_append, Nat.add_assoc], occursAt_append.mpr ⟨o1, o2⟩⟩
        · cases h

/-- The domain of `option c`: `none`, or `some v` with `v` in `c`'s. -/
def OptionFits {α : Type} (P : α → Prop) : Option α → Prop
  | none => True
  | some v => P v

theorem option_lawfulOn {P : α → Prop} {c : Stream α} (hc : LawfulOn P c) : LawfulOn (OptionFits P) (option c) where
  put_eq v buf := by
    cases v with
    | none => rw [option_bytes_none]; exact u8_lawful.put_eq 0 buf
    | some v =>
      have hb : (option c).bytes (some v) = u8.bytes 1 ++ c.bytes v := by
        simp only [bytes, option]; rw [hc.put_eq]; rfl
      rw [hb]; simp only [option]
      rw [hc.put_eq, push_eq_append, ByteArray.append_assoc]; rfl
  size_eq v := by
    cases v with
    | none => rfl
    | some v =>
      have hb : (option c).bytes (some v) = u8.bytes 1 ++ c.bytes v := by
        simp only [bytes, option]; rw [hc.put_eq]; rfl
      rw [hb, ByteArray.size_append, ← hc.size_eq]; rfl
  get_of_occurs v b i hv h := by
    cases v with
    | none =>
      rw [option_bytes_none] at h ⊢
      simp [option, u8_lawful.get_of_occurs _ _ _ h]
    | some v =>
      have hb : (option c).bytes (some v) = u8.bytes 1 ++ c.bytes v := by
        simp only [bytes, option]; rw [hc.put_eq]; rfl
      rw [hb] at h ⊢
      obtain ⟨h1, h2⟩ := occursAt_append.mp h
      have h2' : OccursAt b (i + 1) (c.bytes v) := h2
      simp [option, u8_lawful.get_of_occurs _ _ _ h1, hc.get_of_occurs _ _ _ hv h2', ByteArray.size_append,
        Nat.add_assoc]
  occurs_of_get {b i v j} h := by
    simp only [option] at h
    split at h
    · cases h
    · rename_i k hk
      cases h
      obtain ⟨rfl, o⟩ := u8_lawful.occurs_of_get hk
      exact ⟨trivial, rfl, o⟩
    · rename_i k hk
      split at h
      · rename_i w m hw
        cases h
        obtain ⟨rfl, o1⟩ := u8_lawful.occurs_of_get hk
        obtain ⟨pw, rfl, o2⟩ := hc.occurs_of_get hw
        have hb : (option c).bytes (some w) = u8.bytes 1 ++ c.bytes w := by
          simp only [bytes, option]; rw [hc.put_eq]; rfl
        rw [hb]
        exact ⟨pw, by simp [ByteArray.size_append, Nat.add_assoc], occursAt_append.mpr ⟨o1, o2⟩⟩
      · cases h
    · cases h

/-! ## Lists on a domain -/

theorem foldl_putOn {P : α → Prop} {c : Stream α} (hc : LawfulOn P c) (l : List α) (buf : ByteArray) :
    l.foldl (fun out x => c.put x out) buf = buf ++ manyBytes c l := by
  induction l generalizing buf with
  | nil => simp [manyBytes, ByteArray.append_empty]
  | cons x l ih =>
    simp only [manyBytes, List.foldl_cons]
    rw [ih, ih (c.put x ByteArray.empty), hc.put_eq, hc.put_eq, ByteArray.empty_append,
      ByteArray.append_assoc]

theorem manyBytes_consOn {P : α → Prop} {c : Stream α} (hc : LawfulOn P c) (x : α) (l : List α) :
    manyBytes c (x :: l) = c.bytes x ++ manyBytes c l := by
  simp only [manyBytes, List.foldl_cons]
  rw [foldl_putOn hc]; rfl

theorem foldl_sizeOn {P : α → Prop} {c : Stream α} (hc : LawfulOn P c) (l : List α) (k : Nat) :
    l.foldl (fun n x => n + c.size x) k = k + (manyBytes c l).size := by
  induction l generalizing k with
  | nil => simp [manyBytes]
  | cons x l ih => rw [List.foldl_cons, ih, manyBytes_consOn hc, ByteArray.size_append, hc.size_eq, Nat.add_assoc]

theorem getMany_of_occursOn {P : α → Prop} {c : Stream α} (hc : LawfulOn P c) (l : List α)
    (hl : ∀ x ∈ l, P x) (b : ByteArray) (i : Nat) (acc : Array α) (h : OccursAt b i (manyBytes c l)) :
    getMany c b l.length i acc = .ok (acc ++ l.toArray, i + (manyBytes c l).size) := by
  induction l generalizing i acc with
  | nil => simp [getMany, manyBytes]
  | cons x l ih =>
    rw [manyBytes_consOn hc] at h ⊢
    obtain ⟨h1, h2⟩ := occursAt_append.mp h
    simp only [getMany, hc.get_of_occurs _ _ _ (hl x (List.mem_cons_self ..)) h1]
    rw [ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) _ _ h2]
    simp [ByteArray.size_append, Nat.add_assoc]

theorem occurs_of_getManyOn {P : α → Prop} {c : Stream α} (hc : LawfulOn P c) (n : Nat) (b : ByteArray)
    (i : Nat) (acc a : Array α) (k : Nat) (hi : i ≤ b.size) (h : getMany c b n i acc = .ok (a, k)) :
    ∃ l : List α, l.length = n ∧ a = acc ++ l.toArray ∧ (∀ x ∈ l, P x) ∧
      k = i + (manyBytes c l).size ∧ OccursAt b i (manyBytes c l) := by
  induction n generalizing i acc with
  | zero =>
    simp only [getMany, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, by simp, by simp, by simp [manyBytes],
      ⟨by simp [manyBytes]; omega, by simp [manyBytes, ByteArray.extract_same]⟩⟩
  | succ n ih =>
    simp only [getMany] at h
    split at h
    · rename_i x j hx
      obtain ⟨px, rfl, o1⟩ := hc.occurs_of_get hx
      obtain ⟨l, hl, rfl, pl, rfl, o2⟩ := ih _ _ (by have := o1.1; omega) h
      refine ⟨x :: l, by simp [hl], by simp, ?_, ?_, ?_⟩
      · intro y hy
        cases hy with
        | head => exact px
        | tail _ hy => exact pl y hy
      · rw [manyBytes_consOn hc, ByteArray.size_append, Nat.add_assoc]
      · rw [manyBytes_consOn hc]; exact occursAt_append.mpr ⟨o1, o2⟩
    · cases h

theorem rawList_bytes {P : α → Prop} {c : Stream α} (hc : LawfulOn P c) (max : Nat) (l : List α) :
    (rawList max c).bytes l = u32.bytes (UInt32.ofNat l.length) ++ manyBytes c l := by
  show l.foldl _ (u32.put _ ByteArray.empty) = _
  rw [foldl_putOn hc, u32_lawful.put_eq, ByteArray.empty_append]

theorem rawList_lawfulOn {P : α → Prop} {c : Stream α} (hc : LawfulOn P c) (max : Nat) (fits : max < 2 ^ 32) :
    LawfulOn (fun l => l.length ≤ max ∧ ∀ x ∈ l, P x) (rawList max c) where
  put_eq l buf := by
    rw [rawList_bytes hc]
    show l.foldl _ (u32.put _ buf) = _
    rw [foldl_putOn hc, u32_lawful.put_eq, ByteArray.append_assoc]
  size_eq l := by
    rw [rawList_bytes hc, ByteArray.size_append, u32_size, ← foldl_sizeOn hc]; rfl
  get_of_occurs l b i hl h := by
    rw [rawList_bytes hc] at h ⊢
    obtain ⟨h1, h2⟩ := occursAt_append.mp h
    have hn : (UInt32.ofNat l.length).toNat = l.length :=
      UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega)
    have hget := u32_lawful.get_of_occurs _ _ _ h1
    rw [u32_size] at hget h2
    have hmany := getMany_of_occursOn hc l hl.2 b (i + 4) (Array.emptyWithCapacity l.length) h2
    simp only [Array.emptyWithCapacity_eq, Array.empty_append] at hmany
    simp only [rawList, hget, hn, hl.1, ↓reduceIte, Array.emptyWithCapacity_eq, hmany,
      ByteArray.size_append, u32_size, Nat.add_assoc]
  occurs_of_get {b i v j} h := by
    simp only [rawList] at h
    split at h
    · cases h
    · rename_i n k hk
      split at h
      · rename_i hmax
        split at h
        · rename_i a m hm
          cases h
          obtain ⟨rfl, o1⟩ := u32_lawful.occurs_of_get hk
          obtain ⟨l, hl, rfl, pl, rfl, o2⟩ := occurs_of_getManyOn hc _ _ _ _ _ _ (by have := o1.1; omega) hm
          simp only [Array.emptyWithCapacity_eq, Array.empty_append, List.toList_toArray] at pl ⊢
          rw [rawList_bytes hc]
          have hsz : UInt32.ofNat l.length = n := by simp only [hl, UInt32.ofNat_toNat]
          simp only [hsz]
          exact ⟨⟨by omega, pl⟩, by simp [ByteArray.size_append, Nat.add_assoc], occursAt_append.mpr ⟨o1, o2⟩⟩
        · cases h
      · cases h

end Nanodregg.Codec.Stream
