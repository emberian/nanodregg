import Codec.Kernel
import Codec.Proofs.Raw

/-!
# The kernel codecs are canonical on the values KERNEL admits

`Fits` says a value is within the wire's bounds: counters below 2^64, slot keys and kinds below
2^32, every list and byte string within KERNEL's bounds. Each codec is `LawfulOn Fits`: a fitting
value reads back from its bytes, and whatever is read fits and is spelled exactly one way
(`LawfulOn.decode_eq_ok_iff`). `checkBounds_fits` closes the gap to the kernel: every Turn that
`World.admit` accepts fits, so `turnBytes` is injective on admitted turns.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec.Stream

variable {D : Type}

theorem discipline_lawful : Lawful discipline :=
  refine_lawful u8_lawful "kernel/discipline" (fun d => by cases d <;> rfl) (fun x y h => by
    by_cases h0 : x = 0
    · simp [h0] at h; subst h; simp [h0]
    · by_cases h1 : x = 1
      · simp [h1] at h; subst h; simp [h1]
      · by_cases h2 : x = 2
        · simp [h2] at h; subst h; simp [h2]
        · by_cases h3 : x = 3
          · simp [h3] at h; subst h; simp [h3]
          · simp [h0, h1, h2, h3] at h)

/-! ## Ops, slots, cells -/

def Op.Fits : Op → Prop
  | .set k v => k < 2 ^ 32 ∧ v.size ≤ Bounds.valueBytesMax
  | .erase k => k < 2 ^ 32

abbrev OpWireFits : (s : Fin 2) → OpF s → Prop
  | 0 => fun v => v.1 < 2 ^ 32 ∧ v.2.size ≤ Bounds.valueBytesMax
  | 1 => fun k => k < 2 ^ 32

theorem opWire_lawfulOn : ∀ s, LawfulOn (OpWireFits s) (opWire s)
  | 0 => product_lawfulOn nat32_lawfulOn (rawBytes_lawfulOn _ (by decide))
  | 1 => nat32_lawfulOn

theorem op_lawfulOn : LawfulOn Op.Fits op := by
  unfold op
  refine (refine_lawfulOn (choice_lawfulOn 2 (by decide) opWire_lawfulOn) "kernel/op" ?_ ?_).mono ?_ ?_
  · intro y _; cases y <;> rfl
  · intro x y h
    obtain ⟨s, v⟩ := x
    match s, v, h with
    | 0, (k, w), h => simp at h; subst h; rfl
    | 1, k, h => simp at h; subst h; rfl
  · intro y h; cases y <;> simpa [OpWireFits, Op.Fits] using h
  · intro y h; cases y <;> simpa [OpWireFits, Op.Fits] using h

def Slots.Fits (sl : Slots) : Prop :=
  sl.length ≤ Bounds.slotsPerCellMax ∧ ∀ p ∈ sl, p.1 < 2 ^ 32 ∧ p.2.size ≤ Bounds.valueBytesMax

theorem slots_lawfulOn : LawfulOn Slots.Fits slots :=
  rawList_lawfulOn (product_lawfulOn nat32_lawfulOn (rawBytes_lawfulOn _ (by decide))) _ (by decide)

def Cell.Fits (c : Cell) : Prop := c.kind < 2 ^ 32 ∧ Slots.Fits c.slots

theorem cell_lawfulOn : LawfulOn Cell.Fits cell := by
  unfold cell
  refine (refine_lawfulOn (product_lawfulOn nat32_lawfulOn (product_lawfulOn discipline_lawful.on slots_lawfulOn))
    "kernel/cell" ?_ ?_).mono ?_ ?_
  · intro y _; rfl
  · intro x y h; simp at h; subst h; rfl
  · intro y h; exact ⟨h.1, h.2.2⟩
  · intro y h; exact ⟨h.1, trivial, h.2⟩

/-! ## Acts, touches, turns -/

def Act.Fits : Act → Prop
  | .write ops => ops.length ≤ Bounds.opsPerWriteMax ∧ ∀ o ∈ ops, Op.Fits o
  | _ => True

abbrev ActWireFits : (s : Fin 3) → ActF s → Prop
  | 0 => fun _ => True
  | 1 => fun ops => ops.length ≤ Bounds.opsPerWriteMax ∧ ∀ o ∈ ops, Op.Fits o
  | 2 => fun _ => True

theorem actWire_lawfulOn : ∀ s, LawfulOn (ActWireFits s) (actWire s)
  | 0 => unit_lawful.on
  | 1 => rawList_lawfulOn op_lawfulOn _ (by decide)
  | 2 => unit_lawful.on

theorem act_lawfulOn : LawfulOn Act.Fits act := by
  unfold act
  refine (refine_lawfulOn (choice_lawfulOn 3 (by decide) actWire_lawfulOn) "kernel/act" ?_ ?_).mono ?_ ?_
  · intro y _; cases y <;> rfl
  · intro x y h
    obtain ⟨s, v⟩ := x
    match s, v, h with
    | 0, (), h => simp at h; subst h; rfl
    | 1, ops, h => simp at h; subst h; rfl
    | 2, (), h => simp at h; subst h; rfl
  · intro y h; cases y <;> simp_all [ActWireFits, Act.Fits]
  · intro y h; cases y <;> simp_all [ActWireFits, Act.Fits]

def Touch.Fits (PD : D → Prop) (x : Touch D) : Prop := PD x.cell ∧ PD x.seen ∧ Act.Fits x.act

theorem touch_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (Touch.Fits PD) (touch dc) := by
  unfold touch
  refine (refine_lawfulOn (product_lawfulOn hd (product_lawfulOn hd act_lawfulOn)) "kernel/touch" ?_ ?_).mono ?_ ?_
  · intro y _; rfl
  · intro x y h; simp at h; subst h; rfl
  · intro y h; exact h
  · intro y h; exact h

def Turn.Fits (PD : D → Prop) (t : Turn D) : Prop :=
  PD t.txId ∧ t.notBefore < 2 ^ 64 ∧ t.validUntil < 2 ^ 64 ∧
  (t.touches.length ≤ Bounds.touchesMax ∧ ∀ x ∈ t.touches, Touch.Fits PD x) ∧
  (t.creates.length ≤ Bounds.createsMax ∧ ∀ c ∈ t.creates, Cell.Fits c) ∧
  (t.nullifiers.length ≤ Bounds.nullifiersMax ∧ ∀ n ∈ t.nullifiers, PD n) ∧
  t.charge < 2 ^ 64 ∧ t.event.size ≤ Bounds.eventBytesMax

theorem turn_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (Turn.Fits PD) (turn dc) := by
  unfold turn
  refine (refine_lawfulOn
    (product_lawfulOn hd (product_lawfulOn nat64_lawfulOn (product_lawfulOn nat64_lawfulOn
      (product_lawfulOn (rawList_lawfulOn (touch_lawfulOn hd) _ (by decide))
        (product_lawfulOn (rawList_lawfulOn cell_lawfulOn _ (by decide))
          (product_lawfulOn (rawList_lawfulOn hd _ (by decide))
            (product_lawfulOn nat64_lawfulOn (rawBytes_lawfulOn _ (by decide)))))))))
    "kernel/turn" ?_ ?_).mono ?_ ?_
  · intro y _; rfl
  · intro x y h; simp at h; subst h; rfl
  · intro y h; exact h
  · intro y h; exact h

/-! ## Calls -/

def Right.Fits : Right → Prop
  | .invoke m => m < 2 ^ 64
  | .enroll n => n < 2 ^ 64
  | _ => True

theorem right_lawfulOn : LawfulOn Right.Fits right := by
  unfold right
  refine (refine_lawfulOn (choice_lawfulOn 4 (by decide)
      (P := fun s => match s with
        | 2 => fun (m : Nat) => m < 2 ^ 64 | 3 => fun (n : Nat) => n < 2 ^ 64 | _ => fun _ => True)
      (fun s => match s with
        | 0 => unit_lawful.on
        | 1 => unit_lawful.on
        | 2 => nat64_lawfulOn
        | 3 => nat64_lawfulOn)) "kernel/right" ?_ ?_).mono ?_ ?_
  · intro y _; cases y <;> rfl
  · intro x y h
    obtain ⟨s, v⟩ := x
    match s, v, h with
    | 0, (), h => simp at h; subst h; rfl
    | 1, (), h => simp at h; subst h; rfl
    | 2, m, h => simp at h; subst h; rfl
    | 3, n, h => simp at h; subst h; rfl
  · intro y h; cases y <;> simp_all [Right.Fits]
  · intro y h; cases y <;> simp_all [Right.Fits]

/-- A list of at most `callMax` elements, each in `P`. -/
def ListFits {α : Type} (P : α → Prop) (l : List α) : Prop := l.length ≤ callMax ∧ ∀ x ∈ l, P x

def BytesFits (b : ByteArray) : Prop := b.size ≤ callMax

def Body.Fits (PD : D → Prop) : Body D → Prop
  | .enroll k n p v => BytesFits k ∧ PD n ∧ BytesFits p ∧ PD v
  | .rotate k n => BytesFits k ∧ PD n
  | .install p => BytesFits p
  | .create p ls st => OptionFits PD p ∧ ListFits PD ls ∧ Slots.Fits st
  | .write o es v => PD o ∧ ListFits (fun e => e.1 < 2 ^ 32 ∧ OptionFits (·.size ≤ Bounds.valueBytesMax) e.2) es ∧
      OptionFits PD v
  | .law o ls v => PD o ∧ ListFits PD ls ∧ OptionFits PD v
  | .invoke o m a b v => PD o ∧ m < 2 ^ 64 ∧ BytesFits a ∧ b < 2 ^ 64 ∧ OptionFits PD v
  | .grant t g r p => PD t ∧ PD g ∧ ListFits Right.Fits r ∧ OptionFits PD p
  | .revoke g => PD g
  | .issue cap => cap < 2 ^ 64
  | .account a => PD a
  | .transfer s d n v o => PD s ∧ PD d ∧ n < 2 ^ 64 ∧ OptionFits PD v ∧ OptionFits BytesFits o
  | .credit w a n v => PD w ∧ PD a ∧ n < 2 ^ 64 ∧ OptionFits PD v

abbrev BodyWireFits (PD : D → Prop) : (s : Fin 13) → BodyF D s → Prop
  | 0 => fun v => BytesFits v.1 ∧ PD v.2.1 ∧ BytesFits v.2.2.1 ∧ PD v.2.2.2
  | 1 => fun v => BytesFits v.1 ∧ PD v.2
  | 2 => fun v => BytesFits v
  | 3 => fun v => OptionFits PD v.1 ∧ ListFits PD v.2.1 ∧ Slots.Fits v.2.2
  | 4 => fun v => PD v.1 ∧
      ListFits (fun e => e.1 < 2 ^ 32 ∧ OptionFits (·.size ≤ Bounds.valueBytesMax) e.2) v.2.1 ∧ OptionFits PD v.2.2
  | 5 => fun v => PD v.1 ∧ ListFits PD v.2.1 ∧ OptionFits PD v.2.2
  | 6 => fun v => PD v.1 ∧ v.2.1 < 2 ^ 64 ∧ BytesFits v.2.2.1 ∧ v.2.2.2.1 < 2 ^ 64 ∧ OptionFits PD v.2.2.2.2
  | 7 => fun v => PD v.1 ∧ PD v.2.1 ∧ ListFits Right.Fits v.2.2.1 ∧ OptionFits PD v.2.2.2
  | 8 => fun v => PD v
  | 9 => fun v => v < 2 ^ 64
  | 10 => fun v => PD v
  | 11 => fun v => PD v.1 ∧ PD v.2.1 ∧ v.2.2.1 < 2 ^ 64 ∧ OptionFits PD v.2.2.2.1 ∧
      OptionFits BytesFits v.2.2.2.2
  | 12 => fun v => PD v.1 ∧ PD v.2.1 ∧ v.2.2.1 < 2 ^ 64 ∧ OptionFits PD v.2.2.2

theorem bodyWire_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    ∀ s, LawfulOn (BodyWireFits PD s) (bodyWire dc s)
  | 0 => product_lawfulOn (rawBytes_lawfulOn _ (by decide))
      (product_lawfulOn hd (product_lawfulOn (rawBytes_lawfulOn _ (by decide)) hd))
  | 1 => product_lawfulOn (rawBytes_lawfulOn _ (by decide)) hd
  | 2 => rawBytes_lawfulOn _ (by decide)
  | 3 => product_lawfulOn (option_lawfulOn hd) (product_lawfulOn (rawList_lawfulOn hd _ (by decide)) slots_lawfulOn)
  | 4 => product_lawfulOn hd (product_lawfulOn (rawList_lawfulOn (product_lawfulOn nat32_lawfulOn
      (option_lawfulOn (rawBytes_lawfulOn _ (by decide)))) _ (by decide)) (option_lawfulOn hd))
  | 5 => product_lawfulOn hd (product_lawfulOn (rawList_lawfulOn hd _ (by decide)) (option_lawfulOn hd))
  | 6 => product_lawfulOn hd (product_lawfulOn nat64_lawfulOn (product_lawfulOn (rawBytes_lawfulOn _ (by decide))
      (product_lawfulOn nat64_lawfulOn (option_lawfulOn hd))))
  | 7 => product_lawfulOn hd (product_lawfulOn hd (product_lawfulOn (rawList_lawfulOn right_lawfulOn _ (by decide))
      (option_lawfulOn hd)))
  | 8 => hd
  | 9 => nat64_lawfulOn
  | 10 => hd
  | 11 => product_lawfulOn hd (product_lawfulOn hd (product_lawfulOn nat64_lawfulOn
      (product_lawfulOn (option_lawfulOn hd) (option_lawfulOn (rawBytes_lawfulOn _ (by decide))))))
  | 12 => product_lawfulOn hd (product_lawfulOn hd (product_lawfulOn nat64_lawfulOn (option_lawfulOn hd)))

theorem body_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (Body.Fits PD) (body dc) := by
  unfold body
  refine (refine_lawfulOn (choice_lawfulOn 13 (by decide) (bodyWire_lawfulOn hd)) "kernel/body" ?_ ?_).mono ?_ ?_
  · intro y _; cases y <;> rfl
  · intro x y h
    obtain ⟨s, v⟩ := x
    match s, v, h with
    | 0, (_, _, _, _), h => simp at h; subst h; rfl
    | 1, (_, _), h => simp at h; subst h; rfl
    | 2, _, h => simp at h; subst h; rfl
    | 3, (_, _, _), h => simp at h; subst h; rfl
    | 4, (_, _, _), h => simp at h; subst h; rfl
    | 5, (_, _, _), h => simp at h; subst h; rfl
    | 6, (_, _, _, _, _), h => simp at h; subst h; rfl
    | 7, (_, _, _, _), h => simp at h; subst h; rfl
    | 8, _, h => simp at h; subst h; rfl
    | 9, _, h => simp at h; subst h; rfl
    | 10, _, h => simp at h; subst h; rfl
    | 11, (_, _, _, _, _), h => simp at h; subst h; rfl
    | 12, (_, _, _, _), h => simp at h; subst h; rfl
  · intro y h; cases y <;> exact h
  · intro y h; cases y <;> exact h

def Unsigned.Fits (PD : D → Prop) (u : Unsigned D) : Prop :=
  PD u.world ∧ PD u.member ∧ BytesFits u.key ∧ u.notBefore < 2 ^ 64 ∧ u.validUntil < 2 ^ 64 ∧
  ListFits (fun p => PD p.1 ∧ PD p.2) u.pins ∧ u.maxCharge < 2 ^ 64 ∧ Body.Fits PD u.body

theorem unsigned_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (Unsigned.Fits PD) (unsigned dc) := by
  unfold unsigned
  refine (refine_lawfulOn
    (product_lawfulOn hd (product_lawfulOn hd (product_lawfulOn (rawBytes_lawfulOn _ (by decide)) (product_lawfulOn nat64_lawfulOn
      (product_lawfulOn nat64_lawfulOn (product_lawfulOn (rawList_lawfulOn (product_lawfulOn hd hd) _ (by decide))
        (product_lawfulOn nat64_lawfulOn (body_lawfulOn hd))))))))
    "kernel/unsigned/v2" ?_ ?_).mono ?_ ?_
  · intro y _; rfl
  · intro x y h; simp at h; subst h; rfl
  · intro y h; exact h
  · intro y h; exact h

def Call.Fits (PD : D → Prop) (c : Call D) : Prop := Unsigned.Fits PD c.unsigned ∧ BytesFits c.signature

theorem call_lawfulOn {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) :
    LawfulOn (Call.Fits PD) (call dc) := by
  unfold call
  refine (refine_lawfulOn (product_lawfulOn (unsigned_lawfulOn hd) (rawBytes_lawfulOn _ (by decide)))
    "kernel/call" ?_ ?_).mono ?_ ?_
  · intro y _; rfl
  · intro x y h; simp at h; subst h; rfl
  · intro y h; exact h
  · intro y h; exact h

/-! ## Every admitted turn fits -/

theorem bind_req {ε : Type} {c : Prop} [Decidable c] {e : ε} {r : Except ε Unit} :
    ((if c then Except.ok () else Except.error e) >>= fun (_ : Unit) => r) = Except.ok () ↔
      c ∧ r = Except.ok () := by
  by_cases hc : c <;> simp [hc, bind, Except.bind]

theorem ite_req {ε : Type} {c : Prop} [Decidable c] {e : ε} :
    (if c then Except.ok () else Except.error e : Except ε Unit) = Except.ok () ↔ c := by
  by_cases hc : c <;> simp [hc]

/-- Every turn `World.admit`'s bound check accepts is within the wire's bounds, so its encoding is
canonical and `turnBytes` is injective on admitted turns (with `turn_lawfulOn`). -/
theorem checkBounds_fits (t : Turn D) (h : checkBounds t = .ok ()) : Turn.Fits (fun _ => True) t := by
  simp only [checkBounds, req, decide_eq_true_eq] at h
  simp only [bind_req, ite_req, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hT, hOps, hC, hN, hE, hS, ⟨hKc, hKt⟩, ⟨hVc, hVt⟩, _, _, ⟨⟨⟨hVu, hNb⟩, hCh⟩, hKind⟩⟩ := h
  refine ⟨trivial, by simpa [Bounds.counterLimit] using hNb, by simpa [Bounds.counterLimit] using hVu,
    ⟨hT, fun x hx => ⟨trivial, trivial, ?_⟩⟩, ⟨hC, fun c hc => ⟨?_, hS c hc, fun p hp => ⟨?_, hVc c hc p hp⟩⟩⟩,
    ⟨hN, fun _ _ => trivial⟩, by simpa [Bounds.counterLimit] using hCh, hE⟩
  · have hops := hOps x hx
    have hk := hKt x hx
    have hv := hVt x hx
    unfold Touch.ops at hops hk hv
    cases hact : x.act with
    | keep => trivial
    | retire => trivial
    | write ops =>
      rw [hact] at hops hk hv
      refine ⟨hops, fun o ho => ?_⟩
      have k := hk o ho
      have v := hv o ho
      cases o with
      | set key val => exact ⟨by simpa [Op.key, Bounds.slotKeyLimit] using k, by simpa [opValueSize] using v⟩
      | erase key => simpa [Op.Fits, Op.key, Bounds.slotKeyLimit] using k
  · simpa [Bounds.kindLimit] using hKind c hc
  · simpa [Bounds.slotKeyLimit] using hKc c hc p hp

/-! ## The Env/Ctx facts -/

theorem decodeCall_callBytes {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {c : Call D}
    (hc : Call.Fits PD c) : decodeCall dc (callBytes dc c) = some c := by
  simp [decodeCall, readCall, callBytes, (call_lawfulOn hd).decode_bytes hc]

theorem eq_callBytes_of_decodeCall {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {b : ByteArray}
    {c : Call D} (h : decodeCall dc b = some c) : Call.Fits PD c ∧ b = callBytes dc c := by
  unfold decodeCall at h
  split at h
  · rename_i c' hr
    cases h
    exact (call_lawfulOn hd).eq_bytes_of_decode hr
  · cases h

theorem unsignedBytes_injective {PD : D → Prop} {dc : Stream D} (hd : LawfulOn PD dc) {u v : Unsigned D}
    (hu : Unsigned.Fits PD u) (hv : Unsigned.Fits PD v) (h : unsignedBytes dc u = unsignedBytes dc v) :
    u = v :=
  (unsigned_lawfulOn hd).bytes_injective hu hv h

theorem cellBytes_injective {c c' : Cell} (hc : Cell.Fits c) (hc' : Cell.Fits c') (h : cellBytes c = cellBytes c') :
    c = c' :=
  cell_lawfulOn.bytes_injective hc hc' h

/-- Two turns `World.admit` accepted with the same bytes are the same turn. -/
theorem turnBytes_injective {dc : Stream D} (hd : Lawful dc) {t t' : Turn D}
    (ht : checkBounds t = .ok ()) (ht' : checkBounds t' = .ok ()) (h : turnBytes dc t = turnBytes dc t') :
    t = t' :=
  (turn_lawfulOn hd.on).bytes_injective (checkBounds_fits t ht) (checkBounds_fits t' ht') h

end Nanodregg.Codec.Kernel
