/-
# Hosting.Proofs.Broker — the broker never charges a resident past its cap, and a restart refunds nothing
-/
import Hosting.Broker
import Codec.Proofs.Layout

namespace Nanodregg.Hosting.Proofs.Broker

open Nanodregg.Codec Nanodregg.Hosting.Broker

/-! ## Specifications (private: the proofs' own; nothing deployed calls them)

`Json.escL` is `Json.esc` as a list, `Json.unstr` reads a JSON string's contents after its opening
quote, and `Json.bodySpec` is the body as a list of bytes. -/

namespace Json

private def escL (x : UInt8) : List UInt8 :=
  if x == 34 then [92, 34]
  else if x == 92 then [92, 92]
  else if x < 32 then [92, 117, 48, 48, Broker.Json.hexDigit (x.toNat / 16), Broker.Json.hexDigit (x.toNat % 16)]
  else [x]

private def hexVal (h : UInt8) : Option Nat :=
  if 48 ≤ h && h ≤ 57 then some (h.toNat - 48) else if 97 ≤ h && h ≤ 102 then some (h.toNat - 87) else none

private def unstr : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | x :: rest =>
    if x == 34 then some ([], rest)
    else if x == 92 then
      match rest with
      | 34 :: r => (unstr r).map fun (c, r) => (34 :: c, r)
      | 92 :: r => (unstr r).map fun (c, r) => (92 :: c, r)
      | 117 :: 48 :: 48 :: h :: l :: r =>
        match hexVal h, hexVal l with
        | some a, some b => if a * 16 + b < 32 then (unstr r).map fun (c, r) => ((a * 16 + b).toUInt8 :: c, r) else none
        | _, _ => none
      | _ => none
    else if x < 32 then none
    else (unstr rest).map fun (c, r) => (x :: c, r)
termination_by l => l.length
decreasing_by all_goals simp_all <;> omega

private def u (s : String) : List UInt8 := s.toUTF8.data.toList

private def strSpec (b : ByteArray) : List UInt8 := 34 :: b.data.toList.flatMap escL ++ [34]

private def msgSpec (role : String) (t : ByteArray) : List UInt8 :=
  u ("{\"role\":\"" ++ role ++ "\",\"content\":") ++ strSpec t ++ u "}"

private def msgsSpec : List (String × ByteArray) → List UInt8
  | [] => []
  | [(r, t)] => msgSpec r t
  | (r, t) :: ms => msgSpec r t ++ u "," ++ msgsSpec ms

private def bodySpec (model : ByteArray) (n : Nat) (system : ByteArray) (ms : List (String × ByteArray)) :
    List UInt8 :=
  u "{\"model\":" ++ strSpec model ++ u ",\"max_tokens\":" ++ u (Nat.repr n) ++
    (if system.size = 0 then [] else u ",\"system\":" ++ strSpec system) ++
    u ",\"messages\":[" ++ msgsSpec ms ++ u "]}"

end Json

private theorem ba_beq (a b : ByteArray) : (a == b) = decide (a = b) := by
  cases a with | mk x => cases b with | mk y =>
  show (x == y) = _
  by_cases h : x = y
  · subst h; simp
  · simp [h]

private theorem filter_one {l : List Entry} {p : Entry → Bool} {e : Entry} (h : l.filter p = [e]) :
    e ∈ l ∧ p e = true ∧ ∀ x ∈ l, p x = true → x = e := by
  have he : e ∈ l.filter p := by rw [h]; exact List.mem_singleton_self e
  refine ⟨(List.mem_filter.mp he).1, (List.mem_filter.mp he).2, fun x hx hp => ?_⟩
  have : x ∈ l.filter p := List.mem_filter.mpr ⟨hx, hp⟩
  rw [h] at this
  exact List.mem_singleton.mp this

/-- What a grant reads and writes: the clock did not go back, exactly one entry is the resident's
meter on the asked model, its window is nonzero, the charge fits its cap, and the next broker is
this one with that meter charged and nothing else changed. -/
theorem decide_ok {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask} {b' : Broker} {g : Grant}
    (h : Broker.decide b now r ask = .ok (b', g)) :
    b.last ≤ now ∧ ∃ e, b.entries.filter (Entry.is r ask.model) = [e] ∧ e.allowance.windowMs ≠ 0 ∧
      (e.meter.roll (windowOf e.allowance now)).spent + g.charged ≤ e.allowance.cap ∧
      b' = { b with last := now, entries := b.entries.map fun x => if Entry.is r ask.model x then
        { e with meter := ⟨(e.meter.roll (windowOf e.allowance now)).window,
                           (e.meter.roll (windowOf e.allowance now)).spent + g.charged⟩ } else x } := by
  unfold Broker.decide at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | cases h | skip
  all_goals first
    | (rename_i _ _ _ e he hm _ _ _ _ _ _ _ _ _ _ _
       refine ⟨by omega, e, he, ?_, by dsimp only; omega, rfl⟩
       simp [Allowance.malformed] at hm; omega)
    | skip

/-- What a grant is for: the ONE allowance of the resident on the asked model (any second one
refuses, `ambiguous_refused`), well formed, served by the provider Lean's table names for that model
(so the host keybroker verifies is the table's), whose key slot keybroker holds a key for; a token count
within the allowance and the ceiling; exactly the body `requestBody` prints; the worst-case charge. -/
theorem grant_allowed {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask} {b' : Broker} {g : Grant}
    (h : Broker.decide b now r ask = .ok (b', g)) :
    ∃ e ∈ b.entries, e.resident = r ∧ e.allowance.model = ask.model ∧
      (∀ x ∈ b.entries, x.resident = r → x.allowance.model = ask.model → x = e) ∧
      0 < e.allowance.microPerKTok ∧ e.allowance.keySlot < 2 ^ 32 ∧ e.allowance.keySlot ∈ b.keys ∧
      g.keySlot = e.allowance.keySlot.toUInt32 ∧ providerOf ask.model = some g.upstream ∧
      0 < ask.maxTokens ∧ ask.maxTokens ≤ e.allowance.maxTokens ∧ ask.maxTokens ≤ Bounds.tokensCeiling ∧
      requestBody ask = .ok g.body ∧ g.body.size ≤ Bounds.bodyMax ∧
      g.charged = cost e.allowance (g.body.size + ask.maxTokens) := by
  unfold Broker.decide at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | cases h | skip
  rename_i _ _ _ e he hm _ up hup hk htz hto _ body hb hbs _
  obtain ⟨hmem, hp, hu⟩ := filter_one he
  simp only [Entry.is, Bool.and_eq_true, ba_beq, decide_eq_true_eq] at hp
  have hm' : e.allowance.microPerKTok ≠ 0 ∧ e.allowance.keySlot < 2 ^ 32 := by
    simp only [Allowance.malformed, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hm
    refine ⟨?_, ?_⟩ <;> omega
  refine ⟨e, hmem, hp.1, hp.2, fun x hx h1 h2 => hu x hx (by simp [Entry.is, ba_beq, h1, h2]),
    by omega, by omega, by simpa using hk, rfl, by rw [← hp.2]; exact hup, by omega, ?_, ?_, hb,
    by dsimp only; omega, rfl⟩
  · have := Nat.min_le_left e.allowance.maxTokens Bounds.tokensCeiling; omega
  · have := Nat.min_le_right e.allowance.maxTokens Bounds.tokensCeiling; omega

/-- Two allowances of one resident on one model: no ask on that model is ever granted. -/
theorem ambiguous_refused {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask}
    (h2 : 2 ≤ (b.entries.filter (Entry.is r ask.model)).length) :
    ∀ x, Broker.decide b now r ask ≠ .ok x := by
  intro ⟨b', g⟩ h
  obtain ⟨-, e, he, -⟩ := decide_ok h
  rw [he] at h2
  simp at h2

/-! ## The meter: never past a cap; a new or changed allowance, and a restart, refund nothing -/

/-- No meter is past its cap (`capped_follow`, `capped_decide`). -/
private def Capped (b : Broker) : Prop := ∀ e ∈ b.entries, e.meter.spent ≤ e.allowance.cap

/-- The forfeit invariant (`fresh_follow`, `fresh_decide`): every meter lies between
the window its allowance was first held in and the latest accepted time's, and a meter still in that
first window is spent to its cap. -/
private def Fresh (b : Broker) : Prop :=
  ∀ e ∈ b.entries, e.allowance.windowMs ≠ 0 →
    windowOf e.allowance e.since ≤ e.meter.window ∧ e.meter.window ≤ windowOf e.allowance b.last ∧
    (e.meter.window = windowOf e.allowance e.since → e.allowance.cap ≤ e.meter.spent)


/-- The broker's entries are the World's allowances, one for one and in order. -/
theorem follow_allowances (b : Broker) (now : Nat) (rs : List (ByteArray × Allowance)) :
    (b.follow now rs).entries.map (fun e => (e.resident, e.allowance)) = rs := by
  simp only [Broker.follow, List.map_map]
  conv => rhs; rw [← List.map_id rs]
  apply List.map_congr_left
  intro ⟨r, a⟩ _
  simp only [Function.comp, id]
  split
  · rename_i e he
    have := List.find?_some he
    simp only [Bool.and_eq_true, ba_beq, decide_eq_true_eq, beq_iff_eq] at this
    rw [this.1, this.2]
  · rfl

/-- A follow moves the clock to `max now last` and leaves the key slots as they were. -/
theorem follow_last_keys (b : Broker) (now : Nat) (rs : List (ByteArray × Allowance)) :
    (b.follow now rs).last = max now b.last ∧ (b.follow now rs).keys = b.keys := ⟨rfl, rfl⟩

/-- Every entry after a follow is one the broker already held (same resident, same allowance, its
meter kept) or one opened at the follow's time, spent to its cap. -/
theorem follow_kept_or_opened (b : Broker) (now : Nat) (rs : List (ByteArray × Allowance)) :
    ∀ e ∈ (b.follow now rs).entries, e ∈ b.entries ∨ e = Entry.opened (max now b.last) e.resident e.allowance := by
  intro e he
  simp only [Broker.follow, List.mem_map] at he
  obtain ⟨⟨r, a⟩, -, rfl⟩ := he
  split
  · rename_i x hx; exact .inl (List.mem_of_find?_eq_some hx)
  · exact .inr rfl

/-- An allowance the broker held, unchanged in the World, keeps its meter across a follow. -/
theorem follow_keeps (b : Broker) (now : Nat) (rs : List (ByteArray × Allowance)) {e : Entry}
    (he : e ∈ b.entries) (hu : ∀ x ∈ b.entries, x.resident = e.resident → x.allowance = e.allowance → x = e)
    (hr : (e.resident, e.allowance) ∈ rs) : e ∈ (b.follow now rs).entries := by
  simp only [Broker.follow, List.mem_map]
  refine ⟨_, hr, ?_⟩
  have : b.entries.find? (fun x => x.resident == e.resident && x.allowance == e.allowance) = some e := by
    cases hf : b.entries.find? (fun x => x.resident == e.resident && x.allowance == e.allowance) with
    | none =>
      have := List.find?_eq_none.mp hf e he
      simp [ba_beq] at this
    | some x =>
      have hx := List.find?_some hf
      simp only [Bool.and_eq_true, ba_beq, decide_eq_true_eq, beq_iff_eq] at hx
      rw [hu x (List.mem_of_find?_eq_some hf) hx.1 hx.2]
  simp only [this]

theorem capped_follow {b : Broker} (hi : Capped b) (now : Nat) (rs : List (ByteArray × Allowance)) :
    Capped (b.follow now rs) := by
  intro e he
  rcases follow_kept_or_opened b now rs e he with h | h
  · exact hi e h
  · rw [h]; exact Nat.le_refl _

private theorem windowOf_mono (a : Allowance) {s t : Nat} (h : s ≤ t) : windowOf a s ≤ windowOf a t :=
  Nat.div_le_div_right h

theorem fresh_follow {b : Broker} (hf : Fresh b) (now : Nat) (rs : List (ByteArray × Allowance)) :
    Fresh (b.follow now rs) := by
  intro e he hw
  have hl : (b.follow now rs).last = max now b.last := rfl
  rw [hl]
  rcases follow_kept_or_opened b now rs e he with h | h
  · obtain ⟨h1, h2, h3⟩ := hf e h hw
    exact ⟨h1, Nat.le_trans h2 (windowOf_mono _ (Nat.le_max_right _ _)), h3⟩
  · rw [h]
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ => Nat.le_refl _⟩

/-- A broker life's start: every meter at its cap, the forfeit invariant from the outset. -/
theorem start_capped_fresh (t0 : Nat) (keys : List Nat) (rs : List (ByteArray × Allowance)) :
    Capped (Broker.start t0 keys rs) ∧ Fresh (Broker.start t0 keys rs) :=
  ⟨capped_follow (fun _ h => by cases h) t0 rs, fresh_follow (fun _ h => by cases h) t0 rs⟩

/-- A grant keeps every meter within its cap: no allowance is ever charged past its cap. -/
theorem capped_decide {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask} {b' : Broker} {g : Grant}
    (hi : Capped b) (h : Broker.decide b now r ask = .ok (b', g)) : Capped b' := by
  obtain ⟨-, e, -, -, hc, rfl⟩ := decide_ok h
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  split
  · exact hc
  · exact hi y hy

/-- A grant keeps the forfeit invariant. -/
theorem fresh_decide {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask} {b' : Broker} {g : Grant}
    (hf : Fresh b) (h : Broker.decide b now r ask = .ok (b', g)) : Fresh b' := by
  obtain ⟨hl, e, he, hw, -, rfl⟩ := decide_ok h
  obtain ⟨hmem, -, hu⟩ := filter_one he
  intro x hx hxw
  simp only [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  by_cases hyr : Entry.is r ask.model y = true
  · simp only [hyr, if_true]
    obtain ⟨h1, h2, h3⟩ := hf e hmem hw
    have hm := windowOf_mono e.allowance hl
    simp only [Meter.roll]
    split
    · dsimp only
      refine ⟨by omega, Nat.le_refl _, fun heq => by omega⟩
    · exact ⟨h1, by omega, fun heq => Nat.le_trans (h3 heq) (Nat.le_add_right _ _)⟩
  · simp only [hyr, if_false, Bool.false_eq_true] at hxw ⊢
    obtain ⟨h1, h2, h3⟩ := hf y hy hxw
    exact ⟨h1, Nat.le_trans h2 (windowOf_mono y.allowance hl), h3⟩

/-- Every grant costs something: its token count is positive and its price is not 0. -/
theorem charged_pos {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask} {b' : Broker} {g : Grant}
    (h : Broker.decide b now r ask = .ok (b', g)) : 0 < g.charged := by
  obtain ⟨e, -, -, -, -, hp, -, -, -, -, ht, -, -, -, -, hc⟩ := grant_allowed h
  rw [hc]; unfold cost
  have : 1 ≤ (g.body.size + ask.maxTokens) * e.allowance.microPerKTok :=
    Nat.mul_pos (by omega) hp
  omega

private theorem start_window_cost0 {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask} {b' : Broker} {g : Grant}
    (hf : Fresh b)
    (hnow : ∀ e ∈ b.entries, Entry.is r ask.model e = true →
      windowOf e.allowance now ≤ windowOf e.allowance e.since)
    (h : Broker.decide b now r ask = .ok (b', g)) : g.charged = 0 := by
  obtain ⟨hl, e, he, hw, hc, -⟩ := decide_ok h
  obtain ⟨hmem, hp, -⟩ := filter_one he
  obtain ⟨h1, h2, h3⟩ := hf e hmem hw
  have hn := hnow e hmem hp
  have hm := windowOf_mono e.allowance hl
  simp only [Meter.roll] at hc
  split at hc
  · omega
  · have := h3 (by omega); omega

/-- Nothing is refunded: no ask is granted in the window its allowance was first held in (by this
life, or since the operator last changed it), since that window opened spent to its cap and every
grant costs something (`charged_pos`). With `fresh_follow` and `fresh_decide` this holds after any
run of follows and grants. Across lives it needs the allowance unchanged; a changed allowance is a
new budget, the operator's act (HOSTING-13). -/
theorem start_window_refused {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask}
    (hf : Fresh b)
    (hnow : ∀ e ∈ b.entries, Entry.is r ask.model e = true →
      windowOf e.allowance now ≤ windowOf e.allowance e.since) :
    ∀ x, Broker.decide b now r ask ≠ .ok x := by
  intro ⟨b', g⟩ h
  have := start_window_cost0 hf hnow h
  have := charged_pos h
  omega

/-- The charge is the worst case: never less than the exact price of `tokens` tokens. -/
theorem cost_worst (a : Allowance) (tokens : Nat) : tokens * a.microPerKTok ≤ 1000 * cost a tokens := by
  unfold cost
  omega

/-! ## The refusal table and the frames -/

theorem mem_all (r : Broker.Refusal) : r ∈ Broker.Refusal.all := by cases r <;> decide

theorem ofCode?_code (r : Broker.Refusal) : Broker.Refusal.ofCode? r.code = some r := by
  cases r <;> decide

theorem code_injective {a b : Broker.Refusal} (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> simp_all [Broker.Refusal.code]

theorem name_injective {a b : Broker.Refusal} (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> simp_all [Broker.Refusal.name]

theorem verdictCodes_nodup : (Wire.verdictCases.map (·.2.1)).Nodup := by decide
theorem answerCodes_nodup : (Wire.answerCases.map (·.2.1)).Nodup := by decide

theorem askCodec_lawful : Stream.Lawful Wire.askCodec := Tagged.codec_lawful _ _ _ (by decide)
theorem requestCodec_lawful : Stream.Lawful Wire.requestCodec := Tagged.codec_lawful _ _ _ (by decide)
theorem verdictCodec_lawful : Stream.Lawful Wire.verdictCodec :=
  Tagged.codec_lawful _ _ _ verdictCodes_nodup

private theorem bytes?_val {b : ByteArray} {v : Bytes Bounds.frameMax} (h : Wire.bytes? b = some v) :
    v.val = b := by
  unfold Wire.bytes? at h; split at h <;> simp_all; rw [← h]

/-- The wire value of a verdict reads back as that verdict, field for field (so keybroker, reading
by name, gets the key slot, the charge and Lean's request bytes). -/
theorem verdictOf_wire {v : Verdict} {w : Wire.VerdictTy} (h : Wire.verdictWire? v = some w) :
    Wire.verdictOf w = v := by
  cases v with
  | grant k c hs t hd kh bd =>
    simp only [Wire.verdictWire?] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨hs', hhs, t', ht, hd', hhd, kh', hkh, bd', hbd, hw⟩ := h
      simp only [pure, Option.some.injEq] at hw
      subst hw
      simp only [Wire.verdictOf, bytes?_val hhs, bytes?_val ht, bytes?_val hhd, bytes?_val hkh, bytes?_val hbd]
      simp
    · cases h
  | refuse why =>
    simp only [Wire.verdictWire?, pure, Option.some.injEq] at h
    subst h
    simp only [Wire.verdictOf]
    have := ofCode?_code why
    simp [this]

/-! ## The printed string is one JSON string whose contents are the text -/

private theorem push_data (a : ByteArray) (x : UInt8) : (a.push x).data.toList = a.data.toList ++ [x] := by
  simp [ByteArray.push]

private theorem esc_data (acc : ByteArray) (x : UInt8) :
    (Broker.Json.esc acc x).data.toList = acc.data.toList ++ Json.escL x := by
  unfold Broker.Json.esc Json.escL
  split
  · simp
  · split
    · simp
    · split <;> simp

private theorem foldl_data (l : List UInt8) (acc : ByteArray) :
    (l.foldl Broker.Json.esc acc).data.toList = acc.data.toList ++ l.flatMap Json.escL := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, esc_data]

theorem str_data (acc b : ByteArray) :
    (Broker.Json.str acc b).data.toList = acc.data.toList ++ 34 :: b.data.toList.flatMap Json.escL ++ [34] := by
  have h := foldl_data b.data.toList (acc.push 34)
  rw [Array.foldl_toList] at h
  simp only [Broker.Json.str, push_data, h, List.append_assoc, List.cons_append, List.nil_append]

private theorem hex_round : ∀ n, n < 16 → Json.hexVal (Broker.Json.hexDigit n) = some n := by decide

private theorem unstr_esc (x : UInt8) (L : List UInt8) :
    Json.unstr (Json.escL x ++ L) = (Json.unstr L).map fun (c, r) => (x :: c, r) := by
  unfold Json.escL
  split
  · rename_i h1; simp at h1; subst h1; simp only [List.cons_append, List.nil_append]; rw [Json.unstr.eq_def]; simp
  · split
    · rename_i h1 h2; simp at h2; subst h2; simp only [List.cons_append, List.nil_append]; rw [Json.unstr.eq_def]; simp
    · split
      · rename_i h1 h2 h3
        have hx : x.toNat < 32 := by simpa [UInt8.lt_iff_toNat_lt] using h3
        have ha := hex_round (x.toNat / 16) (by omega)
        have hb := hex_round (x.toNat % 16) (by omega)
        have hv : x.toNat / 16 * 16 + x.toNat % 16 = x.toNat := by omega
        simp only [List.cons_append, List.nil_append]; rw [Json.unstr.eq_def]
        simp [ha, hb, hv, hx]
      · rename_i h1 h2 h3
        simp only [List.cons_append, List.nil_append]; rw [Json.unstr.eq_def]
        simp_all
        intro h; exact absurd h (by simpa [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le] using h3)

/-- Reading a JSON string after `str`'s opening quote gives back exactly the text, and stops at
`str`'s closing quote: no text a resident sends can end the string early or add a field. -/
theorem unstr_str (t : List UInt8) (rest : List UInt8) :
    Json.unstr (t.flatMap Json.escL ++ 34 :: rest) = some (t, rest) := by
  induction t with
  | nil => rw [List.flatMap_nil, List.nil_append, Json.unstr.eq_def]; simp
  | cons x xs ih => rw [List.flatMap_cons, List.append_assoc, unstr_esc, ih]; rfl

private theorem lit_data (acc : ByteArray) (s : String) :
    (Broker.Json.lit acc s).data.toList = acc.data.toList ++ Json.u s := by
  simp [Broker.Json.lit, Json.u]

private theorem str_spec (acc b : ByteArray) :
    (Broker.Json.str acc b).data.toList = acc.data.toList ++ Json.strSpec b := by
  rw [str_data]; simp [Json.strSpec]

private theorem message_data (acc : ByteArray) (r : String) (t : ByteArray) :
    (Broker.Json.message acc r t).data.toList = acc.data.toList ++ Json.msgSpec r t := by
  simp [Broker.Json.message, Json.msgSpec, lit_data, str_spec]

private theorem messages_data : ∀ (acc : ByteArray) (ms : List (String × ByteArray)),
    (Broker.Json.messages acc ms).data.toList = acc.data.toList ++ Json.msgsSpec ms
  | acc, [] => by simp [Broker.Json.messages, Json.msgsSpec]
  | acc, [(r, t)] => by simp [Broker.Json.messages, Json.msgsSpec, message_data]
  | acc, (r, t) :: m :: ms => by
    simp only [Broker.Json.messages, messages_data, lit_data, message_data, Json.msgsSpec, List.append_assoc]

private theorem roleName_some {r : UInt8} {rn : String} (h : roleName r = some rn) :
    rn = "user" ∨ rn = "assistant" := by
  unfold roleName at h; split at h <;> simp_all

private theorem mapM_roles : ∀ (l : List (UInt8 × ByteArray)) (ms : List (String × ByteArray)),
    l.mapM (fun (p : UInt8 × ByteArray) => match roleName p.1 with
      | some rn => (Except.ok (rn, p.2) : Except Broker.Refusal (String × ByteArray))
      | none => Except.error Broker.Refusal.messagesMalformed) = .ok ms →
    ms.map Prod.snd = l.map Prod.snd ∧ l.map (fun p => roleName p.1) = ms.map (fun m => some m.1)
  | [], ms, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; simp
  | (r, t) :: l, ms, h => by
    rw [List.mapM_cons] at h
    cases hr : roleName r with
    | none => simp [hr, bind, Except.bind] at h
    | some rn =>
      simp only [hr, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i ms' hms
        simp only [Except.ok.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := mapM_roles l ms' hms
        exact ⟨by simp [h1], by simp [hr, h2]⟩

/-- The body has exactly the specified shape: every value is printed as a `strSpec` string (so, by
`unstr_str`, read back exactly and closed by its own quote) or the numeral of the ask's
`maxTokens`; message `i` carries the ask's text `i` with the role `roleName` gives the ask's role
byte `i` (`user` for 0, `assistant` for 1), and no role byte or text is dropped. -/
theorem body_shape {ask : Ask} {body : ByteArray} (h : requestBody ask = .ok body) :
    ∃ ms : List (String × ByteArray), ms.map Prod.snd = ask.texts ∧
      ask.roles.data.toList.map roleName = ms.map (fun m => some m.1) ∧
      body.data.toList = Json.bodySpec ask.model ask.maxTokens ask.system ms := by
  unfold requestBody at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | cases h | skip
  all_goals
    rename_i hn _ _ ms hms hs
    have hr : ask.texts.length = ask.roles.size := by
      simp only [not_or] at hn; exact Decidable.of_not_not hn.2.1
    obtain ⟨h1, h2⟩ := mapM_roles _ _ hms
    have hlen : ask.roles.data.toList.length = ask.texts.length := by
      rw [Array.length_toList, hr]; rfl
    refine ⟨ms, by rw [h1, List.map_snd_zip (by omega)], ?_, ?_⟩
    · have hz := List.map_fst_zip (l₁ := ask.roles.data.toList) (l₂ := ask.texts) (by omega)
      rw [← h2, show (fun p : UInt8 × ByteArray => roleName p.1) = roleName ∘ Prod.fst from rfl,
        ← List.map_map, hz]
    simp [lit_data, messages_data, str_spec, Json.bodySpec, hs, List.append_assoc]

/-! ## Every verdict `step` returns has a frame (HOSTING-12's owed theorem) -/

/-- A grant's charge fits its allowance's cap, and the cap is below `capMax`. -/
theorem grant_cap {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask} {b' : Broker} {g : Grant}
    (h : Broker.decide b now r ask = .ok (b', g)) : g.charged < Bounds.capMax := by
  unfold Broker.decide at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | cases h | skip
  rename_i _ _ _ e he hm _ _ _ _ _ _ _ _ _ _ hc
  have hcap : e.allowance.cap < Bounds.capMax := by
    simp only [Allowance.malformed, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hm
    omega
  dsimp only
  omega

/-- The size the verdict codec writes for a refusal, and for a grant with body `bd`. -/
private theorem refuse_size (w : Wire.VerdictTy) (hw : w.1 = ⟨1, by decide⟩) :
    Wire.verdictCodec.size w = 2 := by
  obtain ⟨⟨s, hs⟩, v⟩ := w
  simp only [Fin.mk.injEq] at hw
  subst hw
  rfl

/-- Every provider's fixed request fields fit the 4096 bytes `bodyMax` leaves in a verdict frame. -/
theorem providerOf_fits {m : ByteArray} {u : Upstream} (h : providerOf m = some u) :
    u.host.size + u.target.size + u.headers.size + u.keyHeader.size ≤ 4096 - 33 := by
  unfold providerOf at h
  obtain ⟨x, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  have hm := List.mem_of_find?_eq_some hf
  simp only [providers, List.mem_cons, List.not_mem_nil, or_false] at hm
  subst hm
  decide

/-- The verdict of every `step` encodes in one frame: a refusal is two bytes, and a grant's fields
(Lean's body within `bodyMax`, the provider's fixed request fields, a charge below `capMax`) fit
`frameMax`. So
`hosting-broker`'s `unencodable` end is unreachable: an assertion, never a path. -/
theorem step_encodes (b : Broker) (r : ByteArray) (now : Nat) (askBytes : ByteArray) :
    (Wire.encodeVerdict (Broker.step b r now askBytes).2).isSome = true := by
  have refuse : ∀ why, (Wire.encodeVerdict (.refuse why)).isSome = true := fun why => by
    simp only [Wire.encodeVerdict, Wire.verdictWire?, pure, bind, Option.bind]
    rw [← verdictCodec_lawful.size_eq, refuse_size _ rfl]
    simp [Bounds.frameMax]
  unfold Broker.step
  split
  · exact refuse _
  · split
    · rename_i ask _ b'' g hd
      have hc := grant_cap hd
      obtain ⟨-, -, -, -, -, -, -, -, -, hpv, -, -, -, -, hbs, -⟩ := grant_allowed hd
      have hsz := providerOf_fits hpv
      have hc64 : g.charged < 2 ^ 64 := by unfold Bounds.capMax at hc; omega
      have hb : g.body.size ≤ Bounds.frameMax := by unfold Bounds.bodyMax at hbs; omega
      have hs : g.upstream.host.size ≤ Bounds.frameMax := by unfold Bounds.frameMax; omega
      have ht : g.upstream.target.size ≤ Bounds.frameMax := by unfold Bounds.frameMax; omega
      have hh : g.upstream.headers.size ≤ Bounds.frameMax := by unfold Bounds.frameMax; omega
      have hk : g.upstream.keyHeader.size ≤ Bounds.frameMax := by unfold Bounds.frameMax; omega
      simp only [Wire.encodeVerdict, Wire.verdictWire?, hc64, dite_true, Wire.bytes?, hs, ht, hh, hk, hb,
        bind, Option.bind, pure]
      rw [← verdictCodec_lawful.size_eq]
      show (if 1 + (4 + (8 + ((4 + g.upstream.host.size) + ((4 + g.upstream.target.size) +
          ((4 + g.upstream.headers.size) + ((4 + g.upstream.keyHeader.size) + ((4 + g.body.size) + 0))))))) ≤
          Bounds.frameMax then _ else none).isSome = true
      rw [if_pos (by unfold Bounds.bodyMax Bounds.frameMax at hbs; unfold Bounds.frameMax; omega)]
      rfl
    · exact refuse _

/-! ## Teeth: closed instances that make the general theorems non-vacuous -/

private def alw : Allowance := ⟨"claude-m".toUTF8, 7, 1000, 60000, 1000, 100⟩
private def res : ByteArray := "r1".toUTF8
private def b0 : Broker := Broker.start 0 [7] [(res, alw)]
private def ask1 : Ask := ⟨"claude-m".toUTF8, 10, .empty, ⟨#[0]⟩, ["hi\",\"max_tokens\":99999".toUTF8]⟩

private def refusedBy (why : Broker.Refusal) : Except Broker.Refusal (Broker × Grant) → Bool
  | .error w => w == why
  | .ok _ => false

private def chargedIs (slot : UInt32) (c : Nat) : Except Broker.Refusal (Broker × Grant) → Bool
  | .ok (_, g) => g.keySlot == slot && g.charged == c
  | .error _ => false

/-- The body Lean prints carries the resident's text as one string: the smuggled `max_tokens` stays
inside `content`. -/
private def bodyIs (x : ByteArray) : Except Broker.Refusal ByteArray → Bool
  | .ok b => b == x
  | .error _ => false

theorem body_tooth : bodyIs "{\"model\":\"claude-m\",\"max_tokens\":10,\"messages\":[{\"role\":\"user\",\"content\":\"hi\\\",\\\"max_tokens\\\":99999\"}]}".toUTF8 (requestBody ask1) = true := by
  decide +kernel

/-- A fresh life refuses a costing ask in its start window (`overSpend`), and grants it in the next
window, charging the worst case (`(40 body bytes + 10) × 1000 / 1000`, rounded up) to key slot 7. -/
theorem forfeit_tooth :
    refusedBy .overSpend (Broker.decide b0 5 res ask1) = true ∧
    chargedIs 7 ((requestBody ask1).toOption.map (fun bd => bd.size + 10) |>.getD 0)
      (Broker.decide b0 60000 res ask1) = true := by
  decide +kernel

/-- Each of decide's own refusals is reachable by name. -/
theorem refusal_teeth :
    refusedBy .noAllowance (Broker.decide b0 60000 "r2".toUTF8 ask1) = true ∧
    refusedBy .clockRegressed (Broker.decide { b0 with last := 70000 } 60000 res ask1) = true ∧
    refusedBy .modelNotAllowed (Broker.decide b0 60000 res { ask1 with model := "claude-n".toUTF8 }) = true ∧
    refusedBy .tokensZero (Broker.decide b0 60000 res { ask1 with maxTokens := 0 }) = true ∧
    refusedBy .tokensOver (Broker.decide b0 60000 res { ask1 with maxTokens := 101 }) = true ∧
    refusedBy .messagesMalformed (Broker.decide b0 60000 res { ask1 with roles := ⟨#[2]⟩ }) = true ∧
    refusedBy .messagesMalformed (Broker.decide b0 60000 res { ask1 with roles := .empty }) = true ∧
    refusedBy .textNotUtf8 (Broker.decide b0 60000 res { ask1 with system := ⟨#[0xff]⟩ }) = true ∧
    refusedBy .allowanceMalformed
      (Broker.decide (Broker.start 0 [7] [(res, { alw with windowMs := 0 })]) 60000 res ask1) = true ∧
    refusedBy .allowanceMalformed
      (Broker.decide (Broker.start 0 [7] [(res, { alw with microPerKTok := 0 })]) 60000 res ask1) = true ∧
    refusedBy .allowanceMalformed
      (Broker.decide (Broker.start 0 [7, 2 ^ 32 + 7] [(res, { alw with keySlot := 2 ^ 32 + 7 })]) 60000 res ask1)
      = true ∧
    refusedBy .keyMissing (Broker.decide (Broker.start 0 [8] [(res, alw)]) 60000 res ask1) = true ∧
    refusedBy .keyMissing (Broker.decide (Broker.start 0 [8] [(res, alw)]) 5 res ask1) = true ∧
    refusedBy .allowanceAmbiguous
      (Broker.decide (Broker.start 0 [7] [(res, alw), (res, { alw with cap := 5 })]) 60000 res ask1) = true ∧
    refusedBy .noProvider
      (Broker.decide (Broker.start 0 [7] [(res, { alw with model := "gpt-m".toUTF8 })]) 60000 res
        { ask1 with model := "gpt-m".toUTF8 }) = true ∧
    refusedBy .noProvider
      (Broker.decide (Broker.start 0 [8] [(res, { alw with model := "gpt-m".toUTF8 })]) 5 res
        { ask1 with model := "gpt-m".toUTF8 }) = true := by
  decide +kernel

/-- The provider table names Anthropic for `claude-…` and nothing for a name that only resembles it,
and a grant carries the table's provider (`Grant.upstream`). With one row, `step` writing the constant
`anthropic` into the verdict instead of `g.upstream` would pass this too (HOSTING-15's CRITIQUE). -/
theorem provider_teeth :
    providerOf "claude-m".toUTF8 = some anthropic ∧ anthropic.host = "api.anthropic.com".toUTF8 ∧
    providerOf "claude".toUTF8 = none ∧ providerOf "xclaude-m".toUTF8 = none ∧
    providerOf "Claude-m".toUTF8 = none ∧
    (match Broker.decide b0 60000 res ask1 with
     | .ok (_, g) => g.upstream == anthropic
     | _ => false) = true := by
  decide +kernel

/-- `keyMissing` is Lean's, by the slot set keybroker passed: the ask on model `n` (slot 9) is
refused when keybroker holds only slot 7, and granted on slot 9 when it holds both. Two allowances of
one resident on DIFFERENT models are not ambiguous: each is its own meter. -/
theorem keyMissing_tooth :
    chargedIs 9 ((requestBody { ask1 with model := "claude-n".toUTF8 }).toOption.map (fun bd => bd.size + 10) |>.getD 0) (Broker.decide (Broker.start 0 [7, 9] [(res, alw), (res, { alw with model := "claude-n".toUTF8, keySlot := 9 })])
      60000 res { ask1 with model := "claude-n".toUTF8 }) = true ∧
    refusedBy .keyMissing (Broker.decide (Broker.start 0 [7] [(res, alw), (res, { alw with model := "claude-n".toUTF8, keySlot := 9 })])
      60000 res { ask1 with model := "claude-n".toUTF8 }) = true := by
  decide +kernel

private def ask2 : Ask := { ask1 with texts := ["hi".toUTF8] }
private def b100 : Broker := Broker.start 0 [7] [(res, { alw with cap := 100 })]

/-- Spend accumulates within a window: with a cap of 100, the first ask (charged 90: 80 body bytes
and 10 tokens) is granted, the same ask again in that window is refused `overSpend`, and in the next
window it is granted again. -/
theorem accumulate_tooth :
    (match Broker.decide b100 60000 res ask2 with
     | .ok (b1, g1) =>
       g1.charged == 90 && refusedBy .overSpend (Broker.decide b1 60001 res ask2) &&
         chargedIs 7 90 (Broker.decide b1 120000 res ask2)
     | .error _ => false) = true := by
  decide +kernel

/-- A follow that finds the allowance unchanged keeps its meter (the second ask in the window is
`overSpend`, as without a follow); a follow that finds it CHANGED (cap 100 → 200) opens it spent to
the new cap, so the window is forfeit even though the new cap would fit (HOSTING-13's rule), and the
next window grants. -/
theorem follow_tooth :
    (match Broker.decide b100 60000 res ask2 with
     | .ok (b1, _) =>
       refusedBy .overSpend (Broker.decide (b1.follow 60001 [(res, { alw with cap := 100 })]) 60001 res ask2) &&
       refusedBy .overSpend (Broker.decide (b1.follow 60001 [(res, { alw with cap := 200 })]) 60001 res ask2) &&
       chargedIs 7 90 (Broker.decide (b1.follow 60001 [(res, { alw with cap := 200 })]) 120000 res ask2) &&
       refusedBy .noAllowance (Broker.decide (b1.follow 60001 []) 120000 res ask2)
     | .error _ => false) = true := by
  decide +kernel

/-- An ask frame that does not decode is refused `badAsk` and leaves the broker as it was. -/
theorem badAsk_tooth : (match Broker.step b0 res 60000 ⟨#[7, 0]⟩ with
    | (b, .refuse .badAsk) => b.last == b0.last
    | _ => false) = true := by
  decide +kernel

/-- A system text is printed as one escaped string too. -/
theorem system_tooth : bodyIs
    "{\"model\":\"claude-m\",\"max_tokens\":10,\"system\":\"s\\\"\",\"messages\":[{\"role\":\"user\",\"content\":\"hi\"}]}".toUTF8
    (requestBody { ask1 with system := "s\"".toUTF8, texts := ["hi".toUTF8] }) = true := by
  decide +kernel

end Nanodregg.Hosting.Proofs.Broker
