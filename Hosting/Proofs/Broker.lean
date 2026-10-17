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

theorem decide_ok {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask} {b' : Broker} {g : Grant}
    (h : Broker.decide b now r ask = .ok (b', g)) :
    b.last ≤ now ∧ ∃ e ∈ b.entries, (e.resident == r) = true ∧ e.allowance.windowMs ≠ 0 ∧
      (e.meter.roll (windowOf e.allowance now)).spent + g.charged ≤ e.allowance.cap ∧
      b' = { last := now, entries := b.entries.map fun x => if x.resident == r then
        { e with meter := ⟨(e.meter.roll (windowOf e.allowance now)).window,
                           (e.meter.roll (windowOf e.allowance now)).spent + g.charged⟩ } else x } := by
  unfold Broker.decide at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | cases h | skip
  rename_i e he _ _ md _ _ _ _ _ body _ _ hc
  exact ⟨by omega, e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, by omega,
    by dsimp only; omega, rfl⟩

/-- What a grant is for: an allowed model of the resident's own allowance (its key slot, no
other), a token count within the allowance and the ceiling, and exactly the body `requestBody`
prints from the ask. -/
theorem grant_allowed {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask} {b' : Broker} {g : Grant}
    (h : Broker.decide b now r ask = .ok (b', g)) :
    ∃ e ∈ b.entries, (e.resident == r) = true ∧ ∃ md ∈ e.allowance.models, md.name = ask.model ∧
      0 < md.microPerKTok ∧ g.keySlot = md.keySlot ∧ 0 < ask.maxTokens ∧ ask.maxTokens ≤ e.allowance.maxTokens ∧
      ask.maxTokens ≤ Bounds.tokensCeiling ∧ requestBody ask = .ok g.body ∧ g.body.size ≤ Bounds.bodyMax ∧
      g.charged = cost md (g.body.size + ask.maxTokens) := by
  unfold Broker.decide at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | cases h | skip
  rename_i _ _ e he _ _ md hmd hmicro htz hto _ body hb hbs _
  refine ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, md,
    List.mem_of_find?_eq_some hmd, by simpa [ba_beq] using List.find?_some hmd, by omega, rfl, by omega, ?_, ?_, hb,
    by dsimp only; omega, rfl⟩
  · have := Nat.min_le_left e.allowance.maxTokens Bounds.tokensCeiling; omega
  · have := Nat.min_le_right e.allowance.maxTokens Bounds.tokensCeiling; omega

/-- Every meter of a fresh broker life is within its cap (it is AT its cap). -/
theorem inv_start (t0 : Nat) (rs : List (ByteArray × Allowance)) :
    ∀ e ∈ (Broker.start t0 rs).entries, e.meter.spent ≤ e.allowance.cap := by
  intro e he
  simp only [Broker.start, List.mem_map] at he
  obtain ⟨⟨r, a⟩, -, rfl⟩ := he
  exact Nat.le_refl _

/-- A grant keeps every meter within its cap: no resident is ever charged past its allowance. -/
theorem inv_decide {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask} {b' : Broker} {g : Grant}
    (hi : ∀ e ∈ b.entries, e.meter.spent ≤ e.allowance.cap)
    (h : Broker.decide b now r ask = .ok (b', g)) :
    ∀ e ∈ b'.entries, e.meter.spent ≤ e.allowance.cap := by
  obtain ⟨-, e, -, -, -, hc, rfl⟩ := decide_ok h
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  split
  · exact hc
  · exact hi y hy

/-- The forfeit invariant of a broker life started at `t0`: every meter's window lies between the
start window and the latest accepted time's window, and a meter still in the start window is spent
to its cap. -/
theorem fresh_start (t0 : Nat) (rs : List (ByteArray × Allowance)) :
    ∀ e ∈ (Broker.start t0 rs).entries, e.allowance.windowMs ≠ 0 →
      windowOf e.allowance t0 ≤ e.meter.window ∧
      e.meter.window ≤ windowOf e.allowance (Broker.start t0 rs).last ∧
      (e.meter.window = windowOf e.allowance t0 → e.allowance.cap ≤ e.meter.spent) := by
  intro e he _
  simp only [Broker.start, List.mem_map] at he ⊢
  obtain ⟨⟨r, a⟩, -, rfl⟩ := he
  exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ => Nat.le_refl _⟩

private theorem windowOf_mono (a : Allowance) {s t : Nat} (h : s ≤ t) : windowOf a s ≤ windowOf a t :=
  Nat.div_le_div_right h

/-- A grant keeps the forfeit invariant. -/
theorem fresh_decide {t0 : Nat} {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask} {b' : Broker} {g : Grant}
    (hf : ∀ e ∈ b.entries, e.allowance.windowMs ≠ 0 →
      windowOf e.allowance t0 ≤ e.meter.window ∧ e.meter.window ≤ windowOf e.allowance b.last ∧
      (e.meter.window = windowOf e.allowance t0 → e.allowance.cap ≤ e.meter.spent))
    (h : Broker.decide b now r ask = .ok (b', g)) :
    ∀ e ∈ b'.entries, e.allowance.windowMs ≠ 0 →
      windowOf e.allowance t0 ≤ e.meter.window ∧ e.meter.window ≤ windowOf e.allowance b'.last ∧
      (e.meter.window = windowOf e.allowance t0 → e.allowance.cap ≤ e.meter.spent) := by
  obtain ⟨hl, e, he, -, hw, -, rfl⟩ := decide_ok h
  intro x hx hxw
  simp only [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  by_cases hyr : (y.resident == r) = true
  · simp only [hyr, if_true]
    obtain ⟨h1, h2, h3⟩ := hf e he hw
    have hm := windowOf_mono e.allowance hl
    simp only [Meter.roll]
    split
    · rename_i hlt
      dsimp only
      refine ⟨by omega, Nat.le_refl _, fun heq => by omega⟩
    · exact ⟨h1, by omega, fun heq => Nat.le_trans (h3 heq) (Nat.le_add_right _ _)⟩
  · simp only [hyr, if_false, Bool.false_eq_true] at hxw ⊢
    obtain ⟨h1, h2, h3⟩ := hf y hy hxw
    exact ⟨h1, Nat.le_trans h2 (windowOf_mono y.allowance hl), h3⟩

/-- A restart refunds nothing: an ask in the start window of a broker life is granted only at cost
0, since the life opened that window spent to its cap (the `<` half of `hnow` is empty in a
reachable state: a life's clock never precedes its start). With `fresh_decide`, after any run of grants.
Across lives this needs the allowance unchanged: a new `windowMs` is a new budget, the operator's
act (decisions/hosting.md HOSTING-12). -/
theorem start_window_free {t0 : Nat} {b : Broker} {now : Nat} {r : ByteArray} {ask : Ask} {b' : Broker}
    {g : Grant}
    (hf : ∀ e ∈ b.entries, e.allowance.windowMs ≠ 0 →
      windowOf e.allowance t0 ≤ e.meter.window ∧ e.meter.window ≤ windowOf e.allowance b.last ∧
      (e.meter.window = windowOf e.allowance t0 → e.allowance.cap ≤ e.meter.spent))
    (hnow : ∀ e ∈ b.entries, (e.resident == r) = true → windowOf e.allowance now ≤ windowOf e.allowance t0)
    (h : Broker.decide b now r ask = .ok (b', g)) : g.charged = 0 := by
  obtain ⟨hl, e, he, hr, hw, hc, -⟩ := decide_ok h
  obtain ⟨h1, h2, h3⟩ := hf e he hw
  have hn := hnow e he hr
  have hm := windowOf_mono e.allowance hl
  simp only [Meter.roll] at hc
  split at hc
  · omega
  · have := h3 (by omega); omega

/-- The charge is the worst case: never less than the exact price of `tokens` tokens. -/
theorem cost_worst (md : Model) (tokens : Nat) : tokens * md.microPerKTok ≤ 1000 * cost md tokens := by
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
  | grant k c t hd kh bd =>
    simp only [Wire.verdictWire?] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨t', ht, hd', hhd, kh', hkh, bd', hbd, hw⟩ := h
      simp only [pure, Option.some.injEq] at hw
      subst hw
      simp only [Wire.verdictOf, bytes?_val ht, bytes?_val hhd, bytes?_val hkh, bytes?_val hbd]
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
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
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

/-! ## Teeth: closed instances that make the general theorems non-vacuous -/

private def mdl : Model := ⟨"m".toUTF8, 7, 1000⟩
private def alw : Allowance := ⟨60000, 1000, 100, [mdl]⟩
private def res : ByteArray := "r1".toUTF8
private def b0 : Broker := Broker.start 0 [(res, alw)]
private def ask1 : Ask := ⟨"m".toUTF8, 10, .empty, ⟨#[0]⟩, ["hi\",\"max_tokens\":99999".toUTF8]⟩

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

theorem body_tooth : bodyIs "{\"model\":\"m\",\"max_tokens\":10,\"messages\":[{\"role\":\"user\",\"content\":\"hi\\\",\\\"max_tokens\\\":99999\"}]}".toUTF8 (requestBody ask1) = true := by
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
    refusedBy .modelNotAllowed (Broker.decide b0 60000 res { ask1 with model := "n".toUTF8 }) = true ∧
    refusedBy .tokensZero (Broker.decide b0 60000 res { ask1 with maxTokens := 0 }) = true ∧
    refusedBy .tokensOver (Broker.decide b0 60000 res { ask1 with maxTokens := 101 }) = true ∧
    refusedBy .messagesMalformed (Broker.decide b0 60000 res { ask1 with roles := ⟨#[2]⟩ }) = true ∧
    refusedBy .messagesMalformed (Broker.decide b0 60000 res { ask1 with roles := .empty }) = true ∧
    refusedBy .textNotUtf8 (Broker.decide b0 60000 res { ask1 with system := ⟨#[0xff]⟩ }) = true ∧
    refusedBy .allowanceMalformed
      (Broker.decide (Broker.start 0 [(res, { alw with windowMs := 0 })]) 60000 res ask1) = true ∧
    refusedBy .allowanceMalformed
      (Broker.decide (Broker.start 0 [(res, { alw with models := [{ mdl with microPerKTok := 0 }] })])
        60000 res ask1) = true := by
  decide +kernel

private def ask2 : Ask := { ask1 with texts := ["hi".toUTF8] }
private def b100 : Broker := Broker.start 0 [(res, { alw with cap := 100 })]

/-- Spend accumulates within a window: with a cap of 100, the first ask (charged 83: 73 body bytes
and 10 tokens) is granted, the same ask again in that window is refused `overSpend`, and in the next
window it is granted again. -/
theorem accumulate_tooth :
    (match Broker.decide b100 60000 res ask2 with
     | .ok (b1, g1) =>
       g1.charged == 83 && refusedBy .overSpend (Broker.decide b1 60001 res ask2) &&
         chargedIs 7 83 (Broker.decide b1 120000 res ask2)
     | .error _ => false) = true := by
  decide +kernel

/-- An ask frame that does not decode is refused `badAsk` and leaves the broker as it was. -/
theorem badAsk_tooth : (match Broker.step b0 res 60000 ⟨#[7, 0]⟩ with
    | (b, .refuse .badAsk) => b.last == b0.last
    | _ => false) = true := by
  decide +kernel

/-- A system text is printed as one escaped string too. -/
theorem system_tooth : bodyIs
    "{\"model\":\"m\",\"max_tokens\":10,\"system\":\"s\\\"\",\"messages\":[{\"role\":\"user\",\"content\":\"hi\"}]}".toUTF8
    (requestBody { ask1 with system := "s\"".toUTF8, texts := ["hi".toUTF8] }) = true := by
  decide +kernel

end Nanodregg.Hosting.Proofs.Broker
