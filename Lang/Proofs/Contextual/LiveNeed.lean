/- The live WASTE denominator and charged machine run share one authenticated setup. -/
import Lang.Proofs.NeedComplete

namespace Nanodregg.Lang
open Nanodregg.Kernel Nanodregg.Kernel.Receive
variable {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}

theorem runMeasuredLive_setup {look : Pinned D} {rv : RowView D} {pkg : D}
    {state : Slots} {method : Nat} {args : ByteArray} {r : Req D} {budget : Nat}
    {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {ticks k : Nat}
    (h : runMeasuredLive bytesOf digestOf look rv pkg state method args r budget =
      .ok (s, calls, rows, ticks, k)) :
    ∃ (S : RunSetup) (v : Val) (used : Nat) (d : Data) (left : Nat),
      runSetupLive bytesOf digestOf look rv pkg state method args r = .ok S ∧
      S.preparation ≤ budget ∧
      run S.lib Bounds.stackMax (budget - S.preparation) 0 (State.init S.term S.env) = .value v used ∧
      (Machine.mk S.lib).extract S.ty (budget - S.preparation - used) v = .ok (d, left) ∧
      ticks = budget - left := by
  unfold runMeasuredLive runMeasuredWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, -, -, rfl, -⟩ := h
  exact ⟨_, _, _, _, _, ‹_›, by omega, ‹_›, ‹_›, rfl⟩

theorem requiredOfLive_spec {look : Pinned D} {rv : RowView D} {pkg : D}
    {state : Slots} {method : Nat} {args : ByteArray} {r : Req D} {budget N : Nat}
    (h : Need.requiredOfLive bytesOf digestOf look rv pkg state method args r budget = .ok N) :
    ∃ (S : RunSetup) (v : Val) (n m : Nat),
      runSetupLive bytesOf digestOf look rv pkg state method args r = .ok S ∧
      Derives S.lib S.env S.term (.ok v) n ∧ Forces S.lib S.ty v m ∧
      N = S.preparation + n + m := by
  unfold Need.requiredOfLive at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  cases h
  exact ⟨_, _, _, _, ‹_›, need_derives ‹_›, needExtract_forces _ ‹_›, rfl⟩

/-- Preparation is counted once on both sides; the remaining denominator is
the derivation of the very result returned by this live machine invocation. -/
theorem requiredLive_lt_ticks {look : Pinned D} {rv : RowView D} {pkg : D}
    {state : Slots} {method : Nat} {args : ByteArray} {r : Req D} {budget N : Nat}
    {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {ticks k : Nat}
    (hm : runMeasuredLive bytesOf digestOf look rv pkg state method args r budget =
      .ok (s, calls, rows, ticks, k))
    (hq : Need.requiredOfLive bytesOf digestOf look rv pkg state method args r budget = .ok N) :
    N < ticks := by
  obtain ⟨S, v, n, m, hs, hd, hf, rfl⟩ := requiredOfLive_spec hq
  obtain ⟨S', v', used, d, left, hs', hp, hr, he, rfl⟩ := runMeasuredLive_setup hm
  rw [hs] at hs'
  cases hs'
  have hv := bigStep_deterministic (derives_bigStep hd) (run_bigStep hr)
  cases hv
  obtain ⟨h1, h2⟩ := derives_lt_used hd hr
  have h3 := forces_le hf he
  omega

/-- Every successful deployed invocation has a complete required count within
its supplied budget; contextual preparation cannot make the denominator disappear. -/
theorem requiredOfLive_total {look : Pinned D} {rv : RowView D} {pkg : D}
    {state : Slots} {method : Nat} {args : ByteArray} {r : Req D} {budget : Nat}
    {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {ticks k : Nat}
    (hm : runMeasuredLive bytesOf digestOf look rv pkg state method args r budget =
      .ok (s, calls, rows, ticks, k)) :
    ∃ N, Need.requiredOfLive bytesOf digestOf look rv pkg state method args r budget = .ok N ∧
      N < ticks := by
  obtain ⟨S, v, used, d, left, hs, hp, hr, he, rfl⟩ := runMeasuredLive_setup hm
  obtain ⟨n, hd⟩ := bigStep_derives (run_bigStep hr)
  obtain ⟨m, hf⟩ := means_forces (extract_means _ S.ty he)
  obtain ⟨h1, h2⟩ := derives_lt_used hd hr
  have h3 := forces_le hf he
  have hq : Need.requiredOfLive bytesOf digestOf look rv pkg state method args r budget =
      .ok (S.preparation + n + m) := by
    simp [Need.requiredOfLive, bind, Except.bind, hs, need_complete hd budget (by omega),
      needExtract_complete hf budget (by omega), pure, Except.pure]
  exact ⟨_, hq, requiredLive_lt_ticks hm hq⟩

end Nanodregg.Lang
