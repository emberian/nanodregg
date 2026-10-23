/-
# Lang.Proofs.NeedComplete — the counter is complete: `need` finds every derivation its fuel covers

`need_derives` (Lang.Proofs.Need) is the counter's soundness: what `need` returns is a sized
derivation. This module is its completeness: a derivation of size `n` is FOUND by `need` under
any fuel `f ≥ n` (`need_complete`, with its `Sel`/`Ext` twins), and what extraction must force,
of total size `m`, is counted by `needExtract` under any fuel `≥ m` (`needExtract_complete`). The
fuel `need` spends is nesting depth, and a derivation is at most as deep as it is large, so its
size is enough.

`requiredOf_total` closes cv 01a14aba-1281: for every invoke `runMeasured` admits, `requiredOf`
returns a count (never `required: fuel`, never `required: extraction`), and that count is below
the ticks charged. The budget is enough because the machine finished within it, and the machine
pays more than the derivation's size (`derives_lt_used`, `forces_le`). Tooth: one fuel short of
`idApp`'s size, `need` refuses.
-/
import Lang.Proofs.Need

namespace Nanodregg.Lang

open Nanodregg.Kernel
open Nanodregg.Kernel.Receive

variable {lib : List Term}

theorem derives_pos {env : Env} {t : Term} {r : Except Fault Val} {n : Nat}
    (h : Derives lib env t r n) : 0 < n := by
  cases h <;> first | omega | exact Nat.lt_of_lt_of_le primTicks_pos (Nat.le_add_left _ _)

theorem dsel_pos {v : Val} {ℓ : Label} {r : Except Fault Val} {n : Nat}
    (h : DSel lib v ℓ r n) : 0 < n := by
  cases h <;> omega

theorem dext_pos {v : Val} {fs : List (Label × Term)} {env : Env} {r : Except Fault Val} {n : Nat}
    (h : DExt lib v fs env r n) : 0 < n := by
  cases h <;> omega

theorem meaningful_of_ne {r : Except Fault Val} (h : r ≠ .error .stuck) : Need.meaningful r = true := by
  match r, h with
  | .ok _, _ => rfl
  | .error .overflow, _ | .error .underflow, _ | .error .divZero, _ | .error .tooLarge, _
  | .error .ticks, _ | .error .stack, _ | .error (.refused _), _ => rfl
  | .error .stuck, h => exact absurd rfl h

mutual
/-- **The counter is complete**: a derivation of size `n` is what `need` returns under any fuel
`f ≥ n`. -/
theorem need_complete : ∀ {env : Env} {t : Term} {r : Except Fault Val} {n : Nat},
    Derives lib env t r n → ∀ f, n ≤ f → Need.need lib f env t = some (r, n)
  | _, _, _, _, d, 0, h => absurd h (by have := derives_pos d; omega)
  | _, _, _, _, .var he, _ + 1, _ => by simp [Need.need, he]
  | _, _, _, _, .lam, _ + 1, _ | _, _, _, _, .nat, _ + 1, _ | _, _, _, _, .bool, _ + 1, _
  | _, _, _, _, .bytes, _ + 1, _ | _, _, _, _, .digest, _ + 1, _ | _, _, _, _, .refuse, _ + 1, _ | _, _, _, _, .hole, _ + 1, _
  | _, _, _, _, .record, _ + 1, _ => by simp [Need.need]
  | _, _, _, _, .app hf ha hb, f + 1, h => by
    simp [Need.need, need_complete hf f (by omega), need_complete ha f (by omega),
      need_complete hb f (by omega)]
  | _, _, _, _, .appF hf, f + 1, h => by simp [Need.need, need_complete hf f (by omega)]
  | _, _, _, _, .appA hf ha, f + 1, h => by
    simp [Need.need, need_complete hf f (by omega), need_complete ha f (by omega)]
  | _, _, _, _, .fix ht, f + 1, h => by simp [Need.need, need_complete ht f (by omega)]
  | _, _, _, _, .fixE ht, f + 1, h => by simp [Need.need, need_complete ht f (by omega)]
  | _, _, _, _, .prim (p := p) (x := x) (y := y) ha hb hp, f + 1, h => by
    have := primTicks_pos (p := p) (x := x) (y := y)
    simp [Need.need, need_complete ha f (by omega), need_complete hb f (by omega), meaningful_of_ne hp]
  | _, _, _, _, .primL ha, f + 1, h => by simp [Need.need, need_complete ha f (by omega)]
  | _, _, _, _, .primR ha hb, f + 1, h => by
    simp [Need.need, need_complete ha f (by omega), need_complete hb f (by omega)]
  | _, _, _, _, .get ht hs, f + 1, h => by
    simp [Need.need, need_complete ht f (by omega), needSel_complete hs f (by omega)]
  | _, _, _, _, .getE ht, f + 1, h => by simp [Need.need, need_complete ht f (by omega)]
  | _, _, _, _, .extend ht hx, f + 1, h => by
    simp [Need.need, need_complete ht f (by omega), needExt_complete hx f (by omega)]
  | _, _, _, _, .extendE ht, f + 1, h => by simp [Need.need, need_complete ht f (by omega)]
  | _, _, _, _, .inj ht, f + 1, h => by simp [Need.need, need_complete ht f (by omega)]
  | _, _, _, _, .injE ht, f + 1, h => by simp [Need.need, need_complete ht f (by omega)]
  | _, _, _, _, .case ht hf hb, f + 1, h => by
    simp [Need.need, need_complete ht f (by omega), hf, need_complete hb f (by omega)]
  | _, _, _, _, .caseE ht, f + 1, h => by simp [Need.need, need_complete ht f (by omega)]
  | _, _, _, _, .iteT hc ha, f + 1, h => by
    simp [Need.need, need_complete hc f (by omega), need_complete ha f (by omega)]
  | _, _, _, _, .iteF hc hb, f + 1, h => by
    simp [Need.need, need_complete hc f (by omega), need_complete hb f (by omega)]
  | _, _, _, _, .iteE hc, f + 1, h => by simp [Need.need, need_complete hc f (by omega)]
  | _, _, _, _, .ref hi hb, f + 1, h => by simp [Need.need, hi, need_complete hb f (by omega)]

theorem needSel_complete : ∀ {v : Val} {ℓ : Label} {r : Except Fault Val} {n : Nat},
    DSel lib v ℓ r n → ∀ f, n ≤ f → Need.needSel lib f v ℓ = some (r, n)
  | _, _, _, _, d, 0, h => absurd h (by have := dsel_pos d; omega)
  | _, _, _, _, .field hf hd, f + 1, h => by
    simp [Need.needSel, hf, need_complete hd f (by omega)]
  | _, _, _, _, .knot hd hs, f + 1, h => by
    simp [Need.needSel, need_complete hd f (by omega), needSel_complete hs f (by omega)]
  | _, _, _, _, .knotE hd, f + 1, h => by simp [Need.needSel, need_complete hd f (by omega)]

theorem needExt_complete : ∀ {v : Val} {fs : List (Label × Term)} {env : Env} {r : Except Fault Val}
    {n : Nat}, DExt lib v fs env r n → ∀ f, n ≤ f → Need.needExt lib f v fs env = some (r, n)
  | _, _, _, _, _, d, 0, h => absurd h (by have := dext_pos d; omega)
  | _, _, _, _, _, .record, _ + 1, _ => by simp [Need.needExt]
  | _, _, _, _, _, .knot hd hx, f + 1, h => by
    simp [Need.needExt, need_complete hd f (by omega), needExt_complete hx f (by omega)]
  | _, _, _, _, _, .knotE hd, f + 1, h => by simp [Need.needExt, need_complete hd f (by omega)]
end

theorem needForce_complete {fuel : Nat} {t : Term} {env : Env} {v : Val} {n : Nat}
    (hd : Derives lib env t (.ok v) n) (h : n ≤ fuel) : Need.needForce lib fuel t env = some (v, n) := by
  simp [Need.needForce, need_complete hd fuel h]

theorem needUnknot_complete {fuel : Nat} {v : Val} {fs : List (Label × (Term × Env))} {n : Nat}
    (hu : Unknots lib v fs n) : ∀ rounds, n ≤ fuel → n ≤ rounds →
      Need.needUnknot lib fuel rounds v = some (fs, n) := by
  induction hu with
  | record => intro rounds _ _; cases rounds <;> simp [Need.needUnknot]
  | knot hb _ ih =>
    intro rounds hf hr
    have := derives_pos hb
    obtain ⟨r, rfl⟩ : ∃ r, rounds = r + 1 := ⟨rounds - 1, by omega⟩
    simp [Need.needUnknot, needForce_complete (fuel := fuel) hb (by omega), ih r (by omega) (by omega)]

theorem needExtractArm_find {fuel : Nat} {w : Val} {ℓ : Label} {A : Ty} :
    ∀ {row : List (Label × Ty)}, Row.find? ℓ row = some A →
      Need.needExtractArm lib fuel row ℓ w = Need.needExtract lib fuel A w
  | [], h => by simp [Row.find?] at h
  | (k, B) :: row, h => by
    simp only [Row.find?] at h
    simp only [Need.needExtractArm]
    split
    · rw [if_pos ‹_›] at h; cases h; rfl
    · rw [if_neg ‹_›] at h; exact needExtractArm_find h

mutual
/-- **Extraction's counter is complete**: what extraction must force, of total size `m`, is what
`needExtract` counts under any fuel `≥ m`. -/
theorem needExtract_complete : ∀ {T : Ty} {v : Val} {m : Nat},
    Forces lib T v m → ∀ fuel, m ≤ fuel → Need.needExtract lib fuel T v = some m
  | _, _, _, .nat, _, _ | _, _, _, .bool, _, _ | _, _, _, .bytes, _, _
  | _, _, _, .digest, _, _ => by simp [Need.needExtract]
  | _, _, _, .record hu hr, fuel, h => by
    simp [Need.needExtract, needUnknot_complete (fuel := fuel) hu fuel (by omega) (by omega),
      needExtractRow_complete hr fuel (by omega)]
  | _, _, _, .sum hA hf, fuel, h => by
    simp only [Need.needExtract]
    rw [needExtractArm_find hA]
    exact needExtract_complete hf fuel h

theorem needExtractRow_complete : ∀ {row : List (Label × Ty)} {fs : List (Label × (Term × Env))} {m : Nat},
    ForcesRow lib row fs m → ∀ fuel, m ≤ fuel → Need.needExtractRow lib fuel row fs = some m
  | _, _, _, .nil, _, _ => by simp [Need.needExtractRow]
  | _, _, _, .cons hd hf hr, fuel, h => by
    simp [Need.needExtractRow, needForce_complete (fuel := fuel) hd (by omega), needExtract_complete hf fuel (by omega),
      needExtractRow_complete hr fuel (by omega)]
end

variable {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : ReceiptCheck}

/-- **The required count exists for every admitted invoke** (cv 01a14aba-1281): `requiredOf` never
refuses `required: fuel` or `required: extraction` on an invoke `runMeasured` admits; it counts,
and the count is below the ticks charged. -/
theorem requiredOf_total {rc : Lang.ReceiptCheck} {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)}
    {rows : List (RowSlot D × RowAct)} {ticks k : Nat}
    (hm : runMeasured bytesOf digestOf rc look rv pkg state method args r budget = .ok (s, calls, rows, ticks, k)) :
    ∃ N, Need.requiredOf bytesOf digestOf rc look rv pkg state method args r budget = .ok N ∧ N < ticks := by
  obtain ⟨S, v, used, d, left, hs, hr, he, rfl⟩ := runMeasured_setup hm
  obtain ⟨n, hd⟩ := bigStep_derives (run_bigStep hr)
  obtain ⟨m, hf⟩ := means_forces (extract_means _ S.ty he)
  obtain ⟨h1, h2⟩ := derives_lt_used hd hr
  have h3 := forces_le hf he
  have hq : Need.requiredOf bytesOf digestOf rc look rv pkg state method args r budget = .ok (n + m) := by
    simp [Need.requiredOf, bind, Except.bind, hs, need_complete hd budget (by omega),
      needExtract_complete hf budget (by omega), pure, Except.pure]
  -- the floor has one source: `required_lt_ticks`
  exact ⟨n + m, hq, required_lt_ticks hm hq⟩

/-! ## Teeth -/

private def idApp : Term := .app (.lam .nat (.var 0)) (.nat 1)

/-- The fuel premise is load-bearing: `need`'s fuel is nesting depth, `idApp`'s derivation is two
deep (size 4, `need_idApp`), and under one fuel `need` finds nothing. So "fuel ≥ size" is enough
(`need_complete`), not necessary: under fuel 2 it finds the whole size-4 derivation. -/
theorem need_idApp_short : Need.need [] 1 [] idApp = none := rfl

theorem need_idApp_depth : Need.need [] 2 [] idApp = some (.ok (.nat 1), 4) := rfl

end Nanodregg.Lang
