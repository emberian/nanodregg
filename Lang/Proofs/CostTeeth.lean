/-
# Lang.Proofs.CostTeeth — the price of a 64 KiB `cat`, and the machine that did not pay it (LANG-64)

`cat64_price`: for every two byte strings holding 64 KiB between them, `cat` of their literals
returns under 2053 ticks and not under 2052: 2048 for the primitive (a tick per 32 bytes), 5 for
the term around it. `cat64_walks`: that run walks exactly the 65,536 operand bytes, so `walked` does
not read 0 by construction. `cat64_flat`: the machine before LANG-64 (`Need.flatStep`, the deployed
step except that a primitive computes on its first tick) returns the same value in 6 ticks while
`walkedBy` counts its 65,536 bytes, so `walked_le` is false for it, and 6 is below the cat's
reference size 2050, so `derives_lt_used` is false for it too. `law_walks_le`: no law run, of any
term under any closure, walks more than `wordBytes * lawTicks` = 3,200,000 primitive operand bytes;
before LANG-64 one law run could copy about 6.5 GB.
-/
import Lang.Proofs.Cost
import Lang.Proofs.Complete
import Lang.Proofs.Run
import Lang.Sim.Need

namespace Nanodregg.Lang

variable {lib : List Term}

/-- Paying a primitive's ticks: `i` transitions move its frame from `j` paid to `j + i` paid. -/
private theorem pay_reach {cap : Nat} {p : Prim} {a v : Val} {k : List Frame} {d : Nat} (hd : d ≤ cap) :
    ∀ (i j : Nat), j + i < primTicks p a v →
      Reach lib cap ⟨.ret v, .primR p a j :: k, d⟩ ⟨.ret v, .primR p a (j + i) :: k, d⟩ i
  | 0, j, _ => .refl
  | i + 1, j, h => by
    have hj : j + 1 < primTicks p a v := by omega
    have r := pay_reach (p := p) (a := a) (v := v) (k := k) hd i (j + 1) (by omega)
    rw [show j + 1 + i = j + (i + 1) by omega] at r
    exact .next (by simp [step, primStep, hj]) hd r

private def cat64 (a b : ByteArray) : Term := .prim .cat (.bytes a) (.bytes b)

private theorem cat64_ticks {a b : ByteArray} (h : a.size + b.size = 65536) :
    primTicks .cat (.bytes a) (.bytes b) = 2048 := by
  simp only [primTicks, primBytes, h]
  decide

/-- From the start to the cat's result: 4 transitions to its operands, 2047 paying, 1 computing. -/
private theorem cat64_reach {a b : ByteArray} {cap : Nat} (hc : 1 ≤ cap) (h : a.size + b.size = 65536) :
    Reach lib cap (State.init (cat64 a b)) ⟨.ret (.bytes (a ++ b)), [], 0⟩ 2052 := by
  have ht := cat64_ticks h
  have hm : a.size + b.size ≤ Bounds.bytesMax := by
    rw [h]; decide
  have r4 : Reach lib cap (State.init (cat64 a b)) ⟨.ret (.bytes b), [.primR .cat (.bytes a) 0], 1⟩ 4 :=
    .next rfl hc (.next rfl hc (.next rfl hc (.next rfl hc .refl)))
  have rp : Reach lib cap ⟨.ret (.bytes b), [.primR .cat (.bytes a) 0], 1⟩
      ⟨.ret (.bytes b), [.primR .cat (.bytes a) 2047], 1⟩ 2047 := by
    have := pay_reach (lib := lib) (k := []) hc 2047 0 (by rw [ht]; decide)
    simpa using this
  have rc : Reach lib cap ⟨.ret (.bytes b), [.primR .cat (.bytes a) 2047], 1⟩
      ⟨.ret (.bytes (a ++ b)), [], 0⟩ 1 :=
    .next (by simp [step, primStep, ht, primEval, hm]) (by simp) .refl
  exact (r4.trans rp).trans rc

/-- **A 64 KiB `cat` costs 2053 ticks**: it returns under 2053 and is refused by the budget under
2052, after the tick that computed it and before the halt. -/
theorem cat64_price {a b : ByteArray} {cap : Nat} (hc : 1 ≤ cap) (h : a.size + b.size = 65536) :
    run lib cap 2053 0 (State.init (cat64 a b)) = .value (.bytes (a ++ b)) 2053 ∧
      run lib cap 2052 0 (State.init (cat64 a b)) = .fault .ticks 2052 := by
  have r := cat64_reach (lib := lib) hc h
  refine ⟨?_, ?_⟩
  · rw [run_reach r 1 0]; simp [run, step]
  · rw [run_reach r 0 0]; simp [run]

/-- **The plant: the machine before LANG-64 charged it 6 ticks.** `Need.flatStep` computes the cat
on its first tick. It returns the same value in 6 ticks, walking 65,536 bytes, so `walked_le` is
FALSE for it, and it pays fewer ticks than the cat's reference derivation requires (2050), so
`derives_lt_used` is false for it too. The deployed step is what makes both true. -/
theorem cat64_flat {a b : ByteArray} (h : a.size + b.size = 65536) :
    Need.runBy (Need.flatStep lib) 8 6 0 (State.init (cat64 a b)) = .value (.bytes (a ++ b)) 6 ∧
      walkedBy (Need.flatStep lib) 8 6 (State.init (cat64 a b)) = 65536 ∧
      ¬ walkedBy (Need.flatStep lib) 8 6 (State.init (cat64 a b)) ≤ Bounds.wordBytes * 6 ∧
      Derives lib [] (cat64 a b) (primEval .cat (.bytes a) (.bytes b)) 2050 ∧
      ¬ 2050 < (Need.runBy (Need.flatStep lib) 8 6 0 (State.init (cat64 a b))).used := by
  have hm : a.size + b.size ≤ Bounds.bytesMax := by
    rw [h]; decide
  have hm' : 65536 ≤ Bounds.bytesMax := by decide
  have hw : walkedBy (Need.flatStep lib) 8 6 (State.init (cat64 a b)) = 65536 := by
    simp [walkedBy, stepBytesBy, Need.flatStep, step, push, cat64, State.init, primEval,
      Step.pays, primBytes, h, hm']
  have hr : Need.runBy (Need.flatStep lib) 8 6 0 (State.init (cat64 a b)) = .value (.bytes (a ++ b)) 6 := by
    simp [Need.runBy, Need.flatStep, step, push, cat64, State.init, primEval, hm]
  refine ⟨hr, hw, ?_, ?_, by rw [hr]; simp [Outcome.used]⟩
  · rw [hw]; decide
  · have d := Derives.prim (lib := lib) (env := []) (p := .cat) (Derives.bytes (s := a))
      (Derives.bytes (s := b)) (by simp [primEval, hm])
    rw [cat64_ticks h] at d
    exact d

private theorem walked_cons {cap f : Nat} {s s' : State} (hs : step lib s = .next s')
    (hd : s'.depth ≤ cap) :
    walked lib cap (f + 1) s = stepBytesBy (step lib) s + walked lib cap f s' := by
  simp [walkedBy, hs, show ¬ cap < s'.depth by omega]

/-- Paying walks nothing: `i` paying transitions leave the count to the frame `i` ticks later. -/
private theorem walked_pay {cap m : Nat} {p : Prim} {a v : Val} {k : List Frame} {d : Nat} (hd : d ≤ cap) :
    ∀ (i j : Nat), j + i < primTicks p a v →
      walked lib cap (i + m) ⟨.ret v, .primR p a j :: k, d⟩ =
        walked lib cap m ⟨.ret v, .primR p a (j + i) :: k, d⟩
  | 0, j, _ => by simp
  | i + 1, j, h => by
    have hj : j + 1 < primTicks p a v := by omega
    have hs : step lib ⟨.ret v, .primR p a j :: k, d⟩ = .next ⟨.ret v, .primR p a (j + 1) :: k, d⟩ := by
      simp [step, primStep, hj]
    rw [show i + 1 + m = (i + m) + 1 by omega, walked_cons hs hd]
    have h0 : stepBytesBy (step lib) ⟨.ret v, .primR p a j :: k, d⟩ = 0 := by
      simp [stepBytesBy, hs, Step.pays]
    rw [h0, Nat.zero_add, walked_pay hd i (j + 1) (by omega), show j + 1 + i = j + (i + 1) by omega]

/-- **The deployed run walks the cat's bytes, once, on its computing tick**: from the start, a run
long enough to return walks exactly the 65,536 operand bytes, so `walked` does not read 0 by
construction. -/
theorem cat64_walks {a b : ByteArray} {cap : Nat} (hc : 1 ≤ cap) (h : a.size + b.size = 65536) :
    walked lib cap 2053 (State.init (cat64 a b)) = 65536 := by
  have ht := cat64_ticks h
  have hm : a.size + b.size ≤ Bounds.bytesMax := by
    rw [h]; decide
  have hm' : 65536 ≤ Bounds.bytesMax := by decide
  rw [show 2053 = 2049 + 4 by rfl]
  rw [walked_cons (s' := ⟨.eval (.bytes a) [], [.primL .cat (.bytes b) []], 1⟩) rfl hc,
    walked_cons (s' := ⟨.ret (.bytes a), [.primL .cat (.bytes b) []], 1⟩) rfl hc,
    walked_cons (s' := ⟨.eval (.bytes b) [], [.primR .cat (.bytes a) 0], 1⟩) rfl hc,
    walked_cons (s' := ⟨.ret (.bytes b), [.primR .cat (.bytes a) 0], 1⟩) rfl hc]
  simp only [stepBytesBy, State.init, cat64, Nat.zero_add]
  rw [show 2049 = 2047 + 2 by rfl, walked_pay hc 2047 0 (by rw [ht]; decide)]
  have hs : step lib ⟨.ret (.bytes b), [.primR .cat (.bytes a) (0 + 2047)], 1⟩ =
      .next ⟨.ret (.bytes (a ++ b)), [], 0⟩ := by
    simp [step, primStep, ht, primEval, hm]
  rw [walked_cons hs (by simp)]
  simp [stepBytesBy, Step.pays, primBytes, h, hm', walkedBy, step, primStep, ht, primEval]

/-- **A law walks at most 3.2 MB of primitive operands**: whatever the term and closure, a run under
the law budget walks at most `wordBytes` primitive operand bytes per tick of `lawTicks`. (Label
comparisons, `env[i]?` and `extend`'s merges are bounded by Wire constants and not counted.) -/
theorem law_walks_le {t : Term} {env : Env} :
    walked lib Bounds.stackMax lawTicks (State.init t env) ≤ 3200000 := by
  have h1 := walked_le (lib := lib) (cap := Bounds.stackMax) (fuel := lawTicks) (t := t) (env := env)
  have h2 := run_used_le (lib := lib) (cap := Bounds.stackMax) lawTicks (State.init t env)
  have h3 : Bounds.wordBytes * (run lib Bounds.stackMax lawTicks 0 (State.init t env)).used ≤
      Bounds.wordBytes * lawTicks := Nat.mul_le_mul_left _ h2
  have : Bounds.wordBytes * lawTicks = 3200000 := by decide
  omega

end Nanodregg.Lang
