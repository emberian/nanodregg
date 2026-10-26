/-
# Lang.Proofs.Cost — a tick walks at most one word of bytes (LANG-64; LANG-L made a theorem)

LANG-L reads the tick as a unit of work: every step O(1). Before LANG-64 that was false for the
byte primitives: `cat` copied up to 64 KiB and `beq` compared up to 128 KiB in ONE tick, so one law
run under `lawTicks` could copy about 6.5 GB. LANG-64 charges a primitive `primTicks`: one tick per
`Bounds.wordBytes` (32) bytes its operands hold, rounded up, at least one; it pays them first and
computes on the last (`primStep`).

`primBytes_le`: a primitive walks at most `wordBytes` bytes per tick it is charged.
`walked_le`: a whole run walks at most `wordBytes` primitive operand bytes per tick it reports (`used`), whatever its
budget and however it ends, so a run cut off by its budget while a primitive is paying has walked
none of that primitive's bytes. `primTicks_word`: a primitive on at most one word costs one tick,
as before. `primBytes_cat`: a `cat`'s count is the size of the bytes it writes.
-/
import Lang.Eval

namespace Nanodregg.Lang

theorem primTicks_pos {p : Prim} {x y : Val} : 0 < primTicks p x y := Nat.succ_pos _

/-- **A primitive walks at most one word per tick it is charged.** -/
theorem primBytes_le (p : Prim) (x y : Val) : primBytes p x y ≤ Bounds.wordBytes * primTicks p x y := by
  unfold primTicks
  have hw : 0 < Bounds.wordBytes := by decide
  have := Nat.lt_mul_div_succ (primBytes p x y - 1) hw
  omega

/-- A primitive on at most one word of bytes costs one tick: the charge before LANG-64. -/
theorem primTicks_word {p : Prim} {x y : Val} (h : primBytes p x y ≤ Bounds.wordBytes) :
    primTicks p x y = 1 := by
  unfold primTicks
  have hw : 0 < Bounds.wordBytes := by decide
  have : (primBytes p x y - 1) / Bounds.wordBytes = 0 := Nat.div_eq_of_lt (by omega)
  omega

/-- A primitive walks bytes only where its operands are bytes or digests: every arithmetic and
comparison primitive, and `lenLe`, costs one tick. -/
theorem primTicks_nat {p : Prim} {a b : Nat} : primTicks p (.nat a) (.nat b) = 1 := by
  cases p <;> simp [primTicks, primBytes]

theorem primTicks_lenLe {a : ByteArray} {n : Nat} : primTicks .lenLe (.bytes a) (.nat n) = 1 := by
  simp [primTicks, primBytes]

/-- `beq` is charged for both operands, whatever their sizes: `decide (a = b)` on `ByteArray` is
`ByteArray.ext_iff`, i.e. `a.data = b.data`, and each `.data` is `lean_byte_array_data`, which
builds an array from the whole byte string. -/
theorem primBytes_beq (a b : ByteArray) : primBytes .beq (.bytes a) (.bytes b) = a.size + b.size := rfl

/-- `deq` is `beq` on digests: both operands, by the same copies. -/
theorem primBytes_deq (a b : ByteArray) : primBytes .deq (.digest a) (.digest b) = a.size + b.size := rfl

/-- What a payload writer is charged for is what it writes: the size of its result (LANG-87). -/
theorem primBytes_written {p : Prim} {x y : Val} {r : ByteArray}
    (hp : p = .u64be ∨ p = .sized ∨ p = .dsized) (h : primEval p x y = .ok (.bytes r)) :
    primBytes p x y = r.size := by
  rcases hp with rfl | rfl | rfl <;> cases x <;> cases y <;> simp only [primEval, appended] at h <;>
    (try cases h) <;> split at h <;> cases h <;> simp_all [primBytes, primBytes.written]

/-- What `cat` is charged for is what it writes: the size of its result. -/
theorem primBytes_cat {x y : Val} {r : ByteArray} (h : primEval .cat x y = .ok (.bytes r)) :
    primBytes .cat x y = r.size := by
  cases x <;> cases y <;> simp only [primEval] at h <;> try cases h
  rename_i a b
  by_cases hs : a.size + b.size ≤ Bounds.bytesMax
  · simp only [hs, if_true, Except.ok.injEq, Val.bytes.injEq] at h
    subst h; simp [primBytes, hs, ByteArray.size_append]
  · simp [hs] at h

/-- The ticks already paid toward the primitives on a stack: the `paid` of each `primR` frame. -/
private def stackPaid : List Frame → Nat
  | [] => 0
  | .primR _ _ j :: k => j + stackPaid k
  | _ :: k => stackPaid k

private theorem stepBytes_le_paid (lib : List Term) (s : State) :
    stepBytesBy (step lib) s ≤ Bounds.wordBytes * (stackPaid s.stack + 1) := by
  obtain ⟨c, k, d⟩ := s
  cases c with
  | eval t env => simp [stepBytesBy]
  | ret v =>
    cases k with
    | nil => simp [stepBytesBy]
    | cons f k =>
      cases f with
      | primR p a j =>
        simp only [stepBytesBy, stackPaid]
        split
        · exact Nat.zero_le _
        · rename_i hnp
          have hj : ¬ j + 1 < primTicks p a v := fun hj => hnp (by simp [step, primStep, hj, Step.pays])
          have := primBytes_le p a v
          have : Bounds.wordBytes * primTicks p a v ≤ Bounds.wordBytes * (j + stackPaid k + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          omega
      | _ => simp [stepBytesBy]

/-- One transition: the bytes it walks, plus a word for every tick paid toward a primitive after it,
are at most a word for every tick paid before it and one more for itself. -/
private theorem step_paid {lib : List Term} {s s' : State} (h : step lib s = .next s') :
    stepBytesBy (step lib) s + Bounds.wordBytes * stackPaid s'.stack ≤
      Bounds.wordBytes * (stackPaid s.stack + 1) := by
  obtain ⟨c, k, d⟩ := s
  cases c with
  | eval t env =>
    have h0 : stepBytesBy (step lib) ⟨.eval t env, k, d⟩ = 0 := by simp [stepBytesBy]
    rw [h0]
    cases t <;> simp only [step, push] at h <;> (repeat' split at h) <;> (try simp at h) <;>
      (try (cases h; simp [stackPaid, Nat.mul_add] <;> omega))
  | ret v =>
    cases k with
    | nil => simp [step] at h
    | cons f k =>
      cases f with
      | primR p a j =>
        by_cases hj : j + 1 < primTicks p a v
        · have hs : step lib ⟨.ret v, .primR p a j :: k, d⟩ = .next ⟨.ret v, .primR p a (j + 1) :: k, d⟩ := by
            simp [step, primStep, hj]
          rw [hs] at h; cases h
          have h0 : stepBytesBy (step lib) ⟨.ret v, .primR p a j :: k, d⟩ = 0 := by
            simp [stepBytesBy, hs, Step.pays]
          simp only [h0, stackPaid, Nat.mul_add, Nat.mul_one]; omega
        · have hle : stepBytesBy (step lib) ⟨.ret v, .primR p a j :: k, d⟩ ≤ primBytes p a v := by
            simp only [stepBytesBy]; split <;> omega
          have hs := h
          simp only [step, primStep, hj, if_false] at hs
          split at hs
          · cases hs
            have := primBytes_le p a v
            have : Bounds.wordBytes * primTicks p a v ≤ Bounds.wordBytes * (j + 1) :=
              Nat.mul_le_mul_left _ (by omega)
            simp only [stackPaid, Nat.mul_add, Nat.mul_one] at *
            omega
          · cases hs
      | _ =>
        have h0 : ∀ fr, (∀ p a j, fr ≠ Frame.primR p a j) →
            stepBytesBy (step lib) ⟨.ret v, fr :: k, d⟩ = 0 := by
          intro fr hfr; cases fr <;> simp [stepBytesBy] <;> exact absurd rfl (hfr _ _ _)
        rw [h0 _ (by intros; simp)]
        simp only [step] at h <;> (repeat' split at h) <;> (try simp at h) <;>
          (try (cases h; simp [stackPaid, Nat.mul_add] <;> omega))

/-- **A run walks at most one word per tick** (LANG-L, LANG-64): under every budget and stack bound,
the primitive operand bytes a run walks are at most `wordBytes` per tick it reports, plus a word for each tick already
paid toward a primitive on the stack it starts from (none, from `State.init`). -/
theorem walked_le_paid {lib : List Term} {cap : Nat} :
    ∀ (fuel u : Nat) (s : State),
      walked lib cap fuel s + Bounds.wordBytes * u ≤
        Bounds.wordBytes * ((run lib cap fuel u s).used + stackPaid s.stack)
  | 0, u, s => by simp [walked, walkedBy, run, Outcome.used, Nat.mul_add]
  | fuel + 1, u, s => by
    have hb := stepBytes_le_paid lib s
    simp only [walked, walkedBy, run]
    cases hs : step lib s with
    | halt v => simp only [Outcome.used]; (try simp only [Nat.mul_add, Nat.mul_one] at *); omega
    | fault f => simp only [Outcome.used]; (try simp only [Nat.mul_add, Nat.mul_one] at *); omega
    | next s' =>
      simp only
      split
      · simp only [Outcome.used]; (try simp only [Nat.mul_add, Nat.mul_one] at *); omega
      · have h1 := step_paid hs
        have h2 := walked_le_paid (lib := lib) (cap := cap) fuel (u + 1) s'
        simp only [walked, Nat.mul_add, Nat.mul_one] at *
        omega

/-- **From the start, a run walks at most `wordBytes` primitive operand bytes per tick it is
charged.** -/
theorem walked_le {lib : List Term} {cap fuel : Nat} {t : Term} {env : Env} :
    walked lib cap fuel (State.init t env) ≤
      Bounds.wordBytes * (run lib cap fuel 0 (State.init t env)).used := by
  have := walked_le_paid (lib := lib) (cap := cap) fuel 0 (State.init t env)
  simpa [State.init, stackPaid] using this

end Nanodregg.Lang
