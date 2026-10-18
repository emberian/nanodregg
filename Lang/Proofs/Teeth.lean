/-
# Lang.Proofs.Teeth — named behaviours of the machine on concrete programs

The soundness theorems say a checked run is never stuck; they cannot see a machine that computes
the WRONG value of the right type (swapped `ite` arms, a wrapping `sub`, `lt` as `le`, the wrong
`case` arm, `extend` overriding the wrong way). These theorems pin the behaviours by name, each
proved by the kernel evaluating the run (`decide`), so each such mutation turns one of them red.
-/
import Lang.Eval

namespace Nanodregg.Lang.Teeth

/-- `{fact : nat → nat}` with `fact n = if n == 0 then 1 else n * self.fact (n - 1)`. -/
private def factRow : List (Label × Ty) := [("fact", .fn .nat .nat)]

private def fact : Term :=
  .fix (.lam (.record factRow) (.record [("fact", .lam .nat
     (.ite (.prim .eq (.var 0) (.nat 0)) (.nat 1)
       (.prim .mul (.var 0) (.app (.get (.var 1) "fact") (.prim .sub (.var 0) (.nat 1))))))]))

private def isNat (n : Nat) : Outcome → Bool
  | .value (.nat m) _ => m == n
  | _ => false

private def isBool (b : Bool) : Outcome → Bool
  | .value (.bool c) _ => c == b
  | _ => false

private def isFault (f : Fault) : Outcome → Bool
  | .fault g _ => g == f
  | _ => false

/-- Open recursion through the knot: the final self's `fact`. -/
theorem fact_five : isNat 120 (eval [] 1000 (.app (.get fact "fact") (.nat 5))) = true := by
  decide

/-- Laziness of fields: an unused divergent field of the final self is never forced. -/
theorem lazy_field :
    isNat 7 (eval [] 100 (.get (.fix (.lam (.record [("bad", .nat), ("good", .nat)])
      (.record [("bad", .get (.var 0) "bad"), ("good", .nat 7)]))) "good")) = true := by
  decide

/-- ... and forcing it is a metered divergence, refused by `ticks`. -/
theorem forced_divergence_exhausts :
    isFault .ticks (eval [] 100 (.get (.fix (.lam (.record [("bad", .nat), ("good", .nat)])
      (.record [("bad", .get (.var 0) "bad"), ("good", .nat 7)]))) "bad")) = true := by
  decide

theorem ite_true_arm : isNat 1 (eval [] 10 (.ite (.bool true) (.nat 1) (.nat 2))) = true := by
  decide

theorem sub_underflow_named :
    isFault .underflow (eval [] 10 (.prim .sub (.nat 2) (.nat 3))) = true := by decide

theorem lt_strict : isBool false (eval [] 10 (.prim .lt (.nat 3) (.nat 3))) = true := by decide

theorem add_overflow_named :
    isFault .overflow (eval [] 10 (.prim .add (.nat 18446744073709551615) (.nat 1))) = true := by
  decide

theorem div_zero_named : isFault .divZero (eval [] 10 (.prim .div (.nat 1) (.nat 0))) = true := by
  decide

/-- `case` takes the arm of the injected label and binds its payload. -/
theorem case_selects_arm :
    isNat 9 (eval [] 20 (.case (.inj (.sum [("a", .nat), ("b", .nat)]) "b" (.nat 9))
      [("a", .nat 0), ("b", .var 0)])) = true := by
  decide

/-- `extend` overrides: the new field wins. -/
theorem extend_overrides :
    isNat 2 (eval [] 20 (.get (.extend (.record [("x", .nat 1)]) [("x", .nat 2)]) "x")) = true := by
  decide

/-- The known cost of call-by-name fields (DECISIONS LANG-2, ROOT's ruling): a chain where each
field reads the one below twice does exponential work and is refused by the tick bound, by name,
where the same chain under call-by-need would be linear. Measured: fields `a`…`f` need 9, 23, 51,
107, 219, 443 ticks (each about twice the last); `f` does not fit 200, `d` does. -/
private def names : List Label := ["a", "b", "c", "d", "e", "f"]

/-- Field `i` adds field `i - 1` to itself; field 0 is `1`. -/
private def chainFields : List (Label × Term) :=
  ("a", .nat 1) :: (names.zip names.tail).map fun p =>
    (p.2, .prim .add (.get (.var 0) p.1) (.get (.var 0) p.1))

theorem exponential_chain_exhausts :
    isFault .ticks (eval [] 200 (.get (.fix (.lam (.record (names.map fun n => (n, .nat)))
      (.record chainFields))) "f")) = true := by
  decide

/-- The same chain, short enough to fit: the value is `2^k`, so the bound is the only refusal. -/
theorem short_chain_fits :
    isNat 8 (eval [] 200 (.get (.fix (.lam (.record (names.map fun n => (n, .nat)))
      (.record chainFields))) "d")) = true := by
  decide

/-! ### LANG-51: `refuse` and `len<=` -/

/-- The bytes of `late`. -/
private def late : ByteArray := ⟨#[108, 97, 116, 101]⟩

/-- `refuse` ends the run with exactly the name it wrote, in one step. -/
theorem refuse_named : isFault (.refused late) (eval [] 10 (.refuse .nat late)) = true := by decide

/-- ... in ONE step: under a budget of one tick it is already refused, not out of ticks. -/
theorem refuse_one_step : isFault (.refused late) (eval [] 1 (.refuse .nat late)) = true := by decide

/-- A `refuse` in a field that is never selected never fires (fields are suspended). -/
theorem refuse_lazy_field :
    isNat 7 (eval [] 20 (.get (.record [("bad", .refuse .nat late), ("good", .nat 7)]) "good")) = true := by
  decide

/-- A `refuse` in the arm not taken never fires; in the arm taken, it does. -/
theorem refuse_untaken_arm : isNat 1 (eval [] 20 (.ite (.bool true) (.nat 1) (.refuse .nat late))) = true := by
  decide

theorem refuse_taken_arm :
    isFault (.refused late) (eval [] 20 (.ite (.bool false) (.nat 1) (.refuse .nat late))) = true := by
  decide

/-- Left operand first: a refusal on the left wins over an arithmetic fault on the right. -/
theorem refuse_left_first :
    isFault (.refused late) (eval [] 20 (.prim .add (.refuse .nat late) (.prim .div (.nat 1) (.nat 0)))) = true := by
  decide

/-- `len<=` at the bound is true, one past it false, and it reads the SIZE (not the content). -/
theorem lenLe_at_bound : isBool true (eval [] 10 (.prim .lenLe (.bytes late) (.nat 4))) = true := by decide

theorem lenLe_past_bound : isBool false (eval [] 10 (.prim .lenLe (.bytes late) (.nat 3))) = true := by decide

/-- Four zero bytes against 4: the size counts, not the content. -/
theorem lenLe_size_not_content : isBool true (eval [] 10 (.prim .lenLe (.bytes ⟨#[0, 0, 0, 0]⟩) (.nat 4))) = true := by
  decide

theorem lenLe_empty_zero : isBool true (eval [] 10 (.prim .lenLe (.bytes .empty) (.nat 0))) = true := by decide

end Nanodregg.Lang.Teeth
