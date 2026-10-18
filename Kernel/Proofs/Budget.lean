/-
# Kernel.Proofs.Budget — a reached World's storage plus allowance stays below 2^64 (cv 01a14ba9-cbf4)

`commit` sets `allowance := allowance + credit − charge`, and a retirement credits the retired cell's
whole weight. What bounds the allowance is therefore the SUM `weight + allowance`, never the allowance
alone: `fold_conserves` keeps the sum non-increasing, so a start below 2^64 keeps every reached World
below it, and with it the allowance inside the World codec's `u64`. Genesis and carry check the sum
(`GenesisFits`, `CarryFits`: refused `allowanceTooLarge`), and the World codec's `kernel/world-budget`
refines on it (CODEC's `World.CodecFits`).

* `fold_budget_lt`: a fold keeps `weight + allowance < 2^64` (from `fold_conserves`);
* `genesis_budget`, `carry_budget`: a checked genesis or carry starts below it;
* `genesis_fold_budget_lt`, `carry_fold_budget_lt`: every World a genesis, or a carry of a
  canonical slotted state (what the carried codec reads), reaches is below it;
* `deployed_budget_lt`: at the deployed codec, every World reached from a genesis, or from a carry of
  a World a genesis reached, with no premise.

The tooth is kernel-sim's `carry-budget` arm: the crafted carry (allowance 2^64 − 1 beside a live
cell) is refused `allowanceTooLarge`, while the same carry under the old allowance-only check is
admitted and one light retire turn carries the allowance to 2^64 or past it (`carry-budget-plant`).
-/
import Kernel.Proofs.Weight
import Kernel.Proofs.Carry
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec

variable {D : Type} [Ord D] [DecidableEq D] [Std.TransOrd D] [Std.LawfulEqOrd D]

/-- **A fold keeps the budget below 2^64**: storage plus allowance never grows (`fold_conserves`). -/
theorem fold_budget_lt {E : Env D} {w w' : World D} {l : List (Turn D)} (hc : w.Canon E) (hs : w.Slotted E)
    (hb : w.weight + w.allowance < 2 ^ 64) (h : World.fold E w l = .ok w') :
    w'.weight + w'.allowance < 2 ^ 64 := by
  have := fold_conserves hc hs h
  omega

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A checked genesis starts below 2^64 (`GenesisFits`'s budget clause). -/
theorem genesis_budget {X : Ctx D} {name nonce : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)}
    {g : World D} (hg : genesis X name nonce allowance founders = .ok g) : g.weight + g.allowance < 2 ^ 64 := by
  obtain ⟨hf, rfl⟩ := genesis_ok.mp hg
  exact hf.2.2.2.2

omit [DecidableEq D] [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A checked carry starts below 2^64 (`CarryFits`'s budget clause: the carried cells are the World's). -/
theorem carry_budget {X : Ctx D} {name nonce : ByteArray} {f : D} {c : Carried D} {w : World D}
    (h : carry X name nonce f c = .ok w) : w.weight + w.allowance < 2 ^ 64 := by
  obtain ⟨hf, rfl⟩ := carry_ok.mp h
  exact hf.2.2.1

/-- **Every World a checked genesis reaches is below the budget**, no premise. -/
theorem genesis_fold_budget_lt {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {g w : World D} {l : List (Turn D)}
    (hg : genesis X name nonce allowance founders = .ok g) (hl : World.fold X.env g l = .ok w) :
    w.weight + w.allowance < 2 ^ 64 := by
  have hb := genesis_budget hg
  obtain ⟨_, rfl⟩ := genesis_ok.mp hg
  exact fold_budget_lt (receive_genesis_canon X name nonce allowance founders)
    (receive_genesis_slotted X name nonce allowance founders) hb hl

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A carried World's slots hold the leaves of their kinds when the exported one's did (the trie is the same). -/
theorem carry_slotted {X : Ctx D} {name nonce : ByteArray} {w w' : World D} (hs : w.Slotted X.env)
    (h : carry X name nonce w.origin w.carried = .ok w') : w'.Slotted X.env := by
  obtain ⟨_, rfl⟩ := carry_ok.mp h
  exact hs

/-- **Every World a checked carry reaches is below the budget**, given what the carried codec gives
of the carried trie on import (canonical, every slot holding the leaf of its kind). -/
theorem carry_fold_budget_lt {X : Ctx D} {name nonce : ByteArray} {f : D} {c : Carried D} {w w' : World D}
    {l : List (Turn D)} (h : carry X name nonce f c = .ok w) (hc : w.Canon X.env) (hs : w.Slotted X.env)
    (hl : World.fold X.env w l = .ok w') : w'.weight + w'.allowance < 2 ^ 64 :=
  fold_budget_lt hc hs (carry_budget h) hl

open Nanodregg.Codec.Deployed in
/-- **Deployed: every World reached from a genesis or a carry has storage plus allowance below 2^64**,
so its allowance is inside the World codec's `u64` and every seal of it reads back. The carry is of
a World a genesis reached (`w₀`, the lineage); `host import` of a file reaches the same bound through
the carried codec (`carry_fold_budget_lt`, HOST's `Kept`). No premise. -/
theorem deployed_budget_lt (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w : World Digest} {l : List (Turn Digest)}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w) :
    (w.weight + w.allowance < 2 ^ 64) ∧
      ∀ {name' nonce' : ByteArray} {w₁ w₂ : World Digest} {l' : List (Turn Digest)},
        carry (ctx program) name' nonce' w.origin w.carried = .ok w₁ → World.fold env w₁ l' = .ok w₂ →
          w₂.weight + w₂.allowance < 2 ^ 64 := by
  refine ⟨genesis_fold_budget_lt (X := ctx program) hg hl, fun {_ _ w₁ _ _} hc hl' => ?_⟩
  obtain ⟨_, rfl⟩ := genesis_ok.mp hg
  have hcan : w.Canon (ctx program).env :=
    fold_canon (receive_genesis_canon (ctx program) name nonce allowance founders) hl
  have hsl : w.Slotted (ctx program).env :=
    fold_slotted (receive_genesis_slotted (ctx program) name nonce allowance founders) hl
  exact carry_fold_budget_lt (X := ctx program) hc (carry_canon hcan hc) (carry_slotted hsl hc) hl'

end Nanodregg.Kernel.Receive
