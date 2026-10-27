/-
# Spec.Proofs.Escrow — B2's one-party escrow: it pays out at most once

**`Integrity.escrow S`** (over the field `S.escrow`) (TOPLEVEL-SPEC §3.2): along any `ObjectHistory` of one object at the
system's `Ctx` (every step of the World as the object sees it: its signed and nested invokes, writes,
law changes, every other turn and recorded refusal) whose every judged step reads the object's
package as `E`, at most one call the invokes return is a payout (a transfer with no grant,
`isPayoutCall`). `E` is the component the claim varies: LEDGER's escrow (`Ledger.Escrow.escrow`,
`world/escrow/Escrow`) at `deployed`. Owed: a `System` field `escrow : Lang.Package` (deployed
`Ledger.Escrow.escrow`); the claim then reads `S.escrow`.

Premises, each needed: the `Ctx` is lawful (digests read back) and its program is the language over
its own codec and receipt check (`S.rc`); both hold of `deployed` (`deployed_ctx_lawful`, `rfl`).
The history and the package reading are the claim's subject, not assumptions.

* `top_integrity_escrow`: `Ledger.Proofs.escrow_invokes_one_payout`.
* `floor_integrity_escrow`: the claim refuses `esLazy` (no law on its invokes, and its refund spending
  `"refund"` rather than the shared `"payout"`): at the deployed `Ctx`, from the World a founder's
  install, issue, create, deposit and top-up stage, a release and then a refund are each derived and
  admitted, and the two-step history pays out twice. Either guard alone holds the bound (measured on
  the same run: the law alone refuses the refund `lawDenied`, the shared key alone `spent`), so the
  lazy escrow must drop both: the claim is about the package, and the kernel's once nullifier is the
  package's second line, not the kernel's own promise.
* `inhabited_escrow`: under the deployed escrow the same run's release is an admitted invoke step
  whose history pays out once: the bound is reached.

The history is built step by step from the computed run (`esStep_sound`: an `EsStep` whose Boolean
facts hold IS an `ObjectStep.invoke`), so the run's history is not an existential: its entries, and
the calls `payoutCalls` counts, are the run's.
-/
import Spec.Sim.Escrow
import Ledger.Proofs.EscrowInvokes
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec
open Nanodregg.Lang
open Nanodregg.Ledger.Escrow

/-! ## The claim -/

section
variable {D : Type} [Ord D] [DecidableEq D]

/-- **B2, one-party escrow. It pays out at most once.** At a lawful `Ctx` running the language over
its own codec and the system's receipt check, along any history of one object whose every judged step
reads its package as `S.escrow`, at most one returned call is a payout. -/
def Integrity.escrow (S : System D) : Prop :=
  S.X.Lawful → S.X.program = Lang.program S.X.env.bytes S.X.digestOf S.rc →
    ∀ {obj pkg : D} {w w' : World D}
      {tr : List (Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D))},
      ObjectHistory S.X obj w w' tr → (∀ e ∈ tr, e.2.1 = some pkg ∧ readPackage e.1 pkg = .ok S.escrow) →
      payoutCalls (tr.map fun e => e.2.2.2.2.2.2) ≤ 1

end

/-! ## The top theorem -/

/-- **TOP (B2, one-party escrow).** The deployed system with LEDGER's escrow
(`Ledger.Proofs.escrow_invokes_one_payout`). -/
theorem top_integrity_escrow (d : ByteArray → ByteArray) : Integrity.escrow (deployed d) := by
  intro hX hprog obj pkg w w' tr h hpkg
  exact Ledger.Proofs.escrow_invokes_one_payout hX hprog h hpkg

/-! ## A computed step is an object step -/

theorem esOk_eq {ε α : Type} {e : Except ε α} (d : α) (h : esOk e = true) : e = .ok (esGet e d) := by
  cases e with
  | ok a => rfl
  | error _ => cases h

/-- **A computed invoke step whose facts hold is an `ObjectStep.invoke`** of the run's object, from
the World it was signed on to the World its Turn leaves, with its entry `esEntry`, which names the
run's package and reads it as `P`. -/
theorem esStep_sound {P : Package} {r : EsRun} {w : World Digest} {i method : Nat}
    (h : esStepOk P r method (esStep r w i method) = true) :
    ObjectStep Xd r.obj w (esStep r w i method).w' (some (esEntry (esStep r w i method))) ∧
    (esEntry (esStep r w i method)).2.1 = some r.pkg ∧
    readPackage (esEntry (esStep r w i method)).1 r.pkg = .ok P := by
  generalize hs : esStep r w i method = s at h ⊢
  have hw : s.w = w := by rw [← hs]; rfl
  have ht : s.t = esGet (receive Xd s.w s.c) tMint := by rw [← hs]; rfl
  have hw' : s.w' = esGet (World.admit Xd.env s.w s.t) s.w := by rw [← hs]; rfl
  have hir : s.ir = esGet (invokeRun Xd (pinned Xd.env s.w s.c.unsigned.pins) s.c s.c.unsigned.member none r.obj method none)
      (mintCell, r.pkg, reqOf s.c.unsigned r.obj r.obj .birth none) := by rw [← hs]; rfl
  have hrun : s.run = esGet (Xd.program.run (pinned Xd.env s.w s.c.unsigned.pins) (rowView Xd.env s.w s.c.unsigned) s.ir.2.1
      (stateOf s.ir.1) method (noArgs.getD .empty) s.ir.2.2 (min 100000 (poolOf s.c.unsigned.body))) ([], [], [], 0) := by
    rw [← hs]; rfl
  have hl : s.laws = esGet (lawsOf Xd r.obj s.ir.1) [] := by rw [← hs]; rfl
  clear hs
  subst hw
  unfold esStepOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc, ha⟩, hb⟩, hi⟩, hr⟩, hlw⟩, hp⟩, hpk⟩, hpk'⟩ := h
  have hc' : receive Xd s.w s.c = .ok s.t := by rw [ht]; exact esOk_eq tMint hc
  have ha' : World.admit Xd.env s.w s.t = .ok s.w' := by rw [hw']; exact esOk_eq s.w ha
  have hi' : invokeRun Xd (pinned Xd.env s.w s.c.unsigned.pins) s.c s.c.unsigned.member none r.obj method none =
      .ok (s.ir.1, s.ir.2.1, s.ir.2.2) := by rw [hir]; exact esOk_eq _ hi
  have hr' : Xd.program.run (pinned Xd.env s.w s.c.unsigned.pins) (rowView Xd.env s.w s.c.unsigned) s.ir.2.1
      (stateOf s.ir.1) method (noArgs.getD .empty) s.ir.2.2 (min 100000 (poolOf s.c.unsigned.body)) =
      .ok (s.run.1, s.run.2.1, s.run.2.2.1, s.run.2.2.2) := by rw [hrun]; exact esOk_eq _ hr
  have hl' : lawsOf Xd r.obj s.ir.1 = .ok s.laws := by rw [hl]; exact esOk_eq _ hlw
  refine ⟨?_, ?_, ?_⟩
  · have hst : ObjectStep Xd r.obj s.w s.w' (some (pinned Xd.env s.w s.c.unsigned.pins, some s.ir.2.1, s.laws, s.ir.2.2,
        stateOf s.ir.1, s.run.1, s.run.2.1)) := .invoke hc' ha' (of_decide_eq_true hb) hi' hr' hl'
    exact hst
  · show some s.ir.2.1 = some r.pkg
    rw [of_decide_eq_true hp]
  · show readPackage (pinned Xd.env s.w s.c.unsigned.pins) r.pkg = .ok P
    rw [esOk_eq default hpk, of_decide_eq_true hpk']

section
variable {D : Type} [Ord D] [DecidableEq D]

/-- One and two judged steps, as histories (the entries explicit). -/
theorem hist_one {X : Ctx D} {obj : D} {w w' : World D}
    {e : Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D)}
    (h : ObjectStep X obj w w' (some e)) : ObjectHistory X obj w w' [e] :=
  ObjectHistory.cons h (.nil _)

theorem hist_two {X : Ctx D} {obj : D} {w w₁ w₂ : World D}
    {e₁ e₂ : Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D)}
    (h₁ : ObjectStep X obj w w₁ (some e₁)) (h₂ : ObjectStep X obj w₁ w₂ (some e₂)) :
    ObjectHistory X obj w w₂ [e₁, e₂] :=
  ObjectHistory.cons h₁ (ObjectHistory.cons h₂ (.nil _))

end

/-! ## The floor: the escrow with neither guard -/

/-- **The lazy run**: under the lazy escrow, the release on the World the setup stages and the refund
on the World the release leaves are each an admitted invoke of the escrow object reading the lazy
package, and between them they return two payouts. -/
theorem run_lazy_escrow :
    (esStepOk esLazy esUnfair release (esStep esUnfair esUnfair.world 10 release) &&
      esStepOk esLazy esUnfair refund (esStep esUnfair (esStep esUnfair esUnfair.world 10 release).w' 11 refund) &&
      decide (payoutCalls [(esEntry (esStep esUnfair esUnfair.world 10 release)).2.2.2.2.2.2,
        (esEntry (esStep esUnfair (esStep esUnfair esUnfair.world 10 release).w' 11 refund)).2.2.2.2.2.2] = 2)) = true := by
  native_decide

/-- **FLOOR (B2, one-party escrow).** The claim refuses the escrow with no law on its invokes and two
once keys: at the deployed system, a release and then a refund of one escrow object, each derived
and admitted, are a history that pays out twice. -/
theorem floor_integrity_escrow (d : ByteArray → ByteArray) : ¬ Integrity.escrow { deployed d with escrow := esLazy } := by
  intro h
  have hr := run_lazy_escrow
  rw [Bool.and_eq_true, Bool.and_eq_true] at hr
  obtain ⟨⟨h1, h2⟩, h3⟩ := hr
  obtain ⟨st1, hp1, hk1⟩ := esStep_sound h1
  obtain ⟨st2, hp2, hk2⟩ := esStep_sound h2
  have hpay := of_decide_eq_true h3
  revert st1 hp1 hk1 st2 hp2 hk2 hpay
  generalize esStep esUnfair (esStep esUnfair esUnfair.world 10 release).w' 11 refund = s2
  generalize esStep esUnfair esUnfair.world 10 release = s1
  generalize esUnfair.world = w
  generalize esUnfair.obj = obj
  generalize esUnfair.pkg = pkg
  intro st1 hp1 hk1 st2 hp2 hk2 hpay
  have hb := h (deployed_ctx_lawful _) rfl (hist_two st1 st2)
    (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨hp1, hk1⟩
      · exact ⟨hp2, hk2⟩)
  rw [List.map_cons, List.map_cons, List.map_nil] at hb
  rw [hpay] at hb
  exact absurd hb (by decide)

/-! ## Inhabited: the deployed escrow pays out once -/

theorem run_fair_escrow :
    (esStepOk escrow esFair release (esStep esFair esFair.world 10 release) &&
      decide (payoutCalls [(esEntry (esStep esFair esFair.world 10 release)).2.2.2.2.2.2] = 1)) = true := by
  native_decide

/-- **INHABITED (B2, one-party escrow).** At the deployed `Ctx`, a history of one escrow object
(its release, derived and admitted on the World a founder's deposit and top-up stage) whose every
judged step reads the package as LEDGER's escrow pays out exactly once: the claim's bound is reached
by a deployed run. -/
theorem inhabited_escrow :
    ∃ (obj pkg : Digest) (w w' : World Digest)
      (tr : List (Pinned Digest × Option Digest × List Digest × Req Digest × Slots × Slots × List (Body Digest))),
      ObjectHistory Xd obj w w' tr ∧ (∀ e ∈ tr, e.2.1 = some pkg ∧ readPackage e.1 pkg = .ok escrow) ∧
      payoutCalls (tr.map fun e => e.2.2.2.2.2.2) = 1 := by
  have hr := run_fair_escrow
  rw [Bool.and_eq_true] at hr
  obtain ⟨h1, h3⟩ := hr
  obtain ⟨st1, hp1, hk1⟩ := esStep_sound h1
  have hpay := of_decide_eq_true h3
  revert st1 hp1 hk1 hpay
  generalize esStep esFair esFair.world 10 release = s1
  generalize esFair.world = w
  generalize esFair.obj = obj
  generalize esFair.pkg = pkg
  intro st1 hp1 hk1 hpay
  refine ⟨obj, pkg, w, _, _, hist_one st1, fun e he => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    exact ⟨hp1, hk1⟩
  · rw [List.map_cons, List.map_nil]
    exact hpay

end Nanodregg.Spec
