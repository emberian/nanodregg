/-
# Spec.Proofs.Deployed — the claims, of the deployed system

`theorem top_* : Claim (deployed d)` for each claim of `Spec.Proofs.Claims` whose proof is a
composition of lemmas the tree already proves. The proofs are untrusted; what is trusted is the
statement in `Claims` and its floor in `Floor`.
-/
import Spec.Proofs.Bridge
import Kernel.Proofs.Value
import Kernel.Proofs.ObjectHead
import Kernel.Proofs.RootedDeployed
import Codec.Proofs.Digest
import Protocol.Proofs.Settle
import Protocol.Proofs.Command
import Protocol.Proofs.Behind
import Protocol.Proofs.Envelope

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-- **B2 of the deployed system**: `fold_value`, `fold_floors`. -/
theorem top_integrity_value (d : ByteArray → ByteArray) : Integrity.value (deployed d) := by
  intro w w' l hc hf dd
  rw [fold_eq_world _ rfl rfl] at hf
  exact ⟨fold_value dd hc hf, fun hd => fold_floors hc hf hd⟩

/-- **A2 of the deployed system**: `fold_reaches_host` at the deployed `Env` (`deployed_lawful`). -/
theorem top_oneHistory_pair (d : ByteArray → ByteArray) : OneHistory.pair (deployed d) := by
  intro g wf wg lf lg hf hg hs hc
  rw [fold_eq_world _ rfl rfl] at hf hg
  exact fold_reaches_host deployed_lawful hg hf hs hc

/-- **B3 of the deployed system, for `NoRef` laws**: `object_history_of_honest`,
`fold_package_fixed`, `object_history_chain` (stated for every history) at the deployed program
(`deployed_ctx_lawful`). -/
theorem top_integrity_law (d : ByteArray → ByteArray) : Integrity.law (deployed d) := by
  intro obj law p fs ℓ t hb hℓ hfind hlaw hnr w w' l ha hcan cell hl hk
  rw [audited_deployed] at ha
  obtain ⟨tr, htr⟩ := object_history_of_honest ha.1 ha.2 hcan hl hk
  refine ⟨⟨tr, htr⟩, ?_, fun tr' htr' hin _ ho =>
    object_history_chain (deployed_ctx_lawful _) rfl hb hℓ hfind hlaw hnr htr' hin hl ho⟩
  rcases fold_package_fixed ha.1 ha.2 hl hk with ⟨cell', hl', -, -, hpk⟩ | ht
  · exact .inl ⟨cell', hl', hpk⟩
  · exact .inr ht

/-- A step on a settle-phase (4) continuation keeps follow's state: every arm it can reach is `same`. -/
theorem step_phase4_keeps {D : Type} [Ord D] [DecidableEq D] {X : Ctx D} {dc : Codec.Stream D}
    {B : Thin.Base (World D)} {me : Command.Self D} {f f' : Command.Follow D} {p : Command.Persist D}
    {kb result : ByteArray} {r : Command.Reply} {argv acc : List ByteArray}
    (hst : Command.State.ofBytes kb = some ⟨argv, 4, acc⟩)
    (h : Command.step X dc B me f kb result = (f', p, r)) : f' = f := by
  unfold Command.step at h
  simp only [hst, Option.map_some, Option.getD_some] at h
  split at h
  · rename_i hs; cases hs
  · simp only [Prod.mk.injEq] at h; exact h.1.symm
  · rename_i st cmd hs _
    simp only [Option.some.injEq] at hs
    subst hs
    have h4 : ∀ b, Command.stepResult (D := D) b 4 result = .ok result := by intro b; cases b <;> rfl
    simp only [h4] at h
    split at h
    all_goals first
      | (simp only [Prod.mk.injEq] at h; exact h.1.symm)
      | (exfalso; revert ‹(4 : UInt8) = _›; decide)

/-- **C(ii) of the deployed system, submit-class**: `step_settled_ok`, `settle_committed`; the
settle phase keeps follow's World (`step_phase4_keeps`). -/
theorem top_consent_okCommitted (d : ByteArray → ByteArray) : Consent.okCommitted (deployed d) := by
  intro me f f' kb res o e p argv acc hst h
  obtain ⟨cb, c, hh, td, hl, hd, hs⟩ := Command.step_settled_ok hst h
  obtain rfl := step_phase4_keeps hst h
  exact ⟨cb, c, hh, td, hl, hd, Settle.settle_committed hs⟩

/-- **C(iii) of the deployed system**: a settlement other than `refused stale` is the receipt's
verdict with no staleness read, which `settle_final_never_admits` makes final. -/
theorem top_consent_final (d : ByteArray → ByteArray) : Consent.final (deployed d) := by
  intro me w w' c l hrc hjc hv hf out
  rw [fold_eq_world _ rfl rfl] at hf
  refine Settle.settle_final_never_admits hrc hjc ?_ hf out
  change Settle.ofReceipt _ (Command.staleBehind (deployed d).X me w c) _ _
      (Receipt.build (deployed d).X.env w (txIdOf (deployed d).X c)).answer = _ ∨
    ∃ code, code ≠ staleCode ∧ Settle.ofReceipt _ (Command.staleBehind (deployed d).X me w c) _ _
      (Receipt.build (deployed d).X.env w (txIdOf (deployed d).X c)).answer = _ at hv
  generalize Command.staleBehind (deployed d).X me w c = b at hv
  generalize (Receipt.build (deployed d).X.env w (txIdOf (deployed d).X c)).answer = a at hv ⊢
  cases a <;> simp only [Settle.ofReceipt] at hv ⊢ <;> (repeat' split at hv) <;> (repeat' split) <;>
    simp_all

/-- **G2 of the deployed system**: both of `handle`'s `defer` arms sit under `Envelope.check`, whose
acceptance is the live grant chain, the current key and the verifying signature (`Envelope.check_ok_iff`). -/
theorem top_shown (d : ByteArray → ByteArray) : Shown.onlyFollowers (deployed d) := by
  intro w f dd h
  suffices hs : ∃ e, Envelope.ofBytes Host.Deployed.X f.payload = some e ∧
      Envelope.check Host.Deployed.X w e = .ok () by
    obtain ⟨e, he, hc⟩ := hs
    obtain ⟨-, -, hk, hv, hm, -, -⟩ := (Envelope.check_ok_iff Host.Deployed.X w e).mp hc
    exact ⟨e, he, hc, hm, hk, hv⟩
  change Host.handle Host.Deployed.X w f = .defer dd at h
  unfold Host.handle at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | exact ⟨_, ‹_›, ‹_›⟩
    | (simp at h)

/-- The cancel's code is not `stale`'s: a settlement `refused cancelled` is never follow's own
staleness read. -/
theorem cancelledCode_ne_stale {D : Type} : (Command.cancelledCode (D := D)) ≠ staleCode := by
  have h : Command.cancelledCode (D := D) = Command.cancelledCode (D := Nat) := rfl
  rw [h]
  decide

/-- **A settlement `refused cancelled` is the World's record**: no journal entry for the call, and a
recorded refusal of it with the cancel's code (`build_answer`; the absent arm says `refused` only
by `staleCode`). -/
theorem settleOf_cancelled_record {D : Type} [Ord D] [DecidableEq D] {X : Ctx D}
    {me : Command.Self D} {w : World D} {c : Call D}
    (h : Command.settleOf X me w c = .refused (Command.cancelledCode (D := D))) :
    w.journalAt X.env (txIdOf X c) = none ∧
      ∃ hh m, w.refusalAt X.env (.tx (txIdOf X c)) = some (.refused hh (Command.cancelledCode (D := D)) m) := by
  unfold Command.settleOf at h
  rw [Settle.build_answer] at h
  cases hj : w.journalAt X.env (txIdOf X c) with
  | some x =>
    obtain ⟨hh, td⟩ := x
    rw [hj] at h; simp [Settle.ofReceipt] at h
  | none =>
    rw [hj] at h
    refine ⟨rfl, ?_⟩
    cases hr : w.refusalAt X.env (.tx (txIdOf X c)) with
    | some leaf =>
      rw [hr] at h
      cases leaf with
      | refused hh code m =>
        dsimp only at h
        simp only [Settle.ofReceipt] at h
        split at h
        · cases h; exact ⟨hh, m, rfl⟩
        · cases h
      | head _ _ =>
        dsimp only at h
        simp only [Settle.ofReceipt] at h
        repeat' split at h
        all_goals first | cases h | (injection h with h; exact absurd h.symm cancelledCode_ne_stale)
      | count n =>
        dsimp only at h
        simp only [Settle.ofReceipt] at h
        repeat' split at h
        all_goals first | cases h | (injection h with h; exact absurd h.symm cancelledCode_ne_stale)
    | none =>
      rw [hr] at h
      dsimp only at h
      simp only [Settle.ofReceipt] at h
      repeat' split at h
      all_goals first | cases h | (injection h with h; exact absurd h.symm cancelledCode_ne_stale)

/-- **C(ii), cancel, of the deployed system**: `cancel_ok_settled` (PROTOCOL-71), and the settlement
read back as the World's record (`settleOf_cancelled_record`). -/
theorem top_consent_cancelOk (d : ByteArray → ByteArray) : Consent.cancelOk (deployed d) := by
  intro me f f' kb res o e p st cb hst hcmd h
  obtain ⟨c, hd, hs⟩ := Command.cancel_ok_settled hst hcmd h
  obtain ⟨hj, hh, m, hr⟩ := settleOf_cancelled_record hs
  exact ⟨c, hd, hs, hj, hh, m, hr⟩

/-- **C(iii), stale, of the deployed system**: a `refused stale` settlement is either the receipt's
recorded refusal (final by `settle_final_never_admits`) or follow's own `staleBehind`
(`staleBehind_final`, at the deployed `Env`). -/
theorem top_consent_staleFinal (d : ByteArray → ByteArray) : Consent.staleFinal (deployed d) := by
  intro me w₀ w w' l₁ l₂ key cmd rs b u c hfit hrc hok hrs hplan hcu hrfc hjc h₁ h₂ hv
  rw [fold_eq_world _ rfl rfl] at h₁ h₂
  change Settle.ofReceipt (journalForgets w.height c.unsigned.notBefore)
    (Command.staleBehind Host.Deployed.X me w c) w.height c.unsigned.validUntil
    (Receipt.build Host.Deployed.X.env w (txIdOf Host.Deployed.X c)).answer = .refused staleCode at hv
  cases hb : Command.staleBehind Host.Deployed.X me w c with
  | true => exact Command.staleBehind_final deployed_lawful hfit hrc hok hrs hplan hcu h₁ h₂ hb
  | false =>
    rw [hb] at hv
    exact .inl fun out => Settle.settle_final_never_admits hrfc hjc (.inr ⟨_, hv⟩) h₂ out

end Nanodregg.Spec
