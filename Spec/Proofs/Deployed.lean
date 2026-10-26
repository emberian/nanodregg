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
`fold_package_fixed`, `object_history_chain` at the deployed program (`deployed_ctx_lawful`). -/
theorem top_integrity_law (d : ByteArray → ByteArray) : Integrity.law (deployed d) := by
  intro obj law p fs ℓ t hb hℓ hfind hlaw hnr w w' l ha hcan cell hl hk
  rw [audited_deployed] at ha
  obtain ⟨tr, htr⟩ := object_history_of_honest ha.1 ha.2 hcan hl hk
  obtain ⟨cell', hl', -, -, hpk⟩ := fold_package_fixed ha.1 ha.2 hl hk
  exact ⟨tr, htr, ⟨cell', hl', hpk⟩, fun hin o ho =>
    object_history_chain (deployed_ctx_lawful _) rfl hb hℓ hfind hlaw hnr htr hin hl ho⟩

/-- **C(ii) of the deployed system, submit-class**: `step_settled_ok`, `settle_committed`. -/
theorem top_consent_okCommitted (d : ByteArray → ByteArray) : Consent.okCommitted (deployed d) := by
  intro me f f' kb res o e p argv acc hst h
  obtain ⟨cb, c, hh, td, hl, hd, hs⟩ := Command.step_settled_ok hst h
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

/-- **G2 of the deployed system**: both of `handle`'s `defer` arms sit under `Envelope.check`. -/
theorem top_shown (d : ByteArray → ByteArray) : Shown.onlyFollowers (deployed d) := by
  intro w f dd h
  change Host.handle Host.Deployed.X w f = .defer dd at h
  unfold Host.handle at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | exact ⟨_, ‹_›, ‹_›⟩
    | (simp at h)

end Nanodregg.Spec
