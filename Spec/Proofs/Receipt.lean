/-
# Spec.Proofs.Receipt — §7, the receipt clause: the writer cannot misstate a call in a receipt

**The claim** (`ReceiptTruth`): on every World the system's kernel folds from a genesis World, a
receipt the system's receipt check (`S.receiptCheck`; deployed: `Protocol.Receipt.check`) answers
against that World's own head (its height and roots) tells the truth about that World: `committed h td`
is the journal's entry at the id, `refused h code m` is the World's recorded refusal, and `absent`
is neither a journal entry nor a recorded refusal; each up to a collision among a list fixed by the
receipt and the World. So whoever relays the receipt (the writer included) cannot turn a committed
call into `absent` or `refused`, nor move its entry.

**Premises.** Only the fold from a genesis World: it supplies the trie invariants the lemmas need
(`JournalCanon`, journal heights fitting a u64, `RefusalsOk`), so none is a parameter. The head is
the member's OWN World's: a receipt checked against a head another World holds is §9 (`Foreign`).

Top: `top_receiptTruth` (`check_committed`, `check_refused_sound`, `check_absent`,
`check_absent_unrefused`; `Protocol/Proofs/Receipt.lean`). Floor: `floor_receiptTruth` refuses
`receiptBeliever` (the check that believes the receipt's stated answer). Inhabited:
`inhabited_receiptTruth` (the deployed check answers `committed` for the run's call on the World
the run reaches).
-/
import Spec.Proofs.Floor
import Spec.Sim.Receipt
import Protocol.Proofs.Receipt
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

variable {D : Type} [Ord D] [DecidableEq D]

/-- **§7, receipts. A receipt checked against a folded World's own head tells the truth about it.** -/
def ReceiptTruth (S : System D) : Prop :=
  ∀ {name nonce : ByteArray} {a : Nat} {fs : List (ByteArray × D)} {auth : Authority}
    {l : List (Step D)} {w : World D},
    S.fold (genesisWorld S.X name nonce a fs auth) l = .ok w →
    ∀ {txId : D} {nb : Nat} {r : Receipt.Receipt D},
      (∀ {h : Nat} {td : D}, S.receiptCheck w.height (w.roots S.X.env) txId nb r = .ok (.committed h td) →
        w.journalAt S.X.env txId = some (h, td) ∨
          CollidesAmong S.X.env.hash ([rootsPre S.X.env r.root r.jroot r.rroot r.rowsroot, w.rootsPre S.X.env] ++
            inclPres (journalSpec S.X.env) (journalPre S.X.env) txId (h, td) r.jpath w.journal)) ∧
      (∀ {h code : Nat} {m : D}, S.receiptCheck w.height (w.roots S.X.env) txId nb r = .ok (.refused h code m) →
        w.refusalAt S.X.env (.tx txId) = some (.refused h code m) ∨
          CollidesAmong S.X.env.hash ([rootsPre S.X.env r.root r.jroot r.rroot r.rowsroot, w.rootsPre S.X.env] ++
            inclPres (refusalSpec S.X.env) (refusalPre S.X.env) (.refusal (.tx txId)) (.refused h code m) r.rpath
              w.refusals)) ∧
      (S.receiptCheck w.height (w.roots S.X.env) txId nb r = .ok .absent →
        (w.journalAt S.X.env txId = none ∨
          CollidesAmong S.X.env.hash ([rootsPre S.X.env r.root r.jroot r.rroot r.rowsroot, w.rootsPre S.X.env] ++
            readPres (journalSpec S.X.env) txId r.jpath w.journal)) ∧
        (w.refusalAt S.X.env (.tx txId) = none ∨
          CollidesAmong S.X.env.hash ([rootsPre S.X.env r.root r.jroot r.rroot r.rowsroot, w.rootsPre S.X.env] ++
            readPres (refusalSpec S.X.env) (.refusal (.tx txId)) r.rpath w.refusals)))

/-- **§7, receipts, of the deployed system.** -/
theorem top_receiptTruth (d : ByteArray → ByteArray) : ReceiptTruth (deployed d) := by
  intro name nonce a fs auth l w hA txId nb r
  rw [fold_eq_world _ rfl rfl] at hA
  have hjo := fold_journalOk (genesisWorld_journalOk Host.Deployed.X name nonce a fs auth) hA
  have hfit := Receipt.reached_journal_fits hA
  have h0 : (genesisWorld Host.Deployed.X name nonce a fs auth).RefusalsOk Host.Deployed.X.env :=
    refusalsOk_of_empty (by simp [genesisWorld, World.genesis])
  have hro := fold_refusalsOk h0 hA
  refine ⟨fun hk => Receipt.check_committed deployed_lawful (by decide) hjo.1 hfit hk,
    fun hk => Receipt.check_refused_sound deployed_lawful hro hk, fun hk => ⟨?_, ?_⟩⟩
  · exact (Receipt.check_absent deployed_lawful (by decide) hjo.1 hk).2
  · exact Receipt.check_absent_unrefused deployed_lawful hro hk

/-- No two of the floor's listed inputs collide: the forged receipt's roots, the genesis World's,
and the journal path's inclusion inputs for the stated entry. -/
theorem receipt_forged_free :
    collisionFree Xd.env.hash
      ([rootsPre Xd.env receiptForged.root receiptForged.jroot receiptForged.rroot receiptForged.rowsroot,
        wGenesis.rootsPre Xd.env] ++
        inclPres (journalSpec Xd.env) (journalPre Xd.env) wTx (1, oneDigest) receiptForged.jpath wGenesis.journal) =
      true := by
  native_decide

/-- The believing check believes a receipt at the head's own roots, whatever it states. -/
theorem receiptBelieve_stating (H nb : Nat) (w : World Digest) (t : Digest) (a : Receipt.Answer Digest) :
    receiptBelieve H (w.roots Xd.env) t nb (receiptStating w t a) = .ok a := by
  simp [receiptBelieve, receiptStating, World.roots_eq]

theorem receiptBeliever_check (d : ByteArray → ByteArray) : (receiptBeliever d).receiptCheck = receiptBelieve := rfl

theorem deployed_receiptCheck (d : ByteArray → ByteArray) :
    (deployed d).receiptCheck = Receipt.check Host.Deployed.X.env := rfl

/-- **FLOOR (§7, receipts).** The claim refuses the check that believes the receipt: at the genesis
World (empty log), a receipt at its roots stating the run's call committed is believed, though the
genesis World journals nothing and the listed inputs are collision-free. -/
theorem floor_receiptTruth (d : ByteArray → ByteArray) : ¬ ReceiptTruth (receiptBeliever d) := by
  intro h
  have hk : (receiptBeliever d).receiptCheck wGenesis.height (wGenesis.roots Xd.env) wTx 0 receiptForged =
      .ok (.committed 1 oneDigest) := by
    rw [receiptBeliever_check]
    exact receiptBelieve_stating _ _ wGenesis wTx _
  have hc := receipt_forged_free
  rcases (h (name := "spec".toUTF8) (nonce := "spec-0".toUTF8) (a := 100000000)
      (fs := [(wKey, nextKeyDigest Xd wNext)]) (auth := Authority.none) (l := []) (w := wGenesis) rfl).1
      (h := 1) (td := oneDigest) hk
    with hj | col
  · have hj' : wGenesis.journalAt Xd.env wTx = some (1, oneDigest) := hj
    rw [wGenesis, Foreign.genesisWorld_journalAt] at hj'
    cases hj'
  · exact not_collides hc col

theorem receiptOkThen_eq {ε : Type} {r : Except ε (World Digest)} {k : World Digest → Bool}
    (h : receiptOkThen r k = true) : ∃ w, r = .ok w ∧ k w = true := by
  cases r with
  | ok w => exact ⟨w, rfl, h⟩
  | error e => cases h

theorem receiptCommittedB_eq {a : Except Receipt.Refusal (Receipt.Answer Digest)}
    (h : receiptCommittedB a = true) : ∃ hh td, a = .ok (.committed hh td) := by
  unfold receiptCommittedB at h
  split at h
  · exact ⟨_, _, rfl⟩
  · cases h

/-- **The receipt run**: THE re-deriver accepts the run's log from genesis, and the deployed check
answers the reached World's own receipt for the run's call `committed` against that World's head. -/
theorem receipt_run :
    receiptOkThen (rederiveLog Xd wGenesis wLog) (fun w =>
      receiptCommittedB (Receipt.check Xd.env w.height (w.roots Xd.env) wTx 0 (Receipt.build Xd.env w wTx))) =
      true := by
  native_decide

/-- **INHABITED (§7, receipts).** The claim's committed case is reached by the deployed check: on a
World an audited fold from genesis reaches (`audited_deployed`: the fold and `Honest`), a receipt the
check answers `committed`. -/
theorem inhabited_receiptTruth (d : ByteArray → ByteArray) :
    ∃ (name nonce : ByteArray) (a : Nat) (fs : List (ByteArray × Digest)) (auth : Authority)
      (l : List (Step Digest)) (w : World Digest) (txId : Digest) (nb : Nat) (r : Receipt.Receipt Digest)
      (h : Nat) (td : Digest),
      World.fold Xd.env (genesisWorld Xd name nonce a fs auth) l = .ok w ∧
        Honest Xd (genesisWorld Xd name nonce a fs auth) l ∧
        (deployed d).receiptCheck w.height (w.roots Xd.env) txId nb r = .ok (.committed h td) := by
  obtain ⟨w, hw, hk⟩ := receiptOkThen_eq receipt_run
  obtain ⟨h, td, hc⟩ := receiptCommittedB_eq hk
  have hfh := rederiveLog_sound hw
  rw [deployed_receiptCheck]
  revert hfh hc
  generalize Receipt.build Xd.env w wTx = r
  generalize wTx = txId
  generalize wLog = l
  intro hc hfh
  unfold wGenesis at hfh
  exact ⟨_, _, _, _, _, l, w, txId, 0, r, h, td, hfh.1, hfh.2, hc⟩

end Nanodregg.Spec
