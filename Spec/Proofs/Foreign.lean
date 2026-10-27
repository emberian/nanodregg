/-
# Spec.Proofs.Foreign — §9 RECEIPTS BETWEEN WORLDS

**The claim** (`Foreign`): a receipt the system's receipt check (`S.rc`, the check the deployed
program's laws read: `deployed_program_reads`) shows against a head cell holding the roots of a
fold of A from A's genesis names the call it shows, and that call was admitted in that fold (a Turn
of the log with that id, at the height shown, with the turn digest shown), or the hash collides
among an explicit list fixed by the receipt and the fold (the receipt's root inputs, the fold's,
and the journal path's inclusion inputs).

**Premises.** The fold and the check's acceptance fix what the receipt is about. `HeadOf` (the held
head's roots are the fold's) is NAMED and UNDISCHARGEABLE today (PROTOCOL E-3): heads are posted by
grantees, unsigned by A's writer, with no consistency proof between two posts; `inhabited_foreign`
shows it satisfiable. The decoded receipt `r` and turn digest `td` fix the collision list; the
deployed check supplies both (`check_committed_of`).

**Owed** (TOPLEVEL-SPEC §9): A's writer signs step-indexed heads and the head law demands a chain
link from the held head to the new one; `HeadOf` then reduces to "A's writer signs at most one head
per step count", and the conclusion gains "or A's writer equivocated".

Top: `top_foreign` (`Protocol.Proofs.Foreign.foreign_receipt_sound` at `deployed_lawful`). Floor:
`floor_foreign` refuses `acceptingHead` (the check that accepts any head). Inhabited:
`inhabited_foreign` (the deployed check shows a committed receipt against a head of an audited fold).
-/
import Spec.Proofs.Floor
import Spec.Sim.Foreign
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## The claim -/

/-- **The held head is the head of `wA`** (the undischarged premise, PROTOCOL E-3): if `cell` is a
head object holding an `at` head, its roots decode to `wA`'s roots digest. -/
def HeadOf (S : System D) (cell : Cell) (wA : World D) : Prop :=
  ∀ w c₀ h₀ rootsB s₀, Lang.headView (fun b => (S.dc.decode b).toOption)
      (S.X.env.bytes (Protocol.Foreign.headPackageId S.X.env)) cell = some (.at w c₀ h₀ rootsB s₀) →
    (S.dc.decode rootsB).toOption = some (wA.roots S.X.env)

/-- **§9. A committed receipt is an admission of the World it is a receipt of.** Whatever log `l`
the system's kernel folds from a genesis World of A to `wA`: a receipt `rb` that the receipt check
`S.rc` shows (`s`) against a head cell holding `wA`'s roots (`HeadOf`, the named premise) names the
transaction the check shows, and that transaction was admitted in `l` (a Turn of `l` with that id,
admitted after a prefix folding to `v`, at height `v.height + 1`, with the turn digest shown), or
the hash collides among the receipt's root inputs, `wA`'s, and the journal path's inclusion inputs
(an explicit list, fixed by the receipt and `wA`). -/
def Foreign (S : System D) : Prop :=
  ∀ {name nonce : ByteArray} {a : Nat} {fs : List (ByteArray × D)} {auth : Authority}
    {l : List (Step D)} {wA : World D},
    S.fold (genesisWorld S.X name nonce a fs auth) l = .ok wA →
    ∀ {cell : Cell} {rb : ByteArray} {s : Lang.Seen}, S.rc cell rb = .ok s → HeadOf S cell wA →
    ∀ {r : Receipt.Receipt D} {td : D}, Receipt.ofBytes S.X.env S.dc rb = some r →
      s.turn = S.X.env.bytes td →
      s.tx = S.X.env.bytes r.txId ∧
        ((∃ l₁ t l₂ v v', l = l₁ ++ Step.turn t :: l₂ ∧
            S.fold (genesisWorld S.X name nonce a fs auth) l₁ = .ok v ∧ S.admit v t = .ok v' ∧
            t.txId = r.txId ∧ s.height = v.height + 1 ∧ td = turnDigest S.X.env t) ∨
          CollidesAmong S.X.env.hash ([rootsPre S.X.env r.root r.jroot r.rroot r.rowsroot, wA.rootsPre S.X.env] ++
            inclPres (journalSpec S.X.env) (journalPre S.X.env) r.txId (s.height, td) r.jpath wA.journal))

/-! ## The bridge: the check the claim varies is the one the deployed program reads -/

theorem deployed_program_reads (d : ByteArray → ByteArray) :
    (deployed d).X = Codec.Deployed.ctx
      (Lang.program Digest.bytes Digest.ofBytes? (deployed d).rc) := rfl

/-! ## The top theorem -/

/-- **§9 of the deployed system**: `foreign_receipt_sound` at the deployed `Env` (`deployed_lawful`). -/
theorem top_foreign (d : ByteArray → ByteArray) :
    Foreign (deployed d) := by
  intro name nonce a fs auth l wA hA cell rb s hk hr r td hrb htd
  rw [fold_eq_world _ rfl rfl] at hA
  obtain ⟨htx, h⟩ := Protocol.Foreign.foreign_receipt_sound (X := Host.Deployed.X) deployed_lawful
    (by decide) hA hk hr hrb htd
  refine ⟨htx, ?_⟩
  rcases h with ⟨l₁, t, l₂, v, v', hl, hv, hadm, htx', hh, htd'⟩ | col
  · exact .inl ⟨l₁, t, l₂, v, v', hl, (fold_eq_world (deployed d) rfl rfl _ _).trans hv, hadm, htx', hh, htd'⟩
  · exact .inr col

/-! ## The floor: a check that accepts any head -/

omit [Ord D] [DecidableEq D] in
theorem headView_kind0 (dO : ByteArray → Option D) (pkg : ByteArray) (sl : Slots) :
    Lang.headView dO pkg ⟨0, .rom, sl⟩ = none := by
  simp [Lang.headView, kindObject]

/-- **The receipt decodes**, names the run's call, and no two of the claim's listed inputs collide
at the genesis World with the shown entry `(1, oneDigest)`. -/
theorem run_accept_all :
    (match Receipt.ofBytes Xd.env Codec.Deployed.digestCodec rbAny with
     | some r => decide (r.txId = wTx) &&
        collisionFree Xd.env.hash ([rootsPre Xd.env r.root r.jroot r.rroot r.rowsroot, wGenesis.rootsPre Xd.env] ++
          inclPres (journalSpec Xd.env) (journalPre Xd.env) r.txId (1, oneDigest) r.jpath wGenesis.journal)
     | none => false) = true := by
  native_decide

/-- **FLOOR (§9).** The claim refuses the check that accepts any head: at A's genesis World and the
empty log (no admission exists), a cell that is no head (so `HeadOf` holds), and decoding receipt
bytes naming the call the check shows, the claim's conclusion would need a collision among the
listed inputs, and they are collision-free. -/
theorem floor_foreign (d : ByteArray → ByteArray) : ¬ Foreign (acceptingHead d) := by
  intro h
  have hr := run_accept_all
  cases hro : Receipt.ofBytes Xd.env Codec.Deployed.digestCodec rbAny with
  | none => rw [hro] at hr; cases hr
  | some r =>
    rw [hro] at hr
    dsimp only at hr
    simp only [Bool.and_eq_true] at hr
    obtain ⟨htx, hc⟩ := hr
    have htx' : r.txId = wTx := of_decide_eq_true htx
    have hhead : HeadOf (acceptingHead d) plainCell wGenesis := by
      intro w c₀ h₀ rootsB s₀ hv
      have hv' := hv.symm.trans (headView_kind0 _ _ [])
      cases hv'
    obtain ⟨-, hadm | col⟩ := h (name := "spec".toUTF8) (nonce := "spec-0".toUTF8) (a := 100000000)
      (fs := [(wKey, nextKeyDigest Xd wNext)]) (auth := Authority.none) (l := []) (wA := wGenesis)
      rfl (cell := plainCell) (rb := rbAny) (s := seenAny) rfl hhead (td := oneDigest) hro rfl
    · obtain ⟨l₁, t, l₂, -, -, hl, -⟩ := hadm
      simp at hl
    · exact not_collides hc col

/-! ## Inhabited: the deployed check shows a committed receipt against a head of the fold -/

/-- **The foreign run**: THE re-deriver accepts the run's log from genesis (non-empty); the deployed
check shows that World's receipt for the run's call against the head cell of that World; and the
head cell's held roots decode to that World's roots. -/
theorem run_foreign :
    (match rederiveLog Xd wGenesis wLog with
     | .ok w => !wLog.isEmpty &&
        (match Protocol.Foreign.check Xd.env Codec.Deployed.digestCodec (headCellOf w) (rbOf w) with
         | .ok _ => true | .error _ => false) &&
        (match Lang.headView (fun b => (Codec.Deployed.digestCodec.decode b).toOption)
            (Xd.env.bytes (Protocol.Foreign.headPackageId Xd.env)) (headCellOf w) with
         | some (.at _ _ _ rootsB _) =>
            decide ((Codec.Deployed.digestCodec.decode rootsB).toOption = some (w.roots Xd.env))
         | _ => false)
     | .error _ => false) = true := by
  native_decide

/-- **INHABITED (§9).** Every premise of the claim at the deployed check is reached by a deployed
run: a non-empty log the kernel folds from a genesis World, a head cell holding the fold's roots
(`HeadOf`), and receipt bytes the deployed check shows `committed` against it. -/
theorem inhabited_foreign (d : ByteArray → ByteArray) :
    ∃ (name nonce : ByteArray) (a : Nat) (fs : List (ByteArray × Digest)) (auth : Authority)
      (l : List (Step Digest)) (wA : World Digest) (cell : Cell) (rb : ByteArray) (s : Lang.Seen)
      (r : Receipt.Receipt Digest) (td : Digest),
      (deployed d).fold (genesisWorld (deployed d).X name nonce a fs auth) l = .ok wA ∧ l ≠ [] ∧
        (deployed d).rc cell rb = .ok s ∧
        HeadOf (deployed d) cell wA ∧ Receipt.ofBytes Xd.env Codec.Deployed.digestCodec rb = some r ∧
        s.turn = Xd.env.bytes td := by
  have hr := run_foreign
  cases hw : rederiveLog Xd wGenesis wLog with
  | error e => rw [hw] at hr; cases hr
  | ok w =>
    rw [hw] at hr
    dsimp only at hr
    simp only [Bool.and_eq_true] at hr
    obtain ⟨⟨hne, hk⟩, hv⟩ := hr
    have hfh := rederiveLog_sound hw
    cases hc : Protocol.Foreign.check Xd.env Codec.Deployed.digestCodec (headCellOf w) (rbOf w) with
    | error e => rw [hc] at hk; cases hk
    | ok s =>
      cases hh : Lang.headView (fun b => (Codec.Deployed.digestCodec.decode b).toOption)
          (Xd.env.bytes (Protocol.Foreign.headPackageId Xd.env)) (headCellOf w) with
      | none => rw [hh] at hv; cases hv
      | some hv₀ =>
        cases hv₀ with
        | forked _ => rw [hh] at hv; cases hv
        | «at» w₀ c₀ h₀ rB s₀ =>
          rw [hh] at hv
          dsimp only at hv
          have hro := of_decide_eq_true hv
          obtain ⟨-, -, -, -, -, -, r, td, -, -, hrb, -, htd, -⟩ := Protocol.Foreign.check_committed_of hc
          have hhead : HeadOf (deployed d) (headCellOf w) w := by
            intro w₁ c₁ h₁ rB₁ s₁ hv₁
            have hv₁' : Lang.headView (fun b => (Codec.Deployed.digestCodec.decode b).toOption)
                (Xd.env.bytes (Protocol.Foreign.headPackageId Xd.env)) (headCellOf w) =
                some (.at w₁ c₁ h₁ rB₁ s₁) := hv₁
            rw [hh] at hv₁'
            simp only [Option.some.injEq, Lang.HeadView.at.injEq] at hv₁'
            obtain ⟨-, -, -, rfl, -⟩ := hv₁'
            exact hro
          have hne' : wLog ≠ [] := by
            intro he; rw [he] at hne; cases hne
          revert hfh hc hhead hrb htd hne'
          generalize headCellOf w = cell
          generalize rbOf w = rb
          generalize wLog = l
          intro hfh hc hrb htd hhead hne'
          have hf := hfh.1
          unfold wGenesis at hf
          exact ⟨_, _, _, _, _, l, w, cell, rb, s, r, td,
            (fold_eq_world (deployed d) rfl rfl _ _).trans hf, hne', hc, hhead, hrb, htd⟩

end Nanodregg.Spec
