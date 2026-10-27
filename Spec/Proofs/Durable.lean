/-
# Spec.Proofs.Durable — §5 DURABILITY, the writer's reopen half

**Claim (`Durable.reopen`).** Whatever base file, checkpoint header, index file and segment bytes
the writer's open (`S.reopen`) reads, if it opens, the World it returns is the fold under the
system's kernel (`S.fold`), from the `Kept` World of the base it read, of EXACTLY the records on
disk: every record `Log.recover` verifies in the segment from the base's offset, in order (the
completeness clause), whose encoding is literally the segment's bytes from the base's offset to the
open's position, and which decode under `S.dc` to the steps folded; and that World is `Kept`. No
premise beyond the open succeeding.

The claim is at `System Digest` only: `Host.Deployed.Kept` is the deployed instance's invariant (its
fields read `Host.Deployed.X.env`), and nothing generic over `D` states it.

Why the completeness clause: `host_reopen_folds`' statement alone (`Durable.reopenSound`) holds of
the open that returns the base's World at the base's position on every Store (zero records, the
empty prefix): `amnesiac_reopenSound`. Recovery's records are what refuse it (`floor_durable_reopen`).

Owed (not carried): the reopen is a FOLD, not an audited one: `Honest` is not carried across a
crash (`foldStep` does not re-judge its own records, and no theorem ties a record appended to what
`admitBatch` staged); and the acknowledged-reply half (every `ok`/recorded `refused` names a step on
disk) and the audited half need §11.4's interpreter of `serve` over `Store`/`Port`.
-/
import Spec.Sim.Durable
import Spec.Proofs.Bridge
import Host.Proofs.Refine
import Host.Proofs.Backup
import Host.Proofs.Open
import Host.Proofs.Log

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-- **D1, the writer's reopen.** An open that succeeds returns the fold, under `S`'s kernel, from
the `Kept` World of the base it read, of exactly the records on disk past that base (all those
`Log.recover` verifies there, and their encoding is the bytes up to the open's position), decoded
by `S`'s record codec; and that World is `Kept`. -/
def Durable.reopen (S : System Digest) : Prop :=
  ∀ (keys : Host.Keys) (file H I seg : ByteArray) (o : Host.Opening (World Digest)),
    S.reopen keys file H I seg = .ok o →
    ∃ (b : Host.Base (World Digest)) (n : Nat) (d : ByteArray) (rs : List ByteArray)
      (pss : List (List (Step Digest × Digest))),
      Host.Base.read keys Host.Deployed.c S.B.world file = .ok (b, n, d) ∧ Host.Deployed.Kept b.world ∧
      (Host.Log.recover keys.segment Host.Deployed.c.recordBytesMax b.tag.bytes
        (seg.extract b.offset seg.size)).records = rs ∧
      (seg.extract b.offset seg.size).extract 0 (o.pos.offset - b.offset) =
        Host.Log.encodeAll keys.segment b.tag.bytes rs ∧
      rs.mapM (Host.Record.codec S.dc).decode = .ok pss ∧
      S.fold b.world (pss.flatMap (·.map Prod.fst)) = .ok o.opened.world ∧
      Host.Deployed.Kept o.opened.world

/-- The soundness half alone (`host_reopen_folds`' statement: the World a fold of the records up to
the open's position). Not a claim: `amnesiac_reopenSound` is why `Durable.reopen` says more. -/
def Durable.reopenSound (S : System Digest) : Prop :=
  ∀ (keys : Host.Keys) (file H I seg : ByteArray) (o : Host.Opening (World Digest)),
    S.reopen keys file H I seg = .ok o →
    ∃ (b : Host.Base (World Digest)) (n : Nat) (d : ByteArray) (rs : List ByteArray)
      (pss : List (List (Step Digest × Digest))),
      Host.Base.read keys Host.Deployed.c S.B.world file = .ok (b, n, d) ∧ Host.Deployed.Kept b.world ∧
      (seg.extract b.offset seg.size).extract 0 (o.pos.offset - b.offset) =
        Host.Log.encodeAll keys.segment b.tag.bytes rs ∧
      rs.mapM (Host.Record.codec S.dc).decode = .ok pss ∧
      S.fold b.world (pss.flatMap (·.map Prod.fst)) = .ok o.opened.world ∧
      Host.Deployed.Kept o.opened.world

/-! ## The deployed open -/

/-- The deployed system's reopen is `Host.openWith` at the deployed instance, over bytes. -/
theorem deployed_reopen_eq (d : ByteArray → ByteArray) (keys : Host.Keys) (file H I seg : ByteArray) :
    (deployed d).reopen keys file H I seg = Id.run (Host.openWith keys Host.Deployed.c Host.Deployed.world Host.Deployed.recorder.mark
      Host.Deployed.originChain Host.Deployed.foldStep file H seg.size I.size (Host.segReader I)
      (Host.segReader seg)) := by
  dsimp only [deployed]

/-- The amnesiac system's reopen is `amnesiacOpen`. -/
theorem amnesiac_reopen_eq (d : ByteArray → ByteArray) (keys : Host.Keys) (file H I seg : ByteArray) :
    (amnesiac d).reopen keys file H I seg = amnesiacOpen keys file H I seg := by
  dsimp only [amnesiac]

/-- What `openLog` folds is every record `Log.recover` reads, and it ends where recovery ends. -/
theorem openLog_recover {W F : Type} {s : Host.Log.Sealer} {recordMax : Nat} {step : W → ByteArray → Except F W}
    {w₀ : W} {initial log : ByteArray} {o : Host.Opened W}
    (h : Host.openLog s recordMax step w₀ initial log = .ok o) :
    (Host.Log.recover s recordMax initial log).records.foldlM step w₀ = .ok o.world ∧
      o.validLen = (Host.Log.recover s recordMax initial log).validLen := by
  unfold Host.openLog at h
  generalize Host.Log.recover s recordMax initial log = rv at h ⊢
  simp only at h
  split at h
  · cases h
  · split at h
    · rename_i w hw
      cases h
      exact ⟨(Host.foldRecords_ok step rv.records w₀ w 0).mp hw, rfl⟩
    · cases h

/-- A run of deployed reopen steps over records is the fold of the steps those records decode to
(`Host.Proofs.Refine`'s private `foldlM_foldStep_folds`, restated). -/
theorem foldStep_folds :
    ∀ {w w' : World Digest} {rs : List ByteArray}, rs.foldlM Host.Deployed.foldStep w = .ok w' →
      ∃ pss : List (List (Step Digest × Digest)),
        rs.mapM (Host.Record.codec Codec.Deployed.digestCodec).decode = .ok pss ∧
        World.fold Host.Deployed.X.env w (pss.flatMap (·.map Prod.fst)) = .ok w'
  | w, w', [], h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | w, w', r :: rs, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      obtain ⟨ps, hd, hr⟩ := Host.Record.step_rooted h₁
      obtain ⟨pss, h₂, hf⟩ := foldStep_folds h
      refine ⟨ps :: pss, by simp [List.mapM_cons, hd, h₂, bind, Except.bind, pure, Except.pure], ?_⟩
      simp only [List.flatMap_cons]
      exact fold_append.mpr ⟨w₁, RootedFold.fold hr, hf⟩

/-- **D1 of the deployed system**: `host_reopen_folds` (base `Kept`, opened `Kept`),
`openWith_seg_ok` (the open is `openLog` over the segment past the base), `openLog_recover` and
`encodeAll_recover` (it folds every record recovery reads, and ends where recovery ends). -/
theorem top_durable_reopen (d : ByteArray → ByteArray) : Durable.reopen (deployed d) := by
  intro keys file H I seg o h
  have h' := h
  rw [deployed_reopen_eq] at h'
  obtain ⟨b, n, dd, -, -, hb, hk, -, -, -, hk'⟩ := Host.Deployed.host_reopen_folds h'
  obtain ⟨b', _, _, _, op, _, hb', _, _, _, _, _, _, _, _, _, hop, _, ho⟩ :=
    Host.openWith_seg_ok keys Host.Deployed.c Host.Deployed.world Host.Deployed.recorder.mark
      Host.Deployed.originChain Host.Deployed.foldStep file H I seg h'
  rw [hb] at hb'
  cases hb'
  obtain ⟨hf, hvl⟩ := openLog_recover hop
  obtain ⟨pss, hd, hfold⟩ := foldStep_folds (Host.indexed_foldlM_fst _ _ _ _ _ _ hf)
  obtain ⟨he, -⟩ := Host.Log.encodeAll_recover keys.segment Host.Deployed.c.recordBytesMax b.tag.bytes
    (seg.extract b.offset seg.size)
  subst ho
  refine ⟨b, n, dd, _, pss, hb, hk, rfl, ?_, hd, ?_, hk'⟩
  · show (seg.extract b.offset seg.size).extract 0 (b.offset + op.validLen - b.offset) = _
    rw [Nat.add_sub_cancel_left, hvl]
    exact he
  · rw [fold_eq_world _ rfl rfl]
    exact hfold

/-! ## The floor: the open that forgets the segment -/

/-- What the amnesiac open returns, where the deployed open and the base read succeed. -/
theorem amnesiac_ok {d d' : ByteArray → ByteArray} {keys : Host.Keys} {file H I seg : ByteArray}
    {o₀ : Host.Opening (World Digest)} {b : Host.Base (World Digest)} {n : Nat} {dd : ByteArray}
    (ho : (deployed d').reopen keys file H I seg = .ok o₀)
    (hb : Host.Base.read keys Host.Deployed.c Host.Deployed.world file = .ok (b, n, dd)) :
    (amnesiac d).reopen keys file H I seg =
      .ok { o₀ with opened := ⟨b.world, 0, 0, b.tag.bytes, 0⟩, pos := ⟨b.offset, b.tag⟩, index := #[] } := by
  rw [deployed_reopen_eq] at ho
  rw [amnesiac_reopen_eq]
  unfold amnesiacOpen
  rw [ho]
  dsimp only
  rw [hb]

/-- **Why the completeness clause exists: `host_reopen_folds` alone does not say "exactly the
records on disk".** The open that returns the base's World at the base's position meets its
statement on every Store (zero records, the empty prefix). -/
theorem amnesiac_reopenSound (d : ByteArray → ByteArray) : Durable.reopenSound (amnesiac d) := by
  intro keys file H I seg o h
  cases ho : (deployed d).reopen keys file H I seg with
  | error e =>
    have ho' := ho
    rw [deployed_reopen_eq] at ho'
    have h' := h
    rw [amnesiac_reopen_eq] at h'
    simp only [amnesiacOpen, ho'] at h'
    cases h'
  | ok o₀ =>
    cases hb : Host.Base.read keys Host.Deployed.c Host.Deployed.world file with
    | error e =>
      have ho' := ho
      rw [deployed_reopen_eq] at ho'
      have h' := h
      rw [amnesiac_reopen_eq] at h'
      simp only [amnesiacOpen, ho', hb] at h'
      cases h'
    | ok bnd =>
      obtain ⟨b, n, dd⟩ := bnd
      rw [amnesiac_ok (d := d) ho hb, Except.ok.injEq] at h
      subst h
      rw [deployed_reopen_eq] at ho
      obtain ⟨b', n', d', -, hb', hk, -⟩ := Host.Deployed.openWith_kept ho
      rw [hb] at hb'
      cases hb'
      refine ⟨b, n, dd, [], [], hb, hk, ?_, rfl, rfl, hk⟩
      simp [Host.Log.encodeAll]

/-- **The reopen run**: the deployed open of the Store holding the run's genesis and the rotate's
record opens to a World of height 1, and recovery reads a record in the segment past its base,
whose World has height 0. -/
theorem run_reopen :
    ((match (deployed storeDigest).reopen dKeys dImg.base dImg.header dImg.index dSeg with
      | .ok o => decide (o.opened.world.height = 1)
      | .error _ => false) &&
     match Host.Base.read dKeys Host.Deployed.c Host.Deployed.world dImg.base with
     | .ok (b, _, _) => decide (b.world.height = 0) &&
        decide ((Host.Log.recover dKeys.segment Host.Deployed.c.recordBytesMax b.tag.bytes
          (dSeg.extract b.offset dSeg.size)).records ≠ [])
     | .error _ => false) = true := by
  native_decide

/-- **FLOOR (D1).** The claim refuses the amnesiac writer: on the Store holding genesis and one
appended record, recovery reads that record past the base, so the claim forces the open's position
past it, but the amnesiac open stands at the base. -/
theorem floor_durable_reopen (d : ByteArray → ByteArray) : ¬ Durable.reopen (amnesiac d) := by
  intro h
  have hr := run_reopen
  revert hr
  generalize dSeg = seg
  generalize dImg.base = file
  generalize dImg.header = H
  generalize dImg.index = I
  generalize dKeys = keys
  intro hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨h₁, h₂⟩ := hr
  cases ho : (deployed storeDigest).reopen keys file H I seg with
  | error e => rw [ho] at h₁; cases h₁
  | ok o₀ =>
    cases hb : Host.Base.read keys Host.Deployed.c Host.Deployed.world file with
    | error e => rw [hb] at h₂; cases h₂
    | ok bnd =>
      obtain ⟨b, n, dd⟩ := bnd
      rw [hb] at h₂
      dsimp only at h₂
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h₂
      obtain ⟨-, hne⟩ := h₂
      have ha := amnesiac_ok (d := d) ho hb
      obtain ⟨b', n', d', rs, pss, hb', -, hrec, he, -⟩ := h keys file H I seg _ ha
      have hb'' : Host.Base.read keys Host.Deployed.c Host.Deployed.world file = .ok (b', n', d') := hb'
      rw [hb] at hb''
      cases hb''
      have hsz := congrArg ByteArray.size he
      have hge := Host.Log.size_encodeAll_ge keys.segment b.tag.bytes rs
      rw [hrec] at hne
      have hl : 0 < rs.length := List.length_pos_iff.mpr hne
      simp only [ByteArray.size_extract, Nat.sub_self] at hsz
      simp only [Host.Log.tagBytes] at hge
      have : 1 * 36 ≤ rs.length * 36 := Nat.mul_le_mul_right 36 hl
      omega

/-- **INHABITED (D1).** The deployed open reads a record past its base: on the Store holding the
run's genesis and the rotate's record, it opens to a World of height 1 from a base of height 0. -/
theorem inhabited_durable_reopen (d : ByteArray → ByteArray) :
    ∃ (keys : Host.Keys) (file H I seg : ByteArray) (o : Host.Opening (World Digest)),
      (deployed d).reopen keys file H I seg = .ok o ∧ o.opened.world.height = 1 := by
  have hr := run_reopen
  revert hr
  generalize dSeg = seg
  generalize dImg.base = file
  generalize dImg.header = H
  generalize dImg.index = I
  generalize dKeys = keys
  intro hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨h₁, -⟩ := hr
  cases ho : (deployed storeDigest).reopen keys file H I seg with
  | error e => rw [ho] at h₁; cases h₁
  | ok o =>
    rw [ho] at h₁
    exact ⟨keys, file, H, I, seg, o, ho, of_decide_eq_true h₁⟩

end Nanodregg.Spec
