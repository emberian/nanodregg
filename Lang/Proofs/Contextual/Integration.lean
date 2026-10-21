/- P8: the integration client of LANG-67, P4/P9/P10/P11b and the real kernel.
Nano is LPCFS's single-transaction case: one Store writer atomically changes the
open artifact, the value cells, and the counted grant. No external exactly-once
effect or cross-writer agreement is asserted. -/
import Lang.Journey
import Lang.Proofs.Contextual.Negotiation
import Lang.Proofs.Contextual.Trace
import Lang.Proofs.Contextual.Provenance
import Lang.Proofs.Contextual.TransportKinds
import Ledger.Proofs.GrantCap
import Host.Proofs.Trusted

namespace Nanodregg.Lang.Contextual.Integration
open Nanodregg.Kernel Nanodregg.Kernel.Receive
open Nanodregg.Lang.Journey

/-- Objective 1: the provider choices exercised by the journey are fillings of
LANG-67's open two-cell protocol, including cancellation before commitment.
This is a protocol judgment, not a claim that package lowering is verified. -/
theorem substitution_preserves_open_judgment (p : Protocol.Negotiation.Provider) :
    Protocol.HasProt Protocol.Negotiation.spec Protocol.Negotiation.Ω
      Protocol.Negotiation.Γ₀ (fun _ _ => True) Protocol.Negotiation.Φ₀
      Protocol.Negotiation.Δ₀
      (Protocol.fill Protocol.Negotiation.Ω
        (Protocol.Negotiation.choose (Protocol.Negotiation.plan p))
        Protocol.Negotiation.template) :=
  Protocol.Negotiation.instantiations_hasProt.1 p

/-- Objective 2: P10's complete trace, specialized to the journey's REAL live
provider pins. It does not require equality of unrelated World entries. -/
theorem unchanged_dependencies_preserve_applicability
    (w v : Kernel.World Journey.D) (supports : List (Journey.D × Journey.D)) (i : Nat)
    (h : Trace.observe p8Guard (p8Iface false) (p8World w supports) (p8Candidate i) =
         Trace.observe p8Guard (p8Iface false) (p8World v supports) (p8Candidate i)) :
    judge (p8Iface false) (p8World w supports) (p8Candidate i) =
      judge (p8Iface false) (p8World v supports) (p8Candidate i) :=
  Trace.observation_complete p8Guard (p8Iface false) _ _ _ h

/-- The polynomial read by P8.2 characterizes availability at EVERY kernel World,
not just the initial environment where both grants were live. -/
theorem provenance_over_live_environment (w : Kernel.World Journey.D)
    (supports : List (Journey.D × Journey.D)) :
    (∃ c ∈ [p8Candidate 0, p8Candidate 1],
      judge (p8Iface false) (p8World w supports) c = .verified) ↔
    ∃ m ∈ P9.provenance (p8Iface false) [p8Candidate 0, p8Candidate 1],
      m.eval (p8Iface false) (p8World w supports) = true :=
  P9.provenance_iff

/-- Checked correspondence on all provider indices, not only the chosen one.
The representation tag changes; the provider index survives both inverses. -/
theorem representation_correspondence : p8Correspondence.Checked := by
  constructor <;> intro t ht <;> cases t with
  | mk n b => cases b <;>
      simp_all [p8Correspondence, p8Iface, Trace.Guard.install, p8Data, p8Swap]

theorem registry_checked : p8Registry.Sound := by
  intro n q h
  unfold p8Registry at h
  split at h
  · cases h
    exact representation_correspondence
  · cases h

/-- Objective 3: the accepted repair is judged under its NEW interface.
Only the rechecked constructor is consumed; there is no internal/Quot claim. -/
theorem accepted_repairs_valid
    {w : Kernel.World Journey.D} {supports : List (Journey.D × Journey.D)}
    {i n : Nat} {ev : RepairObjects.TransportEvidence p8Data (Nat → Bool)}
    (h : TransportKinds.recheck p8Registry n (p8World w supports) (p8Candidate i) 1 =
      .ok (.rechecked ev)) :
    judge ev.correspondence.target (p8World w supports) ev.image = .verified :=
  TransportKinds.recheck_sound registry_checked h

/-- The actual translation preserves which retained provider the journey executes. -/
theorem representation_preserves_provider (i : Nat) :
    (p8Correspondence.forward (p8Candidate i).filling).1 = i ∧
    (p8Correspondence.forward (p8Candidate i).filling).2 = true := by
  exact ⟨rfl, rfl⟩

/-- The returned repair's image, not merely the registry's forward function,
names the same provider in the new representation. -/
theorem accepted_repair_preserves_provider
    {w : Kernel.World Journey.D} {supports : List (Journey.D × Journey.D)}
    {i n : Nat} {ev : RepairObjects.TransportEvidence p8Data (Nat → Bool)}
    (h : TransportKinds.recheck p8Registry n (p8World w supports) (p8Candidate i) 1 =
      .ok (.rechecked ev)) :
    ev.image.filling = (i, true) := by
  unfold TransportKinds.recheck at h
  split at h
  · cases h
  · rename_i ev' he
    cases h
    have hs := RepairObjects.transport_sound registry_checked he
    have hq := hs.2.2.2.2.2.2.2
    unfold p8Registry at hq
    split at hq
    · have eq := (Option.some.inj hq).symm
      have image := hs.2.2.1
      rw [eq] at image
      exact image
    · cases hq
  · cases h

/-- The proof transport reaches the actual package-call argument builder.
Changing the representation cannot silently change the asset, grant or provider. -/
theorem accepted_repair_preserves_invocation
    {w : Kernel.World Journey.D} {supports : List (Journey.D × Journey.D)}
    {i n : Nat} {ev : RepairObjects.TransportEvidence p8Data (Nat → Bool)}
    (h : TransportKinds.recheck p8Registry n (p8World w supports) (p8Candidate i) 1 =
      .ok (.rechecked ev)) (asset grant : Journey.D) (owners : List Journey.D) :
    p8Arg asset (owners[ev.image.filling.1]?.getD 0) grant =
      p8Arg asset (owners[i]?.getD 0) grant := by
  rw [accepted_repair_preserves_provider h]

/-- Objective 4: successful commitment is the authorized re-execution, its
actual call bytes and id, and the journal's receipt for exactly that transition.
No independently selected receipt or unbound checked artifact appears here. -/
theorem commitment_binds_receipt
    {w w' : Kernel.World Journey.D} {c : Call Journey.D} {t : Turn Journey.D}
    (hcanon : w.JournalCanon Sim.env)
    (h : submit (ctxWith langProgram) w c = .ok (t, w')) :
    receive (ctxWith langProgram) w c = .ok t ∧
    World.admit Sim.env w t = .ok w' ∧
    t.event = (ctxWith langProgram).callBytes c ∧
    t.txId = txIdOf (ctxWith langProgram) c ∧
    w'.journalAt Sim.env (txIdOf (ctxWith langProgram) c) =
      some (w.height + 1, turnDigest Sim.env t) := by
  obtain ⟨_, hr, ha⟩ := submit_ok h
  have hr' := hr
  unfold receive at hr'
  simp only [except_bind_ok] at hr'
  obtain ⟨_, _, hs⟩ := hr'
  obtain ⟨_, d, _, hd⟩ := receiveWith_sealed hs
  have ht := sealTurn_ok hd
  have hj := admit_journaled hcanon ha
  rw [ht.2.2.2.2.1] at hj
  exact ⟨hr, ha, ht.2.2.2.1, ht.2.2.2.2.1, hj⟩

section Counted
variable {D : Type} [Ord D] [DecidableEq D] [Std.TransOrd D] [Std.LawfulEqOrd D]

/-- One-use means at most one unit across ANY audited history, including nested
object calls. Canonical cells and contiguous ledgers are load-bearing premises
(LEDGER-18/19's gap tooth); cryptographic collision resistance is not silently added. -/
theorem one_use_consumption {X : Kernel.Receive.Ctx D} {g : D}
    {w w' : Kernel.World D} {l : List (Kernel.Step D)} {cell : Cell} {i : Nat}
    (hcan : CellsCanon X.env w) (hlc : LedgerContiguous X.env w)
    (hl : w.live X.env g = some cell) (hk : cell.kind = kindGrant)
    (hleft : ledgerLeft transferBase g cell = .ok (i, 1))
    (h : audit X w l = .ok w') :
    ∃ steps : List (Kernel.Step D × Kernel.World D), steps.map Prod.fst = l ∧
      Std.Chain (Ledger.Proofs.GrantStep X g) w steps ∧
      ∀ amt : Kernel.World D × Kernel.Step D × Kernel.World D → Nat,
        (∀ x ∈ (w :: steps.map Prod.snd).zip steps,
          amt x = 0 ∨ Ledger.Proofs.MovesThrough X g x.1 x.2.1 (amt x)) →
        (((w :: steps.map Prod.snd).zip steps).map amt).sum ≤ 1 :=
  Ledger.Proofs.grant_moves_le_cap hcan hlc hl hk hleft h

end Counted

/-- Objective 6's environment assumption: a writer delivers this call while the
journal and refusal cache are fresh, the checked re-execution succeeds, and its
actual turn is admissible. These are separate receiver/kernel obligations, not
an assumption that submit already succeeds or that a network is fair. -/
structure ReadyWriter (w : Kernel.World Journey.D) (c : Call Journey.D)
    (t : Turn Journey.D) (w' : Kernel.World Journey.D) : Prop where
  fresh : w.journalAt (ctxWith langProgram).env (txIdOf (ctxWith langProgram) c) = none
  uncancelled : refusedAnswer (ctxWith langProgram) w c = none
  executed : receive (ctxWith langProgram) w c = .ok t
  admissible : World.admit (ctxWith langProgram).env w t = .ok w'

/-- A ready writer makes one successful atomic step. No unconditional liveness,
future response, or external side-effect delivery is inferred. -/
theorem progress_under_ready_writer {w w' : Kernel.World Journey.D}
    {c : Call Journey.D} {t : Turn Journey.D} (h : ReadyWriter w c t w') :
    submit (ctxWith langProgram) w c = .ok (t, w') := by
  simp [submit, h.fresh, h.uncancelled, h.executed, h.admissible]

/-- After a committed effect, a saved continuation has no authority to consume
again: the same signed call goes through submit again and is refused by NAME.
A repaired future call is freshly executed (P8.4), never fill-and-resume. -/
theorem reexecute_committed_effect {w : Kernel.World Journey.D} {c : Call Journey.D}
    {h : Nat} {d : Journey.D}
    (hj : w.journalAt Sim.env (txIdOf (ctxWith langProgram) c) = some (h, d)) :
    submit (ctxWith langProgram) w c = .error (.rejected (.replayed h)) :=
  submit_replayed hj

end Nanodregg.Lang.Contextual.Integration

namespace Nanodregg.Lang.Contextual.Integration.Recovery
open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Host.Deployed

/-- HOST-64's assumption strengthened by the application's spent-cap fact.
Received or pruned bases require this premise; a MAC or an origin pin alone does
not prove a grant was consumed. The tail assumption below also names re-execution
honesty, since the local opener folds trusted writer records without re-auditing. -/
structure SpentCheckpoint (origin grant : Host.Deployed.D) (w : Kernel.World Host.Deployed.D) : Prop where
  trusted : CheckpointTrusted origin w
  canonical : CellsCanon X.env w
  contiguous : LedgerContiguous X.env w
  spent : ∃ cell i, w.live X.env grant = some cell ∧ cell.kind = kindGrant ∧
    ledgerLeft transferBase grant cell = .ok (i, 0)

/-- Successful replay composes with future audited execution. -/
private theorem audit_append_to {w mid final : Kernel.World Host.Deployed.D}
    {pre suffix : List (Kernel.Step Host.Deployed.D)}
    (hp : audit X w pre = .ok mid) (hs : audit X mid suffix = .ok final) :
    audit X w (pre ++ suffix) = .ok final := by
  induction pre generalizing w with
  | nil =>
    simp only [audit, Except.ok.injEq] at hp
    subst w
    exact hs
  | cons step rest ih =>
    cases he : auditStep X w step with
    | error e => simp [audit, he] at hp
    | ok next =>
      cases hr : audit X next rest with
      | error e => cases e; simp [audit, he, hr] at hp
      | ok result =>
        have eq : result = mid := by simpa [audit, he, hr] using hp
        subst result
        simp [audit, he, ih hr]

/-- Objective 5: a REAL successful checkpoint open from a spent trusted base
admits zero further consumption in its audited tail AND every future audited
continuation. Assumptions: the decoded
base is trusted and spent, and the writer's actual tail has an audited history.
This does not establish IO crash safety, integrity-key custody or external once. -/
theorem recovery_preserves_consumption
    {origin grant : Host.Deployed.D} {keys : Keys} {file H I S : ByteArray}
    {o : Opening (Kernel.World Host.Deployed.D)}
    (hopen : Id.run (openWith keys c world recorder.mark originChain foldStep file H S.size I.size
      (segReader I) (segReader S)) = .ok o)
    (hbase : ∀ b n d, Base.read keys c world file = .ok (b, n, d) →
      SpentCheckpoint origin grant b.world)
    (htail : ∀ b n d (rs : List ByteArray), Base.read keys c world file = .ok (b, n, d) →
      rs.foldlM foldStep b.world = .ok o.opened.world →
      ∃ l, audit X b.world l = .ok o.opened.world) :
    CheckpointTrusted origin o.opened.world ∧
    ∃ (b : Base (Kernel.World Host.Deployed.D)) (n : Nat) (d : ByteArray)
      (rs : List ByteArray) (l : List (Kernel.Step Host.Deployed.D)),
      Base.read keys c world file = .ok (b, n, d) ∧
      rs.foldlM foldStep b.world = .ok o.opened.world ∧
      audit X b.world l = .ok o.opened.world ∧
      ∀ (future : List (Kernel.Step Host.Deployed.D)) (final : Kernel.World Host.Deployed.D),
        audit X o.opened.world future = .ok final →
      ∃ steps : List (Kernel.Step Host.Deployed.D × Kernel.World Host.Deployed.D),
      steps.map Prod.fst = l ++ future ∧
      Lang.Std.Chain (Ledger.Proofs.GrantStep X grant) b.world steps ∧
      ∀ amt : Kernel.World Host.Deployed.D × Kernel.Step Host.Deployed.D × Kernel.World Host.Deployed.D → Nat,
        (∀ x ∈ (b.world :: steps.map Prod.snd).zip steps,
          amt x = 0 ∨ Ledger.Proofs.MovesThrough X grant x.1 x.2.1 (amt x)) →
        (((b.world :: steps.map Prod.snd).zip steps).map amt).sum = 0 := by
  refine ⟨openWith_trusted hopen (fun b n d hb => (hbase b n d hb).trusted), ?_⟩
  obtain ⟨b, n, d, rs, hb, hf, _⟩ :=
    openWith_world keys c world recorder.mark originChain foldStep file H I S hopen
  have base := hbase b n d hb
  obtain ⟨cell, i, hl, hk, hleft⟩ := base.spent
  obtain ⟨l, ha⟩ := htail b n d rs hb hf
  refine ⟨b, n, d, rs, l, hb, hf, ha, fun future final hfuture => ?_⟩
  obtain ⟨steps, hmap, hc, hsum⟩ := Ledger.Proofs.grant_moves_le_cap
    base.canonical base.contiguous hl hk hleft (audit_append_to ha hfuture)
  exact ⟨steps, hmap, hc, fun amt hamt => Nat.eq_zero_of_le_zero (hsum amt hamt)⟩

end Nanodregg.Lang.Contextual.Integration.Recovery

