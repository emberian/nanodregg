/-
# Host.Proofs.SpentCheckpoint — a reopen from a spent trusted base admits no further grant movement

`openWith_trusted` (`Host.Proofs.Trusted`) says an open from a trusted base opens to a trusted World; it does
not mention a grant. `Ledger.Proofs.grant_moves_le_cap` bounds what one honest history moves through a grant
by that grant's ledger left. This module states their composition at the deployed opener: when the decoded
base is `SpentCheckpoint` (trusted, canonical cells, a contiguous ledger, and the grant's cell left at 0)
and the writer's tail after the base has an honest history, the opened World is trusted and the base's
honest tail followed by ANY honest future moves nothing through that grant.

Premises, by name: the base's trust (HOST-64's `CheckpointTrusted`); canonical cells and a contiguous ledger
(LEDGER-18/19, load-bearing in `grant_moves_le_cap`); the spent left; and `htail`, the re-execution honesty of
the tail, because the local opener folds the writer's records without re-deriving them. A MAC or an origin pin
alone does not prove a grant was consumed. Not established here: IO crash safety, integrity-key custody, an
external exactly-once.

Re-homed from `Lang/Proofs/Contextual/Integration.lean` (LANG-P8 Objective 5) by LANG-74.1b; the tail and the
future compose by the kernel's `fold_append` and `honest_append` (`Kernel.Proofs.Rederive`).
-/
import Host.Proofs.Trusted
import Kernel.Proofs.Rederive
import Ledger.Proofs.GrantCap

namespace Nanodregg.Host.Deployed

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec Nanodregg.Host.Cli

/-- HOST-64's base premise strengthened by the application's spent-cap fact: the premise bundle of
`recovery_preserves_consumption`. A received or pruned base needs it as an assumption. -/
structure SpentCheckpoint (origin grant : D) (w : World D) : Prop where
  trusted : CheckpointTrusted origin w
  canonical : CellsCanon X.env w
  contiguous : LedgerContiguous X.env w
  spent : ∃ cell i, w.live X.env grant = some cell ∧ cell.kind = kindGrant ∧
    ledgerLeft transferBase grant cell = .ok (i, 0)

/-- **A real successful open from a spent trusted base admits zero further consumption**, in its honest
tail AND in every honest continuation: the opened World is trusted, and over the base's tail `l` followed by
any honest `future`, every amount that moves through `grant` sums to 0. -/
theorem recovery_preserves_consumption
    {origin grant : D} {keys : Keys} {file H I S : ByteArray}
    {o : Opening (World D)}
    (hopen : Id.run (openWith keys c world recorder.mark originChain foldStep file H S.size I.size
      (segReader I) (segReader S)) = .ok o)
    (hbase : ∀ b n d, Base.read keys c world file = .ok (b, n, d) →
      SpentCheckpoint origin grant b.world)
    (htail : ∀ b n d (rs : List ByteArray), Base.read keys c world file = .ok (b, n, d) →
      rs.foldlM foldStep b.world = .ok o.opened.world →
      ∃ l, World.fold X.env b.world l = .ok o.opened.world ∧ Honest X b.world l) :
    CheckpointTrusted origin o.opened.world ∧
    ∃ (b : Base (World D)) (n : Nat) (d : ByteArray)
      (rs : List ByteArray) (l : List (Step D)),
      Base.read keys c world file = .ok (b, n, d) ∧
      rs.foldlM foldStep b.world = .ok o.opened.world ∧
      World.fold X.env b.world l = .ok o.opened.world ∧ Honest X b.world l ∧
      ∀ (future : List (Step D)) (final : World D),
        World.fold X.env o.opened.world future = .ok final → Honest X o.opened.world future →
      ∃ steps : List (Step D × World D),
      steps.map Prod.fst = l ++ future ∧
      Nanodregg.Lang.Std.Chain (Ledger.Proofs.GrantStep X grant) b.world steps ∧
      ∀ amt : World D × Step D × World D → Nat,
        (∀ x ∈ (b.world :: steps.map Prod.snd).zip steps,
          amt x = 0 ∨ Ledger.Proofs.MovesThrough X grant x.1 x.2.1 (amt x)) →
        (((b.world :: steps.map Prod.snd).zip steps).map amt).sum = 0 := by
  refine ⟨openWith_trusted hopen (fun b n d hb => (hbase b n d hb).trusted), ?_⟩
  obtain ⟨b, n, d, rs, hb, hf, _⟩ :=
    openWith_world keys c world recorder.mark originChain foldStep file H I S hopen
  have base := hbase b n d hb
  obtain ⟨cell, i, hl, hk, hleft⟩ := base.spent
  obtain ⟨l, ha, hh⟩ := htail b n d rs hb hf
  refine ⟨b, n, d, rs, l, hb, hf, ha, hh, fun future final hfuture hhf => ?_⟩
  obtain ⟨steps, hmap, hc, hsum⟩ := Ledger.Proofs.grant_moves_le_cap
    base.canonical base.contiguous hl hk hleft (fold_append.mpr ⟨_, ha, hfuture⟩) (honest_append hh ha hhf)
  exact ⟨steps, hmap, hc, fun amt hamt => Nat.eq_zero_of_le_zero (hsum amt hamt)⟩

end Nanodregg.Host.Deployed
