/-
# Kernel.Proofs.RowsRangeDeployed — range reads at the deployed codec, every premise discharged

`fold_range_exact`: on every World a checked genesis and a fold reach, every range read of a turn
admitted from it gave the pin of the listing that is exactly the World's rows under its prefix, in
strictly ascending key-byte order (`admit_range_exact` with `hE` from `deployed_lawful`, the rows'
canonicity from `fold_rowsCanon`, and every entry fitting from `fold_rowsOk`).
-/
import Kernel.Proofs.RowsHead
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Deployed

/-- **Deployed: a range read lists exactly the rows under its prefix, in key order.** -/
theorem fold_range_exact (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {auth : Authority} {g w w' : World Digest} {l : List (Step Digest)} {t : Turn Digest}
    (hg : genesis (ctx program) name nonce allowance founders auth = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.admit env w t = .ok w') :
    ∀ q ∈ t.ranges, ∃ c s lim cap width rt rows,
      headOf env w.rows q.parent q.rel = some (c, s, lim, cap, width, rt) ∧ q.pre.size ≤ width ∧
      rangeRows env w.rows q.parent q.rel width q.pre q.most = some rows ∧
      rangePin env q.parent q.rel width q.pre (headFloor env w.rows q.parent q.rel) rows = q.seen ∧
      (∀ s v, (s, v) ∈ rows ↔ rowAt env w.rows s = some v ∧
        startsWith (rowsPrefix env q.parent q.rel width ++ q.pre) (rowKeyBytes env s) = true) ∧
      rows.Pairwise (fun a b => compare (rowKeyBytes env a.1).data (rowKeyBytes env b.1).data = .lt) := by
  obtain ⟨-, rfl⟩ := genesis_ok.mp hg
  have hc : w.RowsCanon env :=
    fold_rowsCanon (receive_genesis_rowsCanon (ctx program) name nonce allowance founders auth) hl
  have hok : w.RowsOk env := fold_rowsOk deployed_lawful
    (receive_genesis_rowsCanon (ctx program) name nonce allowance founders auth)
    (receive_genesis_rowsOk (ctx program) name nonce allowance founders auth) hl
  exact admit_range_exact deployed_lawful hc hok.1 h

end Nanodregg.Kernel.Receive
