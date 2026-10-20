/-
# Hosting.Proofs.Open — the World a tail opens to is canonical (cv 01a14a5f-c476)

HOSTING-14's premise (i): the World `Host.Tail.open` hands the broker and the controller is
`World.Canon`, so `Loop.allIds_complete` / `start_tracks` (stated under Canon) apply at round 0.
The chain, link by link, each a theorem of its owner: `Host.openWith_world` (the opened World is the
fold of the tail step over the segment's records after the base `Base.read` decodes, HOST-28) →
`Host.Base.read_decode` (that base is `Base.codec`'s decode) → `Codec.Codec.Stream.refine_get_inner` and
`product_get_fst` (the base's World is the World codec's read at the record's offset 0) →
`Codec.Deployed.world_get_canon` (any World the deployed codec reads is canonical) → per record,
`stepTurns_fold` (a tail step is `World.fold` of the Turns it reports) and KERNEL's `fold_canon`.
`Tail.open` is `openAt` = this `openWith` over the files' IO readers: that is code, not a theorem.
-/
import Host.Proofs.Backup
import Host.Deployed
import Codec.Proofs.Deployed
import Codec.Proofs.Raw
import Kernel.Proofs.Cells
import Hosting.Proofs.Allowance

namespace Nanodregg.Hosting.Proofs.Open

open Nanodregg.Kernel Nanodregg.Host

/-- Folding the tail's World step (the one `Tail.open` passes to the open) over any records keeps a
World canonical. -/
theorem tail_foldlM_canon : ∀ {w w' : World Codec.Digest} {rs : List ByteArray},
    w.Canon Host.Deployed.X.env → rs.foldlM (fun w r => (Host.Deployed.tailStep w r).map Prod.fst) w = .ok w' → w'.Canon Host.Deployed.X.env
  | w, w', [], hc, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hc
  | w, w', r :: rs, hc, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      cases hp : Host.Deployed.tailStep w r with
      | error e => rw [hp] at h₁; cases h₁
      | ok p =>
        rw [hp] at h₁
        obtain ⟨w₂, ps⟩ := p
        cases h₁
        exact tail_foldlM_canon
          (fold_canon hc (Proofs.Allowance.stepTurns_fold (E := Host.Deployed.X.env) hp)) h

/-- **The World a tail opens to is canonical.** Whatever base file and segment bytes the open
reads, a World it returns is `World.Canon` under the deployed environment: the base's World is
canonical because the deployed World codec read it (`world_get_canon`), and every record after it
is admitted Turns (`fold_canon`). -/
theorem open_world_canon {keys : Keys} {mark : World Codec.Digest → Nat × ByteArray}
    {origin : World Codec.Digest → ByteArray} {file H I S : ByteArray} {o : Opening (World Codec.Digest)}
    (h : Id.run (openWith keys Host.Deployed.c Host.Deployed.world mark origin (fun w r => (Host.Deployed.tailStep w r).map Prod.fst) file H S.size I.size
      (segReader I) (segReader S)) = .ok o) :
    o.opened.world.Canon Host.Deployed.X.env := by
  obtain ⟨b, _n, _d, rs, hb, hf, -⟩ := openWith_world keys Host.Deployed.c Host.Deployed.world mark origin (fun w r => (Host.Deployed.tailStep w r).map Prod.fst) file H I S h
  obtain ⟨r, _, _, hd, _⟩ := Base.read_decode keys Host.Deployed.c Host.Deployed.world file hb
  simp only [Codec.Stream.decode] at hd
  split at hd
  · rename_i v j hget
    split at hd
    · cases hd
      obtain ⟨x, hx, hacc⟩ := Codec.Stream.refine_get_inner hget
      obtain ⟨_j, hw⟩ := Codec.Stream.product_get_fst hx
      obtain ⟨xw, xo, xt, xio, xit, xrf, xk0⟩ := x
      simp only at hacc
      split at hacc
      · cases hacc
        exact tail_foldlM_canon (Codec.Deployed.world_get_canon hw).1 hf
      · cases hacc
    · cases hd
  · cases hd

end Nanodregg.Hosting.Proofs.Open
