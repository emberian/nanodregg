/-
# Protocol.Proofs.Certified — what a stranger learns from a genesis input and a certificate

`stranger_ok`: a head the stranger's check takes is certified, under the authority the genesis input
names, for the World that input makes, whose origin is `originOf` of exactly those inputs (the
authority included, KERNEL-69): so the certificate verifies (`Head.certified`) for the origin the
input commits, with that authority's `threshold` distinct listed signers (`Proofs.Head.certified_ok`).
-/
import Protocol.Certified
import Kernel.Proofs.Origin

namespace Nanodregg.Protocol.Proofs.Certified

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol.Head Nanodregg.Protocol.Certified

variable {D : Type} [Ord D] [DecidableEq D]

theorem stranger_ok {X : Ctx D} {input cert : ByteArray} {h : Head D}
    (hc : Certified.check X input cert = .ok h) :
    ∃ name nonce allowance fs auth c,
      Invite.startOf X input = some (.genesis name nonce allowance fs auth) ∧
      certified X auth (originOf X name nonce allowance fs auth) cert = .ok c ∧ c.head = h := by
  unfold Certified.check at hc
  split at hc
  · cases hc
  · cases hc
  · rename_i name nonce allowance fs auth hs
    split at hc
    · cases hc
    · rename_i w hg
      split at hc
      · cases hc
      · rename_i c hcert
        cases hc
        have hw : w = genesisWorld X name nonce allowance fs auth := by
          unfold genesis at hg
          simp only [bind, Except.bind, pure, Except.pure] at hg
          split at hg
          · cases hg
          · cases hg; rfl
        refine ⟨name, nonce, allowance, fs, auth, c, hs, ?_, rfl⟩
        rw [← genesis_origin, ← hw]
        exact hcert

end Nanodregg.Protocol.Proofs.Certified
