/-
# Kernel.Proofs.RootedDeployed — the rooted-World theorems with their premises discharged

`Kernel.Proofs.Rooted` assumes the digest's bytes are injective and its decoder canonical. CODEC
proves both for the deployed digest (`Codec.Proofs.Deployed`), so under the deployed `Ctx`: every
World an audited log reaches from a founders' genesis is rooted, and every enrolment admitted on
it acts for a founder through that founder's own genesis grant.
-/
import Kernel.Proofs.Rooted
import Codec.Proofs.Deployed

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Deployed

/-- **Deployed: an audited World is rooted at its founders.** -/
theorem deployed_audit_rooted (program : Program Digest) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × Digest)) {w' : World Digest} {l : List (Turn Digest)}
    (h : audit (ctx program) (genesis (ctx program) name nonce allowance founders) l = .ok w') :
    WorldRooted (ctx program) (GenesisRoot (ctx program) (originOf (ctx program) name nonce allowance founders)) w' :=
  audit_rooted (fun _ _ hb => bytes_injective hb) (genesis_rooted _ name nonce allowance founders) h

/-- **Deployed: every enrolment is a founder's.** On a World an audited log reached from genesis,
a derived enrolment's grant chain ends at a founder's live genesis grant, issued by the founder the
chain acts for. -/
theorem deployed_enroll_founder (program : Program Digest) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × Digest)) {w : World Digest} {l : List (Turn Digest)}
    (hw : audit (ctx program) (genesis (ctx program) name nonce allowance founders) l = .ok w)
    {c : Call Digest} {key : ByteArray} {next : Digest} {possession : ByteArray} {via : Digest}
    {t : Turn Digest}
    (h : enroll (ctx program) (pinned w c.unsigned.pins) c key next possession via = .ok t) :
    ∃ p r cell, GenesisRoot (ctx program) (originOf (ctx program) name nonce allowance founders) r ∧ w.live r = some cell ∧
      slotDigest (ctx program) r cell grantIssuer = .ok p ∧
      Chain (ctx program) (pinned w c.unsigned.pins) (worldId (ctx program)) (.enroll 0) true via
        c.unsigned.member p := by
  obtain ⟨⟨p, hc⟩, _⟩ := enroll_authorized h
  have hlook : ∀ x v, pinned w c.unsigned.pins x = .ok v → v = w.live x := by
    intro x v hx
    unfold pinned at hx
    split at hx
    · simp only [Except.ok.injEq] at hx; exact hx.symm
    · simp at hx
  obtain ⟨r, cell, hr, hl, hi⟩ := chain_rooted (deployed_audit_rooted program name nonce allowance founders hw)
    hlook (fun _ _ hd => (bytes_of_digestOf hd).symm) hc
  exact ⟨p, r, cell, hr, hl, hi, hc⟩

end Nanodregg.Kernel.Receive
