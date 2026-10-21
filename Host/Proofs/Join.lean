/-
# Host.Proofs.Join — a carried join discharges trust at its invitation's origin

The signature supplies the independent origin pin. The first writing effect is reached only
after import under that pin, the signed nonce, the export head check and the budget check.
-/
import Host.Proofs.Trusted
import Host.Proofs.Cli

namespace Nanodregg.Host.Cli

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Host.Deployed

/-- A carried join that reaches genesis is trusted at the origin accepted from its invitation. -/
theorem join_carried_trusted (inviteHex keyHex path : String)
    (inR : Except (StoreFault (Record.Fault (Reject D))) ByteArray) (keyR : Option Digest)
    (k : Digest) (w : World D)
    {inv trusted : ByteArray} {i : Protocol.Invite.Invitation D} {accepted o fromO chain : D}
    {name nonce : ByteArray} {height : Nat}
    (hi : Protocol.Text.ofHex inviteHex = some inv)
    (hk : Protocol.Text.ofHex keyHex = some trusted)
    (ha : Protocol.Invite.acceptStart X trusted inv = .ok (i, accepted))
    (hs : i.start = .carried o name nonce fromO height chain)
    (hw : joinWith (m := Except (Option (Digest × World D)))
        { nonce := pure (.ok ByteArray.empty), readIn := pure inR, reopen := fun _ => throw none,
          key := pure keyR, genesis := fun k₀ w₀ => throw (some (k₀, w₀)),
          refuse := fun _ _ => pure 1, report := fun _ => pure () } inviteHex keyHex (some path) =
        .error (some (k, w))) : CheckpointTrusted accepted w := by
  obtain ⟨bytes, r, _, himp, _, _, _, hb, _⟩ :=
    (join_carried_iff inviteHex keyHex path inR keyR k w hi hk ha hs).mp hw
  have ho := Protocol.Invite.acceptStart_carried_origin ha hs
  rw [ho]
  exact import_trusted_pinned himp hb

end Nanodregg.Host.Cli
