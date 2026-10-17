/-
# Kernel.Proofs.LedgerDeployed — the ledger theorems with their premises discharged

`Kernel.Proofs.Ledger.account_keyed` assumes the digest's bytes are injective and all of one
size. The deployed digest is 32 bytes (`Digest.size_eq`) and its bytes injective
(`Codec.Proofs.Deployed.bytes_injective`), so under the deployed `Ctx` two account ids are equal
only for one (owner, denomination), or the account hash has a collision.
-/
import Kernel.Proofs.Ledger
import Codec.Proofs.Deployed

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Deployed

/-- **Deployed: one account per (owner, denomination)**, up to a collision of the account hash. -/
theorem deployed_account_keyed (program : Program Digest) {a s b t : Digest}
    (h : accountId (ctx program) a s = accountId (ctx program) b t) :
    (a, s) = (b, t) ∨ HashColl (ctx program).env domAccount :=
  account_keyed (fun _ _ hb => bytes_injective hb)
    (fun x y => by show x.bytes.size = y.bytes.size; rw [x.size_eq, y.size_eq]) h

end Nanodregg.Kernel.Receive
