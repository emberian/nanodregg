/-
# Kernel.Proofs.LedgerDeployed — the ledger theorems with their premises discharged

`Kernel.Proofs.Ledger.account_keyed` assumes a lawful `Env` (KERNEL-37). The deployed `Env` is
lawful at 32 (`Receive.deployed_lawful`), so under the deployed `Ctx` two account ids are equal
only for one (owner, denomination), or the account hash has a collision.
-/
import Kernel.Proofs.Ledger
import Codec.Proofs.Deployed
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Deployed

/-- **Deployed: one account per (owner, denomination)**, up to a collision of the account hash. -/
theorem deployed_account_keyed (program : Program Digest) {a s b t : Digest}
    (h : accountId (ctx program) a s = accountId (ctx program) b t) :
    (a, s) = (b, t) ∨ HashColl (ctx program).env domAccount :=
  account_keyed deployed_lawful h

end Nanodregg.Kernel.Receive
