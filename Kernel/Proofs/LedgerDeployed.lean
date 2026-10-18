/-
# Kernel.Proofs.LedgerDeployed — the ledger theorems with their premises discharged

`Kernel.Proofs.Ledger.account_keyed` assumes a lawful `Env` (KERNEL-37). The deployed `Env` is
lawful at 32 (`Receive.deployed_lawful`), so under the deployed `Ctx` two account ids are equal
only for one (owner, denomination), or the two account inputs collide (tooth:
`deployed_account_keyed_sep`).
-/
import Kernel.Proofs.Ledger
import Codec.Proofs.Deployed
import Kernel.Proofs.RootedDeployed

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Deployed

/-- **Deployed: one account per (owner, denomination)**, up to a collision of the two account
inputs. -/
theorem deployed_account_keyed (program : Program Digest) {a s b t : Digest}
    (h : accountId (ctx program) a s = accountId (ctx program) b t) :
    (a, s) = (b, t) ∨ CollidesAmong (ctx program).env.hash [accountPre (ctx program) a s, accountPre (ctx program) b t] :=
  account_keyed deployed_lawful h

/-- **Tooth, deployed**: where the deployed hash separates the two account inputs, one account id is
one (owner, denomination). -/
theorem deployed_account_keyed_sep (program : Program Digest) {a s b t : Digest}
    (hs : Separates (ctx program).env.hash [accountPre (ctx program) a s, accountPre (ctx program) b t])
    (h : accountId (ctx program) a s = accountId (ctx program) b t) : (a, s) = (b, t) :=
  hs.elim (deployed_account_keyed program h)

end Nanodregg.Kernel.Receive
