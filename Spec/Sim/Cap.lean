/-
# Spec.Sim.Cap — the capless kernel and the grant-cap runs (B2's grant cap, `Spec.Proofs.Cap`)

The trivial system `capless`: the kernel whose `transfer` and `credit` receivers do not spend the
grant's ledger (`Receive.transfer`/`Receive.credit` without their `spendVia`). The runs: from
`wGenesis`, the founder issues a well, opens its own account, grants itself `transfer 10` (or
`credit 10`) on the well, and moves 10 through the grant twice. Tooling (closure C9): what is
computed of these is stated in `Spec.Proofs.Cap`.
-/
import Spec.Sim.Run

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-- `Receive.transfer` without its `spendVia`: the signer's authority over the source is checked
through `via`'s chain for `transfer`, but the grant's ledger is never spent. -/
def caplessTransfer (X : Ctx Digest) (look : Pinned Digest) (a : At Digest) (srcR dstR : AcctRef Digest)
    (amount : Nat) (via : Option Digest) (once : Option ByteArray) : Except (Refusal Digest) (Draft Digest) := do
  let (src, scell, sv) ← readRef X look srcR
  let (dst, _, dv) ← readRef X look dstR
  let _ ← ownerAuthority X look a.actor src scell (.transfer 0) via
  req (decide (src ≠ dst)) .sameAccount
  req (decide (0 < amount)) .zeroAmount
  req (decide (dv.denom = sv.denom)) (.assetMismatch dst)
  let sb := sv.balance - amount
  let db := dv.balance + amount
  req (Value.fits sb) (.overflow src)
  req (Value.fits db) (.overflow dst)
  pure ⟨[], [(src, setBalance sb), (dst, setBalance db)], (once.map (onceNullifier X src)).toList, []⟩

/-- `Receive.credit` without its `spendVia`: the issuer's authority over the well is checked
through `via`'s chain for `credit`, but the grant's ledger is never spent. -/
def caplessCredit (X : Ctx Digest) (look : Pinned Digest) (a : At Digest) (well : Digest)
    (acctR : AcctRef Digest) (amount : Nat) (via : Option Digest) : Except (Refusal Digest) (Draft Digest) := do
  let (wcell, wv) ← readAccount look well
  let (acct, _, av) ← readRef X look acctR
  let _ ← ownerAuthority X look a.actor well wcell (.credit 0) via
  req (decide (wv.denom = X.env.bytes well)) (.notWell well)
  req (decide (well ≠ acct)) .sameAccount
  req (decide (0 < amount)) .zeroAmount
  req (decide (av.denom = wv.denom)) (.assetMismatch acct)
  req (decide (amount ≤ wv.floor)) (.overflow well)
  req (decide (av.floor + amount ≤ capMax)) (.overflow acct)
  pure ⟨[], [(well, setFloor (wv.floor - amount)), (acct, setFloor (av.floor + amount))], [], []⟩

/-- A signed call whose Body's Draft is `dr`, sealed as `receive` seals a call of no tree. -/
def caplessSeal (w : World Digest) (c : Call Digest) (dr : Pinned Digest → Except (Refusal Digest) (Draft Digest)) :
    Except (Refusal Digest) (Turn Digest) := do
  req (c.unsigned.world = w.origin) .wrongWorld
  let look := pinned Xd.env w c.unsigned.pins
  checkSignature Xd c
  checkKey look c.unsigned
  let d ← dr look
  sealTurn Xd c d.creates d.effects d.nullifiers

/-- The kernel's receivers, except that a signed `transfer` is `caplessTransfer` and a signed
`credit` is `caplessCredit`. -/
def caplessReceive (w : World Digest) (c : Call Digest) : Except (Refusal Digest) (Turn Digest) :=
  match c.unsigned.body with
  | .transfer src dst amount via once =>
      caplessSeal w c fun look => caplessTransfer Xd look ⟨c.unsigned.member, 0⟩ src dst amount via once
  | .credit well acct amount via =>
      caplessSeal w c fun look => caplessCredit Xd look ⟨c.unsigned.member, 0⟩ well acct amount via
  | _ => receive Xd w c

/-- **The capless kernel**: a transfer or a credit line through a grant never spends the grant's cap. -/
def capless (d : ByteArray → ByteArray) : System Digest := { deployed d with receive := caplessReceive }

/-- The founder grants itself `transfer 10` on its well. -/
def gGrant : Call Digest := fCall vW2 [] (.grant vWell wMember [.transfer 10] none)
def gId : Digest := cellIdOf Xd.env (txIdOf Xd gGrant) 0
def gW3 : World Digest := (staged vW2 gGrant).1

/-- Issue, account, grant: the World the two moves start from. -/
def gLog : List (Step Digest) :=
  (staged wGenesis vIssue).2 ++ (staged vW1 vAccount).2 ++ (staged vW2 gGrant).2

/-- The founder moves 10 out of the well into its account through the grant. -/
def gMove (w : World Digest) : Call Digest :=
  fCall w [vWell, vAcct, gId] (.transfer (.well vWell) (.of wMember vWell) 10 (some gId) none)

/-- The World the capless kernel reaches on a call (the World unchanged if it refuses). -/
def caplessStaged (w : World Digest) (c : Call Digest) : World Digest :=
  match caplessReceive w c with
  | .ok t => match World.admit Xd.env w t with
    | .ok w' => w'
    | .error _ => w
  | .error _ => w

def gMove1 : Call Digest := gMove gW3
def gMove2 : Call Digest := gMove (caplessStaged gW3 gMove1)

/-- The founder grants itself `credit 10` on its well, and extends 10 of credit through it twice. -/
def cGrant : Call Digest := fCall vW2 [] (.grant vWell wMember [.credit 10] none)
def cId : Digest := cellIdOf Xd.env (txIdOf Xd cGrant) 0
def cW3 : World Digest := (staged vW2 cGrant).1

def cLog : List (Step Digest) :=
  (staged wGenesis vIssue).2 ++ (staged vW1 vAccount).2 ++ (staged vW2 cGrant).2

def cLine (w : World Digest) : Call Digest :=
  fCall w [vWell, vAcct, cId] (.credit vWell (.of wMember vWell) 10 (some cId))

def cLine1 : Call Digest := cLine cW3
def cLine2 : Call Digest := cLine (caplessStaged cW3 cLine1)

/-- A computation's value passed on, or `false` (the run fact's one shape of step, so a hypothesis
about it is destructured by `okThen_eq`, never by reducing a match at the deployed `Ctx`). -/
def okThen {ε α : Type} (r : Except ε α) (k : α → Bool) : Bool :=
  match r with
  | .ok a => k a
  | .error _ => false

def someThen {α : Type} (r : Option α) (k : α → Bool) : Bool :=
  match r with
  | some a => k a
  | none => false

end Nanodregg.Spec
