/-
# Kernel.Receive.Ledger — the value receivers: issue, account, transfer (LEDGER-3)

Value itself is the kernel's (`Kernel.Value`, `World.checkValue`): whatever these receivers
derive, `World.admit` refuses a turn that moves a balance sum (`notConserved`), takes a cell
below minus its floor (`belowFloor`), or sets a floor outside a denomination's birth. These
receivers decide only AUTHORITY: who may bear a denomination and its cap (anyone, for a fresh
one), who may hold (anyone, an account of their own), and who may move value out of an account
(its owner, or a grantee of `mutate` through a chain that reaches it). There is no solvency
check here: `belowFloor` is the one name for an overdraft, as `stale` is for a stale read.

A denomination is the bytes of its WELL's id. The well is an ordinary account whose floor is the
cap; issuing is a transfer out of it and burning a transfer into it, so value is zero-sum per
denomination from its birth (`Kernel.Proofs.Value.admit_value`).
-/
import Kernel.Receive.Authority

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- An account: a value cell (`Kernel.Value`'s keys) with its owner at `slotOwner`. -/
def kindAccount : Nat := 6

/-- The domain of a transfer's once-only nullifier. -/
def domOnce : String := "nanodregg/kernel/once/v1"

/-- The nullifier a `once` key spends: namespaced by the source account, so a signer spends
only keys in the namespace of a source it has authority over. -/
def onceNullifier (X : Ctx D) (src : D) (key : ByteArray) : D :=
  X.env.hash domOnce (X.env.bytes src ++ key)

/-- An account born for `owner`, of denomination `denom`, balance 0, floor `floor`. -/
def accountCell (X : Ctx D) (owner : D) (denom : ByteArray) (floor : Nat) : Cell :=
  { kind := kindAccount, discipline := .value,
    slots := slotsOf [(slotOwner, X.env.bytes owner), (Value.denomKey, denom),
      (Value.balanceKey, Value.balanceBytes 0), (Value.floorKey, Value.floorBytes floor)] }

/-- A pinned live account and the value it holds. -/
def readAccount (look : Pinned D) (c : D) : Except (Refusal D) (Cell × Value) := do
  let cell ← readKind look c kindAccount
  match Value.ofCell cell with
  | some v => pure (cell, v)
  | none => .error (.malformedCell c Value.balanceKey)

/-- The largest cap: a well at minus its cap is still an `i64`. -/
def capMax : Nat := 2 ^ 63

/-- `issue cap`: the well, its id the turn's first born id, its denomination that id's bytes. -/
def issue (X : Ctx D) (c : Call D) (cap : Nat) : Except (Refusal D) (Turn D) := do
  let well := cellIdOf X.env (txIdOf X c) 0
  req (decide (cap ≤ capMax)) (.overflow well)
  sealTurn X c [accountCell X c.unsigned.member (X.env.bytes well) cap] [] []

/-- `account asset`: an empty account of the asset's denomination. It does not read the well, so
opening an account never pins the hot cell. -/
def account (X : Ctx D) (c : Call D) (asset : D) : Except (Refusal D) (Turn D) :=
  sealTurn X c [accountCell X c.unsigned.member (X.env.bytes asset) 0] [] []

/-- The write setting an account's balance. -/
def setBalance (b : Int) : Act := .write [.set Value.balanceKey (Value.balanceBytes b)]

/-- `transfer src dst amount via once`: both accounts pinned, live and of one denomination; the
signer has `src`'s owner's authority; both post balances are `i64`s. Two effects, and the once
key's nullifier. -/
def transfer (X : Ctx D) (look : Pinned D) (c : Call D) (src dst : D) (amount : Nat)
    (via : Option D) (once : Option ByteArray) : Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  let (scell, sv) ← readAccount look src
  let (_, dv) ← readAccount look dst
  let _ ← ownerAuthority X look u src scell .mutate via
  req (decide (src ≠ dst)) .sameAccount
  req (decide (0 < amount)) .zeroAmount
  req (decide (dv.denom = sv.denom)) (.assetMismatch dst)
  let sb := sv.balance - amount
  let db := dv.balance + amount
  req (Value.fits sb) (.overflow src)
  req (Value.fits db) (.overflow dst)
  sealTurn X c [] [(src, setBalance sb), (dst, setBalance db)] (once.map (onceNullifier X src)).toList

/-- The write setting an account's floor. -/
def setFloor (f : Nat) : Act := .write [.set Value.floorKey (Value.floorBytes f)]

/-- `credit well acct amount via` (LEDGER-4): a credit line is a floor transfer out of the well.
Extending credit IS issuing (minidregg FLOORS-LOG: setFloor's verb was mintAsset), so it is the
issuer's: the well's owner. The kernel conserves the denomination's floor sum, so a credit line
can only be carved from the well's unissued headroom: past it the well goes below its own floor,
`belowFloor`. Past the well's whole floor (a Nat cannot go negative), `overflow`. -/
def credit (X : Ctx D) (look : Pinned D) (c : Call D) (well acct : D) (amount : Nat)
    (via : Option D) : Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  let (wcell, wv) ← readAccount look well
  let (_, av) ← readAccount look acct
  let _ ← ownerAuthority X look u well wcell .mutate via
  req (decide (wv.denom = X.env.bytes well)) (.notWell well)
  req (decide (well ≠ acct)) .sameAccount
  req (decide (0 < amount)) .zeroAmount
  req (decide (av.denom = wv.denom)) (.assetMismatch acct)
  req (decide (amount ≤ wv.floor)) (.overflow well)
  req (decide (av.floor + amount ≤ capMax)) (.overflow acct)
  sealTurn X c [] [(well, setFloor (wv.floor - amount)), (acct, setFloor (av.floor + amount))] []

end Nanodregg.Kernel.Receive
