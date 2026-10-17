/-
# Ledger.Escrow — the escrow package, generated in Lean (decisions/ledger.md LEDGER-6, LEDGER-10)

A depositor's `amount` of `asset` held by an escrow OBJECT `e` until the arbiter or a party
settles it: paid to the beneficiary (`release`) or back to the depositor (`refund`), once.

State `{amount : nat, arbiter, asset, beneficiary, depositor : digest, nonce : bytes, phase}`;
`phase` is a sum of empty records over `held | open | refunded | released`. `nonce` is the deposit's
once key (LEDGER-11: a digest has no bytes in the core, so `self` can no longer be the key). The terms are fixed at birth by the
creator (the object's owner, KERNEL's slot 1, who grants the parties `invoke`, KERNEL-25) and
carried unchanged by every method.

The funds sit in `accountId e asset` (LEDGER-6 (a)), named by reference: `of {owner = req.self,
asset}` (LEDGER-7, LANG-25). Anyone opens it, before the deposit, with a top-level
`account asset e`. Methods, in `pkgOf`'s sorted order (the `n` of `invoke` and `Right.invoke n`):

* 0 `deposit {grant}`: `open → held`, and ONE call: `transfer (of depositor asset) (of self
  asset) amount (via := some grant) (once := some nonce)`. `grant` is the depositor's grant to `e`
  of `mutate` on its own account (v0: the whole balance, LEDGER-6 (c)); the transfer is in the same
  tree as the phase change, so `held` is reached exactly when the funds moved.
* 1 `refund {}`: `held → refunded`, `transfer (of self asset) (of depositor asset) amount none
  (once := some "payout")`.
* 2 `release {}`: `held → released`, `transfer (of self asset) (of beneficiary asset) amount none
  (once := some "payout")`.

Both payouts spend ONE nullifier, `onceNullifier (accountId e asset) "payout"`, so the kernel pays
at most once in the escrow's life whichever way (`Kernel.Proofs.Ledger.transfer_once`); the law
`escrow` refuses by NAME before that (`Ledger.Proofs.Escrow`):

* birth and adoption: the phase is `open`, else `notOpen`;
* a write or a law change: `frozen` (KERNEL refuses both for a programmed object first);
* an invoke: from `released`/`refunded` `settled`; method 0 needs `open` (`notOpen`) and the
  depositor signing (`notParty`); 1 needs `held` (`notHeld`) and the beneficiary or the arbiter;
  2 needs `held` and the depositor or the arbiter; the new phase must be the method's target
  (`badPhase`); any other index `noMethod`.

The law sees `agent`, the signing member (`Req.agent`), so a party acting through the owner's grant
is checked by its own key: the law narrows KERNEL's authority, it does not replace it.
-/
import Lang.Std
import Lang.Wire.Data
import Kernel.Receive.Call

namespace Nanodregg.Ledger.Escrow

open Nanodregg.Lang
open Nanodregg.Lang.Std (At guard allOf anyOf notT refusedT okT natT)

/-! ## Types -/

/-- The phases, in canonical (label) order. -/
def phaseLabels : List Label := ["held", "open", "refunded", "released"]

def phaseTy : Ty := Std.stateTy phaseLabels

def stateTy : Ty :=
  .record [("amount", .nat), ("arbiter", .digest), ("asset", .digest), ("beneficiary", .digest),
    ("depositor", .digest), ("nonce", .bytes), ("phase", phaseTy)]

def unit : Ty := .record []

/-- `deposit`'s argument: the depositor's grant to the escrow object. -/
def depositArg : Ty := .record [("grant", .digest)]

/-- Every method's one call slot: a transfer, nothing else. -/
def T : Ty := callOf ["transfer"]

/-- The once key both payouts spend. -/
def payoutKey : ByteArray := "payout".toUTF8

/-! ## Method terms (under a method's binders: state `var 2`, argument `var 1`, request `var 0`) -/

def st (f : Label) : Term := .get (.var 2) f
def rq (f : Label) : Term := .get (.var 0) f

def someB (t : Term) : Term := .inj (optTy .bytes) "some" t

/-- An optional digest (a call's `via`). -/
def someD (t : Term) : Term := .inj (optTy .digest) "some" t
def noneD : Term := .inj (optTy .digest) "none" (.record [])

/-- The account of `owner` in the escrow's denomination. -/
def ofT (owner : Term) : Term := .inj acctRefTy "of" (.record [("asset", st "asset"), ("owner", owner)])

def transferT (src dst via once : Term) : Term :=
  .inj T "transfer" (.record [("amount", st "amount"), ("dst", dst), ("once", once), ("src", src), ("via", via)])

def phaseT (p : Label) : Term := .inj phaseTy p (.record [])

/-- The new state: every term carried, `phase := p`. -/
def keep (p : Label) : List (Label × Term) :=
  [("amount", st "amount"), ("arbiter", st "arbiter"), ("asset", st "asset"),
    ("beneficiary", st "beneficiary"), ("depositor", st "depositor"), ("nonce", st "nonce"),
    ("phase", phaseT p)]

def depositCall : Term :=
  transferT (ofT (st "depositor")) (ofT (rq "self")) (someD (.get (.var 1) "grant")) (someB (st "nonce"))

def payoutCall (to : Label) : Term :=
  transferT (ofT (rq "self")) (ofT (st to)) noneD (someB (.bytes payoutKey))

/-! ## The law -/

def isPh (t : Term) (p : Label) : Term := Std.isState phaseLabels t p

/-- The signing member is party `f` of the OLD state. -/
def agentIs (a : At) (f : Label) : Term := .prim .deq (a.reqF "agent") (a.oldF f)

def methodIs (a : At) (m : Nat) : Term := .prim .eq a.payload (natT m)

/-- Method `m`'s clause: from phase `src`, a party in `who`, to `dst`. -/
def methodClause (a : At) (src : Label) (srcWhy : String) (who : List Label) (dst : Label) : Term :=
  allOf [(isPh (a.oldF "phase") src, srcWhy), (anyOf (who.map (agentIs a)), "notParty"),
    (isPh (a.newF "phase") dst, "badPhase")]

def invokeC (a : At) : Term :=
  guard (notT (anyOf [isPh (a.oldF "phase") "refunded", isPh (a.oldF "phase") "released"])) "settled"
    (.ite (methodIs a 0) (methodClause a "open" "notOpen" ["depositor"] "held")
      (.ite (methodIs a 1) (methodClause a "held" "notHeld" ["beneficiary", "arbiter"] "refunded")
        (.ite (methodIs a 2) (methodClause a "held" "notHeld" ["depositor", "arbiter"] "released")
          (refusedT "noMethod"))))

/-- Birth and adoption: the state is, and stays, `open`. -/
def startC (a : At) : Term :=
  allOf [(isPh (a.oldF "phase") "open", "notOpen"), (isPh (a.newF "phase") "open", "notOpen")]

def frozenC (_ : At) : Term := refusedT "frozen"

def law : Term := Std.lawOf5 stateTy startC startC frozenC frozenC invokeC

/-! ## The package -/

def methods : List (Label × Ty × List Ty × Term) :=
  [("deposit", depositArg, [T], .lam stateTy (.lam depositArg (.lam reqTy
      (resultT (callsT [someCallT T depositCall]) (.record (keep "held")))))),
   ("refund", unit, [T], .lam stateTy (.lam unit (.lam reqTy
      (resultT (callsT [someCallT T (payoutCall "depositor")]) (.record (keep "refunded")))))),
   ("release", unit, [T], .lam stateTy (.lam unit (.lam reqTy
      (resultT (callsT [someCallT T (payoutCall "beneficiary")]) (.record (keep "released"))))))]

def escrow : Package := Std.pkgOf stateTy [("escrow", law)] methods

/-- The method indices `invoke` names. -/
def deposit : Nat := 0
def refund : Nat := 1
def release : Nat := 2

/-! ## Slots: what `create` seeds and what a reader decodes -/

def unitD : Data := .record []

/-- The terms an escrow is born with. -/
structure Terms where
  amount : Nat
  arbiter : ByteArray
  asset : ByteArray
  beneficiary : ByteArray
  depositor : ByteArray
  /-- the deposit's once key (LEDGER-11): the creator's, fresh per escrow funded from one account -/
  nonce : ByteArray

def stateD (t : Terms) (p : Label) : Data :=
  .record [("amount", .nat t.amount), ("arbiter", .digest t.arbiter), ("asset", .digest t.asset),
    ("beneficiary", .digest t.beneficiary), ("depositor", .digest t.depositor), ("nonce", .bytes t.nonce),
    ("phase", .inj p unitD)]

def labels : List Label := ["amount", "arbiter", "asset", "beneficiary", "depositor", "nonce", "phase"]
def fieldTys : List Ty := [.nat, .digest, .digest, .digest, .digest, .bytes, phaseTy]

/-- The seed of an `open` escrow on `t` (KERNEL's state slots from `stateBase`, in field order);
`none` past LANG's bounds. -/
def seed (t : Terms) : Option Kernel.Slots :=
  match stateD t "open" with
  | .record fs => (fs.zip fieldTys).zipIdx.mapM fun (((_, d), T), i) =>
      (Wire.encodeData T d).map fun b => (Kernel.Receive.stateBase + i, b)
  | _ => none

/-- `deposit`'s argument bytes for grant `g`. -/
def depositArgs (g : ByteArray) : Option ByteArray := Wire.encodeData depositArg (.record [("grant", .digest g)])

def noArgs : Option ByteArray := Wire.encodeData unit unitD

/-- The phase an escrow's slots hold. -/
def phaseOf (s : Kernel.Slots) : Option Label :=
  match s.get (Kernel.Receive.stateBase + 6) with
  | none => none
  | some b => match Wire.decodeData phaseTy b with
    | .ok (.inj l _) => some l
    | _ => none

end Nanodregg.Ledger.Escrow
