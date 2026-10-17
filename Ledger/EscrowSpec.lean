/-
# Ledger.EscrowSpec — the measures the escrow's theorems are stated with

What `Ledger.Proofs.Escrow` counts and reads, as functions: which method an act invokes
(`invoked`, `isPayout`, `payouts`), an escrow state and request with arbitrary values
(`stateOf`, `reqWith`), the call and state a method computes on the reference evaluator
(`callOfMethod`, `stateOfMethod`), and a chain of acts on one escrow with the calls its acts make
(`Act`, `stepsOf`, `callAt`, `spendCount`, `depositFirst`). Nothing here is deployed: the kernel
runs the package itself.
-/
import Ledger.Escrow
import Lang.Eval

namespace Nanodregg.Ledger.Escrow

open Nanodregg.Lang

/-- The method an act invokes, if it is an invoke. -/
def invoked (rq : Data) : Option Nat :=
  match rq.field "occasion" with
  | some (.inj "invoke" (.nat m)) => some m
  | _ => none

/-- An act is a payout: an invoke of `refund` or `release`. -/
def isPayout (rq : Data) : Bool := invoked rq == some refund || invoked rq == some release

def payouts (steps : List (Data × Data)) : Nat := (steps.filter fun s => isPayout s.1).length

/-- An escrow state with arbitrary terms, in phase `p`. -/
def stateOf (amount : Nat) (arbiter asset beneficiary depositor nonce : ByteArray) (p : Label) : Data :=
  .record [("amount", .nat amount), ("arbiter", .digest arbiter), ("asset", .digest asset),
    ("beneficiary", .digest beneficiary), ("depositor", .digest depositor), ("nonce", .bytes nonce),
    ("phase", .inj p (.record []))]

/-- A request signed by `agent` on object `self` for occasion `occ`. -/
def reqWith (agent self : ByteArray) (occ : Data) : Data :=
  .record [("agent", .digest agent), ("notBefore", .nat 0), ("occasion", occ),
    ("principal", .digest agent), ("self", .digest self), ("validUntil", .nat 0)]

def reqOf (agent self : ByteArray) (m : Nat) : Data := reqWith agent self (.inj "invoke" (.nat m))

/-- Method `ℓ` of the package body applied to the bound state, argument and request (`var 2`,
`var 1`, `var 0`), as `Lang.Program` applies it. -/
def methodAt (ℓ : Label) : Term :=
  match escrow.body with
  | .record fs => match Row.find? ℓ fs with
    | some t => .app (.app (.app t (.var 2)) (.var 1)) (.var 0)
    | none => .nat 0
  | _ => .nat 0

/-- Read one field of the transfer in slot `c0` of the calls row: `pick` runs on the transfer's
fields record (bound at `var 0`); an empty slot or another kind of call reads `nat 0`. -/
def slotField (ℓ : Label) (pick : Term) : Term :=
  .case (.get (.get (methodAt ℓ) "calls") "c0")
    [("none", .nat 0), ("some", .case (.var 0) [("transfer", pick)])]

/-- An account reference's owner, or `nat 0` for a well. -/
def ownerOf (f : Label) : Term :=
  .case (.get (.var 0) f) [("of", .get (.var 0) "owner"), ("well", .nat 0)]

def assetOf (f : Label) : Term :=
  .case (.get (.var 0) f) [("of", .get (.var 0) "asset"), ("well", .nat 0)]

/-- An option's payload, or `nat 0` for `none`. -/
def someOf (f : Label) : Term := .case (.get (.var 0) f) [("none", .nat 0), ("some", .var 0)]

def valueOf : Outcome → Option Val
  | .value v _ => some v
  | _ => none

/-- What the call in method `ℓ`'s slot is, field by field, over the reference evaluator:
`(src owner, src asset, dst owner, dst asset, amount, via, once)`. -/
def callOfMethod (ℓ : Label) (state arg rq : Data) : List (Option Val) :=
  let run (t : Term) := valueOf (eval [] 1000 (slotField ℓ t) [rq.toVal, arg.toVal, state.toVal])
  [run (ownerOf "src"), run (assetOf "src"), run (ownerOf "dst"), run (assetOf "dst"),
    run (.get (.var 0) "amount"), run (someOf "via"), run (someOf "once")]

/-- The state method `ℓ` writes, field by field, over the reference evaluator, in `stateTy`'s order. -/
def stateOfMethod (ℓ : Label) (state arg rq : Data) : List (Option Val) :=
  ["amount", "arbiter", "asset", "beneficiary", "depositor", "nonce", "phase"].map fun f =>
    valueOf (eval [] 1000 (.get (.get (methodAt ℓ) "state") f) [rq.toVal, arg.toVal, state.toVal])

/-- A call spends the payout key out of the escrow's own account `of self asset`. -/
def spendsB (self asset : ByteArray) : List (Option Val) → Bool
  | some (.digest s) :: some (.digest a) :: _ :: _ :: _ :: _ :: some (.bytes k) :: _ =>
      decide (s = self) && decide (a = asset) && decide (k = payoutKey)
  | _ => false

/-- One act on escrow `self`: its signer, its occasion, the grant a deposit names, and the phase it
leaves. The terms never change (`escrow_method_state`), so the chain's states differ by phase. -/
structure Act where
  agent : ByteArray
  occ : Data
  grant : ByteArray
  phase : Label

/-- A method's argument as the receiver decodes it at the method's argument type. -/
def argFor (m : Nat) (g : ByteArray) : Data := if m = deposit then .record [("grant", .digest g)] else .record []

section
variable (amount : Nat) (arb asset ben dep nk self : ByteArray)

def stepsOf (acts : List Act) : List (Data × Data) :=
  acts.map fun a => (reqWith a.agent self a.occ, stateOf amount arb asset ben dep nk a.phase)

/-- The call act `a` makes from phase `p`: method `escrow.methods[m]` for an invoke of `m` (how
KERNEL's invoke resolves it), none otherwise. -/
def callAt (p : Label) (a : Act) : List (Option Val) :=
  match invoked (reqWith a.agent self a.occ) with
  | some m => callOfMethod ((escrow.methods[m]?).getD "") (stateOf amount arb asset ben dep nk p) (argFor m a.grant)
      (reqWith a.agent self a.occ)
  | none => []

/-- How many acts of the chain from phase `p` make a call spending the payout key out of the
escrow's own account. -/
def spendCount : Label → List Act → Nat
  | _, [] => 0
  | p, a :: as => (if spendsB self asset (callAt amount arb asset ben dep nk self p a) then 1 else 0) +
      spendCount a.phase as
end

/-- Whether, along a chain of acts, the first that is a deposit or a payout is a deposit. -/
def depositFirst : List (Data × Data) → Bool
  | [] => true
  | (rq, _) :: rest =>
    if invoked rq = some deposit then true else if isPayout rq then false else depositFirst rest

/-- The package body's fields (no imports, no `ref`: what the receiver loads, unrelocated). -/
def bodyFields : List (Label × Term) :=
  match escrow.body with
  | .record fs => fs
  | _ => []

end Nanodregg.Ledger.Escrow
