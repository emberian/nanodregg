/-
# Ledger.EscrowSpec — the measures the escrow's theorems are stated with

What `Ledger.Proofs.Escrow` counts and reads, as functions: which method an act invokes
(`invoked`, `isPayout`, `payouts`), an escrow state and request with arbitrary values
(`stateOf`, `reqAt`, `reqWith`), what a method returns (`methodResult`: the method application
the receiver runs, `apply4 0 ℓ` under the closure `[escrow.body]`, extracted whole at the
methods' result type `resultOf`, as `Lang.runMeasured` extracts it), the order of acts
(`depositFirst`), and what a sequence of the receiver's runs pays out (`isPayoutCall`,
`payoutCalls`).
Nothing here is deployed: the kernel runs the package itself, and `Ledger.Proofs.EscrowRun`
proves that its run extracts `methodResult`.
-/
import Ledger.Escrow
import Lang.Eval
import Lang.Program

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

/-- A request on object `self` with every other field arbitrary (the shape of `Lang.reqData`). -/
def reqAt (agent notBefore occ principal : Data) (self : ByteArray) (validUntil : Data) : Data :=
  .record [("agent", agent), ("notBefore", notBefore), ("occasion", occ), ("principal", principal),
    ("self", .digest self), ("validUntil", validUntil)]

/-- A request signed by `agent` on object `self` for occasion `occ`. -/
def reqWith (agent self : ByteArray) (occ : Data) : Data :=
  reqAt (.digest agent) (.nat 0) occ (.digest agent) self (.nat 0)

/-- The type every method's result is extracted at: its one transfer slot, no row edits, the
state (each method's `resultTy` in its signature, `escrow_run_calls` reads it there). -/
def resultOf : Ty := resultTy stateTy [T] (editTy []) 0

/-- What method `ℓ` returns from `state`, argument `arg`, request `rq` and rows `rows`: the method
application `apply4 0 ℓ` the receiver runs (LANG-49: rows, state, argument, request at `var 3 … 0`),
under the closure `[escrow.body]`, extracted whole at `resultOf`; `none` on a fault. -/
def methodResult (ℓ : Label) (state arg rq rows : Data) : Option Data :=
  match eval [escrow.body] 1000 (apply4 0 ℓ) [rq.toVal, arg.toVal, state.toVal, rows.toVal] with
  | .value v _ =>
    match (Machine.mk [escrow.body]).extract resultOf 1000 v with
    | .ok (d, _) => some d
    | .error _ => none
  | .fault _ _ => none

/-- An option's data. -/
def optSome (d : Data) : Data := .inj "some" d
def optNone : Data := .inj "none" (.record [])

/-- The account reference `of {owner, asset}` as data (`acctRefTy`). -/
def ofD (owner asset : ByteArray) : Data := .inj "of" (.record [("asset", .digest asset), ("owner", .digest owner)])

/-- A transfer call as data, in `transfer`'s field order. -/
def transferD (src dst : Data) (amount : Nat) (via once : Data) : Data :=
  .inj "transfer" (.record [("amount", .nat amount), ("dst", dst), ("once", once), ("src", src), ("via", via)])

/-- A method result with `call` in its one slot, no edits, and new state `state`. -/
def resultD (call state : Data) : Data :=
  .record [("calls", .record [("c0", optSome call)]), ("edits", .record []), ("state", state)]

/-- A call is a payout: a transfer through no grant (`via = none`), which the kernel authorizes
only out of the calling object's own account. `refund` and `release` each return one; `deposit`
returns one through its grant, so none (`escrow_run_calls`). -/
def isPayoutCall {D : Type} : Kernel.Receive.Body D → Bool
  | .transfer _ _ _ none _ => true
  | _ => false

/-- How many payouts a sequence of runs returned: each run's calls, in order. -/
def payoutCalls {D : Type} (runs : List (List (Kernel.Receive.Body D))) : Nat :=
  (runs.map fun cs => (cs.filter isPayoutCall).length).sum

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
