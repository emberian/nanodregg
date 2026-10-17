/-
# Lang.Call — a method's calls as KERNEL's `Body` (LANG-23)

A method returns `rec {calls : callsTy, state : S}` (`Lang.resultTy`). `callsOf` reads the calls
half of the extracted data into the kernel's `List (Body D)`: the slots in label order, `none`
skipped; a bytes field that names a cell must decode as a digest, or the run is refused by name,
`program "calls: cI FIELD: not a digest"`. Every Body it returns is of a kind an object may
exercise (`Lang.Proofs.Call.callsOf_callable`), so KERNEL's `notCallable` is unreachable from
`Lang.program`; KERNEL still asserts it where calls enter (law 4).

`callData` is the other direction, over `Body`'s every constructor (a new kernel constructor does
not build here until it is classified): the data a method returns for that call, `none` for a
kind an object may not exercise or for a grant with more than `rightsMax` rights. `Lang.Proofs.Call`:
the round trip over data (`bodyOf_callData`, `callData_bodyOf`), and `callData_conforms`: the call
data of a callable Body within the language's bounds (`callFits`) is a value of `callTy`, so a
method can return it.

The encoding is not canonical, by design: an option row skips `none` wherever it sits, in the
calls row and in a grant's rights alike, so a method may leave any slot empty.
-/
import Kernel.Receive.Call
import Lang.Package
import Lang.Data

namespace Nanodregg.Lang

open Nanodregg.Kernel.Receive

variable {D : Type}

/-! ## Body → data -/

def optData {α : Type} (f : α → Data) : Option α → Data
  | none => .inj "none" (.record [])
  | some a => .inj "some" (f a)

/-- A row of `labels.length` option slots holding `xs` in order, the rest `none`; `none` when
`xs` is longer than the row. -/
def fillSlots {α : Type} (f : α → Data) : List Label → List α → Option (List (Label × Data))
  | [], [] => some []
  | [], _ :: _ => none
  | l :: ls, [] => (fillSlots f ls []).map ((l, optData f none) :: ·)
  | l :: ls, a :: as => (fillSlots f ls as).map ((l, optData f (some a)) :: ·)

def rightData : Right → Data
  | .enroll n => .inj "enroll" (.nat n)
  | .invoke m => .inj "invoke" (.nat m)
  | .mutate => .inj "mutate" (.record [])
  | .observe => .inj "observe" (.record [])

section
variable (bytesOf : D → ByteArray)

def digestData (d : D) : Data := .bytes (bytesOf d)

def acctRefData : AcctRef D → Data
  | .of owner asset => .inj "of" (.record [("asset", digestData bytesOf asset), ("owner", digestData bytesOf owner)])
  | .well asset => .inj "well" (digestData bytesOf asset)

/-- The data a method returns to make call `b`, at `callTy`; `none` when an object may not make it
(`Body.callable` is false) or a grant carries more than `rightsMax` rights. -/
def callData : Body D → Option Data
  | .account asset owner =>
      some (.inj "account" (.record [("asset", digestData bytesOf asset), ("owner", digestData bytesOf owner)]))
  | .credit well acct amount via =>
      some (.inj "credit" (.record [("acct", acctRefData bytesOf acct), ("amount", .nat amount),
        ("via", optData (digestData bytesOf) via), ("well", digestData bytesOf well)]))
  | .grant target grantee rights parent =>
      (fillSlots rightData rightLabels rights).map fun rs =>
        .inj "grant" (.record [("grantee", digestData bytesOf grantee),
          ("parent", optData (digestData bytesOf) parent), ("rights", .record rs),
          ("target", digestData bytesOf target)])
  | .invoke obj method args budget via =>
      some (.inj "invoke" (.record [("args", .bytes args), ("budget", .nat budget), ("method", .nat method),
        ("obj", digestData bytesOf obj), ("via", optData (digestData bytesOf) via)]))
  | .transfer src dst amount via once =>
      some (.inj "transfer" (.record [("amount", .nat amount), ("dst", acctRefData bytesOf dst),
        ("once", optData Data.bytes once), ("src", acctRefData bytesOf src),
        ("via", optData (digestData bytesOf) via)]))
  | .enroll .. | .rotate .. | .install .. | .create .. | .write .. | .law .. | .revoke .. | .issue .. =>
      none

end

/-- The Body's literal fields are values of the language (naturals below `natLimit`, byte
strings within `bytesMax`); its digests are bounded by the digest codec (`callData_conforms`). -/
def rightFits : Right → Bool
  | .enroll n | .invoke n => decide (n < Bounds.natLimit)
  | .mutate | .observe => true

def callFits : Body D → Bool
  | .credit _ _ amount _ => decide (amount < Bounds.natLimit)
  | .grant _ _ rights _ => rights.all rightFits
  | .invoke _ method args budget _ =>
      decide (method < Bounds.natLimit) && decide (budget < Bounds.natLimit) && decide (args.size ≤ Bounds.bytesMax)
  | .transfer _ _ amount _ once =>
      decide (amount < Bounds.natLimit) && once.all fun k => decide (k.size ≤ Bounds.bytesMax)
  | _ => true

/-! ## data → Body -/

section
variable (digestOf : ByteArray → Option D)

def natOf (f : String) : Data → Except String Nat
  | .nat n => .ok n
  | _ => .error s!"{f}: not a natural"

def bytesAt (f : String) : Data → Except String ByteArray
  | .bytes b => .ok b
  | _ => .error s!"{f}: not bytes"

def digestAt (f : String) : Data → Except String D
  | .bytes b =>
    match digestOf b with
    | some d => .ok d
    | none => .error s!"{f}: not a digest"
  | _ => .error s!"{f}: not bytes"

def optOf {α : Type} (g : Data → Except String α) (f : String) : Data → Except String (Option α)
  | .inj "none" (.record []) => .ok none
  | .inj "some" d => (g d).map some
  | _ => .error s!"{f}: not an option"

def acctRefOf (f : String) : Data → Except String (AcctRef D)
  | .inj "of" (.record [("asset", a), ("owner", o)]) => do
      pure (.of (← digestAt digestOf s!"{f}.owner" o) (← digestAt digestOf s!"{f}.asset" a))
  | .inj "well" a => (digestAt digestOf s!"{f}.well" a).map .well
  | _ => .error s!"{f}: not an account"

def rightOf : Data → Except String Right
  | .inj "enroll" (.nat n) => .ok (.enroll n)
  | .inj "invoke" (.nat m) => .ok (.invoke m)
  | .inj "mutate" (.record []) => .ok .mutate
  | .inj "observe" (.record []) => .ok .observe
  | _ => .error "rights: not a right"

/-- The rights in an option row, in slot order, `none` skipped. -/
def rightsOf : List (Label × Data) → Except String (List Right)
  | [] => .ok []
  | (_, o) :: fs => do
      let r ← optOf rightOf "rights" o
      let rs ← rightsOf fs
      pure (r.toList ++ rs)

/-- The Body that call data at `callTy` asks for. -/
def bodyOf : Data → Except String (Body D)
  | .inj "account" (.record [("asset", a), ("owner", o)]) => do
      pure (.account (← digestAt digestOf "asset" a) (← digestAt digestOf "owner" o))
  | .inj "credit" (.record [("acct", ac), ("amount", n), ("via", v), ("well", w)]) => do
      pure (.credit (← digestAt digestOf "well" w) (← acctRefOf digestOf "acct" ac) (← natOf "amount" n)
        (← optOf (digestAt digestOf "via") "via" v))
  | .inj "grant" (.record [("grantee", ge), ("parent", pa), ("rights", .record rs), ("target", t)]) => do
      if rs.length ≤ rightsMax then
        pure (.grant (← digestAt digestOf "target" t) (← digestAt digestOf "grantee" ge)
          (← rightsOf rs) (← optOf (digestAt digestOf "parent") "parent" pa))
      else throw "rights: too many"
  | .inj "invoke" (.record [("args", a), ("budget", b), ("method", m), ("obj", o), ("via", v)]) => do
      pure (.invoke (← digestAt digestOf "obj" o) (← natOf "method" m) (← bytesAt "args" a)
        (← natOf "budget" b) (← optOf (digestAt digestOf "via") "via" v))
  | .inj "transfer" (.record [("amount", n), ("dst", d), ("once", k), ("src", s), ("via", v)]) => do
      pure (.transfer (← acctRefOf digestOf "src" s) (← acctRefOf digestOf "dst" d) (← natOf "amount" n)
        (← optOf (digestAt digestOf "via") "via" v) (← optOf (bytesAt "once") "once" k))
  | _ => .error "not a call"

/-- The calls in the calls row a method returned, in slot order, `none` skipped; a slot that does
not read as a Body refuses the run by name (`program "calls: cI REASON"`). -/
def callsOf : Data → Except (Refusal D) (List (Body D))
  | .record fs => go fs
  | _ => .error (.program "calls: not a record")
where
  go : List (Label × Data) → Except (Refusal D) (List (Body D))
    | [] => .ok []
    | (ℓ, o) :: fs =>
      match o with
      | .inj "none" (.record []) => go fs
      | .inj "some" d =>
        match bodyOf digestOf d with
        | .ok b => (go fs).map (b :: ·)
        | .error e => .error (.program s!"calls: {ℓ} {e}")
      | _ => .error (.program s!"calls: {ℓ}: not an option")

end

end Nanodregg.Lang
