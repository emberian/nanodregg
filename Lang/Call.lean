/-
# Lang.Call — a method's calls as KERNEL's `Body` (LANG-23, LANG-77)

A method returns `rec {calls : callsTy ks, edits, state : S}` (`Lang.resultTy`). `callsOf ks` reads
the calls half of the extracted data into the kernel's `List (Body D)`, slot by slot WITH each
slot's declared type `ks[i]`: `none` skipped; a `digest` field must be a digest of the World, or
the run is refused by name, `program "calls: cI FIELD: not a digest"`; an `invoke`'s `args` is a
VALUE of the slot's declared argument type (`slotInvokeArg`), encoded here with the one data codec
(`Wire.encodeData`, the codec the callee's `runSetupWith` inverts at its own argument type), so a
method composes a nested call from values it computed (LANG-77; before it, `args` was bytes the
method had to hold). Every Body it returns is of a kind an object may exercise
(`Lang.Proofs.Call.callsOf_callable`), so KERNEL's `notCallable` is unreachable from
`Lang.program`; KERNEL still asserts it where calls enter (law 4). An `install` slot (LANG-86)
carries the package bytes a method computed: the kernel installs them as it would a member's. On a checked run the encoder
never refuses: the extracted datum conforms to the slot's type and the type is one the wire carries
(`callSlotOk`), so `Lang.Proofs.CallLive.callsOf_live` keeps the digest refusal as the only one.

`callData` is the other direction, over `Body`'s every constructor (a new kernel constructor does
not build here until it is classified): the data a method returns for that call, `none` for a
kind an object may not exercise, for a grant with more than `rightsMax` rights, or for an invoke
whose `args` are not the bytes of a value of the slot's argument type. `Lang.Proofs.Call`:
the round trip over data (`bodyOf_callData`, `callData_bodyOf`), and `callData_conforms`: the call
data of a callable Body within the language's bounds (`callFits`) is a value of `callTy`, so a
method can return it.

The encoding is not canonical, by design: an option row skips `none` wherever it sits, in the
calls row and in a grant's rights alike, so a method may leave any slot empty.
-/
import Kernel.Receive.Call
import Lang.Package
import Lang.Data
import Lang.Wire.Data

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
  | .credit n => .inj "credit" (.nat n)
  | .transfer n => .inj "transfer" (.nat n)
  | .enroll n => .inj "enroll" (.nat n)
  | .invoke m => .inj "invoke" (.nat m)
  | .mutate => .inj "mutate" (.record [])
  | .observe => .inj "observe" (.record [])

section
variable (bytesOf : D → ByteArray)

def digestData (d : D) : Data := .digest (bytesOf d)

def acctRefData : AcctRef D → Data
  | .of owner asset => .inj "of" (.record [("asset", digestData bytesOf asset), ("owner", digestData bytesOf owner)])
  | .well asset => .inj "well" (digestData bytesOf asset)

/-- An invoke's `args` bytes read back as a value of the slot's argument type `A`; `none` when the
slot has no invoke arm or the bytes are not a value of `A`. -/
def argsData (A : Option Ty) (args : ByteArray) : Option Data :=
  A.bind fun A => (Wire.decodeData A args).toOption

/-- The data a method returns to make call `b` in a slot whose invoke arm (if any) is at argument
type `A`, at that slot's call type; `none` when an object may not make it (`Body.callable` is
false), a grant carries more than `rightsMax` rights, or an invoke's `args` are not a value of `A`. -/
def callData (A : Option Ty) : Body D → Option Data
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
      (argsData A args).map fun a =>
        .inj "invoke" (.record [("args", a), ("budget", .nat budget), ("method", .nat method),
          ("obj", digestData bytesOf obj), ("via", optData (digestData bytesOf) via)])
  | .transfer src dst amount via once =>
      some (.inj "transfer" (.record [("amount", .nat amount), ("dst", acctRefData bytesOf dst),
        ("once", optData Data.bytes once), ("src", acctRefData bytesOf src),
        ("via", optData (digestData bytesOf) via)]))
  | .install pkg => some (.inj "install" (.record [("pkg", .bytes pkg)]))
  | .enroll .. | .rotate .. | .create .. | .write .. | .law .. | .revoke .. | .issue .. =>
      none

end

/-- The Body's literal fields are values of the language (naturals below `natLimit`, byte
strings within `bytesMax`); its digests are bounded by the digest codec (`callData_conforms`). An
invoke's `args` are bounded by their type: `callData` reads them back or has no data. -/
def rightFits : Right → Bool
  | .enroll n | .invoke n | .transfer n | .credit n => decide (n < Bounds.natLimit)
  | .mutate | .observe => true

def callFits : Body D → Bool
  | .credit _ _ amount _ => decide (amount < Bounds.natLimit)
  | .install pkg => decide (pkg.size ≤ Bounds.bytesMax)
  | .grant _ _ rights _ => rights.all rightFits
  | .invoke _ method _ budget _ => decide (method < Bounds.natLimit) && decide (budget < Bounds.natLimit)
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
  | .digest b =>
    match digestOf b with
    | some d => .ok d
    | none => .error s!"{f}: not a digest"
  | _ => .error s!"{f}: not a digest value"

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
  | .inj "credit" (.nat n) => .ok (.credit n)
  | .inj "transfer" (.nat n) => .ok (.transfer n)
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

/-- An invoke's `args` value `a`, as the bytes the callee decodes: `Wire.encodeData` at the slot's
argument type `A` (LANG-77). Refused by name when the slot has no invoke arm or the value has no
bytes at `A`; neither is reachable from a checked run (`Lang.Proofs.CallLive.callsOf_live`). -/
def argsBytes (A : Option Ty) (f : String) (a : Data) : Except String ByteArray :=
  match A with
  | none => .error s!"{f}: no invoke arm"
  | some A =>
    match Wire.encodeData A a with
    | some b => .ok b
    | none => .error s!"{f}: no bytes at the slot's type"

/-- The Body that call data at a slot's call type asks for, the slot's invoke arm (if any) at
argument type `A`. -/
def bodyOf (A : Option Ty) : Data → Except String (Body D)
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
  | .inj "install" (.record [("pkg", .bytes pkg)]) => pure (.install pkg)
  | .inj "invoke" (.record [("args", a), ("budget", b), ("method", m), ("obj", o), ("via", v)]) => do
      pure (.invoke (← digestAt digestOf "obj" o) (← natOf "method" m) (← argsBytes A "args" a)
        (← natOf "budget" b) (← optOf (digestAt digestOf "via") "via" v))
  | .inj "transfer" (.record [("amount", n), ("dst", d), ("once", k), ("src", s), ("via", v)]) => do
      pure (.transfer (← acctRefOf digestOf "src" s) (← acctRefOf digestOf "dst" d) (← natOf "amount" n)
        (← optOf (digestAt digestOf "via") "via" v) (← optOf (bytesAt "once") "once" k))
  | _ => .error "not a call"

/-- The calls in the calls row a method returned, read against its declared slot types `ks`, in
slot order, `none` skipped; a slot that does not read as a Body refuses the run by name
(`program "calls: cI REASON"`). A row with other than `ks.length` slots is `calls: slots`
(unreachable: the extracted result conforms to `callsTy ks`). -/
def callsOf (ks : List Ty) : Data → Except (Refusal D) (List (Body D))
  | .record fs => go ks fs
  | _ => .error (.program "calls: not a record")
where
  go : List Ty → List (Label × Data) → Except (Refusal D) (List (Body D))
    | [], [] => .ok []
    | k :: ks, (ℓ, o) :: fs =>
      match o with
      | .inj "none" (.record []) => go ks fs
      | .inj "some" d =>
        match bodyOf digestOf (slotInvokeArg k) d with
        | .ok b => (go ks fs).map (b :: ·)
        | .error e => .error (.program s!"calls: {ℓ} {e}")
      | _ => .error (.program s!"calls: {ℓ}: not an option")
    | _, _ => .error (.program "calls: slots")

end

/-! ## Grades at run (LANG-89): what a run's calls MOVE against the method's declared effect -/

/-- What the calls move: the sum of `amount` over every `transfer` and `credit`. -/
def movesOf : List (Body D) → Nat
  | [] => 0
  | .transfer _ _ amount _ _ :: bs => amount + movesOf bs
  | .credit _ _ amount _ :: bs => amount + movesOf bs
  | _ :: bs => movesOf bs

/-- A run's calls move at most the method's grade, or the run is refused by name `effectExceeded`
(the first token names it, law 7's `program` convention): O(`callsMax`), after `callsOf`, before any
call is derived. -/
def checkMoves (e : Effect) (calls : List (Body D)) : Except (Refusal D) Unit :=
  if movesOf calls ≤ e.moves then .ok ()
  else .error (.program s!"effectExceeded moves {movesOf calls} past {e.moves}")

end Nanodregg.Lang
