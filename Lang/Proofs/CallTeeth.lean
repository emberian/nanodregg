/-
# Lang.Proofs.CallTeeth — `callsOf` on concrete rows, and the round trip's premise is satisfiable

Over `D = ByteArray` with an 8-byte digest (the Sim's width): `none` slots are skipped wherever they
sit, a slot that names a cell by non-digest bytes refuses the run with the slot and field by name,
a grant with five rights has no call data, and `bodyOf_callData`'s premise holds for the identity
digest (`bodyOf_callData_bytes`), so the round trip is not vacuous. At install: an `invoke`-only
slot carrying an invoke checks; a slot arm with the right label at the wrong type, and an empty
sum, are refused `badMethod`; a transfer in an `invoke`-only slot is `illTyped`.
-/
import Lang.Proofs.Call

namespace Nanodregg.Lang.Teeth

open Nanodregg.Kernel.Receive

private def dig8 (b : ByteArray) : Option ByteArray := if b.size = 8 then some b else none

private def obj8 : ByteArray := ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩

private def invokeD (obj : ByteArray) : Data :=
  .inj "invoke" (.record [("args", .bytes .empty), ("budget", .nat 10), ("method", .nat 0),
    ("obj", .bytes obj), ("via", .inj "none" (.record []))])

private def callsIs (e : Except (Refusal ByteArray) (List (Body ByteArray))) (bs : List (Body ByteArray)) : Bool :=
  match e with
  | .ok bs' => decide (bs' = bs)
  | .error _ => false

private def refusedWith (e : Except (Refusal ByteArray) (List (Body ByteArray))) (why : String) : Bool :=
  match e with
  | .error (.program w) => w == why
  | _ => false

/-- An empty slot before a call is skipped: the call is the only Body. -/
theorem callsOf_skips_none :
    callsIs (callsOf dig8 (.record [("c0", .inj "none" (.record [])), ("c1", .inj "some" (invokeD obj8))]))
      [.invoke obj8 0 .empty 10 none] = true := by decide +kernel

/-- A call naming its object by three bytes is refused by slot and field. -/
theorem callsOf_not_digest :
    refusedWith (callsOf dig8 (.record [("c0", .inj "some" (invokeD ⟨#[120, 121, 122]⟩))]))
      "calls: c0 obj: not a digest" = true := by decide +kernel

/-- A slot that is not an option is refused by name. -/
theorem callsOf_not_option :
    refusedWith (callsOf dig8 (.record [("c0", .nat 3)])) "calls: c0: not an option" = true := by
  decide +kernel

/-- A grant carrying more rights than `rightsMax` has no call data. -/
theorem callData_five_rights :
    callData id (Body.grant obj8 obj8 [.observe, .mutate, .invoke 0, .invoke 1, .enroll 2] none) = none := by
  decide +kernel

/-- The same grant at four rights has call data. -/
theorem callData_four_rights :
    (callData id (Body.grant obj8 obj8 [.observe, .mutate, .invoke 0, .enroll 2] none)).isSome = true := by
  decide +kernel

/-- `bodyOf_callData` at the identity digest: its premise is satisfiable. -/
theorem bodyOf_callData_bytes {b : Body ByteArray} {d : Data} (h : callData id b = some d) :
    bodyOf some d = .ok b :=
  bodyOf_callData (fun _ => rfl) h

/-! ## Call slots at install: the slot's type is checked against `callArms`, the body against the slot -/

private def S1 : Ty := .record [("n", .nat)]

/-- A one-method package whose method has call slots `ks` and body `go`. -/
private def slotPkg (ks : List Ty) (go : Term) : Package :=
  { imports := [], state := S1, iface := .record [("go", methodTy S1 (.record []) ks)],
    body := .record [("go", go)], methods := ["go"], laws := [] }

private def invokeOnly : Ty := callOf ["invoke"]

private def isOkC : Except CheckError Unit → Bool
  | .ok () => true
  | .error _ => false

private def isBadMethod : Except CheckError Unit → Bool
  | .error (.badMethod "go") => true
  | _ => false

private def isIllTyped : Except CheckError Unit → Bool
  | .error (.illTyped _) => true
  | _ => false

/-- `λ s a r. {calls = {c0 = slot}, state = s}` -/
private def goWith (slot : Term) : Term :=
  .lam S1 (.lam (.record []) (.lam reqTy (resultT (callsT [slot]) (.var 2))))

/-- An `invoke` call of call type `T`. -/
private def anInvoke (T : Ty) : Term :=
  .inj T "invoke" (.record [("args", .bytes .empty), ("budget", .nat 1), ("method", .nat 0),
    ("obj", .bytes .empty), ("via", .inj (optTy .bytes) "none" (.record []))])

/-- The control: an invoke-only slot carrying an invoke installs. -/
theorem slot_invoke_checks : isOkC ((slotPkg [invokeOnly] (goWith (someCallT invokeOnly (anInvoke invokeOnly)))).checkWith []) = true := by
  decide +kernel

/-- A slot whose `invoke` arm has the right label but `budget : bytes` is not a call slot: the
method's type is refused `badMethod`. -/
theorem slot_wrong_arm_type :
    let bad : Ty := .sum [("invoke", .record [("args", .bytes), ("budget", .bytes), ("method", .nat),
      ("obj", .bytes), ("via", optTy .bytes)])]
    isBadMethod ((slotPkg [bad] (goWith (noCallT bad))).checkWith []) = true := by
  decide +kernel

/-- A slot over the empty sum (which could never hold a call) is refused `badMethod`. -/
theorem slot_empty_sum :
    isBadMethod ((slotPkg [.sum []] (goWith (noCallT (.sum [])))).checkWith []) = true := by
  decide +kernel

/-- An invoke-only slot carrying a transfer does not check: `illTyped`. -/
theorem slot_kind_outside :
    let tr : Term := .inj invokeOnly "transfer" (.record [("amount", .nat 1),
      ("dst", .inj acctRefTy "well" (.bytes .empty)), ("once", .inj (optTy .bytes) "none" (.record [])),
      ("src", .inj acctRefTy "well" (.bytes .empty)), ("via", .inj (optTy .bytes) "none" (.record []))])
    isIllTyped ((slotPkg [invokeOnly] (goWith (someCallT invokeOnly tr))).checkWith []) = true := by
  decide +kernel

end Nanodregg.Lang.Teeth
