/-
# Hosting.Proofs.Allowance — the allowance package computes its two methods, has a text, and is read
only from the operator's own objects

The method theorems are the kernel running LANG's machine (`Lang.eval`) on the package BODY, applied
as `Lang.Program` applies a method (state at `var 2`, argument at `var 1`, request at `var 0`), over
a state whose every field is distinct, for both values of `revoked`, so a method that copies the
wrong field, or writes a constant, is caught.
-/
import Hosting.Allowance
import Lang.Print
import Lang.Read
import Lang.Eval
import Lang.Proofs.Print
import Kernel.Receive.Authority
import Kernel.Proofs.Rooted
import Lang.Proofs.Data
import Lang.Program

namespace Nanodregg.Hosting.Proofs.Allowance

open Nanodregg.Lang Nanodregg.Kernel Nanodregg.Hosting Nanodregg.Hosting.Allow

/-- The package passes LANG's install check with no imports. -/
theorem allowance_checks : (allowance.checkWith [] matches .ok ()) = true := by decide +kernel

/-- No law; the methods, in KERNEL's index order, are `revoke` then `set`. -/
theorem allowance_shape :
    allowance.laws = [] ∧ allowance.methods = ["revoke", "set"] ∧
      allowance.methods[revokeIndex]? = some "revoke" ∧ allowance.methods[setIndex]? = some "set" := by
  decide +kernel

private def fuel : Nat := 1000

private def stD (revoked : Bool) : Data :=
  .record [("cap", .nat 11), ("keySlot", .nat 12), ("maxTokens", .nat 13), ("microPerKTok", .nat 14),
    ("model", .bytes "mm".toUTF8), ("resident", .bytes "rr".toUTF8), ("revoked", .bool revoked),
    ("windowMs", .nat 15)]

private def argD : Data :=
  .record [("cap", .nat 21), ("keySlot", .nat 22), ("maxTokens", .nat 23), ("microPerKTok", .nat 24),
    ("windowMs", .nat 25)]

private def rqD : Data :=
  .record [("agent", .bytes .empty), ("notBefore", .nat 0), ("occasion", .inj "invoke" (.nat 0)),
    ("principal", .bytes .empty), ("self", .bytes .empty), ("validUntil", .nat 0)]

private def resultOf (m : Label) : Term :=
  .app (.app (.app (.get allowance.body m) (.var 2)) (.var 1)) (.var 0)

/-- Field `f` of the state half of method `m`'s result. -/
private def fieldOf (m : Label) (arg : Data) (st : Data) (f : Label) : Outcome :=
  eval [] fuel (.get (.get (resultOf m) "state") f) [rqD.toVal, arg.toVal, st.toVal]

/-- The calls half of method `m`'s result. -/
private def callsOf (m : Label) (arg : Data) (st : Data) : Outcome :=
  eval [] fuel (.get (resultOf m) "calls") [rqD.toVal, arg.toVal, st.toVal]

private def emptyIs : Outcome → Bool
  | .value (.record []) _ => true
  | _ => false

private def valIs : Data → Outcome → Bool
  | .nat n, .value (.nat m) _ => n == m
  | .bool b, .value (.bool c) _ => b == c
  | .bytes x, .value (.bytes y) _ => x == y
  | _, _ => false

private def get (d : Data) (f : Label) : Data :=
  match d with
  | .record fs => (fs.find? (·.1 == f)).map (·.2) |>.getD (.nat 0)
  | _ => .nat 0

/-- `revoke` sets `revoked` and keeps every other field; `set` takes the settable fields from its
argument and keeps `model`, `resident` and `revoked` (so a revoked allowance stays revoked). -/
theorem methods_write :
    ∀ rv ∈ [true, false], ∀ f ∈ fields.map (·.1),
      valIs (if f = "revoked" then .bool true else get (stD rv) f) (fieldOf "revoke" (.record []) (stD rv) f) &&
      valIs (if settable.contains f then get argD f else get (stD rv) f) (fieldOf "set" argD (stD rv) f) := by
  decide +kernel

/-- Neither method makes a call (LANG-33): each declares no call slot, and its calls half evaluates
to the empty record. -/
theorem methods_no_calls :
    ((match allowance.iface with | .record r => Row.find? "revoke" r | _ => none).bind
        (methodSig allowance.state) = some (unit, []) ∧
      (match allowance.iface with | .record r => Row.find? "set" r | _ => none).bind
        (methodSig allowance.state) = some (setTy, [])) ∧
    ∀ rv ∈ [true, false], (emptyIs (callsOf "revoke" (.record []) (stD rv)) && emptyIs (callsOf "set" argD (stD rv))) = true := by
  decide +kernel

/-- The package prints: `Print.package` gives it a text. -/
theorem allowance_prints : (Print.package allowance).isSome = true := by decide +kernel

/-- The text the operator installs reads back, by `Lang.Read`, as exactly the package. -/
theorem allowance_text_reads : ∃ s, Print.package allowance = some s ∧ Read.readPackage s = .ok allowance := by
  have hc : allowance.checkWith [] = .ok () := by
    have h := allowance_checks
    split at h
    · assumption
    · cases h
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp allowance_prints
  exact ⟨s, hs, Print.readPackage_checked (by simp) hc hs⟩

/-- The package has wire bytes (what `install` carries and `allowanceId` digests). -/
theorem allowance_encodes : (Wire.encodePackage allowance).isSome = true := by decide +kernel

/-! ## Read only from the operator's own, unrevoked objects -/

private theorem opt_beq {o : Option ByteArray} {b : ByteArray} (h : (o == some b) = true) : o = some b := by
  cases o with
  | none => cases h
  | some a =>
    cases a with | mk x => cases b with | mk y =>
    have : (x == y) = true := h
    simp only [beq_iff_eq] at this
    rw [this]

/-- What `allowanceOf` accepts: an object of the allowance package, owned by `operator`, whose
`revoked` reads `false`. -/
theorem allowanceOf_sound {pkgId operator : ByteArray} {c : Cell} {x : ByteArray × Broker.Allowance}
    (h : allowanceOf pkgId operator c = some x) :
    c.kind = Receive.kindObject ∧ c.slots.get Receive.slotPackage = some pkgId ∧
      c.slots.get Receive.slotOwner = some operator ∧ boolAt c.slots 6 = some false := by
  unfold allowanceOf at h
  dsimp only at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    obtain ⟨⟨hk, hp⟩, ho⟩ := hg
    refine ⟨hk, opt_beq hp, opt_beq ho, ?_⟩
    split at h
    · assumption
    · cases h
  · cases h

private theorem ba_self (x : ByteArray) : (x == x) = true := by
  cases x with | mk y => show (y == y) = true; simp

/-- The object KERNEL creates from a seed (its owner `owner`, its package `p`, no extra law) reads
back as exactly the allowance it was seeded with, named by the resident's directory name, for every
allowance whose fields LANG can carry. -/
theorem seed_reads {D : Type} (X : Receive.Ctx D) (owner p : D) {r : ByteArray} {a : Broker.Allowance}
    {s : Kernel.Slots} (h : seed r a = some s) :
    allowanceOf (X.env.bytes p) (X.env.bytes owner) (Receive.objectCell X owner (some p) [] s) =
      some (Controller.dirOf r, a) := by
  simp only [seed, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨e0, h0, e1, h1, e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, rfl⟩ := h
  have d0 := Wire.decodeData_eq_ok_iff.mpr h0
  have d1 := Wire.decodeData_eq_ok_iff.mpr h1
  have d2 := Wire.decodeData_eq_ok_iff.mpr h2
  have d3 := Wire.decodeData_eq_ok_iff.mpr h3
  have d4 := Wire.decodeData_eq_ok_iff.mpr h4
  have d5 := Wire.decodeData_eq_ok_iff.mpr h5
  have d6 := Wire.decodeData_eq_ok_iff.mpr h6
  have d7 := Wire.decodeData_eq_ok_iff.mpr h7
  simp [allowanceOf, natAt, Allow.bytesAt, boolAt, Receive.objectCell, Receive.slotsOf, Receive.lawSlots,
    slotAt, Receive.stateBase, Receive.slotPackage, Receive.slotOwner, slots_get_set_eq,
    slots_get_set_ne, d0, d1, d2, d3, d4, d5, d6, d7, ba_self]

/-- The seed is the state LANG reads: `Lang.readState` over the package's own state row gives, at
each label, exactly that field of the allowance (so `seed`'s slot order is the state type's, and no
two fields can be swapped between what LANG and the broker read). -/
theorem seed_state {r : ByteArray} {a : Broker.Allowance} {s : Kernel.Slots} (h : seed r a = some s) :
    Lang.readState fields s = .ok (.record [("cap", .nat a.cap), ("keySlot", .nat a.keySlot),
      ("maxTokens", .nat a.maxTokens), ("microPerKTok", .nat a.microPerKTok), ("model", .bytes a.model),
      ("resident", .bytes r), ("revoked", .bool false), ("windowMs", .nat a.windowMs)]) := by
  simp only [seed, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨e0, h0, e1, h1, e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, rfl⟩ := h
  simp [Lang.readState, Lang.readState.go, fields, slotAt, Receive.stateBase, Kernel.Slots.get, List.lookup,
    Wire.decodeData_eq_ok_iff.mpr h0, Wire.decodeData_eq_ok_iff.mpr h1, Wire.decodeData_eq_ok_iff.mpr h2,
    Wire.decodeData_eq_ok_iff.mpr h3, Wire.decodeData_eq_ok_iff.mpr h4, Wire.decodeData_eq_ok_iff.mpr h5,
    Wire.decodeData_eq_ok_iff.mpr h6, Wire.decodeData_eq_ok_iff.mpr h7]

private def pid : ByteArray := "P".toUTF8
private def op : ByteArray := "O".toUTF8
private def alw : Broker.Allowance := ⟨"m".toUTF8, 7, 1000, 60000, 5000, 100⟩
private def rid : ByteArray := ⟨#[0xab, 0x01]⟩

private def cellOf (pkg owner : ByteArray) (s : Kernel.Slots) : Cell :=
  { kind := Receive.kindObject, discipline := .ram,
    slots := Receive.slotsOf ([(Receive.slotPackage, pkg), (Receive.slotOwner, owner)] ++ s) }

private def readsAs (want : Option (ByteArray × Broker.Allowance)) (pkg owner : ByteArray)
    (s : Option Kernel.Slots) : Bool :=
  match s with
  | some s => allowanceOf pid op (cellOf pkg owner s) == want
  | none => false

/-- The seed reads back as the allowance it was built from, named by the resident's hex; another
owner's object, another package's object and a revoked one read as nothing. -/
theorem seed_teeth :
    readsAs (some ("ab01".toUTF8, alw)) pid op (seed rid alw) = true ∧
    readsAs none pid "Q".toUTF8 (seed rid alw) = true ∧
    readsAs none "Z".toUTF8 op (seed rid alw) = true ∧
    readsAs none pid op ((seed rid alw).bind fun s =>
      (Wire.encodeData .bool (.bool true)).map fun b => s.set (slotAt 6) b) = true := by
  decide +kernel

end Nanodregg.Hosting.Proofs.Allowance
