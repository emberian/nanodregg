/-
# Hosting.Proofs.Package — the generated package computes the lifecycle

Each evaluation theorem is the kernel running LANG's machine (`Lang.eval`) on a field of the package
BODY, applied as `Lang.Program` applies it (a law by `apply3` over the `Data.toVal` values of
decoded state and of the request, a method by `apply4` with its rows first: `rec {}`, it reads none), over every phase, event and act. `phase` is a sum of empty records, so a
decoded state holds one of exactly these values: the case split is exhaustive by the type.

LANG's `Proofs.Std` proves `machineLaw`'s spec in general (`machine_birth`, `machine_invoke`,
`machine_write_refused`, `machine_relaw_refused`, `machine_retire_refused`); these pin THIS package: the edges Hosting passes,
resolved to the method indices `Event.index` names, decide `step`.

There is no owner law: authority is KERNEL's gate (KERNEL-25, `invoke_authorized`).
-/
import Hosting.Package
import Lang.Print
import Hosting.Proofs.Lifecycle
import Lang.Read
import Lang.Eval
import Lang.Proofs.Print

namespace Nanodregg.Hosting.Proofs

open Nanodregg.Lang
open Nanodregg.Hosting
open Nanodregg.Hosting.Grain

/-- LANG's generators accept the package's inputs. -/
theorem lifecycle_built : (Grain.lifecycle? matches .ok _) = true := by decide +kernel

/-- The package's body (the theorems below are about the built package: `lifecycle_built`). -/
private def body : Term :=
  match Grain.lifecycle? with
  | .ok p => p.body
  | .error _ => .nat 0

/-- The fuel every evaluation below is given; each needs far less. -/
private def fuel : Nat := 1000

/-- The outcome is the verdict `ok` (`true`) or `refused` with a reason (`false`), and nothing else. -/
private def verdictIs (b : Bool) : Outcome → Bool
  | .value (.inj "ok" (.record [])) _ => b
  | .value (.inj "refused" (.bytes _)) _ => !b
  | _ => false

private def injIs (ℓ : String) : Outcome → Bool
  | .value (.inj m (.record [])) _ => m == ℓ
  | _ => false

/-- A state value: kind `k`, entry `entry`, phase `p`. -/
private def stD (p : Phase) (k : Kind := .app) (entry : ByteArray := .empty) : Data :=
  .record [("entry", .bytes entry), ("kind", .inj k.label unitD), ("phase", .inj p.label unitD)]

private def bytesIs (b : ByteArray) : Outcome → Bool
  | .value (.bytes c) _ => c == b
  | _ => false

/-- The acts a law is told about (LANG ID-1; the retirement, KERNEL-70). -/
private def birthD : Data := .inj "birth" unitD
private def invokeD (m : Nat) : Data := .inj "invoke" (.nat m)
private def writeD : Data := .inj "write" unitD
private def relawD : Data := .inj "relaw" (.bytes .empty)
private def retireD : Data := .inj "retire" unitD

private def rqD (occasion : Data) (principal : ByteArray := .empty) : Data :=
  .record [("agent", .digest .empty), ("notBefore", .nat 0), ("occasion", occasion),
    ("principal", .digest principal), ("self", .digest .empty), ("validUntil", .nat 0)]

/-- Field `ℓ` of the package body applied to the three bound values. -/
private def bodyAt (ℓ : Label) : Term :=
  .app (.app (.app (.get body ℓ) (.var 2)) (.var 1)) (.var 0)

/-- Method `ℓ` of the package body applied to its four bound values (rows first, LANG-49). -/
private def methodAt (ℓ : Label) : Term :=
  .app (.app (.app (.app (.get body ℓ) (.var 3)) (.var 2)) (.var 1)) (.var 0)

private def lawOn (ℓ : Label) (rq new old : Data) : Outcome :=
  eval [] fuel (bodyAt ℓ) [rq.toVal, new.toVal, old.toVal]

private def bE : ByteArray := "app.bin".toUTF8
private def bA : ByteArray := "a".toUTF8

/-- Field `f` of the result half `half` (`state` or `calls`) of method `e`, run from a state of
kind `k`, phase `p`, entry `bE`. -/
private def resultField (half : Label) (e : Event) (k : Kind) (p : Phase) (f : Label) : Outcome :=
  eval [] fuel (.get (.get (methodAt e.label) half) f)
    [(rqD (invokeD e.index) bA).toVal, unitD.toVal, (stD p k bE).toVal, unitD.toVal]

/-- Field `f` of the state method `e` writes. -/
private def methodField (e : Event) (k : Kind) (p : Phase) (f : Label) : Outcome :=
  resultField "state" e k p f

/-- The calls row of method `e`, run from a state of kind `k`, phase `p`, entry `bE`. -/
private def resultCalls (e : Event) (k : Kind) (p : Phase) : Outcome :=
  eval [] fuel (.get (methodAt e.label) "calls")
    [(rqD (invokeD e.index) bA).toVal, unitD.toVal, (stD p k bE).toVal, unitD.toVal]

/-- The calls row is the empty record. -/
private def emptyIs : Outcome → Bool
  | .value (.record []) _ => true
  | _ => false

/-- The method labels, in the package's order, are `Event.all`'s: method `n` is `Event.index`. -/
theorem lifecycle_methods :
    (Grain.lifecycle?.toOption.map (·.methods)) = some (Event.all.map Event.label) := by decide +kernel

/-- KERNEL's `invoke obj m` runs `p.methods[m]?`: method `Event.index e` is `e`. -/
theorem method_at_index :
    ∀ e ∈ Event.all, (Grain.lifecycle?.toOption.map (·.methods[e.index]?)) = some (some e.label) := by
  decide +kernel

theorem index_is_methodIndex :
    ∀ e ∈ Event.all, Std.methodIndex methodLabels e.label = some e.index := by decide

theorem laws_in_force : (Grain.lifecycle?.toOption.map (·.laws)) = some ["phase"] := by
  decide +kernel

/-- The package passes LANG's install check with no imports. -/
theorem lifecycle_checks :
    (Grain.lifecycle?.toOption.map fun p => p.checkWith [] matches .ok ()) = some true := by
  decide +kernel

/-- Birth: the `phase` law admits exactly a seed in the initial phase. -/
theorem phase_birth :
    ∀ q ∈ Phase.all, verdictIs (q == initial) (lawOn "phase" (rqD birthD) (stD q) (stD q)) = true := by
  decide +kernel

/-- An invoke of method `e`: the `phase` law admits `p → q` exactly when `step p e = some q`. -/
theorem phase_invoke :
    ∀ p ∈ Phase.all, ∀ e ∈ Event.all, ∀ q ∈ Phase.all,
      verdictIs (step p e == some q) (lawOn "phase" (rqD (invokeD e.index)) (stD q) (stD p)) = true := by
  decide +kernel

/-- A write, a law change or a retirement is refused, whatever the phases (a grain's lifecycle
object is permanent). -/
theorem phase_frozen :
    ∀ p ∈ Phase.all, ∀ q ∈ Phase.all,
      (verdictIs false (lawOn "phase" (rqD writeD) (stD q) (stD p)) &&
       verdictIs false (lawOn "phase" (rqD relawD) (stD q) (stD p)) &&
       verdictIs false (lawOn "phase" (rqD retireD) (stD q) (stD p))) = true := by
  decide +kernel

/-- Method `e`, as `runMethod` runs it, writes `phase := target p e` and keeps `kind` and `entry`,
for both kinds (so a method writing a constant is caught). -/
theorem method_writes :
    ∀ k ∈ Kind.all, ∀ p ∈ Phase.all, ∀ e ∈ Event.all,
      (injIs (target p e).label (methodField e k p "phase") &&
       injIs k.label (methodField e k p "kind") &&
       bytesIs bE (methodField e k p "entry")) = true := by
  decide +kernel

/-- Every lifecycle method makes no calls, by its type: its signature has no call slots (a
lifecycle step moves the phase and nothing else), and `lifecycle_checks` holds its body to it. -/
theorem method_no_calls :
    (Grain.lifecycle?.toOption.map fun p => Event.all.all fun e =>
      decide (((match p.iface with | .record r => Row.find? e.label r | _ => none).bind
        (methodSig p.state p.rels)) = some ⟨unit, [], [], 0⟩)) = some true := by
  decide +kernel

/-- And every method's calls row evaluates to the empty record, for every kind, phase and event. -/
theorem method_calls_empty :
    ∀ k ∈ Kind.all, ∀ p ∈ Phase.all, ∀ e ∈ Event.all, emptyIs (resultCalls e k p) = true := by
  decide +kernel

/-- Method and law together: the state method `e` writes from phase `p` is admitted by the `phase`
law exactly when `(p, e)` is an edge. -/
theorem method_iff_step :
    ∀ p ∈ Phase.all, ∀ e ∈ Event.all,
      verdictIs (step p e).isSome
        (lawOn "phase" (rqD (invokeD e.index)) (stD (target p e)) (stD p)) = true := by
  decide +kernel

/-- The package prints: `Print.package` gives the lifecycle a text (every depth within
`Read.depthMax`). Whether a text EXISTS needs no string built, so the kernel decides it. -/
theorem lifecycle_prints : (Grain.lifecycle?.toOption.bind Print.package).isSome = true := by
  decide +kernel

/-- The text a member installs reads back, by `Lang.Read`, as exactly the package: LANG-29's
`readPackage_checked` over `lifecycle_checks` (no imports), at the text `lifecycle_prints` says
exists. -/
theorem lifecycle_text_reads :
    ∃ p s, Grain.lifecycle? = .ok p ∧ Print.package p = some s ∧ Read.readPackage s = .ok p := by
  have hc := lifecycle_checks
  have hp := lifecycle_prints
  cases hl : Grain.lifecycle? with
  | error e => rw [hl] at hc; cases hc
  | ok p =>
    rw [hl] at hc hp
    have hc' : p.checkWith [] = .ok () := by
      simp only [Except.toOption, Option.map_some, Option.some.injEq] at hc
      split at hc
      · assumption
      · cases hc
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (by simpa [Except.toOption] using hp)
    exact ⟨p, s, rfl, hs, Print.readPackage_checked (by simp) hc' hs⟩

/-- The package has wire bytes (what `install` carries and `lifecycleId` digests). -/
theorem lifecycle_encodes : (Grain.lifecycle?.toOption.bind Wire.encodePackage).isSome = true := by
  decide +kernel

end Nanodregg.Hosting.Proofs
