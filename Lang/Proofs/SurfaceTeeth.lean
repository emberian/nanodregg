/-
# Lang.Proofs.SurfaceTeeth — the surface theorems' premises are met and their conclusions bite

* `read_print_surface` is met by a printed package (the empty one), and is not "the surface is the
  core reader": the journey's LT0s reads a surface text the core reader refuses.
* `layer_keeps_laws`: a layer adding a method lowers and keeps the super's law; a layer naming the
  super's law, or retyping a super method, is refused by name.
* `boundCheck`: run on concrete arguments, the check refuses an empty and an over-long text by the
  name `text 1..4`, and passes 1 and 4 bytes to the body.
-/
import Lang.Proofs.Surface
import Lang.Proofs.PrintTeeth

namespace Nanodregg.Lang.Surface

/-- The empty package's text (`Print.empty_package_prints`) is read by the surface as by the core. -/
theorem empty_package_surface :
    readPackage ((Print.package (Package.mk [] (.record []) (.record []) (.record []) [] [] [] .empty [] [])).get
      Print.empty_package_prints) =
    liftR (Read.readPackage ((Print.package (Package.mk [] (.record []) (.record []) (.record []) [] [] [] .empty [] [])).get
      Print.empty_package_prints)) :=
  read_print_surface (Option.some_get _).symm

/-! ### A toy super with one law `l` and one method `m` -/

private def S : Ty := .record []
private def mT : Ty := methodTy S (.record [])
private def sup : Package :=
  { imports := [], state := S, iface := .record [("l", lawTy S), ("m", mT)], body := .record [],
    methods := ["m"], laws := ["l"] }

private def isOverride : P Package → Bool
  | .error (.overridesLaw _ "l") => true
  | _ => false

private def isRetyped : P Package → Bool
  | .error (.retypedOverride _ "m") => true
  | _ => false

private def keeps : P Package → Bool
  | .ok p => p.laws == ["l"] && p.methods == ["m", "k"] && p.imports == [⟨#[7]⟩]
  | .error _ => false

/-- Adding a method `k`: the layer lowers, keeps law `l`, and keeps `m` at index 0 (`k` after it). -/
theorem layer_adds_method : keeps (layerOf (fun _ => 0) ⟨#[7]⟩ sup [("k", mT, .nat 0)] [] ["k"]) = true := by
  decide

/-- Naming the super's law is refused `overridesLaw` (a layer never replaces a super's law). -/
theorem layer_law_refused :
    isOverride (layerOf (fun _ => 0) ⟨#[7]⟩ sup [("l", lawTy S, .nat 0)] ["l"] []) = true := by decide

/-- Overriding `m` at another type is refused `retypedOverride`. -/
theorem layer_retype_refused :
    isRetyped (layerOf (fun _ => 0) ⟨#[7]⟩ sup [("m", .nat, .nat 0)] [] []) = true := by decide

/-- Overriding `m` at its own type is a layer. -/
theorem layer_override_same_type :
    (layerOf (fun _ => 0) ⟨#[7]⟩ sup [("m", mT, .nat 0)] [] []).toOption.isSome = true := by decide

/-! ### The bound check on concrete arguments: `text 1..4` -/

private def textBound : Bound := ⟨["text"], true, 1, 4⟩

/-- The environment under a method's binders: the request (a stand-in) at 0, the argument at 1. -/
private def envWith (w : ByteArray) : Env := [.nat 0, .record [("text", (.bytes w, []))]]

private def checked (w : ByteArray) : Outcome := eval [] 100 (boundCheck .nat [textBound] (.nat 7)) (envWith w)

private def refusedAs (why : String) : Outcome → Bool
  | .fault (.refused w) _ => w == why.toUTF8
  | _ => false

private def gives7 : Outcome → Bool
  | .value (.nat 7) _ => true
  | _ => false

theorem bound_name : textBound.name = "text 1..4" := by decide

theorem bound_empty_refused : refusedAs "text 1..4" (checked .empty) = true := by decide

theorem bound_long_refused : refusedAs "text 1..4" (checked ⟨#[1, 2, 3, 4, 5]⟩) = true := by decide

theorem bound_one_passes : gives7 (checked ⟨#[1]⟩) = true := by decide

theorem bound_four_passes : gives7 (checked ⟨#[1, 2, 3, 4]⟩) = true := by decide

end Nanodregg.Lang.Surface
