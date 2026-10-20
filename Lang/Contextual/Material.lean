/- Finite visited material for interaction guards; a demonstration Mini can take.
Fouquere–Quatrini, Incarnation in Ludics (2013), Def 5.1 p24 and Def 5.5 p26.
This is an address-based finite model, not full ludics biorthogonality. -/
import Lang.Contextual.P1

namespace Nanodregg.Lang.Contextual.Material

/-- Finite branching code, with explicit give-up leaves (Fouquere–Quatrini p26). -/
inductive Filling (A : Type) where
  | answer (value : A)
  | gaveUp
  | fork (left right : Filling A)
deriving Repr, DecidableEq

/-- A trace stops at a value, a daimon, or an address needing more interaction (ibid. p24). -/
inductive Stop (A : Type) where
  | answer (value : A)
  | gaveUp
  | missing
deriving Repr, DecidableEq

/-- Interactions select an address and inspect its answer; names are only display labels
(Fouquere–Quatrini Def 5.1 p24, finite specialization). -/
structure Test (A : Type) where
  name : Nat
  path : List Bool
  accepts : A → Bool

/-- The actual visited terminal cell; unused address suffixes after a daimon are discarded
(Fouquere–Quatrini Def 5.5 p26). -/
def visit {A : Type} : Filling A → List Bool → List Bool × Stop A
  | .answer a, _ => ([], .answer a)
  | .gaveUp, _ => ([], .gaveUp)
  | .fork _ _, [] => ([], .missing)
  | .fork l r, b :: bs =>
    let v := visit (if b then r else l) bs
    (b :: v.1, v.2)

/-- Sparse sub-filling: visited terminal cells with their actual addresses; prefixes
are implicit, repeated visits are retained (Fouquere–Quatrini Def 5.1 p24). -/
def material {A : Type} (tests : List (Test A)) (c : Filling A) :
    List (List Bool × Stop A) := tests.map fun t => visit c t.path

/-- Completion is separate from materiality: incarnation is itself daimon-closed
(Fouquere–Quatrini Def 5.5 p26). -/
def complete {A : Type} (t : Test A) (c : Filling A) : Bool :=
  match (visit c t.path).2 with
  | .answer a => t.accepts a
  | _ => false

/-- Preserve the original P1 interaction consumer (Fouquere–Quatrini p24). -/
def interaction {A : Type} (t : Test A) : P1.Interaction (Filling A) :=
  ⟨t.name, complete t⟩

/-- A verified receipt binds the exact interactions and visited material (ibid. Def 5.1 p24). -/
structure Receipt (A : Type) where
  against : List (Test A)
  fragment : List (List Bool × Stop A)

/-- A visited daimon is partial, even if an orthogonality-only test would accept it
(Fouquere–Quatrini Def 5.5 p26; completion is our admission policy). -/
inductive Verdict (A : Type) where
  | verified (receipt : Receipt A)
  | incomplete
  | rejected

/-- First reject unfinished material, then check answers, retaining the tested fragment
(Fouquere–Quatrini pp24–26). -/
def inspect {A : Type} (tests : List (Test A)) (c : Filling A) : Verdict A :=
  if (material tests c).any (fun cell => match cell.2 with
      | .answer _ => false | _ => true) then .incomplete
  else if P1.guard (tests.map interaction) c then
    .verified ⟨tests, material tests c⟩
  else .rejected

/-- A pair whose unvisited branch gives up (Fouquere–Quatrini p24: unused subdesigns). -/
def sample : Filling Nat := .fork (.answer 7) .gaveUp

/-- The left interaction requires seven (Fouquere–Quatrini p24, finite example). -/
def left : Test Nat := ⟨0, [false], fun n => n == 7⟩

/-- The right interaction exposes the daimon (Fouquere–Quatrini p26, finite example). -/
def right : Test Nat := ⟨1, [true], fun _ => true⟩


/-- Strengthen an existing candidate guard with material-aware interactions; never discard
the original guard (Fouquere–Quatrini pp24–26). -/
def withMaterial {D : CalculusData} {E A : Type} (I : Iface D E)
    (tests : E → List (Test A)) (project : E → D.Tm → Filling A) : Iface D E :=
  { I with guard := fun env term =>
      I.guard env term && P1.guard ((tests env).map interaction) (project env term) }

/-- The existing candidate judgment now carries its exact tested scope and sparse material
(Fouquere–Quatrini Def 5.1 p24). Arbitrary data records still need the soundness theorem. -/
def inspectCandidate {D : CalculusData} {E A : Type} (I : Iface D E)
    (tests : E → List (Test A)) (project : E → D.Tm → Filling A)
    (w : World E) (c : Candidate D) : Status × Receipt A :=
  (judge (withMaterial I tests project) w c,
    ⟨tests w.env, material (tests w.env) (project w.env c.filling)⟩)

end Nanodregg.Lang.Contextual.Material
