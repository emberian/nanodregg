/-
# Lang.Contextual.LangInstance — the DEPLOYED term language as a `CalculusData` (ACTIVITIES-2)

The data half of CLOSURE's calculus over deployed `Lang.Term`, built from the operations the Host runs
(`Lang.Subst`): `msubst` is `fillRefs`; strengthening and weakening rename ordinary variables at a position
with `lowerIdx`/`liftIdx` (`Lang.Index`). The signature-aware laws live in
`Lang.Proofs.Contextual.LangInstance`; deployed strengthening is exercised and proved over the installed
contextual ROM generator. No deployed module imports this one.

Below `langData`: the two-support, one-blocker deployed fragment of the same calculus that the `Std.hole`
bridge (`Lang.Proofs.Contextual.HoleBridge`) is stated over.
-/
import Lang.Subst
import Lang.Contextual.Closure

namespace Nanodregg.Lang.Contextual

/-- `Lang.Term` as a `CalculusData`. -/
def langData : CalculusData where
  Ty := Lang.Ty
  Ctx := List Lang.Ty
  Tm := Term
  tmEq := Term.decEq
  msubst := Term.fillRefs
  check Ψ M A := decide (Lang.infer [] Ψ M = some A)
  uses M x := Term.usesVar x M
  drop Ψ x := Ψ.eraseIdx x
  strengthen x := Term.renameVar (lowerIdx x)
  weaken x := Term.renameVar (liftIdx x)
  var := Term.var
  lookup Ψ x := Ψ[x]?

/-! ## The two-support, one-blocker fragment of `langData` for the `Std.hole` bridge -/

variable {E : Type}

/-- Recorded status is advisory. The filling is a real Lang term; its checker
is langData.check, not an invented always-true calculus. -/
def holeModelCandidate (value : Term) (s0 s1 blocker : Option Token)
    (by_ : Party) (recorded : Status) : Candidate langData :=
  ⟨value, s0.toList ++ s1.toList, blocker.toList, 0, by_, recorded⟩

/-- Missing optional supports impose no requirement. -/
def holeLive (w : World E) (s : Option Token) : Bool :=
  match s with | none => true | some t => w.live t

def holeBlocked (w : World E) (blocker : Option Token) : Bool :=
  match blocker with | none => false | some t => w.live t


/-- A generated hole has empty local context and no hypothesis-derived support.
Its clause is supplied by the application, not by a candidate. -/
def holeModelIface (V : Lang.Ty) (guard : E → Term → Bool) (chooser acceptor : Party) :
    Iface langData E where
  name := 0
  ctx := []
  ty := V
  hyps := []
  hyps_real := by intro h hm; cases hm
  guard := guard
  budget := 0
  chooser := chooser
  acceptor := acceptor

/-- The real Lang template is ref 0; substitution installs a closed filling at
that ref. No artificial variable constructor or constant checker is introduced. -/
def holeModelTemplate (V : Lang.Ty) (guard : E → Term → Bool) (chooser acceptor : Party) :
    Template langData E where
  Γ := []
  T := V
  P := .hole 0 []
  Ω := [holeModelIface V guard chooser acceptor]
  names := by simp

end Nanodregg.Lang.Contextual
