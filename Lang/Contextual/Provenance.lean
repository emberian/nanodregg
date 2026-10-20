/- P9: finite dual-literal provenance, retaining environmental conditions.
Grädel–Tannen (2024), Def4 p9, §6 pp19–20; de Kleer (1986), pp144–145.
Candidates are Doyle (1979) IN/OUT justifications, not ATMS labels. The computed
polynomial is a label; its Boolean image forgets multiplicity, not conditions. -/
import Lang.Contextual.Closure

namespace Nanodregg.Lang.Contextual.P9

variable {D : CalculusData} {E : Type}

/-- Grädel–Tannen §6 pp19–20: keep the verdict's input until specialization.
The budget is a literal too, even though Iface fixes it across world edits. -/
inductive EnvLit (D : CalculusData) where
  | guard (filling : D.Tm)
  | budget (cost : Nat)
deriving DecidableEq

def EnvLit.eval (I : Iface D E) (env : E) : EnvLit D → Bool
  | .guard t => I.guard env t
  | .budget cost => decide (cost ≤ I.budget)

/-- Dual token literals plus unevaluated environmental literals (Grädel–Tannen p9, p19). -/
structure Monomial (D : CalculusData) where
  supports : List Token
  blockers : List Token
  envLits : List (EnvLit D)
deriving DecidableEq

def Monomial.envOK (I : Iface D E) (env : E) (m : Monomial D) : Bool :=
  m.envLits.all (EnvLit.eval I env)

def Monomial.eval (I : Iface D E) (w : World E) (m : Monomial D) : Bool :=
  m.envOK I w.env && m.supports.all w.live && m.blockers.all (fun t => !w.live t)

/-- A Candidate is Doyle (1979), an IN/OUT justification, not an ATMS label.
This translation produces one label environment (de Kleer 1986, pp144–145). -/
def monomial (I : Iface D E) (c : Candidate D) : Monomial D :=
  ⟨effSupports I c, c.blockers, [.guard c.filling, .budget c.cost]⟩

/-- Grädel–Tannen §6 p19: no environment argument, hence no erased guard branch.
Only the immutable typing problem is specialized. -/
def provenance (I : Iface D E) (cs : List (Candidate D)) : List (Monomial D) :=
  (cs.filter fun c => D.check I.ctx c.filling I.ty).map (monomial I)

/-- The original token polynomial recovered by evaluating precisely envLits (Prop15 p20). -/
def specialize (I : Iface D E) (env : E) (ms : List (Monomial D)) :
    List (List Token × List Token) :=
  (ms.filter (Monomial.envOK I env)).map fun m => (m.supports, m.blockers)

/-- p·p̄ = 0: a product containing both polarities contributes nothing (Def4 p9). -/
def Monomial.consistent (m : Monomial D) : Bool :=
  m.supports.all fun t => !decide (t ∈ m.blockers)

/-- de Kleer pp144–145: inclusion of ALL literals, including environmental obligations. -/
def Monomial.subsumes (a b : Monomial D) : Bool :=
  a.supports.all (fun t => decide (t ∈ b.supports)) &&
  a.blockers.all (fun t => decide (t ∈ b.blockers)) &&
  a.envLits.all (fun l => decide (l ∈ b.envLits))

/-- Absorption a + ab = a in PosBool[X,X̄], retaining a representative of equal products.
de Kleer p145: no surviving label environment strictly contains another. -/
def minimal : List (Monomial D) → List (Monomial D)
  | [] => []
  | m :: ms =>
    let rest := minimal ms
    if rest.any (fun n => n.subsumes m) then rest
    else m :: rest.filter (fun n => !m.subsumes n)

/-- A complete label: erase complementary products, then absorb supersets. -/
def label (I : Iface D E) (cs : List (Candidate D)) : List (Monomial D) :=
  minimal ((provenance I cs).filter Monomial.consistent)

end Nanodregg.Lang.Contextual.P9
