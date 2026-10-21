/- The two-support, one-blocker deployed fragment of the existing Lang calculus. -/
import Lang.Contextual.LangCalculus

namespace Nanodregg.Lang.Contextual

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

