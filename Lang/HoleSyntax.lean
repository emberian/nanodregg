/- Shared named-variable construction for guarded hole generators. -/
import Lang.StdActivity

namespace Nanodregg.Lang.Std.HoleSyntax

abbrev H := List Label → Term
def hv (x : Label) : H := fun sc => .var (sc.idxOf x)
def hc (t : Term) : H := fun _ => t
def hg (t : H) (l : Label) : H := fun sc => .get (t sc) l
def hr (fs : List (Label × H)) : H :=
  fun sc => .record (Row.sort (fs.map fun (l, t) => (l, t sc)))
def hi (T : Ty) (l : Label) (t : H) : H := fun sc => .inj T l (t sc)
def hl (x : Label) (T : Ty) (t : H) : H := fun sc => .lam T (t (x :: sc))
def ha (f : H) (xs : List H) : H := fun sc => activityApply (f sc) (xs.map (· sc))
def hf (t : H) (arms : List (Label × Label × H)) : H :=
  fun sc => .case (t sc) (Row.sort (arms.map fun (l, x, b) => (l, b (x :: sc))))
def ht (c a b : H) : H := fun sc => .ite (c sc) (a sc) (b sc)
def hp (p : Prim) (a b : H) : H := fun sc => .prim p (a sc) (b sc)
def he (T : Ty) (a b : H) : H := fun sc => eqData T (a sc) (b sc)
def hu (t : H) (fs : List (Label × H)) : H :=
  fun sc => .extend (t sc) (Row.sort (fs.map fun (l, b) => (l, b sc)))
def hn : H := hr []
def hb (b : Bool) : H := hc (.bool b)
def hs (s : String) : H := hc (.bytes s.toUTF8)
def hnone (T : Ty) : H := hi (optTy T) "none" hn
def hsome (T : Ty) (t : H) : H := hi (optTy T) "some" t


def hlet (name : Label) (T : Ty) (value body : H) : H :=
  ha (hl name T body) [value]

def hguard (c : H) (why : String) (rest : H) : H :=
  ht c rest (hc (refusedT why))


end Nanodregg.Lang.Std.HoleSyntax
