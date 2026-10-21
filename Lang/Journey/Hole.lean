/- The hole journey uses the checked generator, not a handwritten lookalike. -/
import Lang.StdHole
import Lang.Print
namespace Nanodregg.Lang.Std

def holeCapClause : Term :=
  .lam holeState (.lam .nat (.prim .le (.var 0) (.get (.var 1) "cap")))

def generatedHoleBundle : Except HoleRefusal HoleBundle := hole .nat holeCapClause

end Nanodregg.Lang.Std
