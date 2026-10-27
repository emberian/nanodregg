/-
# Lang.Journey.Kept — the journey's claiming package `Kept` and its leaky law (§LK, LANG-93)

`Kept` is `Owned` with the invariant `le100` in its interface and `bounded` in certifying shape, claiming
`keeps le100 bounded`; `leaky` is LK6's law whose `write` arm admits without the test. Its own module so
that the testground's kernel prints them (`Web.Sim.Testground.texts`) without linking the journey harness.
-/
import Lang.Journey.Owned
import Lang.Claim

namespace Nanodregg.Lang.Journey

open Nanodregg.Lang

/-- `total ≤ 100`, as a closed invariant of type `fn S bool`. -/
def le100 : Term := .lam S (.prim .le (.get (.var 0) "total") (.nat 100))

/-- `bounded` in certifying shape: refused unless `le100 new`. -/
def boundedKeeps : Term := law3 (.ite (.app le100 (.var 1)) ok (refused "over 100"))

/-- Under `case req.occasion`: var 3 = old, var 2 = new, var 1 = req, var 0 = the payload. The
`write` arm admits without the test (the `retire` arm tests, like every arm but `relaw`). -/
def leaky : Term :=
  let test := Term.ite (.app le100 (.var 2)) ok (refused "over 100")
  .lam S (.lam S (.lam reqTy (.case (.get (.var 0) "occasion")
    [("adopt", test), ("birth", test), ("invoke", test), ("relaw", ok), ("retire", test),
     ("write", ok)])))

/-- `Owned`'s interface with the invariant `le100` as a field (labels ascending). -/
def keptIface : Ty :=
  .record [("bounded", lawTy S), ("le100", .fn S .bool), ("ownerOnly", lawTy S), ("set", methodTy S .nat)]

/-- `Owned` with `le100` in its interface, `bounded := bnd`, carrying `claims`. -/
def keptWith (bnd : Term) (claims : List Claim) : Package :=
  { owned with
    iface := keptIface
    body := .record [("bounded", bnd), ("le100", le100), ("ownerOnly", ownerOnly), ("set", setM)]
    claims := claims }

/-- `Kept`: `bounded` in certifying shape, claiming `keeps le100 bounded`. -/
def kept : Package := keptWith boundedKeeps [.keeps "le100" "bounded"]

end Nanodregg.Lang.Journey
