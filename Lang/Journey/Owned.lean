/-
# Lang.Journey.Owned — the journey's first package, `Owned`, on its own

`Owned` (a record `{owner, total}` under `bounded` and `ownerOnly`, with `set`) and the law helpers it is
written with. It is its own module so that the testground's kernel can print the journey's packages
(`Web.Sim.Testground.texts`) without linking the journey harness.
-/
import Lang.Std

namespace Nanodregg.Lang.Journey

open Nanodregg.Lang

def S : Ty := .record [("owner", .digest), ("total", .nat)]

def ok : Term := .inj verdictTy "ok" (.record [])
def refused (why : String) : Term := .inj verdictTy "refused" (.bytes why.toUTF8)

/-- Under `lam S (lam S (lam reqTy _))`: var 2 = old, var 1 = new, var 0 = req. -/
def law3 (body : Term) : Term := .lam S (.lam S (.lam reqTy body))

def bounded : Term :=
  law3 (.ite (.prim .le (.get (.var 1) "total") (.nat 100)) ok (refused "over 100"))

def ownerOnly : Term :=
  law3 (.ite (.prim .deq (.get (.var 0) "agent") (.get (.var 1) "owner"))
    (.ite (.prim .deq (.get (.var 2) "owner") (.get (.var 1) "owner")) ok (refused "owner changed"))
    (refused "not the owner"))

/-- `set state n req = {owner = state.owner, total = n}` -/
def setM : Term := Std.methodOf S .nat [("owner", .get (.var 2) "owner"), ("total", .var 1)]

def iface : Ty :=
  .record [("bounded", lawTy S), ("ownerOnly", lawTy S), ("set", methodTy S .nat)]

def owned : Package :=
  { imports := [], state := S, iface,
    body := .record [("bounded", bounded), ("ownerOnly", ownerOnly), ("set", setM)],
    methods := ["set"], laws := ["bounded", "ownerOnly"] }

end Nanodregg.Lang.Journey
