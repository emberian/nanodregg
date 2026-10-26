/-
# Lang.Journey.Claims — §LK: a claim's certifying shape, checked as install will check it (LANG-83, L1)

The checker `Term.guardedBy` run as a function on laws over `Owned`'s state `{owner, total}` with the
invariant `le100 = λ s. s.total ≤ 100`: L1 of DESIGN-PCC §8. L2 carries claims in the package and
refuses at install through the receivers.

* LK1 a hand-written law in certifying shape (every `ok` under `app le100 new`) checks, and so does
  `Std.keeps S le100`.
* LK2 a law whose `write` arm admits without the test does not check (an unguarded `ok`).
* LK3 a law that returns a verdict it read from its state is not in shape (nothing but a literal `inj`
  may be an `ok`).
* LK4 the journey's own `bounded` tests `new.total ≤ 100` INLINE, not as `app le100 new`: not in shape
  until the renaming lemma lands (DESIGN-PCC §3.4); it is the row that measures that gap.
-/
import Lang.Journey
import Lang.Claim

namespace Nanodregg.Lang.Journey

open Nanodregg.Kernel

/-- `total ≤ 100`, as a closed invariant of type `fn S bool`. -/
def le100 : Term := .lam S (.prim .le (.get (.var 0) "total") (.nat 100))

/-- `bounded` in certifying shape: refused unless `le100 new`. -/
def boundedKeeps : Term := law3 (.ite (.app le100 (.var 1)) ok (refused "over 100"))

/-- Under `case req.occasion`: var 3 = old, var 2 = new, var 1 = req, var 0 = the payload. The
`write` arm admits without the test. -/
def leaky : Term :=
  let test := Term.ite (.app le100 (.var 2)) ok (refused "over 100")
  .lam S (.lam S (.lam reqTy (.case (.get (.var 0) "occasion")
    [("adopt", test), ("birth", test), ("invoke", test), ("relaw", ok), ("write", ok)])))

/-- A law that returns whatever verdict its new state holds at `flag`. -/
def readsVerdict : Term := law3 (.get (.var 1) "flag")

def claimSession : Run :=
  let X := ctxWith langProgram
  let r : Run := { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
  let chk (t : Term) : Bool := Term.guardedBy le100 1 0 (Std.lawBody t)
  let r := note r s!"LK1 a law in certifying shape checks: {chk boundedKeeps}; Std.keeps S le100 checks: {chk (Std.keeps S le100)}"
    (chk boundedKeeps && chk (Std.keeps S le100))
  let r := note r s!"LK2 a law whose write arm admits without the test does not check: {chk leaky}" (!chk leaky)
  let r := note r s!"LK3 a law that returns a verdict read from its state is not in shape: {chk readsVerdict}" (!chk readsVerdict)
  let r := note r s!"LK4 the journey's bounded (inline test) is not in shape yet (DESIGN-PCC §3.4): {chk bounded}" (!chk bounded)
  r

initialize register { name := "claims", run := pure claimSession }

end Nanodregg.Lang.Journey
