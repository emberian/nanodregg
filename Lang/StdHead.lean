/-
# Lang.StdHead — a foreign World's head, held in this World (E5, plan §2(a))

An object of `headPackage` holds ONE head of another World A: A's origin (`world`, fixed at birth)
and either `at {height, roots, steps}` (the head a member of this World that follows A posted) or
`forked {held, other, steps}` (two posters disagreed at one step count: the object is frozen).

The head is keyed by STEPS, not height: a recorded refusal advances A's `steps` and changes its
refusals root at one height (`Kernel.World.steps`), so two honest heads at one height can differ.

The methods decide nothing: `post` writes `at arg`, `fork` writes `forked` naming the held roots.
The law `head` is the one decision (every change, whatever method wrote it):
* `world` changed: `otherWorld`;
* `at s` → `at s'`: `s' < s` is `staleHead`; `s' = s` with another height or roots is `forkedHead`;
  a lower height at a higher step count is `badHead` (an honest fold never lowers its height);
* `at` → `forked`: only naming the held roots at the held step count, with other roots (`badFork`);
* `forked` → anything else: `forkedHead` (frozen).
A receipt is checked against an `at` head (`Protocol.Foreign.check`); a forked head checks none.
-/
import Lang.Std
import Lang.StdData
import Lang.Program

namespace Nanodregg.Lang.Std

/-- A posted head: what `receipt CALL`'s `head STEPS HEIGHT ROOTS` line prints. -/
def headAtTy : Ty := .record [("height", .nat), ("roots", .digest), ("steps", .nat)]

/-- A recorded disagreement: the held roots, the other poster's, at one step count. -/
def headForkTy : Ty := .record [("held", .digest), ("other", .digest), ("steps", .nat)]

def headTy : Ty := .sum [("at", headAtTy), ("forked", headForkTy)]

/-- The head object's state: one field per slot, so a post is one judged step. -/
def headStateTy : Ty := .record [("head", headTy), ("world", .digest)]

def forkArgTy : Ty := .record [("other", .digest), ("steps", .nat)]

/-- From an `at` head (`var 1` the held, `var 0` the new): the step count never falls, an equal step
count keeps the head, the height never falls. -/
def headAtAt : Term :=
  let o : Term := .var 1
  let n : Term := .var 0
  guards
    [(.prim .le (.get o "steps") (.get n "steps"), "staleHead"),
     (.ite (.prim .eq (.get o "steps") (.get n "steps")) (eqData headAtTy o n) (.bool true), "forkedHead"),
     (.prim .le (.get o "height") (.get n "height"), "badHead")] okT

/-- From an `at` head to a recorded fork (`var 1` the held, `var 0` the fork): it names the held
roots, at the held step count, with other roots. -/
def headAtFork : Term :=
  let o : Term := .var 1
  let f : Term := .var 0
  allOf
    [(.prim .deq (.get f "held") (.get o "roots"), "badFork"),
     (.prim .eq (.get f "steps") (.get o "steps"), "badFork"),
     (notT (.prim .deq (.get f "other") (.get o "roots")), "badFork")]

/-- The head's change, by the held head's arm (`old`, `new` at `a`). -/
def headCase (a : At) : Term :=
  .case (a.oldF "head")
    [("at", .case (a.under.newF "head") [("at", headAtAt), ("forked", headAtFork)]),
     ("forked", guard (eqData headTy (a.under.oldF "head") (a.under.newF "head")) "forkedHead" okT)]

/-- The change clause, with `old` and `new` at `a`. -/
def headChange (a : At) : Term :=
  guard (.prim .deq (a.oldF "world") (a.newF "world")) "otherWorld" (headCase a)

/-- A seed (a birth, or this law added over a state) holds an `at` head. -/
def headSeed (a : At) : Term :=
  .case (a.newF "head") [("at", okT), ("forked", refusedT "badHead")]

/-- The law: `head`. -/
def headLaw : Term :=
  lawOf headStateTy headSeed headSeed (fun _ => refusedT "relaw") headChange

/-- `post (arg : headAtTy)`: the head becomes `at arg`. -/
def headPost : Term :=
  methodOf headStateTy headAtTy
    [("head", .inj headTy "at" (.var 1)), ("world", .get (.var 2) "world")]

/-- `fork (arg : {other, steps})`: the head becomes `forked`, naming the held roots. -/
def headFork : Term :=
  methodOf headStateTy forkArgTy
    [("head", .inj headTy "forked" (.record
        [("held", .case (.get (.var 2) "head")
            [("at", .get (.var 0) "roots"), ("forked", .get (.var 0) "held")]),
         ("other", .get (.var 1) "other"), ("steps", .get (.var 1) "steps")])),
     ("world", .get (.var 2) "world")]

/-- A head object's state as data. -/
def headSt (hd : Data) (w : ByteArray) : Data := .record [("head", hd), ("world", .digest w)]

def atRec (h : Nat) (r : ByteArray) (s : Nat) : Data :=
  .record [("height", .nat h), ("roots", .digest r), ("steps", .nat s)]

def forkRec (held other : ByteArray) (s : Nat) : Data :=
  .record [("held", .digest held), ("other", .digest other), ("steps", .nat s)]

/-- The package: method 0 `fork`, method 1 `post` (labels ascending), law `head`. -/
def headPackage : Package :=
  { pkgOf headStateTy [("head", headLaw)]
      [("fork", forkArgTy, [], headFork), ("post", headAtTy, [], headPost)] with
    doc := "a foreign World's head, keyed by steps; forkedHead freezes it (E5)".toUTF8 }

end Nanodregg.Lang.Std

namespace Nanodregg.Lang

/-- What a receipt is checked against: a head object's state, read from its cell. -/
inductive HeadView
  | at (world : ByteArray) (height : Nat) (roots : ByteArray) (steps : Nat)
  | forked (world : ByteArray)
  deriving DecidableEq, Repr

/-- The head object a cell is, if it is one: an object whose package slot holds `pkg` (the
deployed id of `Std.headPackage`), its state read at `headStateTy`. -/
def headView {D : Type} (digestOf : ByteArray → Option D) (pkg : ByteArray) (c : Kernel.Cell) :
    Option HeadView :=
  if c.kind ≠ Kernel.Receive.kindObject then none
  else if c.slots.get Kernel.Receive.slotPackage ≠ some pkg then none
  else
    match readState digestOf (recordRow Std.headStateTy) (c.slots.filter fun p => Kernel.Receive.stateBase ≤ p.1) with
    | .ok (.record [("head", .inj "at" (.record [("height", .nat h), ("roots", .digest r), ("steps", .nat s)])),
          ("world", .digest w)]) => some (.at w h r s)
    | .ok (.record [("head", .inj "forked" _), ("world", .digest w)]) => some (.forked w)
    | _ => none

end Nanodregg.Lang
