/-
# Protocol.Use — objects made by one member and used by another (PROTOCOL-43)

THE BAR measures speed. It does not measure whether anyone uses what someone else made, and
delvetalk's lesson was that the machinery worked and the residents still left (DELVETALK-LEARNINGS
§4.7, §7; its playtest's go/no-go: "resident-made things used by a resident other than their maker,
at least 4"). This is that count, over the calls a World committed and the World itself:

* a call USES an object when it invokes it or writes it (`usedBy`: the signing member, the object;
  only the call's own body: a use made by a call inside a method's run is not counted);
* an object's MAKER is its owner slot (`Receive.slotOwner`), which the kernel sets to the actor of
  its `create` and no act changes, when that owner is a live MEMBER. An object made inside another
  object's run is owned by that object and has no maker here, so it is never counted;
* `shared` lists the distinct objects some call of a member other than the maker uses.

It counts by the MEMBER a call is signed for, read from the call, never by who ran a command. Calls
each signed for the maker of what they use count 0 (`Proofs.Use.shared_self`); a run of one resident
playing every part is such a run, which the plant `oneMember` shows for the row `use`, not a
theorem. Every gap errs LOW: a dead object, an object's object, a nested use.
-/
import Kernel.Receive.Call

namespace Nanodregg.Protocol.Use

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- The member a call is signed for and the object it uses, if it uses one. -/
def usedBy (c : Call D) : Option (D × D) :=
  match c.unsigned.body with
  | .invoke obj .. => some (c.unsigned.member, obj)
  | .write obj .. => some (c.unsigned.member, obj)
  | _ => none

/-- An object's maker: the owner in its slot, if the object is live and the owner is a live member. -/
def makerOf (X : Ctx D) (w : World D) (obj : D) : Option D :=
  (w.live X.env obj).bind fun c => (c.slots.get slotOwner).bind X.digestOf |>.bind fun o =>
    match w.live X.env o with
    | some m => if m.kind = kindMember then some o else none
    | none => none

/-- The object a call uses, if a member other than its maker signed the call. -/
def sharedBy (X : Ctx D) (w : World D) (c : Call D) : Option D :=
  (usedBy c).bind fun (m, o) =>
    match makerOf X w o with
    | some maker => if maker = m then none else some o
    | none => none

/-- A list's distinct items (each kept at its last occurrence). -/
def uniq : List D → List D
  | [] => []
  | x :: xs => if x ∈ uniq xs then uniq xs else x :: uniq xs

/-- The distinct objects made by one member and used by another, over committed calls. -/
def shared (X : Ctx D) (w : World D) (calls : List (Call D)) : List D :=
  uniq (calls.filterMap (sharedBy X w))

end Nanodregg.Protocol.Use
