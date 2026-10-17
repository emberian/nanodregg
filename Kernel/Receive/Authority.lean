/-
# Kernel.Receive.Authority — whose authority a call exercises on a cell

Ownership (the cell's owner slot) or a grant chain that reaches the owner: the one rule every
receiver that changes a cell it does not bear uses (`Derive`'s writes, `Ledger`'s transfers).
-/
import Kernel.Receive.Call

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- Build slots in canonical order whatever order the pairs come in. -/
def slotsOf (ps : List (Nat × ByteArray)) : Slots := ps.foldl (fun s p => s.set p.1 p.2) []

/-- Whether the link `g` (its cell `cell`) is held by `agent`: its grantee is `agent`, or — when
`pub`, i.e. for the FIRST link only, held by the signer — its grantee is the World and `agent` is
an enrolled member, its member cell pinned and live (KERNEL-26: a public grant). Anything else is
`noGrant g`. A public grant is USED by any member, never re-delegated: a parent link is held by
its child's issuer exactly, the same rule `checkParent` applies when the child is made. -/
def granteeHolds (X : Ctx D) (look : Pinned D) (g : D) (cell : Cell) (agent : D) (pub : Bool) :
    Except (Refusal D) Unit := do
  let grantee ← slotDigest X g cell grantGrantee
  if grantee = agent then pure ()
  else if pub ∧ grantee = worldId X then (readKind look agent kindMember).map fun _ => ()
  else .error (.noGrant g)

/-- The principal a grant chain exercises for `agent`, walking at most `fuel` links: each link
pinned, live, aimed at `obj`, held by the next agent (`pub`: the first link may be a public
grant), carrying `right`. -/
def walk (X : Ctx D) (look : Pinned D) (obj : D) (right : Right) :
    Bool → Nat → D → D → Except (Refusal D) D
  | _, 0, _, _ => .error .grantTooDeep
  | pub, fuel + 1, g, agent => do
      let cell ← readKind look g kindGrant
      let target ← slotDigest X g cell grantTarget
      req (target = obj) (.grantTarget g)
      granteeHolds X look g cell agent pub
      req (cell.slots.get (rightKey right)).isSome (.grantRight g)
      let issuer ← slotDigest X g cell grantIssuer
      match cell.slots.get grantParent with
      | none => .ok issuer
      | some pb => match X.digestOf pb with
        | none => .error (.malformedCell g grantParent)
        | some parent => walk X look obj right false fuel parent issuer

/-- Whose authority a call exercises on `obj`: the signer's, or the root issuer of its grant. -/
def principalOf (X : Ctx D) (look : Pinned D) (u : Unsigned D) (obj : D) (right : Right) :
    Option D → Except (Refusal D) D
  | none => .ok u.member
  | some g => walk X look obj right true grantDepthMax g u.member

/-- Ownership authority (observe, mutate): the principal must be the object's owner. -/
def ownerAuthority (X : Ctx D) (look : Pinned D) (u : Unsigned D) (obj : D) (cell : Cell)
    (right : Right) (via : Option D) : Except (Refusal D) D := do
  let owner ← slotDigest X obj cell slotOwner
  let principal ← principalOf X look u obj right via
  req (principal = owner) (.noGrant obj)
  pure principal

end Nanodregg.Kernel.Receive
