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

/-- The principal a grant chain exercises for `agent`, walking at most `fuel` links: each link
pinned, live, aimed at `obj`, held by the next agent, carrying `right`. -/
def walk (X : Ctx D) (look : Pinned D) (obj : D) (right : Right) :
    Nat → D → D → Except (Refusal D) D
  | 0, _, _ => .error .grantTooDeep
  | fuel + 1, g, agent => do
      let cell ← readKind look g kindGrant
      let target ← slotDigest X g cell grantTarget
      req (target = obj) (.grantTarget g)
      let grantee ← slotDigest X g cell grantGrantee
      req (grantee = agent) (.noGrant g)
      req (cell.slots.get (rightKey right)).isSome (.grantRight g)
      let issuer ← slotDigest X g cell grantIssuer
      match cell.slots.get grantParent with
      | none => .ok issuer
      | some pb => match X.digestOf pb with
        | none => .error (.malformedCell g grantParent)
        | some parent => walk X look obj right fuel parent issuer

/-- Whose authority a call exercises on `obj`: the signer's, or the root issuer of its grant. -/
def principalOf (X : Ctx D) (look : Pinned D) (u : Unsigned D) (obj : D) (right : Right) :
    Option D → Except (Refusal D) D
  | none => .ok u.member
  | some g => walk X look obj right grantDepthMax g u.member

/-- Ownership authority (observe, mutate): the principal must be the object's owner. -/
def ownerAuthority (X : Ctx D) (look : Pinned D) (u : Unsigned D) (obj : D) (cell : Cell)
    (right : Right) (via : Option D) : Except (Refusal D) D := do
  let owner ← slotDigest X obj cell slotOwner
  let principal ← principalOf X look u obj right via
  req (principal = owner) (.noGrant obj)
  pure principal

end Nanodregg.Kernel.Receive
