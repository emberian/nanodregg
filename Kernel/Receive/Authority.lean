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

/-- Whose authority an actor exercises on `obj`: its own, or the root issuer of its grant. -/
def principalOf (X : Ctx D) (look : Pinned D) (actor : D) (obj : D) (right : Right) :
    Option D → Except (Refusal D) D
  | none => .ok actor
  | some g => walk X look obj right true grantDepthMax g actor

/-- Ownership authority (observe, mutate): the principal must be the object's owner. -/
def ownerAuthority (X : Ctx D) (look : Pinned D) (actor : D) (obj : D) (cell : Cell)
    (right : Right) (via : Option D) : Except (Refusal D) D := do
  let owner ← slotDigest X obj cell slotOwner
  let principal ← principalOf X look actor obj right via
  req (principal = owner) (.noGrant obj)
  pure principal

/-! ## Counted rights: one ledger mechanism (KERNEL-16's enrolment, KERNEL-60's transfer and credit) -/

/-- The ledger of a grant's counted right whose first slot is `base`: its next index and what is
left (its last entry). `grantRight` when the grant carries no such right. -/
def ledgerLeft (base : Nat) (g : D) (cell : Cell) : Except (Refusal D) (Nat × Nat) :=
  let led := cell.slots.filter fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax
  match led.getLast? with
  | none => .error (.grantRight g)
  | some (k, v) => match countOf v with
    | some n => .ok (led.length, n)
    | none => .error (.malformedCell g k)

/-- Spend `units` of grant `g`'s counted right at `base` (refused `short` past what is left, and
past the ledger's last slot: a spend is never written where `ledgerLeft` does not read): the write
appending what is left to its ledger, or no effect for nothing. -/
def spendAt (base : Nat) (g : D) (cell : Cell) (units : Nat) (short : Refusal D) :
    Except (Refusal D) (Option (D × Act)) := do
  let (i, left) ← ledgerLeft base g cell
  req (units ≤ left) short
  if units = 0 then pure none else do
    req (decide (i ≤ ledgerSpendsMax)) short
    pure (some (g, .write [.set (base + i) (countBytes (left - units))]))

/-- A use of a counted right through `via` (none: the owner's own authority, nothing to spend): the
pinned live grant's spend of `units` at `base`, refused `short g` past it. -/
def spendVia (look : Pinned D) (base : Nat) (via : Option D) (units : Nat) (short : D → Refusal D) :
    Except (Refusal D) (Option (D × Act)) :=
  match via with
  | none => pure none
  | some g => do
      let gc ← readKind look g kindGrant
      spendAt base g gc units (short g)

end Nanodregg.Kernel.Receive
