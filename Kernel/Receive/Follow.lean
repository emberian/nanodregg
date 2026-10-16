/-
# Kernel.Receive.Follow — who may follow the World, and the founders' genesis

The whole log is served only to a member holding a live follow grant whose chain reaches a root
(PROTOCOL-3). Revoking any link revokes everything issued through it. The founders' root grants
and member cells are the genesis World; nothing else is trusted without a signature.
-/
import Kernel.Receive.Derive

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

def digestAt (X : Ctx D) (cell : Cell) (key : Nat) : Option D := cell.slots.get key >>= X.digestOf

/-- A live follow grant `g` held by `member`, every link up to a root live too. -/
def followChain (X : Ctx D) (w : World D) : Nat → D → D → Bool
  | 0, _, _ => false
  | fuel + 1, g, member =>
      match w.live g with
      | none => false
      | some cell =>
          cell.kind = kindFollow && digestAt X cell grantGrantee = some member &&
            match cell.slots.get grantParent with
            | none => true
            | some pb => match X.digestOf pb, digestAt X cell grantIssuer with
              | some parent, some issuer => followChain X w fuel parent issuer
              | _, _ => false

/-- HOST's gate for `log` and whole-World `read`. -/
def mayFollow (X : Ctx D) (w : World D) (member g : D) : Bool :=
  followChain X w grantDepthMax g member

def domFounder : String := "nanodregg/kernel/founder/v1"
def domFounderFollow : String := "nanodregg/kernel/founder-follow/v1"

def founderId (X : Ctx D) (name : ByteArray) (i : Nat) : D :=
  X.env.hash domFounder (name ++ index32 i)

def founderFollowId (X : Ctx D) (name : ByteArray) (i : Nat) : D :=
  X.env.hash domFounderFollow (name ++ index32 i)

def founderMember (X : Ctx D) (f : ByteArray × D) : Cell :=
  { kind := kindMember, discipline := .ram, slots := slotsOf [(slotKey, f.1), (slotNext, X.env.bytes f.2)] }

def founderRoot (X : Ctx D) (member : D) : Cell :=
  { kind := kindFollow, discipline := .appendOnly,
    slots := slotsOf [(grantGrantee, X.env.bytes member), (grantIssuer, X.env.bytes member)] }

/-- The genesis World: founders `(key, digest of next key)` as members, each with a root follow
grant. -/
def genesis (X : Ctx D) (name : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    World D :=
  let w := World.genesis X.env name allowance
  let place := fun (m : Std.TreeMap D Entry compare) (p : (ByteArray × D) × Nat) =>
    (m.insert (founderId X name p.2) (.live (founderMember X p.1))).insert
      (founderFollowId X name p.2) (.live (founderRoot X (founderId X name p.2)))
  { w with cells := founders.zipIdx.foldl place w.cells }

end Nanodregg.Kernel.Receive
