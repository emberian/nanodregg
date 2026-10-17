/-
# Kernel.Receive.Follow — who may follow the World, and the founders' genesis

The whole log is served only to a member holding a live World grant carrying `observe` whose
chain reaches a founder's root (PROTOCOL-3). Revoking any link revokes everything issued through
it. The founders' root grants (observe, enrol up to `enrollMax`) and member cells are the genesis
World; nothing else is trusted without a signature.
-/
import Kernel.Receive.Derive

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

def digestAt (X : Ctx D) (cell : Cell) (key : Nat) : Option D := cell.slots.get key >>= X.digestOf

/-- HOST's gate for `log` and whole-World `read`: `g` is a live World grant held by `member`
carrying `observe`, every link up to a founder's genesis grant live too. The same `walk` as every
other right, over the whole World (a follower's request pins nothing). -/
def mayFollow (X : Ctx D) (w : World D) (member g : D) : Bool :=
  match walk X (fun c => .ok (w.live c)) (worldId X) .observe true grantDepthMax g member with
  | .ok _ => true
  | .error _ => false

def domFounder : String := "nanodregg/kernel/founder/v1"
def domFounderGrant : String := "nanodregg/kernel/founder-grant/v1"

def founderId (X : Ctx D) (name : ByteArray) (i : Nat) : D :=
  X.env.hash domFounder (name ++ index32 i)

def founderGrantId (X : Ctx D) (name : ByteArray) (i : Nat) : D :=
  X.env.hash domFounderGrant (name ++ index32 i)

def founderMember (X : Ctx D) (f : ByteArray × D) : Cell :=
  { kind := kindMember, discipline := .ram, slots := slotsOf [(slotKey, f.1), (slotNext, X.env.bytes f.2)] }

/-- A founder's root World grant: it may follow and enrol `enrollMax` members, and every World
right in the World is attenuated from one of these (`unrooted` refuses any other root). -/
def founderRoot (X : Ctx D) (member : D) : Cell :=
  { kind := kindGrant, discipline := .appendOnly,
    slots := slotsOf ([(grantTarget, X.env.bytes (worldId X)), (grantGrantee, X.env.bytes member),
      (grantIssuer, X.env.bytes member)] ++ rightSlots [.observe, .enroll enrollMax]) }

/-- The genesis World: founders `(key, digest of next key)` as members, each with a root World
grant. -/
def genesis (X : Ctx D) (name : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    World D :=
  let w := World.genesis X.env name allowance
  let place := fun (m : Std.TreeMap D Entry compare) (p : (ByteArray × D) × Nat) =>
    (m.insert (founderId X name p.2) (.live (founderMember X p.1))).insert
      (founderGrantId X name p.2) (.live (founderRoot X (founderId X name p.2)))
  { w with cells := founders.zipIdx.foldl place w.cells }

end Nanodregg.Kernel.Receive
