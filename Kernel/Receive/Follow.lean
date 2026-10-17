/-
# Kernel.Receive.Follow — who may follow the World, and the founders' genesis

The whole log is served only to a member holding a live World grant carrying `observe` whose
chain reaches a founder's root (PROTOCOL-3). Revoking any link revokes everything issued through
it. The founders' root grants (observe, enrol up to `enrollMax`) and member cells are the genesis
World; nothing else is trusted without a signature.
-/
import Kernel.Receive.Derive
import Codec.Raw

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

def domFounder : String := "nanodregg/kernel/founder/v2"
def domFounderGrant : String := "nanodregg/kernel/founder-grant/v2"
def domOrigin : String := "nanodregg/kernel/origin/v1"

/-- What a genesis is made from, as CODEC's raw combinators write it: the name, HOST's nonce, the
allowance, and each founder's key and next-key digest bytes, in order. -/
abbrev GenesisInput := ByteArray × ByteArray × Nat × List (ByteArray × ByteArray)

open Nanodregg.Codec Nanodregg.Codec.Stream in
def genesisInput : Stream GenesisInput :=
  product (rawBytes Bounds.eventBytesMax) (product (rawBytes Bounds.eventBytesMax) (product nat64
    (rawList Bounds.eventBytesMax (product (rawBytes Bounds.eventBytesMax) (rawBytes Bounds.eventBytesMax)))))

def inputOf (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    GenesisInput :=
  (name, nonce, allowance, founders.map fun f => (f.1, X.env.bytes f.2))

/-- The World's identity (KERNEL-24): the digest of everything its genesis is made from. -/
def originOf (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) : D :=
  X.env.hash domOrigin (genesisInput.bytes (inputOf X name nonce allowance founders))

/-- Founder ids are keyed by the World's ORIGIN, so two Worlds with one name share no member id. -/
def founderId (X : Ctx D) (origin : D) (i : Nat) : D :=
  X.env.hash domFounder (X.env.bytes origin ++ index32 i)

def founderGrantId (X : Ctx D) (origin : D) (i : Nat) : D :=
  X.env.hash domFounderGrant (X.env.bytes origin ++ index32 i)

def founderMember (X : Ctx D) (f : ByteArray × D) : Cell :=
  { kind := kindMember, discipline := .ram, slots := slotsOf [(slotKey, f.1), (slotNext, X.env.bytes f.2)] }

/-- A founder's root World grant: it may follow and enrol `enrollMax` members, and every World
right in the World is attenuated from one of these (`unrooted` refuses any other root). -/
def founderRoot (X : Ctx D) (member : D) : Cell :=
  { kind := kindGrant, discipline := .appendOnly,
    slots := slotsOf ([(grantTarget, X.env.bytes (worldId X)), (grantGrantee, X.env.bytes member),
      (grantIssuer, X.env.bytes member)] ++ rightSlots [.observe, .enroll enrollMax]) }

/-- The genesis World: founders `(key, digest of next key)` as members, each with a root World
grant; its origin commits to the name, HOST's `nonce`, the allowance and the founders. -/
def genesis (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    World D :=
  let o := originOf X name nonce allowance founders
  let w := World.genesis X.env o allowance
  let place := fun (m : Std.TreeMap D Entry compare) (p : (ByteArray × D) × Nat) =>
    (m.insert (founderId X o p.2) (.live (founderMember X p.1))).insert
      (founderGrantId X o p.2) (.live (founderRoot X (founderId X o p.2)))
  { w with cells := founders.zipIdx.foldl place w.cells }

end Nanodregg.Kernel.Receive
