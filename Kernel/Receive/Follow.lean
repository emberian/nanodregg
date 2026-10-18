/-
# Kernel.Receive.Follow — who may follow the World, and the founders' genesis

The whole log is served only to a member holding a live World grant carrying `observe` whose
chain reaches a founder's root (PROTOCOL-3). Revoking any link revokes everything issued through
it. The founders' root grants (observe, enrol up to `enrollMax`) and member cells are the genesis
World; nothing else is trusted without a signature. `genesis` refuses, by name, an input past the
raw codec's bounds (`GenesisRefusal`), so the origin commits to everything genesis was made from.
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
  match walk X (fun c => .ok (w.live X.env c)) (worldId X) .observe true grantDepthMax g member with
  | .ok _ => true
  | .error _ => false

def domFounder : String := "nanodregg/kernel/founder/v2"
def domFounderGrant : String := "nanodregg/kernel/founder-grant/v2"
def domOrigin : String := "nanodregg/kernel/origin/v2"

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

/-- What a carry is made from (KERNEL-29), as CODEC's raw combinators write it: the name, HOST's
nonce, the exported World's origin bytes, the carried trie's root bytes, the allowance, the
height, and the journal listing (each entry's id bytes, height, turn-digest bytes, in trie order). -/
abbrev CarryInput := ByteArray × ByteArray × ByteArray × ByteArray × Nat × Nat × List (ByteArray × Nat × ByteArray)

open Nanodregg.Codec Nanodregg.Codec.Stream in
def carryInput : Stream CarryInput :=
  product (rawBytes Bounds.eventBytesMax) (product (rawBytes Bounds.eventBytesMax)
    (product (rawBytes Bounds.eventBytesMax) (product (rawBytes Bounds.eventBytesMax) (product nat64
      (product nat64 (rawList Bounds.journalMax
        (product (rawBytes Bounds.eventBytesMax) (product nat64 (rawBytes Bounds.eventBytesMax)))))))))

open Nanodregg.Codec Nanodregg.Codec.Stream in
/-- A World's identity input: a genesis's or a carry's, under one domain, the case tagged by one
byte, so a carry's origin is never a genesis's without a collision of the origin hash
(`carry_origin_ne_genesis`). -/
def originInput : Stream (GenesisInput ⊕ CarryInput) := sum genesisInput carryInput

/-- The World's identity (KERNEL-24): the digest of everything its genesis is made from. -/
def originOf (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) : D :=
  X.env.hash domOrigin (originInput.bytes (.inl (inputOf X name nonce allowance founders)))

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

/-- Each founder's member cell, then its root World grant. -/
def founderEntries (X : Ctx D) (o : D) (founders : List (ByteArray × D)) : List (D × Entry) :=
  founders.zipIdx.flatMap fun p =>
    [(founderId X o p.2, .live (founderMember X p.1)),
     (founderGrantId X o p.2, .live (founderRoot X (founderId X o p.2)))]

/-- The World a genesis builds, UNCHECKED: founders `(key, digest of next key)` as members, each
with a root World grant; its origin commits to the name, HOST's `nonce`, the allowance and the
founders. Only `genesis` calls it on the request path; the theorems about the genesis World are
stated over it (`genesis_ok` says `genesis` returns exactly it). -/
def genesisWorld (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    World D :=
  let o := originOf X name nonce allowance founders
  let w := World.genesis X.env o allowance
  { w with trie := insertAll X.env w.trie (founderEntries X o founders) }

/-- Why a genesis is refused (law 7): one constructor per clause of `GenesisFits`, in its order.
Past these bounds `genesisInput`'s raw codec truncates, so two different geneses would share one
origin with no hash collision (KERNEL-31). -/
inductive GenesisRefusal
  | nameTooLong
  | nonceTooLong
  | tooManyFounders
  /-- founder `index`'s key is longer than `Bounds.eventBytesMax` -/
  | founderKeyTooLong (index : Nat)
  /-- founder `index`'s next-key digest bytes are longer than `Bounds.eventBytesMax` -/
  | founderNextTooLong (index : Nat)
  /-- the allowance plus the genesis World's storage is not below 2^64: past it a retirement's credit
  could carry the allowance out of the World codec's `u64` (cv 01a14ba9-cbf4). Checked last, so the
  World is weighed only once every founder is within bounds. -/
  | allowanceTooLarge
  deriving DecidableEq, Repr

/-- The refusal's name on the wire: its constructor's, arguments dropped. -/
def GenesisRefusal.name : GenesisRefusal → String
  | .nameTooLong => "nameTooLong"
  | .nonceTooLong => "nonceTooLong"
  | .allowanceTooLarge => "allowanceTooLarge"
  | .tooManyFounders => "tooManyFounders"
  | .founderKeyTooLong _ => "founderKeyTooLong"
  | .founderNextTooLong _ => "founderNextTooLong"

/-- Each founder from index `i` on: its key, then its next-key digest bytes. -/
def checkFounders (X : Ctx D) : Nat → List (ByteArray × D) → Except GenesisRefusal Unit
  | _, [] => .ok ()
  | i, f :: rest => do
      req (f.1.size ≤ Bounds.eventBytesMax) (.founderKeyTooLong i)
      req ((X.env.bytes f.2).size ≤ Bounds.eventBytesMax) (.founderNextTooLong i)
      checkFounders X (i + 1) rest

/-- The genesis input is within the raw codec's bounds, checked in `GenesisFits`'s order
(`checkGenesis_ok`). -/
def checkGenesis (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    Except GenesisRefusal Unit := do
  req (name.size ≤ Bounds.eventBytesMax) .nameTooLong
  req (nonce.size ≤ Bounds.eventBytesMax) .nonceTooLong
  req (founders.length ≤ Bounds.eventBytesMax) .tooManyFounders
  checkFounders X 0 founders
  req ((genesisWorld X name nonce allowance founders).weight + allowance < Bounds.counterLimit) .allowanceTooLarge

/-- THE genesis: refused by name outside `GenesisFits`, else `genesisWorld` (`genesis_ok`). -/
def genesis (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) :
    Except GenesisRefusal (World D) := do
  checkGenesis X name nonce allowance founders
  pure (genesisWorld X name nonce allowance founders)

/-! ## Carry (KERNEL-29): a new World from a carried state -/

def carryInputOf (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) : CarryInput :=
  (name, nonce, X.env.bytes fromOrigin, X.env.bytes (c.trie.hashOf (trieSpec X.env)), c.allowance, c.height,
    c.journal.toList.map fun p => (X.env.bytes p.1, p.2.1, X.env.bytes p.2.2))

/-- A carried World's identity: everything the carry is made from, the trie by its root. -/
def carryOriginOf (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) : D :=
  X.env.hash domOrigin (originInput.bytes (.inr (carryInputOf X name nonce fromOrigin c)))

/-- The World a carry builds, UNCHECKED: the carried state under a new origin, its chain at
`genesisChain` of that origin. No founders: the members are the carried member cells, and their
keys sign the new World's calls (`Unsigned.world` = the new origin). -/
def carryWorld (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) : World D :=
  let o := carryOriginOf X name nonce fromOrigin c
  { trie := c.trie, journal := c.journal, refusals := .empty, height := c.height, steps := c.height,
    chain := World.genesisChain X.env o, allowance := c.allowance, origin := o }

/-- Why a carry is refused (law 7): one constructor per clause of `CarryFits`, in its order. Past
these bounds `carryInput`'s raw codec truncates, so two different carries would share an origin. -/
inductive CarryRefusal
  | nameTooLong
  | nonceTooLong
  /-- the carried allowance plus the carried cells' storage is not below 2^64 (`fold_conserves` keeps
  that sum, so no later retirement can overflow the allowance; cv 01a14ba9-cbf4) -/
  | allowanceTooLarge
  | heightTooLarge
  | journalTooLong
  /-- a digest's bytes (the exported origin, the root, a journal entry's) are longer than
  `Bounds.eventBytesMax`, or an entry's height is past the counter limit -/
  | entryTooLarge
  deriving DecidableEq, Repr

def CarryRefusal.name : CarryRefusal → String
  | .nameTooLong => "nameTooLong"
  | .nonceTooLong => "nonceTooLong"
  | .allowanceTooLarge => "allowanceTooLarge"
  | .heightTooLarge => "heightTooLarge"
  | .journalTooLong => "journalTooLong"
  | .entryTooLarge => "entryTooLarge"

/-- The carry input is within the raw codec's bounds (`checkCarry_ok`). -/
def checkCarry (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) : Except CarryRefusal Unit := do
  req (name.size ≤ Bounds.eventBytesMax) .nameTooLong
  req (nonce.size ≤ Bounds.eventBytesMax) .nonceTooLong
  req (cellsWeight c.trie + c.allowance < Bounds.counterLimit) .allowanceTooLarge
  req (c.height < Bounds.counterLimit) .heightTooLarge
  req (c.journal.toList.length ≤ Bounds.journalMax) .journalTooLong
  req ((X.env.bytes fromOrigin).size ≤ Bounds.eventBytesMax &&
      (X.env.bytes (c.trie.hashOf (trieSpec X.env))).size ≤ Bounds.eventBytesMax &&
      c.journal.toList.all fun p => (X.env.bytes p.1).size ≤ Bounds.eventBytesMax &&
        p.2.1 < Bounds.counterLimit && (X.env.bytes p.2.2).size ≤ Bounds.eventBytesMax) .entryTooLarge

/-- THE carry: refused by name outside `CarryFits`, else `carryWorld` (`carry_ok`). `fromOrigin`
is the exported World's origin (its lineage, committed in the new origin). -/
def carry (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) :
    Except CarryRefusal (World D) := do
  checkCarry X name nonce fromOrigin c
  pure (carryWorld X name nonce fromOrigin c)

end Nanodregg.Kernel.Receive
