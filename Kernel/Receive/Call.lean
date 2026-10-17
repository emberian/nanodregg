/-
# Kernel.Receive.Call — the signed call, the receive refusals, the pinned view, the seal

A receiver derives a `Turn` from a signed call; the Host then commits `World.admit` of exactly
that Turn (derive-then-admit). There is no intermediate intent type.

A receiver never sees the World. It sees the `Pinned` view: the live cell at an id the caller
PINNED, and the refusal `unpinned` for any other id. So a derivation depends only on the cells
the signer observed (`Kernel.Proofs.Receive.receive_congr`): a member's own follow derives the
same Turn the Host does whenever their pinned cells agree, and `World.admit`'s pin check refuses
the Turn when the Host's cells are not what the signer saw.

Identity is a MEMBER cell (its id is stable; its key rotates). A call names its member and the
key it signs with; the key must be the member's current one (`unknownKey`), except for `rotate`,
which is signed by the precommitted next key (`notPrecommitted`).
-/
import Kernel.World

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

/-- A right a grant can carry. -/
inductive Right
  /-- read the cell -/
  | observe
  /-- write state slots and replace laws of a data object -/
  | mutate
  /-- run a method of a programmed object -/
  | invoke (method : Nat)
  /-- enrol at most `count` members, directly or through grants carved from this one (meaningful
  on the World target only: a World right is only ever attenuated from a founder's, KERNEL-16) -/
  | enroll (count : Nat)
  deriving DecidableEq, Repr

/-- What a call asks for, one constructor per operation kind. -/
inductive Body (D : Type)
  /-- the signer sponsors a new member with `key`, precommitting the digest of its next key;
  `possession` is the new key's signature over the enrolment; `via` is the signer's World grant
  carrying `Right.enroll`, whose count the enrolment spends -/
  | enroll (key : ByteArray) (next : D) (possession : ByteArray) (via : D)
  /-- the signer's member moves to `key`, which must be the precommitted one, and precommits
  `next`; the call is signed by `key` -/
  | rotate (key : ByteArray) (next : D)
  /-- install a package: canonical package bytes (LANG's encoding) -/
  | install (pkg : ByteArray)
  /-- birth an object owned by the signer: programmed by `pkg`, or a data object without one;
  judged by `laws` (and the package's) from birth -/
  | create (pkg : Option D) (laws : List D) (state : Slots)
  /-- set (`some`) or erase (`none`) state slots of a data object -/
  | write (obj : D) (edits : List (Nat × Option ByteArray)) (via : Option D)
  /-- replace a data object's extra laws (judged by the laws in force) -/
  | law (obj : D) (laws : List D) (via : Option D)
  /-- run `method` of a programmed object -/
  | invoke (obj : D) (method : Nat) (args : ByteArray) (budget : Nat) (via : Option D)
  /-- let member `grantee` exercise `rights` on `target` for the signer (or, through `parent`, for
  that grant's principal, attenuated). A grant on the World (`worldId`) is how a member may
  follow (`observe`) and enrol (`enroll n`); it always has a parent -/
  | grant (target : D) (grantee : D) (rights : List Right) (parent : Option D)
  /-- retire a grant the signer issued -/
  | revoke (grant : D)
  /-- bear a new denomination: its WELL, a value account owned by the signer whose id is the
  denomination and whose floor is `cap`, the most that can ever be outstanding of it (LEDGER-3) -/
  | issue (cap : Nat)
  /-- bear an empty account of `asset`'s denomination (the well's id), owned by the signer -/
  | account (asset : D)
  /-- move `amount` from `src` to `dst` (same denomination), with the authority of `src`'s owner
  (directly, or through `via`'s grant chain for `mutate`); `once` spends the nullifier
  `onceNullifier src key`, so a call carrying the same key for the same source lands once.
  Minting is a transfer out of a well, burning one into it -/
  | transfer (src dst : D) (amount : Nat) (via : Option D) (once : Option ByteArray)
  /-- a credit line: move `amount` of the well's floor to `acct` (same denomination), with the
  authority of the well's owner, the issuer (directly, or through `via` for `mutate`). The
  denomination's floor sum is unchanged, so its cap still bounds what is outstanding (LEDGER-4) -/
  | credit (well acct : D) (amount : Nat) (via : Option D)
  deriving DecidableEq

/-- What the caller signs. `pins` is the caller's observation; `maxCharge` the price ceiling. -/
structure Unsigned (D : Type) where
  /-- the World this call is for: its genesis origin (KERNEL-24); checked first, `wrongWorld` -/
  world : D
  member : D
  key : ByteArray
  notBefore : Nat
  validUntil : Nat
  pins : List (D × D)
  maxCharge : Nat
  body : Body D
  deriving DecidableEq

structure Call (D : Type) where
  unsigned : Unsigned D
  signature : ByteArray
  deriving DecidableEq

/-- Every receive refusal, by name (law 7). Kernel refusals come later, from `World.admit`. -/
inductive Refusal (D : Type)
  /-- the call names another World (`Unsigned.world ≠ w.origin`, KERNEL-24) -/
  | wrongWorld
  | badSignature
  /-- the member does not exist, or the key is not its current one -/
  | unknownKey (member : D)
  /-- a rotation to a key whose digest is not the precommitted one -/
  | notPrecommitted (member : D)
  /-- the enrolled key did not sign its own enrolment -/
  | badPossession
  /-- the derivation needed a cell the caller did not pin -/
  | unpinned (cell : D)
  | missingCell (cell : D)
  | wrongKind (cell : D) (expected : Nat)
  /-- a slot the receive layer reads does not hold what it must -/
  | malformedCell (cell : D) (key : Nat)
  /-- the law of package `law` refused the write, with LANG's name for why -/
  | lawDenied (law : D) (reason : String)
  /-- LANG refused for a reason that is not a law: type error, budget, method error -/
  | program (reason : String)
  /-- a state slot below `stateBase`, or an edit key past `Bounds.slotKeyLimit` -/
  | stateKey (key : Nat)
  | tooManyLaws
  /-- a write or law change on a programmed object (its state moves only by its methods) -/
  | hasMethods (obj : D)
  /-- an invoke on a data object -/
  | noMethods (obj : D)
  /-- the signer neither owns the object nor acts through a grant that reaches its owner -/
  | noGrant (cell : D)
  | grantTarget (grant : D)
  | grantRight (grant : D)
  /-- an attenuated grant may only narrow its parent (rights, and an enrolment count within what
  the parent has left) -/
  | grantWidens (parent : D)
  /-- a grant on the World, or one carrying `enroll`, without a parent: World rights are only
  ever attenuated from the founders' genesis grants -/
  | unrooted (target : D)
  /-- the grant's enrolment count is used up -/
  | enrollSpent (grant : D)
  | notIssuer (grant : D)
  | grantTooDeep
  | overPrice (charge : Nat)
  /-- a logged event is not a canonical call (the follower's re-derivation, `rederive`) -/
  | undecodableEvent
  /-- a logged Turn is not what its own event derives on the World before it -/
  | eventMismatch
  /-- a receiver gave one cell two effects (no receiver does: a probe meets it) -/
  | duplicateEffect (cell : D)
  /-- a transfer from an account to itself -/
  | sameAccount
  /-- a transfer of nothing -/
  | zeroAmount
  /-- a transfer between accounts of different denominations (names the destination) -/
  | assetMismatch (cell : D)
  /-- a post balance an `i64` cannot hold, or an issuance cap past `2^63` -/
  | overflow (cell : D)
  /-- a credit line out of an account that is not a well (its denomination is not its own id) -/
  | notWell (cell : D)
  deriving DecidableEq, Repr

/-- The refusal's name on the wire (law 7): its constructor's, arguments dropped
(`Refusal.name_injective`). -/
def Refusal.name {D : Type} : Refusal D → String
  | .wrongWorld => "wrongWorld"
  | .badSignature => "badSignature"
  | .unknownKey _ => "unknownKey"
  | .notPrecommitted _ => "notPrecommitted"
  | .badPossession => "badPossession"
  | .unpinned _ => "unpinned"
  | .missingCell _ => "missingCell"
  | .wrongKind _ _ => "wrongKind"
  | .malformedCell _ _ => "malformedCell"
  | .lawDenied _ _ => "lawDenied"
  | .program _ => "program"
  | .stateKey _ => "stateKey"
  | .tooManyLaws => "tooManyLaws"
  | .hasMethods _ => "hasMethods"
  | .noMethods _ => "noMethods"
  | .noGrant _ => "noGrant"
  | .grantTarget _ => "grantTarget"
  | .grantRight _ => "grantRight"
  | .grantWidens _ => "grantWidens"
  | .unrooted _ => "unrooted"
  | .enrollSpent _ => "enrollSpent"
  | .notIssuer _ => "notIssuer"
  | .grantTooDeep => "grantTooDeep"
  | .overPrice _ => "overPrice"
  | .undecodableEvent => "undecodableEvent"
  | .eventMismatch => "eventMismatch"
  | .duplicateEffect _ => "duplicateEffect"
  | .sameAccount => "sameAccount"
  | .zeroAmount => "zeroAmount"
  | .assetMismatch _ => "assetMismatch"
  | .overflow _ => "overflow"
  | .notWell _ => "notWell"

/-- A receiver's only access to state: live cells at pinned ids. -/
abbrev Pinned (D : Type) := D → Except (Refusal D) (Option Cell)

/-- Which act the laws in force are judging. A law sees `old` and `new` state; without the
occasion a birth (`create` judges the seed as `old = new`) and a law replacement (`law` judges the
unchanged state) look exactly like a no-op write, so a transition law admitting no-ops admitted a
seeded birth and its own removal (ASSEMBLY-lang-docs H1/H2). -/
inductive Occasion (D : Type)
  /-- `create`: `old = new` is the seed -/
  | birth
  /-- `write` on a data object -/
  | write
  /-- `law` on a data object: the laws in force judge their replacement by `laws` (state unchanged) -/
  | relaw (laws : List D)
  /-- `law` on a data object: each INCOMING law judges the state it is adopted over, knowing the
  whole incoming list `laws` (KERNEL-27; a law that refuses `relaw` may still accept its own
  adoption, and adoption onto a populated object is not a birth) -/
  | adopt (laws : List D)
  /-- `invoke` of method `method` -/
  | invoke (method : Nat)
  deriving DecidableEq

/-- Who a call acts for, as member ids: `agent` signed; `principal` is whose authority it
exercises (the agent, or the root issuer of the grant chain). Laws judge by these. -/
structure Req (D : Type) where
  agent : D
  principal : D
  /-- the call's signed window: the Turn lands at a height in `[notBefore, validUntil]`
  (`World.admit` enforces it), so a law can say "not before h" without reading the World -/
  notBefore : Nat
  validUntil : Nat
  /-- the act being judged -/
  occasion : Occasion D
  deriving DecidableEq

/-- What KERNEL's receivers need from LANG. Every function reads state only through the pinned
view, so `receive_congr` covers LANG's reads too. LANG's glue module instantiates it. -/
structure Program (D : Type) where
  /-- type-check canonical package bytes against their (pinned) imports -/
  checkInstall : Pinned D → ByteArray → Except (Refusal D) Unit
  /-- every law in force (the package's, if any, then the extra `laws`) admits `old → new` -/
  judge : Pinned D → (pkg : Option D) → (laws : List D) → (old new : Slots) → Req D →
    Except (Refusal D) Unit
  /-- run a method; the new state slots (the receiver then judges them) -/
  run : Pinned D → (pkg : D) → (state : Slots) → (method : Nat) → (args : ByteArray) → Req D →
    (budget : Nat) → Except (Refusal D) Slots

/-- What the receive layer needs beyond the kernel's `Env`: the call's canonical bytes (the
signed message and the logged event), the digest decoder, the verifier, the program. CODEC
supplies the encodings; the verifier's answer is a premise asserted where it enters (law 4). -/
structure Ctx (D : Type) where
  env : Env D
  unsignedBytes : Unsigned D → ByteArray
  callBytes : Call D → ByteArray
  /-- inverse of `callBytes` on canonical bytes: how a follower re-reads a logged event -/
  decodeCall : ByteArray → Option (Call D)
  /-- inverse of `env.bytes` on canonical digests -/
  digestOf : ByteArray → Option D
  verify : (key message signature : ByteArray) → Bool
  program : Program D

/-! Cell kinds and slot layouts of the receive layer. -/

def kindPackage : Nat := 1
def kindObject : Nat := 2
def kindGrant : Nat := 3
def kindMember : Nat := 4

/-- Object: 0 package id (absent: a data object), 1 owner, `2 ≤ k < stateBase` extra law ids,
state at `stateBase + i`. -/
def slotPackage : Nat := 0
def slotOwner : Nat := 1
def lawBase : Nat := 2
def stateBase : Nat := 16
/-- Member: 0 current key, 1 digest of the next key, 2 sponsor. -/
def slotKey : Nat := 0
def slotNext : Nat := 1
def slotSponsor : Nat := 2
/-- Grant: 0 target, 1 grantee, 2 issuer, 3 parent (absent at a root), the rights at `rightKey`.
`enroll`'s slot is the first of its LEDGER, `enrollBase + i` for `i ≤ enrollMax`: slot `i` holds
the count left after the grant's `i`-th spend (slot 0: as granted). The grant is append-only, so
the ledger only grows and the count left only falls; every spend takes at least one, and a
grant's count is at most `enrollMax`, so the ledger fits its range. The ranges are disjoint. -/
def grantTarget : Nat := 0
def grantGrantee : Nat := 1
def grantIssuer : Nat := 2
def grantParent : Nat := 3
def enrollBase : Nat := 1024
def invokeBase : Nat := 4096
def rightKey : Right → Nat
  | .observe => 16
  | .mutate => 17
  | .enroll _ => enrollBase
  | .invoke m => invokeBase + m
/-- The most one grant may enrol (a founder's genesis grant has exactly this). -/
def enrollMax : Nat := 256
/-- The longest grant chain a call walks. -/
def grantDepthMax : Nat := 8

def domTx : String := "nanodregg/kernel/tx/v1"
def domWorld : String := "nanodregg/kernel/world/v1"
def domNextKey : String := "nanodregg/kernel/next-key/v1"
def tagPossession : ByteArray := "nanodregg/kernel/possession/v1".toUTF8

variable {D : Type} [Ord D]

def pinned [DecidableEq D] (w : World D) (pins : List (D × D)) : Pinned D := fun c =>
  if pins.any (fun p => p.1 = c) then .ok (w.live c) else .error (.unpinned c)

def reqOf (u : Unsigned D) (principal : D) (occasion : Occasion D) : Req D :=
  { agent := u.member, principal, notBefore := u.notBefore, validUntil := u.validUntil, occasion }

/-- The transaction id: the digest of the call's canonical bytes. -/
def txIdOf (X : Ctx D) (c : Call D) : D := X.env.hash domTx (X.callBytes c)

/-- The target of a grant on the World itself (follow, enrol): an id no cell is born at. -/
def worldId (X : Ctx D) : D := X.env.hash domWorld ByteArray.empty

/-- A count in a ledger slot: CODEC's eight little-endian bytes. -/
def countBytes (n : Nat) : ByteArray := Nanodregg.Codec.Stream.u64.bytes (UInt64.ofNat n)

def countOf (b : ByteArray) : Option Nat :=
  match Nanodregg.Codec.Stream.u64.decode b with
  | .ok n => some n.toNat
  | .error _ => none

/-- The digest a member precommits for its next key. -/
def nextKeyDigest (X : Ctx D) (key : ByteArray) : D := X.env.hash domNextKey key

/-- What a new key signs to prove its holder asked to be enrolled by this sponsor. -/
def possessionMessage (X : Ctx D) (sponsor : D) (next : D) (key : ByteArray) : ByteArray :=
  tagPossession ++ X.env.bytes sponsor ++ X.env.bytes next ++ key

/-- What `effects` do to `cell`: the act of the effect on it, `keep` when there is none
(`effectsPinned` has made the effect cells distinct, so "the first" is "the only"). -/
def actFor [DecidableEq D] (effects : List (D × Act)) (cell : D) : Act :=
  match effects.find? (fun e => e.1 = cell) with
  | some (_, a) => a
  | none => .keep

/-- The caller's pins as the Turn's touches, in the caller's order, each with its act. -/
def touchesOf [DecidableEq D] (pins : List (D × D)) (effects : List (D × Act)) : List (Touch D) :=
  pins.map fun p => { cell := p.1, seen := p.2, act := actFor effects p.1 }

/-- Every effect is on a pinned cell, and on a cell no other effect names. -/
def effectsPinned [Ord D] [DecidableEq D] (pins : List (D × D)) (effects : List (D × Act)) :
    Except (Refusal D) Unit := do
  forEx (fun e => req (pins.any fun p => p.1 = e.1) (.unpinned e.1)) effects
  match firstDup (effects.map Prod.fst) with
  | none => .ok ()
  | some c => .error (.duplicateEffect c)

/-- The ids a call's fresh births get (`bornId`: content for ROM, else the transaction and the
index), paired with the cells. -/
def bornAt (X : Ctx D) (c : Call D) (creates : List Cell) : List (D × Cell) :=
  creates.zipIdx.map fun p => (bornId X.env (txIdOf X c) p, p.1)

/-- The Turn a call's effects become: the caller's window, the caller's pins as touches carrying
the effects (a receiver writes or retires only cells it read, so only pinned ones: `unpinned`
otherwise; at most one effect per cell: `duplicateEffect`), the receiver's nullifiers, the call as
the event, the exact charge (refused above the signed ceiling). -/
def sealTurn [DecidableEq D] (X : Ctx D) (c : Call D) (creates : List Cell)
    (effects : List (D × Act)) (nullifiers : List D) : Except (Refusal D) (Turn D) := do
  let pins := c.unsigned.pins
  effectsPinned pins effects
  let t0 : Turn D :=
    { txId := txIdOf X c, notBefore := c.unsigned.notBefore, validUntil := c.unsigned.validUntil,
      touches := touchesOf pins effects,
      creates := bornAt X c creates,
      nullifiers, charge := 0,
      event := X.callBytes c }
  let t := { t0 with charge := t0.weight }
  if t.charge ≤ c.unsigned.maxCharge then .ok t else .error (.overPrice t.charge)

/-- A pinned live cell of a kind. -/
def readKind (look : Pinned D) (c : D) (kind : Nat) : Except (Refusal D) Cell :=
  match look c with
  | .error e => .error e
  | .ok none => .error (.missingCell c)
  | .ok (some cell) => if cell.kind = kind then .ok cell else .error (.wrongKind c kind)

/-- A digest held in a slot. -/
def slotDigest (X : Ctx D) (id : D) (cell : Cell) (key : Nat) : Except (Refusal D) D :=
  match cell.slots.get key >>= X.digestOf with
  | some d => .ok d
  | none => .error (.malformedCell id key)

end Nanodregg.Kernel.Receive
