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

/-- How a call names a value account (LEDGER-7): a WELL by its denomination (its id IS the
denomination), any other account by its owner and denomination, resolved to the keyed
`accountId` by the receiver. Every value cell has exactly one name. -/
inductive AcctRef (D : Type)
  | well (asset : D)
  | of (owner asset : D)
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
  /-- bear the empty account of `asset`'s denomination (the well's id) owned by `owner`, at its
  keyed id `accountId owner asset`: anyone may open anyone's, once (`idTaken` after) -/
  | account (asset owner : D)
  /-- move `amount` from `src` to `dst` (same denomination), with the authority of `src`'s owner
  (directly, or through `via`'s grant chain for `mutate`); `once` spends the nullifier
  `onceNullifier src key`, so a call carrying the same key for the same source lands once.
  Minting is a transfer out of a well, burning one into it -/
  | transfer (src dst : AcctRef D) (amount : Nat) (via : Option D) (once : Option ByteArray)
  /-- a credit line: move `amount` of the well's floor to `acct` (same denomination), with the
  authority of the well's owner, the issuer (directly, or through `via` for `mutate`). The
  denomination's floor sum is unchanged, so its cap still bounds what is outstanding (LEDGER-4) -/
  | credit (well : D) (acct : AcctRef D) (amount : Nat) (via : Option D)
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
  /-- the row slots the caller observed (KERNEL-48, LANG-49): a point read's or an upsert's or a
  retract's row, each at the digest the caller saw (`rowPin`) -/
  rowPins : List (RowSlot D × D) := []
  /-- the range reads the caller observed (the second pin kind), each at its listing's pin -/
  ranges : List (RangeRead D) := []
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
  /-- a state slot below `stateBase` or not above the one before it, or an edit key past
  `Bounds.slotKeyLimit` -/
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
  /-- a method returned a call of a kind an object may not exercise (only `invoke`, `transfer`,
  `account`, `credit` and `grant` are callable): the kernel's own assertion where calls enter -/
  | notCallable (kind : String)
  /-- a call nested past `Bounds.callDepthMax` -/
  | callTooDeep
  /-- an invoke of an object already invoked in this call's tree (re-entry) -/
  | revisited (obj : D)
  /-- a method run returned more than `Bounds.callsMax` calls -/
  | tooManyCalls
  /-- a run reported more ticks than it was given: the kernel's assertion where `used` enters -/
  | overTicks
  /-- a pinned row effect (an upsert or a retract) on a slot of relation `rel` under `parent` the
  caller did not pin (LANG-49); `key` is the slot's row key bytes (empty for a head slot), so the
  client learns WHICH row to pin (`Protocol` derivePins, KERNEL-54 day) -/
  | rowUnpinned (parent : D) (rel : Nat) (key : ByteArray)
  /-- a run read a range of relation `rel` under `parent` the caller did not sign -/
  | rangeUnpinned (parent : D) (rel : Nat)
  /-- a signed range holds more rows than its `most` (refused, never truncated) -/
  | rangeTooLong (parent : D)
  /-- a method returned a row edit under an object other than its own: the kernel's assertion
  where row edits enter (law 4) -/
  | rowParent (obj : D)
  /-- a receiver gave one row slot two effects -/
  | duplicateRow (parent : D)
  /-- a log records a `stale` refusal (KERNEL-54): `judge` never records one (a stale pin observed on
  the fold is final without a record, `stale_behind_forever`), so the follower's audit refuses it -/
  | staleRecorded
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
  | .notCallable _ => "notCallable"
  | .callTooDeep => "callTooDeep"
  | .revisited _ => "revisited"
  | .tooManyCalls => "tooManyCalls"
  | .overTicks => "overTicks"
  | .rowUnpinned _ _ _ => "rowUnpinned"
  | .rangeUnpinned _ _ => "rangeUnpinned"
  | .rangeTooLong _ => "rangeTooLong"
  | .rowParent _ => "rowParent"
  | .duplicateRow _ => "duplicateRow"
  | .staleRecorded => "staleRecorded"

/-- A receiver's only access to state: live cells at pinned ids. -/
abbrev Pinned (D : Type) := D → Except (Refusal D) (Option Cell)

/-- A receiver's only access to rows (LANG-49, KERNEL-48): the caller's row pins under
`(parent, rel)`, in pin order, as each row's key bytes and its current leaf; and the caller's
signed ranges under `(parent, rel)`, in signed order, each as its prefix, its `most` and its
current listing (`rangeTooLong` past its `most`: refused, never truncated). A run reads no other
row. -/
structure RowView (D : Type) where
  points : D → Nat → List (ByteArray × Option RowLeaf)
  ranges : D → Nat → Except (Refusal D) (List (ByteArray × Nat × List (RowSlot D × RowLeaf)))

/-- The parent and relation a row slot is under. -/
def _root_.Nanodregg.Kernel.RowSlot.under {D : Type} : RowSlot D → D × Nat
  | .head p rel => (p, rel)
  | .row k => (k.parent, k.rel)

/-- A row slot's key bytes (a head has none). -/
def _root_.Nanodregg.Kernel.RowSlot.keyBytes {D : Type} : RowSlot D → ByteArray
  | .head _ _ => ByteArray.empty
  | .row k => k.k

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
  /-- the object the act is judged or run on (LEDGER-6 (b)): a method names its own accounts by it -/
  self : D
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
  /-- run a method: the new state slots (the receiver then judges them), the calls it makes as
  the object (LEDGER-5, LANG-23), its row edits (LANG-49: inserts, upserts and retracts under the
  object's own relations, each already judged by its relation's guard), and the ticks it used of
  `budget` (LEDGER-8 (e)). It reads rows only through the `RowView`. -/
  run : Pinned D → RowView D → (pkg : D) → (state : Slots) → (method : Nat) → (args : ByteArray) →
    Req D → (budget : Nat) → Except (Refusal D) (Slots × List (Body D) × List (RowSlot D × RowAct) × Nat)
  /-- the relations an object of package `pkg` born at `self` holds, as the `declare` acts of
  their heads in relation-index order (LANG-49, KERNEL-46 amendment 2) -/
  rels : Pinned D → (pkg : D) → (self : D) → Except (Refusal D) (List RowAct)

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

/-- The inputs whose `domTx` digests a retry's transaction id is compared against: the retry's own
event and every event of the log (the explicit list `Kernel.Proofs.Journal`'s retry-window theorems escape
through, `CollidesAmong E.hash (retryPres t l)`; KERNEL-38 (c)). -/
def retryPres {D : Type} (t : Turn D) (l : List (Step D)) : List (String × ByteArray) :=
  (domTx, t.event) :: (Step.turns l).map fun u => (domTx, u.event)

def domWorld : String := "nanodregg/kernel/world/v1"
def domNextKey : String := "nanodregg/kernel/next-key/v1"
def tagPossession : ByteArray := "nanodregg/kernel/possession/v1".toUTF8

variable {D : Type} [Ord D]

def pinned [DecidableEq D] (E : Env D) (w : World D) (pins : List (D × D)) : Pinned D := fun c =>
  if pins.any (fun p => p.1 = c) then .ok (w.live E c) else .error (.unpinned c)

/-- The rows a caller observed, on `w`: its pinned rows' leaves, and its signed ranges' current
listings at their relations' widths (`rangeOf`: the pre-state `rangeRows` admission recomputes). -/
def rowView [DecidableEq D] (E : Env D) (w : World D) (u : Unsigned D) : RowView D where
  points parent rel := u.rowPins.filterMap fun p =>
    match p.1 with
    | .row k => if k.parent = parent ∧ k.rel = rel then some (k.k, rowAt E w.rows p.1) else none
    | .head .. => none
  ranges parent rel :=
    (u.ranges.filter fun q => q.parent = parent ∧ q.rel = rel).mapM fun q =>
      match rangeOf E w.rows parent rel q.pre q.most with
      | none => .error (.rangeUnpinned parent rel)
      | some (_, none) => .error (.rangeTooLong parent)
      | some (_, some l) => .ok (q.pre, q.most, l)

def reqOf (u : Unsigned D) (self principal : D) (occasion : Occasion D) : Req D :=
  { agent := u.member, principal, self, notBefore := u.notBefore, validUntil := u.validUntil, occasion }

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

/-- The call signature's domain (KERNEL-42): every message a member key signs begins with its own
domain, so a call's signature is never one over another protocol's message (a read envelope, a
possession proof, an identity probe): `Protocol.Proofs.Domains`. -/
def domCall : ByteArray := "nanodregg/kernel/call-signature".toUTF8

/-- What a call's signature is over: `domCall`, then the call's canonical unsigned bytes. -/
def Ctx.callMessage (X : Ctx D) (u : Unsigned D) : ByteArray := domCall ++ X.unsignedBytes u

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
index, counted from `base`, the births before them in the call's tree), paired with the cells. -/
def bornAt (X : Ctx D) (c : Call D) (base : Nat) (creates : List Cell) : List (D × Cell) :=
  creates.zipIdx base |>.map fun p => (bornId X.env (txIdOf X c) p, p.1)

/-- What one receiver derives (KERNEL-28 (c)): births at their ids, effects, nullifiers. A call's
tree of receivers concatenates its Drafts and `receiveWith` seals them ONCE. -/
structure Draft (D : Type) where
  creates : List (D × Cell)
  effects : List (D × Act)
  nullifiers : List D
  /-- row effects (LANG-49): a create's `declare`s, a run's inserts, upserts and retracts -/
  rows : List (RowSlot D × RowAct) := []

def Draft.append (a b : Draft D) : Draft D :=
  ⟨a.creates ++ b.creates, a.effects ++ b.effects, a.nullifiers ++ b.nullifiers, a.rows ++ b.rows⟩

/-- Where in a call's tree a receiver runs (LEDGER-8 (b)): `actor` is whose authority it spends
(the signer at the top, the calling object for an effect, KERNEL-28 (b)); `base` is the fresh
births before it in the tree. -/
structure At (D : Type) where
  actor : D
  base : Nat

/-- The kinds an object may exercise as a call (KERNEL-28 (a)). -/
def Body.callable : Body D → Bool
  | .invoke .. | .transfer .. | .account .. | .credit .. | .grant .. => true
  | _ => false

/-- The body is an invoke (the one receiver that derives calls through `sub`). -/
def Body.isInvoke : Body D → Bool
  | .invoke .. => true
  | _ => false

/-- A Body's kind, by name (`notCallable`'s argument). -/
def Body.kindName : Body D → String
  | .enroll .. => "enroll" | .rotate .. => "rotate" | .install .. => "install"
  | .create .. => "create" | .write .. => "write" | .law .. => "law" | .invoke .. => "invoke"
  | .grant .. => "grant" | .revoke .. => "revoke" | .issue .. => "issue"
  | .account .. => "account" | .transfer .. => "transfer" | .credit .. => "credit"

/-- What row effects do to row slot `s`: `keep` when there is none. -/
def rowActFor [DecidableEq D] (rows : List (RowSlot D × RowAct)) (s : RowSlot D) : RowAct :=
  match rows.find? (fun e => e.1 = s) with
  | some (_, a) => a
  | none => .keep

/-- The first element that occurs again later (at most `Bounds.rowsMax` row effects reach it). -/
def dupBy {α : Type} [DecidableEq α] : List α → Option α
  | [] => none
  | x :: xs => if xs.contains x then some x else dupBy xs

/-- A row act that needs no pin: a birth (`insert` of a row, `declare` of a head). -/
def _root_.Nanodregg.Kernel.RowAct.unpinned : RowAct → Bool
  | .insert .. | .declare .. => true
  | _ => false

/-- The caller's row pins as row touches, each with its act, then every unpinned row effect
(an insert or a declare) with no pin. A pinned effect on an unpinned slot is `rowUnpinned`; one
slot given two effects is `duplicateRow`. -/
def rowTouchesOf [Ord D] [DecidableEq D] (pins : List (RowSlot D × D)) (rows : List (RowSlot D × RowAct)) :
    Except (Refusal D) (List (RowTouch D)) := do
  forEx (fun e => req (e.2.unpinned || pins.any fun p => p.1 = e.1) (.rowUnpinned e.1.under.1 e.1.under.2 e.1.keyBytes)) rows
  match dupBy (rows.map Prod.fst) with
  | some s => throw (.duplicateRow s.under.1)
  | none => pure ()
  pure (pins.map (fun p => { slot := p.1, seen := some p.2, act := rowActFor rows p.1 }) ++
    (rows.filter fun e => !(pins.any fun p => p.1 = e.1)).map fun e => { slot := e.1, seen := none, act := e.2 })

/-- The Turn a call's effects become: its births at the ids the receiver computed, the caller's window, the caller's pins as touches carrying
the effects (a receiver writes or retires only cells it read, so only pinned ones: `unpinned`
otherwise; at most one effect per cell: `duplicateEffect`), the receiver's nullifiers, the call as
the event, the exact charge (refused above the signed ceiling). -/
def sealTurn [DecidableEq D] (X : Ctx D) (c : Call D) (creates : List (D × Cell))
    (effects : List (D × Act)) (nullifiers : List D) (rows : List (RowSlot D × RowAct) := []) :
    Except (Refusal D) (Turn D) := do
  let pins := c.unsigned.pins
  effectsPinned pins effects
  let rts ← rowTouchesOf c.unsigned.rowPins rows
  let t0 : Turn D :=
    { txId := txIdOf X c, notBefore := c.unsigned.notBefore, validUntil := c.unsigned.validUntil,
      touches := touchesOf pins effects,
      creates,
      nullifiers, charge := 0,
      event := X.callBytes c, rows := rts, ranges := c.unsigned.ranges }
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
