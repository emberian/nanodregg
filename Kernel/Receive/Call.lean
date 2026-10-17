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
  deriving DecidableEq, Repr

/-- What a call asks for, one constructor per operation kind. -/
inductive Body (D : Type)
  /-- the signer sponsors a new member with `key`, precommitting the digest of its next key;
  `possession` is the new key's signature over the enrolment -/
  | enroll (key : ByteArray) (next : D) (possession : ByteArray)
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
  that grant's principal, attenuated) -/
  | grant (target : D) (grantee : D) (rights : List Right) (parent : Option D)
  /-- let member `grantee` follow the World (read the log), under the signer's follow grant -/
  | follow (grantee : D) (parent : D)
  /-- retire a grant or follow grant the signer issued -/
  | revoke (grant : D)
  deriving DecidableEq

/-- What the caller signs. `pins` is the caller's observation; `maxCharge` the price ceiling. -/
structure Unsigned (D : Type) where
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
  /-- an attenuated grant may only narrow its parent -/
  | grantWidens (parent : D)
  | notIssuer (grant : D)
  | grantTooDeep
  | overPrice (charge : Nat)
  deriving DecidableEq, Repr

/-- A receiver's only access to state: live cells at pinned ids. -/
abbrev Pinned (D : Type) := D → Except (Refusal D) (Option Cell)

/-- Who a call acts for, as member ids: `agent` signed; `principal` is whose authority it
exercises (the agent, or the root issuer of the grant chain). Laws judge by these. -/
structure Req (D : Type) where
  agent : D
  principal : D
  /-- the call's signed window: the Turn lands at a height in `[notBefore, validUntil]`
  (`World.admit` enforces it), so a law can say "not before h" without reading the World -/
  notBefore : Nat
  validUntil : Nat
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
def kindFollow : Nat := 5

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
/-- Grant and follow grant: 0 target (grants only), 1 grantee, 2 issuer, 3 parent (absent at a
root), and the rights at `rightKey`. -/
def grantTarget : Nat := 0
def grantGrantee : Nat := 1
def grantIssuer : Nat := 2
def grantParent : Nat := 3
def rightKey : Right → Nat
  | .observe => 16
  | .mutate => 17
  | .invoke m => 32 + m
/-- The longest grant chain a call walks. -/
def grantDepthMax : Nat := 8

def domTx : String := "nanodregg/kernel/tx/v1"
def domNextKey : String := "nanodregg/kernel/next-key/v1"
def tagPossession : ByteArray := "nanodregg/kernel/possession/v1".toUTF8

variable {D : Type} [Ord D]

def pinned [DecidableEq D] (w : World D) (pins : List (D × D)) : Pinned D := fun c =>
  if pins.any (fun p => p.1 = c) then .ok (w.live c) else .error (.unpinned c)

def reqOf (u : Unsigned D) (principal : D) : Req D :=
  { agent := u.member, principal, notBefore := u.notBefore, validUntil := u.validUntil }

/-- The transaction id: the digest of the call's canonical bytes. -/
def txIdOf (X : Ctx D) (c : Call D) : D := X.env.hash domTx (X.callBytes c)

/-- The digest a member precommits for its next key. -/
def nextKeyDigest (X : Ctx D) (key : ByteArray) : D := X.env.hash domNextKey key

/-- What a new key signs to prove its holder asked to be enrolled by this sponsor. -/
def possessionMessage (X : Ctx D) (sponsor : D) (next : D) (key : ByteArray) : ByteArray :=
  tagPossession ++ X.env.bytes sponsor ++ X.env.bytes next ++ key

/-- What `effect` does to `cell`: its act on its own cell, `keep` on every other. -/
def actFor [DecidableEq D] (effect : Option (D × Act)) (cell : D) : Act :=
  match effect with
  | some (c, a) => if c = cell then a else .keep
  | none => .keep

/-- The caller's pins as the Turn's touches, in the caller's order, each with its act. -/
def touchesOf [DecidableEq D] (pins : List (D × D)) (effect : Option (D × Act)) : List (Touch D) :=
  pins.map fun p => { cell := p.1, seen := p.2, act := actFor effect p.1 }

/-- The effect is on a pinned cell. -/
def effectPinned [DecidableEq D] (pins : List (D × D)) : Option (D × Act) → Except (Refusal D) Unit
  | some (e, _) => req (pins.any fun p => p.1 = e) (.unpinned e)
  | none => .ok ()

/-- The Turn a call's effect becomes: the caller's window, the caller's pins as touches carrying
the effect (a receiver writes or retires at most one cell, always one it read, so always a
pinned one: `unpinned` otherwise), the call as the event, the exact charge (refused above the
signed ceiling). -/
def sealTurn [DecidableEq D] (X : Ctx D) (c : Call D) (creates : List Cell)
    (effect : Option (D × Act)) : Except (Refusal D) (Turn D) := do
  let pins := c.unsigned.pins
  effectPinned pins effect
  let t0 : Turn D :=
    { txId := txIdOf X c, notBefore := c.unsigned.notBefore, validUntil := c.unsigned.validUntil,
      touches := touchesOf pins effect, creates, nullifiers := [], charge := 0,
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
