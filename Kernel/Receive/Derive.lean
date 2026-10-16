/-
# Kernel.Receive.Derive — one derivation per operation kind, and `receive`

`receive X w c` is the whole of "what may this call do": signature, the member's current key,
authority (ownership, or a grant chain that reaches the owner), the laws, the price. Its result
is exactly the `Turn` the Host hands to `World.admit`.
-/
import Kernel.Receive.Call

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

def checkSignature (X : Ctx D) (c : Call D) : Except (Refusal D) Unit :=
  req (X.verify c.unsigned.key (X.unsignedBytes c.unsigned) c.signature) .badSignature

/-- The signer's member exists and `key` is its current key. -/
def checkKey (look : Pinned D) (u : Unsigned D) : Except (Refusal D) Unit :=
  match readKind look u.member kindMember with
  | .error (.unpinned c) => .error (.unpinned c)
  | .error _ => .error (.unknownKey u.member)
  | .ok m => req (m.slots.get slotKey = some u.key) (.unknownKey u.member)

/-- Build slots in canonical order whatever order the pairs come in. -/
def slotsOf (ps : List (Nat × ByteArray)) : Slots := ps.foldl (fun s p => s.set p.1 p.2) []

/-- The slot operations that turn `old` into `new`. -/
def diffOps (old new : Slots) : List Op :=
  (new.filter fun p => old.get p.1 != some p.2).map (fun p => .set p.1 p.2) ++
  (old.filter fun p => (new.get p.1).isNone).map (fun p => .erase p.1)

def legOf (cell : D) (ops : List Op) : List (Leg D) :=
  if ops.isEmpty then [] else [{ cell, ops }]

def stateOf (cell : Cell) : Slots := cell.slots.filter fun p => stateBase ≤ p.1

def lawSlotsOf (cell : Cell) : Slots := cell.slots.filter fun p => lawBase ≤ p.1 && p.1 < stateBase

def lawSlots (X : Ctx D) (laws : List D) : Slots :=
  laws.zipIdx.map fun (l, i) => (lawBase + i, X.env.bytes l)

def lawsOf (X : Ctx D) (obj : D) (cell : Cell) : Except (Refusal D) (List D) :=
  mapEx (fun p => slotDigest X obj cell p.1) (lawSlotsOf cell)

def packageOf (X : Ctx D) (obj : D) (cell : Cell) : Except (Refusal D) (Option D) :=
  match cell.slots.get slotPackage with
  | none => .ok none
  | some b => match X.digestOf b with
    | none => .error (.malformedCell obj slotPackage)
    | some d => .ok (some d)

def checkState (state : Slots) : Except (Refusal D) Unit :=
  forEx (fun p => req (stateBase ≤ p.1) (.stateKey p.1)) state

def checkLaws (look : Pinned D) (laws : List D) : Except (Refusal D) Unit := do
  req (laws.length ≤ stateBase - lawBase) .tooManyLaws
  forEx (fun l => (readKind look l kindPackage).map fun _ => ()) laws

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

def enroll (X : Ctx D) (c : Call D) (key : ByteArray) (next : D) (possession : ByteArray) :
    Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  req (X.verify key (possessionMessage X u.member next key) possession) .badPossession
  let slots := slotsOf [(slotKey, key), (slotNext, X.env.bytes next),
    (slotSponsor, X.env.bytes u.member)]
  sealTurn X c [{ kind := kindMember, discipline := .ram, slots }] [] []

/-- Signed by the new key; the new key's digest must be the one precommitted. -/
def rotate (X : Ctx D) (look : Pinned D) (c : Call D) (key : ByteArray) (next : D) :
    Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  let m ← readKind look u.member kindMember
  req (u.key = key) (.notPrecommitted u.member)
  let committed ← slotDigest X u.member m slotNext
  req (committed = nextKeyDigest X key) (.notPrecommitted u.member)
  let ops := [Op.set slotKey key, Op.set slotNext (X.env.bytes next)]
  sealTurn X c [] [{ cell := u.member, ops }] []

/-- `install pkg`: a ROM package cell, its id its content digest (KERNEL-3). -/
def install (X : Ctx D) (look : Pinned D) (c : Call D) (pkg : ByteArray) :
    Except (Refusal D) (Turn D) := do
  X.program.checkInstall look pkg
  sealTurn X c [{ kind := kindPackage, discipline := .rom, slots := [(0, pkg)] }] [] []

def objectCell (X : Ctx D) (owner : D) (pkg : Option D) (laws : List D) (state : Slots) : Cell :=
  { kind := kindObject, discipline := .ram,
    slots := slotsOf ((pkg.map fun p => (slotPackage, X.env.bytes p)).toList ++
      [(slotOwner, X.env.bytes owner)] ++ lawSlots X laws ++ state) }

/-- A named package is a live, pinned package cell. -/
def checkPackage (look : Pinned D) : Option D → Except (Refusal D) Unit
  | none => .ok ()
  | some p => (readKind look p kindPackage).map fun _ => ()

def create (X : Ctx D) (look : Pinned D) (c : Call D) (pkg : Option D) (laws : List D)
    (state : Slots) : Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  checkPackage look pkg
  checkLaws look laws
  checkState state
  X.program.judge look pkg laws state state { agent := u.member, principal := u.member }
  sealTurn X c [objectCell X u.member pkg laws state] [] []

def applyEdits (s : Slots) (edits : List (Nat × Option ByteArray)) : Slots :=
  edits.foldl (fun s e => match e.2 with
    | some v => s.set (stateBase + e.1) v
    | none => s.erase (stateBase + e.1)) s

def write (X : Ctx D) (look : Pinned D) (c : Call D) (obj : D)
    (edits : List (Nat × Option ByteArray)) (via : Option D) : Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  let cell ← readKind look obj kindObject
  let pkg ← packageOf X obj cell
  req pkg.isNone (.hasMethods obj)
  let principal ← ownerAuthority X look u obj cell .mutate via
  forEx (fun e => req (stateBase + e.1 < Bounds.slotKeyLimit) (.stateKey e.1)) edits
  let old := stateOf cell
  let new := applyEdits old edits
  let laws ← lawsOf X obj cell
  X.program.judge look none laws old new { agent := u.member, principal }
  sealTurn X c [] (legOf obj (diffOps old new)) []

/-- Replace a data object's extra laws; the laws in force judge the change. -/
def law (X : Ctx D) (look : Pinned D) (c : Call D) (obj : D) (laws' : List D) (via : Option D) :
    Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  let cell ← readKind look obj kindObject
  let pkg ← packageOf X obj cell
  req pkg.isNone (.hasMethods obj)
  let principal ← ownerAuthority X look u obj cell .mutate via
  checkLaws look laws'
  let laws ← lawsOf X obj cell
  X.program.judge look none laws (stateOf cell) (stateOf cell) { agent := u.member, principal }
  sealTurn X c [] (legOf obj (diffOps (lawSlotsOf cell) (lawSlots X laws'))) []

def requireMethods (obj : D) : Option D → Except (Refusal D) D
  | none => .error (.noMethods obj)
  | some p => .ok p

def invoke (X : Ctx D) (look : Pinned D) (c : Call D) (obj : D) (method : Nat) (args : ByteArray)
    (budget : Nat) (via : Option D) : Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  let cell ← readKind look obj kindObject
  let pkg ← packageOf X obj cell
  let p ← requireMethods obj pkg
  let principal ← principalOf X look u obj (.invoke method) via
  let r : Req D := { agent := u.member, principal }
  let old := stateOf cell
  let new ← X.program.run look p old method args r budget
  checkState new
  let laws ← lawsOf X obj cell
  X.program.judge look (some p) laws old new r
  sealTurn X c [] (legOf obj (diffOps old new)) []

/-- An attenuated grant narrows a parent the signer holds on the same target. -/
def checkParent (X : Ctx D) (look : Pinned D) (u : Unsigned D) (target : D) (rights : List Right) :
    Option D → Except (Refusal D) Unit
  | none => .ok ()
  | some p => do
      let pc ← readKind look p kindGrant
      let pt ← slotDigest X p pc grantTarget
      req (pt = target) (.grantTarget p)
      let pg ← slotDigest X p pc grantGrantee
      req (pg = u.member) (.noGrant p)
      forEx (fun r => req (pc.slots.get (rightKey r)).isSome (.grantWidens p)) rights

def grant (X : Ctx D) (look : Pinned D) (c : Call D) (target grantee : D) (rights : List Right)
    (parent : Option D) : Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  let _ ← readKind look grantee kindMember
  checkParent X look u target rights parent
  let slots := slotsOf ([(grantTarget, X.env.bytes target), (grantGrantee, X.env.bytes grantee),
      (grantIssuer, X.env.bytes u.member)] ++
    (parent.map fun p => (grantParent, X.env.bytes p)).toList ++
    rights.map fun r => (rightKey r, ByteArray.empty))
  sealTurn X c [{ kind := kindGrant, discipline := .appendOnly, slots }] [] []

def follow (X : Ctx D) (look : Pinned D) (c : Call D) (grantee parent : D) :
    Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  let _ ← readKind look grantee kindMember
  let pc ← readKind look parent kindFollow
  let pg ← slotDigest X parent pc grantGrantee
  req (pg = u.member) (.noGrant parent)
  let slots := slotsOf [(grantGrantee, X.env.bytes grantee), (grantIssuer, X.env.bytes u.member),
    (grantParent, X.env.bytes parent)]
  sealTurn X c [{ kind := kindFollow, discipline := .appendOnly, slots }] [] []

/-- A pinned live grant or follow grant. -/
def readGrantLike (look : Pinned D) (g : D) : Except (Refusal D) Cell :=
  match look g with
  | .error e => .error e
  | .ok none => .error (.missingCell g)
  | .ok (some cell) =>
      if cell.kind = kindGrant || cell.kind = kindFollow then .ok cell
      else .error (.wrongKind g kindGrant)

/-- The issuer retires a grant or follow grant; every chain through it dies with it. -/
def revoke (X : Ctx D) (look : Pinned D) (c : Call D) (g : D) : Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  let cell ← readGrantLike look g
  let issuer ← slotDigest X g cell grantIssuer
  req (issuer = u.member) (.notIssuer g)
  sealTurn X c [] [] [g]

def dispatch (X : Ctx D) (look : Pinned D) (c : Call D) : Body D → Except (Refusal D) (Turn D)
  | .enroll key next possession => enroll X c key next possession
  | .rotate key next => rotate X look c key next
  | .install pkg => install X look c pkg
  | .create pkg laws state => create X look c pkg laws state
  | .write obj edits via => write X look c obj edits via
  | .law obj laws via => law X look c obj laws via
  | .invoke obj method args budget via => invoke X look c obj method args budget via
  | .grant target grantee rights parent => grant X look c target grantee rights parent
  | .follow grantee parent => follow X look c grantee parent
  | .revoke g => revoke X look c g

/-- A rotation is signed by the incoming key; every other call by the member's current key. -/
def keyRule (look : Pinned D) (u : Unsigned D) : Except (Refusal D) Unit :=
  match u.body with
  | .rotate _ _ => .ok ()
  | _ => checkKey look u

/-- Derive from the pinned view: signature, key, then the kind's derivation. -/
def receiveWith (X : Ctx D) (look : Pinned D) (c : Call D) : Except (Refusal D) (Turn D) := do
  checkSignature X c
  keyRule look c.unsigned
  dispatch X look c c.unsigned.body

/-- THE derivation: a signed call against a World, through the caller's pins only. -/
def receive (X : Ctx D) (w : World D) (c : Call D) : Except (Refusal D) (Turn D) :=
  receiveWith X (pinned w c.unsigned.pins) c

end Nanodregg.Kernel.Receive
