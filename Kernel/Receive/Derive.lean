/-
# Kernel.Receive.Derive — one derivation per operation kind, and `receive`

`receive X w c` is the whole of "what may this call do": signature, the member's current key,
authority (ownership, or a grant chain that reaches the owner), the laws, the price. Its result
is exactly the `Turn` the Host hands to `World.admit`.
-/
import Kernel.Receive.Authority
import Kernel.Receive.Ledger

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

/-- The slot operations that turn `old` into `new`. -/
def diffOps (old new : Slots) : List Op :=
  (new.filter fun p => old.get p.1 != some p.2).map (fun p => .set p.1 p.2) ++
  (old.filter fun p => (new.get p.1).isNone).map (fun p => .erase p.1)

/-- A write of `ops` to `cell`, or no effect when there are none. -/
def writeOf (cell : D) (ops : List Op) : List (D × Act) :=
  if ops.isEmpty then [] else [(cell, .write ops)]

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

/-- The ledger of a grant's enrolment right: its next index and the count left (its last
entry). `grantRight` when the grant carries no enrolment right. -/
def enrollLeft (g : D) (cell : Cell) : Except (Refusal D) (Nat × Nat) :=
  let led := cell.slots.filter fun p => enrollBase ≤ p.1 && p.1 ≤ enrollBase + enrollMax
  match led.getLast? with
  | none => .error (.grantRight g)
  | some (k, v) => match countOf v with
    | some n => .ok (led.length, n)
    | none => .error (.malformedCell g k)

/-- Spend `units` of grant `g`'s enrolment count (refused `short` past what is left): the write
appending the count left to its ledger, or no effect for nothing. -/
def spendEnroll (g : D) (cell : Cell) (units : Nat) (short : Refusal D) :
    Except (Refusal D) (Option (D × Act)) := do
  let (i, left) ← enrollLeft g cell
  req (units ≤ left) short
  pure (if units = 0 then none else some (g, .write [.set (enrollBase + i) (countBytes (left - units))]))

/-- Enrolment is a right (KERNEL-16): the sponsor acts through a World grant chain carrying
`enroll`, rooted at a founder's genesis grant, and spends one of its own grant's count. -/
def enroll (X : Ctx D) (look : Pinned D) (c : Call D) (key : ByteArray) (next : D)
    (possession : ByteArray) (via : D) : Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  let _ ← walk X look (worldId X) (.enroll 0) true grantDepthMax via u.member
  let g ← readKind look via kindGrant
  let spend ← spendEnroll via g 1 (.enrollSpent via)
  req (X.verify key (possessionMessage X u.member next key) possession) .badPossession
  let slots := slotsOf [(slotKey, key), (slotNext, X.env.bytes next),
    (slotSponsor, X.env.bytes u.member)]
  sealTurn X c [{ kind := kindMember, discipline := .ram, slots }] spend.toList []

/-- Signed by the new key; the new key's digest must be the one precommitted. -/
def rotate (X : Ctx D) (look : Pinned D) (c : Call D) (key : ByteArray) (next : D) :
    Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  let m ← readKind look u.member kindMember
  req (u.key = key) (.notPrecommitted u.member)
  let committed ← slotDigest X u.member m slotNext
  req (committed = nextKeyDigest X key) (.notPrecommitted u.member)
  let ops := [Op.set slotKey key, Op.set slotNext (X.env.bytes next)]
  sealTurn X c [] [(u.member, .write ops)] []

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
  X.program.judge look pkg laws state state (reqOf u u.member .birth)
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
  X.program.judge look none laws old new (reqOf u principal .write)
  sealTurn X c [] (writeOf obj (diffOps old new)) []

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
  X.program.judge look none laws (stateOf cell) (stateOf cell) (reqOf u principal (.relaw laws'))
  -- LANG-19 (KERNEL-27): the incoming laws judge the state they are adopted over, as `.adopt`, so a
  -- law that would deny it cannot be installed
  X.program.judge look none laws' (stateOf cell) (stateOf cell) (reqOf u principal (.adopt laws'))
  sealTurn X c [] (writeOf obj (diffOps (lawSlotsOf cell) (lawSlots X laws'))) []

def requireMethods (obj : D) : Option D → Except (Refusal D) D
  | none => .error (.noMethods obj)
  | some p => .ok p

/-- What an invoke hands the program to run: the object's cell, its package, and the request,
after the owner authority (KERNEL-25). `invoke` is this, then the run; a measurement of the run
(THE BAR's WASTE lines, LANG's `runMeasured`) starts from the same inputs, never a restatement. -/
def invokeRun (X : Ctx D) (look : Pinned D) (c : Call D) (obj : D) (method : Nat) (via : Option D) :
    Except (Refusal D) (Cell × D × Req D) := do
  let u := c.unsigned
  let cell ← readKind look obj kindObject
  let pkg ← packageOf X obj cell
  let p ← requireMethods obj pkg
  let principal ← ownerAuthority X look u obj cell (.invoke method) via
  pure (cell, p, reqOf u principal (.invoke method))

def invoke (X : Ctx D) (look : Pinned D) (c : Call D) (obj : D) (method : Nat) (args : ByteArray)
    (budget : Nat) (via : Option D) : Except (Refusal D) (Turn D) := do
  let (cell, p, r) ← invokeRun X look c obj method via
  let old := stateOf cell
  let new ← X.program.run look p old method args r budget
  checkState new
  let laws ← lawsOf X obj cell
  X.program.judge look (some p) laws old new r
  sealTurn X c [] (writeOf obj (diffOps old new)) []

/-- The enrolment count a list of rights grants (several `enroll` rights add up). -/
def enrollUnits : List Right → Nat
  | [] => 0
  | .enroll n :: rest => n + enrollUnits rest
  | _ :: rest => enrollUnits rest

def isEnroll : Right → Bool
  | .enroll _ => true
  | _ => false

/-- A grant's right slots: every right but `enroll` as a key, and one ledger entry with the sum
of the `enroll` counts. -/
def rightSlots (rights : List Right) : List (Nat × ByteArray) :=
  (rights.filter (!isEnroll ·)).map (fun r => (rightKey r, ByteArray.empty)) ++
    if rights.any isEnroll then [(enrollBase, countBytes (enrollUnits rights))] else []

/-- An attenuated grant narrows a parent the signer holds on the same target; an enrolment count
is carved out of the parent's (the parent's ledger is the effect). World rights and enrolment
rights are never rooted here (`unrooted`): only genesis roots them. -/
def checkParent (X : Ctx D) (look : Pinned D) (u : Unsigned D) (target : D) (rights : List Right) :
    Option D → Except (Refusal D) (Option (D × Act))
  | none => do
      req (!(target = worldId X || rights.any isEnroll)) (.unrooted target)
      pure none
  | some p => do
      let pc ← readKind look p kindGrant
      let pt ← slotDigest X p pc grantTarget
      req (pt = target) (.grantTarget p)
      let pg ← slotDigest X p pc grantGrantee
      req (pg = u.member) (.noGrant p)
      forEx (fun r => req (pc.slots.get (rightKey r)).isSome (.grantWidens p)) rights
      if rights.any isEnroll then spendEnroll p pc (enrollUnits rights) (.grantWidens p)
      else pure none

/-- A grant names a live member, or the World itself: a public grant, held by every enrolled
member (KERNEL-26, `granteeHolds`). -/
def checkGrantee (X : Ctx D) (look : Pinned D) (grantee : D) : Except (Refusal D) Unit :=
  if grantee = worldId X then pure () else (readKind look grantee kindMember).map fun _ => ()

def grant (X : Ctx D) (look : Pinned D) (c : Call D) (target grantee : D) (rights : List Right)
    (parent : Option D) : Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  checkGrantee X look grantee
  let carve ← checkParent X look u target rights parent
  let slots := slotsOf ([(grantTarget, X.env.bytes target), (grantGrantee, X.env.bytes grantee),
      (grantIssuer, X.env.bytes u.member)] ++
    (parent.map fun p => (grantParent, X.env.bytes p)).toList ++ rightSlots rights)
  sealTurn X c [{ kind := kindGrant, discipline := .appendOnly, slots }] carve.toList []

/-- The issuer retires a grant; every chain through it dies with it. -/
def revoke (X : Ctx D) (look : Pinned D) (c : Call D) (g : D) : Except (Refusal D) (Turn D) := do
  let u := c.unsigned
  let cell ← readKind look g kindGrant
  let issuer ← slotDigest X g cell grantIssuer
  req (issuer = u.member) (.notIssuer g)
  sealTurn X c [] [(g, .retire)] []

def dispatch (X : Ctx D) (look : Pinned D) (c : Call D) : Body D → Except (Refusal D) (Turn D)
  | .enroll key next possession via => enroll X look c key next possession via
  | .rotate key next => rotate X look c key next
  | .install pkg => install X look c pkg
  | .create pkg laws state => create X look c pkg laws state
  | .write obj edits via => write X look c obj edits via
  | .law obj laws via => law X look c obj laws via
  | .invoke obj method args budget via => invoke X look c obj method args budget via
  | .grant target grantee rights parent => grant X look c target grantee rights parent
  | .revoke g => revoke X look c g
  | .issue cap => issue X c cap
  | .account asset => account X c asset
  | .transfer src dst amount via once => transfer X look c src dst amount via once
  | .credit well acct amount via => credit X look c well acct amount via

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
