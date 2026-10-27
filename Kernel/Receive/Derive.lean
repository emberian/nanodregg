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
  req (X.verify c.unsigned.key (X.callMessage c.unsigned) c.signature) .badSignature

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

/-- The receiver's effect on its own cell: a write of `ops`, or the cell kept when there are
none. A receiver that read its cell claims it either way, so the act the Turn carries there is this
one (`actFor` finds the first effect at a cell, and a second is `duplicateEffect`), never another
receiver's of the same tree (`Kernel.Proofs.InvokeNext.invoke_next_slots`). A kept cell is the
default of a pin, so the sealed Turn is the same as with no effect. -/
def writeOf (cell : D) (ops : List Op) : List (D × Act) :=
  [(cell, if ops.isEmpty then .keep else .write ops)]

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

/-- A state's keys from `lo` on: each at least the one before it plus one, the first at least `lo`;
the first key out of place is named. -/
def checkStateFrom (lo : Nat) : Slots → Except (Refusal D) Unit
  | [] => .ok ()
  | p :: rest => do
      req (decide (lo ≤ p.1)) (.stateKey p.1)
      checkStateFrom (p.1 + 1) rest

/-- A state (a run's, or a birth's) is canonical state: every key at least `stateBase`, strictly
ascending, the form a cell holds (`Slots.ascending`). So `diffOps` of it is a write whose cell
reads back, key by key, exactly this state (`Kernel.Proofs.InvokeNext.diffOps_next`); a run
returning one key twice is refused here, not written as one of its two values. -/
def checkState (state : Slots) : Except (Refusal D) Unit := checkStateFrom stateBase state

def checkLaws (look : Pinned D) (laws : List D) : Except (Refusal D) Unit := do
  req (laws.length ≤ stateBase - lawBase) .tooManyLaws
  forEx (fun l => (readKind look l kindPackage).map fun _ => ()) laws

/-- The ledger of a grant's enrolment right: its next index and the count left (its last
entry). `grantRight` when the grant carries no enrolment right. -/
def enrollLeft (g : D) (cell : Cell) : Except (Refusal D) (Nat × Nat) := ledgerLeft enrollBase g cell

/-- Spend `units` of grant `g`'s enrolment count (refused `short` past what is left): the write
appending the count left to its ledger, or no effect for nothing. -/
def spendEnroll (g : D) (cell : Cell) (units : Nat) (short : Refusal D) :
    Except (Refusal D) (Option (D × Act)) := spendAt enrollBase g cell units short

/-- Enrolment is a right (KERNEL-16): the sponsor acts through a World grant chain carrying
`enroll`, rooted at a founder's genesis grant, and spends one of its own grant's count. The new key
consented to this join (PROTOCOL-79): its join verifies under the key over `joinMessage` of the
World it names (`badJoin`); that the World it names is the receiving one is `receive`'s check
(`otherWorld`), so the derivation stays blind to the World's name (KERNEL-40). The member is born at
`memberId`, the digest of that consent, so the same consent enrolled twice is `World.admit`'s
`idTaken`. -/
def enroll (X : Ctx D) (look : Pinned D) (a : At D) (key : ByteArray) (next : D)
    (origin : D) (join : ByteArray) (via : D) : Except (Refusal D) (Draft D) := do
  let _ ← walk X look (worldId X) (.enroll 0) true grantDepthMax via a.actor
  let g ← readKind look via kindGrant
  let spend ← spendEnroll via g 1 (.enrollSpent via)
  req (X.verify key (joinMessage X origin a.actor next key) join) .badJoin
  let slots := slotsOf [(slotKey, key), (slotNext, X.env.bytes next),
    (slotSponsor, X.env.bytes a.actor)]
  pure ⟨[(memberId X origin a.actor next key, { kind := kindMember, discipline := .ram, slots })],
    spend.toList, [], []⟩

/-- Signed by the new key; the new key's digest must be the one precommitted. -/
def rotate (X : Ctx D) (look : Pinned D) (c : Call D) (key : ByteArray) (next : D) :
    Except (Refusal D) (Draft D) := do
  let u := c.unsigned
  let m ← readKind look u.member kindMember
  req (u.key = key) (.notPrecommitted u.member)
  let committed ← slotDigest X u.member m slotNext
  req (committed = nextKeyDigest X key) (.notPrecommitted u.member)
  let ops := [Op.set slotKey key, Op.set slotNext (X.env.bytes next)]
  pure ⟨[], [(u.member, .write ops)], [], []⟩

/-- `install pkg`: a ROM package cell, its id its content digest (KERNEL-3). -/
def install (X : Ctx D) (look : Pinned D) (c : Call D) (a : At D) (pkg : ByteArray) :
    Except (Refusal D) (Draft D) := do
  X.program.checkInstall look pkg
  pure ⟨bornAt X c a.base [{ kind := kindPackage, discipline := .rom, slots := [(0, pkg)] }], [], [], []⟩

def objectCell (X : Ctx D) (owner : D) (pkg : Option D) (laws : List D) (state : Slots) : Cell :=
  { kind := kindObject, discipline := .ram,
    slots := slotsOf ((pkg.map fun p => (slotPackage, X.env.bytes p)).toList ++
      [(slotOwner, X.env.bytes owner)] ++ lawSlots X laws ++ state) }

/-- A named package is a live, pinned package cell. -/
def checkPackage (look : Pinned D) : Option D → Except (Refusal D) Unit
  | none => .ok ()
  | some p => (readKind look p kindPackage).map fun _ => ()

def create (X : Ctx D) (look : Pinned D) (c : Call D) (a : At D) (pkg : Option D) (laws : List D)
    (state : Slots) : Except (Refusal D) (Draft D) := do
  let u := c.unsigned
  checkPackage look pkg
  checkLaws look laws
  checkState state
  let self := cellIdOf X.env (txIdOf X c) a.base
  X.program.judge look pkg laws state state (reqOf u self a.actor .birth a.caller)
  -- LANG-49: the heads of the package's relations are born with the object, in relation order
  let decls ← match pkg with
    | some p => X.program.rels look p self
    | none => pure []
  pure ⟨bornAt X c a.base [objectCell X a.actor pkg laws state], [], [],
    decls.zipIdx.map fun d => (.head self d.2, d.1)⟩

/-- The cell `install pkg` bears (`install`'s literal): ROM, the bytes in slot 0, at its content id `romIdOf`. -/
def packageCell (pkg : ByteArray) : Cell := { kind := kindPackage, discipline := .rom, slots := [(0, pkg)] }

/-- The view a receiver has after a birth earlier in its own call: `look`, and the cell `cell` live
at `id`. The only view a receiver reads beside the pinned one, and only for the cell its own call
bears (`createOf`'s package). -/
def withBorn (look : Pinned D) (id : D) (cell : Cell) : Pinned D := fun i =>
  if i = id then .ok (some cell) else look i

/-- `createOf pkg laws state` (KERNEL-77): an object of the package the bytes `pkg` install as, born
in one call and owned by the SIGNER (`c.unsigned.member`), whoever the actor. The package's id is its
content id, and the signer's pins decide:
* the signer pinned it LIVE: the package is installed already (a ROM cell is its content), and the
  object is `create`d of it, at the call's birth index;
* otherwise (not pinned, or pinned absent): `install pkg` (the one install receiver, its check), then
  `create` of the new id over the view that holds it (`withBorn`). Admission keeps its rules for the
  birth: an id already taken is `idTaken`, and a pinned-absent id that is also born is
  `bornTouched` (a born cell is never touched, KERNEL-11), so a call that reuses pins the package
  live and a call that installs does not pin it (the client's `derivePins` does both).
The object is born at the call's birth index and the package after it, so the object's id is the same
either way.
Spends nobody's authority: the signer could `install` and `create` the same cells itself; the
object it bears is the signer's, so a generator that makes one decides its laws and state, never
its owner. -/
def createOf (X : Ctx D) (look : Pinned D) (c : Call D) (a : At D) (pkg : ByteArray) (laws : List D)
    (state : Slots) : Except (Refusal D) (Draft D) := do
  let p := romIdOf X.env (packageCell pkg)
  let me : At D := ⟨c.unsigned.member, a.base, a.caller⟩
  match look p with
  | .ok (some _) => create X look c me (some p) laws state
  | .error (.unpinned _) | .ok none => do
      let i ← install X look c ⟨a.actor, a.base + 1, a.caller⟩ pkg
      let o ← create X (withBorn look p (packageCell pkg)) c me (some p) laws state
      pure (o.append i)
  | .error e => .error e

def applyEdits (s : Slots) (edits : List (Nat × Option ByteArray)) : Slots :=
  edits.foldl (fun s e => match e.2 with
    | some v => s.set (stateBase + e.1) v
    | none => s.erase (stateBase + e.1)) s

def write (X : Ctx D) (look : Pinned D) (c : Call D) (a : At D) (obj : D)
    (edits : List (Nat × Option ByteArray)) (via : Option D) : Except (Refusal D) (Draft D) := do
  let u := c.unsigned
  let cell ← readKind look obj kindObject
  let pkg ← packageOf X obj cell
  req pkg.isNone (.hasMethods obj)
  let principal ← ownerAuthority X look a.actor obj cell .mutate via
  forEx (fun e => req (stateBase + e.1 < Bounds.slotKeyLimit) (.stateKey e.1)) edits
  let old := stateOf cell
  let new := applyEdits old edits
  let laws ← lawsOf X obj cell
  X.program.judge look none laws old new (reqOf u obj principal .write a.caller)
  pure ⟨[], writeOf obj (diffOps old new), [], []⟩

/-- Replace a data object's extra laws; the laws in force judge the change. -/
def law (X : Ctx D) (look : Pinned D) (c : Call D) (a : At D) (obj : D) (laws' : List D) (via : Option D) :
    Except (Refusal D) (Draft D) := do
  let u := c.unsigned
  let cell ← readKind look obj kindObject
  let pkg ← packageOf X obj cell
  req pkg.isNone (.hasMethods obj)
  let principal ← ownerAuthority X look a.actor obj cell .mutate via
  checkLaws look laws'
  let laws ← lawsOf X obj cell
  X.program.judge look none laws (stateOf cell) (stateOf cell) (reqOf u obj principal (.relaw laws') a.caller)
  -- LANG-19 (KERNEL-27): the ADDED laws judge the state they are adopted over, as `.adopt`, so a
  -- law that would deny it cannot be installed; a kept law already judged the change as `relaw`
  -- (LANG-4: re-judging it on `adopt` refused every relaw that keeps a quorum)
  X.program.judge look none (laws'.filter fun l => decide (l ∉ laws)) (stateOf cell) (stateOf cell)
    (reqOf u obj principal (.adopt laws') a.caller)
  pure ⟨[], writeOf obj (diffOps (lawSlotsOf cell) (lawSlots X laws')), [], []⟩

def requireMethods (obj : D) : Option D → Except (Refusal D) D
  | none => .error (.noMethods obj)
  | some p => .ok p

/-- What an invoke hands the program to run: the object's cell, its package, and the request,
after the owner authority (KERNEL-25). `invoke` is this, then the run; a measurement of the run
(THE BAR's WASTE lines, LANG's `runMeasured`) starts from the same inputs, never a restatement. -/
def invokeRun (X : Ctx D) (look : Pinned D) (c : Call D) (actor : D) (caller : Option D) (obj : D) (method : Nat)
    (via : Option D) : Except (Refusal D) (Cell × D × Req D) := do
  let u := c.unsigned
  let cell ← readKind look obj kindObject
  let pkg ← packageOf X obj cell
  let p ← requireMethods obj pkg
  let principal ← ownerAuthority X look actor obj cell (.invoke method) via
  pure (cell, p, reqOf u obj principal (.invoke method) caller)

/-- How far a call's tree has got (LEDGER-8): the objects invoked so far (re-entry is
`revisited`), the ticks left of the tree's one pool, the fresh births so far. -/
structure Walk (D : Type) where
  visited : List D
  pool : Nat
  born : Nat

/-- What derives one call of a tree: from where the walk is, as an actor, a Body. -/
abbrev Sub (D : Type) := Walk D → D → Body D → Except (Refusal D) (Draft D × Walk D)

/-- The calls a run returned, derived depth-first, each AS the calling object `obj` (KERNEL-28 (b)),
by `sub`: the deriver one level down. -/
def callStep (sub : Sub D) (obj : D) (acc : Draft D × Walk D) (b : Body D) :
    Except (Refusal D) (Draft D × Walk D) := do
  let r ← sub acc.2 obj b
  pure (acc.1.append r.1, r.2)

def deriveCalls (sub : Sub D) (obj : D) (own : Draft D) (wk : Walk D) (calls : List (Body D)) :
    Except (Refusal D) (Draft D × Walk D) :=
  calls.foldlM (callStep sub obj) (own, wk)

/-- `invoke`: the owner's authority (KERNEL-25), the run under what the pool has left (its used
ticks asserted, `overTicks`), the laws over old and new, then the calls the run returned, as the
object. An object already invoked in the tree is `revisited`. -/
def invoke (X : Ctx D) (look : Pinned D) (rv : RowView D) (c : Call D) (sub : Sub D) (wk : Walk D) (actor : D)
    (caller : Option D) (obj : D) (method : Nat) (args : ByteArray) (budget : Nat) (via : Option D) :
    Except (Refusal D) (Draft D × Walk D) := do
  req (!wk.visited.contains obj) (.revisited obj)
  let (cell, p, r) ← invokeRun X look c actor caller obj method via
  let old := stateOf cell
  let fuel := min budget wk.pool
  let (new, calls, rows, used) ← X.program.run look rv p old method args r fuel
  req (decide (used ≤ fuel)) .overTicks
  -- LANG-49: a run edits only its own object's rows (law 4: asserted where row edits enter)
  forEx (fun e => req (decide (e.1.under.1 = obj)) (.rowParent obj)) rows
  checkState new
  let laws ← lawsOf X obj cell
  X.program.judge look (some p) laws old new r
  req (decide (calls.length ≤ Bounds.callsMax)) .tooManyCalls
  deriveCalls sub obj ⟨[], writeOf obj (diffOps old new), [], rows⟩
    { wk with visited := obj :: wk.visited, pool := wk.pool - used } calls

/-- The enrolment count a list of rights grants (several `enroll` rights add up). -/
def enrollUnits : List Right → Nat
  | [] => 0
  | .enroll n :: rest => n + enrollUnits rest
  | _ :: rest => enrollUnits rest

/-- The transfer cap a list of rights grants (several add up). -/
def transferUnits : List Right → Nat
  | [] => 0
  | .transfer n :: rest => n + transferUnits rest
  | _ :: rest => transferUnits rest

/-- The credit cap a list of rights grants (several add up). -/
def creditUnits : List Right → Nat
  | [] => 0
  | .credit n :: rest => n + creditUnits rest
  | _ :: rest => creditUnits rest

def isEnroll : Right → Bool
  | .enroll _ => true
  | _ => false

def isTransfer : Right → Bool
  | .transfer _ => true
  | _ => false

def isCredit : Right → Bool
  | .credit _ => true
  | _ => false

/-- A counted right: one whose grant holds a ledger. -/
def isCounted (r : Right) : Bool := isEnroll r || isTransfer r || isCredit r

/-- A grant's right slots: every uncounted right as a key, and for each counted kind one ledger
entry with the sum of its counts. -/
def rightSlots (rights : List Right) : List (Nat × ByteArray) :=
  (rights.filter (!isCounted ·)).map (fun r => (rightKey r, ByteArray.empty)) ++
    ((if rights.any isEnroll then [(enrollBase, countBytes (enrollUnits rights))] else []) ++
     (if rights.any isTransfer then [(transferBase, countBytes (transferUnits rights))] else []) ++
     (if rights.any isCredit then [(creditBase, countBytes (creditUnits rights))] else []))

/-- A grant's counted rights fit its target (KERNEL-60), refused `rightTarget` otherwise: at most
one counted kind (one ledger per grant, so a carve never skips one), `enroll` only on the World,
`transfer` and `credit` never on it. A cap an account cannot hold (past `capMax`) is `overflow`. -/
def checkRights (X : Ctx D) (target : D) (rights : List Right) : Except (Refusal D) Unit := do
  let e := rights.any isEnroll
  let v := rights.any isTransfer || rights.any isCredit
  req (!(rights.any isTransfer && rights.any isCredit) && !(e && v) &&
    (!e || decide (target = worldId X)) && (!v || decide (target ≠ worldId X))) (.rightTarget target)
  req (decide (transferUnits rights ≤ capMax ∧ creditUnits rights ≤ capMax)) (.overflow target)

/-- An attenuated grant narrows a parent the signer holds on the same target; a counted right's
count (an enrolment count, a transfer or credit cap) is carved out of the parent's (the parent's
ledger is the effect; `checkRights` has made it the grant's only counted kind). World rights and enrolment
rights are never rooted here (`unrooted`): only genesis roots them. -/
def checkParent (X : Ctx D) (look : Pinned D) (actor : D) (target : D) (rights : List Right) :
    Option D → Except (Refusal D) (Option (D × Act))
  | none => do
      req (!(target = worldId X || rights.any isEnroll)) (.unrooted target)
      pure none
  | some p => do
      let pc ← readKind look p kindGrant
      let pt ← slotDigest X p pc grantTarget
      req (pt = target) (.grantTarget p)
      let pg ← slotDigest X p pc grantGrantee
      req (pg = actor) (.noGrant p)
      forEx (fun r => req (pc.slots.get (rightKey r)).isSome (.grantWidens p)) rights
      if rights.any isEnroll then spendEnroll p pc (enrollUnits rights) (.grantWidens p)
      else if rights.any isTransfer then spendAt transferBase p pc (transferUnits rights) (.grantWidens p)
      else if rights.any isCredit then spendAt creditBase p pc (creditUnits rights) (.grantWidens p)
      else pure none

/-- A grant names a live member, a live object (an object acts through grants naming it,
KERNEL-28 (b)), or the World itself: a public grant, held by every enrolled member (KERNEL-26,
`granteeHolds`). Any other id is refused by its read's name. -/
def checkGrantee (X : Ctx D) (look : Pinned D) (grantee : D) : Except (Refusal D) Unit :=
  if grantee = worldId X then pure ()
  else match readKind look grantee kindObject with
    | .ok _ => pure ()
    | .error _ => (readKind look grantee kindMember).map fun _ => ()

def grant (X : Ctx D) (look : Pinned D) (c : Call D) (a : At D) (target grantee : D) (rights : List Right)
    (parent : Option D) : Except (Refusal D) (Draft D) := do
  checkGrantee X look grantee
  checkRights X target rights
  let carve ← checkParent X look a.actor target rights parent
  let slots := slotsOf ([(grantTarget, X.env.bytes target), (grantGrantee, X.env.bytes grantee),
      (grantIssuer, X.env.bytes a.actor)] ++
    (parent.map fun p => (grantParent, X.env.bytes p)).toList ++ rightSlots rights)
  pure ⟨bornAt X c a.base [{ kind := kindGrant, discipline := .appendOnly, slots }], carve.toList, [], []⟩

/-- Who may retire the pinned live cell `x` (KERNEL-70), by its kind: a grant its issuer
(`notIssuer`); an object its owner (`notOwner`), every law in force (the package's, then the extra
laws) judging the occasion `retire` over its last state; an account its owner (`notOwner`), once
its balance and floor are both 0 (`valueRemains`), so a retirement moves no value. Nothing retires a
member, a package or the authority (`notRetirable`): a member roots authority (the owner of cells,
the issuer of grants) that no cell lists, so its end would leave grants nobody can revoke. -/
def retireCheck (X : Ctx D) (look : Pinned D) (c : Call D) (a : At D) (x : D) :
    Except (Refusal D) Unit := do
  let cell ← match look x with
    | .error e => .error e
    | .ok none => .error (.missingCell x)
    | .ok (some cell) => .ok cell
  if cell.kind = kindGrant then
    let issuer ← slotDigest X x cell grantIssuer
    req (issuer = a.actor) (.notIssuer x)
  else if cell.kind = kindObject then
    let owner ← slotDigest X x cell slotOwner
    req (owner = a.actor) (.notOwner x)
    let pkg ← packageOf X x cell
    let laws ← lawsOf X x cell
    X.program.judge look pkg laws (stateOf cell) (stateOf cell) (reqOf c.unsigned x a.actor .retire a.caller)
  else if cell.kind = kindAccount then
    let owner ← slotDigest X x cell slotOwner
    req (owner = a.actor) (.notOwner x)
    match Value.ofCell cell with
    | some v => req (decide (v.balance = 0 ∧ v.floor = 0)) (.valueRemains x)
    | none => .error (.malformedCell x Value.balanceKey)
  else .error (.notRetirable x)

/-- `retire x` (KERNEL-70): `retireCheck`, then the one effect, the retirement of `x`. The kernel
credits its weight back to the World's allowance (KERNEL-19) and leaves a tombstone; a retired
object's relation heads leave with it, and an object still holding rows is `rowsRemain`. -/
def retire (X : Ctx D) (look : Pinned D) (c : Call D) (a : At D) (x : D) : Except (Refusal D) (Draft D) := do
  retireCheck X look c a x
  pure ⟨[], [(x, .retire)], [], []⟩

/-- A receiver's Draft, and the walk past its fresh births. -/
def stepped (wk : Walk D) (d : Except (Refusal D) (Draft D)) : Except (Refusal D) (Draft D × Walk D) :=
  d.map fun d => (d, { wk with born := wk.born + d.creates.length })

/-- One receiver of a call's tree, as `actor`; `sub` derives an invoke's calls one level down. -/
def dispatch (X : Ctx D) (look : Pinned D) (rv : RowView D) (c : Call D) (sub : Sub D) (wk : Walk D) (actor : D)
    (caller : Option D) :
    Body D → Except (Refusal D) (Draft D × Walk D)
  | .enroll key next origin join via => stepped wk (enroll X look ⟨actor, wk.born, caller⟩ key next origin join via)
  | .rotate key next => stepped wk (rotate X look c key next)
  | .install pkg => stepped wk (install X look c ⟨actor, wk.born, caller⟩ pkg)
  | .create pkg laws state => stepped wk (create X look c ⟨actor, wk.born, caller⟩ pkg laws state)
  | .createOf pkg laws state => stepped wk (createOf X look c ⟨actor, wk.born, caller⟩ pkg laws state)
  | .write obj edits via => stepped wk (write X look c ⟨actor, wk.born, caller⟩ obj edits via)
  | .law obj laws via => stepped wk (law X look c ⟨actor, wk.born, caller⟩ obj laws via)
  | .invoke obj method args budget via => invoke X look rv c sub wk actor caller obj method args budget via
  | .grant target grantee rights parent =>
      stepped wk (grant X look c ⟨actor, wk.born, caller⟩ target grantee rights parent)
  | .retire x => stepped wk (retire X look c ⟨actor, wk.born, caller⟩ x)
  | .issue cap => stepped wk (issue X c ⟨actor, wk.born, caller⟩ cap)
  | .account asset owner => stepped wk (account X asset owner)
  | .transfer src dst amount via once => stepped wk (transfer X look ⟨actor, wk.born, caller⟩ src dst amount via once)
  | .credit well acct amount via => stepped wk (credit X look ⟨actor, wk.born, caller⟩ well acct amount via)

/-- The deriver of a call made `n` levels above the depth bound: a call of a kind an object may
not exercise is `notCallable`, a call past the bound `callTooDeep`; otherwise THE SAME `dispatch`
the signed call goes through, with the calling object as actor and as caller (`effect_as_signed`). -/
def tree (X : Ctx D) (look : Pinned D) (rv : RowView D) (c : Call D) : Nat → Sub D
  | 0 => fun _ _ _ => .error .callTooDeep
  | n + 1 => fun wk obj b =>
      if b.callable then dispatch X look rv c (tree X look rv c n) wk obj (some obj) b
      else .error (.notCallable b.kindName)

/-- The pool a signed call's tree runs on: an invoke's signed budget, capped at
`Bounds.treeTicksMax`; nothing else runs a program. -/
def poolOf : Body D → Nat
  | .invoke _ _ _ budget _ => min budget Bounds.treeTicksMax
  | _ => 0

/-- The signed call's Draft: its Body at the signer, its calls down to `callDepthMax`; and the ticks
the tree used of its pool (the pool at the start less what is left: 0 for every Body but an
invoke), which the Turn carries for the kernel's meter (DESIGN-OBS §1.3). -/
def deriveWithTicks (X : Ctx D) (look : Pinned D) (rv : RowView D) (c : Call D) :
    Except (Refusal D) (Draft D × Nat) :=
  (dispatch X look rv c (tree X look rv c Bounds.callDepthMax) ⟨[], poolOf c.unsigned.body, 0⟩
    c.unsigned.member none c.unsigned.body).map fun r => (r.1, poolOf c.unsigned.body - r.2.pool)

/-- The signed call's Draft: its Body at the signer, its calls down to `callDepthMax`. -/
def derive (X : Ctx D) (look : Pinned D) (rv : RowView D) (c : Call D) : Except (Refusal D) (Draft D) :=
  (deriveWithTicks X look rv c).map (·.1)

/-- A rotation is signed by the incoming key; every other call by the member's current key. -/
def keyRule (look : Pinned D) (u : Unsigned D) : Except (Refusal D) Unit :=
  match u.body with
  | .rotate _ _ => .ok ()
  | _ => checkKey look u

/-- The signed call's Turn: its tree's Draft, sealed ONCE (KERNEL-28 (c)). -/
def deriveTurn (X : Ctx D) (look : Pinned D) (rv : RowView D) (c : Call D) : Except (Refusal D) (Turn D) := do
  let (d, ticks) ← deriveWithTicks X look rv c
  sealTurn X c d.creates d.effects d.nullifiers d.rows ticks

/-- Derive from the pinned view: signature, key, then the call's tree. -/
def receiveWith (X : Ctx D) (look : Pinned D) (rv : RowView D) (c : Call D) : Except (Refusal D) (Turn D) := do
  checkSignature X c
  keyRule look c.unsigned
  deriveTurn X look rv c

/-- THE derivation: a signed call against a World, through the caller's pins only. The FIRST
check is the World the call names (KERNEL-24): a call for another World is `wrongWorld`, never
`badSignature` or `unknownKey`, whatever else is wrong with it. Past the signature, the World an
enrolment's join names (PROTOCOL-79): a consent to join another World is `otherWorld`. Then
`receiveWith`'s key rule and tree, which read the World's name nowhere
(`Kernel.Proofs.Carry.receiveWith_world`). -/
def receive (X : Ctx D) (w : World D) (c : Call D) : Except (Refusal D) (Turn D) := do
  req (c.unsigned.world = w.origin) .wrongWorld
  checkSignature X c
  req (c.unsigned.body.joinOrigin.all (· = w.origin)) .otherWorld
  keyRule (pinned X.env w c.unsigned.pins) c.unsigned
  deriveTurn X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c

end Nanodregg.Kernel.Receive
