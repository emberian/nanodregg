/-
# Kernel.Receive.Derive — one derivation per operation kind, and `receive`

`receive X w c` is the whole of "what may this call do": signature, authority (the signer, or
a grant chain), the program's laws, the price. Its result is exactly the `Turn` the Host hands
to `World.admit`.
-/
import Kernel.Receive.Call

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- Signature first: nothing is derived for an unsigned call. -/
def checkSignature (X : Ctx D) (c : Call D) : Except (Refusal D) Unit :=
  if X.verify c.unsigned.signer (X.unsignedBytes c.unsigned) c.signature then .ok ()
  else .error .badSignature

/-- Build slots in canonical order whatever order the pairs come in. -/
def slotsOf (ps : List (Nat × ByteArray)) : Slots := ps.foldl (fun s p => s.set p.1 p.2) []

/-- `install pkg`: a ROM package cell, its id its content digest. LANG checks it. -/
def install (X : Ctx D) (look : Pinned D) (c : Call D) (pkg : ByteArray) :
    Except (Refusal D) (Turn D) := do
  X.program.checkInstall look pkg
  sealTurn X c [{ kind := kindPackage, discipline := .rom, slots := [(0, pkg)] }] [] []

/-- The object cell `create` births: package id, extra law ids, the initial state. -/
def objectCell (X : Ctx D) (pkg : D) (laws : List D) (state : Slots) : Cell :=
  { kind := kindObject, discipline := .ram,
    slots := slotsOf ((0, X.env.bytes pkg) :: laws.zipIdx.map (fun (l, i) => (1 + i, X.env.bytes l))
      ++ state) }

def checkState (state : Slots) : Except (Refusal D) Unit :=
  forEx (fun p => if stateBase ≤ p.1 then .ok () else .error (.stateKey p.1)) state

/-- `create pkg laws state`: a RAM object cell, judged by its laws at birth. -/
def create (X : Ctx D) (look : Pinned D) (c : Call D) (pkg : D) (laws : List D) (state : Slots) :
    Except (Refusal D) (Turn D) := do
  let _ ← readKind look pkg kindPackage
  forEx (fun l => (readKind look l kindPackage).map fun _ => ()) laws
  req (laws.length < stateBase) (.program "too many extra laws")
  checkState state
  let req : Req := { agent := c.unsigned.signer, principal := c.unsigned.signer }
  X.program.checkCreate look pkg laws state req
  sealTurn X c [objectCell X pkg laws state] [] []

/-- The principal a grant chain exercises for `agent` on `obj.method`, walking at most
`fuel` links; every link must be pinned, live, aimed at `obj`, held by the next agent, and
grant the method. -/
def walk (X : Ctx D) (look : Pinned D) (obj : D) (method : Nat) :
    Nat → D → ByteArray → Except (Refusal D) ByteArray
  | 0, _, _ => .error .grantTooDeep
  | fuel + 1, g, agent => do
      let cell ← readKind look g kindGrant
      let target ← slotDigest X g cell grantTarget
      req (target = obj) (.grantTarget g)
      req (cell.slots.get grantGrantee = some agent) (.noGrant g)
      req (cell.slots.get (stateBase + method)).isSome (.grantMethod g method)
      let some issuer := cell.slots.get grantIssuer | .error (.malformedCell g grantIssuer)
      match cell.slots.get grantParent with
      | none => pure issuer
      | some pb =>
          match X.digestOf pb with
          | none => .error (.malformedCell g grantParent)
          | some parent => walk X look obj method fuel parent issuer

/-- Whose authority an invoke exercises: the signer's own, or the root issuer of its grant. -/
def principalOf (X : Ctx D) (look : Pinned D) (c : Call D) (obj : D) (method : Nat) :
    Option D → Except (Refusal D) ByteArray
  | none => .ok c.unsigned.signer
  | some g => walk X look obj method grantDepthMax g c.unsigned.signer

/-- The slot operations that turn `old` into `new`. -/
def diffOps (old new : Slots) : List Op :=
  (new.filter fun p => old.get p.1 != some p.2).map (fun p => .set p.1 p.2) ++
  (old.filter fun p => (new.get p.1).isNone).map (fun p => .erase p.1)

/-- `invoke obj method args budget via`: LANG runs the method and the laws; the receiver turns
the new state into one leg of exactly the changed state slots. -/
def invoke (X : Ctx D) (look : Pinned D) (c : Call D) (obj : D) (method : Nat) (args : ByteArray)
    (budget : Nat) (via : Option D) : Except (Refusal D) (Turn D) := do
  let cell ← readKind look obj kindObject
  let pkg ← slotDigest X obj cell 0
  let laws ← mapEx (fun p => slotDigest X obj cell p.1)
    (cell.slots.filter fun p => 1 ≤ p.1 && p.1 < stateBase)
  let principal ← principalOf X look c obj method via
  let req : Req := { agent := c.unsigned.signer, principal }
  let state := cell.slots.filter fun p => stateBase ≤ p.1
  let new ← X.program.run look pkg laws state method args req budget
  checkState new
  let ops := diffOps state new
  sealTurn X c [] (if ops.isEmpty then [] else [{ cell := obj, ops }]) []

/-- An attenuated grant narrows a parent the signer holds on the same target. -/
def checkParent (X : Ctx D) (look : Pinned D) (c : Call D) (target : D) (methods : List Nat) :
    Option D → Except (Refusal D) Unit
  | none => .ok ()
  | some p => do
      let pc ← readKind look p kindGrant
      let pt ← slotDigest X p pc grantTarget
      req (pt = target) (.grantTarget p)
      req (pc.slots.get grantGrantee = some c.unsigned.signer) (.noGrant p)
      forEx (fun m => if (pc.slots.get (stateBase + m)).isSome then .ok ()
        else .error (.grantWidens p m)) methods

/-- `grant target grantee methods parent`: a retirable grant cell. With a parent, the signer
must hold the parent and may only narrow it. -/
def grant (X : Ctx D) (look : Pinned D) (c : Call D) (target : D) (grantee : ByteArray)
    (methods : List Nat) (parent : Option D) : Except (Refusal D) (Turn D) := do
  checkParent X look c target methods parent
  let base : List (Nat × ByteArray) :=
    [(grantTarget, X.env.bytes target), (grantGrantee, grantee), (grantIssuer, c.unsigned.signer)]
  let par : List (Nat × ByteArray) := (parent.map fun p => (grantParent, X.env.bytes p)).toList
  let slots := slotsOf (base ++ par ++ methods.map fun m => (stateBase + m, ByteArray.empty))
  let cell : Cell := { kind := kindGrant, discipline := .appendOnly, slots }
  sealTurn X c [cell] [] []

/-- `revoke g`: the issuer retires the grant; every chain through it dies with it. -/
def revoke (X : Ctx D) (look : Pinned D) (c : Call D) (g : D) : Except (Refusal D) (Turn D) := do
  let cell ← readKind look g kindGrant
  req (cell.slots.get grantIssuer = some c.unsigned.signer) (.notIssuer g)
  sealTurn X c [] [] [g]

/-- Derive from the pinned view. -/
def receiveWith (X : Ctx D) (look : Pinned D) (c : Call D) : Except (Refusal D) (Turn D) := do
  checkSignature X c
  match c.unsigned.body with
  | .install pkg => install X look c pkg
  | .create pkg laws state => create X look c pkg laws state
  | .invoke obj method args budget via => invoke X look c obj method args budget via
  | .grant target grantee methods parent => grant X look c target grantee methods parent
  | .revoke g => revoke X look c g

/-- THE derivation: a signed call against a World, through the caller's pins only. -/
def receive (X : Ctx D) (w : World D) (c : Call D) : Except (Refusal D) (Turn D) :=
  receiveWith X (pinned w c.unsigned.pins) c

end Nanodregg.Kernel.Receive
