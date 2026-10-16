/-
# Kernel.Receive.Call — the signed call, the receive refusals, the pinned view, the seal

A receiver derives a `Turn` from a signed call; the Host then commits `World.admit` of exactly
that Turn (derive-then-admit). There is no intermediate intent type.

A receiver never sees the World. It sees the `Pinned` view: the live cell at an id the caller
PINNED, and the refusal `unpinned` for any other id. So a derivation depends only on the cells
the signer observed (`Kernel.Proofs.Receive.receive_congr`): a consent provider folding its own
copy of the log derives the same Turn the Host does whenever their pinned cells agree, and
`World.admit`'s pin check refuses the Turn when the Host's cells are not what the signer saw.
-/
import Kernel.World

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

/-- What a call asks for, one constructor per operation kind. -/
inductive Body (D : Type)
  /-- install a package: canonical package bytes (LANG's encoding) -/
  | install (pkg : ByteArray)
  /-- create an object of package `pkg`, judged also by the extra law packages `laws`,
  with initial state slots (keys at or above `stateBase`) -/
  | create (pkg : D) (laws : List D) (state : Slots)
  /-- run `method` of object `obj`; `via` is the grant the signer acts through, if any -/
  | invoke (obj : D) (method : Nat) (args : ByteArray) (budget : Nat) (via : Option D)
  /-- let `grantee` invoke `methods` of `target` as the signer (or, with `parent`, as the
  principal of that grant, attenuated) -/
  | grant (target : D) (grantee : ByteArray) (methods : List Nat) (parent : Option D)
  /-- retire a grant the signer issued -/
  | revoke (grant : D)
  deriving DecidableEq

/-- What the caller signs. `pins` is the caller's observation; `maxCharge` the price ceiling. -/
structure Unsigned (D : Type) where
  signer : ByteArray
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
  /-- the derivation needed a cell the caller did not pin -/
  | unpinned (cell : D)
  | missingCell (cell : D)
  | wrongKind (cell : D) (expected : Nat)
  /-- a slot the receive layer reads does not hold what it must (a digest, a key) -/
  | malformedCell (cell : D) (key : Nat)
  /-- the law of package `law` refused the write, with LANG's name for why -/
  | lawDenied (law : D) (reason : String)
  /-- LANG refused for a reason that is not a law: type error, budget, method error -/
  | program (reason : String)
  /-- LANG returned a state slot below `stateBase` -/
  | stateKey (key : Nat)
  | noGrant (grant : D)
  | grantTarget (grant : D)
  | grantMethod (grant : D) (method : Nat)
  /-- an attenuated grant may only narrow its parent -/
  | grantWidens (parent : D) (method : Nat)
  | notIssuer (grant : D)
  | grantTooDeep
  | overPrice (charge : Nat)
  deriving DecidableEq, Repr

/-- A receiver's only access to state: live cells at pinned ids. -/
abbrev Pinned (D : Type) := D → Except (Refusal D) (Option Cell)

/-- Who a call acts for. `agent` signed; `principal` is whose authority it exercises (the
agent, or the root issuer of the grant chain it acts through). Laws judge by these. -/
structure Req where
  agent : ByteArray
  principal : ByteArray
  deriving DecidableEq

/-- What KERNEL's receivers need from LANG. Every function reads state only through the pinned
view, so `receive_congr` covers LANG's reads too. LANG's glue module instantiates it. -/
structure Program (D : Type) where
  /-- type-check canonical package bytes against their (pinned) imports; the package's id is
  its ROM cell id -/
  checkInstall : Pinned D → ByteArray → Except (Refusal D) Unit
  /-- judge an initial state by the package's and the extra laws (old = new = state) -/
  checkCreate : Pinned D → (pkg : D) → (laws : List D) → Slots → Req → Except (Refusal D) Unit
  /-- run a method and every law; the object's new state slots -/
  run : Pinned D → (pkg : D) → (laws : List D) → (state : Slots) → (method : Nat) →
    (args : ByteArray) → Req → (budget : Nat) → Except (Refusal D) Slots

/-- What the receive layer needs beyond the kernel's `Env`: the call's canonical bytes (the
signed message and the logged event), the digest decoder, the verifier, the program. CODEC
supplies the encodings; the verifier's answer is a premise asserted where it enters (law 4). -/
structure Ctx (D : Type) where
  env : Env D
  unsignedBytes : Unsigned D → ByteArray
  callBytes : Call D → ByteArray
  /-- inverse of `env.bytes` on canonical digests -/
  digestOf : ByteArray → Option D
  verify : (signer message signature : ByteArray) → Bool
  program : Program D

/-- Cell kinds and slot layout of the receive layer. -/
def kindPackage : Nat := 1
def kindObject : Nat := 2
def kindGrant : Nat := 3
/-- Object: slot 0 the package id, slots `1 ≤ k < stateBase` the extra law ids, state above. -/
def stateBase : Nat := 16
/-- Grant: 0 target, 1 grantee, 2 issuer, 3 parent (absent at a root), `stateBase + m` method m. -/
def grantTarget : Nat := 0
def grantGrantee : Nat := 1
def grantIssuer : Nat := 2
def grantParent : Nat := 3
/-- The longest grant chain an invoke walks. -/
def grantDepthMax : Nat := 8

variable {D : Type} [Ord D]

def pinned [DecidableEq D] (w : World D) (pins : List (D × D)) : Pinned D := fun c =>
  if pins.any (fun p => p.1 = c) then .ok (w.live c) else .error (.unpinned c)

/-- The transaction id: the digest of the call's canonical bytes. -/
def txIdOf (X : Ctx D) (c : Call D) : D :=
  X.env.hash ("nanodregg/kernel/tx/v1".toUTF8 ++ X.callBytes c)

/-- The Turn a call's effect becomes: the caller's window and pins, the call as the event,
the exact charge (refused above the signed ceiling). -/
def sealTurn (X : Ctx D) (c : Call D) (creates : List Cell) (legs : List (Leg D))
    (retires : List D) : Except (Refusal D) (Turn D) :=
  let t0 : Turn D :=
    { txId := txIdOf X c, notBefore := c.unsigned.notBefore, validUntil := c.unsigned.validUntil,
      pins := c.unsigned.pins, creates, legs, retires, nullifiers := [], charge := 0,
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
