/-
# Spec.Sim.Auth — the open kernel B1 refuses, and the inputs of its runs

The kernel whose `write` checks no owner (`openKernel`), a genesis World with two founders, founder 0's
data object, and the two writes of it (founder 1's, the owner's). A def-module: what is computed of
these is stated in `Spec.Proofs.Auth` (`native_decide` facts).
-/
import Spec.Sim.Run

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-- The kernel's `write`, with the owner check removed (`ownerAuthority` answering the actor): any
member's signed write of any data object derives, judged by its laws as the signer's. -/
def openWrite (X : Ctx Digest) (w : World Digest) (c : Call Digest) (obj : Digest)
    (edits : List (Nat × Option ByteArray)) : Except (Refusal Digest) (Turn Digest) := do
  req (c.unsigned.world = w.origin) .wrongWorld
  let look := pinned X.env w c.unsigned.pins
  checkSignature X c
  checkKey look c.unsigned
  let cell ← readKind look obj kindObject
  let pkg ← packageOf X obj cell
  req pkg.isNone (.hasMethods obj)
  forEx (fun e => req (stateBase + e.1 < Bounds.slotKeyLimit) (.stateKey e.1)) edits
  let old := stateOf cell
  let new := applyEdits old edits
  let laws ← lawsOf X obj cell
  X.program.judge look none laws old new (reqOf c.unsigned obj c.unsigned.member .write none)
  sealTurn X c [] (writeOf obj (diffOps old new)) []

/-- The kernel's receivers, except that a signed `write` is `openWrite`. -/
def openReceive (w : World Digest) (c : Call Digest) : Except (Refusal Digest) (Turn Digest) :=
  match c.unsigned.body with
  | .write obj edits _ => openWrite Host.Deployed.X w c obj edits
  | _ => receive Host.Deployed.X w c

/-- **The open kernel**: any member may write any data object. -/
def openKernel (d : ByteArray → ByteArray) : System Digest := { deployed d with receive := openReceive }

/-- The run's second founder: its key and its precommitted next key. -/
def aKey1 : ByteArray := Ed25519.publicKey (wSeed "f1")
def aNext1 : ByteArray := Ed25519.publicKey (wSeed "f1-next")

/-- A genesis World with TWO founders. -/
def aGenesis : World Digest :=
  genesisWorld Xd "spec".toUTF8 "spec-auth".toUTF8 100000000
    [(wKey, nextKeyDigest Xd wNext), (aKey1, nextKeyDigest Xd aNext1)] Authority.none

def aOwner : Digest := founderId Xd aGenesis.origin 0
def aOther : Digest := founderId Xd aGenesis.origin 1

/-- Founder 0 creates a data object (no package, no laws) holding one state slot. -/
def aCreate : Call Digest :=
  let u : Unsigned Digest :=
    { world := aGenesis.origin, member := aOwner, key := wKey, notBefore := 0, validUntil := 101,
      pins := [(aOwner, pinOf Xd.env (aGenesis.entry Xd.env aOwner))], maxCharge := 1000000,
      body := .create none [] [(stateBase, "x".toUTF8)] }
  ⟨u, Ed25519.sign (wSeed "f0") (Xd.callMessage u)⟩

def aLog : List (Step Digest) := (staged aGenesis aCreate).2
def aWorld : World Digest := (staged aGenesis aCreate).1
def aObj : Digest := cellIdOf Xd.env (txIdOf Xd aCreate) 0

/-- A write of the object at state key 0, by `m` under key `key` signed from `seed`. -/
def aWriteBy (m : Digest) (key : ByteArray) (seed : String) : Call Digest :=
  let u : Unsigned Digest :=
    { world := aWorld.origin, member := m, key, notBefore := 0, validUntil := 101,
      pins := [(m, pinOf Xd.env (aWorld.entry Xd.env m)), (aObj, pinOf Xd.env (aWorld.entry Xd.env aObj))],
      maxCharge := 1000000, body := .write aObj [(0, some "y".toUTF8)] none }
  ⟨u, Ed25519.sign (wSeed seed) (Xd.callMessage u)⟩

/-- Founder 1 (not the owner, holding no grant) writes founder 0's object. -/
def aWrite : Call Digest := aWriteBy aOther aKey1 "f1"

/-- Founder 0, the owner, writes it. -/
def aOwnWrite : Call Digest := aWriteBy aOwner wKey "f0"

end Nanodregg.Spec
