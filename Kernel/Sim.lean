/-
# Kernel.Sim — the seeded simulation's TOY parameters (the generator is `Kernel.Sim.Gen`)

`lake exe kernel-sim --seeds N` runs N seeded scenarios under the DEPLOYED parameters
(`Kernel.Sim.Deployed`); these toy parameters have no `kernel-sim` run (GATES-14: the carry-budget
plant is vacuous at an 8-byte digest) and serve `lang-journey`, `host-sim` and the codec teeth. Each drives the REAL
receive path (`Receive.submit`: journal, then the receivers, then `World.admit`) with honest and
adversarial calls, checks every verdict against the one the generator built the call to get (by
refusal NAME), restarts the "Host" from a fold of its own log at random points, and at the end
requires

* the follower (`World.fold` from genesis over the admitted log) to reach the Host's World,
* the follower's re-derivation (`Receive.rederiveLog`: each step's event decoded with CODEC's
  decoder and re-derived by `Receive.rederive`, the step `host follow` takes) to accept the same
  log and reach the same World, and to name a forged write `eventMismatch` at its index,
* every planted refusal (`Gen.planted`) to have been met by its name,
* every revocation to have handed the grant cell's weight back to the budget (KERNEL-19).

Toy PARAMETERS in the real pipeline (memory: never toy code beside it): the digest is a `UInt64`
spelled by CODEC's `Stream.u64`, the hash FNV-1a, a signature the hash of key ‖ message. Turns,
cells and calls are CODEC's codecs (`Codec.Kernel`, generic in the digest's codec) and a call is
read back by CODEC's `decodeCall`, exactly as deployed. The program is a parameter (`ctxWith`):
the generator's two-law stub here, LANG's program in `lang-journey` and PROTOCOL's rows.

The Host side here is incremental `admit` plus restart-by-fold: the stand-in for HOST's loop
(KERNEL K0); HOST's own loop runs in `host-sim`.
-/
import Kernel.Sim.Gen
import Codec.Kernel

namespace Nanodregg.Kernel.Sim

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec

abbrev D := UInt64

/-! ## Toy parameters -/

def fnv (b : ByteArray) : UInt64 :=
  b.foldl (fun h x => (h ^^^ x.toUInt64) * 1099511628211) 14695981039346656037

/-- The digest's codec: eight bytes, little-endian. -/
def dc : Stream D := Stream.u64

def digestOf (b : ByteArray) : Option D :=
  match dc.decode b with
  | .ok d => some d
  | .error _ => none

def env : Env D :=
  { hash := fun dom b => fnv (dom.toUTF8 ++ b)
    bytes := dc.bytes
    turnBytes := Codec.Kernel.turnBytes dc
    cellBytes := Codec.Kernel.cellBytes }

def toySign (key msg : ByteArray) : ByteArray := dc.bytes (fnv (key ++ msg))

/-- The toy `Ctx` with a given program. -/
def ctxWith (program : Program D) : Ctx D :=
  { env
    unsignedBytes := Codec.Kernel.unsignedBytes dc
    callBytes := Codec.Kernel.callBytes dc
    decodeCall := Codec.Kernel.decodeCall dc
    digestOf
    verify := fun key msg sig => toySign key msg == sig
    program }

def ctx : Ctx D := ctxWith (Gen.program digestOf 8)

/-- The toy parameters: a secret IS its public key, and its "signature" is a hash. -/
def toy : Gen.Params D :=
  { name := "toy parameters (UInt64 digest, FNV-1a, hash signatures; CODEC codecs and decodeCall)",
    ctx, pub := fun k => k, sign := toySign, zero := 0 }

/-! The generator under the toy parameters, by the names `lang-journey` uses. -/

abbrev Member := Gen.Member D
abbrev State := Gen.State D

def nameOf {α : Type} [Repr α] (a : α) : String := Gen.nameOf a
def worldName : ByteArray := Gen.worldName
def nonceOf (seed : Nat) : ByteArray := Gen.nonceOf seed
def same (a b : World D) : Bool := Gen.same env a b
def S.pinsFor (w : World D) (ids : List D) : List (D × D) := Gen.S.pinsFor env w ids
def signed (st : State) (m : Member) (key : ByteArray) (pins : List (D × D)) (body : Body D) :
    Call D := Gen.signed toy st m key pins body

end Nanodregg.Kernel.Sim
