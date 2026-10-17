/-
# Protocol.Rows.Sim — the parameters the member rows run under

Toy PARAMETERS in the real pipeline (memory: never toy code beside it). The digest is a `UInt64`
spelled by CODEC's `Stream.u64` and hashed by the Sim's FNV-1a; a signature is the Sim's
`toySign`. Everything else is deployed code: CODEC's Call/Turn/Cell codecs (`Codec.Kernel`, generic
in the digest's codec), its batch record (`Codec.Kernel.batch`), LANG's program, KERNEL's
receivers. So a logged event the follower decodes is exactly the bytes follow built and the Host
admitted: `Codec.Proofs.Kernel.decodeCall_callBytes` holds of it, not a registry lookup.
-/
import Codec.World
import Kernel.Sim
import Lang.Program

namespace Nanodregg.Protocol.Rows.Sim

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec

abbrev D := UInt64

/-- The digest's codec. -/
def dc : Stream D := Stream.u64

def digestOf (b : ByteArray) : Option D :=
  match dc.decode b with
  | .ok d => some d
  | .error _ => none

def env : Env D :=
  { hash := fun dom b => Kernel.Sim.fnv (dom.toUTF8 ++ b)
    bytes := dc.bytes
    turnBytes := Codec.Kernel.turnBytes dc
    cellBytes := Codec.Kernel.cellBytes }

def sign (key msg : ByteArray) : ByteArray := Kernel.Sim.toySign key msg

def ctx : Ctx D :=
  { env
    unsignedBytes := Codec.Kernel.unsignedBytes dc
    callBytes := Codec.Kernel.callBytes dc
    decodeCall := Codec.Kernel.decodeCall dc
    digestOf
    verify := fun key msg sig => sign key msg == sig
    program := Lang.program dc.bytes digestOf }

/-- The World's codec (a base's World part, CODEC-14). -/
def world : Stream (World D) := Codec.Kernel.world dc

def worldName : ByteArray := "rows".toUTF8
def allowance : Nat := 2 ^ 40

end Nanodregg.Protocol.Rows.Sim
