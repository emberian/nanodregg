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

/-- The digest's codec (the Kernel Sim's: CODEC's `Stream.u64`). -/
def dc : Stream D := Kernel.Sim.dc

def digestOf (b : ByteArray) : Option D := Kernel.Sim.digestOf b

def env : Env D := Kernel.Sim.env

def sign (key msg : ByteArray) : ByteArray := Kernel.Sim.toySign key msg

/-- The Kernel Sim's toy `Ctx` with LANG's program. -/
def ctx : Ctx D := Kernel.Sim.ctxWith (Lang.program dc.bytes digestOf)

/-- The World's codec (a base's World part, CODEC-14). -/
def world : Stream (World D) := Codec.Kernel.world dc

def worldName : ByteArray := "rows".toUTF8
def allowance : Nat := 2 ^ 40
/-- The rows' genesis nonce (KERNEL-24): fixed, a test parameter; a real genesis draws it. -/
def nonce : ByteArray := "rows-nonce".toUTF8

end Nanodregg.Protocol.Rows.Sim
