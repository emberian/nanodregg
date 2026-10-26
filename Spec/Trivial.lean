/-
# Spec.Trivial — the trivial systems the claims refuse

Each is `deployed d` with ONE field replaced by what a lazy implementation would do. They are the
other half of each claim's meaning: `Spec.Proofs.Floor` proves the claim false of each, so a claim
that held of every system would hold of these. (A def-module: the floors live in `Floor`.)
-/
import Spec.System

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-- The World a trusting follower is told: one admitted Turn more than it has steps, of another
World. -/
def told (w : World Digest) : World Digest :=
  { w with height := w.steps + 1, origin := Digest.zero }

/-- **The trusting follower**: it takes the World the Host's reply tells it, re-deriving nothing. -/
def trustingFollower (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with
    follow := fun _ f _ _ => ({ f with world := told f.world }, .steps [], .done 0 .empty .empty) }

/-- **The Host's-word follower**: every step ends its command `done ok` (the pre-PROTOCOL-64
machine's reading of a `committed` reply, without a settlement on follow's own World). -/
def hostWord (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with
    follow := fun _ f _ _ => (f, .steps [], .done CommandExit.ok.code.toUInt8 .empty .empty) }

/-- **The always-final settlement**: every call is `expired`. -/
def alwaysFinal (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with settle := fun _ _ _ => .expired }

/-- **The open host**: it answers every frame with a page of the log. -/
def openHost (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with handle := fun _ _ => .defer (.log 0) }

/-- **The chainless kernel**: it admits as the kernel does but never extends the log chain, so the
chain binds nothing that was folded. -/
def chainless (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with
    admit := fun w t => (World.admit Host.Deployed.X.env w t).map fun w' => { w' with chain := w.chain } }

end Nanodregg.Spec
