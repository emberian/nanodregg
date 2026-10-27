/-
# Spec.Sim.Member — the trivial systems A1 and C(ii) refuse besides `Spec.Trivial`'s

The reset follower (A1: it replaces its World by one fixed genesis on every frame), the forgetful
follower (C(ii): it answers as the deployed one and keeps the genesis World), and the settled-word
pair (C(ii), cancel: the Host's-word follower with a settlement that always says `cancelled`).
Tooling (closure C9): the floors are in `Spec.Proofs.Floor`.
-/
import Spec.Sim.Run

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-- **The reset follower**: every frame replaces follow's World by the run's genesis World and ends
the command refused. -/
def resetFollower (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with
    follow := fun _ f _ _ =>
      ({ f with world := wGenesis }, .steps [], .done CommandExit.refused.code.toUInt8 .empty .empty) }

/-- A step's answer with follow's World replaced by the genesis World. -/
def forget (r : Command.Follow Digest × Command.Persist Digest × Command.Reply) :
    Command.Follow Digest × Command.Persist Digest × Command.Reply :=
  ({ r.1 with world := wGenesis }, r.2.1, r.2.2)

/-- **The forgetful follower**: it answers every frame as the deployed follower does, and keeps the
genesis World (a success that erases the journal). -/
def forgetful (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with follow := fun me f kb res => forget ((deployed d).follow me f kb res) }

/-- **The settled word**: the Host's-word follower, with a settlement that always says `cancelled`. -/
def settledWord (d : ByteArray → ByteArray) : System Digest :=
  { hostWord d with settle := fun _ _ _ => .refused (Command.cancelledCode (D := Digest)) }

end Nanodregg.Spec
