/-
# Spec.Sim.Sign — the relay signer and the signing run (C(i), `Spec.Proofs.Sign`)

The trivial system `relaySigner`: a follower that checks the continuation is a command (it decodes
to a state whose argv parses) and then has custody sign the Host's reply bytes, planning nothing.
The run: follow, at the genesis World, steps the founder's `rotate` at its precommit phase with
custody's next and pending keys. Tooling (closure C9): what is computed of these is stated in
`Spec.Proofs.Sign`.
-/
import Spec.Sim.Run

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-- **The relay signer**: on a continuation that decodes to a state whose argv parses, it hands
custody the Host's reply bytes to sign; on any other it refuses. -/
def relaySigner (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with
    follow := fun _ f kb res =>
      match Command.State.ofBytes kb with
      | some st =>
          match Command.parse Host.Deployed.X.digestOf st.argv with
          | .ok _ => (f, .steps [], .sign res .empty)
          | .error _ => (f, .steps [], .done CommandExit.refused.code.toUInt8 .empty .empty)
      | none => (f, .steps [], .done CommandExit.refused.code.toUInt8 .empty .empty) }

/-- A `sync` command at its envelope phase: a continuation that decodes, whose argv parses. -/
def kSync : ByteArray := (Command.State.bytes ⟨["sync".toUTF8], 1, []⟩).getD .empty

/-- Custody's pending key in the run (the founder's key after next). -/
def iPending : ByteArray := Ed25519.publicKey (wSeed "f0-next-next")

/-- Custody's answer to `precommit`: its next key (the founder's precommitted `wNext`) and pending key. -/
def iRes : ByteArray :=
  match Text.fit Bounds.frameBytesMax wNext, Text.fit Bounds.frameBytesMax iPending with
  | some n, some p => ⟨#[Status.ok.code]⟩ ++ precommitResultFrame.bytes (n, p, ())
  | _, _ => .empty

/-- A `rotate` command at its precommit phase. -/
def iKb : ByteArray := (Command.State.bytes ⟨["rotate".toUTF8], 5, []⟩).getD .empty

/-- The reply asks `signNext` over the call message of `u`. -/
def callAsked (r : Command.Reply) (u : Unsigned Digest) : Bool :=
  match r with
  | .signNext m _ => decide (m = Xd.callMessage u)
  | _ => false

end Nanodregg.Spec
