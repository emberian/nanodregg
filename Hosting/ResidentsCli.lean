/-
# Hosting.ResidentsCli — `hosting-residents`: nd-members' decider (HOSTING-33)

    hosting-residents STORE

nd-members (HOSTING-30) asks which resident grains the World holds, and nothing else: it holds no
provider key, decides no ask and keeps no clock. So its decider takes only the World it follows,
STORE (read, never written: HOST's tail), and answers only `residents` frames: the resident grains'
socket names (`Controller.residentOf`: born, not removed; `Controller.dirOf`), at most
`Broker.Bounds.residentsMax`, else it ends `residentsPastBound`. Before each answer it catches the
tail up (at most `drainMax` reads, else `behind`) and re-reads the ids the new Turns touched.

It is `hosting-broker`'s follow with nothing else: the same `BrokerCli.Follow`, `catchUp`,
`Follow.absorbTurns` (so `Proofs.Residents.absorbTurns_tracks`, `residents_mem` and
`answer_encodes` speak of it too), `readFrame`, `emit` and `Exit` table (`DeciderExit`), with no
operator (so no allowance is ever held: `Allow.allowanceOf` matches only the operator's) and no
`Broker`. A `decide` or a `reply` frame is not its parent's to send: it ends `badRequest`.
Replacing `hosting-broker 0 1 STORE OPERATOR` in nd-members' unit removes two literals that stood
in for a clock and a key-slot list a residents answer never reads.
-/
import Hosting.BrokerCli

namespace Nanodregg.Hosting.ResidentsCli

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Hosting.Broker Nanodregg.Hosting.BrokerCli
open Nanodregg.Host (Tail File readKey Keys StoreFault)

/-- Answer `residents` frames until the parent closes the pipe, at most `fuel` of them. -/
def serve (input out : IO.FS.Stream) : Nat → Follow → IO Exit
  | 0, _ => pure .lifetime
  | fuel + 1, f => do
    let some hdr ← readFrame input | return .keybrokerGone
    let .ok hdr := hdr | return .badFrame
    let .ok req := Wire.decodeRequest hdr | return .badRequest
    match req with
    | .residents _ =>
      match ← catchUp f.keys f.seg drainMax f.tail [] [] with
      | .error e => return e
      | .ok (t, turns, _) =>
        let f := if turns.isEmpty then { f with tail := t } else f.absorbTurns t turns
        let names := f.residents
        if Broker.Bounds.residentsMax < names.length then return .residentsPastBound names.length
        unless ← emit out (Broker.Verdict.residents names) do return .unencodable
        serve input out fuel f
    | .decide .. | .reply .. | .certify .. => return .badRequest

def run (store : System.FilePath) : IO Exit := do
  let some pid := Allow.allowanceId Host.Deployed.X.env | return .noPackage
  let some lid := Controller.lifecycleId Host.Deployed.X.env | return .noPackage
  match ← (readKey store : IO (Except (StoreFault (Host.Record.Fault (Kernel.Reject D))) Digest)) with
  | .error f => return .store f.text
  | .ok key =>
    let sk := Keys.ofKey key Host.Deployed.shapes
    match ← Tail.open store sk Host.Deployed.c Host.Deployed.world Host.Deployed.recorder.mark
        Host.Deployed.originChain Host.Deployed.tailStep with
    | .error f => return .store f.text
    | .ok (t, seg) =>
      let grains := Track.update Host.Deployed.X.env (Controller.residentOf lid.bytes) t.world []
        (Loop.allIds t.world)
      serve (← IO.getStdin) (← IO.getStdout) lifetime
        ⟨sk, seg, pid.bytes, ByteArray.empty, lid.bytes, t, [], grains⟩

def main (args : List String) : IO UInt32 := do
  let e ← match args with
    | [store] => try run store catch err => pure (.io (toString err))
    | _ => pure .usage
  IO.eprintln s!"hosting-residents: {e.name}"
  return e.code

end Nanodregg.Hosting.ResidentsCli
