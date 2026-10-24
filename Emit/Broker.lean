import Emit.Rust
import Hosting.BrokerWire
import Hosting.BrokerExit
import Hosting.Plan
import Hosting.Broker

/-!
# Emit.Broker — the Rust copy of the provider-key broker's frames

`launcher/src/broker_generated.rs` is this function's output and nothing else (law 2): the resident's
ask, keybroker's decide request, the decider's verdict and keybroker's answer
(`Hosting.Broker.Wire.askCases`, `requestCases`, `verdictCases`, `answerCases`) as `wire::Ask`,
`wire::Request`, `wire::Verdict` and `wire::Answer`, with `FRAME_MAX` (`Broker.Bounds.frameMax`, the
frame and every field bound) and the refusal table as `wire::BrokerRefusal`, and keybroker's own
exit codes as `keybroker_exit`, its decider's as `decider_exit` (`Hosting.BrokerExit`, HOSTING-16) and
nd-members' as `members_exit` (HOSTING-30, CLIENT-29), with `RESIDENTS_MAX` (`Broker.Bounds.residentsMax`),
`GRAIN_NAME_MAX` (`Codec.Path.componentMax`, a grain directory name's bound) and `SOCK_PATH_MAX`
(`Hosting.sockPathMax`, sun_path's: nd-members refuses a socket root its residents' sockets would pass),
`ANSWER_MS_MAX` (`Broker.Bounds.answerMsMax`, one decider answer's deadline),
`DECIDER_TICK_MS` (`Broker.Bounds.tickMs`) and the restart policy nd-members applies per resident, the
units' own (`Hosting.restartSeconds`, `startBurst`, `startIntervalSeconds`; CLIENT-40). It is a second file beside
`generated.rs` because one tagged file carries one bound, and Hosting.Wire's is 4096.
-/

namespace Nanodregg.Emit.Broker

open Nanodregg.Hosting.Broker

def file : Except String String :=
  Rust.taggedFile "Hosting/BrokerWire.lean" [("FRAME_MAX", Bounds.frameMax), ("RESIDENTS_MAX", Bounds.residentsMax),
     ("GRAIN_NAME_MAX", Codec.Path.componentMax), ("SOCK_PATH_MAX", Hosting.sockPathMax), ("ANSWER_MS_MAX", Bounds.answerMsMax),
     ("DECIDER_TICK_MS", Bounds.tickMs), ("RESTART_SECONDS", Hosting.restartSeconds),
     ("START_BURST", Hosting.startBurst), ("START_INTERVAL_SECONDS", Hosting.startIntervalSeconds)] Bounds.frameMax
    [("Ask", Wire.askCases), ("Request", Wire.requestCases), ("Verdict", Wire.verdictCases),
     ("Answer", Wire.answerCases)]
  |>.map (· ++ "\n" ++ Rust.byteModule "keybroker_exit" Hosting.KeybrokerExit.all (fun e => e.code.toUInt8) ++
    "\n\n" ++ Rust.byteModule "decider_exit" Hosting.DeciderExit.all (fun e => e.code.toUInt8) ++
    "\n\n" ++ Rust.byteModule "members_exit" Hosting.MembersExit.all (fun e => e.code.toUInt8) ++ "\n")

/-- `emit-broker PATH` writes the file; `emit-broker --check PATH` exits 1 if PATH differs. -/
def run (args : List String) : IO UInt32 := Rust.runWith "emit-broker" file args

end Nanodregg.Emit.Broker
