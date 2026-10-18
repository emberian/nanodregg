import Emit.Rust
import Hosting.BrokerWire
import Hosting.BrokerExit

/-!
# Emit.Broker — the Rust copy of the provider-key broker's frames

`launcher/src/broker_generated.rs` is this function's output and nothing else (law 2): the resident's
ask, keybroker's decide request, the decider's verdict and keybroker's answer
(`Hosting.Broker.Wire.askCases`, `requestCases`, `verdictCases`, `answerCases`) as `wire::Ask`,
`wire::Request`, `wire::Verdict` and `wire::Answer`, with `FRAME_MAX` (`Broker.Bounds.frameMax`, the
frame and every field bound) and the refusal table as `wire::BrokerRefusal`, and keybroker's own
exit codes as `keybroker_exit`, its decider's as `decider_exit` (`Hosting.BrokerExit`, HOSTING-16) and
nd-members' as `members_exit` (HOSTING-30, CLIENT-29), with `RESIDENTS_MAX` (`Broker.Bounds.residentsMax`). It is a second file beside
`generated.rs` because one tagged file carries one bound, and Hosting.Wire's is 4096.
-/

namespace Nanodregg.Emit.Broker

open Nanodregg.Hosting.Broker

def file : Except String String :=
  Rust.taggedFile "Hosting/BrokerWire.lean" [("FRAME_MAX", Bounds.frameMax), ("RESIDENTS_MAX", Bounds.residentsMax)] Bounds.frameMax
    [("Ask", Wire.askCases), ("Request", Wire.requestCases), ("Verdict", Wire.verdictCases),
     ("Answer", Wire.answerCases)]
  |>.map (· ++ "\n" ++ Rust.byteModule "keybroker_exit" Hosting.KeybrokerExit.all (fun e => e.code.toUInt8) ++
    "\n\n" ++ Rust.byteModule "decider_exit" Hosting.DeciderExit.all (fun e => e.code.toUInt8) ++
    "\n\n" ++ Rust.byteModule "members_exit" Hosting.MembersExit.all (fun e => e.code.toUInt8) ++ "\n")

/-- `emit-broker PATH` writes the file; `emit-broker --check PATH` exits 1 if PATH differs. -/
def run (args : List String) : IO UInt32 := Rust.runWith "emit-broker" file args

end Nanodregg.Emit.Broker
