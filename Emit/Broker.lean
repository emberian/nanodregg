import Emit.Rust
import Hosting.BrokerWire

/-!
# Emit.Broker — the Rust copy of the provider-key broker's frames

`launcher/src/broker_generated.rs` is this function's output and nothing else (law 2): the resident's
ask, keybroker's decide request, the decider's verdict and keybroker's answer
(`Hosting.Broker.Wire.askCases`, `requestCases`, `verdictCases`, `answerCases`) as `wire::Ask`,
`wire::Request`, `wire::Verdict` and `wire::Answer`, with `FRAME_MAX` (`Broker.Bounds.frameMax`, the
frame and every field bound) and the refusal table as `wire::BrokerRefusal`. It is a second file beside
`generated.rs` because one tagged file carries one bound, and Hosting.Wire's is 4096.
-/

namespace Nanodregg.Emit.Broker

open Nanodregg.Hosting.Broker

def file : Except String String :=
  Rust.taggedFile "Hosting/BrokerWire.lean" [("FRAME_MAX", Bounds.frameMax)] Bounds.frameMax
    [("Ask", Wire.askCases), ("Request", Wire.requestCases), ("Verdict", Wire.verdictCases),
     ("Answer", Wire.answerCases)]

/-- `emit-broker PATH` writes the file; `emit-broker --check PATH` exits 1 if PATH differs. -/
def run (args : List String) : IO UInt32 := Rust.runWith "emit-broker" file args

end Nanodregg.Emit.Broker
