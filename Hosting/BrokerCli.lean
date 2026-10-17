/-
# Hosting.BrokerCli — `hosting-broker`: keybroker's decider (HOSTING-12)

    hosting-broker T0 --drive RESIDENT=WINDOWMS:CAP:MAXTOKENS:MODEL/SLOT/PRICE[+MODEL/SLOT/PRICE…] …

keybroker starts it with `T0` first, the operator clock (ms) at the start of this broker life, which
`Broker.start` forfeits. Then, per ask, it reads a `decide` frame (resident, atMs) and the
resident's ask frame from stdin, runs `Broker.step`, and writes one verdict frame to stdout.
Every frame is `u32le len ‖ payload`, `1 ≤ len ≤ Broker.Bounds.frameMax`. Every way it ends is an
`Exit` by name on stderr; asks are bounded by `lifetime`.

`--drive` takes each resident's allowance from the command line (stage 1 of HOSTING-12: the launcher
test is the only caller). Stage 2 replaces it with the allowance objects of a Store.
-/
import Hosting.Broker
import Host.Wire

namespace Nanodregg.Hosting.BrokerCli

open Nanodregg.Hosting.Broker

/-- Asks one process answers at most. -/
def lifetime : Nat := 1 <<< 48

inductive Exit
  /-- keybroker closed the pipe: the normal end -/
  | keybrokerGone
  | usage
  /-- a frame length of 0 or past `frameMax` -/
  | badFrame
  /-- a `decide` header that does not decode -/
  | badRequest
  /-- a verdict past `frameMax` (an assertion: `decide` bounds every field it prints) -/
  | unencodable
  | lifetime

def Exit.name : Exit → String
  | .keybrokerGone => "keybrokerGone" | .usage => "usage" | .badFrame => "badFrame"
  | .badRequest => "badRequest" | .unencodable => "unencodable" | .lifetime => "lifetime"

def Exit.code : Exit → UInt32
  | .keybrokerGone => 0
  | .usage => 2
  | _ => 1

/-- One frame: `none` at end of input, `.error` for a length outside `1 ≤ len ≤ frameMax`. -/
def readFrame (input : IO.FS.Stream) : IO (Option (Except Exit ByteArray)) := do
  let some head ← Host.readExact input 4 | return none
  let some len := Host.Log.lenAt head 0 | return none
  if len = 0 ∨ Broker.Bounds.frameMax < len then return some (.error .badFrame)
  let some body ← Host.readExact input len | return none
  return some (.ok body)

def serve (input out : IO.FS.Stream) : Nat → Broker → IO Exit
  | 0, _ => pure .lifetime
  | fuel + 1, b => do
    let some hdr ← readFrame input | return .keybrokerGone
    let .ok hdr := hdr | return .badFrame
    let some ask ← readFrame input | return .keybrokerGone
    let .ok ask := ask | return .badFrame
    let .ok (r, now) := Wire.decodeRequest hdr | return .badRequest
    let (b', v) := Broker.step b r now ask
    let some bytes := Wire.encodeVerdict v | return .unencodable
    out.write (Host.Log.lenBytes bytes.size ++ bytes)
    out.flush
    serve input out fuel b'

/-- `MODEL/SLOT/PRICE`. -/
def parseModel (s : String) : Option Model :=
  match s.splitOn "/" with
  | [m, k, p] => do
    let k ← k.toNat?
    if 2 ^ 32 ≤ k then none
    pure ⟨m.toUTF8, k.toUInt32, ← p.toNat?⟩
  | _ => none

/-- `RESIDENT=WINDOWMS:CAP:MAXTOKENS:MODELS`. -/
def parseResident (s : String) : Option (ByteArray × Allowance) :=
  match s.splitOn "=" with
  | [r, spec] =>
    match spec.splitOn ":" with
    | [w, c, t, ms] => do
      let models ← (ms.splitOn "+").mapM parseModel
      pure (r.toUTF8, ⟨← w.toNat?, ← c.toNat?, ← t.toNat?, models⟩)
    | _ => none
  | _ => none

def run : List String → IO Exit
  | t0 :: "--drive" :: specs => do
    let some t0 := t0.toNat? | return .usage
    let some rs := specs.mapM parseResident | return .usage
    serve (← IO.getStdin) (← IO.getStdout) lifetime (Broker.start t0 rs)
  | _ => pure .usage

def main (args : List String) : IO UInt32 := do
  let e ← run args
  IO.eprintln s!"hosting-broker: {e.name}"
  return e.code

end Nanodregg.Hosting.BrokerCli
