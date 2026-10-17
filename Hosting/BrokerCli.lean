/-
# Hosting.BrokerCli — `hosting-broker`: keybroker's decider (HOSTING-12)

    hosting-broker T0 SLOTS --drive RESIDENT=MODEL/SLOT/PRICE/WINDOWMS/CAP/MAXTOKENS …

keybroker starts it with `T0` first, the operator clock (ms) at the start of this broker life, which
`Broker.start` forfeits, then SLOTS, the comma-separated key slots its key file holds (so an
allowance whose slot has no key is refused `keyMissing` before any charge). Then, per ask, it reads a `decide` frame (resident, atMs) and the
resident's ask frame from stdin, runs `Broker.step`, and writes one verdict frame to stdout.
Every frame is `u32le len ‖ payload`, `1 ≤ len ≤ Broker.Bounds.frameMax`. Every way it ends is an
`Exit` by name on stderr; asks are bounded by `lifetime`.

`--drive` takes each allowance (one resident, one model) from the command line (stage 1 of HOSTING-12: the launcher
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

/-- `RESIDENT=MODEL/SLOT/PRICE/WINDOWMS/CAP/MAXTOKENS`. -/
def parseAllowance (s : String) : Option (ByteArray × Allowance) :=
  match s.splitOn "=" with
  | [r, spec] =>
    match spec.splitOn "/" with
    | [m, k, p, w, c, t] => do
      pure (r.toUTF8, ⟨m.toUTF8, ← k.toNat?, ← p.toNat?, ← w.toNat?, ← c.toNat?, ← t.toNat?⟩)
    | _ => none
  | _ => none

/-- `S1,S2,…`: the key slots keybroker holds. -/
def parseSlots (s : String) : Option (List Nat) := (s.splitOn ",").mapM String.toNat?

def run : List String → IO Exit
  | t0 :: slots :: "--drive" :: specs => do
    let some t0 := t0.toNat? | return .usage
    let some keys := parseSlots slots | return .usage
    let some rs := specs.mapM parseAllowance | return .usage
    serve (← IO.getStdin) (← IO.getStdout) lifetime (Broker.start t0 keys rs)
  | _ => pure .usage

def main (args : List String) : IO UInt32 := do
  let e ← run args
  IO.eprintln s!"hosting-broker: {e.name}"
  return e.code

end Nanodregg.Hosting.BrokerCli
