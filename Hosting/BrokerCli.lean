/-
# Hosting.BrokerCli — `hosting-broker`: keybroker's decider (HOSTING-12, HOSTING-13)

    hosting-broker T0 SLOTS STORE OPERATOR

keybroker starts it with `T0`, the operator clock (ms) at the start of this broker life, which
`Broker.start` forfeits, and SLOTS, the comma-separated key slots its key file holds (so an
allowance whose slot has no key is refused `keyMissing` before any charge). STORE is the World it
follows, read and never written: HOST's tail (`Host.Tail`), the open and then O(appended bytes)
per ask. OPERATOR is the operator's member id in lowercase hex; only allowance objects it owns are
read (`Allow.allowanceOf`).

At the open, every live cell id is read (`Loop.allIds`, once). Then, per ask, it reads a `decide`
frame (resident, atMs) and the resident's ask frame from stdin; catches the tail up (at most
`drainMax` reads, past which it ends `behind` rather than decide on a stale World); re-reads the
ids the new Turns touched (`Allow.update`, exact by `Proofs.Allowance.update_tracks`); follows
them (`Broker.follow` at the ask's time); runs `Broker.step`; and writes one verdict frame to
stdout. Every frame is `u32le len ‖ payload`, `1 ≤ len ≤ Broker.Bounds.frameMax`. Every way it ends
is an `Exit` by name on stderr; asks are bounded by `lifetime`.
-/
import Hosting.Broker
import Hosting.BrokerExit
import Hosting.Allowance
import Hosting.Loop
import Host.Deployed
import Host.Tail
import Host.Wire
import Lang.Read

namespace Nanodregg.Hosting.BrokerCli

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Hosting.Broker
open Nanodregg.Host (Tail File readKey Keys StoreFault)

/-- Asks one process answers at most. -/
def lifetime : Nat := 1 <<< 48

/-- Tail reads one catch-up may take, each at most one frame bound: a writer this far ahead of a
broker means the broker is not following it. -/
def drainMax : Nat := 1 <<< 16

inductive Exit
  /-- keybroker closed the pipe: the normal end -/
  | keybrokerGone
  | usage
  /-- a frame length of 0 or past `frameMax` -/
  | badFrame
  /-- a `decide` header that does not decode -/
  | badRequest
  /-- a verdict with no frame: unreachable (`Proofs.Broker.step_encodes`), kept as the assertion -/
  | unencodable
  | lifetime
  /-- the allowance package has no id (`Allow.allowanceId`): no allowance could be read -/
  | noPackage
  /-- the Store refused to open or to be followed (its own name, `StoreFault.name`) -/
  | store (name : String)
  /-- `drainMax` reads did not catch the tail up -/
  | behind
  | io (msg : String)

def Exit.name : Exit → String
  | .keybrokerGone => "keybrokerGone" | .usage => "usage" | .badFrame => "badFrame"
  | .badRequest => "badRequest" | .unencodable => "unencodable" | .lifetime => "lifetime"
  | .noPackage => "noPackage" | .store n => s!"store {n}" | .behind => "behind" | .io m => s!"io {m}"

/-- The kind of an end, in the exit table (`Hosting.BrokerExit`). -/
def Exit.kind : Exit → DeciderExit
  | .keybrokerGone => .keybrokerGone | .usage => .usage | .badFrame => .badFrame
  | .badRequest => .badRequest | .unencodable => .unencodable | .lifetime => .lifetime
  | .noPackage => .noPackage | .store _ => .store | .behind => .behind | .io _ => .io

def Exit.code (e : Exit) : UInt32 := e.kind.code.toUInt32

/-- One frame: `none` at end of input, `.error` for a length outside `1 ≤ len ≤ frameMax`. -/
def readFrame (input : IO.FS.Stream) : IO (Option (Except Exit ByteArray)) := do
  let some head ← Host.readExact input 4 | return none
  let some len := Host.Log.lenAt head 0 | return none
  if len = 0 ∨ Broker.Bounds.frameMax < len then return some (.error .badFrame)
  let some body ← Host.readExact input len | return none
  return some (.ok body)

abbrev D := Host.Deployed.D

/-- What the broker follows: the tail, its read handle, and the allowances it holds by World id. -/
structure Follow where
  keys : Keys
  seg : File
  pkgId : ByteArray
  operator : ByteArray
  tail : Tail (World D)
  held : List (D × (ByteArray × Allowance))

/-- Read what was appended until nothing is new, at most `n` reads; the Turns absorbed. -/
def catchUp (keys : Keys) (seg : File) : Nat → Tail (World D) → List (Turn D) →
    IO (Except Exit (Tail (World D) × List (Turn D)))
  | 0, _, _ => pure (.error .behind)
  | n + 1, t, acc => do
    match ← Tail.next keys Host.Deployed.c Host.Deployed.tailStep seg t with
    | .error f => pure (.error (.store f.name))
    | .ok (t', outs) =>
      if outs.isEmpty && t'.pos.offset == t.pos.offset then pure (.ok (t', acc))
      else catchUp keys seg n t' (acc ++ outs.toList.flatten.map Prod.fst)

/-- Before an ask at `now`: catch up, re-read the touched ids, follow them. -/
def refresh (f : Follow) (b : Broker) (now : Nat) : IO (Except Exit (Follow × Broker)) := do
  match ← catchUp f.keys f.seg drainMax f.tail [] with
  | .error e => pure (.error e)
  | .ok (t, turns) =>
    if turns.isEmpty then return .ok ({ f with tail := t }, b)
    let held := Allow.absorb Host.Deployed.X.env f.pkgId f.operator t.world f.held turns
    pure (.ok ({ f with tail := t, held }, b.follow now (held.map (·.2))))

def serve (input out : IO.FS.Stream) : Nat → Follow → Broker → IO Exit
  | 0, _, _ => pure .lifetime
  | fuel + 1, f, b => do
    let some hdr ← readFrame input | return .keybrokerGone
    let .ok hdr := hdr | return .badFrame
    let some ask ← readFrame input | return .keybrokerGone
    let .ok ask := ask | return .badFrame
    let .ok (r, now) := Wire.decodeRequest hdr | return .badRequest
    let (f, b) ← match ← refresh f b now with
      | .ok fb => pure fb
      | .error e => return e
    let (b', v) := Broker.step b r now ask
    let some bytes := Wire.encodeVerdict v | return .unencodable
    out.write (Host.Log.lenBytes bytes.size ++ bytes)
    out.flush
    serve input out fuel f b'

/-- `S1,S2,…`: the key slots keybroker holds. -/
def parseSlots (s : String) : Option (List Nat) := (s.splitOn ",").mapM String.toNat?

def run (t0 : Nat) (keys : List Nat) (store : System.FilePath) (operator : ByteArray) : IO Exit := do
  let some pid := Allow.allowanceId Host.Deployed.X.env | return .noPackage
  match ← (readKey store : IO (Except (StoreFault (Host.Record.Fault (Kernel.Reject D))) Digest)) with
  | .error f => return .store f.text
  | .ok key =>
    let sk := Keys.ofKey key Host.Deployed.shapes
    match ← Tail.open store sk Host.Deployed.c Host.Deployed.world Host.Deployed.recorder.mark
        Host.Deployed.originChain Host.Deployed.tailStep with
    | .error f => return .store f.text
    | .ok (t, seg) =>
      let pkgId := pid.bytes
      let held := Allow.update Host.Deployed.X.env pkgId operator t.world [] (Loop.allIds t.world)
      serve (← IO.getStdin) (← IO.getStdout) lifetime ⟨sk, seg, pkgId, operator, t, held⟩
        (Broker.start t0 keys (held.map (·.2)))

def main (args : List String) : IO UInt32 := do
  let e ← match args with
    | [t0, slots, store, operator] =>
      match t0.toNat?, parseSlots slots, Lang.Read.unhex .empty operator.toList with
      | some t0, some keys, some op => try run t0 keys store op catch err => pure (.io (toString err))
      | _, _, _ => pure .usage
    | _ => pure .usage
  IO.eprintln s!"hosting-broker: {e.name}"
  return e.code

end Nanodregg.Hosting.BrokerCli
