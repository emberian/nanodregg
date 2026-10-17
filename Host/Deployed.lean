/-
# Host.Deployed — the one deployed instance of the Host's parameters

The kernel, the loop, the Store and the page builder are generic. This module fixes them for
`host`: CODEC's deployed `Ctx` (`Codec.Digest`, cSHAKE256, the kernel codecs, Ed25519) with LANG's
`Program`, CODEC's batch record over the 32-byte digest, the deployed `Cadence`, and the KMAC
sealers under the Store key. The writer reopens its own records with `World.fold`; a follower
re-derives every Turn with `Receive.audit` (PROTOCOL-4).
-/
import Host.Store
import Host.Keys
import Host.Page
import Host.Serve
import Codec.Deployed
import Lang.Program
import Kernel.Receive.Audit

namespace Nanodregg.Host.Deployed

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec

abbrev D := Digest

def X : Ctx D := Codec.Deployed.ctx (Lang.program Digest.bytes Digest.ofBytes?)

def c : Cadence := Cadence.deployed

def world : Stream (World D) := Codec.Deployed.world

def recorder : Recorder (World D) (Turn D) where
  encode := Record.encode Codec.Deployed.digestCodec
  mark w := (w.height, w.chain.bytes)

/-- The writer's reopen: its own records, folded. -/
def foldStep : World D → ByteArray → Except (Record.Fault (Reject D)) (World D) :=
  Record.step Codec.Deployed.digestCodec (World.fold X.env)

/-- A follower's reopen and absorb: every Turn re-derived from its event. -/
def auditStep : World D → ByteArray → Except (Record.Fault (Verdict D)) (World D) :=
  Record.step Codec.Deployed.digestCodec (audit X)

/-- The loop's batch bounds: a record's Turns, and a megabyte of request payload. -/
def limits : Limits := ⟨Record.turnsMax, 1 <<< 20⟩

/-- A `log` page from the segment file. -/
def pager (keys : Keys) (seg : File) (r : Resident (World D)) (start : Nat) : IO (UInt8 × ByteArray) := do
  match ← Page.build X.env Codec.Deployed.digestCodec X.digestOf keys.segment c.recordBytesMax
      Page.budget (fun off len => seg.readAt off.toUInt64 len.toUSize) r.index (recorder.mark r.world)
      start with
  | .error f => return named f.name
  | .ok a => match Page.bytes a with
    | .ok b => return (Protocol.Status.ok.code, b)
    | .error f => return named f.name

end Nanodregg.Host.Deployed
