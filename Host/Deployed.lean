/-
# Host.Deployed — the one deployed instance of the Host's parameters

The kernel, the loop, the Store and the page builder are generic. This module fixes them for
`host`: CODEC's deployed `Ctx` (`Codec.Digest`, cSHAKE256, the kernel codecs, Ed25519) with LANG's
`Program`, CODEC's batch record over the 32-byte digest, the deployed `Cadence`, and the KMAC
sealers under the Store key. Writer and follower both reopen their own records with `World.fold`
(`foldStep`, HOST-22): a follower audits at follow time (`Protocol.Command.step`), never at reopen.
-/
import Host.Store
import Host.Keys
import Host.Page
import Host.Serve
import Codec.Deployed
import Lang.Program

namespace Nanodregg.Host.Deployed

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec

abbrev D := Digest

def X : Ctx D := Codec.Deployed.ctx (Lang.program Digest.bytes Digest.ofBytes?)

def c : Cadence := Cadence.deployed

def world : Stream (World D) := Codec.Deployed.world

/-- The deployed shape stamp (D2): the tags of the deployed base and batch record codecs. -/
def shapes : Digest := Base.shapeStamp world (Record.codec Codec.Deployed.digestCodec)

def recorder : Recorder (World D) (Turn D) where
  encode := Record.encode Codec.Deployed.digestCodec
  mark w := (w.height, w.chain.bytes)

/-- The genesis chain of a World's origin (KERNEL's `World.genesisChain`), as `mark` writes a
chain: what the origin frame of its Store holds, checked at every open (HOST-25). -/
def originChain (w : World D) : ByteArray := (World.genesisChain X.env w.origin).bytes

/-- The writer's reopen: its own records, folded. -/
def foldStep : World D → ByteArray → Except (Record.Fault (Reject D)) (World D) :=
  Record.step Codec.Deployed.digestCodec (World.fold X.env)

/-- A tail's step (`Host.Tail`, HOSTING-7): the writer's fold, with each record's Turns. -/
def tailStep : World D → ByteArray → Except (Record.Fault (Reject D)) (World D × List (Turn D)) :=
  Record.stepTurns Codec.Deployed.digestCodec (World.fold X.env)


/-- The loop's batch bounds: a record's Turns, and a megabyte of request payload. -/
def limits : Limits := ⟨recordTurnsMax, 1 <<< 20⟩

/-- A deferred reply from the Store's files: a `log` page from the segment, a `read` page from the
newest base (opened per page: the base is replaced, never written in place). -/
def pager (keys : Keys) (dir : System.FilePath) (seg : File) (r : Resident (World D)) :
    Deferred → IO (UInt8 × ByteArray)
  | .read start => do
    let base ← File.open (basePath dir) .read
    match ← Page.basePage Page.budget (fun off len => base.readAt off.toUInt64 len.toUSize) r.sealed start with
    | .error f => return named f.name
    | .ok b => return (Protocol.Status.ok.code, b)
  | .log start => do
  match ← Page.build X.env Codec.Deployed.digestCodec X.digestOf keys.segment c.recordBytesMax
      Page.budget (fun off len => seg.readAt off.toUInt64 len.toUSize) r.index (recorder.mark r.world)
      start with
  | .error f => return named f.name
  | .ok a => match Page.bytes a r.world.height with
    | .ok b => return (Protocol.Status.ok.code, b)
    | .error f => return named f.name

end Nanodregg.Host.Deployed
