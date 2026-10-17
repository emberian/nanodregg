/-
# Host.Cli — the `host` executable's verbs (Host/Main.lean holds only `main`)

    host genesis STORE NAME [KEY_HEX NEXT_HEX]...   create a Store: founders (Ed25519 key, the
                                                   precommitted NEXT public key; the Store
                                                   holds its digest, `Receive.nextKeyDigest`, which
                                                   only Lean computes: law 2)
    host serve STORE                               the writer loop on stdin/stdout
    host follow STORE MEMBER_HEX GRANT_HEX         the follower loop on stdin/stdout (Host.Follow)
    host check STORE [--anchor HEIGHT:CHAIN_HEX]   open read-only, print one STATUS line, refuse a
                                                   Store behind or off the anchor (Host.Check)

STORE is the only path any verb touches. Frames are `Host.Wire`'s (the supervisor's mux is the
other end). The exit code is `Host.Status.code` of how the process ended (`Host.Exit`): one code
per status, each of class done, restart or fatal, with its name on stderr.
There is no fuel exit: a spent round reopens in process (`Host.restarts`, D4).

`serve` and `follow` are never silent (D8): one `STATUS` line on stderr once the Store is open and
the reader thread is proved live, one at exit; a reader that cannot get its own thread (the
runtime runs a `.dedicated` task inline when it cannot read the CPU count: the macOS sandbox
without `hw.ncpu`) is refused `noThreads` by name rather than answering nothing.
-/
import Host.Deployed
import Host.Follow
import Host.Exit
import Host.Check
import Kernel.Receive.Follow

namespace Nanodregg.Host.Cli

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Host.Deployed

/-- Batches per round: each round ends in an in-process reopen checked against the loop's state,
so the open path runs routinely (D4). -/
def fuelBatches : Nat := 1 <<< 12

/-- Frames the reader reads in one process (`Stop.lifetime`): 2^48, centuries at any rate the
loop can sustain. -/
def lifetimeFrames : Nat := 1 <<< 48

/-- Rounds in one process. A round that ends `fuel` consumed `fuelBatches` batches of at least one
frame each, so the reader's lifetime ends first and `Exit.lifetime` is unreachable before it. -/
def restartsMax : Nat := lifetimeFrames / fuelBatches + 1

/-- Frames the reader task may queue ahead of the loop. -/
def queueMax : Nat := 1024

def exitCode (e : Exit) : UInt32 := e.status.code.toUInt32

/-- Refuse with `status`'s code; `name` is the refusal's own name (finer than the status for an
argument: which argument). -/
def refuse (status : Status) (name : String := status.name) : IO UInt32 := do
  IO.eprintln s!"refused {name}"
  return status.code.toUInt32

def refuseStore {F : Type} (f : StoreFault F) : IO UInt32 := refuse f.status f.name

def usage : String :=
  "usage: host genesis STORE NAME [KEY_HEX NEXT_HEX]... | host serve STORE | host follow STORE MEMBER_HEX GRANT_HEX | host check STORE [--anchor HEIGHT:CHAIN_HEX]"

def hexDigest (s : String) : Option Digest := Protocol.Text.ofHex s >>= Digest.ofBytes?

/-- `(key, digest of next key)` pairs from the argv tail of `(key, next key)` public keys. -/
def founders : List String → Option (List (ByteArray × Digest))
  | [] => some []
  | k :: n :: rest => do
    let key ← Protocol.Text.ofHex k
    let next ← Protocol.Text.ofHex n
    if key.size ≠ 32 ∨ next.size ≠ 32 then none
    return (key, Receive.nextKeyDigest X next) :: (← founders rest)
  | [_] => none

def genesisVerb (store name : String) (fs : List String) : IO UInt32 := do
  let some fs := founders fs | refuse .usage "founders"
  let some key := Digest.ofBytes? (← IO.getRandomBytes 32) | refuse .entropy
  let w₀ := Receive.genesis X name.toUTF8 allowanceMax fs
  match ← (Host.genesis store key (Keys.ofKey key shapes) c world recorder.mark w₀ :
      IO (Except (StoreFault (Record.Fault (Reject D))) Unit)) with
  | .error f => refuseStore f
  | .ok () =>
    for i in List.range fs.length do
      IO.println s!"founder {i} member {(Receive.founderId X name.toUTF8 i).toHex} grant {(Receive.founderGrantId X name.toUTF8 i).toHex}"
    IO.println s!"chain {w₀.chain.toHex}"
    return 0

/-- After the Store opened, an IO error that escapes the loop is the disk or the pipe misbehaving
mid-service, the same class as `uncertain`: `ioServing`, restart (a fresh open recovers or
refuses by name). -/
def serving (act : IO UInt32) : IO UInt32 :=
  try act catch e => refuse .ioServing s!"ioServing {e}"

/-- Whether a `.dedicated` task gets a thread of its own. Without one the reader would run inline,
read stdin to its end, and only then let the loop answer: a resident that answers nothing. -/
def threadsLive : IO Bool := do
  let me ← IO.getTID
  match ← IO.wait (← IO.asTask IO.getTID .dedicated) with
  | .ok tid => pure (tid ≠ me)
  | .error _ => pure false

/-- Read frames from stdin into a bounded channel in a dedicated task; the loop's port and the
reader's task (why it stopped). -/
def stdioPort : IO (Port × Task (Except IO.Error Stop)) := do
  let ch ← Std.CloseableChannel.Sync.new (some queueMax)
  let input ← IO.getStdin
  let reader ← IO.asTask (pump input ch lifetimeFrames) .dedicated
  let out ← IO.getStdout
  return (channelPort ch (← IO.mkRef none) (sendTo out), reader)

def status (verb : String) (fields : List (String × String)) : IO Unit :=
  IO.eprintln s!"STATUS {verb} {" ".intercalate (fields.map fun (k, v) => s!"{k}={v}")}"

def residentFields (r : Resident (World D)) : List (String × String) :=
  [("height", toString r.world.height), ("chain", r.world.chain.toHex),
   ("offset", toString r.pos.offset), ("base_offset", toString r.sealed.offset),
   ("base_height", toString r.sealed.height)]

/-- Run a resident on stdin/stdout: prove the reader thread live, state the opened Store, run the
rounds, and at the end answer every frame still queued `refused stopped`, then state the exit. -/
def runResident (verb : String) (r₀ : Resident (World D))
    (rounds : Port → Resident (World D) → IO (Exit × Resident (World D))) : IO UInt32 := do
  if !(← threadsLive) then return ← refuse .noThreads
  let (port, reader) ← stdioPort
  status verb (residentFields r₀)
  let (exit, r) ← rounds port r₀
  let exit ← match exit with
    | .eof => match ← IO.wait reader with
      | .ok .eof => pure Exit.eof
      | .ok stop => pure (Exit.stream stop)
      | .error _ => pure (Exit.stream .readFailed)
    | e => pure e
  let refused ← refuseQueued port (named FrameRefusal.stopped.name) (queueMax + 1)
  status verb (("exit", exit.status.name) :: ("refused_queued", toString refused) :: residentFields r)
  return exitCode exit

def serveVerb (store : String) : IO UInt32 := do
  match ← (readKey store : IO (Except (StoreFault (Record.Fault (Reject D))) Digest)) with
  | .error f => refuseStore f
  | .ok key =>
    let keys := Keys.ofKey key shapes
    match ← openWriter store keys c world recorder.mark foldStep with
    | .error f => refuseStore f
    | .ok wr => serving do
      let pagerSeg ← File.open (segmentPath store) .read
      let code ← runResident "serve" wr.opening.resident fun port =>
        restarts (serve (machine X) recorder keys.segment (fileCheckpoint store keys c world) c
            (fileStore wr.segment) (pager keys store pagerSeg) port limits fuelBatches)
          (reopenAt store keys c world recorder.mark foldStep) recorder.mark restartsMax
      wr.segment.sync  -- the writer's handle, and so its lock, lives to here
      return code

def followVerb (store memberHex grantHex : String) : IO UInt32 := do
  let some member := hexDigest memberHex | refuse .usage "member"
  let some grant := hexDigest grantHex | refuse .usage "grant"
  match ← (readKey store : IO (Except (StoreFault (Record.Fault (Receive.Verdict D))) Digest)) with
  | .error f => refuseStore f
  | .ok key =>
    let keys := Keys.ofKey key shapes
    -- follow's own Store, reopened by the audit: every Turn of its tail re-derived
    match ← openWriter store keys c world recorder.mark auditStep with
    | .error f => refuseStore f
    | .ok wr => serving do
      let download ← IO.mkRef none
      let code ← runResident "follow" wr.opening.resident fun port =>
        restarts (Follow.loop keys ⟨member, grant, Follow.window⟩ (fileStore wr.segment)
            (fileCheckpoint store keys c world) port download fuelBatches)
          (reopenAt store keys c world recorder.mark auditStep) recorder.mark restartsMax
      wr.segment.sync  -- the follower's handle, and so its lock, lives to here
      return code

def verb : List String → IO UInt32
  | ["genesis", store, name] => genesisVerb store name []
  | "genesis" :: store :: name :: fs => genesisVerb store name fs
  | ["serve", store] => serveVerb store
  | ["follow", store, member, grant] => followVerb store member grant
  | ["check", store] => Check.run store none
  | ["check", store, "--anchor", a] => do
    let some a := Check.Anchor.parse a | refuse .usage "anchor"
    Check.run store (some a)
  | _ => do IO.eprintln usage; return Status.usage.code.toUInt32

/-- Every other IO error ends as `io` with its text, never as the runtime's uncaught-exception
exit 1: it happened before a Store opened (a missing or unreadable Store file, genesis, check),
so a restart would meet it again. -/
def main (args : List String) : IO UInt32 :=
  try verb args catch e => refuse .io s!"io {e}"

end Nanodregg.Host.Cli
