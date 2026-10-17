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
-/
import Host.Deployed
import Host.Follow
import Host.Exit
import Host.Check
import Kernel.Receive.Follow

namespace Nanodregg.Host.Cli

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Host.Deployed

/-- How many batches one `serve` process runs before it exits `fuel` and is restarted (law 4: the
one unbounded loop is the supervisor's restart). -/
def fuelBatches : Nat := 1 <<< 24

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
  match ← (Host.genesis store key (Keys.ofKey key) c world recorder.mark w₀ :
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

/-- Read frames from stdin into a bounded channel in a dedicated task; the loop's port. -/
def stdioPort : IO Port := do
  let ch ← Std.CloseableChannel.Sync.new (some queueMax)
  let input ← IO.getStdin
  let _ ← IO.asTask (pump input ch fuelBatches) .dedicated
  return channelPort ch (← IO.getStdout)

def serveVerb (store : String) : IO UInt32 := do
  match ← (readKey store : IO (Except (StoreFault (Record.Fault (Reject D))) Digest)) with
  | .error f => refuseStore f
  | .ok key =>
    let keys := Keys.ofKey key
    match ← openWriter store keys c world recorder.mark foldStep with
    | .error f => refuseStore f
    | .ok wr => serving do
      let port ← stdioPort
      let (exit, _) ← serve (machine X) recorder keys.segment (fileCheckpoint store keys c world) c
        (fileStore wr.segment) (pager keys store (← File.open (segmentPath store) .read)) port limits
        fuelBatches wr.opening.resident none
      wr.segment.sync  -- the writer's handle, and so its lock, lives to here
      if exitCode exit ≠ 0 then IO.eprintln s!"exit {exit.status.name}"
      return exitCode exit

def followVerb (store memberHex grantHex : String) : IO UInt32 := do
  let some member := hexDigest memberHex | refuse .usage "member"
  let some grant := hexDigest grantHex | refuse .usage "grant"
  match ← (readKey store : IO (Except (StoreFault (Record.Fault (Receive.Verdict D))) Digest)) with
  | .error f => refuseStore f
  | .ok key =>
    let keys := Keys.ofKey key
    -- follow's own Store, reopened by the audit: every Turn of its tail re-derived
    match ← openWriter store keys c world recorder.mark auditStep with
    | .error f => refuseStore f
    | .ok wr => serving do
      IO.eprintln s!"follow: audited to height {wr.opening.opened.world.height}"
      let port ← stdioPort
      let (exit, _) ← Follow.loop keys ⟨member, grant, Follow.window⟩ (fileStore wr.segment)
        (fileCheckpoint store keys c world) port fuelBatches none wr.opening.resident
      wr.segment.sync  -- the follower's handle, and so its lock, lives to here
      if exitCode exit ≠ 0 then IO.eprintln s!"exit {exit.status.name}"
      return exitCode exit

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
