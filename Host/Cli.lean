/-
# Host.Cli — the `host` executable's verbs (Host/Main.lean holds only `main`)

    host genesis STORE NAME [KEY_HEX NEXT_HEX]...   create a Store: founders (Ed25519 key, the
                                                   precommitted NEXT public key; the Store
                                                   holds its digest, `Receive.nextKeyDigest`, which
                                                   only Lean computes: law 2)
    host serve STORE                               the writer loop on stdin/stdout
    host follow STORE MEMBER_HEX GRANT_HEX         the follower loop on stdin/stdout (Host.Follow)

STORE is the only path any verb touches. Frames are `Host.Wire`'s (the supervisor's mux is the
other end). Exit codes, one per `Exit` and one for a refused open, so the supervisor can tell them
apart without parsing text: 0 eof · 2 usage or refused (its name on stderr) · 3 uncertain ·
4 fuel (restart) · 5 sealFailed · 6 recordTooLarge.
-/
import Host.Deployed
import Host.Follow
import Kernel.Receive.Follow

namespace Nanodregg.Host.Cli

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Host.Deployed

/-- How many batches one `serve` process runs before it exits `fuel` and is restarted (law 4: the
one unbounded loop is the supervisor's restart). -/
def fuelBatches : Nat := 1 <<< 24

/-- Frames the reader task may queue ahead of the loop. -/
def queueMax : Nat := 1024

def exitCode : Exit → UInt32
  | .eof => 0
  | .uncertain _ => 3
  | .fuel => 4
  | .sealFailed _ => 5
  | .recordTooLarge _ => 6

def refuse (name : String) : IO UInt32 := do
  IO.eprintln s!"refused {name}"
  return 2

def usage : String :=
  "usage: host genesis STORE NAME [KEY_HEX NEXT_HEX]... | host serve STORE | host follow STORE MEMBER_HEX GRANT_HEX"

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
  let some fs := founders fs | refuse "founders"
  let some key := Digest.ofBytes? (← IO.getRandomBytes 32) | refuse "random"
  let w₀ := Receive.genesis X name.toUTF8 allowanceMax fs
  match ← (Host.genesis store key (Keys.ofKey key) c world w₀ :
      IO (Except (StoreFault (Record.Fault (Reject D))) Unit)) with
  | .error f => refuse f.name
  | .ok () =>
    for i in List.range fs.length do
      IO.println s!"founder {i} member {(Receive.founderId X name.toUTF8 i).toHex} grant {(Receive.founderGrantId X name.toUTF8 i).toHex}"
    IO.println s!"chain {w₀.chain.toHex}"
    return 0

/-- Read frames from stdin into a bounded channel in a dedicated task; the loop's port. -/
def stdioPort : IO Port := do
  let ch ← Std.CloseableChannel.Sync.new (some queueMax)
  let input ← IO.getStdin
  let _ ← IO.asTask (pump input ch fuelBatches) .dedicated
  return channelPort ch (← IO.getStdout)

def serveVerb (store : String) : IO UInt32 := do
  match ← (readKey store : IO (Except (StoreFault (Record.Fault (Reject D))) Digest)) with
  | .error f => refuse f.name
  | .ok key =>
    let keys := Keys.ofKey key
    match ← openWriter store keys c world recorder.mark foldStep with
    | .error f => refuse f.name
    | .ok wr =>
      let port ← stdioPort
      let (exit, _) ← serve (machine X) recorder keys.segment (fileCheckpoint store keys c world) c
        (fileStore wr.segment) (pager keys store (← File.open (segmentPath store) .read)) port limits
        fuelBatches wr.opening.resident none
      wr.segment.sync  -- the writer's handle, and so its lock, lives to here
      if exitCode exit ≠ 0 then IO.eprintln s!"exit {exit.name}"
      return exitCode exit

def followVerb (store memberHex grantHex : String) : IO UInt32 := do
  let some member := hexDigest memberHex | refuse "member"
  let some grant := hexDigest grantHex | refuse "grant"
  match ← (readKey store : IO (Except (StoreFault (Record.Fault (Receive.Verdict D))) Digest)) with
  | .error f => refuse f.name
  | .ok key =>
    let keys := Keys.ofKey key
    -- follow's own Store, reopened by the audit: every Turn of its tail re-derived
    match ← openWriter store keys c world recorder.mark auditStep with
    | .error f => refuse f.name
    | .ok wr =>
      IO.eprintln s!"follow: audited to height {wr.opening.opened.world.height}"
      let port ← stdioPort
      let (exit, _) ← Follow.loop keys ⟨member, grant, Follow.window⟩ (fileStore wr.segment)
        (fileCheckpoint store keys c world) port fuelBatches wr.opening.resident
      wr.segment.sync  -- the follower's handle, and so its lock, lives to here
      if exitCode exit ≠ 0 then IO.eprintln s!"exit {exit.name}"
      return exitCode exit

def main : List String → IO UInt32
  | ["genesis", store, name] => genesisVerb store name []
  | "genesis" :: store :: name :: fs => genesisVerb store name fs
  | ["serve", store] => serveVerb store
  | ["follow", store, member, grant] => followVerb store member grant
  | _ => do IO.eprintln usage; return 2

end Nanodregg.Host.Cli
