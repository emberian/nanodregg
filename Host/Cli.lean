/-
# Host.Cli — the `host` executable's verbs (Host/Main.lean holds only `main`)

    host genesis STORE NAME [KEY_HEX NEXT_HEX]...   create a Store: founders (Ed25519 key, the
                                                   precommitted NEXT public key; the Store
                                                   holds its digest, `Receive.nextKeyDigest`, which
                                                   only Lean computes: law 2)
    host serve STORE                               the writer loop on stdin/stdout
    host follow STORE MEMBER_HEX GRANT_HEX         the follower loop on stdin/stdout (Host.Follow)
    host check STORE [--anchor STEPS:CHAIN_HEX]   open read-only, print one STATUS line, refuse a
                                                   Store behind or off the anchor (Host.Check)
    host export STORE OUT                          write the carried file of a STOPPED Store's World
                                                   (Host.Carry), print `carried DIGEST`, `from
                                                   ORIGIN`, `anchor S:C`; writes nothing in STORE
    host join STORE INVITE_HEX KEY_HEX              a member's own Store, from an invitation its
                                                   sponsor signed (PROTOCOL-42): `Invite.accept`
                                                   under KEY_HEX, the sponsor's member PUBLIC key
                                                   as the member received it OUT OF BAND (the
                                                   trust root: never take it from the Host), then the
                                                   one genesis of the signed inputs; nothing is
                                                   written unless both passed (`join_genesis_iff`)
    host seal STORE                                the OPERATOR's seal of a STOPPED writer's Store
                                                   (HOST-43): the Store's lock (a live writer holds
                                                   it: `locked`), one seal of the World at its
                                                   position through the writer's own checkpoint
                                                   (`Loop.sealNow`), then `sealed steps=S chain=C
                                                   digest=D`, the base a thin member adopts; at a
                                                   sealed position it writes nothing. No socket op
                                                   seals: a forced seal writes the whole World
    host import STORE NAME IN --digest HEX [--nonce HEX32]
                                                   a new Store from a carried file: the digest is
                                                   REQUIRED and checked, with the stamp and the
                                                   decode, before any Store file exists; KERNEL's
                                                   one carry, the one genesis, then a reopen whose
                                                   carried bytes must be the file's (HOST-28)

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
import Host.Carry
import Protocol.Invite

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

def refuseStore {F : Type} (f : StoreFault F) : IO UInt32 := refuse f.status f.text

def usage : String :=
  "usage: host genesis STORE NAME [--nonce HEX32] [KEY_HEX NEXT_HEX]... | host serve STORE | host seal STORE | host join STORE INVITE_HEX KEY_HEX | host follow STORE MEMBER_HEX GRANT_HEX | host check STORE [--anchor STEPS:CHAIN_HEX] | host export STORE OUT | host import STORE NAME IN --digest HEX [--nonce HEX32]"

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

/-- The genesis nonce (KERNEL-24): `--nonce HEX` (exactly 32 bytes, so a member's own Store can
reproduce the writer's genesis from the invitation), else 32 bytes from the OS. -/
def genesisNonce : Option String → IO (Except Status ByteArray)
  | some h => pure (match Protocol.Text.ofHex h with
      | some b => if b.size = 32 then .ok b else .error .usage
      | none => .error .usage)
  | none => do
      let b ← try IO.getRandomBytes 32 catch _ => pure ByteArray.empty
      pure (if b.size = 32 then .ok b else .error .entropy)

/-- What a genesis prints: the origin, the nonce, each founder's member and grant ids, the chain. -/
def genesisLines (w₀ : World D) (nonce : ByteArray) (n : Nat) : List String :=
  [s!"origin {w₀.origin.toHex}", s!"nonce {Protocol.Text.toHex nonce}"] ++
  (List.range n).map (fun i =>
    s!"founder {i} member {(Receive.founderId X w₀.origin i).toHex} grant {(Receive.founderGrantId X w₀.origin i).toHex}") ++
  [s!"chain {w₀.chain.toHex}"]

def genesisVerb (store name : String) (nonceArg : Option String) (fs : List String) : IO UInt32 := do
  let some fs := founders fs | refuse .usage "founders"
  let nonce ← match ← genesisNonce nonceArg with
    | .ok b => pure b
    | .error s => return ← refuse s "nonce"
  -- KERNEL's genesis refuses, by name, any input past the raw codec's bounds (`GenesisRefusal`)
  let w₀ ← match Receive.genesis X name.toUTF8 nonce allowanceMax fs with
    | .ok w => pure w
    | .error r => return ← refuse .usage r.name
  let some key := Digest.ofBytes? (← IO.getRandomBytes 32) | refuse .entropy
  match ← (Host.genesis store key (Keys.ofKey key shapes) c world recorder.mark w₀ :
      IO (Except (StoreFault (Record.Fault (Reject D))) Unit)) with
  | .error f => refuseStore f
  | .ok () =>
    (genesisLines w₀ nonce fs.length).forM IO.println
    -- last, so no parser of the lines above moves: the inputs a founder invites from (PROTOCOL-42)
    IO.println s!"input {Protocol.Text.toHex (Protocol.Invite.inputBytes X name.toUTF8 nonce allowanceMax fs)}"
    return 0

/-- What `join` reaches outside itself: the Store key (the OS random source), `genesis` (the one
effect that writes a Store path), the refusal and the report. -/
structure JoinFx (m : Type → Type) where
  key : m (Option Digest)
  genesis : Digest → World D → m (Except (StoreFault (Record.Fault (Reject D))) Unit)
  refuse : Status → String → m UInt32
  report : List String → m Unit

/-- `host join`'s decision over its effects. INVITE and KEY parse as hex (`usage`), the invitation
is accepted under KEY (`Protocol.Invite.accept`: any refusal but the genesis's is `inviteRefused`
by name; a genesis refusal is `usage` by its own name, as `host genesis` refuses it), the key is
drawn; only then `genesis` writes the World the signed inputs make. `Host.Proofs.Cli.join_genesis_iff`
states, over this function, that `genesis` runs exactly when every check before it passed. -/
def joinWith {m : Type → Type} [Monad m] (fx : JoinFx m) (inviteHex keyHex : String) : m UInt32 := do
  let some inv := Protocol.Text.ofHex inviteHex | fx.refuse .usage "invite"
  let some trusted := Protocol.Text.ofHex keyHex | fx.refuse .usage "key"
  let (i, w₀) ← match Protocol.Invite.accept X trusted inv with
    | .ok p => pure p
    | .error (.inputs r) => return ← fx.refuse .usage r.name
    | .error r => return ← fx.refuse .inviteRefused s!"inviteRefused {r.name}"
  let some key ← fx.key | fx.refuse .entropy Status.entropy.name
  match ← fx.genesis key w₀ with
  | .error f => fx.refuse f.status f.text
  | .ok () =>
    -- `input` LAST, the line `host genesis` prints: a joiner keeps it to invite from (CLIENT-26)
    fx.report (genesisLines w₀ i.nonce i.founders.length ++ [s!"sponsor {i.sponsor.toHex}",
      s!"input {Protocol.Text.toHex (Protocol.Invite.inputBytes X i.name i.nonce i.allowance i.founders)}"])
    return 0

/-- `host join STORE INVITE_HEX KEY_HEX`: `joinWith` over the files. -/
def joinVerb (store inviteHex keyHex : String) : IO UInt32 :=
  joinWith (inviteHex := inviteHex) (keyHex := keyHex)
    { key := return Digest.ofBytes? (← IO.getRandomBytes 32)
      genesis := fun key w₀ => Host.genesis store key (Keys.ofKey key shapes) c world recorder.mark w₀
      refuse := fun s n => refuse s n
      report := fun ls => ls.forM IO.println }

/-- `host export STORE OUT`: the read-only open `check` makes (`openClean`), the carried file of
its World, checked to read back (`Carry.exportFile`), written to OUT only (never over an existing
file), and its digest, origin and anchor on stdout. Take it from a STOPPED writer (RUNBOOK §6): it
reads a consistent base and the tail that verifies, as `check` does. -/
def exportVerb (store out : String) : IO UInt32 := do
  match ← Check.openClean store with
  | .error (s, n) => refuse s n
  | .ok (_, o) =>
    let w := o.opened.world
    match Carry.exportFile X.env Codec.Deployed.digestCodec w with
    | .error f => refuse .carryMismatch s!"carryMismatch {f.name}"
    | .ok bytes =>
      if ← (System.FilePath.mk out).pathExists then return ← refuse .exists "out"
      writeNew out bytes
      IO.println s!"carried {(Carry.digestOf bytes).toHex}"
      IO.println s!"from {w.origin.toHex}"
      IO.println s!"anchor {w.steps}:{w.chain.toHex}"
      return 0

/-- The most bytes a carried file may have: its stamp and head, and a World's worth. -/
def carriedMax : Nat := Carry.stampBytes + 128 + c.worldBytesMax

/-- What `host import` reaches outside itself, in the order it reaches it. Two effects write:
`genesis` creates the Store's paths, and `reopen` (`openWriter`) locks, truncates and syncs what
`genesis` wrote; `import_genesis_iff` states `genesis` comes first and only after every check. The
others read (IN, the OS random source) or print. `reopen` gives back the reopened World and the act
that releases the writer's handle (its lock lives until then). -/
structure ImportFx (m : Type → Type) where
  nonce : m (Except Status ByteArray)
  readIn : m (Except (StoreFault (Record.Fault (Reject D))) ByteArray)
  key : m (Option Digest)
  genesis : Digest → World D → m (Except (StoreFault (Record.Fault (Reject D))) Unit)
  reopen : Digest → m (Except (StoreFault (Record.Fault (Reject D))) (World D × m Unit))
  refuse : Status → String → m UInt32
  report : List String → m Unit

/-- `host import`'s decision over its effects. The digest parses (`usage digest`), the nonce, IN is
at most `carriedMax`, and `Carry.importWorld` checks the digest, the stamp (`shapeMismatch`), the
decode, the anchor and KERNEL's carry (a name or nonce past its bound is `usage`, any other refusal
`carryMismatch`), and the key is 32 bytes; only then `genesis` writes the World, and the reopen's
carried bytes must be the file's (`carryMismatch reopen`). The deployed verb is
this function at `IO` (`importVerb`); `Host.Proofs.Cli.import_genesis_iff` states, over the same
function, that `genesis` runs exactly when every check before it passed. -/
def importWith {m : Type → Type} [Monad m] (fx : ImportFx m) (name digestHex : String) : m UInt32 := do
  let some want := hexDigest digestHex | fx.refuse .usage "digest"
  let nonce ← match ← fx.nonce with
    | .ok b => pure b
    | .error s => return ← fx.refuse s "nonce"
  let bytes ← match ← fx.readIn with
    | .ok b => pure b
    | .error (.base (.baseTooLarge _)) => return ← fx.refuse .carryMismatch "carryMismatch tooLarge"
    | .error f => return ← fx.refuse f.status f.text
  let dc := Codec.Deployed.digestCodec
  let (w₀, r) ← match Carry.importWorld X dc name.toUTF8 nonce want bytes with
    | .ok p => pure p
    | .error (s, n) => return ← fx.refuse s n
  let some key ← fx.key | fx.refuse .entropy Status.entropy.name
  match ← fx.genesis key w₀ with
  | .error f => fx.refuse f.status f.text
  | .ok () =>
    match ← fx.reopen key with
    | .error f => fx.refuse f.status f.text
    | .ok (back, release) =>
      unless (Codec.Kernel.carried X.env dc).bytes back.carried = bytes.extract r.carriedAt bytes.size do
        return ← fx.refuse .carryMismatch "carryMismatch reopen"
      release
      fx.report [s!"origin {back.origin.toHex}", s!"nonce {Protocol.Text.toHex nonce}",
        s!"from {r.head.fromOrigin.toHex}", s!"height {back.height}", s!"chain {back.chain.toHex}"]
      return 0

/-- `host import STORE NAME IN --digest HEX [--nonce HEX32]`: `importWith` over the files.
`genesis` is `Host.genesis` into STORE (the one writer of a Store path); every refusal before it
leaves nothing (`import_genesis_iff`); a refusal from it on (genesis itself, `openWriter`, the
reopen compare, an IO error mid-write) can leave a Store directory behind. -/
def importVerb (store name inPath digestHex : String) (nonceArg : Option String) : IO UInt32 :=
  importWith (name := name) (digestHex := digestHex)
    { nonce := genesisNonce nonceArg
      readIn := readBounded inPath carriedMax (fun n => .base (.baseTooLarge n))
      key := return Digest.ofBytes? (← IO.getRandomBytes 32)
      genesis := fun key w₀ => Host.genesis store key (Keys.ofKey key shapes) c world recorder.mark w₀
      reopen := fun key => do
        match ← openWriter store (Keys.ofKey key shapes) c world recorder.mark originChain foldStep with
        | .error f => return .error f
        | .ok wr => return .ok (wr.opening.opened.world, wr.segment.sync)
      refuse := fun s n => refuse s n
      report := fun ls => ls.forM IO.println }

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
  [("height", toString r.world.height), ("steps", toString r.world.steps), ("chain", r.world.chain.toHex),
   ("offset", toString r.pos.offset), ("base_offset", toString r.sealed.offset),
   ("base_steps", toString r.sealed.steps)]

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
  let refused ← refuseQueued port (named FrameRefusal.stopped.name) hangUpAnswer (queueMax + 1)
  status verb (("exit", exit.status.name) :: ("refused_queued", toString refused) :: residentFields r)
  return exitCode exit

def serveVerb (store : String) : IO UInt32 := do
  match ← (readKey store : IO (Except (StoreFault (Record.Fault (Reject D))) Digest)) with
  | .error f => refuseStore f
  | .ok key =>
    let keys := Keys.ofKey key shapes
    match ← openWriter store keys c world recorder.mark originChain foldStep with
    | .error f => refuseStore f
    | .ok wr => serving do
      let pagerSeg ← File.open (segmentPath store) .read
      let pagerIdx ← File.open (indexPath store) .read
      let code ← runResident "serve" wr.opening.resident fun port =>
        restarts (serve (machine X) recorder keys.segment (fileCheckpoint store keys c world recorder.mark originChain wr.index) c
            (fileStore wr.segment) (pager keys store pagerSeg pagerIdx) port limits fuelBatches)
          (reopenAt store keys c world recorder.mark originChain foldStep) recorder.mark restartsMax
      wr.segment.sync  -- the writer's handle, and so its lock, lives to here
      return code

def followVerb (store memberHex grantHex : String) : IO UInt32 := do
  let some member := hexDigest memberHex | refuse .usage "member"
  let some grant := hexDigest grantHex | refuse .usage "grant"
  match ← (readKey store : IO (Except (StoreFault (Record.Fault (Receive.Verdict D))) Digest)) with
  | .error f => refuseStore f
  | .ok key =>
    let keys := Keys.ofKey key shapes
    -- follow's own Store, reopened as the writer's is (HOST-22): every Turn in it was admitted by
    -- follow's own fold before it was appended
    match ← openWriter store keys c world recorder.mark originChain foldStep with
    | .error f => refuseStore f
    | .ok wr => serving do
      let download ← IO.mkRef ({} : Protocol.Command.Memory)
      let code ← runResident "follow" wr.opening.resident fun port =>
        -- the World this member was invited to: its own Store's genesis origin, never the writer's word
        restarts (Follow.loop keys ⟨wr.opening.opened.world.origin, member, grant, Follow.window⟩ (fileStore wr.segment)
            (fileCheckpoint store keys c world recorder.mark originChain wr.index) port download fuelBatches)
          (reopenAt store keys c world recorder.mark originChain foldStep) recorder.mark restartsMax
      wr.segment.sync  -- the follower's handle, and so its lock, lives to here
      return code

/-- What `host seal` reaches outside itself: the key, the writer's open (the Store's lock), the
seal (`Loop.sealNow` over the Store's checkpoint: the ONE effect that writes), the refusal and the
report. -/
structure SealFx (m : Type → Type) (R : Type) where
  key : m (Except (StoreFault (Record.Fault (Reject D))) Digest)
  open_ : Digest → m (Except (StoreFault (Record.Fault (Reject D))) R)
  write : R → m (Except SealFault Sealed)
  refuse : Status → String → m UInt32
  report : Sealed → m Unit

/-- `host seal`'s decision over its effects (HOST-43): the key, then the writer's open, and only
then the one seal; any refusal before it is answered by name with nothing written
(`Host.Proofs.Cli.seal_writes_iff`). -/
def sealWith {m : Type → Type} [Monad m] {R : Type} (fx : SealFx m R) : m UInt32 := do
  match ← fx.key with
  | .error f => fx.refuse f.status f.text
  | .ok key =>
    match ← fx.open_ key with
    | .error f => fx.refuse f.status f.text
    | .ok r =>
      match ← fx.write r with
      | .error f => fx.refuse f.status f.name
      | .ok s => fx.report s; return 0

/-- `host seal STORE` (HOST-43): `sealWith` over the files. The open is the writer's
(`openWriter`: the Store's lock, so a running writer refuses it `locked`); the seal is `sealNow`
with the writer's own file checkpoint, inline (the process waits for its one base); the report is
the base an invitation pins: `sealed steps=S chain=C digest=D`. -/
def sealVerb (store : String) : IO UInt32 := do
  let held ← IO.mkRef (none : Option (Writer (World D)))
  let code ← sealWith (R := Keys × Writer (World D))
    { key := readKey store
      open_ := fun key => do
        let keys := Keys.ofKey key shapes
        match ← openWriter store keys c world recorder.mark originChain foldStep with
        | .error f => return .error f
        | .ok wr => held.set (some wr); return .ok (keys, wr)
      write := fun (keys, wr) => do
        let ck := fileCheckpoint store keys c world recorder.mark originChain wr.index (async := false)
        return (← sealNow ck recorder.mark wr.opening.resident).map (·.sealed)
      refuse := fun s n => refuse s n
      report := fun s => IO.println s!"sealed steps={s.steps} chain={Protocol.Text.toHex s.chain} digest={Protocol.Text.toHex s.digest}" }
  -- the writer's handle, and so its lock, lives to here
  if let some wr := ← held.get then wr.segment.sync
  return code

def verb : List String → IO UInt32
  | "genesis" :: store :: name :: "--nonce" :: n :: fs => genesisVerb store name (some n) fs
  | "genesis" :: store :: name :: fs => genesisVerb store name none fs
  | ["serve", store] => serveVerb store
  | ["seal", store] => sealVerb store
  | ["follow", store, member, grant] => followVerb store member grant
  | ["join", store, inv, key] => joinVerb store inv key
  | ["check", store] => Check.run store none
  | ["check", store, "--anchor", a] => do
    let some a := Check.Anchor.parse a | refuse .usage "anchor"
    Check.run store (some a)
  | ["export", store, out] => exportVerb store out
  | ["import", store, name, inp, "--digest", d] => importVerb store name inp d none
  | ["import", store, name, inp, "--digest", d, "--nonce", n] => importVerb store name inp d (some n)
  | ["import", store, name, inp, "--nonce", n, "--digest", d] => importVerb store name inp d (some n)
  | "import" :: _ => refuse .usage "digest"
  | _ => do IO.eprintln usage; return Status.usage.code.toUInt32

/-- Every other IO error ends as `io` with its text, never as the runtime's uncaught-exception
exit 1: it happened before a Store opened (a missing or unreadable Store file, genesis, check),
so a restart would meet it again. -/
def main (args : List String) : IO UInt32 :=
  try
    ignoreFileSizeSignal
    verb args
  catch e => refuse .io s!"io {e}"

end Nanodregg.Host.Cli
