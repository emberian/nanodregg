/-
# Host.Cli — the `host` executable's verbs (Host/Main.lean holds only `main`)

    host genesis STORE NAME [KEY_HEX NEXT_HEX]...   create a Store: founders (Ed25519 key, the
                                                   precommitted NEXT public key; the Store
                                                   holds its digest, `Receive.nextKeyDigest`, which
                                                   only Lean computes: law 2)
    host serve STORE [--retain N]                  the writer loop on stdin/stdout; with --retain
                                                   (N ≥ 2, `retainBelowFloor` below) each base
                                                   install keeps the N newest segment files and
                                                   drops the rest (HOST-64); without it nothing
                                                   is ever dropped; with --certify SOCK each
                                                   installed base is certified through
                                                   keybroker's writer socket (Host.Certify)
    host follow STORE MEMBER_HEX GRANT_HEX         the follower loop on stdin/stdout (Host.Follow)
    host check STORE [--anchor STEPS:CHAIN_HEX]   open read-only, print one STATUS line, refuse a
                                                   Store behind or off the anchor (Host.Check)
    host certified INPUT_HEX CERT                  the stranger's check (Protocol.Certified): the
                                                   head CERT certifies under the authority the
                                                   genesis input commits; no Store read
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
    host seal STORE [--retain N]                   the OPERATOR's seal of a STOPPED writer's Store
                                                   (HOST-43): the Store's lock (a live writer holds
                                                   it: `locked`), one seal of the World at its
                                                   position through the writer's own checkpoint
                                                   (`Loop.sealNow`), then `sealed steps=S chain=C
                                                   digest=D`, the base a thin member adopts; at a
                                                   sealed position the seal writes nothing (the open may repair a torn tail, HOST-77). No socket op
                                                   seals: a forced seal writes the whole World
    host import STORE NAME IN --digest HEX [--nonce HEX32]
    host import STORE NAME IN --origin HEX --nonce HEX32
                                                   a new Store from a carried file, PINNED: by the
                                                   file's digest (the operator's own carry), or by
                                                   the origin of the World it makes (a sponsor's
                                                   invitation names it with the name and nonce:
                                                   another is `carryMismatch wrongWorld`); every
                                                   check runs before any Store file exists; KERNEL's
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
import Host.Certify
import Protocol.Certified
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
  "usage: host genesis STORE NAME [--nonce HEX32] [--certifier HEX32]... [--threshold N] [KEY_HEX NEXT_HEX]... | host serve STORE [--retain N] [--certify SOCK] | host seal STORE [--retain N] [--certify SOCK] | host join STORE INVITE_HEX KEY_HEX [IN (carried only)] | host follow STORE MEMBER_HEX GRANT_HEX | host check STORE [--anchor STEPS:CHAIN_HEX] | host export STORE OUT | host certified INPUT_HEX CERT | host import STORE NAME IN (--digest HEX [--nonce HEX32] | --origin HEX --nonce HEX32)"

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

/-- What a genesis prints: the origin, the nonce, each founder's member and grant ids, the chain,
then the authority (KERNEL-69) as `authority THRESHOLD COUNT`. Nothing above `chain` moves; `input`
follows last. -/
def genesisLines (w₀ : World D) (nonce : ByteArray) (n : Nat) (auth : Receive.Authority) : List String :=
  [s!"origin {w₀.origin.toHex}", s!"nonce {Protocol.Text.toHex nonce}"] ++
  (List.range n).map (fun i =>
    s!"founder {i} member {(Receive.founderId X w₀.origin i).toHex} grant {(Receive.founderGrantId X w₀.origin i).toHex}") ++
  [s!"chain {w₀.chain.toHex}", s!"authority {auth.threshold} {auth.certifiers.length}"]

/-- The certifier keys from `--certifier HEX` options, in order: each exactly 32 bytes. The quorum
itself is not judged here: `Receive.genesis` refuses `badThreshold`, `repeatedCertifier`, … by name. -/
def certifiers : List String → Option (List ByteArray)
  | [] => some []
  | k :: rest => do
    let key ← Protocol.Text.ofHex k
    if key.size ≠ 32 then none
    return key :: (← certifiers rest)

/-- The budget check every World this binary creates a Store from passes (HOST-56, KERNEL-55; `host
genesis`, `host join`, `host import`, before anything is written): its allowance within
`allowanceMax` (ROOT's Q3), and its potential within `Host.potentialMax`. The second arm is what bounds the
World a fold reaches (`Host.Cli.budget_reaches`): an allowance check alone admits a carried World
heavy enough that admitted turns grow it past the derived World bound. -/
def budgetFault (w : World D) : Option Status :=
  if allowanceMax < w.allowance then some .allowancePastBound
  else if potentialMax < potential w then some .potentialPastBound
  else none

def genesisVerb (store name : String) (nonceArg : Option String) (certifierArgs : List String)
    (thresholdArg : Option String) (fs : List String) : IO UInt32 := do
  let some fs := founders fs | refuse .usage "founders"
  let some cs := certifiers certifierArgs | refuse .usage "certifier"
  let some t := (match thresholdArg with | none => some 0 | some v => v.toNat?) | refuse .usage "threshold"
  let auth : Receive.Authority := ⟨cs, t⟩
  let nonce ← match ← genesisNonce nonceArg with
    | .ok b => pure b
    | .error s => return ← refuse s "nonce"
  -- KERNEL's genesis refuses, by name, any input past the raw codec's bounds and any quorum nobody
  -- meets (`GenesisRefusal`)
  let w₀ ← match Receive.genesis X name.toUTF8 nonce allowanceMax fs auth with
    | .ok w => pure w
    | .error r => return ← refuse .usage r.name
  if let some s := budgetFault w₀ then return ← refuse s s.name
  let some key := Digest.ofBytes? (← IO.getRandomBytes 32) | refuse .entropy
  match ← (Host.genesis store key (Keys.ofKey key shapes) c world recorder.mark w₀ :
      IO (Except (StoreFault (Record.Fault (Reject D))) Unit)) with
  | .error f => refuseStore f
  | .ok () =>
    (genesisLines w₀ nonce fs.length auth).forM IO.println
    -- last, so no parser of the lines above moves: the inputs a founder invites from (PROTOCOL-42)
    IO.println s!"input {Protocol.Text.toHex (Protocol.Invite.inputBytes X name.toUTF8 nonce allowanceMax fs auth)}"
    return 0

/-- `host export STORE OUT`: the read-only open `check` makes (`openClean`), the carried file of
its World, checked to read back (`Carry.exportFile`), written to OUT only (never over an existing
file), and its digest, origin and anchor on stdout. Take it from a STOPPED writer (RUNBOOK §6): it
reads a consistent base and the tail that verifies, as `check` does. -/
def exportVerb (store out : String) : IO UInt32 := do
  match ← Check.openClean store with
  | .error (s, n) => refuse s n
  | .ok k =>
    let w := k.opening.opened.world
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

/-- `host import`'s pin as given: `--digest HEX` or `--origin HEX`. -/
inductive PinArg where
  | digest (hex : String)
  | origin (hex : String)

/-- The pin's argument name (`usage digest` / `usage origin` when its hex does not parse). -/
def PinArg.name : PinArg → String
  | .digest _ => "digest"
  | .origin _ => "origin"

def PinArg.parse : PinArg → Option (Carry.Pin D)
  | .digest h => (hexDigest h).map .digest
  | .origin h => (hexDigest h).map .origin

/-- What `host import` reaches outside itself, in the order it reaches it. Two effects write:
`genesis` creates the Store's paths, and `reopen` (`openWriter`) locks, truncates and syncs what
`genesis` wrote; `import_genesis_iff` states `genesis` comes first and only after every check. The
others read (IN, the OS random source) or print. `reopen` gives back the reopened World. -/
structure ImportFx (m : Type → Type) where
  nonce : m (Except Status ByteArray)
  readIn : m (Except (StoreFault (Record.Fault (Reject D))) ByteArray)
  key : m (Option Digest)
  genesis : Digest → World D → m (Except (StoreFault (Record.Fault (Reject D))) Unit)
  reopen : Digest → m (Except (StoreFault (Record.Fault (Reject D))) (World D))
  refuse : Status → String → m UInt32
  report : List String → m Unit

/-- `host import`'s decision over its effects. The pin parses (`usage digest` / `usage origin`), the
nonce, IN is at most `carriedMax`, and `Carry.importWorld` checks the digest pin, the stamp
(`shapeMismatch`), the decode, the anchor, KERNEL's carry (a name or nonce past its bound is `usage`,
any other refusal `carryMismatch`) and the origin pin (`carryMismatch wrongWorld`), and the key is 32
bytes; only then `genesis` writes the World, and the reopen's
carried bytes must be the file's (`carryMismatch reopen`). The deployed verb is
this function at `IO` (`importVerb`); `Host.Proofs.Cli.import_genesis_iff` states, over the same
function, that `genesis` runs exactly when every check before it passed. -/
def importWithPin {m : Type → Type} [Monad m] (fx : ImportFx m) (name : ByteArray)
    (pin : Carry.Pin D) (anchor : Option (Carry.Head D) := none) :
    m UInt32 := do
  let nonce ← match ← fx.nonce with
    | .ok b => pure b
    | .error s => return ← fx.refuse s "nonce"
  let bytes ← match ← fx.readIn with
    | .ok b => pure b
    | .error (.base (.baseTooLarge _)) => return ← fx.refuse .carryMismatch "carryMismatch tooLarge"
    | .error f => return ← fx.refuse f.status f.text
  let dc := Codec.Deployed.digestCodec
  let (w₀, r) ← match Carry.importWorld X dc name nonce pin bytes with
    | .ok p => pure p
    | .error (s, n) => return ← fx.refuse s n
  if let some h := anchor then
    unless r.head.fromOrigin = h.fromOrigin ∧ r.head.height = h.height ∧ r.head.chain = h.chain do
      return ← fx.refuse .carryMismatch "carryMismatch anchor"
  match budgetFault w₀ with
  | some s => return ← fx.refuse s s.name
  | none => pure ()
  let some key ← fx.key | fx.refuse .entropy Status.entropy.name
  match ← fx.genesis key w₀ with
  | .error f => fx.refuse f.status f.text
  | .ok () =>
    match ← fx.reopen key with
    | .error f => fx.refuse f.status f.text
    | .ok back =>
      unless (Codec.Kernel.carried X.env dc).bytes back.carried = bytes.extract r.carriedAt bytes.size do
        return ← fx.refuse .carryMismatch "carryMismatch reopen"
      fx.report [s!"origin {back.origin.toHex}", s!"nonce {Protocol.Text.toHex nonce}",
        s!"from {r.head.fromOrigin.toHex}", s!"height {back.height}", s!"chain {back.chain.toHex}",
        s!"start {Protocol.Text.toHex (Protocol.Invite.startBytes X (.carried back.origin name nonce r.head.fromOrigin r.head.height r.head.chain))}"]
      return 0

/-- Parse the operator's pin, then use the same importer as a carried join. -/
def importWith {m : Type → Type} [Monad m] (fx : ImportFx m) (name : String) (pinHex : PinArg) :
    m UInt32 := do
  let some pin := pinHex.parse | fx.refuse .usage pinHex.name
  importWithPin fx name.toUTF8 pin

/-- Join uses import's effects; its nonce comes only from the signed start. -/
abbrev JoinFx := ImportFx

/-- One join verb, accepting either a genesis start without IN or a carried start with IN. -/
def joinWith {m : Type → Type} [Monad m] (fx : JoinFx m) (inviteHex keyHex : String)
    (inPath : Option String := none) : m UInt32 := do
  let some inv := Protocol.Text.ofHex inviteHex | fx.refuse .usage "invite"
  let some trusted := Protocol.Text.ofHex keyHex | fx.refuse .usage "key"
  let (i, _) ← match Protocol.Invite.acceptStart X trusted inv with
    | .ok p => pure p
    | .error (.inputs r) => return ← fx.refuse .usage r.name
    | .error r => return ← fx.refuse .inviteRefused s!"inviteRefused {r.name}"
  match i.start with
  | .carried o name nonce fromO height chain =>
    if inPath.isNone then return ← fx.refuse .usage "in"
    importWithPin { fx with nonce := pure (.ok nonce), report := (fun ls =>
        fx.report ([s!"sponsor {i.sponsor.toHex}"] ++ ls ++
        [s!"input {Protocol.Text.toHex (Protocol.Invite.startBytes X i.start)}"])) }
      name (.origin o) (some ⟨fromO, height, chain⟩)
  | .genesis _ nonce _ fs auth =>
    if inPath.isSome then return ← fx.refuse .usage "in"
    let w₀ ← match Protocol.Invite.startGenesis X i.start with
      | .ok w => pure w
      | .error r => return ← fx.refuse .inviteRefused s!"inviteRefused {r.name}"
    match budgetFault w₀ with
    | some s => return ← fx.refuse s s.name
    | none => pure ()
    let some key ← fx.key | fx.refuse .entropy Status.entropy.name
    match ← fx.genesis key w₀ with
    | .error f => fx.refuse f.status f.text
    | .ok () =>
      fx.report (genesisLines w₀ nonce fs.length auth ++ [s!"sponsor {i.sponsor.toHex}",
        s!"input {Protocol.Text.toHex (Protocol.Invite.startBytes X i.start)}"])
      return 0

/-- Files behind the one join verb. The optional path is read only for a carried invitation. -/
def joinVerb (store inviteHex keyHex : String) (inPath : Option String) : IO UInt32 :=
  joinWith (inviteHex := inviteHex) (keyHex := keyHex) (inPath := inPath)
    { nonce := pure (.ok ByteArray.empty)
      readIn := match inPath with
        | some p => readBounded p carriedMax (fun n => .base (.baseTooLarge n))
        | none => pure (.error (.missing .base))
      key := return Digest.ofBytes? (← IO.getRandomBytes 32)
      genesis := fun key w₀ => Host.genesis store key (Keys.ofKey key shapes) c world recorder.mark w₀
      reopen := fun key => do
        match ← openWriter store (Keys.ofKey key shapes) c world recorder.mark originChain foldStep with
        | .error f => return .error f
        | .ok wr => return .ok wr.opening.opened.world
      refuse := fun s n => refuse s n
      report := fun ls => ls.forM IO.println }

/-- `host import STORE NAME IN (--digest HEX [--nonce HEX32] | --origin HEX --nonce HEX32)`:
`importWith` over the files.
`genesis` is `Host.genesis` into STORE (the one writer of a Store path); every refusal before it
leaves nothing (`import_genesis_iff`); a refusal from it on (genesis itself, `openWriter`, the
reopen compare, an IO error mid-write) can leave a Store directory behind. -/
def importVerb (store name inPath : String) (pinHex : PinArg) (nonceArg : Option String) : IO UInt32 :=
  importWith (name := name) (pinHex := pinHex)
    { nonce := genesisNonce nonceArg
      readIn := readBounded inPath carriedMax (fun n => .base (.baseTooLarge n))
      key := return Digest.ofBytes? (← IO.getRandomBytes 32)
      genesis := fun key w₀ => Host.genesis store key (Keys.ofKey key shapes) c world recorder.mark w₀
      reopen := fun key => do
        match ← openWriter store (Keys.ofKey key shapes) c world recorder.mark originChain foldStep with
        | .error f => return .error f
        | .ok wr => return .ok wr.opening.opened.world
      refuse := fun s n => refuse s n
      report := fun ls => ls.forM IO.println }

/-- After the Store opened, an IO error that escapes the loop is the disk or the pipe misbehaving
mid-service, the same class as `uncertain`: `ioServing`, restart (a fresh open recovers or
refuses by name). A page's IO error does not escape: it refuses that page `pageIo`
(`Host.pageOrRefuse`, HOST-48). -/
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
rounds, and at the end answer every frame still queued `declined stopped` (`FrameRefusal.stopped.reply`:
nothing of it was admitted, so not final), then state the exit. -/
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
  let refused ← refuseQueued port FrameRefusal.stopped.reply hangUpAnswer (queueMax + 1)
  status verb (("exit", exit.status.name) :: ("refused_queued", toString refused) :: residentFields r)
  return exitCode exit

/-- `host serve STORE [--retain N] [--certify SOCK]`: with `--certify`, every base a seal installs is
certified through keybroker's writer socket SOCK and `base.cert` replaced (`Host.Certify`, HOST-80), and
a Store that holds no certificate yet has its newest base certified at the start (PROTOCOL-84). -/
def serveVerb (store : String) (retain : Retain) (certify : Option String := none) : IO UInt32 := do
  match ← (readKey store : IO (Except (StoreFault (Record.Fault (Reject D))) Digest)) with
  | .error f => refuseStore f
  | .ok key =>
    let keys := Keys.ofKey key shapes
    match ← openWriter store keys c world recorder.mark originChain foldStep retain with
    | .error f => refuseStore f
    | .ok wr => serving do
      let files : PageFiles := ⟨store, keys, originChain wr.opening.opened.world, wr.kept,
        ← IO.mkRef #[wr.opening.sealed.offset], wr.generation⟩
      let ck := fileCheckpoint store keys c world recorder.mark originChain wr
      let ck ← match certify with
        | some sock => do
          let queue ← Certify.start store sock lifetimeFrames
          -- a Store with no certificate yet (a fresh genesis): its newest base is certified now, not at
          -- the next seal, so under an authority that certifies no honest page goes out without one
          -- (followers refuse such a page `uncertifiedPage`, PROTOCOL-84)
          if (← readCert store).isEmpty then
            let file ← IO.FS.readBinFile (basePath store)
            if let .ok w := world.decode (worldBytesOf file wr.opening.sealed.bytes) then queue w
          pure (Certify.certifying ck queue)
        | none => pure ck
      let code ← runResident "serve" wr.opening.resident fun port =>
        restarts (serve (machine X) recorder keys.segment ck c
            (fileStore wr) (pager keys files) port limits fuelBatches)
          (reopenAt store keys c world recorder.mark originChain foldStep) recorder.mark restartsMax
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
      -- follow's own kept files, read as serve's pager reads them: the chain at a behind post's step (T2b')
      let files : PageFiles := ⟨store, keys, originChain wr.opening.opened.world, wr.kept,
        ← IO.mkRef #[wr.opening.sealed.offset], wr.generation⟩
      let code ← runResident "follow" wr.opening.resident fun port =>
        -- the World this member was invited to: its own Store's genesis origin, never the writer's word
        restarts (Follow.loop keys ⟨wr.opening.opened.world.origin, member, grant, Follow.window⟩ (fileStore wr)
            (fileCheckpoint store keys c world recorder.mark originChain wr) files port download fuelBatches)
          (reopenAt store keys c world recorder.mark originChain foldStep) recorder.mark restartsMax
      return code

/-- What `host seal` reaches outside itself: the key, the writer's open (the Store's lock), the
seal (`Loop.sealNow` over the Store's checkpoint: the one effect that writes a base), the refusal
and the report. The open is `openWriter`'s, which also writes (HOST-77): it truncates a torn tail and
orphan index entries and syncs, and with `--retain` unlinks surplus files; `seal_writes_iff`
models the open as pure, so its "nothing written" is about the seal's effects, not the open's. -/
structure SealFx (m : Type → Type) (R : Type) where
  key : m (Except (StoreFault (Record.Fault (Reject D))) Digest)
  open_ : Digest → m (Except (StoreFault (Record.Fault (Reject D))) R)
  write : R → m (Except SealFault Sealed)
  refuse : Status → String → m UInt32
  report : Sealed → m Unit

/-- `host seal`'s decision over its effects (HOST-43): the key, then the writer's open, and only
then the one seal; a refusal before the seal is answered by name with no base written
(`Host.Proofs.Cli.seal_writes_iff`; the open's own repair of a torn tail is the open's, HOST-77). -/
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
the base an invitation pins: `sealed steps=S chain=C digest=D`. With `--certify SOCK` (HOST-80) the
base it leaves (the one it wrote, or the one already at the World's position) is then certified
through keybroker's writer socket, as `host serve --certify` certifies each seal (`Host.Certify`). -/
def sealVerb (store : String) (retain : Retain) (certify : Option String := none) : IO UInt32 :=
  sealWith (R := Keys × Writer (World D))
    { key := readKey store
      open_ := fun key => do
        let keys := Keys.ofKey key shapes
        match ← openWriter store keys c world recorder.mark originChain foldStep retain with
        | .error f => return .error f
        | .ok wr => return .ok (keys, wr)
      write := fun (keys, wr) => do
        let ck := fileCheckpoint store keys c world recorder.mark originChain wr (async := false)
        let r ← sealNow ck recorder.mark wr.opening.resident
        if let (.ok _, some sock) := (r, certify) then
          Certify.certifyBase store sock wr.opening.resident.world
        return r.map (·.sealed)
      refuse := fun s n => refuse s n
      report := fun s => IO.println s!"sealed steps={s.steps} chain={Protocol.Text.toHex s.chain} digest={Protocol.Text.toHex s.digest}" }

/-- `--retain N`: refused `usage` by the name `retainBelowFloor` under the floor of two files
(`Host.retainFloor`), `usage retain` when N is not a number; nothing is opened before it parses. -/
def withRetain (n : String) (k : Retain → IO UInt32) : IO UInt32 :=
  match Retain.parse n with
  | .ok r => k r
  | .error name => refuse .usage name

/-- `host genesis`'s options, in any order before the founders: `--nonce HEX32` (KERNEL-24),
`--certifier HEX32` (repeatable, in order) and `--threshold N` (KERNEL-69; neither given is
`Authority.none`). -/
def genesisOpts (store name : String) : List String → Option String → List String → Option String → IO UInt32
  | "--nonce" :: n :: rest, _, cs, t => genesisOpts store name rest (some n) cs t
  | "--certifier" :: k :: rest, n, cs, t => genesisOpts store name rest n (cs ++ [k]) t
  | "--threshold" :: v :: rest, n, cs, _ => genesisOpts store name rest n cs (some v)
  | fs, n, cs, t => genesisVerb store name n cs t fs

/-- `host certified INPUT_HEX CERT`: the stranger's check (PROTOCOL-78, DESIGN-TRUST T3e). From a
World's genesis input (`host genesis`'s `input` line) and a certificate file alone, the head the
certificate certifies under the authority the input commits (`Protocol.Certified.check`), printed
`certified origin=O steps=S height=H roots=R chain=C`; refused `notCertified` with the reason's name.
No Store is read and nothing is written. -/
def certifiedVerb (inputHex certPath : String) : IO UInt32 := do
  let some input := Protocol.Text.ofHex inputHex | refuse .usage "input"
  let cert ← IO.FS.readBinFile certPath
  match Protocol.Certified.check X input cert with
  | .error r => refuse .notCertified s!"notCertified {r.name}"
  | .ok h =>
    IO.println s!"certified origin={h.origin.toHex} steps={h.steps} height={h.height} roots={h.roots.toHex} chain={h.chain.toHex}"
    return 0

def verb : List String → IO UInt32
  | "genesis" :: store :: name :: rest => genesisOpts store name rest none [] none
  | ["serve", store] => serveVerb store none
  | ["serve", store, "--retain", n] => withRetain n (serveVerb store)
  | ["serve", store, "--certify", sock] => serveVerb store none (some sock)
  | ["serve", store, "--retain", n, "--certify", sock] => withRetain n (fun r => serveVerb store r (some sock))
  | ["seal", store] => sealVerb store none
  | ["seal", store, "--retain", n] => withRetain n (sealVerb store)
  | ["seal", store, "--certify", sock] => sealVerb store none (some sock)
  | ["seal", store, "--retain", n, "--certify", sock] => withRetain n (fun r => sealVerb store r (some sock))
  | ["follow", store, member, grant] => followVerb store member grant
  | ["join", store, inv, key] => joinVerb store inv key none
  | ["join", store, inv, key, inp] => joinVerb store inv key (some inp)
  | ["check", store] => Check.run store none
  | ["check", store, "--anchor", a] => do
    let some a := Check.Anchor.parse a | refuse .usage "anchor"
    Check.run store (some a)
  | ["export", store, out] => exportVerb store out
  | ["certified", input, cert] => certifiedVerb input cert
  | ["import", store, name, inp, "--digest", d] => importVerb store name inp (.digest d) none
  | ["import", store, name, inp, "--digest", d, "--nonce", n] => importVerb store name inp (.digest d) (some n)
  | ["import", store, name, inp, "--nonce", n, "--digest", d] => importVerb store name inp (.digest d) (some n)
  -- an origin pin needs the invitation's nonce: a fresh one can never make the named origin
  | ["import", store, name, inp, "--origin", o, "--nonce", n] => importVerb store name inp (.origin o) (some n)
  | ["import", store, name, inp, "--nonce", n, "--origin", o] => importVerb store name inp (.origin o) (some n)
  | ["import", _, _, _, "--origin", _] => refuse .usage "nonce"
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
