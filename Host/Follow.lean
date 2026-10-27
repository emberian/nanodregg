/-
# Host.Follow — `host follow`: the member's own Store, audited at follow time, driven by steps

    loop, one frame at a time (conn, op, payload) from the supervisor:
      command(argv)      → Command.start on follow's World                     → a step
      resume(k, result)  → Command.step: absorbs any log page it carried, every event re-derived
                           (PROTOCOL-4)                                        → a step
      steps absorbed     → appended to follow's own segment as one batch record, durably, BEFORE
                           the step is answered (`Host.append`, the writer's own append path);
                           a page of more steps than one record holds (`recordTurnsMax`, which
                           an honest page never exceeds: `Page.build_events_le`) is refused
                           `recordTooLarge`, never written as a record its reopen refuses

Follow decides nothing the kernel does not: `Command.step` re-judges every logged event (a Turn by
`Receive.submit`, a recorded refusal by `Receive.judge`, which must record the very same refusal)
BEFORE anything is appended, so follow's Store holds only steps its own `World.step` took
(`Protocol.Command.step_persists_admitted`). Its Store is the same format as
the writer's (key, segment of batch records, sealed base) and is reopened EXACTLY as the writer's
is: the one `openWriter`, folding with `World.step` (`Deployed.foldStep`), no signature verified at
reopen (HOST-22, ROOT ruling 2026-10-17: the base and the tail rest under one MAC and key, so a
reopen re-audit distinguishes nothing the MAC does not). A logged event that does not re-derive is refused by the step
(`eventMismatch`), and a page whose stated chain is not follow's fold by `chainMismatch`. Both are
PROTOCOL's names, carried in the step's `done`.

Refusals before the machine, by name: `undecodableCommand`, `undecodableResume`, `wrongSocket`
(submit, lookup, read, log, cancel belong to host.sock), `unknownOp`. One refusal AFTER the machine:
`stepTooLarge`, a step whose reply has no wire bytes (a field past `frameBytesMax`, or a `.host`
submit, `Protocol.Command.Wire`). That step's effects are kept: the steps it absorbed (catch-up of
the writer's log, each re-derived) are appended, or the base it adopted is sealed, BEFORE the
refusal is sent; only the reply is refused (HOST-77). The member's next command starts from that
durable World.
-/
import Protocol.Command.Frames
import Host.Deployed
import Protocol.Command.Wire

namespace Nanodregg.Host.Follow

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Host.Deployed Nanodregg.Protocol

/-- Why follow refuses a frame before the machine sees it (law 7). -/
inductive Refusal where
  | undecodableCommand
  | undecodableResume
  | wrongSocket (op : Protocol.Op)
  | unknownOp (code : UInt8)
  | stepTooLarge
  deriving Repr

def Refusal.name : Refusal → String
  | .undecodableCommand => "undecodableCommand"
  | .undecodableResume => "undecodableResume"
  | .wrongSocket _ => "wrongSocket"
  | .unknownOp _ => "unknownOp"
  | .stepTooLarge => "stepTooLarge"

/-- How many heights a call or envelope follow plans stays valid. -/
def window : Nat := 128

/-- One frame's answer: follow's state after it (its World and any base download in progress),
what to make durable before replying (`Command.Persist`), the reply. Generic in the `Ctx` and the
way a base is read (`Protocol.Thin.Base`), so PROTOCOL's rows drive this very function on their
toy digest. -/
def answer {D : Type} [Ord D] [DecidableEq D] (X : Receive.Ctx D) (dc : Stream D) (B : Protocol.Thin.Base (World D))
    (me : Command.Self D) (fs : Command.Follow D) (f : Frame) :
    Command.Follow D × Command.Persist D × UInt8 × ByteArray :=
  let refused (r : Refusal) := (fs, .steps [], named r.name)
  let stepOut (fs' : Command.Follow D) (p : Command.Persist D) (r : Command.Reply) :=
    match r.bytes with
    | some b => (fs', p, Status.ok.code, b)
    | none => (fs', p, named Refusal.stepTooLarge.name)
  match Protocol.Op.ofCode? f.op with
  | none =>
    match hangUpAnswer f with
    | some (s, p) => (fs, .steps [], s, p)
    | none => refused (.unknownOp f.op)
  | some .command =>
    match commandFrame.decode f.payload with
    | .error _ => refused .undecodableCommand
    | .ok v => stepOut fs (.steps []) (Command.start X me fs (Text.unlist v.1.1))
  | some .resume =>
    match resumeFrame.decode f.payload with
    | .error _ => refused .undecodableResume
    | .ok (k, result, ()) =>
      let (fs', p, r) := Command.step X dc B me fs k.1 result.1
      stepOut fs' p r
  | some op => refused (.wrongSocket op)

/-- The reply a page's BEHIND self-head posts force, else `out` (T2b', cv 01a176ab-14f5): a post at a
step count follow was already at or past before the page (`Head.behindPosts`: the walk of
`Command.postOr` cannot reach it) is compared with the chain follow's OWN Store holds at that step
(`chainKept` over the kept files, `r` the Store before the page is appended); the first mismatch is
`refused forkedPost` (`Head.forkedBehindPost`, `Proofs.Head.forkedBehindPost_forked`), the page kept
as `postOr` keeps it. A step below the kept files, or a file the read cannot find, is not compared:
the Store cannot say. The writer's certified head the page carries (`Head.behindCertified`, PROTOCOL-81)
is compared the same way: another chain there is `refused forkedCertified`. -/
def behindOr (keys : Keys) (files : PageFiles) (r : Resident (World D)) (posts : List (Head.Post D))
    (cert : Option (Nat × ByteArray)) (out : UInt8 × ByteArray) : IO (UInt8 × ByteArray) := do
  if posts.isEmpty && cert.isNone then return out
  let (k0, read, readIndex) ← files.readers
  let chainAt (s : Nat) : IO (Option ByteArray) := do
    try (·.toOption) <$> chainKept keys k0 read readIndex r s catch _ => pure none
  let chains ← posts.mapM fun p => do pure (p.steps, ← chainAt p.steps)
  let refuse (e : Command.Refusal D) : IO (UInt8 × ByteArray) :=
    match (Command.forkRefused (D := D) e).bytes with
    | some b => return (Status.ok.code, b)
    | none => return named Refusal.stepTooLarge.name
  match Head.forkedBehindPost posts (fun s => (chains.lookup s).join) with
  | some p => refuse (.forkedPost p.steps (X.env.bytes p.member))
  | none =>
  -- the writer's certified head behind follow's position (PROTOCOL-81): its own Store's chain there
  match cert with
  | none => return out
  | some (s, c) =>
    match ← chainAt s with
    | some c' => if c' = c then return out else refuse (.forkedCertified s)
    | none => return out

/-- The follower loop: one frame at a time, at most `fuel` frames. `dl` is follow's memory (the base
download in progress and the newest writer base it verified itself, PROTOCOL-47), held in memory only, in a reference the caller owns, so it survives a fuel restart's
in-process reopen exactly as the port's queued frames do (a process restart starts it again). Absorbed steps are appended through
`Host.append` BEFORE the step is answered; an adopted base is sealed as follow's own newest base
at its segment position (no record before it belongs to the adopted World's history, so the index
restarts empty: adopt runs only at genesis (PROTOCOL's `notAtGenesis`), where the index file is empty,
so the base counts no entry and the seal writes none) BEFORE the step is answered. -/
def loop (keys : Keys) (me : Command.Self D) (store : Store) (ck : Checkpoint (World D)) (files : PageFiles)
    (port : Port) (dl : IO.Ref Command.Memory) : Nat → Resident (World D) → IO (Exit × Resident (World D))
  | 0, r => finish .fuel r
  | fuel + 1, r => do
    let r ← match ← reap r with
      | .ok r => pure r
      | .error f => return (.sealFailed f, { r with pending := none })
    let some f ← port.recv | finish .eof r
    -- the version first (PROTOCOL-87): a command at another wire is refused by name, follow never reads it
    match wiredReply f with
    | .error reply =>
      port.send reply
      loop keys me store ck files port dl fuel r
    | .ok f =>
      let (fs', p, status, payload) :=
        answer X Codec.Deployed.digestCodec ⟨world, World.steps, keys.worldDigest, c.worldBytesMax⟩ me ⟨r.world, (← dl.get).download, (← dl.get).verified⟩ f
      -- follow's memory moves only once the step's effects are durable: `verified` never names a base
      -- the follower's own durable World has not crossed (PROTOCOL-47, HOST-12)
      -- the writer's certified head a log page carries, at or behind follow's position before the
      -- page (PROTOCOL-81): follow's own Store answers it, on an empty page too (the caught-up case)
      let cert := match resumeFrame.decode f.payload with
        | .ok (_, res, ()) => Head.behindCertified X r.world (Command.frameCertificate res.1)
        | .error _ => none
      match p with
      | .steps [] =>
        let (status, payload) ← behindOr keys files r [] cert (status, payload)
        dl.set fs'.memory
        port.send ⟨f.conn, status, payload⟩
        loop keys me store ck files port dl fuel { r with world := fs'.world }
      | .steps ts =>
        let (status, payload) ← behindOr keys files r (Head.behindPosts X r.world fs'.world ts) cert (status, payload)
        match ← append recorder keys.segment ck c store r fs'.world ts.toArray with
        | .error e =>
          port.send ⟨f.conn, Status.uncertain.code, ByteArray.empty⟩
          finish e r
        | .ok r =>
          dl.set fs'.memory
          port.send ⟨f.conn, status, payload⟩
          loop keys me store ck files port dl fuel r
      | .adopt w' =>
        let r ← match r.pending with
          | none => pure r
          | some pd => match ← settle pd with
            | .ok sealed => pure { r with sealed, pending := none }
            | .error e => return (.sealFailed e, { r with pending := none })
        match ← ck.adopt r.world w' r.pos with
        | .error e =>
          port.send ⟨f.conn, Status.uncertain.code, ByteArray.empty⟩
          return (.sealFailed e, { r with pending := none })
        | .ok (bytes, digest, ix) =>
          let sealed : Sealed := ⟨r.pos.offset, bytes, (recorder.mark w').1,
            (recorder.mark w').2, digest, ix⟩
          dl.set fs'.memory
          port.send ⟨f.conn, status, payload⟩
          loop keys me store ck files port dl fuel
            { r with world := w', sealed, index := #[], pending := none }

end Nanodregg.Host.Follow
