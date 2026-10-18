/-
# Protocol.Rows.Writer — HOST's loop, run in process for the member rows

The writer the rows drive is `Host.serve` (the deployed loop: group commit, the seal cadence,
whole-World bases) over the in-memory disk (`Host.Sim.memStore`, `Host.Sim.memCheckpoint`), on a
dedicated thread, fed through a channel port; it reopens with `Host.openWith` (one base, the tail
after it, `Host.Record.step` folding each batch record and asserting its chain). Generic in the
digest: the codecs and the sealers are the run's `Rows.Params` (the toy's FNV tags, or `host`'s
KMAC256 sealers at the deployed parameters); the cadence is small enough that the rows seal bases.

Every arm is HOST's: `log` is `Host.handle`'s (the read envelope checked against the World as the
batch advanced it) and its page is `Host.Page.build` over the in-memory segment (`pager`), the
same code `Host.Deployed.pager` runs over the segment file. The one deviation is a plant
(`Params.gateLog = false`).
-/
import Protocol.Rows.Params
import Protocol.Envelope
import Host.Serve
import Host.Loop
import Host.Open
import Host.Record
import Host.Sim.MemStore
import Host.Page

namespace Nanodregg.Protocol.Rows.Writer

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Protocol

variable {D : Type} [Ord D] [DecidableEq D]

/-- The writer's parameters, which a plant may mutate. -/
structure Params (D : Type) [Ord D] where
  /-- the run's parameters -/
  R : Rows.Params D
  /-- the writer's kernel parameters: `R.ctx`, or a plant's mutation of it -/
  X : Ctx D
  /-- serve `log` only to an envelope `Envelope.check` accepts (HOST's `handle`); `false` is the
  plant that answers a page to any envelope that decodes -/
  gateLog : Bool := true
  /-- reopen to a World whose journal is empty -/
  forgetJournal : Bool := false
  /-- every page states its own end as the tip (a plant: the writer hides the rest of its log) -/
  lieTip : Bool := false
  /-- `read` pages serve the newest base with one World byte flipped, stating the honest digest (a
  plant: a forged base) -/
  forgeBase : Bool := false
  /-- an `expired` refusal states the name alone, no height (a plant: the shape before
  PROTOCOL-19, which leaves a follower more than a window behind unable to catch up) -/
  unstatedExpiry : Bool := false
  /-- `log` serves an envelope the gate refuses `notYet` (a plant: the read gate without the
  envelope's lower bound, PROTOCOL-27) -/
  ignoreNotBefore : Bool := false
  /-- admit against the World with every spent nullifier forgotten (a plant: a writer that does
  not keep its spent set) -/
  forgetSpent : Bool := false
  /-- an `uncertain forgotten` reply is sent as `refused forgotten` (a plant: the status rule
  KERNEL-33 / PROTOCOL-6 fixed) -/
  forgottenRefused : Bool := false
  /-- commit a call whose transaction id holds a recorded refusal (judged on the World with the
  refusals forgotten) while answering it `refused NAME` (a plant: KERNEL-44's A→B→A defect, as a
  writer that lies to its client) -/
  admitsRecorded : Bool := false
  /-- every page states its TIP as the newest base, with the sealed base's digest (a plant: a
  writer that lies about where its base is, PROTOCOL-47) -/
  lieBase : Bool := false

/-- The run's seal threshold (`Rows.Params.sealMinBytes`); the deployed bounds on size. -/
def cadence (P : Params D) : Cadence :=
  { sealMinBytes := P.R.sealMinBytes, worldBytesMax := Cadence.deployed.worldBytesMax,
    recordBytesMax := Cadence.deployed.recordBytesMax }

def limits : Limits := ⟨16, 1 <<< 20⟩
/-- Batches one round of the loop serves before it ends `fuel` (`Host.restarts` reopens in process). -/
def fuel : Nat := 1000000

/-- The World with its spent nullifiers removed and its cells kept (the `writerForgetsSpent`
plant's view; the trie is rebuilt from the kept listing). -/
def unspend (E : Env D) (w : World D) : World D :=
  { w with trie := (w.trie.toList.filter fun p => match p.1 with
      | .cell _ => true
      | .nullifier _ => false).foldl (fun m p => m.insert (trieSpec E) p.1 p.2) .empty }

/-- The writer's step count and chain, as `Host.Recorder.mark` writes them (KERNEL-47). -/
def mark (P : Params D) (w : World D) : Nat × ByteArray := (w.steps, P.X.env.bytes w.chain)

/-- The `admitsRecorded` plant's submit: a call whose transaction id holds a recorded refusal is
admitted on the World with its refusals forgotten, the refusals are put back, and the client is
told the recorded name, status `refused`. `none` for any other frame. -/
def admitRecorded (X : Ctx D) (w : World D) (f : Frame) : Option (Answer (World D) (Kernel.Step D)) := do
  if f.op ≠ Op.submit.code then none
  let c ← X.decodeCall f.payload
  let code ← refusedAnswer X w c
  match submit X { w with refusals := .empty } c with
  | .ok (t, w') =>
      some (.commit (.turn t) { w' with refusals := w.refusals } Status.refused.code
        ((codeName code).getD "refusedFinal").toUTF8)
  | .error _ => none

/-- `Host.handle`, except under a plant: `openLog` pages a `log` envelope that decodes without
`Envelope.check`; `forgetSpent` judges a submit on the World with its spent set forgotten (and
keeps the World that reaches); `admitsRecorded` commits a recorded call. -/
def machine (P : Params D) : Machine (World D) (Kernel.Step D) Frame D where
  note := World.roots P.X.env
  handle w f :=
    if !P.gateLog && f.op = Op.log.code then
      match Envelope.ofBytes P.X f.payload with
      | some e => .defer (.log e.start)
      | none => Host.handle P.X w f
    else if P.ignoreNotBefore && f.op = Op.log.code then
      match Envelope.ofBytes P.X f.payload with
      | some e => match Envelope.check P.X w e with
        | .error .notYet => .defer (.log e.start)
        | _ => Host.handle P.X w f
      | none => Host.handle P.X w f
    else if P.forgetSpent && f.op = Op.submit.code then Host.handle P.X (unspend P.X.env w) f
    else match (if P.admitsRecorded then admitRecorded P.X w f else none) with
    | some a => a
    | none =>
    match Host.handle P.X w f with
      | .reply c p =>
        if P.unstatedExpiry && (expiredHeight? p).isSome then .reply c "expired".toUTF8
        else if P.forgottenRefused && c = Status.uncertain.code && p = "forgotten".toUTF8 then
          .reply Status.refused.code p
        else .reply c p
      | a => a
  ok := Status.ok.code

/-- The Store in memory: the segment and the base file. -/
structure Mem where
  disk : IO.Ref Host.Sim.Disk
  bases : IO.Ref Host.Sim.Bases

/-- HOST's in-memory checkpoint (its entries tagged for the Store of the World it seals, HOST-33). -/
def checkpoint (P : Params D) (m : Mem) : Checkpoint (World D) :=
  Host.Sim.memCheckpoint m.disk m.bases P.R.keys (cadence P) P.R.world
    (fun w => P.X.env.bytes (World.genesisChain P.X.env w.origin))

/-- HOST's pager (`Host.Page.build` + `Host.Page.bytes`) over the in-memory segment's synced bytes
and `index.log` (`Host.Page.entryAt`): what `Host.Deployed.pager` does over the files. -/
def pager (P : Params D) (m : Mem) (r : Resident (World D)) : Deferred → IO (UInt8 × ByteArray)
  | .read start => do
    if !P.forgeBase then Host.Sim.memBasePage Page.budget m.bases r start else
    -- the World bytes follow the base frame's 4-byte length; flip one in the middle
    let file := Host.Sim.flipByte (← m.bases.get).file (4 + r.sealed.bytes / 2)
    match Id.run (Page.basePage Page.budget (fun off len => pure (file.extract off (off + len))) r.sealed start) with
    | .ok b => pure (Status.ok.code, b)
    | .error f => pure (Status.refused.code, f.name.toUTF8)
  | .log start => do
  let seg := (← m.disk.get).synced
  let idx := (← m.bases.get).index
  let X := P.X
  match Id.run (Page.build X.env P.R.dc X.digestOf P.R.keys.segment (cadence P).recordBytesMax
      P.R.pageBudget (fun off len => pure (seg.extract off (off + len)))
      (Page.entryAt (P.R.keys.forStore (X.env.bytes (World.genesisChain X.env r.world.origin)))
        (fun off len => pure (idx.extract off (off + len))) r.sealed.index.count r.index)
      (r.sealed.index.count + r.index.size) r.pos.offset
      (r.world.steps, X.env.bytes r.world.chain) start) with
  | .error f => pure (Status.refused.code, f.name.toUTF8)
  | .ok a =>
    -- `lieTip` hides the log after the page, so a base after the page too (a consistent lie)
    let baseSteps := if P.lieBase then r.world.steps
      else if P.lieTip then min r.sealed.steps a.steps else r.sealed.steps
    match Page.bytes a (if P.lieTip then a.steps else r.world.steps) r.world.height baseSteps r.sealed.digest with
    | .ok b => pure (Status.ok.code, b)
    | .error f => pure (Status.refused.code, f.name.toUTF8)

/-- A Store as genesis leaves it (HOST's `memGenesis`: the origin frame, the base after it), and
the loop's state the one open gives over it. -/
def genesisStore (P : Params D) (g : World D) : IO (Except String (Mem × Resident (World D))) := do
  match Host.Sim.memGenesis P.R.keys (cadence P) P.R.world (mark P)
      (fun w => P.X.env.bytes (World.genesisChain P.X.env w.origin))
      (Record.step P.R.dc (World.step P.X.env) (World.roots P.X.env)) g with
  | .error f => return .error f.name
  | .ok (d, b, r) => return .ok (⟨← IO.mkRef d, ← IO.mkRef b⟩, r)

/-- The one open over the in-memory Store: HOST's `openWith`, the writer's fold. -/
def reopen (P : Params D) (index base seg : ByteArray) : Except String (Resident (World D)) :=
  match Id.run (openWith P.R.keys (cadence P) P.R.world (mark P)
      (fun w => P.X.env.bytes (World.genesisChain P.X.env w.origin))
      (Record.step P.R.dc (World.step P.X.env) (World.roots P.X.env))
      base seg.size index.size (fun off len => pure (.ok (index.extract off (off + len))))
      fun off len => pure (.ok (seg.extract off (off + len)))) with
  | .error f => .error f.name
  | .ok o =>
      let w := if P.forgetJournal then { o.opened.world with journal := .empty } else o.opened.world
      .ok { world := w, pos := o.pos, sealed := o.sealed,
            index := o.index }

/-- A loop running on its own thread. -/
structure Running (D : Type) [Ord D] where
  reqs : Std.CloseableChannel.Sync Frame
  reps : Std.CloseableChannel.Sync Host.Reply
  task : Task (Except IO.Error (Exit × Resident (World D)))

def start (P : Params D) (m : Mem) (r : Resident (World D)) : IO (Running D) := do
  let reqs ← Std.CloseableChannel.Sync.new
  let reps ← Std.CloseableChannel.Sync.new
  let port := channelPort reqs (← IO.mkRef none) fun r => do discard <| (reps.send r).toBaseIO
  let task ← IO.asTask (prio := .dedicated) do
    try
      serve (machine P) ⟨fun _ ts => Record.encode P.R.dc ts, mark P⟩ P.R.keys.segment
        (checkpoint P m) (cadence P) (Host.Sim.memStore m.disk none) (pager P m)
        port limits fuel r
    finally
      discard <| (reps.close).toBaseIO
  pure ⟨reqs, reps, task⟩

/-- One request and its reply; `none` once the loop has stopped. -/
def Running.ask (h : Running D) (f : Frame) : IO (Option Host.Reply) := do
  match ← (h.reqs.send f).toBaseIO with
  | .error _ => pure none
  | .ok () => h.reps.recv

/-- Stop the loop at a frame boundary; why it stopped and its last state. -/
def Running.stop (h : Running D) : IO (Except String (Exit × Resident (World D))) := do
  discard <| (h.reqs.close).toBaseIO
  match ← IO.wait h.task with
  | .ok r => pure (.ok r)
  | .error e => pure (.error (toString e))

end Nanodregg.Protocol.Rows.Writer
