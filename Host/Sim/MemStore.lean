/-
# Host.Sim.MemStore — an in-memory disk for the loop, with the crash plants

`synced` is what survived the last successful `sync`; `pending` is appended since. A crash keeps
`synced` plus any prefix of `pending` (`crashImage cut`). The plants are a property of this disk,
not code in the loop: `failSyncAt n` makes the n-th sync throw (the loop must answer the batch
`uncertain` and stop), and `crashImage` / `flipByte` produce the bytes `recover` must judge.
-/
import Host.Loop
import Host.Open
import Host.Page

namespace Nanodregg.Host.Sim

structure Disk where
  synced : ByteArray := ByteArray.empty
  pending : ByteArray := ByteArray.empty
  syncs : Nat := 0

/-- A store over a disk reference; `failSyncAt n`: the `n`-th sync (0-based) fails with EIO. -/
def memStore (disk : IO.Ref Disk) (failSyncAt : Option Nat) : Store where
  append bytes := disk.modify fun d => { d with pending := d.pending ++ bytes }
  sync := do
    let d ← disk.get
    if failSyncAt = some d.syncs then
      disk.set { d with syncs := d.syncs + 1 }
      throw (IO.userError "plant: fsync EIO")
    disk.set { synced := d.synced ++ d.pending, pending := ByteArray.empty, syncs := d.syncs + 1 }

/-- What a crash leaves: the synced bytes and the first `cut` unsynced ones. -/
def crashImage (d : Disk) (cut : Nat) : ByteArray :=
  d.synced ++ d.pending.extract 0 cut

/-- The base "file" of an in-memory Store, and every base it ever held: each with the synced
segment size at the moment it became durable (what a crash just before the NEXT base's rename
leaves on disk). -/
structure Bases where
  file : ByteArray := ByteArray.empty
  history : Array (ByteArray × Nat) := #[]
  /-- the Store's `index.log`: every entry a seal appended (HOST-30, HOST-33) -/
  index : ByteArray := ByteArray.empty
  /-- `index.log`'s size when each base of `history` became durable -/
  indexAt : Array Nat := #[]
  /-- bytes written by seals, pages and bases (the waste numerator) -/
  written : Nat := 0
  /-- index entries handed to seals (law 5: each entry is handed once, HOST-30) -/
  handed : Nat := 0

/-- A checkpoint over memory: the deployed `Base.file`, then an atomic replace. Inline, so a seeded
run seals at the same points every time. -/
def memCheckpoint {W : Type} (disk : IO.Ref Disk) (bases : IO.Ref Bases) (keys : Keys) (c : Cadence)
    (world : Codec.Stream W) (origin : W → ByteArray) : Checkpoint W where
  async := false
  write w seg entries ipos := do
    match Base.seal (keys.forStore (origin w)) c world w seg ipos entries (← bases.get).index.size with
    | .error f => return .error f
    | .ok (page, ipos', file) =>
      let synced := (← disk.get).synced.size
      bases.modify fun b =>
        { file, history := b.history.push (file, synced), index := b.index ++ page,
          indexAt := b.indexAt.push (b.index.size + page.size), written := b.written + page.size + file.size,
          handed := b.handed + entries.size }
      return .ok (world.size w, keys.worldDigest (worldBytesOf file (world.size w)), ipos')

/-- An in-memory Store as genesis leaves it: `genesisImage`'s segment (synced) and base, and the
loop's state as the one open (`openWith`, with the caller's own fold step) reads them back. The
start state is therefore never built by hand. -/
def memGenesis {W F : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W) (w₀ : W) :
    Except (StoreFault F) (Disk × Bases × Resident W) :=
  match genesisImage keys c world mark w₀ with
  | .error f => .error (.seal f)
  | .ok img =>
    match Id.run (openWith keys c world mark origin step img.base img.segment.size img.index.size
        (fun off len => pure (.ok (img.index.extract off (off + len))))
        fun off len => pure (.ok (img.segment.extract off (off + len)))) with
    | .error f => .error f
    | .ok o =>
      let b : Bases := { file := img.base, history := #[(img.base, img.segment.size)], index := img.index, indexAt := #[img.index.size] }
      .ok ({ synced := img.segment }, b,
        { world := o.opened.world, pos := o.pos, sealed := o.sealed, index := o.index })

/-- A `read` page over the in-memory base (`Host.Page.basePage`, what `Host.Deployed.pager` does
over base.world). -/
def memBasePage {W : Type} (budget : Nat) (bases : IO.Ref Bases) (r : Resident W) (start : Nat) :
    IO (UInt8 × ByteArray) := do
  let file := (← bases.get).file
  match Id.run (Page.basePage budget (fun off len => pure (file.extract off (off + len))) r.sealed start) with
  | .ok b => return (Protocol.Status.ok.code, b)
  | .error f => return (Protocol.Status.refused.code, f.name.toUTF8)

/-- Flip one byte (xor 0x01) at `i`; out of range leaves the bytes unchanged. -/
def flipByte (b : ByteArray) (i : Nat) : ByteArray :=
  if h : i < b.size then b.set i (b[i] ^^^ 1) h else b

/-- A port that serves a fixed list of frames; `split` decides, per frame after the first of a
batch, whether it is already queued (the seeded batch boundaries). -/
def scriptPort (frames : IO.Ref (List Frame)) (split : IO.Ref (List Bool))
    (sent : IO.Ref (Array Reply)) : Port where
  recv := do
    match ← frames.get with
    | [] => pure none
    | f :: rest => frames.set rest; pure (some f)
  poll := do
    let queued ← match ← split.get with
      | [] => pure true
      | b :: rest => split.set rest; pure b
    if !queued then return none
    match ← frames.get with
    | [] => pure none
    | f :: rest => frames.set rest; pure (some f)
  unread f := frames.modify (f :: ·)
  send r := sent.modify (·.push r)
  close := pure ()

end Nanodregg.Host.Sim
