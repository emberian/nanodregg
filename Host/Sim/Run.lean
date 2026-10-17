/-
# Host.Sim.Run — the loop end to end, and the crash plants

`Nanodregg.Host.Sim.run [seed]` drives `serve` (the deployed loop) over the
in-memory disk with toy parameters, admitting every Turn through `Kernel.World.admit`, and checks:

1. one reply per request; a resend of the same txId (the same bytes, or other bytes under it:
   a txId is the digest of the signed call, KERNEL-7) answers `ok` with the original receipt and
   admits nothing; double spends answer `refused`;
2. `recover` of the disk is `clean`, and `World.fold` of the recovered records from genesis
   reaches the loop's World (height and chain);
3. a different seeded batch split reaches the same chain;
4. plant-fsync-fail: the 4th sync throws; the batch's replies are all `uncertain`; the loop stops;
   for every crash cut of the unsynced frame, `recover` returns the synced batches (and the
   failed batch only if all its bytes are there), `torn` with the cut length otherwise;
5. plant-flip-byte / plant-flip-header: a flipped byte in the first frame (body or length) of a
   multi-frame segment is `corrupt`; plant-flip-last-frame: a flip in the last frame reads as
   `torn` (the one case no format can decide; DESIGN §4).

Returns 0 iff every check holds; each failure prints `FAIL <name>`. `lake exe host-sim SEED`
(`Host.Sim.Main`) is the exe; standing runs seeds 1 2 3.
-/
import Host.Sim.MemStore
import Host.Sim.Toy
import Kernel.World
import Host.Open

namespace Nanodregg.Host.Sim

open Nanodregg.Kernel

/-- A deterministic generator (64-bit LCG). -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def receipt (h d : Nat) : ByteArray := le64 h ++ le64 d

def machine : Machine (World Nat) (Turn Nat) (Reject Nat) Frame where
  admit := World.admit env
  handle _ f :=
    match decodeRecord f.payload with
    | some [t] => .admit t fun w' => receipt w'.height (turnDigest env t)
    | _ => .reply Protocol.Status.refused.code "malformed".toUTF8
  refuse w t r :=
    match r with
    | .replayed h => match w.journal[t.txId]? with
      | some (_, d) => (Protocol.Status.ok.code, receipt h d)
      | none => (Protocol.Status.refused.code, (toString (repr r)).toUTF8)
    | _ => (Protocol.Status.refused.code, (toString (repr r)).toUTF8)
  ok := Protocol.Status.ok.code

def genesis : World Nat := World.genesis env "sim".toUTF8 (2 ^ 40)

inductive Kind | fresh | replay | sameTxId | doubleSpend
  deriving DecidableEq

/-- `n` requests from a seed: each a fresh turn, an exact replay, other bytes under a used txId, or a double spend. -/
def scenario (seed n : Nat) : List (Frame × Kind) :=
  (go n seed [] []).reverse
where
  go : Nat → Nat → List (Turn Nat) → List (Frame × Kind) → List (Frame × Kind)
    | 0, _, _, acc => acc
    | k + 1, s, made, acc =>
      let s' := lcg s
      let i := acc.length
      let pick := (s' / 65536) % 10
      let (t, kind) :=
        match made with
        | [] => (mkTurn (1000 + i) 0 1024 [5000 + i], Kind.fresh)
        | m :: _ =>
          if pick < 7 then (mkTurn (1000 + i) 0 1024 [5000 + i], .fresh)
          else if pick < 8 then (m, .replay)
          else if pick < 9 then (mkTurn m.txId 0 1024 [9000 + i], .sameTxId)
          else (mkTurn (1000 + i) 0 1024 m.nullifiers, .doubleSpend)
      let f : Frame := ⟨UInt32.ofNat i, Protocol.Op.submit.code, record genesis #[t]⟩
      go k s' (if kind = .fresh then t :: made else made) ((f, kind) :: acc)

/-- Seeded batch boundaries: `true` = the next frame is already queued. -/
def splits (seed n : Nat) : List Bool :=
  (List.range n).foldl (fun (s, acc) _ => let s' := lcg s; (s', ((s' / 4096) % 3 != 0) :: acc))
    (seed, []) |>.2.reverse

structure RunResult where
  exit : Exit
  world : World Nat
  replies : Array Reply
  disk : Disk

/-- Serve `frames` from a disk and the World/tag the disk opened to. -/
def serveFrom (seed : Nat) (frames : List Frame) (failSyncAt : Option Nat) (d : Disk) (w : World Nat)
    (tag : ByteArray) : IO RunResult := do
  let disk ← IO.mkRef d
  let fr ← IO.mkRef frames
  let sp ← IO.mkRef (splits seed frames.length)
  let sent ← IO.mkRef #[]
  let (exit, w) ← serve machine ⟨record⟩ sealer (memStore disk failSyncAt) (scriptPort fr sp sent)
    ⟨16, 1 <<< 20⟩ (frames.length + 1) w tag none
  return ⟨exit, w, ← sent.get, ← disk.get⟩

def initialTag : ByteArray := ByteArray.empty

def runOnce (seed : Nat) (frames : List Frame) (failSyncAt : Option Nat) : IO RunResult :=
  serveFrom seed frames failSyncAt {} genesis initialTag

/-- One batch record folded into the World: what open does per record. -/
def foldStep (w : World Nat) (r : ByteArray) : Except String (World Nat) :=
  match decodeRecord r with
  | none => .error "undecodable"
  | some ts => match World.fold env w ts with
    | .ok w' => .ok w'
    | .error (i, rj) => .error s!"turn {i}: {repr rj}"

/-- Open a disk image from genesis: the deployed `openLog`. -/
def reopen (bytes : ByteArray) : Except (OpenFault String) (Opened (World Nat)) :=
  openLog sealer bodyMax foldStep genesis initialTag bytes

def isCorrupt (r : Except (OpenFault String) (Opened (World Nat))) (off : Nat) : Bool :=
  match r with
  | .error (.corrupt o) => o = off
  | _ => false

/-- `a / b` to three decimals, as standing's waste gate reads it (`b = 0` prints the numerator). -/
def ratio (a b : Nat) : String :=
  if b = 0 then toString a else
  let m := (a * 1000 + b / 2) / b
  let frac := toString (m % 1000)
  s!"{m / 1000}.{"".pushn '0' (3 - frac.length)}{frac}"

def check (name : String) (ok : Bool) (failures : IO.Ref Nat) : IO Unit := do
  if ok then IO.println s!"PASS {name}" else
    IO.println s!"FAIL {name}"; failures.modify (· + 1)

def run (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 1
  let failures ← IO.mkRef 0
  let sc := scenario seed 200
  let frames := sc.map (·.1)
  let r ← runOnce seed frames none
  let statusOf (k : Kind) := sc.zip r.replies.toList |>.filter (·.1.2 = k) |>.map (·.2.status)
  check "one reply per request" (r.replies.size = 200) failures
  check "loop ended at eof" (match r.exit with | .eof => true | _ => false) failures
  check "fresh turns admitted" ((statusOf .fresh).all (· = Protocol.Status.ok.code)) failures
  check "replays answered ok" ((statusOf .replay).all (· = Protocol.Status.ok.code)) failures
  check "a used txId answers ok, admitting nothing" ((statusOf .sameTxId).all (· = Protocol.Status.ok.code)) failures
  check "double spends refused" ((statusOf .doubleSpend).all (· = Protocol.Status.refused.code)) failures
  check "height = fresh turns" (r.world.height = (statusOf .fresh).length) failures
  IO.println s!"admitted {r.world.height} turns in {r.disk.syncs} batches, {r.disk.synced.size} bytes"
  let opened := reopen r.disk.synced
  check "open clean: the whole image, no torn tail"
    (match opened with | .ok o => o.torn = 0 ∧ o.validLen = r.disk.synced.size | .error _ => false) failures
  check "open = loop World (height, chain)"
    (match opened with | .ok o => o.world.height = r.world.height ∧ o.world.chain = r.world.chain | .error _ => false)
    failures
  -- waste (law 5): work done ÷ work the operation must do
  let records := (Log.recover sealer bodyMax initialTag r.disk.synced).records
  let admittedBytes := ((records.mapM decodeRecord).getD []).flatten.foldl (fun n t => n + (turnBytes t).size) 0
  IO.println s!"WASTE submit bytes-per-turn {ratio r.disk.synced.size admittedBytes}"
  IO.println s!"WASTE submit fsyncs-per-batch {ratio r.disk.syncs records.length}"
  IO.println s!"WASTE open bytes-read-per-record {ratio r.disk.synced.size (match opened with | .ok o => o.validLen | .error _ => 0)}"
  let r2 ← runOnce (seed + 7919) frames none
  IO.println s!"second split: {r2.disk.syncs} batches"
  check "a different batch split reaches the same chain" (r2.world.chain = r.world.chain) failures
  -- plant-fsync-fail, then plant-restart-at-every-cut
  let p ← runOnce seed frames (some 3)
  let pendingSize := p.disk.pending.size
  check "plant-fsync-fail: loop stops uncertain"
    (match p.exit with | .uncertain _ => true | _ => false) failures
  let uncertainN := (p.replies.toList.filter (·.status = Protocol.Status.uncertain.code)).length
  let lastBatch := p.replies.toList.drop (p.replies.size - uncertainN)
  check "plant-fsync-fail: the batch's replies are uncertain"
    (0 < uncertainN ∧ lastBatch.all (·.status = Protocol.Status.uncertain.code) ∧ pendingSize > 0) failures
  let baseRecords := match reopen p.disk.synced with | .ok o => o.records | .error _ => 0
  check "plant-fsync-fail: synced prefix opens" (baseRecords = 3) failures
  -- every crash cut of the unsynced frame: open (truncating the torn tail, as the writer does),
  -- resend the uncertain batch and the rest, and reach the no-crash chain.
  let resend := frames.drop (p.replies.size - uncertainN)
  let mut cutsOk := true
  for cut in List.range (pendingSize + 1) do
    match reopen (crashImage p.disk cut) with
    | .error e =>
      cutsOk := false; IO.println s!"  cut {cut}: open refused {repr e}"
    | .ok o =>
      let expectTorn := if cut = pendingSize then 0 else cut
      let expectRecords := if cut = pendingSize then baseRecords + 1 else baseRecords
      let img := (crashImage p.disk cut).extract 0 o.validLen
      let q ← serveFrom seed resend none { synced := img } o.world o.lastTag
      let reopened := reopen q.disk.synced
      let finalOk : Bool := match reopened with
        | .ok o' => decide (o'.torn = 0 ∧ o'.world.chain = r.world.chain ∧ q.world.chain = r.world.chain)
        | .error _ => false
      unless decide (o.torn = expectTorn ∧ o.records = expectRecords) && finalOk do
        cutsOk := false
        IO.println s!"  cut {cut}: torn {o.torn} records {o.records} final {finalOk}"
  check s!"plant-restart-at-every-cut 0..{pendingSize}: open, truncate, resend, reach the no-crash chain" cutsOk failures
  -- plant-flip-byte
  check "plant-flip-byte: corrupt" (isCorrupt (reopen (flipByte r.disk.synced 6)) 0) failures
  check "plant-flip-header: corrupt (the frames after it are found by the forward scan)"
    (isCorrupt (reopen (flipByte r.disk.synced 0)) 0) failures
  let fullRecords := match opened with | .ok o => o.records | .error _ => 0
  check "plant-flip-last-frame: torn (the stated undecidable case: one frame lost, loudly)"
    (match reopen (flipByte r.disk.synced (r.disk.synced.size - 1)) with
     | .ok o => 0 < o.torn ∧ o.records + 1 = fullRecords
     | .error _ => false) failures
  let n ← failures.get
  IO.println (if n = 0 then "ALL PASS" else s!"{n} FAILED")
  return (if n = 0 then 0 else 1)

end Nanodregg.Host.Sim
