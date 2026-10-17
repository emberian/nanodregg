/-
# Host.Sim.File — the loop over a real Store directory (Host.Store, Host/c/file.c)

`run [seed]`, in a fresh temporary directory it removes afterwards:
1. `openWriter` on an empty Store opens to genesis; the seeded scenario is served through
   `fileStore` (real `write` + `F_FULLFSYNC`/`fdatasync`);
2. plant-second-writer: while the first writer lives, a second `openWriter` is refused `locked`;
3. plant-torn-file: half of one more frame is appended behind the writer's back (a crash
   mid-write); `openFollower` reports it torn and leaves the file as it is; `openWriter` truncates
   it, and the World it opens has the loop's height and chain; a third open is clean.
Prints `FAIL <check>` per failure and `ALL PASS` when none.
-/
import Host.Store
import Host.Sim.Run

namespace Nanodregg.Host.Sim.File

open Nanodregg.Kernel Nanodregg.Host.Sim

/-- Serve `frames` as the writer of `dir`; return what the loop holds. The writer (and its lock)
is released when this returns. -/
def serveDir (dir : System.FilePath) (seed : Nat) (frames : List Frame) :
    IO (Except String (World Nat × ByteArray × Bool)) := do
  match ← openWriter dir sealer bodyMax foldStep genesis initialTag with
  | .error e => return .error s!"open: {repr e}"
  | .ok wr =>
    let fr ← IO.mkRef frames
    let sp ← IO.mkRef (splits seed frames.length)
    let sent ← IO.mkRef #[]
    let (_, w) ← serve machine ⟨record⟩ sealer (fileStore wr.segment) (scriptPort fr sp sent)
      ⟨16, 1 <<< 20⟩ (frames.length + 1) wr.opened.world wr.opened.lastTag none
    let second ← openWriter dir sealer bodyMax foldStep genesis initialTag
    let refused := match second with | .error .locked => true | _ => false
    wr.segment.sync  -- the writer's handle (and so its lock) is alive up to here
    let tag := (Log.recover sealer bodyMax initialTag (← readBytes dir)).lastTag
    return .ok (w, tag, refused)
where
  readBytes (dir : System.FilePath) : IO ByteArray := do
    match ← (readSegment dir : IO (Except (StoreFault String) ByteArray)) with
    | .ok b => pure b
    | .error _ => pure ByteArray.empty

def run (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 1
  let failures ← IO.mkRef 0
  let frames := (scenario seed 200).map (·.1)
  IO.FS.withTempDir fun dir => do
    match ← serveDir dir seed frames with
    | .error e => check s!"writer opens an empty Store ({e})" false failures
    | .ok (w, tag, refused) =>
      check "writer opens an empty Store and serves the scenario" (0 < w.height) failures
      check "plant-second-writer: refused `locked` while the first lives" refused failures
      -- a crash mid-write: half of one more frame
      let extra := Log.frame sealer tag (record w #[mkTurn 77777 0 1024 [77777]])
      let half := extra.extract 0 (extra.size / 2)
      let f ← File.open (segmentPath dir) .append
      f.writeAll half
      f.sync
      let before ← (File.open (segmentPath dir) .read >>= File.size)
      match ← openFollower dir sealer bodyMax foldStep genesis initialTag with
      | .error e => check s!"plant-torn-file: follower opens ({repr e})" false failures
      | .ok o =>
        let after ← (File.open (segmentPath dir) .read >>= File.size)
        check "plant-torn-file: follower sees the torn tail and truncates nothing"
          (o.torn = half.size ∧ before = after ∧ o.world.chain = w.chain) failures
      match ← openWriter dir sealer bodyMax foldStep genesis initialTag with
      | .error e => check s!"plant-torn-file: writer opens ({repr e})" false failures
      | .ok wr =>
        let size ← (File.open (segmentPath dir) .read >>= File.size)
        check "plant-torn-file: writer truncates the torn tail; World = the loop's"
          (wr.opened.torn = half.size ∧ size.toNat = wr.opened.validLen ∧
            wr.opened.world.height = w.height ∧ wr.opened.world.chain = w.chain) failures
      match ← openFollower dir sealer bodyMax foldStep genesis initialTag with
      | .ok o => check "reopen after truncation is clean" (o.torn = 0 ∧ o.world.chain = w.chain) failures
      | .error e => check s!"reopen after truncation ({repr e})" false failures
  let n ← failures.get
  IO.println (if n = 0 then "ALL PASS" else s!"{n} FAILED")
  return (if n = 0 then 0 else 1)

end Nanodregg.Host.Sim.File
