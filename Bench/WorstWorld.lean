/-
# Bench.WorstWorld — THE BAR's reopen at the worst World (PERF-8, ROOT 2026-10-18)

`worldBytesMax` is the READER's bound: a base FILE may hold any World up to it, whatever the genesis
allowance (which binds an honest history far below it: a create's bytes are paid three times, event,
logged creates and growth). So the reopen's worst World is an adversarially sized base, not an honest
history. Two modes, both on the deployed path (`Host.genesis`'s seal and MAC, `openFollower`):

- `bench-worstworld SCRATCH synthetic N [--harness-control]` (the standing row, N = 200000):
  N tombstones (the smallest cell entry: an id and a tag) at uniformly hashed ids are put in the
  genesis World's cells trie, written as a Store's base and reopened. The reopen's World must be the
  one written (its roots), and the base decode is counted under countingEnv: trie hashes per entry,
  which is scale-free (2·entries − 1 at 200k, at the bound, PERF-10, and past it at 2^28, PERF-8). Prints that,
  `WASTE worstworld decode-trie-hashes-per-entry R`, and the total DERIVED at worldBytesMax (the
  entries a base of that size holds at this run's bytes per entry, times R), beside it.
- `bench-worstworld SCRATCH honest [STATE_BYTES] [--harness-control]` (by hand, RUNBOOK; minutes):
  one founder births data objects of STATE_BYTES (default 60000) until `submit` refuses (the
  allowance binds) or a seal refuses; the final base is reopened, folded counted, and decoded counted.

`--harness-control` (either mode): the reopen's World must equal the written one with its roots'
first byte flipped, which nothing meets: `FAIL harness-control …`, judged where the real check is.
Clock lines are reported, never gated.
-/
import Bench.WorstCut

namespace Nanodregg.Bench.WorstWorld

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Host.Deployed
open Nanodregg.Bench.Count (captured marks ratio countingX auditRecord)
open Nanodregg.Bench.WorstCut

/-- `want` against the reopen's roots (`control`: against them with the first byte flipped). -/
def rootsMatch (got want : D) (control : Bool) : Bool :=
  if control then
    let b := want.bytes
    got.bytes == b.set! 0 (b.get! 0 ^^^ 1)
  else got.toHex == want.toHex

/-- The base decode counted: `w` encoded by the deployed codec and decoded by the same codec over
countingEnv (the bytes reach the decode through a Ref, so it runs inside the capture); it must reach
`w`'s roots. Its trie hashes, the bytes, and `w`'s trie entries. -/
def countDecode (w : World D) (control : Bool) : IO (Except String (Nat × Nat × Nat)) := do
  let src ← IO.mkRef (world.bytes w)
  let countingWorld := Codec.Kernel.world (Kernel.Sim.Gen.countingEnv X.env) Codec.Deployed.digestCodec
  let (dec, derr) ← captured (do
    let bytes ← src.get
    match countingWorld.decode bytes with
    | .ok w2 => pure (some (World.roots X.env w2, bytes.size))
    | .error _ => pure none)
  let some (droots, dbytes) := dec | return .error "the counted decode refused the base World"
  unless rootsMatch droots (World.roots X.env w) control do
    return .error (if control then "harness-control: the decoded roots are not the planted ones"
      else "the counted decode reached another World")
  return .ok (marks derr '#', dbytes, w.trie.toList.length)

def honest (scratch : System.FilePath) (stateBytes : Nat) (control : Bool) : IO UInt32 := do
  IO.FS.createDirAll scratch
  let dir := scratch / "world"
  if ← dir.pathExists then return ← fail s!"{dir} exists (SCRATCH must be fresh)"
  let g ← match Receive.genesis X "worstworld".toUTF8 "worstworld-nonce".toUTF8 allowanceMax founders with
    | .ok g => pure g
    | .error r => return ← fail s!"genesis {r.name}"
  let m := Who.of ⟨founderId X g.origin 0, founderSecret, nextSecret⟩
  let some key := Codec.Digest.ofBytes? (← IO.getRandomBytes 32) | return ← fail "getRandomBytes"
  let keys := Keys.ofKey key shapes
  if let .error f ← (Host.genesis dir key keys c world recorder.mark g : IO (Except (StoreFault (Record.Fault (Reject D))) Unit)) then
    return ← fail s!"Host.genesis {f.text}"
  let t0 ← IO.monoMsNow
  let mut w := g
  let mut births := 0
  let mut seals := 0
  let mut bound : Option String := none
  let payload (i : Nat) : ByteArray :=
    let n := Kernel.Sim.Gen.nat i
    n ++ ByteArray.mk (Array.replicate (stateBytes - n.size) 0x5a)
  -- a bound on the rounds, never reached: each round fills one tail (or ends at the bound)
  for _ in [0:4096] do
    if bound.isSome then break
    let wr ← match ← openWriter dir keys c world recorder.mark originChain foldStep with
      | .ok wr => pure wr
      | .error f => return ← fail s!"open {f.text}"
    let mut pos := wr.opening.pos
    let mut full := false
    for _ in [0:1 <<< 20] do
      if full || bound.isSome then break
      let mut staged : Array (Step D × D) := #[]
      let mut w' := w
      let mut n := 0
      for _ in [0:recordTurnsMax] do
        if bound.isSome then break
        match admit w' (call w' m [m.id] (.create none [] [(stateBase, payload (births + n))])) with
        | .ok (s, w'') => staged := staged.push s; w' := w''; n := n + 1
        | .error e => bound := some e
      if staged.isEmpty then break
      match ← commit wr.opening.sealed wr.segment keys pos staged with
      | .ok (some p) => pos := p; w := w'; births := births + n
      | .ok none => full := true; bound := none
      | .error e => return ← fail s!"commit {e}"
    wr.segment.sync
    match ← sealBase dir keys with
    | .ok _ => seals := seals + 1
    | .error e => bound := some s!"seal: {e}"
  let t1 ← IO.monoMsNow
  let some why := bound | return ← fail "the World never reached a bound within the loop's rounds"
  let host ← match ← openWith dir keys foldStep with
    | .ok o => pure o
    | .error e => return ← fail s!"reopen {e}"
  let t2 ← IO.monoMsNow
  let foldCounted : World D → ByteArray → Except (Record.Fault (Reject D)) (World D) :=
    Record.step Codec.Deployed.digestCodec (World.step countingX.env) (World.roots countingX.env)
  let (ro, rerr) ← captured (openWith dir keys foldCounted)
  let t3 ← IO.monoMsNow
  let some _ := ro.toOption | return ← fail "counted reopen refused"
  let sealed := host.sealed
  let (dh, dbytes, entries) ← match ← countDecode host.opened.world control with
    | .ok x => pure x
    | .error e => return ← fail e
  IO.println s!"WORSTWORLD base decode {dbytes} bytes, {entries} trie entries, trie-hashes {dh} ({ratio dh entries} per entry)"
  IO.println s!"WORSTWORLD births {births} of {stateBytes} state bytes, seals {seals}, bound: {why}"
  IO.println s!"WORSTWORLD base step {sealed.steps}, base world bytes {sealed.bytes} of worldBytesMax {c.worldBytesMax} ({ratio sealed.bytes c.worldBytesMax}), weight {World.weight w}, allowance left {w.allowance} of {allowanceMax}, world bytes per weight {ratio sealed.bytes (World.weight w)}"
  IO.println s!"WORSTWORLD tail past the base {host.pos.offset - sealed.offset} bytes, {host.opened.world.steps - sealed.steps} steps; reopen trie-hashes {marks rerr '#'} verifies {marks rerr '@'}"
  IO.println s!"WORSTWORLD clock (reported, never gated): build {t1 - t0} ms, reopen {t2 - t1} ms, counted reopen {t3 - t2} ms"
  IO.println "BENCH-WORSTWORLD PASS"
  return 0

/-- The synthetic reader-bound base (the module doc). -/
def synthetic (scratch : System.FilePath) (n : Nat) (control : Bool) : IO UInt32 := do
  if n = 0 then return ← fail "synthetic needs N > 0"
  IO.FS.createDirAll scratch
  let dir := scratch / "synthetic"
  if ← dir.pathExists then return ← fail s!"{dir} exists (SCRATCH must be fresh)"
  let g ← match Receive.genesis X "worstworld".toUTF8 "worstworld-nonce".toUTF8 allowanceMax founders with
    | .ok g => pure g
    | .error r => return ← fail s!"genesis {r.name}"
  let t0 ← IO.monoMsNow
  let mut trie := g.trie
  for i in [0:n] do
    trie := trie.insert (trieSpec X.env) (.cell (X.env.hash "perf/worstworld-id" (Kernel.Sim.Gen.nat i))) (.entry .tomb)
  let w := { g with trie }
  let (size, size0) := (world.size w, world.size g)
  let some key := Codec.Digest.ofBytes? (← IO.getRandomBytes 32) | return ← fail "getRandomBytes"
  let keys := Keys.ofKey key shapes
  if let .error f ← (Host.genesis dir key keys c world recorder.mark w : IO (Except (StoreFault (Record.Fault (Reject D))) Unit)) then
    return ← fail s!"Host.genesis {f.text}"
  let t1 ← IO.monoMsNow
  let host ← match ← openWith dir keys foldStep with
    | .ok o => pure o
    | .error e => return ← fail s!"reopen {e}"
  let t2 ← IO.monoMsNow
  unless (World.roots X.env host.opened.world).toHex == (World.roots X.env w).toHex do
    return ← fail "the reopen reached another World than the one written"
  let (dh, dbytes, entries) ← match ← countDecode host.opened.world control with
    | .ok x => pure x
    | .error e => return ← fail e
  let t3 ← IO.monoMsNow
  -- derived at worldBytesMax: the entries a base of that size holds at this run's bytes per entry
  let perEntry := (size - size0) / n
  let maxEntries := (c.worldBytesMax - size0) / perEntry + (entries - n)
  let derived := (dh * maxEntries + entries / 2) / entries
  IO.println s!"WORSTWORLD synthetic {n} tombstones, base world bytes {host.sealed.bytes} (genesis {size0}, {perEntry} per entry; decode {dbytes} bytes), {entries} trie entries"
  IO.println s!"WORSTWORLD decode trie-hashes {dh} ({ratio dh entries} per entry)"
  IO.println s!"WORSTWORLD derived at worldBytesMax {c.worldBytesMax}: {maxEntries} entries, decode trie-hashes {derived} (measured by hand at 2626112 tombstones, a base at the bound: 5252227, PERF-10)"
  IO.println s!"WORSTWORLD clock (reported, never gated): build+write {t1 - t0} ms, reopen {t2 - t1} ms, counted decode {t3 - t2} ms"
  IO.println s!"WASTE worstworld decode-trie-hashes-per-entry {ratio dh entries}"
  IO.println "BENCH-WORSTWORLD PASS"
  return 0

def run (args : List String) : IO UInt32 := do
  let act : Option (IO UInt32) := match args with
    | [s, "synthetic", n] => n.toNat?.map (synthetic s · false)
    | [s, "synthetic", n, "--harness-control"] => n.toNat?.map (synthetic s · true)
    | [s, "honest"] => some (honest s 60000 false)
    | [s, "honest", "--harness-control"] => some (honest s 60000 true)
    | [s, "honest", b] => b.toNat?.map (honest s · false)
    | [s, "honest", b, "--harness-control"] => b.toNat?.map (honest s · true)
    | _ => none
  let some act := act | do
    IO.eprintln "usage: bench-worstworld SCRATCH synthetic N [--harness-control] | SCRATCH honest [STATE_BYTES] [--harness-control]"
    return 2
  try act
  catch e =>
    IO.println s!"FAIL io: {e}"
    return (1 : UInt32)

end Nanodregg.Bench.WorstWorld
