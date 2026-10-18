/-
# Bench.WorstCut — `bench-worstcut SCRATCH [--harness-control]` (PERF-5, ROOT 2026-10-18)

THE BAR's reopen at its TRUE worst cut, as a sized bench row (never a bar run: ~25k records of THE
BAR's mix are ~18.9 MB, and a socket run of that size is not a gate). Everything that writes or opens
is the deployed definition: `Receive.genesis`/`Receive.submit` under `Host.Deployed.X`,
`Host.genesis`, `openWriter`, `commitBatch` (each frame admitted only with `withinTail`'s proof),
`sealNow` with the writer's file checkpoint, and `openFollower` with the writer's own fold
(`foldStep`). The calls are signed by `Kernel.Sim.Deployed.params` (RFC 8032 Ed25519 from a Sim tag's
seed): a bench's fixed identity, never a custody mode, so every count below is a function of the
code alone (the Store's random key moves MAC bytes, never a size or a count).

The Store: one founder births one data object; a base is sealed over it; then the tail is filled
with one-slot `write`s to that object, `recordTurnsMax` per batch record, until the next frame would
leave `tailMax` of that base (`withinTail` refuses it): the most a reopen can ever have to fold past
its base, made of the smallest Turns, so the most steps.

The counts (marks on stderr, captured, as Bench.Count): the reopen (`foldStep` under countingEnv
with a counted verify: what `host serve` runs at restart, HOST-22) and the follower's re-derivation
of the same tail (`auditStep`, what follow pays as it pages). Each counted open must reach the World
the uncounted reopen reaches (steps, chain, roots digest), or `FAIL replay`.

The tail must fill at least 99 % of tailMax (`FAIL not the worst cut` otherwise). Prints `WORSTCUT …`
lines and `WASTE worstcut <metric> <ratio>` (trie hashes and verifies per step, reopen and
re-derivation); ends `BENCH-WORSTCUT PASS`.
`--harness-control`: the cut must also fill more than tailMax (a ratio above 1, which `withinTail`
makes impossible), judged on the ordinary path: `FAIL harness-control …`.
-/
import Host.Deployed
import Kernel.Sim.Deployed
import Bench.Count

namespace Nanodregg.Bench.WorstCut

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Host.Deployed
open Nanodregg.Bench.Count (captured marks ratio countingX auditRecord)

abbrev P : Kernel.Sim.Gen.Params D := Kernel.Sim.Deployed.params

def founderSecret : ByteArray := "worstcut-founder".toUTF8
def nextSecret : ByteArray := "worstcut-founder-next".toUTF8
def founders : List (ByteArray × D) := [(P.pub founderSecret, nextKeyDigest X (P.pub nextSecret))]

/-- The founder's signed call of `body` on World `w`: Kernel.Sim.Gen's `signed` shape, its window
starting at the World's height (the generator's `notBefore := 0` is refused past `windowMax`). -/
def call (w : World D) (m : Kernel.Sim.Gen.Member D) (pins : List D) (body : Body D) : Call D :=
  let u : Unsigned D :=
    { world := w.origin, member := m.id, key := P.pub m.key, notBefore := w.height,
      validUntil := w.height + 1 + 100, pins := Kernel.Sim.Gen.S.pinsFor X.env w pins,
      maxCharge := 1000000, body }
  { unsigned := u, signature := P.sign m.key (X.callMessage u) }

/-- Submit `c` on `w` under the deployed `Ctx`; the Turn's step and roots, and the World after. -/
def admit (w : World D) (c : Call D) : Except String ((Step D × D) × World D) :=
  match submit X w c with
  | .ok (t, w') => .ok ((.turn t, World.roots X.env w'), w')
  | .error v => .error (match v with | .refused r => s!"refused {r.name}" | .rejected r => s!"rejected {r.name}")

/-- Commit `staged` as one batch record at `pos`, if its frame stays within `tailMax`; `none` when
`withinTail` refuses it (the cut is reached). -/
def commit (sealed : Sealed) (seg : File) (keys : Keys) (pos : Position) (staged : Array (Step D × D)) :
    IO (Except String (Option Position)) := do
  let some rec_ := Record.encode Codec.Deployed.digestCodec staged | return .error "a record past its bounds"
  if h : withinTail c sealed pos.offset (frameSize rec_) = true then
    match ← commitBatch c sealed (fileStore seg) keys.segment pos rec_ h with
    | .ok p => return .ok (some p)
    | .error e => return .error e
  else return .ok none

def fail (s : String) : IO UInt32 := do IO.println s!"FAIL {s}"; return 1

def openWith {F : Type} (dir : System.FilePath) (keys : Keys) (step : World D → ByteArray → Except F (World D)) :
    IO (Except String (Opening (World D))) := do
  return (← openFollower dir keys c world recorder.mark originChain step).mapError (·.text)

def worstcut (scratch : System.FilePath) (control : Bool) : IO UInt32 := do
  let dir := scratch / "W"
  if ← dir.pathExists then return ← fail s!"{dir} exists (SCRATCH must be fresh)"
  IO.FS.createDirAll scratch  -- runs.py's `{fresh}` does not exist when the run starts
  let g ← match Receive.genesis X "worstcut".toUTF8 "worstcut-nonce".toUTF8 allowanceMax founders with
    | .ok g => pure g
    | .error r => return ← fail s!"genesis {r.name}"
  let m : Kernel.Sim.Gen.Member D := ⟨founderId X g.origin 0, founderSecret, nextSecret⟩
  let some key := Codec.Digest.ofBytes? (← IO.getRandomBytes 32) | return ← fail "getRandomBytes"
  let keys := Keys.ofKey key shapes
  if let .error f ← (Host.genesis dir key keys c world recorder.mark g : IO (Except (StoreFault (Record.Fault (Reject D))) Unit)) then
    return ← fail s!"Host.genesis {f.text}"
  -- the object, in its own record, then a base sealed over it (the writer's open, `host seal`'s path)
  let wr ← match ← openWriter dir keys c world recorder.mark originChain foldStep with
    | .ok wr => pure wr
    | .error f => return ← fail s!"openWriter {f.text}"
  let ((s0, w1), obj) ← match admit g (call g m [m.id] (.create none [] [(stateBase, Kernel.Sim.Gen.nat 0)])) with
    | .ok (s, w1) => match s.1 with
      | .turn t => match t.creates.head? with
        | some (o, _) => pure ((s, w1), o)
        | none => return ← fail "the create born no cell"
      | _ => return ← fail "the create was not a Turn"
    | .error e => return ← fail s!"create {e}"
  match ← commit wr.opening.sealed wr.segment keys wr.opening.pos #[s0] with
  | .ok (some _) => pure ()
  | .ok none => return ← fail "the first record left tailMax"
  | .error e => return ← fail s!"commit {e}"
  wr.segment.sync
  let wr ← match ← openWriter dir keys c world recorder.mark originChain foldStep with
    | .ok wr => pure wr
    | .error f => return ← fail s!"reopen for the seal {f.text}"
  let ck := fileCheckpoint dir keys c world recorder.mark originChain wr.index (async := false)
  let r ← match ← sealNow ck recorder.mark wr.opening.resident with
    | .ok r => pure r
    | .error f => return ← fail s!"seal {f.name}"
  wr.segment.sync
  -- the tail: one-slot writes, recordTurnsMax per record, until withinTail refuses the next frame
  let wr ← match ← openWriter dir keys c world recorder.mark originChain foldStep with
    | .ok wr => pure wr
    | .error f => return ← fail s!"reopen for the tail {f.text}"
  let sealed := wr.opening.sealed
  unless sealed.steps = r.sealed.steps && sealed.steps ≥ 1 do return ← fail s!"no base past genesis (base at step {sealed.steps})"
  let mut w := w1
  let mut pos := wr.opening.pos
  let mut i := 0
  let mut records := 0
  let mut full := false
  -- a bound on the loop, never reached: tailMax over the smallest frame
  for _ in [0:(c.tailMax sealed.bytes) / 64 + 1] do
    if full then break
    let mut staged : Array (Step D × D) := #[]
    let mut w' := w
    for _ in [0:recordTurnsMax] do
      match admit w' (call w' m [m.id, obj] (.write obj [(stateBase, some (Kernel.Sim.Gen.nat (i + 1)))] none)) with
      | .ok (s, w'') => staged := staged.push s; w' := w''; i := i + 1
      | .error e => return ← fail s!"write {i}: {e}"
    match ← commit sealed wr.segment keys pos staged with
    | .ok (some p) => pos := p; w := w'; records := records + 1
    | .ok none => full := true; i := i - recordTurnsMax
    | .error e => return ← fail s!"commit {e}"
  unless full do return ← fail "the tail never reached tailMax within the loop's bound"
  wr.segment.sync
  let tail := pos.offset - sealed.offset
  let tmax := c.tailMax sealed.bytes
  IO.println s!"WORSTCUT base step {sealed.steps}, base world bytes {sealed.bytes}, tailMax {tmax}"
  IO.println s!"WORSTCUT tail {tail} bytes, {records} records, {i} steps (one-slot writes, {recordTurnsMax} per record)"
  -- the reopen as the host runs it, uncounted, then counted; then the follower's re-derivation
  let host ← match ← openWith dir keys foldStep with
    | .ok o => pure o
    | .error e => return ← fail s!"reopen {e}"
  let foldCounted : World D → ByteArray → Except (Record.Fault (Reject D)) (World D) :=
    Record.step Codec.Deployed.digestCodec (World.step countingX.env) (World.roots countingX.env)
  let (ro, rerr) ← captured (openWith dir keys foldCounted)
  let (ao, aerr) ← captured (openWith dir keys auditRecord)
  let same (o : Opening (World D)) : Bool :=
    o.opened.world.steps == host.opened.world.steps && o.opened.world.chain.toHex == host.opened.world.chain.toHex
      && (World.roots X.env o.opened.world).toHex == (World.roots X.env host.opened.world).toHex
  match ro, ao with
  | .error e, _ => return ← fail s!"replay: the counted reopen refused {e}"
  | _, .error e => return ← fail s!"replay: the re-derivation refused {e}"
  | .ok r1, .ok a1 =>
    unless same r1 && same a1 do return ← fail "replay: a counted open reached another World than the host's reopen"
    let steps := host.opened.world.steps - host.sealed.steps
    unless steps = i do return ← fail s!"the reopen folds {steps} steps past the base, the tail holds {i}"
    if control then
      unless tail > tmax do
        return ← fail s!"harness-control: the cut fills {tail} of tailMax {tmax}, and the control expects more than tailMax"
    IO.println s!"WORSTCUT reopen (foldStep) trie-hashes {marks rerr '#'} verifies {marks rerr '@'}; re-derivation (auditStep) trie-hashes {marks aerr '#'} verifies {marks aerr '@'}"
    -- at the cut: within one record of tailMax (a floor, so it is this exe's own check, never a
    -- waste ceiling; `withinTail` is the ceiling, by proof)
    unless tail * 100 ≥ tmax * 99 do return ← fail s!"not the worst cut: the tail fills {tail} of tailMax {tmax}"
    IO.println s!"WORSTCUT tail-bytes-per-tailmax {ratio tail tmax}, reopen-bytes-per-allowed-byte {ratio (sealed.bytes + tail) (sealed.bytes + tmax)}"
    IO.println s!"WASTE worstcut reopen-trie-hashes-per-step {ratio (marks rerr '#') steps}"
    IO.println s!"WASTE worstcut reopen-verifies-per-step {ratio (marks rerr '@') steps}"
    IO.println s!"WASTE worstcut audit-trie-hashes-per-step {ratio (marks aerr '#') steps}"
    IO.println s!"WASTE worstcut audit-verifies-per-step {ratio (marks aerr '@') steps}"
    IO.println "BENCH-WORSTCUT PASS"
    return 0

def run (args : List String) : IO UInt32 := do
  let (scratch, control) ← match args with
    | [s] => pure (s, false)
    | [s, "--harness-control"] => pure (s, true)
    | _ => do IO.eprintln "usage: bench-worstcut SCRATCH [--harness-control]"; return 2
  try worstcut scratch control
  catch e =>
    IO.println s!"FAIL io: {e}"
    return (1 : UInt32)

end Nanodregg.Bench.WorstCut
