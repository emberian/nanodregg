/-
# Bench.WorstCut — `bench-worstcut SCRATCH [--harness-control]` (PERF-5, PERF-6; ROOT 2026-10-18)

THE BAR's reopen at its TRUE worst cut, as a sized bench row (never a bar run: ~25k records of THE
BAR's mix are ~18.9 MB, and a socket run of that size is not a gate). Everything that writes or opens
is the deployed definition: `Receive.genesis`/`Receive.submit` under `Host.Deployed.X`,
`Host.genesis`, `openWriter`, `commitBatch` (each frame admitted only with `withinTail`'s proof),
`sealNow` with the writer's file checkpoint, and `openFollower` with the writer's own fold
(`foldStep`). The calls are signed by `Kernel.Sim.Deployed.params` (RFC 8032 Ed25519 from a Sim tag's
seed): a bench's fixed identity, never a custody mode, so every count below is a function of the
code alone (the Store's random key moves MAC bytes, never a size or a count).

Three Stores, one per tail SHAPE (PERF-6: which tail costs most is measured, never assumed), each
under `SCRATCH/<shape>`. In each, one founder births one data object; a base is sealed; then the tail
is filled, `recordTurnsMax` one-cell Turns per batch record, until the next frame would leave
`tailMax` of that base (`withinTail` refuses it): the most a reopen can ever fold past its base, made
of the smallest Turns of that shape, so the most steps.
- `writes`: one-slot `write`s to the object;
- `births`: one-slot data-object `create`s (the World grows by a cell per step);
- `retires`: `revoke`s, each retiring one grant (a cell tombstoned, its weight credited). The grants
  are born BEFORE the base, enough for the whole tail (a revoke's frame is sampled on the World and
  the count re-derived from the sealed base's tailMax until it suffices), sealing whenever the
  pre-base tail is full, so the base the tail folds onto holds every grant it retires.

The counts (marks on stderr, captured, as Bench.Count), per shape: the reopen (`foldStep` under
countingEnv with a counted verify: what `host serve` runs at restart, HOST-22) and the follower's
re-derivation of the same tail (`auditStep`, what follow pays as it pages). Each counted open must
reach the World the uncounted reopen reaches (steps, chain, roots digest), or `FAIL replay`.

Every tail must fill at least 99 % of tailMax (`FAIL not the worst cut` otherwise); a refusal
before it (an allowance or any other bound binding first) is `FAIL <shape> …` by name, and each shape
prints the allowance it left, so which bound binds is printed, not assumed. Prints `WORSTCUT <shape> …`
lines, `WORSTCUT worst <metric> …` naming the costliest shape per metric, and
`WASTE worstcut <metric> <ratio>` at that worst (trie hashes and verifies per step, reopen and
re-derivation); ends `BENCH-WORSTCUT PASS`.
`--harness-control`: the cut must also fill more than tailMax (a ratio above 1, which `withinTail`
makes impossible), judged on the ordinary path after all three shapes are built, on the LAST shape
counted (`retires`), so the control reads red only at the end of the shape loop:
`FAIL retires: harness-control …`.

The three Stores are built at once (one dedicated task each: they share nothing but the process);
the counts run one at a time, since each captures the process's stderr.
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

/-- A tail's shape: the one kind of one-cell Turn it is made of. -/
inductive Shape | writes | births | retires
  deriving BEq

def Shape.name : Shape → String
  | .writes => "writes"
  | .births => "births"
  | .retires => "retires"

def Shape.all : List Shape := [.writes, .births, .retires]

/-- What one shape's cut measured. -/
structure Cut where
  shape : Shape
  steps : Nat
  reopenHashes : Nat
  reopenVerifies : Nat
  auditHashes : Nat
  auditVerifies : Nat

/-- One shape's Store, built to its cut (never counted yet). -/
structure Built where
  shape : Shape
  dir : System.FilePath
  keys : Keys
  sealed : Sealed
  tail : Nat
  records : Nat
  steps : Nat
  allowanceBefore : Nat
  allowanceAfter : Nat
  grants : Nat

/-- The pins and body of tail step `i` of `shape` (the `retires` tail retires `grants[i]`). -/
def tailCall (shape : Shape) (m : Kernel.Sim.Gen.Member D) (obj : D) (grants : Array D) (i : Nat) :
    Except String (List D × Body D) :=
  match shape with
  | .writes => .ok ([m.id, obj], .write obj [(stateBase, some (Kernel.Sim.Gen.nat (i + 1)))] none)
  | .births => .ok ([m.id], .create none [] [(stateBase, Kernel.Sim.Gen.nat (i + 1))])
  | .retires =>
    if h : i < grants.size then let g := grants[i]; .ok ([m.id, g], .revoke g)
    else .error s!"no grant left to retire at step {i} (the base holds {grants.size})"

/-- Admit the founder's call of `body` on `w`, and the cell it bore, if any. -/
def admitBorn (w : World D) (m : Kernel.Sim.Gen.Member D) (pins : List D) (body : Body D) :
    Except String ((Step D × D) × World D × Option D) := do
  let (s, w') ← admit w (call w m pins body)
  match s.1 with
  | .turn t => pure (s, w', t.creates.head?.map (·.1))
  | _ => throw "the call was not a Turn"

/-- Seal a base at the Store's tail (`host seal`'s path: the writer's open, its file checkpoint,
`sealNow`); the base it sealed, as the next writer's open reads it. Every writer this opens is dropped
on return, and its segment lock with it (the caller holds none while it seals). -/
def sealBase (dir : System.FilePath) (keys : Keys) : IO (Except String Sealed) := do
  let wr ← match ← openWriter dir keys c world recorder.mark originChain foldStep with
    | .ok wr => pure wr
    | .error f => return .error s!"reopen for the seal {f.text}"
  let ck := fileCheckpoint dir keys c world recorder.mark originChain wr.index (async := false)
  if let .error f ← sealNow ck recorder.mark wr.opening.resident then return .error s!"seal {f.name}"
  wr.segment.sync
  match ← openFollower dir keys c world recorder.mark originChain foldStep with
  | .ok o =>
    unless o.sealed.offset = o.pos.offset do return .error "the new base is not at the Store's tail"
    return .ok o.sealed
  | .error f => return .error s!"open after the seal {f.text}"

/-- Bear grants of `obj` to the founder (`mutate`, unparented: the founder acts as itself) until
`goal` of them exist or the tail past the newest base is full, `recordTurnsMax` per record; the
World and grants after. -/
def bearGrants (dir : System.FilePath) (keys : Keys) (m : Kernel.Sim.Gen.Member D) (obj : D) (goal : Nat)
    (w0 : World D) (grants0 : Array D) : IO (Except String (World D × Array D)) := do
  let wr ← match ← openWriter dir keys c world recorder.mark originChain foldStep with
    | .ok wr => pure wr
    | .error f => return .error s!"open for the grants {f.text}"
  let mut w := w0
  let mut grants := grants0
  let mut pos := wr.opening.pos
  -- a bound on the loop, never reached: one record per round
  for _ in [0:(goal - grants0.size) / recordTurnsMax + 1] do
    if grants.size ≥ goal then break
    let mut staged : Array (Step D × D) := #[]
    let mut w' := w
    let mut born : Array D := #[]
    for _ in [0:min recordTurnsMax (goal - grants.size)] do
      match admitBorn w' m [m.id] (.grant obj m.id [.mutate] none) with
      | .ok (s, w'', some g) => staged := staged.push s; w' := w''; born := born.push g
      | .ok (_, _, none) => return .error "a grant bore no cell"
      | .error e => return .error s!"grant {grants.size + born.size}: {e}"
    match ← commit wr.opening.sealed wr.segment keys pos staged with
    | .ok (some p) => pos := p; w := w'; grants := grants ++ born
    | .ok none => break
    | .error e => return .error s!"commit {e}"
  wr.segment.sync
  return .ok (w, grants)

/-- The frame of one record of `recordTurnsMax` revokes staged on `w` (never committed): what the
`retires` tail pays per record. -/
def revokeFrame (w : World D) (m : Kernel.Sim.Gen.Member D) (obj : D) (grants : Array D) : Except String Nat := do
  let mut staged : Array (Step D × D) := #[]
  let mut w' := w
  for i in [0:recordTurnsMax] do
    let (pins, body) ← tailCall .retires m obj grants i
    let (s, w'') ← admit w' (call w' m pins body)
    staged := staged.push s; w' := w''
  let some rec_ := Record.encode Codec.Deployed.digestCodec staged | throw "a record past its bounds"
  pure (frameSize rec_)

/-- One shape's Store under `dir`, built to its cut. Touches nothing but `dir` and marks nothing,
so the three shapes build at once (`worstcut`); only the counts, which capture this process's
stderr, run one at a time. -/
def build (dir : System.FilePath) (shape : Shape) : IO (Except String Built) := do
  let name := shape.name
  if ← dir.pathExists then return .error s!"{dir} exists (SCRATCH must be fresh)"
  let g ← match Receive.genesis X "worstcut".toUTF8 "worstcut-nonce".toUTF8 allowanceMax founders with
    | .ok g => pure g
    | .error r => return .error s!"genesis {r.name}"
  let m : Kernel.Sim.Gen.Member D := ⟨founderId X g.origin 0, founderSecret, nextSecret⟩
  let some key := Codec.Digest.ofBytes? (← IO.getRandomBytes 32) | return .error "getRandomBytes"
  let keys := Keys.ofKey key shapes
  if let .error f ← (Host.genesis dir key keys c world recorder.mark g : IO (Except (StoreFault (Record.Fault (Reject D))) Unit)) then
    return .error s!"Host.genesis {f.text}"
  -- the object, in its own record
  let wr0 ← match ← openWriter dir keys c world recorder.mark originChain foldStep with
    | .ok x => pure x
    | .error f => return .error s!"openWriter {f.text}"
  let (s0, w1, obj) ← match admitBorn g m [m.id] (.create none [] [(stateBase, Kernel.Sim.Gen.nat 0)]) with
    | .ok (s, w1, some o) => pure (s, w1, o)
    | .ok (_, _, none) => return .error "the create bore no cell"
    | .error e => return .error s!"create {e}"
  match ← commit wr0.opening.sealed wr0.segment keys wr0.opening.pos #[s0] with
  | .ok (some _) => pure ()
  | .ok none => return .error "the first record left tailMax"
  | .error e => return .error s!"commit {e}"
  wr0.segment.sync
  -- the base: sealed over the object (and, for `retires`, over every grant the tail retires)
  if let .error e ← sealBase dir keys then return .error e
  let mut w := w1
  let mut grants : Array D := #[]
  if shape == .retires then
    -- grants until those the newest base holds cover the tail its own tailMax allows: each round
    -- bears toward the need (or until the pre-base tail is full), seals, and re-derives the need from
    -- that base (a bound on the rounds, never reached)
    let mut need := recordTurnsMax
    let mut covered := false
    for _ in [0:32] do
      if covered then break
      match ← bearGrants dir keys m obj need w grants with
      | .ok (w', gs) => w := w'; grants := gs
      | .error e => return .error e
      let sealed ← match ← sealBase dir keys with
        | .ok s => pure s
        | .error e => return .error e
      if grants.size ≥ need then
        let frame ← match revokeFrame w m obj grants with
          | .ok f => pure f
          | .error e => return .error s!"revoke sample: {e}"
        let need' := recordTurnsMax * (c.tailMax sealed.bytes / frame + 2)
        if grants.size ≥ need' then covered := true else need := need'
    unless covered do return .error s!"the base holds {grants.size} grants, short of the tail's need {need}"
  let wr ← match ← openWriter dir keys c world recorder.mark originChain foldStep with
    | .ok wr => pure wr
    | .error f => return .error s!"open for the tail {f.text}"
  let sealed := wr.opening.sealed
  unless sealed.steps ≥ 1 do return .error s!"no base past genesis (base at step {sealed.steps})"
  unless sealed.offset = wr.opening.pos.offset do return .error "the base is not at the writer's tail"
  let allowance0 := w.allowance
  let mut pos := wr.opening.pos
  let mut i := 0
  let mut records := 0
  let mut full := false
  -- a bound on the loop, never reached: tailMax over the smallest frame
  for _ in [0:(c.tailMax sealed.bytes) / 64 + 1] do
    if full then break
    let mut staged : Array (Step D × D) := #[]
    let mut w' := w
    let mut j := i
    for _ in [0:recordTurnsMax] do
      let r := match tailCall shape m obj grants j with
        | .ok (pins, body) => admit w' (call w' m pins body)
        | .error e => .error e
      match r with
      | .ok (s, w'') => staged := staged.push s; w' := w''; j := j + 1
      | .error e => return .error s!"{name} step {j}: {e}"
    match ← commit sealed wr.segment keys pos staged with
    | .ok (some p) => pos := p; w := w'; records := records + 1; i := j
    | .ok none => full := true
    | .error e => return .error s!"commit {e}"
  unless full do return .error "the tail never reached tailMax within the loop's bound"
  wr.segment.sync
  return .ok ⟨shape, dir, keys, sealed, pos.offset - sealed.offset, records, i, allowance0, w.allowance, grants.size⟩

/-- A built Store's counts: the host's reopen, then the counted reopen and re-derivation. -/
def count (b : Built) (control : Bool) : IO (Except String Cut) := do
  let (name, dir, keys, sealed, tail, i) := (b.shape.name, b.dir, b.keys, b.sealed, b.tail, b.steps)
  let tmax := c.tailMax sealed.bytes
  IO.println s!"WORSTCUT {name} base step {sealed.steps}, base world bytes {sealed.bytes}, tailMax {tmax}{if b.shape == .retires then s!", grants in the base {b.grants}" else ""}"
  IO.println s!"WORSTCUT {name} tail {tail} bytes, {b.records} records, {i} steps ({recordTurnsMax} per record); allowance {b.allowanceBefore} -> {b.allowanceAfter} of allowanceMax {allowanceMax}: tailMax binds first"
  -- the reopen as the host runs it, uncounted, then counted; then the follower's re-derivation
  let host ← match ← openWith dir keys foldStep with
    | .ok o => pure o
    | .error e => return .error s!"reopen {e}"
  let foldCounted : World D → ByteArray → Except (Record.Fault (Reject D)) (World D) :=
    Record.step Codec.Deployed.digestCodec (World.step countingX.env) (World.roots countingX.env)
  let (ro, rerr) ← captured (openWith dir keys foldCounted)
  let (ao, aerr) ← captured (openWith dir keys auditRecord)
  let same (o : Opening (World D)) : Bool :=
    o.opened.world.steps == host.opened.world.steps && o.opened.world.chain.toHex == host.opened.world.chain.toHex
      && (World.roots X.env o.opened.world).toHex == (World.roots X.env host.opened.world).toHex
  match ro, ao with
  | .error e, _ => return .error s!"replay: the counted reopen refused {e}"
  | _, .error e => return .error s!"replay: the re-derivation refused {e}"
  | .ok r1, .ok a1 =>
    unless same r1 && same a1 do return .error "replay: a counted open reached another World than the host's reopen"
    let steps := host.opened.world.steps - host.sealed.steps
    unless steps = i do return .error s!"the reopen folds {steps} steps past the base, the tail holds {i}"
    if control then
      unless tail > tmax do
        return .error s!"harness-control: the cut fills {tail} of tailMax {tmax}, and the control expects more than tailMax"
    let k : Cut := ⟨b.shape, steps, marks rerr '#', marks rerr '@', marks aerr '#', marks aerr '@'⟩
    IO.println s!"WORSTCUT {name} reopen (foldStep) trie-hashes {k.reopenHashes} verifies {k.reopenVerifies}; re-derivation (auditStep) trie-hashes {k.auditHashes} verifies {k.auditVerifies}"
    -- at the cut: within one record of tailMax (a floor, so it is this exe's own check, never a
    -- waste ceiling; `withinTail` is the ceiling, by proof)
    unless tail * 100 ≥ tmax * 99 do return .error s!"not the worst cut: the {name} tail fills {tail} of tailMax {tmax}"
    IO.println s!"WORSTCUT {name} tail-bytes-per-tailmax {ratio tail tmax}, reopen-bytes-per-allowed-byte {ratio (sealed.bytes + tail) (sealed.bytes + tmax)}"
    IO.println s!"WORSTCUT {name} per step: reopen trie-hashes {ratio k.reopenHashes steps} verifies {ratio k.reopenVerifies steps}; audit trie-hashes {ratio k.auditHashes steps} verifies {ratio k.auditVerifies steps}"
    return .ok k

/-- The cut whose `count / steps` is largest (the first, on a tie), exactly (cross-multiplied). -/
def worst (count : Cut → Nat) : List Cut → Option Cut
  | [] => none
  | k :: ks => some <| ks.foldl (fun a b => if count b * a.steps > count a * b.steps then b else a) k

def worstcut (scratch : System.FilePath) (control : Bool) : IO UInt32 := do
  IO.FS.createDirAll scratch  -- runs.py's `{fresh}` does not exist when the run starts
  let shapes := Shape.all
  let tasks ← shapes.mapM fun shape => IO.asTask (build (scratch / shape.name) shape) (prio := .dedicated)
  let mut built : Array Built := #[]
  let mut failed : Option String := none
  for (shape, t) in shapes.zip tasks do
    match ← IO.wait t with
    | .ok (.ok b) => built := built.push b
    | .ok (.error e) => failed := failed <|> some s!"{shape.name}: {e}"
    | .error e => failed := failed <|> some s!"{shape.name}: io {e}"
  if let some e := failed then return ← fail e
  let mut cuts : Array Cut := #[]
  -- the control's impossible expectation is judged on the LAST shape counted, so it reads red only
  -- once every shape was built and the count loop reached its end (GATES-6)
  for (b, n) in built.toList.zipIdx do
    match ← count b (control && n + 1 = built.size) with
    | .ok k => cuts := cuts.push k
    | .error e => return ← fail s!"{b.shape.name}: {e}"
  let metrics : List (String × (Cut → Nat)) :=
    [("reopen-trie-hashes-per-step", (·.reopenHashes)), ("reopen-verifies-per-step", (·.reopenVerifies)),
     ("audit-trie-hashes-per-step", (·.auditHashes)), ("audit-verifies-per-step", (·.auditVerifies))]
  for (metric, count) in metrics do
    let some k := worst count cuts.toList | return ← fail "no shape measured"
    let all := ", ".intercalate (cuts.toList.map fun x => s!"{x.shape.name} {ratio (count x) x.steps}")
    IO.println s!"WORSTCUT worst {metric} {ratio (count k) k.steps} ({k.shape.name}; {all})"
    IO.println s!"WASTE worstcut {metric} {ratio (count k) k.steps}"
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
