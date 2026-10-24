/-
# Bench.WorstCut — the worst-cut harness, shared by one bench per tail shape (PERF-5, PERF-6, PERF-12)

THE BAR's reopen at its TRUE worst cut, as sized bench rows (never a bar run: ~25k records of THE
BAR's mix are ~18.9 MB, and a socket run of that size is not a gate). Everything that writes or opens
is the deployed definition: `Receive.genesis`/`Receive.submit` under `Host.Deployed.X`,
`Host.genesis`, `openWriter`, `commitBatch` (each frame admitted only with `withinTail`'s proof),
`sealNow` with the writer's file checkpoint, and `openAt` with the writer's own fold
(`foldStep`). The calls are signed by `Kernel.Sim.Deployed.params` (RFC 8032 Ed25519 from a Sim tag's
seed): a bench's fixed identity, never a custody mode, so every count below is a function of the
code alone (the Store's random key moves MAC bytes, never a size or a count).

One exe per tail SHAPE (PERF-12: each is its own standing row, bounded well under the runner's
deadline, and a change to one shape's module selects that row only): `bench-worstcut-writes`,
`-births`, `-retires`, `-rows` (Bench.WorstCut<Shape>, each a `Shape` handed to `run`). Each builds its
Store under `SCRATCH/<shape>`: one founder births one data object (with whatever the shape's `first`
adds to that record); a base is sealed (and whatever `beforeTail` must put in the base, sealed with
it); then the tail is filled, `recordTurnsMax` of the shape's Turns per batch record, until the next
frame would leave `tailMax` of that base (`withinTail` refuses it): the most a reopen can ever fold
past its base, made of the smallest Turns of that shape, so the most steps.

The counts (marks on stderr, captured, as Bench.Count): the reopen (`foldStep` under countingEnv with
a counted verify: what `host serve` runs at restart, HOST-22) and the follower's re-derivation of the
same tail (`rederiveStep`, what follow pays as it pages). Each counted open must reach the World the
uncounted reopen reaches (steps, chain, roots digest), or `FAIL replay`.

The tail must fill at least 99 % of tailMax (`FAIL not the worst cut` otherwise); a refusal before it
(an allowance or any other bound binding first) is `FAIL <shape> …` by name, and the allowance it left
is printed, so which bound binds is printed, not assumed. Prints `WORSTCUT <shape> …` lines, and per
metric (trie hashes and verifies per step, reopen and re-derivation) two WASTE lines: `WASTE
worstcut-<shape> <metric> <ratio>` (the shape's own row) and `WASTE worstcut <metric> <ratio>` (the
worst-over-shapes row: gates/waste.py keeps the largest value a run set printed for a row, so the four
benches judged together are judged at their worst); ends `BENCH-WORSTCUT <shape> PASS`.
`--harness-control`: the cut must also fill more than tailMax (a ratio above 1, which `withinTail`
makes impossible), judged after the shape's Store is built and both its counted opens agree:
`FAIL <shape>: harness-control …`.
-/
import Host.Deployed
import Kernel.Sim.Deployed
import Bench.Count

namespace Nanodregg.Bench.WorstCut

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Host Nanodregg.Host.Deployed
open Nanodregg.Bench.Count (captured marks ratio countingX rederiveRecord)

abbrev P : Kernel.Sim.Gen.Params D := Kernel.Sim.Deployed.params

def founderSecret : ByteArray := "worstcut-founder".toUTF8
def nextSecret : ByteArray := "worstcut-founder-next".toUTF8
def founders : List (ByteArray × D) := [(P.pub founderSecret, nextKeyDigest X (P.pub nextSecret))]

/-- A Sim secret's Ed25519 key, derived once (PERF-12): the secret scalar, the prefix and the public
key, which `Ed25519.sign` re-derives from the seed on every call. A bench call then costs one base
multiplication to sign, not three (`P.pub` and `sign`'s own `pk`); the bytes are `P.pub`'s and
`P.sign`'s (`Signer.pk_eq`, `Signer.sign_eq`). -/
structure Signer where
  a : Nat
  pre : ByteArray
  pk : ByteArray

def Signer.of (secret : ByteArray) : Signer :=
  match Codec.Ed25519.expand (Kernel.Sim.Deployed.seed secret) with
  | (a, pre) => ⟨a, pre, Codec.Ed25519.encodePoint (Codec.Ed25519.baseMul a)⟩

/-- RFC 8032 §5.1.6 with the key derived: `Ed25519.sign`'s body past its `expand` and `pk`. -/
def Signer.sign (k : Signer) (msg : ByteArray) : ByteArray :=
  let r := Codec.Ed25519.leNat (Codec.Sha512.hash (k.pre ++ msg)).val 0 64 % Codec.Ed25519.L
  let R := Codec.Ed25519.encodePoint (Codec.Ed25519.baseMul r)
  let h := Codec.Ed25519.leNat (Codec.Sha512.hash (R ++ k.pk ++ msg)).val 0 64 % Codec.Ed25519.L
  R ++ Codec.Ed25519.le32Bytes ((r + h * k.a) % Codec.Ed25519.L)

/-- A bench member with its key derived once. -/
structure Who where
  m : Kernel.Sim.Gen.Member D
  k : Signer

def Who.of (m : Kernel.Sim.Gen.Member D) : Who := ⟨m, Signer.of m.key⟩
def Who.id (a : Who) : D := a.m.id

/-- The member's signed call of `body` on World `w`: Kernel.Sim.Gen's `signed` shape, its window
starting at the World's height (the generator's `notBefore := 0` is refused past `windowMax`). The
key and signature are `P.pub` and `P.sign` of the member's secret (`Signer.pk_eq`, `Signer.sign_eq`). -/
def call (w : World D) (m : Who) (pins : List D) (body : Body D)
    (rowPins : List (RowSlot D × D) := []) : Call D :=
  let u : Unsigned D :=
    { world := w.origin, member := m.id, key := m.k.pk, notBefore := w.height,
      validUntil := w.height + 1 + 100, pins := Kernel.Sim.Gen.S.pinsFor X.env w pins,
      maxCharge := 1000000, body, rowPins }
  { unsigned := u, signature := m.k.sign (X.callMessage u) }

/-- Submit `c` on `w` under the deployed `Ctx`; the Turn's step and roots, and the World after. -/
def admit (w : World D) (c : Call D) : Except String ((Step D × D) × World D) :=
  match submit X w c with
  | .ok (t, w') => .ok ((.turn t, World.roots X.env w'), w')
  | .error v => .error (match v with | .refused r => s!"refused {r.name}" | .rejected r => s!"rejected {r.name}")

/-- Commit `staged` as one batch record at `pos`, if its frame stays within `tailMax`; `none` when
`withinTail` refuses it (the cut is reached). -/
def commit (sealed : Sealed) (wr : Writer (World D)) (keys : Keys) (pos : Position) (staged : Array (Step D × D)) :
    IO (Except String (Option Position)) := do
  let some rec_ := Record.encode Codec.Deployed.digestCodec staged | return .error "a record past its bounds"
  if h : withinTail c sealed pos.offset (frameSize rec_) = true then
    match ← commitBatch c sealed (fileStore wr) keys.segment pos rec_ h with
    | .ok p => return .ok (some p)
    | .error e => return .error e
  else return .ok none

def fail (s : String) : IO UInt32 := do IO.println s!"FAIL {s}"; return 1

def openWith {F : Type} (dir : System.FilePath) (keys : Keys) (step : World D → ByteArray → Except F (World D)) :
    IO (Except String (Opening (World D))) := do
  return (← (·.map Prod.fst) <$> openAt dir keys c world recorder.mark originChain step).mapError (·.text)

/-- Admit the founder's call of `body` on `w`, and the cell it bore, if any. -/
def admitBorn (w : World D) (m : Who) (pins : List D) (body : Body D) :
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
  let ck := fileCheckpoint dir keys c world recorder.mark originChain wr (async := false)
  if let .error f ← sealNow ck recorder.mark wr.opening.resident then return .error s!"seal {f.name}"
  (← wr.segment.get).sync
  match ← (·.map Prod.fst) <$> openAt dir keys c world recorder.mark originChain foldStep with
  | .ok o =>
    unless o.sealed.offset = o.pos.offset do return .error "the new base is not at the Store's tail"
    return .ok o.sealed
  | .error f => return .error s!"open after the seal {f.text}"

/-- A tail shape: what its module (Bench.WorstCut<Shape>) adds to the shared build. `σ` is what its
tail carries from step to step (the retires' grants, the rows' Bell and its ring). -/
structure Shape (σ : Type) where
  name : String
  founders : List (ByteArray × D) := Nanodregg.Bench.WorstCut.founders
  /-- More steps for the object's first record, on the World after its create (`g` the genesis, `m`
  its founder, `obj` the object), and what the tail starts from. -/
  first : World D → Who → World D → D → IO (Except String (Array (Step D × D) × World D × σ))
  /-- After the first base is sealed, before the tail: what else the base the tail folds onto must
  hold, committed and sealed under `dir` (the retires' grants); the World and state after. -/
  beforeTail : System.FilePath → Keys → Who → D → World D → σ → IO (Except String (World D × σ)) :=
    fun _ _ _ _ w s => pure (.ok (w, s))
  /-- Tail step `j`'s call on `w` by the founder `m` on the object, and the state after it. -/
  step : σ → Who → D → World D → Nat → Except String (Call D × σ)
  /-- What the shape adds to its base line (the retires: the grants the base holds). -/
  note : σ → String := fun _ => ""

/-- What the cut measured. -/
structure Cut where
  steps : Nat
  reopenHashes : Nat
  reopenVerifies : Nat
  auditHashes : Nat
  auditVerifies : Nat

/-- The shape's Store, built to its cut (never counted yet). -/
structure Built where
  name : String
  dir : System.FilePath
  keys : Keys
  sealed : Sealed
  tail : Nat
  records : Nat
  steps : Nat
  allowanceBefore : Nat
  allowanceAfter : Nat
  note : String

/-- The shape's Store under `dir`, built to its cut. Touches nothing but `dir` and marks nothing. -/
def build {σ : Type} (dir : System.FilePath) (s : Shape σ) : IO (Except String Built) := do
  let name := s.name
  if ← dir.pathExists then return .error s!"{dir} exists (SCRATCH must be fresh)"
  let g ← match Receive.genesis X "worstcut".toUTF8 "worstcut-nonce".toUTF8 allowanceMax s.founders with
    | .ok g => pure g
    | .error r => return .error s!"genesis {r.name}"
  let m := Who.of ⟨founderId X g.origin 0, founderSecret, nextSecret⟩
  let some key := Codec.Digest.ofBytes? (← IO.getRandomBytes 32) | return .error "getRandomBytes"
  let keys := Keys.ofKey key shapes
  if let .error f ← (Host.genesis dir key keys c world recorder.mark g : IO (Except (StoreFault (Record.Fault (Reject D))) Unit)) then
    return .error s!"Host.genesis {f.text}"
  -- the object, in its own record (with what the shape's `first` adds)
  let wr0 ← match ← openWriter dir keys c world recorder.mark originChain foldStep with
    | .ok x => pure x
    | .error f => return .error s!"openWriter {f.text}"
  let (s0, w1, obj) ← match admitBorn g m [m.id] (.create none [] [(stateBase, Kernel.Sim.Gen.nat 0)]) with
    | .ok (st, w1, some o) => pure (st, w1, o)
    | .ok (_, _, none) => return .error "the create bore no cell"
    | .error e => return .error s!"create {e}"
  let (more, w1, st0) ← match ← s.first g m w1 obj with
    | .ok x => pure x
    | .error e => return .error s!"the first record: {e}"
  match ← commit wr0.opening.sealed wr0 keys wr0.opening.pos (#[s0] ++ more) with
  | .ok (some _) => pure ()
  | .ok none => return .error "the first record left tailMax"
  | .error e => return .error s!"commit {e}"
  (← wr0.segment.get).sync
  -- the base: sealed over the object (and over whatever the shape's `beforeTail` adds)
  if let .error e ← sealBase dir keys then return .error e
  let (w, st1) ← match ← s.beforeTail dir keys m obj w1 st0 with
    | .ok x => pure x
    | .error e => return .error e
  let wr ← match ← openWriter dir keys c world recorder.mark originChain foldStep with
    | .ok wr => pure wr
    | .error f => return .error s!"open for the tail {f.text}"
  let sealed := wr.opening.sealed
  unless sealed.steps ≥ 1 do return .error s!"no base past genesis (base at step {sealed.steps})"
  unless sealed.offset = wr.opening.pos.offset do return .error "the base is not at the writer's tail"
  let allowance0 := w.allowance
  let mut w := w
  let mut st := st1
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
    let mut st' := st
    for _ in [0:recordTurnsMax] do
      match (s.step st' m obj w' j).bind fun (cl, st'') => (admit w' cl).map (·, st'') with
      | .ok ((stp, w''), st'') => staged := staged.push stp; w' := w''; st' := st''; j := j + 1
      | .error e => return .error s!"{name} step {j}: {e}"
    match ← commit sealed wr keys pos staged with
    | .ok (some p) => pos := p; w := w'; records := records + 1; i := j; st := st'
    | .ok none => full := true
    | .error e => return .error s!"commit {e}"
  unless full do return .error "the tail never reached tailMax within the loop's bound"
  (← wr.segment.get).sync
  return .ok ⟨name, dir, keys, sealed, pos.offset - sealed.offset, records, i, allowance0, w.allowance, s.note st⟩

/-- A built Store's counts: the host's reopen, then the counted reopen and re-derivation. -/
def count (b : Built) (control : Bool) : IO (Except String (Cut × Nat × Nat × Nat)) := do
  let (name, dir, keys, sealed, tail, i) := (b.name, b.dir, b.keys, b.sealed, b.tail, b.steps)
  let tmax := c.tailMax sealed.bytes
  IO.println s!"WORSTCUT {name} base step {sealed.steps}, base world bytes {sealed.bytes}, tailMax {tmax}{b.note}"
  IO.println s!"WORSTCUT {name} tail {tail} bytes, {b.records} records, {i} steps ({recordTurnsMax} per record); allowance {b.allowanceBefore} -> {b.allowanceAfter} of allowanceMax {allowanceMax}: tailMax binds first"
  -- the reopen as the host runs it, uncounted, then counted; then the follower's re-derivation
  -- the host's reopen marks nothing, so it runs beside the counted opens (a follower open locks and
  -- writes nothing); the counted ones run one at a time, since each captures this process's stderr
  let t0 ← IO.monoMsNow
  let hostTask ← IO.asTask (do let r ← openWith dir keys foldStep; return (r, ← IO.monoMsNow)) (prio := .dedicated)
  let foldCounted : World D → ByteArray → Except (Record.Fault (Reject D)) (World D) :=
    Record.step Codec.Deployed.digestCodec (World.step countingX.env) (World.roots countingX.env)
  let t1 := t0
  let (ro, rerr) ← captured (openWith dir keys foldCounted)
  let t2 ← IO.monoMsNow
  let (ao, aerr) ← captured (openWith dir keys rederiveRecord)
  let t3 ← IO.monoMsNow
  let (host, th) ← match ← IO.wait hostTask with
    | .ok (.ok o, th) => pure (o, th)
    | .ok (.error e, _) => return .error s!"reopen {e}"
    | .error e => return .error s!"reopen: io {e}"
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
    let k : Cut := ⟨steps, marks rerr '#', marks rerr '@', marks aerr '#', marks aerr '@'⟩
    IO.println s!"WORSTCUT {name} reopen (foldStep) trie-hashes {k.reopenHashes} verifies {k.reopenVerifies}; re-derivation (rederiveStep) trie-hashes {k.auditHashes} verifies {k.auditVerifies}"
    -- at the cut: within one record of tailMax (a floor, so it is this exe's own check, never a
    -- waste ceiling; `withinTail` is the ceiling, by proof)
    unless tail * 100 ≥ tmax * 99 do return .error s!"not the worst cut: the {name} tail fills {tail} of tailMax {tmax}"
    IO.println s!"WORSTCUT {name} tail-bytes-per-tailmax {ratio tail tmax}, reopen-bytes-per-allowed-byte {ratio (sealed.bytes + tail) (sealed.bytes + tmax)}"
    IO.println s!"WORSTCUT {name} per step: reopen trie-hashes {ratio k.reopenHashes steps} verifies {ratio k.reopenVerifies steps}; audit trie-hashes {ratio k.auditHashes steps} verifies {ratio k.auditVerifies steps}"
    return .ok (k, th - t0, t2 - t1, t3 - t2)

def worstcut {σ : Type} (s : Shape σ) (scratch : System.FilePath) (control : Bool) : IO UInt32 := do
  IO.FS.createDirAll scratch  -- runs.py's `{fresh}` does not exist when the run starts
  let t0 ← IO.monoMsNow
  let b ← match ← build (scratch / s.name) s with
    | .ok b => pure b
    | .error e => return ← fail s!"{s.name}: {e}"
  let t1 ← IO.monoMsNow
  let (k, tr, tc, ta) ← match ← count b control with
    | .ok k => pure k
    | .error e => return ← fail s!"{s.name}: {e}"
  -- the box's load moves these, so they are printed and never judged (no WASTE line, no row)
  IO.println s!"WORSTCUT {s.name} wall ms (reported, never judged): build {t1 - t0}, reopen {tr} (beside the counted opens), counted reopen {tc}, re-derivation {ta}"
  let metrics : List (String × Nat) :=
    [("reopen-trie-hashes-per-step", k.reopenHashes), ("reopen-verifies-per-step", k.reopenVerifies),
     ("audit-trie-hashes-per-step", k.auditHashes), ("audit-verifies-per-step", k.auditVerifies)]
  for (metric, n) in metrics do
    IO.println s!"WASTE worstcut-{s.name} {metric} {ratio n k.steps}"
    IO.println s!"WASTE worstcut {metric} {ratio n k.steps}"
  IO.println s!"BENCH-WORSTCUT {s.name} PASS"
  return 0

def run {σ : Type} (s : Shape σ) (args : List String) : IO UInt32 := do
  let (scratch, control) ← match args with
    | [d] => pure (d, false)
    | [d, "--harness-control"] => pure (d, true)
    | _ => do IO.eprintln s!"usage: bench-worstcut-{s.name} SCRATCH [--harness-control]"; return 2
  try worstcut s scratch control
  catch e =>
    IO.println s!"FAIL io: {e}"
    return (1 : UInt32)

end Nanodregg.Bench.WorstCut
