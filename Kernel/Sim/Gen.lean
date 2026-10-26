/-
# Kernel.Sim.Gen — the seeded generator, generic in its parameters

The generator, the Host stand-in, the fold and re-derivation checks of `Kernel.Sim`, over any
digest, hash, encodings and signature scheme (`Params`). Two instances run it: the toy
(`Kernel.Sim`: UInt64 digests, FNV, a hash "signature") and the deployed (`Kernel.Sim.Deployed`:
CODEC's digest, cSHAKE256, codecs and RFC 8032 Ed25519), so the pipeline is the same code and only
the parameters differ.
-/
import Kernel.Receive.Rederive
import Kernel.Receive.Submit
import Kernel.Receive.Follow
import Kernel.Sim.Shadow
import Kernel.Sim.Required

namespace Nanodregg.Kernel.Sim.Gen

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## Shared byte helpers (payloads the generator writes; not digests) -/

def u64le (x : UInt64) : ByteArray :=
  ⟨#[x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8,
     (x >>> 32).toUInt8, (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8]⟩

def nat (n : Nat) : ByteArray := u64le n.toUInt64

def denyAll : ByteArray := "deny-all".toUTF8

/-- A law that admits a birth and its own adoption but refuses every write and invoke: what the
occasion (ID-1) lets a law say, and what LANG-19 needs (deny-all can no longer be adopted). -/
def freeze : ByteArray := "freeze".toUTF8

/-- A law that reads the OLD state (KERNEL-66's race, `probeRace`): a write must lengthen the first
state slot. -/
def grows : ByteArray := "grows".toUTF8

/-- The package of the Sim's programmed objects (the stub's method 0). -/
def methods : ByteArray := "methods".toUTF8

/-- The acts `freeze` refuses. -/
def frozenAct {D : Type} : Occasion D → Bool
  | .write | .invoke _ => true
  | .birth | .relaw _ | .adopt _ => false

/-- `b` cut into digests of `width` bytes (a short tail is dropped). -/
def idsOf (digestOf : ByteArray → Option D) (width : Nat) (b : ByteArray) : List D :=
  (List.range (b.size / width)).filterMap fun i => digestOf (b.extract (i * width) (i * width + width))

/-- The calls the stub's methods make (D5c's arms; every one is a test of the kernel's visitor):
1 pays 1 of the asset named by its argument from the object's own account to the signer's, under
the once key `payout`; 2 re-enters the object; 3 makes a call no object may make; 4 makes nine;
6 invokes the next object of its argument (`obj ‖ grant ‖ rest`) through the grant, passing the
rest on. -/
def stubCalls (digestOf : ByteArray → Option D) (width : Nat) (method : Nat) (args : ByteArray)
    (r : Req D) (budget : Nat) : List (Body D) :=
  match method with
  | 1 => match digestOf args with
    | some asset => [.transfer (.of r.self asset) (.of r.agent asset) 1 none (some "payout".toUTF8)]
    | none => []
  | 2 => [.invoke r.self 0 ByteArray.empty budget none]
  | 3 => [.issue 1]
  | 4 => List.replicate 9 (.issue 1)
  | 6 => match idsOf digestOf width args with
    | o :: g :: _ => [.invoke o 6 (args.extract (2 * width) args.size) budget (some g)]
    | _ => []
  | _ => []

/-- The size of a state's first slot (0 when absent): what `grows` compares. -/
def firstSize (s : Slots) : Nat := ((s.get stateBase).map ByteArray.size).getD 0

/-- The law-program stub both instances run (`deny-all` refuses every act, `freeze` refuses writes
and invokes, `grows` refuses a write that does not lengthen the first state slot of the OLD state,
anything else admits; method 0 sets the first state slot, the others make the calls of `stubCalls`;
method 5 reports one tick more than it was given). Each run uses one tick. LANG's real program runs
in `lang-journey`. -/
def program (digestOf : ByteArray → Option D) (width : Nat) : Program D :=
  { checkInstall := fun _ _ => .ok ()
    judge := fun look _ laws old new r =>
      forEx (fun l => match look l with
        | .ok (some cell) =>
            if cell.slots.get 0 = some denyAll then .error (.lawDenied l "deny-all")
            else if cell.slots.get 0 = some freeze ∧ frozenAct r.occasion then .error (.lawDenied l "freeze")
            else if cell.slots.get 0 = some grows ∧ r.occasion = .write ∧ firstSize new ≤ firstSize old then
              .error (.lawDenied l "grows")
            else .ok ()
        | .ok none => .error (.missingCell l)
        | .error e => .error e) laws
    run := fun _ _ _ state method args r budget =>
      if method = 0 then .ok (state.set stateBase args, [], [], min 1 budget)
      else if method = 5 then .ok (state, [], [], budget + 1)
      else if method ≤ 6 then .ok (state, stubCalls digestOf width method args r budget, [], min 1 budget)
      else .error (.program "no such method")
    rels := fun _ _ _ => .ok [] }

/-- What an instance supplies: its `Ctx` (whose `env` the generator hashes and encodes with), how
a secret becomes a public key and signs, a default digest, and a name for the report. -/
structure Params (D : Type) where
  name : String
  ctx : Ctx D
  pub : ByteArray → ByteArray
  sign : ByteArray → ByteArray → ByteArray
  zero : D
  /-- the wire bytes of a cell proof (CODEC's `proof (trieSpec env)` at the deployed codecs), where the
  instance has the proof codec; `report` prints `proof bytes-per-inclusion` only then -/
  proofSize : Option (Trie.Proof (Slot D) D → Nat) := none

/-- The instance's `Env`: its `Ctx`'s, so the two cannot disagree. -/
abbrev Params.env {D : Type} (P : Params D) : Env D := P.ctx.env

/-! ## The generator -/

structure Rng where
  s : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  let (x, r) := r.next
  (if n = 0 then 0 else x.toNat % n, r)

structure Member (D : Type) where
  id : D
  key : ByteArray
  nextKey : ByteArray

/-- The Sim's own model of a member's World grant (KERNEL-16), independent of the kernel's. -/
structure Holding (D : Type) where
  /-- the grant, then its parents up to a founder's root -/
  chain : List D
  /-- does it carry `enroll`, and how much is left -/
  enrolls : Bool
  left : Nat

/-- What the generator expects a call to get. -/
inductive Expect
  | ok
  | refused (name : String)
  | rejected (name : String)
  deriving DecidableEq, Repr

structure State (D : Type) [Ord D] where
  rng : Rng
  /-- the Host's World and its admitted log -/
  host : World D
  log : List (Step D) := []
  members : List (Member D)
  objects : List (D × D) := []
  /-- member ↦ its World grant (a member without one has none) -/
  holds : List (D × Holding D) := []
  /-- live grants: (grant, object, grantee, issuer) -/
  grants : List (D × D × D × D) := []
  /-- revoked grants: (grant, object, grantee) -/
  revoked : List (D × D × D) := []
  denyPkg : Option D := none
  freezePkg : Option D := none
  methodsPkg : Option D := none
  /-- programmed objects: (object, owner) -/
  progs : List (D × D) := []
  /-- public grants (KERNEL-26): (grant, object), each for `invoke 0`, grantee the World -/
  publics : List (D × D) := []
  fresh : Nat := 0
  lastCall : Option (Call D) := none
  steps : Nat := 0
  admitted : Nat := 0
  refusedAsExpected : Nat := 0
  /-- every refusal name met as expected (the run requires each planted name at least once) -/
  seen : List String := []
  restarts : Nat := 0
  failures : List String := []
  /-- the Sim's OWN model of value (LEDGER-2/3), independent of the kernel's: issued wells and
  their caps, accounts (id, owner, well), each account's balance, the once keys spent -/
  wells : List (D × Nat) := []
  accounts : List (D × D × D) := []
  balances : List (D × Int) := []
  /-- each account's floor in the model: a well's starts at its cap, credit lines move it -/
  floors : List (D × Nat) := []
  onces : List (D × ByteArray) := []
  /-- cv 01a14afe-7380: the trie hashes the admitted run turns REQUIRE (`Required.admit`, read off the
  tries they built), by part; `countTurn` counts what they made (`<A`) against it -/
  required : Required.Parts := {}
  /-- the cell inserts of the run turns (touches and births): the plant `hash-required:empty-per-insert`
  makes exactly one more hash per each -/
  cellInserts : Nat := 0
  /-- the call-tree arms (D5c) ran in this seed -/
  treeDone : Bool := false
  /-- KERNEL-60's counted-right and cancel arms ran (once a seed) -/
  capDone : Bool := false
  /-- admitted turns whose record bytes were compared with `Turn.logWeight` (at a 32-byte digest) -/
  weighed : Nat := 0
  /-- KERNEL-33's journal probe: the most entries any probe World held, the entries its prunes
  scanned, and the turns it admitted -/
  journalMax : Nat := 0
  journalScanned : Nat := 0
  journalTurns : Nat := 0
  /-- KERNEL-41: the journal probe's inserts (`<K`, one per probe turn) and prunes (`<R`), whose
  hashes it bracketed -/
  probeInserts : Nat := 0
  prunes : Nat := 0
  /-- what the journal probe's inserts and prunes require (`Required.insertReq`, `Required.fresh`) -/
  probeInsertReq : Nat := 0
  pruneReq : Nat := 0
  /-- what the recorded refusals require (`Required.refuse`, `<F`) -/
  refuseReq : Nat := 0
  /-- KERNEL-44: refusals the Host recorded, the most any member had recorded in one window, the
  calls declined `refusalBudget`, and the record bytes of the recorded ones -/
  recorded : Nat := 0
  /-- recorded refusals whose verdict carried its signature verify (`Verdict.verified`, PERF-1) -/
  carried : Nat := 0
  refusalMax : Nat := 0
  budgeted : Nat := 0
  refusalBytes : Nat := 0
  /-- KERNEL-46/48, the rows probe: row inserts and retracts in the admitted turns whose hashes it
  bracketed (`<W`/`<V`, `<X`/`<Y`), the range reads its turns made, and the rows those reads listed -/
  rowInserts : Nat := 0
  rowRetracts : Nat := 0
  rangeReads : Nat := 0
  rowsRead : Nat := 0
  /-- KERNEL-49 (a), the stem probe: row inserts under 64 u64-counter keys (`<S`/`<T`) -/
  stemInserts : Nat := 0
  /-- what the rows probe's counted turns require of their rows share (`<W`-`<V`, `<X`-`<Y`, `<S`-`<T`) -/
  rowInsReq : Nat := 0
  rowRetReq : Nat := 0
  stemReq : Nat := 0
  /-- Surviving written nodes of the retirement-and-birth probe. -/
  retireHeadsReq : Nat := 0
  /-- the wire bytes of the changed cells' inclusion proofs (`Params.proofSize`), and how many -/
  proofBytes : Nat := 0
  proofs : Nat := 0
  /-- what those proofs require on the wire (`Required.proofReq`, cv 01a15107-2290), and the two
  plants' wire bytes: each proof with one sibling more than its path (`extra-sibling`), and each
  sibling one byte wider than CODEC's layout (`sibling-byte`) -/
  proofReq : Nat := 0
  proofPlantSib : Nat := 0
  proofPlantByte : Nat := 0

def nameOf {α : Type} [Repr α] (a : α) : String :=
  match (reprStr a).splitOn " " with
  | h :: _ => (h.splitOn ".").getLast!
  | [] => ""

def vname : Verdict D → String
  | .refused r => s!"refused {r.name}"
  | .rejected r => s!"rejected {r.name}"

def S.pinsFor (E : Env D) (w : World D) (ids : List D) : List (D × D) :=
  ids.eraseDups.map fun c => (c, pinOf E (w.entry E c))

def signed (P : Params D) (st : State D) (m : Member D) (key : ByteArray) (pins : List (D × D)) (body : Body D) :
    Call D :=
  let u : Unsigned D :=
    { world := st.host.origin, member := m.id, key := P.pub key, notBefore := 0, validUntil := st.host.height + 1 + 100, pins,
      maxCharge := 1000000, body }
  { unsigned := u, signature := P.sign key (P.ctx.callMessage u) }

def freshKey (st : State D) (tag : String) : ByteArray × State D :=
  ((s!"key-{tag}-{st.fresh}").toUTF8, { st with fresh := st.fresh + 1 })

/-! ## The World's root (KERNEL-23): every admitted turn's slots proved, verified, and forged -/

def failWith (st : State D) (f : String) : State D := { st with failures := f :: st.failures }

/-! ### The hash counter (KERNEL-36): the rows count the calls the kernel makes

`countingEnv E` is `E` with every trie-domain hash marked: it writes one `#` to stderr through
core's `dbgTrace` (never extracted, so the compiler neither shares nor hoists a marked call), then
returns `E`'s digest unchanged. `checkRoot` runs the REAL `World.admit` and the REAL `commitTrie`
under it, each inside a bracket (`<A`, `<C`), and `report` captures stderr and counts the marks
per bracket. Sim-only: no deployed code names it. -/

def countingEnv (E : Env D) : Env D :=
  { E with hash := fun dom b =>
      if dom == domTrie then dbgTrace "#" fun _ => E.hash dom b else E.hash dom b }

/-- PLANT (the counter's tooth): the roots digest with each root's own `hashOf`, an empty trie
re-hashing the empty digest: `World.roots` as it read before cv 01a15107-2272 (and `commitWith`
before KERNEL-47). The same value (`roots_eq`), one more hash per further empty trie; `report` must
count more for it than for the real `World.roots` (`<O`) on a seed whose World had two empty tries at
once (arm `hash-count:empty-per-root`). Since KERNEL-49 (a) no insert reads an empty digest; KERNEL-35's
per-insert recomputation is planted against the requirement instead (`plantEmptyPerInsert`). -/
def plantRootsUnshared (E : Env D) (w : World D) : D :=
  rootsDigest E (w.root E) (w.journalRoot E) (w.refusalsRoot E) (w.rowsRoot E)

/-- PLANT `hash-required:empty-per-insert` (cv 01a14afe-7380): KERNEL-35's per-insert recomputation of
the empty digest, written on the compressed trie: the cell write (`commitTrie` without the
nullifiers), each insert followed by its own copy of the empty trie's digest, as every insert forced
one before KERNEL-35. Its digests are returned so none is dropped; `report` requires exactly one more
hash per cell insert than the real cell write (`<E` = `<C` + inserts), and the admission with it in
place of the cell write to read above the requirement (`hashes-per-required`). -/
def plantEmptyPerInsert (E : Env D) (w : World D) (t : Turn D) (posts : List (Post D)) : Cells D × List D :=
  let S := trieSpec E
  -- the cell write as the kernel makes it (one batch, cv 01a15107-2281), then one empty digest per insert
  let c := commitTrie E w { t with nullifiers := [] } posts
  let step := fun (acc : Cells D × List D) (_ : D × Entry) => (acc.1, Trie.emptyHash S :: acc.2)
  (bornEntries t).foldl step ((posts.map Post.pair).foldl step (c, []))

/-- PLANT `hash-required:rewalk` (cv 01a15107-2281): the turn's map written each key in turn, the
sequential fold `commitTrie` was before the batch (`Kernel.Proofs.Admit.commitTrie_eq`: the same trie),
each insert rebuilding its path from the root, so a node two of the turn's keys pass through is hashed
once per key. `report` requires it to reach the batch's root, never to count below the batch (`<B`), and
the admission with it in place of the batch to read above the requirement over the run. -/
def plantRewalk (E : Env D) (w : World D) (t : Turn D) (posts : List (Post D)) : Cells D :=
  spendAll E (insertAll E (insertAll E w.trie (posts.map Post.pair)) (bornEntries t)) t.nullifiers

/-- The counted calls for one admitted turn `w → w'`: the whole admission (`<A`), its trie write
without the nullifiers (`<C`, the cell share), its rows write (`<Q`, KERNEL-46/48: the rows trie's
nodes hash in the one trie domain, so its share is bracketed apart), the roots digest as every read
takes it (`<O`, the real `World.roots`, the four roots' one shared empty digest: since KERNEL-49 (a)
the empty digest is read only at a root, so it is its own share), and the two plants (`<P`, `<E`). Each result must be what the uncounted call gives, or
the counter changed the computation. Beside them, what the admission REQUIRES (`Required.admit`, read
off the tries the uncounted replay builds and checked against `w'`'s roots), which `report` holds the
whole count `<A` to: never below it, and at most its ceiling above. -/
def countTurn (E : Env D) (st : State D) (w w' : World D) (t : Turn D) : State D :=
  let cE := countingEnv E
  let S := trieSpec E
  match check E w t with
  | .error _ => failWith st "hash count: an admitted turn does not re-check"
  | .ok posts =>
      let t0 := { t with nullifiers := [] }
      let a := dbgTrace "<A" fun _ => World.admit cE w t
      let c := dbgTrace "<C" fun _ => commitTrie cE w t0 posts
      let e := dbgTrace "<E" fun _ => plantEmptyPerInsert cE w t posts
      let b := dbgTrace "<B" fun _ => commitTrie cE w t posts
      let n := dbgTrace "<N" fun _ => plantRewalk cE w t posts
      -- KERNEL-46/48: the rows' share, bracketed apart so the nullifier share is the nullifiers': as
      -- the compiled admission runs it (`World.admitImpl`, `@[csimp]`), `checkWith`'s ONE `rowsRun`
      let rq := dbgTrace "<Q" fun _ =>
        match rowsRun cE w t with
        | .ok rr => some rr.1
        | .error _ => none
      let o := dbgTrace "<O" fun _ => w'.roots cE
      let p := dbgTrace "<P" fun _ => plantRootsUnshared cE w'
      let roots := w'.roots E
      let st := match a with
        | .ok w'' => if w''.root E == w'.root E then st
            else failWith st "hash count: the counted admission reached another root"
        | .error _ => failWith st "hash count: the counted admission refused an admitted turn"
      let st := if c.hashOf S == (commitTrie E w t0 posts).hashOf S then st
        else failWith st "hash count: the counted cell write reached another root"
      let inserts := posts.length + t.creates.length
      let st := if e.1.hashOf S == c.hashOf S && e.2.length == inserts &&
          e.2.all (· == Trie.emptyHash S) then st
        else failWith st "hash count: the empty-per-insert plant reached another root"
      let st := match Required.admit E w t w' with
        | .ok q => { st with required := st.required.add q, cellInserts := st.cellInserts + inserts }
        | .error why => failWith st s!"hash required: {why}"
      let st := if b.hashOf S == w'.root E && n.hashOf S == w'.root E then st
        else failWith st "hash count: the batch or the re-walk plant reached another root"
      let st := if rq.map (·.hashOf (rowSpec E)) == some (w'.rowsRoot E) then st
        else failWith st "hash count: the counted rows write reached another rows root"
      let st := if o == roots then st
        else failWith st "hash count: the counted roots are not the admitted World's"
      if p == roots then st
      else failWith st "hash count: the per-root plant reached other roots"

/-- The marks of one captured run, summed per bracket tag. -/
structure Marks where
  admit : Nat := 0
  cells : Nat := 0
  plant : Nat := 0
  /-- the plant `hash-required:empty-per-insert`'s cell write (`<E`) -/
  plantInsert : Nat := 0
  /-- the turn's whole map write as the kernel makes it, one batch (`<B`), and the plant
  `hash-required:rewalk`'s, each key in turn (`<N`; cv 01a15107-2281) -/
  batch : Nat := 0
  rewalk : Nat := 0
  /-- the insert turns' rows run (`<L`) and the plant `hash-required:rows-rewalk`'s (`<M`; cv 01a153a5-0e09) -/
  rowsRun : Nat := 0
  rowsRewalk : Nat := 0
  /-- the retract turns' rows run (`<J`) and the plant `hash-required:rows-retract-seal`'s (`<Z`; cv 01a15460-e096) -/
  rowsRetRun : Nat := 0
  rowsRetSeal : Nat := 0
  retireHeadsRun : Nat := 0
  retireHeadsSeal : Nat := 0
  probeInsert : Nat := 0
  prune : Nat := 0
  refuse : Nat := 0
  rowsRoot : Nat := 0
  rowIns : Nat := 0
  rowInsBase : Nat := 0
  rowRet : Nat := 0
  rowRetBase : Nat := 0
  /-- the four roots' empty digest (`<O`, KERNEL-49 (a)) -/
  emptyRoot : Nat := 0
  /-- the stem probe (`<S` less `<T`): its row inserts' hashes, and the most one insert cost -/
  stemIns : Nat := 0
  stemBase : Nat := 0
  stemWorst : Nat := 0
  pendS : Option Nat := none
  pendT : Option Nat := none
  /-- signature verifies (`@`) of `judge` and of the two-verify plant on recorded refusals (`<G`, `<H`) -/
  verifyOnce : Nat := 0
  verifyTwice : Nat := 0
  /-- signature verifies (`@`) of the follower's re-derivation (`rederiveStep`) of recorded refusals (`<U`) -/
  verifyAudit : Nat := 0

/-- An `S` mark count and its `T` met: the insert's own hashes, kept if the most so far. -/
def pairStem (m : Marks) : Marks :=
  match m.pendS, m.pendT with
  | some a, some b => { m with stemWorst := max m.stemWorst (a - b), pendS := none, pendT := none }
  | _, _ => m

/-- `report`'s side: the marks of one captured run, summed per bracket tag (`A`, `C`, `P`, `E`,
`K`, `R`, `F`, `Q`, `O`, the verify counter's `G`, `H` (counting `@`), and the rows probe's `W`, `V`, `X`, `Y`, `S`, `T`, `L`, `M`, `J`, `Z`). An `S` and its `T` are one
stem insert turn: their difference is that insert's hashes, the most of which is `stemWorst`. -/
def countMarks (out : String) : Marks :=
  (out.splitOn "<").foldl (fun m seg =>
    let n := (seg.toList.filter (· == '#')).length
    let v := (seg.toList.filter (· == '@')).length
    match seg.toList.head? with
    | some 'A' => { m with admit := m.admit + n }
    | some 'C' => { m with cells := m.cells + n }
    | some 'P' => { m with plant := m.plant + n }
    | some 'E' => { m with plantInsert := m.plantInsert + n }
    | some 'B' => { m with batch := m.batch + n }
    | some 'N' => { m with rewalk := m.rewalk + n }
    | some 'L' => { m with rowsRun := m.rowsRun + n }
    | some 'M' => { m with rowsRewalk := m.rowsRewalk + n }
    | some 'J' => { m with rowsRetRun := m.rowsRetRun + n }
    | some 'Z' => { m with rowsRetSeal := m.rowsRetSeal + n }
    | some 'D' => { m with retireHeadsRun := m.retireHeadsRun + n }
    | some 'I' => { m with retireHeadsSeal := m.retireHeadsSeal + n }
    | some 'K' => { m with probeInsert := m.probeInsert + n }
    | some 'R' => { m with prune := m.prune + n }
    | some 'F' => { m with refuse := m.refuse + n }
    | some 'Q' => { m with rowsRoot := m.rowsRoot + n }
    | some 'W' => { m with rowIns := m.rowIns + n }
    | some 'V' => { m with rowInsBase := m.rowInsBase + n }
    | some 'X' => { m with rowRet := m.rowRet + n }
    | some 'Y' => { m with rowRetBase := m.rowRetBase + n }
    | some 'O' => { m with emptyRoot := m.emptyRoot + n }
    | some 'S' => pairStem { m with stemIns := m.stemIns + n, pendS := some n }
    | some 'T' => pairStem { m with stemBase := m.stemBase + n, pendT := some n }
    | some 'G' => { m with verifyOnce := m.verifyOnce + v }
    | some 'H' => { m with verifyTwice := m.verifyTwice + v }
    | some 'U' => { m with verifyAudit := m.verifyAudit + v }
    | _ => m) {}

/-- The slots a turn changed, in `commitTrie`'s order: its non-`keep` touches, its born cells,
its nullifiers. -/
def changedSlots (t : Turn D) : List (Slot D) :=
  (t.touches.filter fun x => x.act != .keep).map (fun x => .cell x.cell) ++
    (createdIds t).map .cell ++ t.nullifiers.map .nullifier

def meet (st : State D) (arm : String) : State D :=
  { st with refusedAsExpected := st.refusedAsExpected + 1, seen := arm :: st.seen }

/-- At a 32-byte digest (`digestWeight`, the deployed one), an admitted turn's record is exactly
`Turn.logWeight` bytes of the instance's turn codec: the charge prices the bytes the log holds.
A toy digest of another width skips the comparison (and `weighed` says how many were compared). -/
def checkLogWeight (P : Params D) (st : State D) (t : Turn D) : State D :=
  if (P.env.bytes P.zero).size = digestWeight then
    let n := (P.env.turnBytes t).size
    if n = t.logWeight then { st with weighed := st.weighed + 1 }
    else failWith st s!"log weight: the record is {n} bytes, Turn.logWeight says {t.logWeight}"
  else st

/-- The shape scan (KERNEL-49 (a)): a subtree whose every node has two non-empty children and branches
at a bit at or past `d` (strictly below its parent's children) and below the depth, and whose every
leaf holds an entry. An `empty` passes only as a whole trie (`shapeScanRoot`). Run on every World the
sim reaches through the deployed admission (`checkRoot`, `rowsTry`, the Host's World at each seed's
end); planted in `probeTrieShape` with a unary node, which it must refuse. -/
def shapeScan {K V D' : Type} (S : Trie.Spec K V D') : Nat → Trie.T K V D' → Bool
  | _, .empty => false
  | _, .leaf _ kvs => !kvs.isEmpty
  | d, .node _ b _ l r => decide (d ≤ b) && decide (b < S.depth) && shapeScan S (b + 1) l && shapeScan S (b + 1) r

def shapeScanRoot {K V D' : Type} (S : Trie.Spec K V D') : Trie.T K V D' → Bool
  | .empty => true
  | t => shapeScan S 0 t

/-- A World's four tries pass the shape scan, or the seed fails naming `what`. -/
def scanWorld (E : Env D) (st : State D) (w : World D) (what : String) : State D :=
  if shapeScanRoot (trieSpec E) w.trie && shapeScanRoot (journalSpec E) w.journal &&
      shapeScanRoot (refusalSpec E) w.refusals && shapeScanRoot (rowSpec E) w.rows then st
  else failWith st s!"shape scan: {what} holds a one-sided node, a non-ascending branching bit or an empty leaf"

/-- After an admitted turn `w → w'`: count its hashes and what they require (`countTurn`), replay its
inserts from `w`'s trie with `w'`'s leaves (the replay must reach `w'`'s root, or a touched path was
left unrehashed), prove
and verify every changed slot and one untouched one against `w'`'s root, each nullifier as absent
against `w`'s, and forge four proofs, each of which must fail to verify. -/
def checkRoot (P : Params D) (st : State D) (w w' : World D) (t : Turn D) : State D :=
  let E := P.env
  let S := trieSpec E
  let slots := changedSlots t
  let st := countTurn E st w w' t
  let st := scanWorld E st w' "an admitted turn's World"
  let (tr, st) := slots.foldl (fun (tr, st) s =>
    match w'.trie.get S s with
    | none => (tr, failWith st "root: a changed slot is absent after the turn")
    | some l => (tr.insert S s l, st)) (w.trie, st)
  let st := if tr.hashOf S == w'.root E then st
    else failWith st "root: replaying the turn's inserts does not reach the admitted root"
  let root := w'.root E
  let verifyAt := fun (st : State D) (s : Slot D) =>
    match w'.trie.get S s with
    | none => if Trie.verifyExclusion S root s (w'.trie.prove S s) then st
        else failWith st "root: an absent slot's exclusion proof does not verify"
    | some l =>
        let pr := w'.trie.prove S s
        let st := match s, P.proofSize with
          | .cell _, some size =>
              { st with proofBytes := st.proofBytes + size pr, proofs := st.proofs + 1
                        proofReq := st.proofReq + Required.proofReq S size (0, P.zero) s w'.trie
                        proofPlantSib := st.proofPlantSib + size ⟨pr.term, pr.sibs ++ [(0, P.zero)]⟩
                        proofPlantByte := st.proofPlantByte + size pr + pr.sibs.length }
          | _, _ => st
        if Trie.verifyInclusion S root s (leafDigest E l) pr then st
        else failWith st "root: a slot's inclusion proof does not verify"
  let untouched : Slot D := .cell (cellIdOf E t.txId 1000)
  let st := (slots ++ [untouched] ++ (st.members.head?.map fun m => Slot.cell m.id).toList).foldl verifyAt st
  let st := t.nullifiers.foldl (fun st nf =>
    if Trie.verifyExclusion S (w.root E) (.nullifier nf) (w.trie.prove S (.nullifier nf)) then st
    else failWith st "root: a nullifier was not provably unspent before its turn") st
  -- the forgeries: each must fail to verify, by name
  let forged : Trie.Proof (Slot D) D → Trie.Proof (Slot D) D := fun p =>
    match p.sibs with
    | [] => p
    | s :: rest => ⟨p.term, (s.1, if s.2 == E.hash domTrie "forged".toUTF8 then E.hash domTrie "forged2".toUTF8
        else E.hash domTrie "forged".toUTF8) :: rest⟩
  let st := match slots.head? with
    | none => st
    | some s =>
        match w'.trie.get S s with
        | none => st
        | some l =>
            let p := w'.trie.prove S s
            let st := if p.sibs.isEmpty then st
              else if Trie.verifyInclusion S root s (leafDigest E l) (forged p) then
                failWith st "root: a proof with a flipped sibling verified"
              else meet st "proof-sibling:refused"
            let other : Leaf := match l with
              | .entry (.live _ _) => .entry .tomb
              | _ => .entry (.live ⟨0, .ram, []⟩ 0)
            let st := if Trie.verifyInclusion S root s (leafDigest E other) p then
              failWith st "root: a proof verified a leaf the World does not hold"
            else meet st "proof-leaf:refused"
            -- the pre-turn proof of the same slot, against the post-turn root (a stale proof)
            let st := if Trie.verifyInclusion S root s (leafDigest E l) (w.trie.prove S s) then
              failWith st "root: a stale (pre-turn) proof verified against the new root"
            else meet st "proof-stale:refused"
            -- a proof longer than the trie's depth is refused before anything is hashed
            let long : Trie.Proof (Slot D) D := ⟨p.term, p.sibs ++ List.replicate (S.depth + 1) (0, root)⟩
            let st := if Trie.verifyInclusion S root s (leafDigest E l) long then
              failWith st "root: a proof longer than the depth verified"
            else meet st "proof-overlong:refused"
            -- KERNEL-49 (a): the honest proof with its last sibling claiming the next bit (the bits
            -- still ascend below the depth, so only the node hash's committed `b` can refuse it)
            match p.sibs.getLast? with
            | some (b, sd) =>
                if b + 1 < S.depth then
                  let moved : Trie.Proof (Slot D) D := ⟨p.term, p.sibs.dropLast ++ [(b + 1, sd)]⟩
                  if !Trie.ascends S 0 moved.sibs then failWith st "root: the moved-bit proof does not ascend"
                  else if Trie.verifyInclusion S root s (leafDigest E l) moved then
                    failWith st "root: a proof claiming another branching bit verified"
                  else meet st "proof-bit:refused"
                else st
            | none => st
  -- a retired cell claimed live: its old cell against the tombstone's path
  let st := t.touches.foldl (fun st x =>
    match x.act, w.entry E x.cell with
    | .retire, some (.live old v) =>
        if Trie.verifyInclusion S root (.cell x.cell) (leafDigest E (.entry (.live old v))) (w'.trie.prove S (.cell x.cell))
        then failWith st "root: a tombstone was proved live"
        else meet st "proof-tomb-live:refused"
    | _, _ => st) st
  -- KERNEL-41: the phone's journal reads against the head (`Kernel.Proofs.JournalHead`). The head
  -- link is recomputed from its four parts; the turn's own entry is proved against the journal root
  -- (`journal_prove_verifies`, `admit_journaled`); a fresh id is proved absent
  -- (`journal_prove_absent`); and four forgeries must fail: the entry at another height
  -- (`journal_inclusion_sound`), the admitted id claimed absent (`head_absent_admitted`), the
  -- pre-turn exclusion proof against the new root, and the journal proof against the CELLS root
  let JS := journalSpec E
  let jroot := w'.journalRoot E
  let st := if headLink E w.chain 0 (turnDigest E t) (rootsDigest E root jroot (w'.refusalsRoot E) (w'.rowsRoot E)) == w'.chain then st
    else failWith st "journal head: the head link over the two roots is not the admitted chain"
  let entry : Nat × D := (w.height + 1, turnDigest E t)
  let jp := w'.journal.prove JS t.txId
  let st := if Trie.verifyInclusion JS jroot t.txId (journalDigest E entry) jp then st
    else failWith st "journal head: the turn's own entry does not verify against the journal root"
  let fresh := cellIdOf E t.txId 1001
  let st := if Trie.verifyExclusion JS jroot fresh (w'.journal.prove JS fresh) then st
    else failWith st "journal head: a fresh id's exclusion proof does not verify"
  let st := if Trie.verifyInclusion JS jroot t.txId (journalDigest E (entry.1 + 1, entry.2)) jp then
      failWith st "journal head: the entry verified at another height"
    else meet st "journal-proof-height:refused"
  let st := if Trie.verifyExclusion JS jroot t.txId jp || Trie.verifyExclusion JS jroot t.txId ⟨none, jp.sibs⟩ then
      failWith st "journal head: an admitted id was proved absent"
    else meet st "journal-proof-admitted:refused"
  let st := if Trie.verifyExclusion JS jroot t.txId (w.journal.prove JS t.txId) then
      failWith st "journal head: the pre-turn exclusion proof verified against the new journal root"
    else meet st "journal-proof-stale:refused"
  let st := if Trie.verifyInclusion JS root t.txId (journalDigest E entry) jp then
      failWith st "journal head: a journal proof verified against the cells root"
    else meet st "journal-proof-cells-root:refused"
  -- a spent nullifier claimed unspent
  t.nullifiers.foldl (fun st nf =>
    let p := w'.trie.prove S (.nullifier nf)
    let st := if Trie.verifyExclusion S root (.nullifier nf) p then
      failWith st "root: a spent nullifier was proved unspent"
    else meet st "proof-spent-unspent:refused"
    -- the same path claiming an EMPTY end: only `climb = root` can refuse it
    if Trie.verifyExclusion S root (.nullifier nf) ⟨none, p.sibs⟩ then
      failWith st "root: a spent nullifier's path with an empty end verified"
    else meet st "proof-spent-empty:refused") st

/-! ### The verify counter (PERF-1): one Ed25519 verify per judgement

`verifyingCtx X` is `X` with every signature verify marked (`@`, through `dbgTrace` as the hash counter
is). `record` re-judges each recorded refusal under it in a bracket (`<G`), and the plant `judgeTwice`
(the two-verify judge before PERF-1: `submit` verifies, then `authenticated` verifies again) in
another (`<H`). Arm `verify-count:once`: on a seed with a recorded refusal the plant must count more,
or the counter is blind. Sim-only. -/

def verifyingCtx (X : Ctx D) : Ctx D :=
  { X with verify := fun k m s => dbgTrace "@" fun _ => X.verify k m s }

/-- PLANT (the verify counter's tooth): `judge` as it was before PERF-1, authenticating a refused
call by verifying its signature again: exactly `judge_eq`'s right side. The same Outcome; one more
verify per refusal whose verdict carries the verify (`Verdict.verified`). -/
def judgeTwice (X : Ctx D) (w : World D) (c : Call D) : Outcome D :=
  judgeBy X w c fun _ => authenticated X w c

/-- Both judges re-run under the verify counter, each in its bracket: each must record `r` again. -/
def countVerifies (X : Ctx D) (st : State D) (c : Call D) (r : Refused D) : State D :=
  let vX := verifyingCtx X
  let once := dbgTrace "<G" fun _ => Receive.judge vX st.host c
  let twice := dbgTrace "<H" fun _ => judgeTwice vX st.host c
  -- the follower's re-derivation of the same record (`rederiveStep`: decode, then `judge`), in its own bracket
  let audited := dbgTrace "<U" fun _ => Receive.rederiveStep vX st.host (.refusal r)
  let st := match audited with
    | .ok _ => st
    | .error _ => failWith st "verify count: the counted re-derivation refused the recorded refusal"
  let st := match once with
    | .recorded _ r' _ => if r' = r then st else failWith st "verify count: the counted judge recorded another refusal"
    | _ => failWith st "verify count: the counted judge did not record the refusal"
  match twice with
  | .recorded _ r' _ => if r' = r then st else failWith st "verify count: the two-verify plant recorded another refusal"
  | _ => failWith st "verify count: the two-verify plant did not record the refusal"

/-- The Host's recording of a refused call (KERNEL-44: `Receive.judge`), checked against the verdict
`submit` gave: a recorded refusal is that verdict, logged as a step and its hashes counted (`<F`)
against what it requires (`Required.refuse`);
an admitted call is never recorded, a refused one never admitted. -/
def record (P : Params D) (st : State D) (c : Call D) (verdict : Except (Verdict D) (Turn D × World D)) : State D :=
  let X := P.ctx
  match verdict, Receive.judge X st.host c with
  | .error v, .recorded v' r w' =>
      if v' ≠ v then failWith st s!"judge recorded {vname v'} for a call refused {vname v}"
      else
        let st := countVerifies X st c r
        let st := if v.verified then { st with carried := st.carried + 1 } else st
        let cE := countingEnv P.env
        let counted := dbgTrace "<F" fun _ => World.refuse cE st.host r
        let st := match counted with
          | .ok w'' => if w''.refusalsRoot P.env == w'.refusalsRoot P.env then st
              else failWith st "hash count: the counted refusal reached another refusals root"
          | .error _ => failWith st "hash count: the counted refusal was refused"
        let st := match Required.refuse P.env st.host r w' with
          | .ok n => { st with refuseReq := st.refuseReq + n }
          | .error why => failWith st s!"hash required: {why}"
        { st with host := w', log := st.log ++ [.refusal r], recorded := st.recorded + 1,
                  refusalMax := max st.refusalMax (refusalCount P.env w' r.member),
                  refusalBytes := st.refusalBytes + (refusedBytes P.env r).size }
  | .error _, .declined (.rejected .refusalBudget) => { st with budgeted := st.budgeted + 1 }
  | .error _, .declined _ => st
  | .error v, .admitted _ _ => failWith st s!"judge admitted a call submit refused {vname v}"
  | .ok _, .admitted _ _ => st
  | .ok _, _ => failWith st "judge refused a call submit admitted"

/-- Submit a call on the Host path and judge the verdict. -/
def submit (P : Params D) (st : State D) (c : Call D) (expect : Expect) (what : String) : State D × Option (Turn D) :=
  let X := P.ctx
  let st := { st with steps := st.steps + 1, lastCall := some c }
  -- the generator signs the same call twice now and then (same bytes, same transaction id): once
  -- its refusal is recorded, the second answer is that record (KERNEL-44), whatever it would derive
  let (expect, what) := if (refusedAnswer X st.host c).isSome ∧ expect ≠ .rejected "refusedFinal" then
      (Expect.rejected "refusedFinal", "refused-again")
    else (expect, what)
  let verdict := Receive.submit X st.host c
  let st := record P st c verdict
  let fail := fun (got : String) =>
    ({ st with failures := s!"step {st.steps} {what}: expected {reprStr expect}, got {got}" :: st.failures }, none)
  match verdict with
  | .error (.refused r) =>
      if expect = .refused r.name then
        ({ st with refusedAsExpected := st.refusedAsExpected + 1,
                   seen := s!"{what}:{r.name}" :: r.name :: st.seen }, none)
      else fail s!"refused {r.name}"
  | .error (.rejected r) =>
      if expect = .rejected r.name then
        ({ st with refusedAsExpected := st.refusedAsExpected + 1,
                   seen := s!"{what}:{r.name}" :: r.name :: st.seen }, none)
      else fail s!"rejected {r.name}"
  | .ok (t, w') =>
      if expect = .ok then
        let st := checkLogWeight P (checkRoot P st st.host w' t) t
        ({ st with host := w', log := st.log ++ [.turn t], admitted := st.admitted + 1,
                   seen := s!"{what}:ok" :: st.seen }, some t)
      else fail "admitted"

def pick {α : Type} (st : State D) (l : List α) (d : α) : α × State D :=
  let (i, rng) := st.rng.below l.length
  (l.getD i d, { st with rng })

def founder0 (P : Params D) (st : State D) : Member D := st.members.headD ⟨P.zero, ByteArray.empty, ByteArray.empty⟩

def holdOf (st : State D) (m : D) : Holding D :=
  ((st.holds.find? fun p => p.1 = m).map Prod.snd).getD ⟨[], false, 0⟩

def setHold (st : State D) (m : D) (h : Holding D) : State D :=
  { st with holds := (m, h) :: st.holds.filter fun p => p.1 ≠ m }

/-! ## The ledger arms (LEDGER-2/3) -/

def balOf (st : State D) (a : D) : Int := ((st.balances.find? fun p => p.1 = a).map Prod.snd).getD 0

def setBal (st : State D) (a : D) (b : Int) : State D :=
  { st with balances := (a, b) :: st.balances.filter fun p => p.1 ≠ a }

def capOf (st : State D) (well : D) : Nat := ((st.wells.find? fun p => p.1 = well).map Prod.snd).getD 0

/-- An account's floor in the model (0 until a credit line or an issue sets it). -/
def floorOfAcct (st : State D) (a : D) : Nat := ((st.floors.find? fun p => p.1 = a).map Prod.snd).getD 0

def setFloorM (st : State D) (a : D) (f : Nat) : State D :=
  { st with floors := (a, f) :: st.floors.filter fun p => p.1 ≠ a }

def memberOf (P : Params D) (st : State D) (id : D) : Member D :=
  (st.members.find? fun m => m.id = id).getD (founder0 P st)

/-- Record a refusal met straight at `World.admit` (a forged turn no receiver derives). -/
def metAtAdmit (st : State D) (what want : String) : Except (Reject D) (World D) → State D
  | .error r =>
      if r.name = want then
        { st with steps := st.steps + 1, refusedAsExpected := st.refusedAsExpected + 1, seen := want :: st.seen }
      else { st with failures := s!"probe {what}: expected {want}, got {r.name}" :: st.failures }
  | .ok _ => { st with failures := s!"probe {what}: forged turn admitted (expected {want})" :: st.failures }

/-- A forged turn: the given touches and births, re-priced, in the Host's window. -/
def forgedTurn (P : Params D) (w : World D) (tag : String) (touches : List (Touch D)) (creates : List Cell) : Turn D :=
  let txId := P.env.hash "nanodregg/sim/forge" (tag.toUTF8 ++ P.env.bytes w.chain)
  let t0 : Turn D := ⟨txId, 0, w.height + 1, touches,
    creates.zipIdx.map (fun p => (bornId P.env txId p, p.1)), [], 0, ByteArray.empty, [], [], txId, 0⟩
  { t0 with charge := t0.weight }

/-- The value probes: forged turns no receiver derives, each refused by the kernel by name. -/
def probeValue (P : Params D) (st : State D) : State D :=
  let w := st.host
  match st.accounts with
  | [] => st
  | a0 :: _ =>
      let (acct, st) := pick st st.accounts a0
      match w.entry P.env acct.1 with
      | none | some .tomb => st
      | some (.live cell v) =>
          let seen := pinOf P.env (some (.live cell v))
          let one (tag : String) (ops : List Op) := forgedTurn P w tag [⟨acct.1, seen, .write ops⟩] []
          let b := balOf st acct.1
          -- a credit with no debit: value from nothing
          let st := metAtAdmit st "credit-only" "notConserved"
            (World.admit P.env w (one "credit" [.set Value.balanceKey (Value.balanceBytes (b + 1))]))
          -- a floor raised outside the denomination's birth
          let st := metAtAdmit st "floor" "floorNotConserved"
            (World.admit P.env w (one "floor" [.set Value.floorKey (Value.floorBytes (floorOfAcct st acct.1 + 1))]))
          -- a balance that does not decode
          let st := metAtAdmit st "malformed" "valueMalformed"
            (World.admit P.env w (one "malformed" [.set Value.balanceKey ⟨#[1, 2, 3]⟩]))
          -- nine denominations in one turn
          let born := (List.range 9).map fun i =>
            ({ kind := kindAccount, discipline := .value,
               slots := slotsOf [(Value.denomKey, nat i), (Value.balanceKey, Value.balanceBytes 0),
                 (Value.floorKey, Value.floorBytes 0)] } : Cell)
          metAtAdmit st "denoms" "overBound" (World.admit P.env w (forgedTurn P w "denoms" [] born))

/-- The content-id probe (D5): a Turn carries its births' ids, so `World.admit` checks a ROM
birth's id is its content digest. The same ROM cell is admitted at `romIdOf` (the control: the
forgery differs only in the id) and refused `notContentId` at a transaction-derived id. -/
def probeRom (P : Params D) (st : State D) : State D :=
  let w := st.host
  let cell : Cell :=
    { kind := kindPackage, discipline := .rom, slots := [(0, ("sim/rom/" ++ toString w.height).toUTF8)] }
  let honest := forgedTurn P w "rom" [] [cell]
  let forged := { honest with creates := [(cellIdOf P.env honest.txId 0, cell)] }
  match World.admit P.env w honest, World.admit P.env w forged with
  | .ok _, .error r =>
      if r.name = "notContentId" then
        { st with steps := st.steps + 1, refusedAsExpected := st.refusedAsExpected + 1,
                  seen := "rom-id:notContentId" :: "notContentId" :: st.seen }
      else { st with failures := s!"probe rom-id: expected notContentId, got {r.name}" :: st.failures }
  | .error r, _ => { st with failures := s!"probe rom-id: the control at its content id refused {r.name}" :: st.failures }
  | _, .ok _ => { st with failures := "probe rom-id: a ROM birth at a non-content id was admitted" :: st.failures }

/-- The meter probe (DESIGN-OBS §1.3): on a COPY of the World, sixteen forged Turns by one member,
each spending `Bounds.treeTicksMax` ticks, are admitted (the sixteenth is the control), the
seventeenth is refused `ticksBudget` naming the member (`ticks-window:ticksBudget`), and a Turn
stating more ticks than one tree may use is `overBound`. Met straight at `World.admit`; nothing of
the run's World moves. Skipped when the seventeen heights would cross a window boundary (the meter
resets there, which is its design, not this probe's subject). -/
def probeTicks (P : Params D) (st : State D) : State D :=
  let w := st.host
  if (w.height + 1) / Bounds.windowMax ≠ (w.height + 17) / Bounds.windowMax then st else
  let m := P.env.hash "nanodregg/sim/ticks-member" ByteArray.empty
  let spend (w : World D) (i : Nat) : Turn D :=
    { forgedTurn P w s!"ticks-{i}" [] [] with member := m, ticks := Bounds.treeTicksMax }
  let step (acc : Except String (World D)) (i : Nat) : Except String (World D) := do
    let w ← acc
    match World.admit P.env w (spend w i) with
    | .ok w' => pure w'
    | .error r => throw s!"probe ticks-window: full tree {i + 1} of 16 in one window refused {r.name}"
  match (List.range 16).foldl step (.ok w) with
  | .error e => { st with failures := e :: st.failures }
  | .ok w16 =>
    match World.admit P.env w16 (spend w16 16),
      World.admit P.env w { spend w 99 with ticks := Bounds.treeTicksMax + 1 } with
    | .error r, .error r' =>
      if r.name = "ticksBudget" ∧ r'.name = "overBound" then
        { st with steps := st.steps + 1, refusedAsExpected := st.refusedAsExpected + 2,
                  seen := "ticks-window:ticksBudget" :: "ticksBudget" :: "overBound" :: st.seen }
      else { st with failures := s!"probe ticks-window: expected ticksBudget and overBound, got {r.name} and {r'.name}" :: st.failures }
    | .ok _, _ => { st with failures := "probe ticks-window: a seventeenth full tree in one window was admitted" :: st.failures }
    | _, .ok _ => { st with failures := "probe ticks-over: a Turn stating more ticks than a tree may use was admitted" :: st.failures }

/-- After every step: the World's value agrees with the model, every denomination sums to 0, its
floor sum is its cap, and every account is within its floor. A whole-World scan (Sim only). -/
def scanValue (P : Params D) (st : State D) : State D :=
  let w := st.host
  let bad := st.wells.filterMap fun (well, cap) =>
    let d := P.env.bytes well
    if w.valueSum d ≠ 0 then some s!"value sum {w.valueSum d} ≠ 0"
    else if w.floorSum d ≠ cap then some s!"floor sum {w.floorSum d} ≠ cap {cap}"
    else if w.outstanding d > cap then some s!"outstanding {w.outstanding d} > cap {cap}"
    else none
  let drift := st.accounts.filterMap fun (a, _, _) =>
    match (w.live P.env a).bind Value.ofCell with
    | none => some "an account is gone or malformed"
    | some v =>
        if v.balance ≠ balOf st a then some s!"balance {v.balance} ≠ model {balOf st a}"
        else if v.floor ≠ floorOfAcct st a then some s!"floor {v.floor} ≠ model {floorOfAcct st a}"
        else if !v.withinFloor then some "an account is below its floor"
        else none
  match bad ++ drift with
  | [] => st
  | f :: _ => { st with failures := s!"value scan: {f}" :: st.failures }

/-- How the model's account `(id, owner, well)` is named in a call (LEDGER-7): a well by its
denomination, any other by its owner and denomination. -/
def refOf (a : D × D × D) : AcctRef D := if a.1 = a.2.2 then .well a.1 else .of a.2.1 a.2.2

/-- One ledger action: issue (and an over-cap issue), open, transfer (honest, overdrawn,
by a stranger, to itself, of nothing, across denominations, with a once key fresh or spent). -/
def ledgerAct (P : Params D) (st : State D) (k : Nat) : State D :=
  let w := st.host
  match k with
  | 0 => -- issue a denomination; past the cap bound, `overflow`
      let (m, st) := pick st st.members (founder0 P st)
      let (r, st) := st.rng.below 8 |> fun (x, rr) => (x, { st with rng := rr })
      if r = 0 then
        let c := signed P st m m.key (S.pinsFor P.env w [m.id]) (.issue (capMax + 1))
        (submit P st c (.refused "overflow") "issue-over").1
      else
        let cap := 50 + 100 * r
        let c := signed P st m m.key (S.pinsFor P.env w [m.id]) (.issue cap)
        let (st, t) := submit P st c .ok "issue"
        match t with
        | some t =>
            let well := (createdIds t).headD P.zero
            setFloorM { st with wells := st.wells ++ [(well, cap)], accounts := st.accounts ++ [(well, m.id, well)] } well cap
        | none => st
  | 1 => -- open an account of a denomination, for the opener or for another member: at its keyed
         -- id; a pair already open is `idTaken` (one account per owner and denomination)
      match st.wells with
      | [] => st
      | w0 :: _ =>
          let (well, st) := pick st st.wells w0
          let (m, st) := pick st st.members (founder0 P st)
          let (o, st) := pick st st.members m
          let id := accountId P.ctx o.id well.1
          let taken := st.accounts.any fun a => a.1 = id
          let what := if taken then "account-twice" else if o.id = m.id then "account" else "account-for-other"
          let c := signed P st m m.key (S.pinsFor P.env w [m.id]) (.account well.1 o.id)
          let (st, t) := submit P st c (if taken then .rejected "idTaken" else .ok) what
          match t with
          | some t =>
              if (createdIds t).headD P.zero = id then { st with accounts := st.accounts ++ [(id, o.id, well.1)] }
              else { st with failures := "account: born at an id that is not accountId owner asset" :: st.failures }
          | none => st
  | 3 => -- a credit line (LEDGER-4): the issuer moves floor out of its well into an account;
         -- past the well's floor `overflow`, past its unissued headroom `belowFloor`; a non-issuer
         -- `noGrant`; out of an account that is not a well `notWell`
      match st.wells with
      | [] => st
      | w0 :: _ =>
          let (well, st) := pick st st.wells w0
          let issuer := memberOf P st (((st.accounts.find? fun a => a.1 = well.1).map fun a => a.2.1).getD (founder0 P st).id)
          let holders := st.accounts.filter fun a =>
            a.2.2 = well.1 ∧ a.1 ≠ well.1 ∧ st.members.any (·.id = a.2.1)
          match holders with
          | [] => st
          | h0 :: _ =>
              let (acct, st) := pick st holders h0
              let (r, st) := st.rng.below 6 |> fun (x, rr) => (x, { st with rng := rr })
              let wf := floorOfAcct st well.1
              let head : Int := wf + balOf st well.1
              if r = 0 then
                match st.members.find? fun m => m.id ≠ issuer.id with
                | none => st
                | some thief =>
                    let c := signed P st thief thief.key (S.pinsFor P.env w [thief.id, well.1, acct.1]) (.credit well.1 (refOf acct) 1 none)
                    (submit P st c (.refused "noGrant") "credit-stranger").1
              else if r = 1 then
                let owner := memberOf P st acct.2.1
                let c := signed P st owner owner.key (S.pinsFor P.env w [owner.id, acct.1, well.1]) (.credit acct.1 (.well well.1) 1 none)
                (submit P st c (.refused "notWell") "credit-not-well").1
              else
                let (amt, st) := st.rng.below (wf + 4) |> fun (x, rr) => (x + 1, { st with rng := rr })
                let expect : Expect := if amt > wf then .refused "overflow"
                  else if (amt : Int) > head then .rejected "belowFloor" else .ok
                let c := signed P st issuer issuer.key (S.pinsFor P.env w [issuer.id, well.1, acct.1]) (.credit well.1 (refOf acct) amt none)
                let (st, t) := submit P st c expect "credit"
                match t with
                | some _ => setFloorM (setFloorM st well.1 (wf - amt)) acct.1 (floorOfAcct st acct.1 + amt)
                | none => st
  | _ => -- a transfer, out of an account a member owns (an object's moves only by its calls)
      let acs := st.accounts.filter fun a => st.members.any (·.id = a.2.1)
      match acs with
      | [] => st
      | a0 :: _ =>
          let (kind, st) := st.rng.below 8 |> fun (x, rr) => (x, { st with rng := rr })
          -- kind 7 replays a once key already spent: from a source that spent one
          let spentFrom := acs.filter fun a => st.onces.any fun p => p.1 = a.1
          let (src, st) := if kind = 7 && !spentFrom.isEmpty then pick st spentFrom a0
            else pick st acs a0
          let same := st.accounts.filter fun a => a.2.2 = src.2.2 ∧ a.1 ≠ src.1
          let other := st.accounts.filter fun a => a.2.2 ≠ src.2.2
          let owner := memberOf P st src.2.1
          let avail : Int := balOf st src.1 + floorOfAcct st src.1
          let (amt, st) := st.rng.below (avail.toNat + 4) |> fun (x, rr) => (x + 1, { st with rng := rr })
          match kind, same, other with
          | 0, _, _ => -- to itself
              let c := signed P st owner owner.key (S.pinsFor P.env w [owner.id, src.1]) (.transfer (refOf src) (refOf src) 1 none none)
              (submit P st c (.refused "sameAccount") "transfer-self").1
          | 1, d :: _, _ => -- nothing
              let c := signed P st owner owner.key (S.pinsFor P.env w [owner.id, src.1, d.1]) (.transfer (refOf src) (refOf d) 0 none none)
              (submit P st c (.refused "zeroAmount") "transfer-zero").1
          | 2, _, d :: _ => -- across denominations
              let c := signed P st owner owner.key (S.pinsFor P.env w [owner.id, src.1, d.1]) (.transfer (refOf src) (refOf d) 1 none none)
              (submit P st c (.refused "assetMismatch") "transfer-mismatch").1
          | 3, d :: _, _ => -- a member who does not own the source, without a grant
              match st.members.find? fun m => m.id ≠ src.2.1 with
              | none => st
              | some thief =>
                  let c := signed P st thief thief.key (S.pinsFor P.env w [thief.id, src.1, d.1]) (.transfer (refOf src) (refOf d) 1 none none)
                  (submit P st c (.refused "noGrant") "transfer-stranger").1
          | 4, d :: _, _ => -- a `.well` reference to an account that is not a well: `notWell`
              if src.1 = src.2.2 then st else
              let c := signed P st owner owner.key (S.pinsFor P.env w [owner.id, src.1, d.1]) (.transfer (.well src.1) (refOf d) 1 none none)
              (submit P st c (.refused "notWell") "transfer-ref-not-well").1
          | _, d0 :: _, _ => -- the owner moves value: within the floor admitted, past it `belowFloor`;
                             -- a once key already spent from this source is `spent`
              let (d, st) := pick st same d0
              let used := st.onces.filter fun p => p.1 = src.1
              let (once, reused, st) : Option ByteArray × Bool × State D :=
                if kind = 7 then match used with
                  | u :: _ => (some u.2, true, st)
                  | [] => let (key, st) := freshKey st "once"; (some key, false, st)
                else if kind = 6 then let (key, st) := freshKey st "once"; (some key, false, st)
                else (none, false, st)
              let expect : Expect := if (amt : Int) > avail then .rejected "belowFloor"
                else if reused then .rejected "spent" else .ok
              let c := signed P st owner owner.key (S.pinsFor P.env w [owner.id, src.1, d.1])
                (.transfer (refOf src) (refOf d) amt none once)
              let (st, t) := submit P st c expect "transfer"
              match t with
              | some _ =>
                  let st := setBal st src.1 (balOf st src.1 - amt)
                  let st := setBal st d.1 (balOf st d.1 + amt)
                  match once with
                  | some key => { st with onces := (src.1, key) :: st.onces }
                  | none => st
              | none => st
          | _, _, _ => st

/-- `duplicateEffect`, met straight at the seal (the `planted` table says so): the last call's first
pin given two effects. A signed invoke whose run returns two calls moving one account reaches the
same refusal (KERNEL-67); this probe does not sign one. -/
def probeSeal (P : Params D) (st : State D) : State D :=
  match st.lastCall with
  | none => st
  | some c =>
      match c.unsigned.pins with
      | [] => st
      | p :: _ =>
          match sealTurn P.ctx c [] [(p.1, .keep), (p.1, .keep)] [] with
          | .error (.duplicateEffect x) =>
              if x = p.1 then
                { st with steps := st.steps + 1, refusedAsExpected := st.refusedAsExpected + 1,
                          seen := "duplicateEffect" :: st.seen }
              else { st with failures := "probe: duplicateEffect names another cell" :: st.failures }
          | .error r => { st with failures := s!"probe seal: got {r.name}" :: st.failures }
          | .ok _ => { st with failures := "probe: two effects on one cell sealed" :: st.failures }

/-- A programmed object of the stub package, owned by `m`. -/
def mkObj (P : Params D) (st : State D) (m : Member D) (pkg : D) : State D × Option D :=
  let c := signed P st m m.key (S.pinsFor P.env st.host [m.id, pkg]) (.create (some pkg) [] [(stateBase, nat 0)])
  let (st, t) := submit P st c .ok "tree-create"
  (st, t.map fun t => (createdIds t).headD P.zero)

/-- `m` grants object `grantee` `invoke 6` on object `target` (an object as grantee, D5c). -/
def grantObj (P : Params D) (st : State D) (m : Member D) (target grantee : D) : State D × Option D :=
  let c := signed P st m m.key (S.pinsFor P.env st.host [m.id, target, grantee]) (.grant target grantee [.invoke 6] none)
  let (st, t) := submit P st c .ok "grant-to-object"
  (st, t.map fun t => (createdIds t).headD P.zero)

/-- KERNEL-60's arms (once a seed): a COUNTED transfer right in the grant, spent per transfer and
refused past its cap (`transferSpent`); a `mutate` grant moves no value (`grantRight`); a counted
right off its target (`rightTarget`); and the CANCEL record (design C1): the member's cancel is
recorded and the call is then `refusedFinal`; another key's cancel is declined `badSignature`; a
cancel before the call's window opens is declined `outsideWindow`; the follower's re-derivation refuses
a cancel record with a forged signature `cancelForged`. -/
def capArms (P : Params D) (st : State D) : State D :=
  let X := P.ctx
  let acs := st.accounts.filter fun a => st.members.any (·.id = a.2.1) ∧ balOf st a.1 + floorOfAcct st a.1 ≥ 2
  match acs with
  | [] => st
  | src :: _ =>
    match (st.accounts.filter fun a => a.2.2 = src.2.2 ∧ a.1 ≠ src.1), st.members.find? (·.id ≠ src.2.1) with
    | d :: _, some g =>
      let st := { st with capDone := true }
      let o := memberOf P st src.2.1
      -- a root transfer grant of 1 on the owner's account
      let c := signed P st o o.key (S.pinsFor P.env st.host [o.id, g.id]) (.grant src.1 g.id [.transfer 1] none)
      let (st, t) := submit P st c .ok "transfer-grant"
      match t with
      | none => st
      | some t =>
        let gid := (createdIds t).headD P.zero
        let pins := fun (st : State D) => S.pinsFor P.env st.host [g.id, src.1, d.1, gid]
        let c := signed P st g g.key (pins st) (.transfer (refOf src) (refOf d) 1 (some gid) none)
        let (st, t) := submit P st c .ok "transfer-via"
        let st := if t.isSome then setBal (setBal st src.1 (balOf st src.1 - 1)) d.1 (balOf st d.1 + 1) else st
        let c := signed P st g g.key (pins st) (.transfer (refOf src) (refOf d) 1 (some gid) none)
        let st := (submit P st c (.refused "transferSpent") "transfer-past-cap").1
        -- a mutate grant on an account lends nothing
        let c := signed P st o o.key (S.pinsFor P.env st.host [o.id, g.id]) (.grant src.1 g.id [.mutate] none)
        let (st, t) := submit P st c .ok "mutate-grant"
        let st := match t with
          | some t =>
              let mid := (createdIds t).headD P.zero
              let c := signed P st g g.key (S.pinsFor P.env st.host [g.id, src.1, d.1, mid])
                (.transfer (refOf src) (refOf d) 1 (some mid) none)
              (submit P st c (.refused "grantRight") "transfer-mutate").1
          | none => st
        -- a counted right off its target: enroll on an account
        let c := signed P st o o.key (S.pinsFor P.env st.host [o.id, g.id]) (.grant src.1 g.id [.enroll 1] none)
        let st := (submit P st c (.refused "rightTarget") "right-target").1
        -- a counted credit right on a well: spent per credit line, refused past its cap
        let st := match st.wells.find? fun wl => floorOfAcct st wl.1 ≥ 2 ∧
            (st.accounts.any fun a => a.1 = wl.1 ∧ st.members.any (·.id = a.2.1)) ∧
            (st.accounts.any fun a => a.2.2 = wl.1 ∧ a.1 ≠ wl.1) with
          | none => st
          | some wl =>
            let iss := memberOf P st (((st.accounts.find? fun a => a.1 = wl.1).map fun a => a.2.1).getD (founder0 P st).id)
            match st.accounts.find? (fun a => a.2.2 = wl.1 ∧ a.1 ≠ wl.1), st.members.find? (·.id ≠ iss.id) with
            | some acct, some cg =>
              let c := signed P st iss iss.key (S.pinsFor P.env st.host [iss.id, cg.id]) (.grant wl.1 cg.id [.credit 1] none)
              let (st, t) := submit P st c .ok "credit-grant"
              match t with
              | some t =>
                let cid := (createdIds t).headD P.zero
                let c := signed P st cg cg.key (S.pinsFor P.env st.host [cg.id, wl.1, acct.1, cid])
                  (.credit wl.1 (refOf acct) 1 (some cid))
                let (st, t) := submit P st c .ok "credit-via"
                let st := if t.isSome then
                    setFloorM (setFloorM st wl.1 (floorOfAcct st wl.1 - 1)) acct.1 (floorOfAcct st acct.1 + 1)
                  else st
                let c := signed P st cg cg.key (S.pinsFor P.env st.host [cg.id, wl.1, acct.1, cid])
                  (.credit wl.1 (refOf acct) 1 (some cid))
                (submit P st c (.refused "creditSpent") "credit-past-cap").1
              | none => st
            | _, _ => st
        -- the cancel record: g withdraws a call it signed, before it lands
        let call := signed P st g g.key (S.pinsFor P.env st.host [g.id]) (.issue 7)
        let sig := P.sign g.key (X.cancelMessage call)
        -- another key over the same transaction id: declined, not recorded
        let st := match Receive.cancel X st.host call (P.sign o.key (X.cancelMessage call)) with
          | .declined (.refused .badSignature) => meet st "cancel-other:badSignature"
          | _ => failWith st "cancel: another member's signature was not declined badSignature"
        -- a cancel of a call whose window has not opened: declined
        let eu : Unsigned D := { call.unsigned with notBefore := st.host.height + 5, validUntil := st.host.height + 50 }
        let early : Call D := { call with unsigned := eu }
        let st := match Receive.cancel X st.host early (P.sign g.key (X.cancelMessage early)) with
          | .declined (.rejected .outsideWindow) => meet st "cancel-early:outsideWindow"
          | _ => failWith st "cancel: an early cancel was not declined outsideWindow"
        -- a forged cancel record is refused by the follower's re-derivation
        let forged := cancelOf X call (P.sign o.key (X.cancelMessage call))
        let st := match Receive.rederiveStep X st.host (.refusal forged) with
          | .error (.refused .cancelForged) => meet st "cancel-forged:cancelForged"
          | _ => failWith st "cancel: the re-derivation did not refuse a forged cancel cancelForged"
        match Receive.cancel X st.host call sig with
        | .recorded _ r w' =>
            let st := meet { st with host := w', log := st.log ++ [.refusal r] }
              "cancel:recorded"
            (submit P st call (.rejected "refusedFinal") "cancel-final").1
        -- a cancel is spam-class (KERNEL-60): a member past its window budget cannot record one
        | .declined (.rejected .refusalBudget) => meet st "cancel-budget:refusalBudget"
        | .declined v => failWith st s!"cancel: the member's own cancel was declined {vname v}"
        | _ => failWith st "cancel: the member's own cancel was admitted"
    | _, _ => st

/-- The call-tree arms (D5c, once a seed): an object pays out of the account IT owns, through its
own call (`effect_as_signed`'s tooth: derived as the invoker it is `noGrant`), and a second payout
under the same once key is `spent`; re-entry is `revisited`; a call no object may make is
`notCallable`; nine calls are `tooManyCalls`; a run claiming more ticks than it had is
`overTicks`; a chain of grants between objects nests to depth 3 (admitted) and to depth 5
(`callTooDeep`). -/
def treeArms (P : Params D) (st : State D) : State D :=
  match st.methodsPkg, st.wells with
  | some pkg, w0 :: _ =>
    let st := { st with treeDone := true }
    let (well, st) := pick st st.wells w0
    let (m, st) := pick st st.members (founder0 P st)
    let issuer := memberOf P st (((st.accounts.find? fun a => a.1 = well.1).map fun a => a.2.1).getD (founder0 P st).id)
    let avail : Int := balOf st well.1 + floorOfAcct st well.1
    match mkObj P st m pkg with
    | (st, none) => st
    | (st, some o) =>
      let X := P.ctx
      let oa := accountId X o well.1
      let ma := accountId X m.id well.1
      -- the object's account, opened by its owner; the owner's own, if it has none
      let c := signed P st m m.key (S.pinsFor P.env st.host [m.id]) (.account well.1 o)
      let (st, _) := submit P st c .ok "tree-account"
      let st := { st with accounts := st.accounts ++ [(oa, o, well.1)] }
      let st := if st.accounts.any (fun a => a.1 = ma) then st else
        let c := signed P st m m.key (S.pinsFor P.env st.host [m.id]) (.account well.1 m.id)
        let (st, _) := submit P st c .ok "tree-account"
        { st with accounts := st.accounts ++ [(ma, m.id, well.1)] }
      -- the issuer funds the object's account out of the well
      let st := if avail < 2 then st else
        let c := signed P st issuer issuer.key (S.pinsFor P.env st.host [issuer.id, well.1, oa])
          (.transfer (.well well.1) (.of o well.1) 2 none none)
        let (st, t) := submit P st c .ok "tree-fund"
        match t with
        | some _ => setBal (setBal st well.1 (balOf st well.1 - 2)) oa (balOf st oa + 2)
        | none => st
      let st := if avail < 2 then st else
        let pins := S.pinsFor P.env st.host [m.id, o, oa, ma]
        let c := signed P st m m.key pins (.invoke o 1 (P.env.bytes well.1) 1000 none)
        let (st, t) := submit P st c .ok "object-pays"
        let st := match t with
          | some _ => { setBal (setBal st oa (balOf st oa - 1)) ma (balOf st ma + 1) with
              onces := (oa, "payout".toUTF8) :: st.onces }
          | none => st
        let c := signed P st m m.key (S.pinsFor P.env st.host [m.id, o, oa, ma]) (.invoke o 1 (P.env.bytes well.1) 1000 none)
        (submit P st c (.rejected "spent") "object-pays-twice").1
      let one := fun (st : State D) (method : Nat) (want : Expect) (what : String) =>
        let c := signed P st m m.key (S.pinsFor P.env st.host [m.id, o]) (.invoke o method ByteArray.empty 1000 none)
        (submit P st c want what).1
      let st := one st 2 (.refused "revisited") "reenter"
      let st := one st 3 (.refused "notCallable") "call-not-callable"
      let st := one st 4 (.refused "tooManyCalls") "too-many-calls"
      let st := one st 5 (.refused "overTicks") "over-ticks"
      -- a chain o1 → o2 → … through grants naming the calling object
      let mk := fun (st : State D) => mkObj P st m pkg
      let (st, o1) := mk st
      let (st, o2) := mk st
      let (st, o3) := mk st
      let (st, o4) := mk st
      let (st, o5) := mk st
      match o1, o2, o3, o4, o5 with
      | some o1, some o2, some o3, some o4, some o5 =>
        let (st, g2) := grantObj P st m o2 o1
        let (st, g3) := grantObj P st m o3 o2
        let (st, g4) := grantObj P st m o4 o3
        let (st, g5) := grantObj P st m o5 o4
        match g2, g3, g4, g5 with
        | some g2, some g3, some g4, some g5 =>
          let b := P.env.bytes
          let pins := S.pinsFor P.env st.host [m.id, o1, o2, o3, o4, o5, g2, g3, g4, g5]
          -- o2 → o3 → o4 → o5: depth 3, admitted
          let c := signed P st m m.key pins (.invoke o2 6 (b o3 ++ b g3 ++ b o4 ++ b g4 ++ b o5 ++ b g5) 1000 none)
          let st := (submit P st c .ok "call-chain").1
          -- o1 → o2 → o3 → o4 → o5 → (o1): o5's call is at depth 5, past the bound
          let c := signed P st m m.key pins
            (.invoke o1 6 (b o2 ++ b g2 ++ b o3 ++ b g3 ++ b o4 ++ b g4 ++ b o5 ++ b g5 ++ b o1 ++ b g2) 1000 none)
          (submit P st c (.refused "callTooDeep") "call-too-deep").1
        | _, _, _, _ => st
      | _, _, _, _, _ => st
  | _, _ => st

/-- One generated action. -/
def act (P : Params D) (st : State D) : State D :=
  let (k, rng) := st.rng.below 24
  let st := { st with rng }
  let w := st.host
  match k with
  | 15 | 16 => ledgerAct P st (k - 15)
  | 17 | 18 => ledgerAct P st 2
  | 19 => probeTicks P (probeRom P (probeValue P st))
  | 23 => if !st.treeDone then treeArms P st else if st.capDone then st else capArms P st
  | 20 => ledgerAct P st 3
  | 21 => -- birth a programmed object; half the time its owner makes method 0 public (KERNEL-26:
          -- a grant whose grantee is the World)
      match st.methodsPkg with
      | none => st
      | some pkg =>
          let (m, st) := pick st st.members (founder0 P st)
          let c := signed P st m m.key (S.pinsFor P.env w [m.id, pkg]) (.create (some pkg) [] [(stateBase, nat 0)])
          let (st, t) := submit P st c .ok "create-programmed"
          match t with
          | none => st
          | some t =>
              let obj := (createdIds t).headD P.zero
              let st := { st with progs := st.progs ++ [(obj, m.id)] }
              let (pub, st) := st.rng.below 2 |> fun (x, r) => (x == 0, { st with rng := r })
              if !pub then st else
              let c := signed P st m m.key (S.pinsFor P.env st.host [m.id, obj])
                (.grant obj (worldId P.ctx) [.invoke 0] none)
              let (st, t) := submit P st c .ok "grant-public"
              match t with
              | some t => { st with publics := st.publics ++ [((createdIds t).headD P.zero, obj)] }
              | none => st
  | 22 => -- invoke (KERNEL-25): the owner is admitted; another member without a grant is refused
          -- `noGrant`; any member through a public grant is admitted for method 0 and refused
          -- `grantRight` for method 1 (the grant carries `invoke 0` only); a public grant is used,
          -- never re-delegated: carving a child from it is `noGrant` (KERNEL-26)
      match st.progs with
      | [] => st
      | o :: _ =>
          let (prog, st) := pick st st.progs o
          let (obj, owner) := prog
          let (m, st) := pick st st.members (founder0 P st)
          let (how, st) := st.rng.below 4 |> fun (x, r) => (x, { st with rng := r })
          match how, st.publics.find? (fun p => p.2 = obj) with
          | 0, _ | _, none =>
              let c := signed P st m m.key (S.pinsFor P.env w [m.id, obj]) (.invoke obj 0 (nat st.steps) 1000 none)
              if m.id = owner then (submit P st c .ok "invoke-owner").1
              else (submit P st c (.refused "noGrant") "invoke-no-grant").1
          | 3, some (gid, _) =>
              let (ge, st) := pick st st.members (founder0 P st)
              let c := signed P st m m.key (S.pinsFor P.env w [m.id, ge.id, obj, gid])
                (.grant obj ge.id [.invoke 0] (some gid))
              (submit P st c (.refused "noGrant") "carve-public").1
          | how, some (gid, _) =>
              let method := if how = 1 then 0 else 1
              let c := signed P st m m.key (S.pinsFor P.env w [m.id, obj, gid])
                (.invoke obj method (nat st.steps) 1000 (some gid))
              if method = 0 then (submit P st c .ok "invoke-public").1
              else (submit P st c (.refused "grantRight") "invoke-public-method-1").1
  | 0 | 13 => -- enrol a newcomer (KERNEL-16): through the sponsor's own World grant, admitted
         -- while its count lasts (`enrollSpent` after), `grantRight` through a grant without
         -- `enroll`; a sponsor without a grant tries someone else's (`noGrant`)
      let (sp, st) := pick st st.members (founder0 P st)
      let (key, st) := freshKey st "m"
      let (nk, st) := freshKey st "n"
      let X := P.ctx
      let possession := P.sign key (possessionMessage X sp.id (nextKeyDigest X (P.pub nk)) (P.pub key))
      let hs := holdOf st sp.id
      let (chain, expect, st) : List D × Expect × State D := match hs.chain with
        | _ :: _ =>
            (hs.chain, (if !hs.enrolls then .refused "grantRight"
              else if hs.left = 0 then .refused "enrollSpent" else .ok), st)
        | [] =>
            let other := st.holds.filter fun p => p.1 ≠ sp.id
            let (o, st) := pick st other (P.zero, ⟨[], false, 0⟩)
            (o.2.chain, .refused "noGrant", st)
      match chain with
      | [] => st
      | via :: _ =>
          let c := signed P st sp sp.key (S.pinsFor P.env w (sp.id :: chain))
            (.enroll (P.pub key) (nextKeyDigest X (P.pub nk)) possession via)
          let (st, t) := submit P st c expect "enroll"
          match t with
          | some t =>
              let id := (createdIds t).headD P.zero
              let st := setHold st sp.id { hs with left := hs.left - 1 }
              { st with members := st.members ++ [{ id, key, nextKey := nk }] }
          | none => st
  | 12 => -- delegate: a member with a World grant gives another member World rights, carving an
          -- enrolment count from its own (`grantWidens` past what is left); a parentless World
          -- grant is `unrooted`
      let (m, st) := pick st st.members (founder0 P st)
      let (ge, st) := pick st st.members (founder0 P st)
      let (n, st) := st.rng.below 4 |> fun (x, r) => (x, { st with rng := r })
      let X := P.ctx
      let hm := holdOf st m.id
      match hm.chain with
      | [] =>
          let c := signed P st m m.key (S.pinsFor P.env w [m.id, ge.id]) (.grant (worldId X) ge.id [.observe] none)
          (submit P st c (.refused "unrooted") "world-root").1
      | g :: _ =>
          -- n = 3: observe only (the grantee may follow, not enrol)
          let rights := if n = 3 then [.observe] else [.observe, .enroll n]
          let units := if n = 3 then 0 else n
          let expect : Expect := if !hm.enrolls && n ≠ 3 then .refused "grantWidens"
            else if units ≤ hm.left then .ok else .refused "grantWidens"
          let c := signed P st m m.key (S.pinsFor P.env w [m.id, ge.id, g]) (.grant (worldId X) ge.id rights (some g))
          let (st, t) := submit P st c expect "delegate"
          match t with
          | some t =>
              let gid := (createdIds t).headD P.zero
              let st := setHold st m.id { hm with left := hm.left - units }
              -- the grantee now acts through the new grant (its old one, if any, is forgotten;
              -- when the grantee is the granter, the carved grant replaces the spent one)
              setHold st ge.id ⟨gid :: hm.chain, n ≠ 3, units⟩
          | none => st
  | 1 => -- birth a data object; a birth under deny-all is judged by it and refused, a birth under
         -- freeze is a birth, which freeze admits
      let (m, st) := pick st st.members (founder0 P st)
      let (d, st) := st.rng.below 4 |> fun (x, r) => (x, { st with rng := r })
      let laws := if d = 0 then st.denyPkg.toList else if d = 1 then st.freezePkg.toList else []
      let denied := d = 0 ∧ !laws.isEmpty
      let c := signed P st m m.key (S.pinsFor P.env w (m.id :: laws)) (.create none laws [(stateBase, nat 0)])
      let (st, t) := submit P st c (if denied then .refused "lawDenied" else .ok)
        (if d = 1 then "create-frozen" else "create")
      match t with
      | some t => { st with objects := st.objects ++ [((createdIds t).headD P.zero, m.id)] }
      | none => st
  | 3 => -- the owner replaces an object's laws: judged by the laws in force (deny-all refuses) AND by
         -- the new laws over the unchanged state (LANG-19: deny-all denies its own adoption; freeze
         -- admits it, and then refuses writes)
      match st.objects, st.denyPkg, st.freezePkg with
      | o :: _, some deny, some frz =>
          let (obj, st) := pick st st.objects o
          let (d, st) := st.rng.below 2 |> fun (x, r) => (x, { st with rng := r })
          let new := if d = 0 then deny else frz
          let owner := (st.members.find? fun m => m.id = obj.2).getD (founder0 P st)
          let laws := match w.live P.env obj.1 with
            | some cell => (lawSlotsOf cell).filterMap fun (p : Nat × ByteArray) => P.ctx.digestOf p.2
            | none => []
          let denied := laws.any (· = deny) ∨ new = deny
          let c := signed P st owner owner.key (S.pinsFor P.env w (owner.id :: obj.1 :: new :: laws))
            (.law obj.1 [new] none)
          -- `law-self` is the ADOPTION refusal (`law_judged`, `law_adopt_refused`): no object ever
          -- has deny-all in force (a birth under it is refused, and so is every adoption of it), so
          -- the laws in force admit the `relaw` and the refusal is the added law's own, on `adopt`
          (submit P st c (if denied then .refused "lawDenied" else .ok) (if d = 0 then "law-self" else "law")).1
      | _, _, _ => st
  | 2 => -- the owner writes; under deny-all it must be lawDenied
      match st.objects with
      | [] => st
      | o :: _ =>
          let (obj, st) := pick st st.objects o
          let owner := (st.members.find? fun m => m.id = obj.2).getD (founder0 P st)
          let laws := match w.live P.env obj.1 with
            | some cell => (lawSlotsOf cell).filterMap fun (p : Nat × ByteArray) => P.ctx.digestOf p.2
            | none => []
          let denied := laws.any fun l => some l = st.denyPkg ∨ some l = st.freezePkg
          let c := signed P st owner owner.key (S.pinsFor P.env w (owner.id :: obj.1 :: laws))
            (.write obj.1 [(0, nat st.steps)] none)
          (submit P st c (if denied then .refused "lawDenied" else .ok) "write").1
  | 4 => -- a member who does not own the object writes without a grant
      match st.objects with
      | [] => st
      | o :: _ =>
          let (obj, st) := pick st st.objects o
          match st.members.find? fun m => m.id ≠ obj.2 with
          | none => st
          | some m =>
              let c := signed P st m m.key (S.pinsFor P.env w [m.id, obj.1]) (.write obj.1 [(0, nat 1)] none)
              (submit P st c (.refused "noGrant") "write-no-grant").1
  | 5 => -- a stranger (never enrolled) signs
      let (key, st) := freshKey st "stranger"
      let ghost : Member D := ⟨P.env.hash "nanodregg/sim/ghost" key, key, key⟩
      let c := signed P st ghost key (S.pinsFor P.env w [ghost.id]) (.create none [] [])
      (submit P st c (.refused "unknownKey") "stranger").1
  | 6 => -- replay the last call exactly
      match st.lastCall with
      | none => st
      | some c =>
          match w.journalAt P.env (txIdOf P.ctx c) with
          | some (h, _) => (submit P st c (.rejected "replayed") s!"replay@{h}").1
          | none => st
  | 7 => -- a stale pin: the owner claims the object is absent. `stale` whatever laws the object has
         -- (KERNEL-66: the pins are compared before any law judges; a frozen object's law would refuse the
         -- write `lawDenied`, and before KERNEL-66 that refusal was recorded, so this arm skipped lawed objects)
      match st.objects with
      | [] => st
      | o :: _ =>
          let (obj, st) := pick st st.objects o
          let owner := (st.members.find? fun m => m.id = obj.2).getD (founder0 P st)
          let pins := (S.pinsFor P.env w [owner.id]) ++ [(obj.1, pinOf P.env none)]
          let c := signed P st owner owner.key pins (.write obj.1 [(0, nat 7)] none)
          (submit P st c (.rejected "stale") "stale").1
  | 8 => -- rotation: a thief's key is refused; the member's precommitted key is admitted
      let (m, st) := pick st st.members (founder0 P st)
      let (thief, st) := freshKey st "thief"
      let X := P.ctx
      let bad := signed P st m thief (S.pinsFor P.env w [m.id]) (.rotate (P.pub thief) (nextKeyDigest X (P.pub thief)))
      let (st, _) := submit P st bad (.refused "notPrecommitted") "thief-rotate"
      let (nk, st) := freshKey st "n"
      let good := signed P st m m.nextKey (S.pinsFor P.env st.host [m.id]) (.rotate (P.pub m.nextKey) (nextKeyDigest X (P.pub nk)))
      let (st, t) := submit P st good .ok "rotate"
      match t with
      | some _ =>
          let members := st.members.map fun x => if x.id = m.id then ⟨x.id, x.nextKey, nk⟩ else x
          let st := { st with members }
          -- the old key is no longer the member's
          let old := signed P st m m.key (S.pinsFor P.env st.host [m.id]) (.create none [] [])
          let st := (submit P st old (.refused "unknownKey") "old-key").1
          -- KERNEL-60 `rotate_stales_outstanding`: a call that pinned the member before the rotation is
          -- never admitted after it, even signed with the member's current key: its member pin is
          -- behind for ever (declined `stale`, never recorded)
          let outstanding := signed P st m m.nextKey (S.pinsFor P.env w [m.id]) (.create none [] [])
          (submit P st outstanding (.rejected "stale") "rotate-stales").1
      | none => st
  | 9 => -- the owner grants `mutate` on its object to another member
      match st.objects with
      | [] => st
      | o :: _ =>
          let (obj, st) := pick st st.objects o
          let owner := (st.members.find? fun m => m.id = obj.2).getD (founder0 P st)
          let (ge, st) := pick st st.members (founder0 P st)
          let c := signed P st owner owner.key (S.pinsFor P.env w [owner.id, ge.id]) (.grant obj.1 ge.id [.mutate] none)
          let (st, t) := submit P st c .ok "grant"
          match t with
          | some t => { st with grants := st.grants ++ [((createdIds t).headD P.zero, obj.1, ge.id, owner.id)] }
          | none => st
  | 10 => -- revoke: a non-issuer is refused; the issuer retires the grant and the budget gets the
          -- grant cell's weight back (KERNEL-15, `admit_retire`)
      match st.grants with
      | [] => st
      | g0 :: _ =>
          let (g, st) := pick st st.grants g0
          let (gid, obj, ge, iss) := g
          let issuer := (st.members.find? fun m => m.id = iss).getD (founder0 P st)
          let st := match st.members.find? fun m => m.id ≠ iss with
            | some m => (submit P st (signed P st m m.key (S.pinsFor P.env w [m.id, gid]) (.revoke gid))
                (.refused "notIssuer") "revoke-not-issuer").1
            | none => st
          let w := st.host
          let back := ((w.entry P.env gid).map Entry.weight).getD 0
          let (st, t) := submit P st (signed P st issuer issuer.key (S.pinsFor P.env w [issuer.id, gid]) (.revoke gid))
            .ok "revoke"
          match t with
          | some t =>
              let st := { st with grants := st.grants.filter (·.1 ≠ gid),
                                  revoked := st.revoked ++ [(gid, obj, ge)] }
              if st.host.allowance + t.charge = w.allowance + back ∧ 0 < back then st
              else { st with failures := s!"revoke: allowance {st.host.allowance} + charge {t.charge} ≠ {w.allowance} + {back}" :: st.failures }
          | none => st
  | 11 => -- a grantee writes through its grant (admitted unless the object is under deny-all),
          -- or through a revoked one (refused: the grant cell is gone)
      let (useRevoked, st) := st.rng.below 3 |> fun (x, r) => (x == 0, { st with rng := r })
      let cand := if useRevoked then st.revoked else st.grants.map fun (g, o, ge, _) => (g, o, ge)
      match cand with
      | [] => st
      | g0 :: _ =>
          let (g, st) := pick st cand g0
          let (gid, obj, ge) := g
          match st.members.find? fun m => m.id = ge with
          | none => st
          | some m =>
              let laws := match w.live P.env obj with
                | some cell => (lawSlotsOf cell).filterMap fun (p : Nat × ByteArray) => P.ctx.digestOf p.2
                | none => []
              let denied := laws.any fun l => some l = st.denyPkg ∨ some l = st.freezePkg
              let c := signed P st m m.key (S.pinsFor P.env w (m.id :: obj :: gid :: laws))
                (.write obj [(1, nat st.steps)] (some gid))
              let expect := if useRevoked then .refused "missingCell"
                else if denied then .refused "lawDenied" else .ok
              (submit P st c expect "write-via-grant").1
  | _ => -- a probe straight at admit: an admitted-shape turn with the wrong charge
      let st := probeSeal P st
      match (Step.turns st.log).getLast? with
      | none => st
      | some t =>
          let bad := { t with txId := P.env.hash "nanodregg/sim/probe" (P.env.bytes t.txId), charge := t.charge + 1 }
          let st := match World.admit P.env w bad with
            | .error r =>
                -- (a re-identified copy of an `issue` bears its well under a NEW id, while the
                -- well still names the OLD denomination: a second issuance, `floorNotConserved`)
                if r.name = "chargeMismatch" ∨ r.name = "stale" ∨ r.name = "idTaken" ∨
                    r.name = "floorNotConserved" then
                  { st with steps := st.steps + 1, refusedAsExpected := st.refusedAsExpected + 1 }
                else { st with failures := s!"probe: got {r.name}" :: st.failures }
            | .ok _ => { st with failures := "probe: wrong charge admitted" :: st.failures }
          match t.touches with
          | [] => st
          | x :: _ =>
              -- a cell touched twice is refused by shape, before anything is looked up
              let twice := { t with txId := P.env.hash "nanodregg/sim/probe2" (P.env.bytes t.txId), touches := t.touches ++ [x] }
              match World.admit P.env w twice with
              | .error (.duplicateTouch c) =>
                  if c = x.cell then
                    { st with steps := st.steps + 1, refusedAsExpected := st.refusedAsExpected + 1 }
                  else { st with failures := "probe: duplicateTouch names another cell" :: st.failures }
              | .error r => { st with failures := s!"probe twice: got {r.name}" :: st.failures }
              | .ok _ => { st with failures := "probe: a cell touched twice admitted" :: st.failures }

/-! ## Work per admitted turn (the waste ratchet's kernel rows)

Counted from the structure of `World.admit` (DERIVED from the code, not instrumented): `check`
does one World cell lookup per touch (`touchCheck` reads the cell once for its pin and its act) and
one per born id, one journal lookup and one spent lookup per nullifier; `commit` one insert per
written or retired touch, birth and nullifier, and one journal insert. Nothing in either is
proportional to the size of the World. -/

/-- Thousandths, as an integer: `WASTE` lines carry a decimal ratio. -/
def ratio (num den : Nat) : Nat := if den = 0 then 0 else num * 1000 / den

/-- Thousandths rounded UP: an exact row (counted ÷ required, 1 when nothing is wasted) reads above
1.000 at a single extra hash, however large the denominator. -/
def ratioUp (num den : Nat) : Nat := if den = 0 then 0 else (num * 1000 + den - 1) / den

def showRatio (milli : Nat) : String :=
  let frac := toString (milli % 1000)
  s!"{milli / 1000}.{"".pushn '0' (3 - frac.length)}{frac}"

/-- (World cell lookups ÷ cells named, map operations ÷ things named), in thousandths. (Pins
checked per pinned cell is no longer a ratio: a cell is touched once by shape, `duplicateTouch`.) -/
def turnWork (t : Turn D) : Nat × Nat :=
  let ids := createdIds t
  let cells := t.touches.map Touch.cell
  let named := (cells ++ ids).eraseDups.length
  let cellLookups := t.touches.length + ids.length
  let changed := (t.touches.filter fun x => x.act != .keep).length
  let ops := cellLookups + 1 + t.nullifiers.length +
    (changed + ids.length + t.nullifiers.length + 1)
  (ratio cellLookups named, ratio ops (named + t.nullifiers.length + 1))

def maxWork (log : List (Step D)) : Nat × Nat :=
  let log := Step.turns log
  log.foldl (fun (a, b) t => let (x, y) := turnWork t; (max a x, max b y)) (0, 0)

/-- Same contents and the same ROOTS (the four tries are canonical, so the same listing is the same
trie: KERNEL-41). -/
def same (E : Env D) (a b : World D) : Bool :=
  a.trie.toList == b.trie.toList && a.root E == b.root E && a.journal.toList == b.journal.toList &&
  a.journalRoot E == b.journalRoot E && a.refusals.toList == b.refusals.toList &&
  a.refusalsRoot E == b.refusalsRoot E && a.rows.toList == b.rows.toList &&
  a.rowsRoot E == b.rowsRoot E && a.steps == b.steps &&
  a.height == b.height && a.chain == b.chain && a.allowance == b.allowance && a.origin == b.origin

/-- A World rebuilt from its own listings, as a checkpoint decode does (CODEC-19): the four tries by
`Trie.build` (KERNEL-23, KERNEL-41: the same tries, `build_toList`). -/
def reopened (E : Env D) (w : World D) : World D :=
  let trie := Trie.build (trieSpec E) (trieSpec E).depth 0 w.trie.toList
  let journal := Trie.build (journalSpec E) (journalSpec E).depth 0 w.journal.toList
  let refusals := Trie.build (refusalSpec E) (refusalSpec E).depth 0 w.refusals.toList
  let rows := Trie.build (rowSpec E) (rowSpec E).depth 0 w.rows.toList
  { w with trie, journal, refusals, rows }

def worldName : ByteArray := "sim".toUTF8

/-- HOST draws a genesis nonce from the OS; the Sim's is a function of the seed (KERNEL-24). -/
def nonceOf (seed : Nat) : ByteArray := s!"sim-nonce-{seed}".toUTF8

/-- The log up to its last write, that write's values replaced and its charge re-priced: a log
`fold` accepts (later turns, which pinned the honest value, are cut) and no signed call derives. -/
def forge (log : List (Step D)) : Option (Nat × List (Step D)) :=
  -- a value cell's kernel keys are not forged here: the kernel itself refuses a forged balance
  -- (`valueMalformed`, `notConserved`), so such a log is not one `fold` accepts
  let valueKey (k : Nat) : Bool := k == Value.denomKey || k == Value.balanceKey || k == Value.floorKey
  let forged (x : Touch D) : Touch D := match x.act with
    | .write ops => { x with act := .write (ops.map fun o => match o with
        | .set k v => if valueKey k then .set k v else .set k "forged".toUTF8
        | o => o) }
    | _ => x
  let isWrite (t : Turn D) := t.touches.any fun x => match x.act with
    | .write ops => ops.any fun o => match o with | .set k _ => !valueKey k | _ => false
    | _ => false
  let turnAt : Step D × Nat → Option (Turn D × Nat)
    | (.turn t, i) => if isWrite t then some (t, i) else none
    | _ => none
  match (log.zipIdx.filterMap turnAt).getLast? with
  | none => none
  | some (t, i) =>
      let t0 := { t with touches := t.touches.map forged }
      let t1 := { t0 with charge := t0.weight }
      some (i, log.take i ++ [.turn t1])

/-- The genesis probe (KERNEL-31): past `Bounds.eventBytesMax` the raw codec truncates, so an
oversize founder key would give two geneses one origin with no hash collision. A third founder
whose key is one byte too long must be refused `founderKeyTooLong`, naming its index; the control
is the run's own genesis, which was admitted. -/
def probeGenesis (P : Params D) (st : State D) (founders : List (ByteArray × D)) : State D :=
  let long : ByteArray := ⟨Array.replicate (Bounds.eventBytesMax + 1) 7⟩
  let bad := founders ++ [(long, nextKeyDigest P.ctx (P.pub "f2-next".toUTF8))]
  match genesis P.ctx worldName (nonceOf 0) 100000000 bad Authority.none with
  | .error (.founderKeyTooLong i) =>
      if i = founders.length then
        { st with refusedAsExpected := st.refusedAsExpected + 1,
                  seen := "genesis-founder-key:founderKeyTooLong" :: "founderKeyTooLong" :: st.seen }
      else failWith st s!"probe genesis: founderKeyTooLong named founder {i}, not {founders.length}"
  | .error r => failWith st s!"probe genesis: expected founderKeyTooLong, got {r.name}"
  | .ok _ => failWith st "probe genesis: a founder key past eventBytesMax was admitted"

/-- An empty turn of the journal probe: transaction id `i`'s digest, window `[nb, vu]`, priced. -/
def journalTurn (P : Params D) (i nb vu : Nat) : Turn D :=
  let t0 : Turn D :=
    { txId := P.env.hash "nanodregg/sim/journal-tx" (toString i).toUTF8, notBefore := nb, validUntil := vu,
      touches := [], creates := [], nullifiers := [], charge := 0, event := ByteArray.empty,
      member := P.env.hash "nanodregg/sim/journal-tx" (toString i).toUTF8 }
  { t0 with charge := t0.weight }

/-- One verdict of the journal probe, by name. -/
def journalExpect (P : Params D) (st : State D) (w : World D) (t : Turn D) (what want : String) : State D :=
  let got := match World.admit P.env w t with
    | .ok _ => "ok"
    | .error r => r.name
  if got = want then
    { st with refusedAsExpected := st.refusedAsExpected + 1, seen := s!"{what}:{want}" :: want :: st.seen }
  else failWith st s!"probe journal {what}: expected {want}, got {got}"

/-- The journal probe (KERNEL-33), on seed 0: `3 * windowMax + 2` empty turns from an empty World,
turn `i` at height `i + 1` inside window `[i + 1, i + 1]`. Every World holds fewer than
`3 * windowMax` entries (`journal_bounded`), and every turn whose `notBefore + 2 * windowMax` is
above the height is still journaled (`fold_answers`). At the end: turn 0's entry is pruned; its
own window is refused `outsideWindow` (`journal-expired`), a kept entry's own window is refused
`outsideWindow` too, though its entry is there (`journal-window-first`: the window is checked
first, so pruning changes no verdict), a fresh window on a kept id is `replayed`
(`journal-kept`), and a fresh window on the pruned id is admitted (`journal-reuse`: at bare
`admit` two admissions of one id are only spaced, `admit_spacing`; `submit_once` is what makes a
call once). -/
def probeJournal (P : Params D) (st : State D) (seed : Nat) : State D :=
  if seed ≠ 0 then st else
  let W := Bounds.windowMax
  let n := 3 * W + 2
  let step := fun (acc : Except String (World D × Nat × Nat × List (Turn D) × Nat × Nat)) (i : Nat) =>
    match acc with
    | .error e => .error e
    | .ok (w, mx, scanned, log, ri, rp) =>
      let H := w.height + 1
      let scan := if H % W = 0 then w.journal.toList.length + 1 else 0
      let t := journalTurn P i H H
      match World.admit P.env w t with
      | .ok w' =>
          -- KERNEL-41: the journal write's hashes, counted at the window's steady state (up to
          -- `3 * windowMax` entries): the insert (`<K`) and, at a multiple of `windowMax`, the
          -- prune (`<R`), each under the counting Env; together they must reach the admitted
          -- World's journal root
          let cE := countingEnv P.env
          let ins := dbgTrace "<K" fun _ =>
            w.journal.insert (journalSpec cE) t.txId (H, turnDigest P.env t)
          let after := if H % W = 0 then dbgTrace "<R" fun _ => pruneJournal cE H ins else ins
          -- what they require (cv 01a14afe-7380), read off the uncounted journal before and after
          let JS := journalSpec P.env
          let insU := w.journal.insert JS t.txId (H, turnDigest P.env t)
          let ri := ri + Required.insertReq JS insU t.txId
          let rp := if H % W = 0 then rp + Required.fresh JS w'.journal insU else rp
          if after.hashOf (journalSpec P.env) != w'.journalRoot P.env then
            .error s!"the counted journal write at height {H} reached another journal root"
          else if w'.journal.toList.length < 3 * W then
            .ok (w', max mx w'.journal.toList.length, scanned + scan, t :: log, ri, rp)
          else .error s!"journal holds {w'.journal.toList.length} entries at height {w'.height}"
      | .error r => .error s!"journal turn {i} refused {r.name}"
  let g := World.genesis P.env P.zero 100000000
  match (List.range n).foldl step (.ok (g, 0, 0, [], 0, 0)) with
  | .error e => failWith st s!"probe journal: {e}"
  | .ok (w, mx, scanned, log, ri, rp) =>
      let st := { st with journalMax := mx, journalScanned := scanned, journalTurns := n,
                          probeInserts := n, prunes := n / W, probeInsertReq := ri, pruneReq := rp }
      let tx := fun i => P.env.hash "nanodregg/sim/journal-tx" (toString i).toUTF8
      let missing := (List.range n).filter fun i =>
        !journalForgets w.height (i + 1) && (w.journalAt P.env (tx i)).isNone
      if !missing.isEmpty then failWith st s!"probe journal: ids {missing.take 4} unanswered below journalForgets"
      else if (w.journalAt P.env (tx 0)).isSome then failWith st "probe journal: turn 0's entry was never pruned"
      else
        let H := w.height + 1
        let k := 2 * W + 5
        let st := journalExpect P st w (journalTurn P 0 1 1) "journal-expired" "outsideWindow"
        let st := journalExpect P st w (journalTurn P k (k + 1) (k + 1)) "journal-window-first" "outsideWindow"
        let st := journalExpect P st w (journalTurn P k H H) "journal-kept" "replayed"
        let st := journalExpect P st w (journalTurn P 0 H H) "journal-reuse" "ok"
        -- KERNEL-38: the real journal is the never-pruned one filtered at the last prune
        -- (`fold_journal_filter`), and the never-pruned World checks every windowed retry as the
        -- real one does (`fold_prune_check`); the fresh-window reuse is outside that premise and is
        -- the one place the two answer differently
        let J := shadowJournal P.env g.height g.journal (log.reverse.map .turn)
        let wS := { w with journal := J }
        -- the reference is `build` of the filtered never-pruned listing, not `retainAt`: so a prune
        -- that keeps the right entries in a non-canonical trie (no collapse) is red here by its root
        let kept' := J.toList.filter fun p => kept (lastPrune w.height) p.2
        let ref := Trie.build (journalSpec P.env) (journalSpec P.env).depth 0 kept'
        if w.journal.toList != kept' || w.journalRoot P.env != ref.hashOf (journalSpec P.env) then
          failWith st s!"probe journal shadow: the journal at height {w.height} is not the never-pruned one filtered at {lastPrune w.height}"
        else
          let st := { st with refusedAsExpected := st.refusedAsExpected + 1,
                              seen := "journal-shadow:filtered" :: "filtered" :: st.seen }
          -- KERNEL-39: the reached World's journal fits (`journalFits_of_ok`); one entry above the
          -- height, a second entry at a journaled height, or one past due for pruning, does not
          -- (`kernel/journal` at decode)
          let l := w.journal.toList
          let future := (tx (n + 7), (w.height + 1, P.zero)) :: l
          let twice := match l.head? with
            | some (_, (h, _)) => (tx (n + 8), (h, P.zero)) :: l
            | none => l
          let stale := (tx (n + 9), (0, P.zero)) :: l
          let st := if !(journalFits w.height l) then
              failWith st s!"probe journal: the journal at height {w.height} does not fit"
            else if journalFits w.height future || journalFits w.height twice || journalFits w.height stale then
              failWith st "probe journal: a future, a doubled or a stale entry fits"
            else { st with refusedAsExpected := st.refusedAsExpected + 1,
                           seen := "journal-fits:misfit" :: "misfit" :: st.seen }
          let st := journalExpect P st wS (journalTurn P k H H) "journal-shadow-kept" "replayed"
          journalExpect P st wS (journalTurn P 0 H H) "journal-shadow-reuse" "replayed"

/-! ### `retainAt`, the canonical erase (KERNEL-41) -/

/-- PLANT (`retainAt`'s tooth): `retainAll` with `join` replaced by `mkNode`, so a node left with one
key or none does not collapse. Same contents, a non-canonical trie: `probeRetain` must find its
root differs from `build`'s on some seed (arm `retain-plant:refuted`). -/
def plantRetainAll {K V D' : Type} (S : Trie.Spec K V D') (q : K → V → Bool) :
    Trie.T K V D' → Trie.T K V D' × Bool
  | .empty => (.empty, false)
  | .leaf h kvs =>
      if kvs.all (fun p => q p.1 p.2) then (.leaf h kvs, false)
      else
        let kept := kvs.filter fun p => q p.1 p.2
        if kept.isEmpty then (.empty, true) else (Trie.mkLeaf S kept, true)
  | .node h b rep l r =>
      let x := plantRetainAll S q l
      let y := plantRetainAll S q r
      if x.2 || y.2 then (Trie.mkNode S b rep x.1 y.1, true) else (.node h b rep l r, false)

/-- The plant's `retainAt` at path `[true]` (a node branching at bit 0 takes its right side; any
other is filtered whole, as `retainAt` does where the path has no bit `b`). -/
def plantRetainRight {K V D' : Type} (S : Trie.Spec K V D') (q : K → V → Bool) :
    Trie.T K V D' → Trie.T K V D'
  | .node h b rep l r =>
      if b = 0 then Trie.mkNode S b rep l (plantRetainAll S q r).1
      else (plantRetainAll S q (.node h b rep l r)).1
  | t => (plantRetainAll S q t).1

/-- The retain probe, every seed: a trie of up to 4 cells (tombstones) and 1–6 spent nullifiers;
`retainAt [true]` drops the nullifiers whose index meets the seed's stride and keeps every cell.
The result must be `build` of the filtered listing (`retainAt_eq_build`: same root, same listing,
no dropped key readable), and on some seed the non-collapsing plant must reach another root. -/
def probeRetain (P : Params D) (st : State D) (seed : Nat) : State D :=
  let E := P.env
  let S := trieSpec E
  let key := fun (tag : String) (i : Nat) => E.hash "nanodregg/sim/retain" s!"{tag}/{seed}/{i}".toUTF8
  let t0 : Cells D := (List.range (seed % 5)).foldl (fun t i => t.insert S (.cell (key "c" i)) (.entry .tomb)) .empty
  let nn := seed % 6 + 1
  let t := (List.range nn).foldl (fun t i => t.insert S (.nullifier (key "n" i)) .spent) t0
  let drop := fun (i : Nat) => (i + seed / 6) % 3 = 0 || (seed % 4 = 0 && i + 1 < nn)
  let dropped := ((List.range nn).filter drop).map fun i => Slot.nullifier (key "n" i)
  let q := fun (s : Slot D) (_ : Leaf) => !dropped.contains s
  let r := Trie.retainAt S q [true] t
  let b := Trie.build S S.depth 0 (t.toList.filter fun p => q p.1 p.2)
  let pl := plantRetainRight S q t
  if r.hashOf S != b.hashOf S || r.toList != b.toList then
    failWith st s!"probe retain: retainAt at seed {seed} is not build of the filtered listing"
  else if dropped.any fun s => (r.get S s).isSome then
    failWith st s!"probe retain: a dropped key is still readable at seed {seed}"
  else
    let st := meet st "retain:canonical"
    if pl.hashOf S != b.hashOf S then meet st "retain-plant:refuted" else st

/-- One verdict of the carry probe, by name: `submit` on the carried World. -/
def carryExpect (P : Params D) (st : State D) (w : World D) (c : Call D) (what want : String) : State D :=
  let got := match Receive.submit P.ctx w c with
    | .ok _ => "ok"
    | .error v => match v with
      | .refused r => r.name
      | .rejected r => r.name
  if got = want then
    { st with refusedAsExpected := st.refusedAsExpected + 1, seen := s!"{what}:{want}" :: want :: st.seen }
  else failWith st s!"probe {what}: expected {want}, got {got}"

/-- The call-signature domain (KERNEL-42): a fresh call signed over its bare unsigned bytes, without
`domCall`, is refused `badSignature` at the signature check, before any derivation (so it adds
no trie hash to the WASTE counts). That the same call signed over `callMessage` is admitted is
every other arm's `ok` (each call the generator signs). Arm `sig-bare:badSignature`. -/
def probeSigDomain (P : Params D) (st : State D) : State D :=
  let X := P.ctx
  let f := founder0 P st
  let c := signed P st f f.key (S.pinsFor P.env st.host [f.id]) (.create none [] [])
  let bare : Call D := { c with signature := P.sign f.key (X.unsignedBytes c.unsigned) }
  carryExpect P st st.host bare "sig-bare" "badSignature"

/-- Canonical state (cv 01a15412-44e2): a state's keys strictly ascend from `stateBase`
(`checkState`). On the Host's World, through `Receive.submit`, a create whose state is out of order or
repeats a key is refused `stateKey` (it used to be admitted: `slotsOf` sorted it, the last duplicate
winning); the control, the same keys ascending, is admitted. PLANT: the owner's invoke of a
programmed object under a program whose run returns its state out of order is refused `stateKey`;
the same program returning it ascending is admitted. Nothing is committed. Arms
`state-order-create:stateKey`, `state-dup-create:stateKey`, `state-order-control:ok`,
`state-order-run:stateKey`, `state-order-run-control:ok`. -/
def probeStateOrder (P : Params D) (st : State D) : State D :=
  let f := founder0 P st
  let mk := fun (state : Slots) =>
    signed P st f f.key (S.pinsFor P.env st.host [f.id]) (.create none [] state)
  let st := carryExpect P st st.host (mk [(stateBase + 1, nat 1), (stateBase, nat 0)])
    "state-order-create" "stateKey"
  let st := carryExpect P st st.host (mk [(stateBase, nat 0), (stateBase, nat 1)])
    "state-dup-create" "stateKey"
  let st := carryExpect P st st.host (mk [(stateBase, nat 0), (stateBase + 1, nat 1)])
    "state-order-control" "ok"
  match st.progs with
  | [] => st
  | (obj, owner) :: _ =>
    match st.members.find? (fun m => m.id = owner) with
    | none => failWith st "probe state-order: the object's owner is not a member"
    | some m =>
      let planted := fun (out : Slots) =>
        { P with ctx := { P.ctx with program := { P.ctx.program with
            run := fun look rv pkg state method args r budget =>
              (P.ctx.program.run look rv pkg state method args r budget).map
                fun (_, calls, rows, used) => (out, calls, rows, used) } } }
      let c := signed P st m m.key (S.pinsFor P.env st.host [m.id, obj])
        (.invoke obj 0 (nat st.steps) 1000 none)
      let st := carryExpect (planted [(stateBase + 1, nat 1), (stateBase, nat 0)]) st st.host c
        "state-order-run" "stateKey"
      carryExpect (planted [(stateBase, nat 0), (stateBase + 1, nat 1)]) st st.host c
        "state-order-run-control" "ok"

/-- The carry probe (KERNEL-29), at the end of every seed: the Host's World is carried under a new
nonce. The carried World holds the same trie, allowance, height and journal (`carry_carried`)
under a new origin; the last logged call is answered `replayed` at its height (`carry_replayed`:
answered, never re-run); a fresh call signed for the OLD World is `wrongWorld`; the same call
signed for the NEW World is admitted (`carry-new`); and a carry whose name is past the raw
codec's bound is refused `nameTooLong` (`carry_ok`). -/
def probeCarry (P : Params D) (st : State D) : State D :=
  let X := P.ctx
  let w := st.host
  let long : ByteArray := ⟨Array.replicate (Bounds.eventBytesMax + 1) 7⟩
  let st := match carry X long (nonceOf 7) w.origin w.carried with
    | .error .nameTooLong =>
        { st with refusedAsExpected := st.refusedAsExpected + 1,
                  seen := "carry-name:nameTooLong" :: "nameTooLong" :: st.seen }
    | .error r => failWith st s!"probe carry name: expected nameTooLong, got {r.name}"
    | .ok _ => failWith st "probe carry name: a name past eventBytesMax was carried"
  match carry X worldName (nonceOf 7) w.origin w.carried with
  | .error r => failWith st s!"probe carry: refused {r.name}"
  | .ok w' =>
    if !(w'.root P.env == w.root P.env && w'.allowance == w.allowance && w'.height == w.height &&
        w'.journal.toList == w.journal.toList && w'.journalRoot P.env == w.journalRoot P.env) then
      failWith st "probe carry: the carried World differs"
    else if w'.origin == w.origin then failWith st "probe carry: the carried World kept the old origin"
    else
      let st := match (Step.turns st.log).getLast? with
        | none => st
        | some t => match X.decodeCall t.event with
          | none => failWith st "probe carry: the last logged event does not decode"
          | some c =>
              let want := (w.journalAt P.env t.txId).map Prod.fst
              match Receive.submit X w' c, want with
              | .error (.rejected (.replayed h)), some h' =>
                  if h = h' then
                    { st with refusedAsExpected := st.refusedAsExpected + 1,
                              seen := "carry-old-call:replayed" :: "replayed" :: st.seen }
                  else failWith st s!"probe carry old-call: replayed at {h}, journaled at {h'}"
              | _, none => failWith st "probe carry old-call: the last logged turn is not journaled"
              | .error v, _ => failWith st s!"probe carry old-call: expected replayed, got {vname v}"
              | .ok _, _ => failWith st "probe carry old-call: a carried call was admitted again"
      let f := founder0 P st
      let old := signed P st f f.key (S.pinsFor P.env w [f.id]) (.create none [] [])
      let st := carryExpect P st w' old "carry-old-world" "wrongWorld"
      let fresh := signed P { st with host := w' } f f.key (S.pinsFor P.env w' [f.id]) (.create none [] [])
      carryExpect P st w' fresh "carry-new" "ok"

/-! ### Refusals (KERNEL-44, KERNEL-47): recorded, final, bounded, and only when authenticated -/

/-- A signed call with an explicit window (the generator's `signed` opens one at the next height). -/
def signedAt (P : Params D) (st : State D) (m : Member D) (key : ByteArray) (pins : List (D × D))
    (body : Body D) (nb vu : Nat) : Call D :=
  let u : Unsigned D :=
    { world := st.host.origin, member := m.id, key := P.pub key, notBefore := nb, validUntil := vu, pins,
      maxCharge := 1000000, body }
  { unsigned := u, signature := P.sign key (P.ctx.callMessage u) }

def arm (st : State D) (name : String) (ok : Bool) (msg : String) : State D :=
  if ok then meet st name else failWith st s!"probe refusals: {msg}"

/-- KERNEL-66's race, on a branch of the Host's World (the deployed `Receive.submit` and `Receive.judge`
on Worlds it builds from `st.host`, never committed: the Host's World, log and counters, which the
WASTE rows measure, are left as they were): an object under `grows` (a law that reads the OLD state),
and two writes signed against ONE observation of it. The first lands ("aa"). The second ("a") is
refused `stale` by `submit` (`race-loser:stale`) and DECLINED by `judge`: no record, no budget, not
final (`race-loser-declined:declined`). The tooth (`race-law:lawDenied`): `receive` on the World the
winner left refuses the loser `lawDenied` ("a" does not lengthen "aa"), which a judge that ran the
receivers before the pins recorded, charged and made final (the defect KERNEL-66 closes). -/
def probeRace (P : Params D) (st : State D) : State D :=
  let X := P.ctx
  let E := P.env
  let f := founder0 P st
  let ci := signed P st f f.key (S.pinsFor E st.host [f.id]) (.install grows)
  match Receive.submit X st.host ci with
  | .error v => failWith st s!"probe race: the grows law did not install ({vname v})"
  | .ok (ti, w1) =>
  match (createdIds ti).head? with
  | none => failWith st "probe race: the grows install bore no cell"
  | some gl =>
  let cc := signed P st f f.key (S.pinsFor E w1 [f.id, gl]) (.create none [gl] [(stateBase, ByteArray.empty)])
  match Receive.submit X w1 cc with
  | .error v => failWith st s!"probe race: the lawed object was not born ({vname v})"
  | .ok (tc, w2) =>
  match (createdIds tc).head? with
  | none => failWith st "probe race: the create bore no cell"
  | some r =>
  -- ONE observation; two calls signed against it
  let seen := S.pinsFor E w2 [f.id, r, gl]
  let win := signed P st f f.key seen (.write r [(0, some "aa".toUTF8)] none)
  let lose := signed P st f f.key seen (.write r [(0, some "a".toUTF8)] none)
  match Receive.submit X w2 win with
  | .error v => failWith st s!"probe race: the winner was not admitted ({vname v})"
  | .ok (_, w3) =>
  let st := match Receive.submit X w3 lose with
    | .error (.rejected (.stale _)) => meet st "race-loser:stale"
    | .error v => failWith st s!"probe race: the loser was {vname v}, not rejected stale"
    | .ok _ => failWith st "probe race: the loser was admitted"
  let st := match Receive.judge X w3 lose with
    | .declined (.rejected (.stale _)) => meet st "race-loser-declined:declined"
    | .recorded v _ _ => failWith st s!"probe race: the loser was RECORDED {vname v}"
    | .declined v => failWith st s!"probe race: the loser was declined {vname v}, not stale"
    | .admitted _ _ => failWith st "probe race: judge admitted the loser"
  match Receive.receive X w3 lose with
  | .error (.lawDenied _ _) => meet st "race-law:lawDenied"
  | .error e => failWith st s!"probe race: the law on the winner's state said {e.name}, not lawDenied (the race is blind)"
  | .ok _ => failWith st "probe race: the law admitted the loser's edit on the winner's state (the race is blind)"

/-- The refusals probe, from the founder's fresh budget (it runs before the random acts):
* `refusal-aba`: the A→B→A defect KERNEL-44 names, closed by versions (KERNEL-54). A call pinned to A
  is refused `stale` after a write to B and DECLINED (no record, no budget); the object is written back
  to A, and its pin does NOT return (`refusal-aba-pin:moved`: the version moved), so resubmitted the
  call is `stale` again. PLANT `refusal-aba-plant:returned`: the content did return to A, so the pin
  before KERNEL-54 (a content digest) would have matched. `refusal-stale-fold`: a Host that admits the
  call anyway is refused `stale` by the follower's fold at that step's index. `refusal-stale-rederive`: a
  log recording a stale refusal is refused `eventMismatch` by the follower's re-derivation (`judge`
  declines the stale call, so nothing re-derives the record: `rederiveStep_stale`).
* `refusal-early`: a call whose window has not opened is refused `outsideWindow` and NOT recorded
  (`World.refuse` itself refuses to: `refusal-early-kernel`); in its window it is admitted.
  PLANT `refusal-early-plant`: had it been recorded, its own window would refuse it `refusedFinal`.
* `refusal-rotate-stranger`: a stranger signs a rotation naming the founder with its own key: refused
  `notPrecommitted`, NOT recorded, the founder's count and the refusals root unmoved. PLANT
  `refusal-rotate-plant`: classified by `keyRule` (which skips the key for `rotate`) it would be
  authenticated, and `World.refuse` would take one of the founder's slots.
* `refusal-budget`: `missingCell` calls are recorded up to `Bounds.refusalsPerWindow`; the next is
  `refusalBudget`, not recorded.
* `refusals-counted`: the Host's World passes `refusalsCounted` (KERNEL-50). PLANT
  `refusals-counted-plant`: one of the founder's charges moved to another member, counts only; every
  leaf still fits (`refusalsFits`) and `refusalsCounted` refuses it.
* `refusals-full` (KERNEL-55 R1): the Host's World with its total at `Bounds.refusalsPerWindowMax`
  declines `refusalsFull` a record charged to a member with no count (the cap is not the member's
  budget); `refusals-full-control`: the Host's own World takes it. PLANT `refusals-full-plant`: the
  record committed past the cap leaves a total that misfits `refusalsFits`. PLANT
  `refusals-total-plant`: the total lowered by one fits, and `refusalsCounted` refuses it. The cap
  itself is not reached through `judge`: C = 16,384 records need over a thousand enrolled members at
  16 each, which a seed's founders cannot sign cheaply; the probe builds the World at the cap. -/
def probeRefusals (P : Params D) (st : State D) (g : World D) : State D :=
  let X := P.ctx
  let E := P.env
  let f := founder0 P st
  let mk := fun (st : State D) => submit P st (signed P st f f.key (S.pinsFor E st.host [f.id]) (.create none [] [])) .ok "refusal-object"
  let (st, t1) := mk st
  let (st, t2) := mk st
  match t1.bind (fun t => (createdIds t).head?), t2.bind (fun t => (createdIds t).head?) with
  | some o, some o2 =>
    let pinsNow := fun (st : State D) (x : D) => S.pinsFor E st.host [f.id, x]
    let wr := fun (st : State D) (x : D) (k : Nat) (v : String) (pins : List (D × D)) =>
      signed P st f f.key pins (.write x [(k, v.toUTF8)] none)
    -- KERNEL-54: A → B → (a call pinned to A, refused stale, DECLINED: never recorded) → A → the same
    -- call again, still stale: the object's pin names its version, so it never returns to A
    let (st, _) := submit P st (wr st o 1 "A" (pinsNow st o)) .ok "refusal-aba-a"
    let pinsA := pinsNow st o
    let contentA := (st.host.live E o).map E.cellBytes
    let (st, _) := submit P st (wr st o 1 "B" (pinsNow st o)) .ok "refusal-aba-b"
    let c := wr st o 1 "C" pinsA
    let root := st.host.refusalsRoot E
    let (st, _) := submit P st c (.rejected "stale") "refusal-aba-stale"
    let st := arm st "refusal-aba-declined:declined"
      ((st.host.refusalAt E (.tx (txIdOf X c))).isNone && st.host.refusalsRoot E == root)
      "a stale refusal was recorded"
    let (st, _) := submit P st (wr st o 1 "A" (pinsNow st o)) .ok "refusal-aba-a2"
    -- the content returned to A (the pin before KERNEL-54, a content digest, would match again: the
    -- PLANT), the versioned pin did not
    let st := arm st "refusal-aba-plant:returned" ((st.host.live E o).map E.cellBytes == contentA)
      "the object's content did not return to A (the plant is blind)"
    let st := arm st "refusal-aba-pin:moved" (pinsNow st o != pinsA) "the object's pin returned to A"
    let (st, _) := submit P st c (.rejected "stale") "refusal-aba"
    -- a Host that admits the call anyway is refused `stale` by the follower's fold at that step
    let st := match Receive.receive X st.host c with
      | .ok t =>
          match World.fold E g (st.log ++ [.turn t]) with
          | .error (i, .stale _) =>
              arm st "refusal-stale-fold:stale" (i == st.log.length) s!"the follower refused at {i}, not {st.log.length}"
          | .error (_, r) => failWith st s!"probe refusals: the follower refused the stale call's admission {r.name}"
          | .ok _ => failWith st "probe refusals: the follower admitted a stale call"
      | .error r => failWith st s!"probe refusals: the stale call did not derive ({r.name}): the fold plant is blind"
    -- a log that records a stale refusal: the kernel takes the record, the follower's re-derivation refuses it
    let rs := refusedOf X c (.rejected (.stale o))
    let st := match World.refuse E st.host rs, Receive.rederiveStep X st.host (.refusal rs) with
      | .ok _, .error (.refused .eventMismatch) => meet st "refusal-stale-rederive:eventMismatch"
      | .error e, _ => failWith st s!"probe refusals: the kernel refused the planted stale record {e.name} (the plant is blind)"
      | .ok _, _ => failWith st "probe refusals: the re-derivation took a recorded stale"
    let st := probeRace P st
    -- an early call: refused, not recorded, admitted in its window
    let H := st.host.height
    let ce := signedAt P st f f.key (pinsNow st o) (.write o [(2, "early".toUTF8)] none) (H + 3) (H + 50)
    let before := st.host.refusalsRoot E
    let (st, _) := submit P st ce (.rejected "outsideWindow") "refusal-early-refused"
    let st := arm st "refusal-early:declined" (st.host.refusalsRoot E == before) "an early refusal was recorded"
    let st := match World.refuse E st.host (refusedOf X ce (.rejected .outsideWindow)) with
      | .error .outsideWindow => meet st "refusal-early-kernel:outsideWindow"
      | _ => failWith st "probe refusals: World.refuse recorded an early call"
    let (st, _) := submit P st (wr st o2 1 "x" (pinsNow st o2)) .ok "refusal-early-advance"
    let (st, _) := submit P st (wr st o2 1 "y" (pinsNow st o2)) .ok "refusal-early-advance"
    let earlyCode := (Verdict.rejected (D := D) .outsideWindow).code
    let earlyRefusals := st.host.refusals.insert (refusalSpec E) (.refusal (.tx (txIdOf X ce))) (.refused (H + 1) earlyCode (refusedOf X ce (.rejected .outsideWindow)).member)
    let early := { st.host with refusals := earlyRefusals }
    let st := match Receive.submit X early ce with
      | .error (.rejected (.refusedFinal _)) => meet st "refusal-early-plant:refusedFinal"
      | _ => failWith st "probe refusals: a recorded early refusal did not finalize the call (the plant is blind)"
    let (st, _) := submit P st ce .ok "refusal-early-window"
    -- a stranger's rotation naming the founder
    let (thief, st) := freshKey st "stranger"
    let bad := signed P st f thief (S.pinsFor E st.host [f.id]) (.rotate (P.pub thief) (nextKeyDigest X (P.pub thief)))
    let cnt := refusalCount E st.host f.id
    let root := st.host.refusalsRoot E
    let (st, _) := submit P st bad (.refused "notPrecommitted") "refusal-rotate-stranger"
    let st := arm st "refusal-rotate-kept:declined"
      (refusalCount E st.host f.id == cnt && st.host.refusalsRoot E == root) "a stranger's rotation took the founder's slot"
    let plantAuth := match (do
        req (bad.unsigned.world = st.host.origin) Refusal.wrongWorld
        checkSignature X bad
        keyRule (pinned E st.host bad.unsigned.pins) bad.unsigned : Except (Refusal D) Unit) with
      | .ok () => true
      | .error _ => false
    let st := match plantAuth, World.refuse E st.host (refusedOf X bad (.refused (.notPrecommitted f.id))) with
      | true, .ok w' => arm st "refusal-rotate-plant:authenticated" (refusalCount E w' f.id == cnt + 1)
          "the keyRule plant did not take a slot"
      | _, _ => failWith st "probe refusals: the keyRule plant would not record the stranger (the plant is blind)"
    -- the budget: writes to ids that hold nothing (pinned absent: `missingCell`, a recorded class;
    -- KERNEL-54 took stale out of the record) until the founder's window is full, then one more
    let stale := fun (st : State D) (i : Nat) =>
      let ghost := E.hash "nanodregg/sim/absent" (s!"g{i}".toUTF8 ++ E.bytes st.host.chain)
      signed P st f f.key ((S.pinsFor E st.host [f.id]) ++ [(ghost, pinOf E none)]) (.write ghost [(3, s!"s{i}".toUTF8)] none)
    let st := (List.range (Bounds.refusalsPerWindow + 1)).foldl (fun st i =>
      if refusalCount E st.host f.id < Bounds.refusalsPerWindow then
        (submit P st (stale st i) (.refused "missingCell") "refusal-budget-fill").1
      else st) st
    let c17 := stale st 99
    let full := refusalCount E st.host f.id == Bounds.refusalsPerWindow
    let st := match Receive.judge X st.host c17 with
      | .declined (.rejected .refusalBudget) =>
          let (st, _) := submit P st c17 (.refused "missingCell") "refusal-budget-verdict"
          arm st "refusal-budget:refusalBudget"
            (full && (st.host.refusalAt E (.tx (txIdOf X c17))).isNone) "the refusal past the budget was stored"
      | _ => failWith st "probe refusals: the refusal past the member's budget was not refused refusalBudget"
    -- the counts are the records' (KERNEL-50): the Host's World passes `refusalsCounted`; the PLANT
    -- moves one of the founder's charges to another member (counts only), which every leaf check
    -- (`refusalsFits`) still admits and `refusalsCounted` refuses
    let st := arm st "refusals-counted:counted" (refusalsCounted E st.host) "the Host's World fails refusalsCounted"
    let w := st.host
    let r₁ := w.refusals.insert (refusalSpec E) (.refusal (.count f.id (refusalWindow w.height)))
      (.count (refusalCount E w f.id - 1))
    let r₂ := r₁.insert (refusalSpec E) (.refusal (.count o (refusalWindow w.height))) (.count (refusalCount E w o + 1))
    let moved : World D := { w with refusals := r₂ }
    let st := if f.id != o && 2 ≤ refusalCount E w f.id && refusalCount E w o < Bounds.refusalsPerWindow then
        arm st "refusals-counted-plant:refused"
          (refusalsFits moved.height moved.refusals.toList && !refusalsCounted E moved)
          "a moved charge passed refusalsCounted (or the plant misfit refusalsFits)"
      else failWith st "probe refusals: no member with two charges to move (the plant is blind)"
    -- KERNEL-55 R1, the World's cap: the Host's World with its total raised to C declines a record
    -- charged to a member with no count at all, `refusalsFull`; the same record on the Host's World is
    -- taken and bumps the total (the control); PLANT: committed past the cap, as a kernel without the
    -- check would, the total is C + 1 and misfits `refusalsFits`; PLANT: the total lowered by one fits
    -- and `refusalsCounted` refuses it
    let cur := refusalWindow w.height
    let rFull := { refusedOf X c17 (.rejected (.missingCell o)) with member := o }
    let rsFull := w.refusals.insert (refusalSpec E) (.refusal (.total w.origin cur)) (.count Bounds.refusalsPerWindowMax)
    let wFull : World D := { w with refusals := rsFull }
    let st := match World.refuse E wFull rFull, World.refuse E w rFull with
      | .ok _, _ => failWith st "probe refusals: a refusal past the World's cap was recorded"
      | .error .refusalsFull, .ok w1 =>
          let st := meet st "refusals-full:refusalsFull"
          let st := arm st "refusals-full-control:ok" (refusalTotal E w1 == refusalTotal E w + 1)
            "the control refusal did not bump the World's total"
          let over := commitRefusal E wFull rFull
          arm st "refusals-full-plant:overflow"
            (refusalTotal E over == Bounds.refusalsPerWindowMax + 1 && !refusalsFits over.height over.refusals.toList)
            "the uncapped commit's total still fits (the plant is blind)"
      | .error .refusalsFull, .error e => failWith st s!"probe refusals: the control refusal was refused {e.name}"
      | .error e, _ => failWith st s!"probe refusals: at the World's cap the refusal was refused {e.name}, not refusalsFull"
    let tot := refusalTotal E w
    let rsLow := w.refusals.insert (refusalSpec E) (.refusal (.total w.origin cur)) (.count (tot - 1))
    let lowered : World D := { w with refusals := rsLow }
    let st := if 2 ≤ tot then
        arm st "refusals-total-plant:refused"
          (refusalsFits lowered.height lowered.refusals.toList && !refusalsCounted E lowered)
          "a lowered total passed refusalsCounted (or the plant misfit refusalsFits)"
      else failWith st "probe refusals: fewer than two records this window (the total plant is blind)"
    st
  | _, _ => failWith st "probe refusals: the objects were not created"

/-- A forged turn that retires `id` (a live cell) and nothing else: the light turn of cv 01a14ba9-cbf4.
Its charge is its own weight; its credit is the retired cell's whole weight. -/
def retireTurn (P : Params D) (w : World D) (id : D) : Turn D :=
  let txId := P.env.hash "nanodregg/sim/forge" ("retire-budget".toUTF8 ++ P.env.bytes w.chain)
  let t0 : Turn D := ⟨txId, w.height + 1, w.height + 1, [⟨id, pinOf P.env (w.entry P.env id), .retire⟩], [], [], 0,
    ByteArray.empty, [], [], txId, 0⟩
  { t0 with charge := t0.weight }

/-- The budget probe (cv 01a14ba9-cbf4, `Kernel.Proofs.Budget`), at the end of every seed, on the
Host's World `w`:
* `carry-budget:allowanceTooLarge` — the crafted carry, `w`'s cells beside an allowance of 2^64 − 1,
  is refused by the checked carry (`CarryFits`'s budget clause);
* `carry-budget-edge:ok` — the same carry at allowance 2^64 − 1 − weight (the boundary) is admitted,
  and the light retire on it leaves storage plus allowance below 2^64 (`carry_fold_budget_lt`);
* `carry-budget-plant:overflow` — the PLANT: the crafted carry built UNCHECKED (`carryWorld`, what the
  old allowance-only check admitted), beside a crafted 1 KiB cell (KERNEL-68: a retire's record carries
  its member and ticks, 40 bytes more, so a seed's own cells can all be lighter than their retire),
  and the light retire of its heaviest retirable live cell carries the allowance to 2^64 or past it,
  outside the World codec's `u64`. The plant must reach the overflow, or the tooth is vacuous and the
  probe fails. -/
def probeCarryBudget (P : Params D) (st : State D) : State D :=
  let X := P.ctx
  let w := st.host
  let top := 2 ^ 64
  let live := (w.trie.toList.filterMap fun p => match p with
    | (.cell id, .entry (.live c _)) => some (id, c)
    | _ => none).mergeSort (fun a b => b.2.weight ≤ a.2.weight)
  let crafted : Carried D := { w.carried with allowance := top - 1 }
  let st := match carry X worldName (nonceOf 9) w.origin crafted with
    | .error .allowanceTooLarge =>
        { st with refusedAsExpected := st.refusedAsExpected + 1,
                  seen := "carry-budget:allowanceTooLarge" :: "allowanceTooLarge" :: st.seen }
    | .error r => failWith st s!"probe carry-budget: expected allowanceTooLarge, got {r.name}"
    | .ok _ => failWith st "probe carry-budget: an allowance of 2^64 - 1 beside live cells was carried"
  let st := match carry X worldName (nonceOf 9) w.origin { w.carried with allowance := top - 1 - w.weight } with
    | .error r => failWith st s!"probe carry-budget-edge: refused {r.name} at weight + allowance = 2^64 - 1"
    | .ok we =>
        let after := live.filterMap fun (id, _) => match World.admit P.env we (retireTurn P we id) with
          | .ok we' => some we'
          | .error _ => none
        if after.isEmpty then failWith st "probe carry-budget-edge: no light retire was admitted on the boundary carry"
        else if after.any (fun we' => decide (top ≤ we'.weight + we'.allowance)) then
          failWith st "probe carry-budget-edge: a retire carried storage plus allowance past 2^64"
        else { st with refusedAsExpected := st.refusedAsExpected + 1, seen := "carry-budget-edge:ok" :: st.seen }
  let heavyId := P.env.hash "nanodregg/sim/forge" ("carry-budget-heavy".toUTF8 ++ P.env.bytes w.chain)
  let heavy : Cell := ⟨0, .ram, [(0, ⟨Array.replicate 1024 0⟩)]⟩
  let unchecked := carryWorld X worldName (nonceOf 9) w.origin
    { crafted with trie := crafted.trie.insert (trieSpec P.env) (.cell heavyId) (.entry (.live heavy 0)) }
  let reached := ((heavyId, heavy) :: live).findSome? fun (id, _) =>
    match World.admit P.env unchecked (retireTurn P unchecked id) with
    | .ok w' => if top ≤ w'.allowance then some w'.allowance else none
    | .error _ => none
  match reached with
  | some _ => { st with refusedAsExpected := st.refusedAsExpected + 1,
                        seen := "carry-budget-plant:overflow" :: st.seen }
  | none => failWith st "probe carry-budget-plant: no light retire on the unchecked carry overflowed the allowance"

/-! ### Rows (KERNEL-46/48): keyed rows under a parent, through the REAL `World.admit`

The stub program declares no relation (`rels` is empty), so the Host's own log holds no rows and
every existing WASTE row is unmoved. The rows probe forges its turns on a side World that starts at
the Host's final World (as `probeValue` forges value turns): the World it continues with after a
refusal is the one before it, and `rowsAgree` compares that World with the Sim's own model of every
row after each step, so a refused turn that had moved a row, a head's count or its sum is red there.
The hashes of its admitted insert-only and retract-only turns are COUNTED (`countingEnv`, brackets
`<W`/`<V` and `<X`/`<Y`), and its range reads' listings are the kernel's own `under` reads. -/

/-- The probe's transaction id for `tag` on `w`. -/
def rowsTx (P : Params D) (w : World D) (tag : String) : D :=
  P.env.hash "nanodregg/sim/rows" (tag.toUTF8 ++ P.env.bytes w.chain)

/-- A forged rows turn on `w`: the given touches, births, row touches and range reads, re-priced, its
window open from the next height for 64 heights (so a turn built on `w` can follow another). -/
def rowsTurn (P : Params D) (w : World D) (tag : String) (touches : List (Touch D))
    (creates : List (D × Cell)) (rows : List (RowTouch D)) (ranges : List (RangeRead D)) : Turn D :=
  let t0 : Turn D :=
    { txId := rowsTx P w tag, notBefore := w.height + 1, validUntil := w.height + 64, touches, creates,
      nullifiers := [], charge := 0, event := ByteArray.empty, rows, ranges, member := rowsTx P w tag }
  { t0 with charge := t0.weight }

/-- A relation's head as `(count, sum)`. -/
def headCS (E : Env D) (w : World D) (p : D) (rel : Nat) : Option (Nat × Nat) :=
  (headOf E w.rows p rel).map fun h => (h.1, h.2.1)

/-- The rows the kernel lists for each of `t`'s range reads (`rangeRows`' own `under` call, at the
same arguments, on the pre-state it judges), counted into `rangeReads` and `rowsRead`; a read that
lists more than `most + 1` rows is red (the early stop, KERNEL-17 addendum 4). A read whose relation
is undeclared or whose prefix is wider than its keys never reaches the listing, and is not counted. -/
def countRangeReads (E : Env D) (st : State D) (w : World D) (t : Turn D) : State D :=
  t.ranges.foldl (fun st q =>
    match headOf E w.rows q.parent q.rel with
    | some (_, _, _, _, width, _) =>
        if q.pre.size ≤ width then
          let n := (under (rowSpec E) (rowsPrefix E q.parent q.rel width ++ q.pre) (q.most + 1) w.rows).length
          let st := { st with rangeReads := st.rangeReads + 1, rowsRead := st.rowsRead + n }
          if n ≤ q.most + 1 then st
          else failWith st s!"probe rows: a range read listed {n} rows, past most + 1 = {q.most + 1}"
        else st
    | none => st) st

/-- PLANT `hash-required:rows-rewalk` (cv 01a153a5-0e09): the rows run each touch on the trie in turn,
`rowsRun` before the overlay (`Kernel.Proofs.Admit.rowsRun_eq`: the same rows), each row and head write
rebuilding its path from the root. `report` requires it never to count below the real run (`<L`) and to
reach the same rows, and the insert turns' rows share with it in place of the run to read above their
requirement. -/
def plantRowsRewalk (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) (Rows D × Nat) := do
  let acc ← t.rows.foldlM (rowStepFreed E w t) (w.rows, 0)
  pure (dropHeads E t acc)

/-- The pre-overlay retirement path: seal the rows batch, then remove heads
one at a time. The retirement probe must measure this above its requirement. -/
def plantHeadsSeal (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) (Rows D × Nat) := do
  let acc ← t.rows.foldlM (rowStepFreedOn (uStore E) E w t) (.clean w.rows, 0)
  pure (dropHeads E t (acc.1.seal (rowSpec E), acc.2))

/-- PLANT `hash-required:rows-retract-seal` (cv 01a15460-e096): the rows overlay whose removal seals
the batch before it removes (`World.uStore.drop` before this cv: `.clean (retainAt … (u.seal))`), so a
retract splits the batch, and the nodes its re-join and the head write after it share are hashed again. -/
def sealStore (E : Env D) : RowStore D (Trie.U (RowSlot D) RowLeaf D) where
  get u s := Trie.U.getAt (rowSpec E) s 0 u
  ins u k v := Trie.insU (rowSpec E) k v 0 u
  drop u k := .clean (Trie.retainAt (rowSpec E) (fun k' _ => decide (k' ≠ k)) (rowPath E k) (u.seal (rowSpec E)))

/-- The rows run on `sealStore`. `report` requires it never to count below the real run (`<J`) and to
reach the same rows, and the retract turns' rows share with it in place of the run to read above their
requirement. -/
def plantRowsRetractSeal (E : Env D) (w : World D) (t : Turn D) : Except (Reject D) (Rows D × Nat) := do
  let acc ← t.rows.foldlM (rowStepFreedOn (sealStore E) E w t) (.clean w.rows, 0)
  pure (dropHeads E t (acc.1.seal (rowSpec E), acc.2))

/-- The counted hashes of one admitted rows turn `w → w'` whose row touches are all inserts, or all
retracts, and which reads no range: the whole REAL `World.admit` under the counting Env (`<W` for
inserts, `<X` for retracts), and everything its `commit` does besides the rows (`<V`, `<Y`: the cell
write, the journal write, the refusals prune and the three roots, sharing ONE empty-digest thunk in
`commit`'s order, so the empty digest is counted where `commit` first forces it). The difference is
the rows' share: the compiled admission's (`World.admitImpl`) one `rowsRun` in `checkWith`, and the
rows root `commitWith` takes. Each counted result must be what
the uncounted admission reached, or the counter changed the computation. The share is held to what
it requires (`Required.admit`'s rows part, plus the empty digest where the rows root alone forces
it). -/
def countRowsTurn (E : Env D) (st : State D) (w w' : World D) (t : Turn D) (stem : Bool := false) : State D :=
  let ins := t.rows.all fun x => match x.act with | .insert .. => true | _ => false
  let ret := t.rows.all fun x => match x.act with | .retract => true | _ => false
  if t.rows.isEmpty || !t.ranges.isEmpty || !(ins || ret) then st else
  match check E w t with
  | .error _ => failWith st "rows hash count: an admitted turn does not re-check"
  | .ok posts =>
      let cE := countingEnv E
      let whole := fun (_ : Unit) => World.admit cE w t
      let a := if stem then dbgTrace "<S" whole else if ins then dbgTrace "<W" whole else dbgTrace "<X" whole
      let base := fun (_ : Unit) =>
        let e : Thunk D := Thunk.mk fun _ => Trie.emptyHash (trieSpec cE)
        let trie := commitTrie cE w t posts
        let journal := commitJournal cE w t
        let refusals := pruneRefusals cE (w.height + 1) w.refusals
        (trie.rootWith (trieSpec cE) e, journal.rootWith (journalSpec cE) e, refusals.rootWith (refusalSpec cE) e)
      let b := if stem then dbgTrace "<T" base else if ins then dbgTrace "<V" base else dbgTrace "<Y" base
      -- the rows run alone (`<L`) and the re-walk plant (`<M`), on the insert turns
      let lm := if ins then
          some (dbgTrace "<L" fun _ => rowsRun cE w t, dbgTrace "<M" fun _ => plantRowsRewalk cE w t)
        else none
      let st := match lm with
        | some (.ok l, .ok m) => if l.1.hashOf (rowSpec E) == w'.rowsRoot E && m.1.hashOf (rowSpec E) == w'.rowsRoot E then st
            else failWith st "rows hash count: the rows run or the re-walk plant reached another rows root"
        | some _ => failWith st "rows hash count: the rows run or the re-walk plant refused an admitted turn"
        | none => st
      -- the rows run alone (`<J`) and the retract-seal plant (`<Z`), on the retract turns (cv 01a15460-e096)
      let jz := if ret then
          some (dbgTrace "<J" fun _ => rowsRun cE w t, dbgTrace "<Z" fun _ => plantRowsRetractSeal cE w t)
        else none
      let st := match jz with
        | some (.ok l, .ok m) => if l.1.hashOf (rowSpec E) == w'.rowsRoot E && m.1.hashOf (rowSpec E) == w'.rowsRoot E then st
            else failWith st "rows hash count: the rows run or the retract-seal plant reached another rows root"
        | some _ => failWith st "rows hash count: the rows run or the retract-seal plant refused an admitted turn"
        | none => st
      let st := match a with
        | .ok w'' => if w''.rowsRoot E == w'.rowsRoot E then st
            else failWith st "rows hash count: the counted admission reached another rows root"
        | .error _ => failWith st "rows hash count: the counted admission refused an admitted turn"
      let st := if b == (w'.root E, w'.journalRoot E, w'.refusalsRoot E) then st
        else failWith st "rows hash count: the counted non-rows share reached other roots"
      -- what the rows share requires: the row operations, and the empty digest when only the rows
      -- root forces it (the base's three roots share the copy the four would)
      match Required.admit E w t w' with
      | .error why => failWith st s!"rows hash required: {why}"
      | .ok q =>
          let three := if Required.isEmpty w'.trie || Required.isEmpty w'.journal || Required.isEmpty w'.refusals
            then 1 else 0
          let req := q.rows + (q.roots - three)
          if stem then { st with stemInserts := st.stemInserts + t.rows.length, stemReq := st.stemReq + req }
          else if ins then { st with rowInserts := st.rowInserts + t.rows.length, rowInsReq := st.rowInsReq + req }
          else { st with rowRetracts := st.rowRetracts + t.rows.length, rowRetReq := st.rowRetReq + req }

/-- One rows turn at the REAL `World.admit`, its range reads and (if admitted) its hashes counted:
the next World, or the refusal's name. -/
def rowsTry (P : Params D) (st : State D) (w : World D) (t : Turn D) (stem : Bool := false) :
    State D × Except String (World D) :=
  let st := countRangeReads P.env st w t
  match World.admit P.env w t with
  | .ok w' => (scanWorld P.env (countRowsTurn P.env st w w' t stem) w' "a rows turn's World", .ok w')
  | .error r => (st, .error r.name)

/-- The rows probe's monad: the Sim's state, and the first failure (which ends the probe). -/
abbrev RowsM (D : Type) [Ord D] (α : Type) := ExceptT String (StateM (State D)) α

def rowsStep (P : Params D) (w : World D) (t : Turn D) (stem : Bool := false) :
    RowsM D (Except String (World D)) := do
  let (st, r) := rowsTry P (← get) w t stem
  set st
  pure r

/-- A turn the probe needs admitted. -/
def rowsOk (P : Params D) (w : World D) (t : Turn D) (what : String) (stem : Bool := false) :
    RowsM D (World D) := do
  match ← rowsStep P w t stem with
  | .ok w' => pure w'
  | .error n => throw s!"{what}: refused {n}"

/-- Arm `arm:want`: the kernel refuses the turn by that exact name. -/
def rowsRefused (P : Params D) (w : World D) (t : Turn D) (arm want : String) : RowsM D Unit := do
  match ← rowsStep P w t with
  | .ok _ => throw s!"{arm}: admitted (expected {want})"
  | .error n => if n = want then modify (meet · s!"{arm}:{want}") else throw s!"{arm}: expected {want}, got {n}"

/-- Arm `arm` met when `ok`. -/
def hit (arm : String) (ok : Bool) (msg : String) : RowsM D Unit :=
  if ok then modify (meet · arm) else throw s!"{arm}: {msg}"

/-- The Sim's model of the probe's rows: `(rel, key, amt)` of every row it expects live under `p`. -/
abbrev RowModel := List (Nat × String × Nat)

/-- Where `w`'s rows under `p` (relations 0 and 1) differ from the model, if anywhere: a head's
count or sum that is not the model's, a modelled row missing or holding another amt, a row the model
does not hold, or a rows listing that does not fit or is not headed (`rowsFits`, `rowsHeaded`: what a
decoded base must satisfy). -/
def rowsDiff (E : Env D) (w : World D) (p : D) (model : RowModel) : Option String :=
  let rels := [0, 1]
  let heads := rels.filterMap fun rel =>
    let ms := model.filter (·.1 = rel)
    match headCS E w p rel with
    | some (c, s) =>
        if c = ms.length ∧ s = (ms.map (·.2.2)).sum then none
        else some s!"relation {rel}'s head holds ({c}, {s}), the model ({ms.length}, {(ms.map (·.2.2)).sum})"
    | none => some s!"relation {rel} has no head"
  let rows := model.filterMap fun m =>
    match rowAt E w.rows (.row ⟨p, m.1, m.2.1.toUTF8⟩) with
    | some (.row a _ _) => if a = m.2.2 then none else some s!"row {m.2.1} holds amt {a}, the model {m.2.2}"
    | _ => some s!"row {m.2.1} is missing"
  let listed := (w.rows.toList.filter fun x => match x.1 with
    | .row k => decide (k.parent = p) | _ => false).length
  let l := w.rows.toList
  match heads ++ rows with
  | f :: _ => some f
  | [] =>
      if listed ≠ model.length then some s!"{listed} rows listed, the model holds {model.length}"
      else if !(rowsFits E l && rowsHeaded l) then some "the rows listing does not fit or is not headed"
      else none

def rowsAgree (E : Env D) (w : World D) (p : D) (model : RowModel) (what : String) : RowsM D Unit :=
  match rowsDiff E w p model with
  | none => pure ()
  | some f => throw s!"{what}: the World differs from the model: {f}"

/-- The key of the listing's row with the greatest amt (the first, on a tie): a method's arg-max. -/
def argMaxAmt (l : List (RowSlot D × RowLeaf)) : Option ByteArray :=
  (l.foldl (fun best x => match x with
    | (.row k, .row a _ _) => match best with
        | some (_, b) => if b < a then some (k.k, a) else best
        | none => some (k.k, a)
    | _ => best) none).map (·.1)

/-! ### Pins across the compressed trie (KERNEL-49 (a), ROOT condition 2)

A pin is bytes a turn signs about what the World holds: a cell pin (`pinOf` of the live cell), a row
pin (`rowPin` of the leaf), a range pin (`rangePin` of the listing under a prefix). Path compression
changes how the trie is walked, never what a read returns, so every pin must equal the one computed
from a REFERENCE that does not walk the trie at all: an association list, and for a range the
reference listing sorted by key bytes. Each pin kind has a plant, a perturbed walk, that the
reference must catch. -/

/-- Byte strings in lexicographic order, a proper prefix first: for prefix-free keys, the trie's
order (bits most significant first, left before right). -/
def bytesLt (a b : ByteArray) : Bool := decide (a.toList < b.toList)

/-- The value at `k` in an association list (the last write wins). -/
def assoc {K V : Type} [DecidableEq K] (l : List (K × V)) (k : K) : Option V :=
  (l.reverse.find? fun p => p.1 = k).map (·.2)

/-- PLANT (the cell pin's): the uncompressed walk on the compressed shape, each node read at the bit
its DEPTH names (the old reader: one level per bit), not the bit it branches on. -/
def plantGetByDepth {K V D' : Type} [DecidableEq K] (S : Trie.Spec K V D') (k : K) :
    Nat → Trie.T K V D' → Option V
  | _, .empty => none
  | _, .leaf _ kvs => Trie.find k kvs
  | d, .node _ _ _ l r => if S.bit k d then plantGetByDepth S k (d + 1) r else plantGetByDepth S k (d + 1) l

/-- PLANT (the row pin's): the walk with its children swapped (bit 1 read left). -/
def plantGetSwapped {K V D' : Type} [DecidableEq K] (S : Trie.Spec K V D') (k : K) :
    Trie.T K V D' → Option V
  | .empty => none
  | .leaf _ kvs => Trie.find k kvs
  | .node _ b _ l r => if S.bit k b then plantGetSwapped S k l else plantGetSwapped S k r

/-- PLANT (the range pin's): `under` without its `rep` check, so a subtree the path reached on the
prefix's bits at its branchings is listed though its keys leave the prefix on a skipped bit. -/
def plantUnder {K V : Type} (S : Trie.Spec K V D) (pre : ByteArray) (n : Nat) : Trie.T K V D → List (K × V)
  | .empty => []
  | .leaf _ kvs => (kvs.filter fun p => startsWith pre (S.kbytes p.1)).take n
  | .node h b rep l r =>
      if b < 8 * pre.size then
        (if byteBit pre b then plantUnder S pre n r else plantUnder S pre n l)
      else takeList n (.node h b rep l r)

/-! ### The forgery tooth (KERNEL-49 (a), ROOT): a node hash without its branching bit

`Trie.nodeHash` commits `u16 b`. The plant hashes `tagged 2 (left ‖ right)`, its climb and its
exclusion check mirrored. Under it a proof may claim a branching bit the node does not have, steer
`k`'s walk into the other side and end at a leaf there that does not hold `k`: an exclusion proof of
a key the trie holds. The deployed `verifyExclusion` refuses the same proof against the real root. -/

def plantNodeHash {K V D' : Type} (S : Trie.Spec K V D') (l r : D') : D' :=
  S.hash (Trie.tagged 2 (S.dbytes l ++ S.dbytes r))

/-- A subtree's digest under the plant (its cached digests ignored below a leaf). -/
def plantHash {K V D' : Type} (S : Trie.Spec K V D') : Trie.T K V D' → D'
  | .empty => Trie.emptyHash S
  | .leaf h _ => h
  | .node _ _ _ l r => plantNodeHash S (plantHash S l) (plantHash S r)

/-- `Trie.proveAt` with the plant's sibling digests. -/
def plantProve {K V D' : Type} (S : Trie.Spec K V D') (k : K) : Trie.T K V D' → Trie.Proof K D'
  | .empty => ⟨none, []⟩
  | .leaf _ kvs => ⟨some (Trie.digests S kvs), []⟩
  | .node _ b _ l r =>
      if S.bit k b then let p := plantProve S k r; ⟨p.term, (b, plantHash S l) :: p.sibs⟩
      else let p := plantProve S k l; ⟨p.term, (b, plantHash S r) :: p.sibs⟩

/-- `Trie.climb` with the plant's node hash. -/
def plantClimb {K V D' : Type} (S : Trie.Spec K V D') (k : K) : List (Nat × D') → D' → D'
  | [], h => h
  | (b, s) :: rest, h =>
      let c := plantClimb S k rest h
      if S.bit k b then plantNodeHash S s c else plantNodeHash S c s

/-- `Trie.verifyExclusion` with the plant's climb (every other check kept). -/
def plantVerifyExclusion {K V D' : Type} [DecidableEq K] [DecidableEq D'] (S : Trie.Spec K V D')
    (root : D') (k : K) (p : Trie.Proof K D') : Bool :=
  Trie.ascends S 0 p.sibs &&
  (match p.term with
   | some kds => (Trie.find k kds).isNone
   | none => true) &&
  plantClimb S k p.sibs (Trie.termHash S p.term) = root

/-- The trie-shape probe, every seed, on tries of its own (no World): the forgery tooth
(`depth-unhashed-plant:caught`), a unary node refused by the shape scan every reached World passes
(`shape-unary-plant:caught`; the theorem is lane A's `canon_no_empty_child`), and the cell pin through the deployed read against
an association list (`pin-cell:same`) with its plant caught (`pin-cell-plant:caught`). -/
def probeTrieShape (P : Params D) (st : State D) (seed : Nat) : State D :=
  let E := P.env
  let S := trieSpec E
  let id := fun (tag : String) (i : Nat) => E.hash "nanodregg/sim/shape" s!"{tag}/{seed}/{i}".toUTF8
  -- nullifiers only: every key's bit 0 is set, so the root branches at a bit b ≥ 1
  let ns := (List.range (seed % 7 + 2)).map fun i => Slot.nullifier (id "n" i)
  let t : Cells D := ns.foldl (fun t n => t.insert S n .spent) .empty
  let st := match t with
    | .node _ b _ l r =>
        match l.first with
        | none => failWith st "probe shape: the root's left side is empty"
        | some k =>
            let q := plantProve S k r
            let forged : Trie.Proof (Slot D) D := ⟨q.term, (0, plantHash S l) :: q.sibs⟩
            let real : Trie.Proof (Slot D) D :=
              let q := r.prove S k
              ⟨q.term, (0, l.hashOf S) :: q.sibs⟩
            if b = 0 || (t.get S k).isNone then failWith st "probe shape: the forgery's premise (b ≥ 1, k held) failed"
            else if !plantVerifyExclusion S (plantHash S t) k forged then
              failWith st "probe shape: the depth-unhashed plant refused its own forgery (the tooth is blind)"
            else if Trie.verifyExclusion S (t.hashOf S) k real then
              failWith st "probe shape: an exclusion proof of a held key, claiming another branching bit, verified"
            else meet st "depth-unhashed-plant:caught"
    | _ => failWith st "probe shape: two or more nullifiers made no node"
  -- PLANT (the shape scan's): a unary node (one empty child) over the same keys. The scan the sim runs
  -- on every World it reaches must refuse it, and pass the deployed trie it wraps; beside that, the
  -- unary node does not hash as the canonical trie of its listing (history independence would break)
  let unary : Cells D := Trie.mkNode S 0 (ns.headD (.cell P.zero)) t .empty
  let canon := Trie.build S S.depth 0 unary.toList
  let st := if !shapeScanRoot S t then failWith st "probe shape: the deployed trie fails the shape scan"
    else if canon.hashOf S != t.hashOf S then failWith st "probe shape: the trie is not the build of its listing"
    else if shapeScanRoot S unary then failWith st "probe shape: the shape scan passed a unary node (the scan is blind)"
    else if unary.toList == canon.toList && unary.hashOf S != canon.hashOf S then meet st "shape-unary-plant:caught"
    else failWith st "probe shape: a unary node reached the canonical root"
  -- the cell pin: cells (live and tombstones) and nullifiers with ids sharing their first byte or not
  let cell := fun (i : Nat) => ({ kind := kindObject, discipline := .ram, slots := [(stateBase, nat i)] } : Cell)
  let ws : List (Slot D × Leaf) := (List.range (seed % 9 + 3)).map (fun i =>
      (Slot.cell (id "c" i), if i % 4 = 3 then Leaf.entry .tomb else .entry (.live (cell i) i))) ++
    ns.map (·, .spent) ++ [(Slot.cell (id "c" 0), .entry (.live (cell 100) 7))]
  let m : Cells D := ws.foldl (fun m p => m.insert S p.1 p.2) .empty
  let w : World D := { World.genesis E P.zero 0 with trie := m }
  let entryOf := fun (l : Option Leaf) => match l with
    | some (.entry e) => some e
    | _ => none
  let probes := (List.range (seed % 9 + 6)).map (id "c") ++ (List.range 3).map (id "absent")
  let same := probes.all fun c => pinOf E (w.entry E c) == pinOf E (entryOf (assoc ws (.cell c)))
  let plantMoved := probes.any fun c => pinOf E (entryOf (plantGetByDepth S (.cell c) 0 m)) != pinOf E (entryOf (assoc ws (.cell c)))
  let st := if same then meet st "pin-cell:same" else failWith st "probe shape: a cell pin differs from the association list's"
  if plantMoved then meet st "pin-cell-plant:caught" else st

/-- The rows reference of the probe's parent: both heads and every modelled row, in key-byte order,
built from the model alone (no trie). Versions (KERNEL-54), from the probe's history: relation 0's
floor is 2 (a1 retracted at version 0 raises it to 1, re-inserted at 1 and retracted again raises it
to 2), relation 1's is 0 (never retracted); every modelled row was inserted and never upserted, so its
version is its relation's floor when it landed, 0 for all of them (a0 and a2 landed before the first
retract). -/
def rowsReference (E : Env D) (p : D) (model : RowModel) : List (RowSlot D × RowLeaf) :=
  let ms := fun (rel : Nat) => model.filter (·.1 = rel)
  let heads : List (RowSlot D × RowLeaf) :=
    [(.head p 0, .head (ms 0).length ((ms 0).map (·.2.2)).sum 3 10 2 true 2),
     (.head p 1, .head (ms 1).length ((ms 1).map (·.2.2)).sum 8 1000 2 false 0)]
  let rows : List (RowSlot D × RowLeaf) := model.map fun m =>
    (.row ⟨p, m.1, m.2.1.toUTF8⟩, .row m.2.2 ("v-" ++ m.2.1).toUTF8 0)
  (heads ++ rows).mergeSort fun a b => bytesLt (rowKeyBytes E a.1) (rowKeyBytes E b.1)

/-- The floor a listing gives a row slot's relation (its head's), 0 where it holds no head. -/
def listedFloor (l : List (RowSlot D × RowLeaf)) : RowSlot D → Nat
  | .row k => match assoc l (.head k.parent k.rel) with
    | some (.head _ _ _ _ _ _ f) => f
    | _ => 0
  | .head .. => 0

/-- The row and range pins at `w` against the reference (`pin-row:same`, `pin-range:same`), and their
plants caught (`pin-row-plant:caught`, `pin-range-plant:caught`). -/
def pinsAgree (E : Env D) (w : World D) (p : D) (model : RowModel) : RowsM D Unit := do
  let ref := rowsReference E p model
  let slots : List (RowSlot D) := ref.map (·.1) ++
    [.row ⟨p, 0, "zz".toUTF8⟩, .row ⟨p, 1, "b9".toUTF8⟩, .row ⟨p, 1, "a".toUTF8⟩, .head p 2]
  let wfl := fun (s : RowSlot D) => match s with
    | .row k => headFloor E w.rows k.parent k.rel
    | .head .. => 0
  hit "pin-row:same" (slots.all fun s => rowPin E (wfl s) (rowAt E w.rows s) == rowPin E (listedFloor ref s) (assoc ref s))
    "a row pin differs from the reference listing's"
  hit "pin-row-plant:caught" (slots.any fun s =>
    rowPin E (wfl s) (plantGetSwapped (rowSpec E) s w.rows) != rowPin E (listedFloor ref s) (assoc ref s))
    "the swapped walk read every row pin right"
  let pres : List ByteArray := ["", "a", "b", "c", "d", "e", "f", "b0", "b1", "bz", "c0"].map String.toUTF8
  let refList := fun (rel : Nat) (pre : ByteArray) =>
    ref.filter fun x => startsWith (rowsPrefix E p rel 2 ++ pre) (rowKeyBytes E x.1)
  let honest := fun (rel : Nat) (pre : ByteArray) => (rangeRows E w.rows p rel 2 pre 100).getD []
  hit "pin-range:same" (pres.all fun pre => [0, 1].all fun rel =>
      rangePin E p rel 2 pre (headFloor E w.rows p rel) (honest rel pre) ==
        rangePin E p rel 2 pre (listedFloor ref (.row ⟨p, rel, pre⟩)) (refList rel pre) &&
        (rangeRows E w.rows p rel 2 pre 100).isSome)
    "a range pin differs from the reference listing's"
  hit "pin-range-plant:caught" (pres.any fun pre => [0, 1].any fun rel =>
      rangePin E p rel 2 pre (headFloor E w.rows p rel) (plantUnder (rowSpec E) (rowsPrefix E p rel 2 ++ pre) 101 w.rows) !=
        rangePin E p rel 2 pre (listedFloor ref (.row ⟨p, rel, pre⟩)) (refList rel pre))
    "the listing without the rep check pinned every range right"

/-- The stem probe (KERNEL-49 (a)): a parent born with one relation of key width 8, then 64 turns each
inserting one row whose key is a big-endian u64 counter, so the keys agree on their first 58 bits.
Each insert's hashes are counted (`<S` less `<T`; `stemWorst`, the most one insert cost). -/
def probeStem (P : Params D) (w0 : World D) : RowsM D Unit := do
  let E := P.env
  let cell : Cell := { kind := kindObject, discipline := .ram, slots := [(stateBase, nat 1)] }
  let p := cellIdOf E (rowsTx P w0 "stem-create") 0
  let decl : RowTouch D := { slot := .head p 0, seen := none, act := .declare 64 1000000 8 false }
  let w1 ← rowsOk P w0 (rowsTurn P w0 "stem-create" [] [(p, cell)] [decl] []) "stem: the parent's birth"
  let be := fun (i : Nat) => ByteArray.mk ((List.range 8).reverse.map fun j => (i >>> (8 * j)).toUInt8).toArray
  let wN ← (List.range 64).foldlM (fun w i => do
      let ins : RowTouch D := { slot := .row ⟨p, 0, be i⟩, seen := none, act := .insert 1 ByteArray.empty }
      rowsOk P w (rowsTurn P w s!"stem-{i}" [⟨p, pinOf E (w.entry E p), .keep⟩] [] [ins] []) s!"stem insert {i}" true) w1
  hit "rows-stem:ok" (headCS E wN p 0 == some (64, 64) &&
    (List.range 64).all fun i => (rowAt E wN.rows (.row ⟨p, 0, be i⟩)).isSome) "the 64 stem rows are not all there"

/-- The rows probe, at the end of every seed, on a side World from the Host's (`RowsM`'s note).
Relation 0 (limit 3, cap 10, key width 2, retractable) and relation 1 (limit 8, cap 1000, width 2,
not retractable) are declared by the turn that bears their parent, a data object; every row turn
pins the parent with `keep`. Arms, each by its exact name:
* `rows-insert:ok` — an insert moves the head from (0, 0) to (1, amt) and the row is there;
* `rows-keyTaken:keyTaken` — the same key again; `rows-relationCapped:relationCapped` — an amt past
  the cap; `rows-relationFull:relationFull` — a fourth row in a relation of limit 3;
* `rows-retract:ok` — a pinned retract removes the row and takes its amt off the head;
  `rows-retractForbidden:retractForbidden` — a retract in relation 1;
* `rows-rangeTooLong:rangeTooLong` — a range whose listing passes `most` (refused, never truncated);
  `rows-range:ok` — the same range under its honest pin and a `most` it fits;
* `rows-range-stale:stale` — a range pin taken, a row lands under its prefix, the read with the old
  pin is `stale`; under the new pin it is admitted;
* `rows-two-rains:both` — two turns built on ONE World, each inserting its own key into relation 1
  and pinning the parent `keep`: both admit in either order, each order ends at count + 2 and
  sum + a₁ + a₂, and the two orders reach the same rows root and the same cells root.
Plants, each a kernel misbehaviour the probe must catch by name:
* `rows-taken-plant:caught` — the insert of a taken key let through (`rowStep`'s insert without its
  `keyTaken` check: the leaf overwritten, the head counted up): the World it commits differs from the
  model (`rowsDiff`: the head counts two rows over one, and the row's amt is overwritten);
* `rows-range-drop-plant:stale` — a listing with its arg-max row dropped: its pin differs from the
  honest one, the kernel refuses a read under it `stale`, and its arg-max is another key;
* `rows-repin-plant:stale` — the first rain also WRITES the parent: the second rain's `keep` pin is
  then stale and refused, though the other order admits both. Neither rain writing a cell the other
  pins is the premise under which `rows-two-rains:both` holds (KERNEL-46's `admit_comm`: the head
  update is additive and unpinned, so two inserts under one relation commute). -/
def probeRows (P : Params D) (seed : Nat) : RowsM D Unit := do
  let E := P.env
  let w0 := (← get).host
  let cell : Cell := { kind := kindObject, discipline := .ram, slots := [(stateBase, nat 0)] }
  let p := cellIdOf E (rowsTx P w0 "create") 0
  let decl := fun (rel limit cap width : Nat) (retract : Bool) =>
    ({ slot := .head p rel, seen := none, act := .declare limit cap width retract } : RowTouch D)
  let w1 ← rowsOk P w0 (rowsTurn P w0 "create" [] [(p, cell)] [decl 0 3 10 2 true, decl 1 8 1000 2 false] [])
    "the parent's birth with its relations"
  rowsAgree E w1 p [] "after the declares"
  -- A real admitted retirement shares its rows seal with a new parent's heads.
  let q := cellIdOf E (rowsTx P w1 "retire-and-birth") 0
  let replacement := rowsTurn P w1 "retire-and-birth"
    [⟨p, pinOf E (w1.entry E p), .retire⟩] [(q, cell)]
    ((List.range 8).map fun i => ⟨.head q i, none, .declare 8 1000 2 true⟩) []
  let wr ← rowsOk P w1 replacement "rows-retire-heads"
  let cE := countingEnv E
  let current := dbgTrace "<D" fun _ => rowsRun cE w1 replacement
  let planted := dbgTrace "<I" fun _ => plantHeadsSeal cE w1 replacement
  hit "rows-retire-heads:equal"
    (match current, planted with
     | .ok a, .ok b => a.1.hashOf (rowSpec E) == wr.rowsRoot E &&
         b.1.hashOf (rowSpec E) == wr.rowsRoot E && a.2 == b.2 &&
         (under (rowSpec E) (E.bytes p) 257 wr.rows).isEmpty
     | _, _ => false) "overlay and seal-before-heads disagree"
  let needed := Required.rowsReq E w1 replacement
    (fun k => (wr.rows.get (rowSpec E) k).getD Required.rowDummy)
  modify fun st => { st with retireHeadsReq := st.retireHeadsReq + needed.2 }
  -- One changed leaf in the real deployed trie must change its root.
  let changed := w1.trie.insert (trieSpec E) (.cell p) (.entry .tomb)
  hit "trie-binding:one-leaf" (changed.hashOf (trieSpec E) != w1.root E)
    "changing a live leaf to a tomb kept the root"

  let keep := fun (w : World D) => (⟨p, pinOf E (w.entry E p), .keep⟩ : Touch D)
  let fl := fun (w : World D) (rel : Nat) => headFloor E w.rows p rel
  let key := fun (rel : Nat) (k : String) => (⟨p, rel, k.toUTF8⟩ : RowKey D)
  let ins := fun (rel : Nat) (k : String) (amt : Nat) =>
    ({ slot := .row (key rel k), seen := none, act := .insert amt ("v-" ++ k).toUTF8 } : RowTouch D)
  let insT := fun (w : World D) (tag : String) (xs : List (RowTouch D)) => rowsTurn P w tag [keep w] [] xs []
  -- relation 0: insert, a taken key, the cap, the limit, a retract
  let w2 ← rowsOk P w1 (insT w1 "insert-a0" [ins 0 "a0" 2]) "rows-insert"
  hit "rows-insert:ok" (headCS E w1 p 0 == some (0, 0) && headCS E w2 p 0 == some (1, 2) &&
    rowAt E w2.rows (.row (key 0 "a0")) == some (.row 2 "v-a0".toUTF8 0)) "the head or the row did not move"
  let m2 : RowModel := [(0, "a0", 2)]
  rowsAgree E w2 p m2 "rows-insert"
  rowsRefused P w2 (insT w2 "taken" [ins 0 "a0" 1]) "rows-keyTaken" "keyTaken"
  -- PLANT (a): the same insert let through, as `rowStep` would commit it without `keyTaken`
  let planted := match headOf E w2.rows p 0 with
    | some (c, s, l, cap, wd, r) =>
        let over := w2.rows.insert (rowSpec E) (.row (key 0 "a0")) (.row 1 "v-a0".toUTF8 0)
        let rows := setHead E over p 0 (c + 1) (s + 1) l cap wd r (fl w2 0)
        some { w2 with rows }
    | none => none
  hit "rows-taken-plant:caught"
    (match planted with
     | some wp => (rowsDiff E wp p m2).isSome && !rowsHeaded wp.rows.toList
     | none => false) "a taken key let through left a World the model and rowsHeaded accept"
  rowsRefused P w2 (insT w2 "capped" [ins 0 "a1" 9]) "rows-relationCapped" "relationCapped"
  rowsAgree E w2 p m2 "after the refusals"
  let w3 ← rowsOk P w2 (insT w2 "fill" [ins 0 "a1" 3, ins 0 "a2" 1]) "rows-fill"
  let m3 : RowModel := m2 ++ [(0, "a1", 3), (0, "a2", 1)]
  rowsAgree E w3 p m3 "rows-fill"
  rowsRefused P w3 (insT w3 "full" [ins 0 "a3" 0]) "rows-relationFull" "relationFull"
  let pinA1 := rowPin E (fl w3 0) (rowAt E w3.rows (.row (key 0 "a1")))
  let w4 ← rowsOk P w3 (rowsTurn P w3 "retract" [keep w3] []
    [{ slot := .row (key 0 "a1"), seen := some pinA1, act := .retract }] []) "rows-retract"
  hit "rows-retract:ok" (headCS E w4 p 0 == some (2, 3) && (rowAt E w4.rows (.row (key 0 "a1"))).isNone)
    "the retract left the row or the head"
  let m4 : RowModel := [(0, "a0", 2), (0, "a2", 1)]
  rowsAgree E w4 p m4 "rows-retract"
  -- KERNEL-54: a row's absence recurs (re-insert, retract again), its pin does not: each retract
  -- raises the relation's floor past the row it removes, so the first absence's pin is behind
  let absA1 := rowPin E (fl w4 0) (rowAt E w4.rows (.row (key 0 "a1")))
  let w4a ← rowsOk P w4 (insT w4 "reinsert-a1" [ins 0 "a1" 3]) "rows-aba's re-insert"
  let pinA1b := rowPin E (fl w4a 0) (rowAt E w4a.rows (.row (key 0 "a1")))
  let w4b ← rowsOk P w4a (rowsTurn P w4a "re-retract" [keep w4a] []
    [{ slot := .row (key 0 "a1"), seen := some pinA1b, act := .retract }] []) "rows-aba's re-retract"
  hit "rows-aba-floor:moved" (fl w4 0 == 1 && fl w4b 0 == 2 && (rowAt E w4b.rows (.row (key 0 "a1"))).isNone &&
    absA1 != rowPin E (fl w4b 0) none) "the absence after the second retract pinned as the first"
  rowsRefused P w4b (rowsTurn P w4b "aba-old-absence" [keep w4b] []
    [{ slot := .row (key 0 "a1"), seen := some absA1, act := .keep }] []) "rows-aba" "stale"
  rowsRefused P w4b (rowsTurn P w4b "retract-absent" [keep w4b] []
    [{ slot := .row (key 0 "a1"), seen := some (rowPin E (fl w4b 0) none), act := .retract }] [])
    "rows-missingRow" "missingRow"
  let w4 := w4b
  rowsAgree E w4 p m4 "rows-aba"
  -- relation 1: rows, a forbidden retract, range reads
  let w5 ← rowsOk P w4 (insT w4 "rel1" [ins 1 "b0" 5, ins 1 "b1" 7, ins 1 "c0" 1]) "rows-rel1"
  let m5 : RowModel := m4 ++ [(1, "b0", 5), (1, "b1", 7), (1, "c0", 1)]
  rowsAgree E w5 p m5 "rows-rel1"
  rowsRefused P w5 (rowsTurn P w5 "retract-forbidden" [keep w5] []
    [{ slot := .row (key 1 "b0"), seen := some (rowPin E (fl w5 1) (rowAt E w5.rows (.row (key 1 "b0")))), act := .retract }] [])
    "rows-retractForbidden" "retractForbidden"
  let pre := "b".toUTF8
  let listing := fun (w : World D) (most : Nat) => rangeRows E w.rows p 1 2 pre most
  let range := fun (most : Nat) (seen : D) => ({ parent := p, rel := 1, pre, most, seen } : RangeRead D)
  let readT := fun (w : World D) (tag : String) (q : RangeRead D) => rowsTurn P w tag [keep w] [] [] [q]
  rowsRefused P w5 (readT w5 "range-long" (range 1 P.zero)) "rows-rangeTooLong" "rangeTooLong"
  let some l5 := listing w5 4 | throw "rows-range: the honest listing passed most"
  let pin5 := rangePin E p 1 2 pre (fl w5 1) l5
  let w6 ← rowsOk P w5 (readT w5 "range" (range 4 pin5)) "rows-range"
  hit "rows-range:ok" (l5.length == 2) s!"the listing under b holds {l5.length} rows, not 2"
  rowsAgree E w6 p m5 "rows-range"
  -- PLANT (b): the listing with its arg-max row dropped
  let top := argMaxAmt l5
  let dropped := l5.filter fun x => match x.1 with | .row k => some k.k != top | _ => true
  let pinD := rangePin E p 1 2 pre (fl w6 1) dropped
  match ← rowsStep P w6 (readT w6 "range-drop" (range 4 pinD)) with
  | .error "stale" =>
      hit "rows-range-drop-plant:stale" (pinD != pin5 && dropped.length + 1 == l5.length &&
        argMaxAmt dropped != top && top == some "b1".toUTF8) "the dropped listing's pin or arg-max agreed with the honest one"
  | .error n => throw s!"rows-range-drop-plant: expected stale, got {n}"
  | .ok _ => throw "rows-range-drop-plant: a read under the dropped listing's pin was admitted"
  -- a range pin taken, then a row lands under its prefix
  let some l6 := listing w6 4 | throw "rows-range-stale: the honest listing passed most"
  let pin6 := rangePin E p 1 2 pre (fl w6 1) l6
  let w7 ← rowsOk P w6 (insT w6 "lands" [ins 1 "b2" 2]) "rows-range-stale's insert"
  let m7 : RowModel := m5 ++ [(1, "b2", 2)]
  rowsRefused P w7 (readT w7 "range-old-pin" (range 4 pin6)) "rows-range-stale" "stale"
  let some l7 := listing w7 4 | throw "rows-range-stale: the new listing passed most"
  let w8 ← rowsOk P w7 (readT w7 "range-new-pin" (range 4 (rangePin E p 1 2 pre (fl w7 1) l7))) "rows-range-stale's re-read"
  rowsAgree E w8 p m7 "rows-range-stale"
  pinsAgree E w8 p m7
  -- two rains on one World
  let a1 := seed % 7 + 1
  let a2 := seed % 5 + 2
  let r1 := insT w8 "rain-1" [ins 1 "d1" a1]
  let r2 := insT w8 "rain-2" [ins 1 "d2" a2]
  let x1 ← rowsOk P w8 r1 "rows-two-rains: the first rain first"
  let x12 ← rowsOk P x1 r2 "rows-two-rains: the second rain second"
  let y2 ← rowsOk P w8 r2 "rows-two-rains: the second rain first"
  let y21 ← rowsOk P y2 r1 "rows-two-rains: the first rain second"
  let some (c8, s8) := headCS E w8 p 1 | throw "rows-two-rains: relation 1 has no head"
  hit "rows-two-rains:both" (headCS E x12 p 1 == some (c8 + 2, s8 + a1 + a2) &&
    headCS E y21 p 1 == some (c8 + 2, s8 + a1 + a2) && x12.rowsRoot E == y21.rowsRoot E &&
    x12.root E == y21.root E) "the two orders reached other heads or other roots"
  let m9 : RowModel := m7 ++ [(1, "d1", a1), (1, "d2", a2)]
  rowsAgree E x12 p m9 "rows-two-rains (1, 2)"
  rowsAgree E y21 p m9 "rows-two-rains (2, 1)"
  -- PLANT (c): the first rain also writes the parent cell
  let r1w := rowsTurn P w8 "rain-1-repin" [{ (keep w8) with act := .write [.set stateBase (nat 1)] }] [] [ins 1 "d1" a1] []
  let z1 ← rowsOk P w8 r1w "rows-repin-plant: the writing rain"
  let z2 ← rowsOk P w8 r2 "rows-repin-plant: the second rain first"
  let _ ← rowsOk P z2 r1w "rows-repin-plant: the writing rain second"
  match ← rowsStep P z1 r2 with
  | .error "stale" => modify (meet · "rows-repin-plant:stale")
  | .error n => throw s!"rows-repin-plant: expected stale, got {n}"
  | .ok _ => throw "rows-repin-plant: a rain admitted after the other rain re-wrote the parent it pins"
  probeStem P w0

def run (P : Params D) (seed : Nat) (steps : Nat) : State D :=
  let rng : Rng := ⟨seed.toUInt64 * 0x2545F4914F6CDD1D + 1⟩
  let fk : List (ByteArray × ByteArray) :=
    [("f0".toUTF8, "f0-next".toUTF8), ("f1".toUTF8, "f1-next".toUTF8)]
  let X := P.ctx
  let founders := fk.map fun (k, n) => (P.pub k, nextKeyDigest X (P.pub n))
  match genesis X worldName (nonceOf seed) 100000000 founders Authority.none with
  | .error r =>
      { rng, host := World.genesis P.env P.zero 0, members := [], failures := [s!"genesis refused {r.name}"] }
  | .ok g =>
  let members := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Member D)
  let holds := (List.range fk.length).map fun i =>
    (founderId X g.origin i, (⟨[founderGrantId X g.origin i], true, enrollMax⟩ : Holding D))
  let st0 : State D := { rng, host := g, members, holds }
  let st0 := probeTrieShape P (probeRetain P (probeJournal P (probeGenesis P st0 founders) seed) seed) seed
  -- install the deny-all law package first
  let f := founder0 P st0
  let c := signed P st0 f f.key (S.pinsFor P.env g [f.id]) (.install denyAll)
  let (st, t) := submit P st0 c .ok "install"
  let st := { st with denyPkg := t.bind fun t => (createdIds t).head? }
  let (st, t) := submit P st (signed P st f f.key (S.pinsFor P.env st.host [f.id]) (.install freeze)) .ok "install"
  let st := { st with freezePkg := t.bind fun t => (createdIds t).head? }
  let (st, t) := submit P st (signed P st f f.key (S.pinsFor P.env st.host [f.id]) (.install methods)) .ok "install"
  let st := { st with methodsPkg := t.bind fun t => (createdIds t).head? }
  let st := probeRefusals P st g
  let st := (List.range steps).foldl (fun st _ =>
    let st := scanValue P (act P st)
    -- restart: the Host reopens by folding its own log from genesis
    let (r, rng) := st.rng.below 16
    let st := { st with rng }
    if r = 0 then
      match World.fold P.env g st.log with
      | .ok w => if same P.env w st.host then { st with host := w, restarts := st.restarts + 1 }
          else { st with failures := "restart: reopened World differs" :: st.failures }
      | .error (i, r) => { st with failures := s!"restart: fold refused at {i}: {r.name}" :: st.failures }
    else if r = 1 then
      -- a checkpoint reopen: both tries rebuilt from their listings (the same tries:
      -- `Trie.build_toList`, so the same World, `=`)
      let w := reopened P.env st.host
      if same P.env w st.host then { st with host := w, restarts := st.restarts + 1 }
      else { st with failures := "checkpoint: the rebuilt trie differs (root or listing)" :: st.failures }
    else st) st
  let st := scanWorld P.env st st.host "the Host's World at the seed's end"
  -- the fold and the follower's re-derivation, from genesis
  let st := match World.fold P.env g st.log with
    | .ok w =>
        if !same P.env w st.host then { st with failures := "follower differs" :: st.failures }
        else
          -- the Host's proofs verify against the follower's root (KERNEL-23 (g))
          let S := trieSpec P.env
          let ok := match (Step.turns st.log).getLast? with
            | none => true
            | some t => (changedSlots t).all fun s => match st.host.trie.get S s with
                | some l => Trie.verifyInclusion S (w.root P.env) s (leafDigest P.env l) (st.host.trie.prove S s)
                | none => false
          if ok then st else { st with failures := "follower: a Host proof does not verify at the follower's root" :: st.failures }
    | .error (i, r) => { st with failures := s!"follower refused at {i}: {r.name}" :: st.failures }
  let st := match rederiveLog P.ctx g st.log with
    | .ok w => if same P.env w st.host then st else { st with failures := "re-derivation differs" :: st.failures }
    | .error (i, f) => { st with failures := s!"re-derivation refused at {i}: {vname f}" :: st.failures }
  -- a forged refusal record: its code changed; `fold` keeps it (the kernel cannot see the code was
  -- not the call's), `rederiveLog` re-judges the call and names the step
  let st := match (st.log.zipIdx.filterMap fun (s, i) => match s with
      | .refusal r => some (r, i) | _ => none).head? with
    | none => failWith st "refusals: the log recorded none"
    | some (r, i) =>
        let bad := st.log.set i (.refusal { r with code := r.code + 1 })
        match World.fold P.env g bad, rederiveLog P.ctx g bad with
        | .ok _, .error (j, .refused .eventMismatch) =>
            arm st "refusal-forged-code:eventMismatch" (i == j) s!"forged refusal at {i} named at {j}"
        | .ok _, .error (j, v) => failWith st s!"forged refusal at {i}: the re-derivation said {vname v} at {j}"
        | .ok _, .ok _ => failWith st s!"forged refusal at {i}: the re-derivation accepted"
        | .error _, _ => failWith st s!"forged refusal at {i}: fold refused it (not a forgery test)"
  let st := probeSigDomain P st
  let st := probeStateOrder P st
  let st := probeCarry P st
  let st := probeCarryBudget P st
  let st := match ((probeRows P seed).run).run st with
    | (.ok (), st) => st
    | (.error f, st) => failWith st s!"probe rows: {f}"
  -- KERNEL-24: the same log's calls against a second genesis (same name and founders, another
  -- nonce) are each refused `wrongWorld`; another nonce, or the founders swapped, is another chain
  match genesis X worldName (nonceOf (seed + 1000000)) 100000000 founders Authority.none with
  | .error r => failWith st s!"second genesis refused {r.name}"
  | .ok g2 =>
  let st := st.log.foldl (fun st s =>
    let event := match s with | .turn t => t.event | .refusal r => r.event
    match X.decodeCall event with
    | none => { st with failures := "replay elsewhere: a logged event does not decode" :: st.failures }
    | some c =>
        match Receive.submit X g2 c with
        | .error (.refused .wrongWorld) =>
            { st with refusedAsExpected := st.refusedAsExpected + 1, seen := "wrongWorld" :: st.seen }
        | .error v => { st with failures := s!"replay elsewhere: got {vname v}" :: st.failures }
        | .ok _ => { st with failures := "replay elsewhere: admitted on a second World" :: st.failures }) st
  match genesis X worldName (nonceOf seed) 100000000 founders.reverse Authority.none with
  | .error r => failWith st s!"swapped genesis refused {r.name}"
  | .ok swapped =>
  let st := if swapped.chain = g.chain ∨ g2.chain = g.chain then
      { st with failures := "genesis: swapped founders or another nonce gave the same chain" :: st.failures }
    else st
  -- a forged log: the writer changes what the last write of the log wrote (its event, the signed
  -- call, still says otherwise) and re-prices it, so `fold` accepts it; `rederiveLog` must not
  match forge st.log with
  | none => st
  | some (i, bad) =>
      match World.fold P.env g bad, rederiveLog P.ctx g bad with
      | .ok _, .error (j, .refused .eventMismatch) =>
          if i = j then { st with refusedAsExpected := st.refusedAsExpected + 1 }
          else { st with failures := s!"forgery at {i} named at {j}" :: st.failures }
      | .ok _, .error (j, f) => { st with failures := s!"forgery at {i}: the re-derivation said {vname f} at {j}" :: st.failures }
      | .ok _, .ok _ => { st with failures := s!"forgery at {i}: the re-derivation accepted" :: st.failures }
      | .error _, _ => { st with failures := s!"forgery at {i}: fold refused it (not a forgery test)" :: st.failures }

/-- The refusals the generator plants, each of which a run of 16 or more seeds must meet. Every
name is reached through a signed call on the Host path, except `duplicateEffect`, which the probe
meets straight at `sealTurn` (`probeSeal`; a signed call reaches it too, a method whose run returns
two transfers out of the object's own account, which no arm here signs: KERNEL-67), and
`notConserved`, `floorNotConserved`, `valueMalformed` and `overBound` (nine denominations), which
no receiver derives and `probeValue` meets straight at `World.admit` with forged turns, and
`founderKeyTooLong`, genesis's refusal, which `probeGenesis` meets at `genesis`. -/
def planted : List String :=
  ["wrongWorld", "lawDenied", "noGrant", "unknownKey", "replayed", "stale", "notPrecommitted", "notIssuer",
   "missingCell", "enrollSpent", "transferSpent", "creditSpent", "rightTarget", "grantRight", "grantWidens", "unrooted", "duplicateEffect",
   "overflow", "sameAccount", "zeroAmount", "assetMismatch", "belowFloor", "spent",
   "notConserved", "floorNotConserved", "valueMalformed", "overBound", "notWell", "founderKeyTooLong", "ticksBudget"]

/-- The arms a run of 16 or more seeds must each reach with the named verdict (`what:verdict`): a
refusal name met somewhere else does not test the receiver this arm exercises. -/
def plantedArms : List String :=
  ["invoke-owner:ok", "invoke-no-grant:noGrant", "invoke-public:ok", "invoke-public-method-1:grantRight", "carve-public:noGrant",
   "law-self:lawDenied", "transfer-via:ok", "transfer-past-cap:transferSpent", "transfer-mutate:grantRight", "credit-via:ok", "credit-past-cap:creditSpent",
   "right-target:rightTarget", "cancel:recorded", "cancel-final:refusedFinal", "cancel-other:badSignature",
   "cancel-early:outsideWindow", "cancel-forged:cancelForged", "rotate-stales:stale", "law:ok", "create-frozen:ok", "write:lawDenied", "write-no-grant:noGrant",
   "rom-id:notContentId", "ticks-window:ticksBudget", "genesis-founder-key:founderKeyTooLong",
   "proof-sibling:refused", "proof-leaf:refused", "proof-tomb-live:refused", "proof-spent-unspent:refused",
   "proof-stale:refused", "proof-overlong:refused", "proof-spent-empty:refused",
   "account-twice:idTaken", "account-for-other:ok", "transfer-ref-not-well:notWell",
   "object-pays:ok", "object-pays-twice:spent", "reenter:revisited", "call-not-callable:notCallable",
   "too-many-calls:tooManyCalls", "over-ticks:overTicks", "grant-to-object:ok", "call-chain:ok",
   "call-too-deep:callTooDeep", "journal-expired:outsideWindow", "journal-window-first:outsideWindow",
   "journal-kept:replayed", "journal-reuse:ok", "journal-shadow:filtered", "journal-fits:misfit",
   "journal-shadow-kept:replayed", "journal-shadow-reuse:replayed",
   "journal-proof-height:refused", "journal-proof-admitted:refused", "journal-proof-stale:refused",
   "journal-proof-cells-root:refused", "carry-name:nameTooLong", "carry-old-call:replayed",
   "carry-old-world:wrongWorld", "carry-new:ok", "sig-bare:badSignature", "hash-count:empty-per-root", "verify-count:once", "retain:canonical",
   "retain-plant:refuted", "carry-budget:allowanceTooLarge", "carry-budget-edge:ok", "carry-budget-plant:overflow",
   "race-loser:stale", "race-loser-declined:declined", "race-law:lawDenied",
   "refusal-aba-stale:stale", "refusal-aba-declined:declined", "refusal-aba-plant:returned",
   "refusal-aba-pin:moved", "refusal-aba:stale", "refusal-stale-fold:stale", "refusal-stale-rederive:eventMismatch",
   "refusal-early-refused:outsideWindow", "refusal-early:declined", "refusal-early-kernel:outsideWindow",
   "refusal-early-plant:refusedFinal", "refusal-early-window:ok", "refusal-rotate-stranger:notPrecommitted",
   "refusal-rotate-kept:declined", "refusal-rotate-plant:authenticated", "refusal-budget:refusalBudget",
   "refusal-forged-code:eventMismatch", "refusals-counted:counted", "refusals-counted-plant:refused",
   "refusals-full:refusalsFull", "refusals-full-control:ok", "refusals-full-plant:overflow",
   "refusals-total-plant:refused",
   "rows-insert:ok", "rows-keyTaken:keyTaken", "rows-aba-floor:moved", "rows-aba:stale",
   "rows-missingRow:missingRow", "rows-relationCapped:relationCapped",
   "rows-relationFull:relationFull", "rows-retract:ok", "rows-retractForbidden:retractForbidden",
   "rows-rangeTooLong:rangeTooLong", "rows-range:ok", "rows-range-stale:stale", "rows-two-rains:both",
   "rows-taken-plant:caught", "rows-range-drop-plant:stale", "rows-repin-plant:stale",
   "proof-bit:refused", "depth-unhashed-plant:caught", "shape-unary-plant:caught",
   "pin-cell:same", "pin-cell-plant:caught", "pin-row:same", "pin-row-plant:caught",
   "pin-range:same", "pin-range-plant:caught", "rows-stem:ok",
   "rows-retire-heads:equal", "hash-required:heads-seal", "trie-binding:one-leaf",
   "hash-required:empty-per-insert", "proof-required:extra-sibling", "proof-required:sibling-byte",
   "hash-required:rewalk", "hash-required:rows-rewalk", "hash-required:rows-retract-seal",
   "state-order-create:stateKey", "state-dup-create:stateKey", "state-order-control:ok",
   "state-order-run:stateKey", "state-order-run-control:ok"]

/-- `--seeds N` (N ≥ 1) runs seeds `0 … N-1`; otherwise each argument is a seed; none is 64 seeds.
`--harness-control` may stand anywhere (GATES-15). Anything else is refused (`none`): an argument
that is not read is never a run of other seeds (it was: `kernel-sim foo` ran zero seeds and printed
`ALL PASS`). -/
def parseArgs (args : List String) : Option (List Nat × Bool) :=
  let control := args.contains "--harness-control"
  let seeds := match args.filter (· != "--harness-control") with
    | ["--seeds", n] => n.toNat?.bind fun k => if k = 0 then none else some (List.range k)
    | [] => some (List.range 64)
    | rest => rest.mapM String.toNat?
  seeds.map (·, control)

/-- The name `--harness-control` adds to the required arms (GATES-15): nothing meets it, so a
run with it must read `FAIL planted refusals never met: [harness-control]`, the known-red control
gates/runs.py runs before it reads kernel-sim's verdict. -/
def controlArm : String := "harness-control"

/-- Run seeds under `P` and report; 0 (`ALL PASS`) when every seed passes and every planted
refusal is met. The planted refusals are judged only over 16 or more seeds; a shorter run that
fails nothing ends `PLANTS NOT JUDGED …` with exit 3, never `ALL PASS` (it did: the gate was skipped
and the run passed). `control` adds `controlArm` to the required arms. -/
def report (P : Params D) (seeds : List Nat) (control : Bool := false) : IO UInt32 := do
  IO.println s!"kernel-sim under {P.name}"
  let mut bad := 0
  let mut admitted := 0
  let mut refused := 0
  let mut restarts := 0
  let mut work : Nat × Nat := (0, 0)
  let mut seen : List String := []
  -- cv 01a14afe-7380: what the run turns' admissions require, by part; their counted hashes (`<A`);
  -- the plant's admissions (`<A` less `<C` plus `<E`)
  let mut req : Required.Parts := {}
  let mut counted := 0
  let mut plantCounted := 0
  -- cv 01a15107-2281: the admissions with the re-walk plant in place of the batch
  let mut rewalkCounted := 0
  -- cv 01a153a5-0e09: the rows probe's insert turns (row and stem) with the rows re-walk plant in place
  -- of the run, and what they require
  let mut rowsRewalkCounted := 0
  let mut rowsInsReqAll := 0
  -- cv 01a15460-e096: the retract turns with the retract-seal plant in place of the run
  let mut retSealCounted := 0
  let mut headsRun := 0
  let mut headsSeal := 0
  let mut headsReq := 0
  -- (journal-probe inserts, prunes, refusals, row inserts, row retracts, stem inserts) required
  let mut reqs : Nat × Nat × Nat × Nat × Nat × Nat := (0, 0, 0, 0, 0, 0)
  let mut weighed := 0
  let mut journal : Nat × Nat × Nat := (0, 0, 0)
  -- KERNEL-41: (journal-insert marks, inserts, prune marks, prunes)
  let mut jhashes : Nat × Nat × Nat × Nat := (0, 0, 0, 0)
  -- KERNEL-44: (refuse marks, recorded refusals, record bytes, most per member per window, budgeted)
  let mut rf : Nat × Nat × Nat × Nat × Nat := (0, 0, 0, 0, 0)
  -- KERNEL-46/48: (insert marks less their non-rows share, inserts, retract marks less theirs,
  -- retracts, range reads, rows those reads listed)
  let mut rw : Nat × Nat × Nat × Nat × Nat × Nat := (0, 0, 0, 0, 0, 0)
  -- KERNEL-46/48: the rows' share of the run turns' admissions (`<Q`)
  let mut rowsRootMarks := 0
  -- KERNEL-49 (a): the roots' empty digest (`<O`), and the stem probe (marks, inserts, worst insert)
  let mut emptyRootMarks := 0
  -- the per-root plant's marks (`<P`): the roots read as before cv 01a15107-2272
  let mut plantRootMarks := 0
  let mut stem : Nat × Nat × Nat := (0, 0, 0)
  let mut proofBytes : Nat × Nat := (0, 0)
  -- cv 01a15107-2290: (required, extra-sibling plant, sibling-byte plant) proof bytes
  let mut proofReqs : Nat × Nat × Nat := (0, 0, 0)
  -- PERF-1: signature verifies of `judge` re-run on each recorded refusal (`<G`)
  let mut verifies := 0
  let mut auditVerifies := 0
  for seed in seeds do
    -- the run's trie hashes are counted off its stderr (`countingEnv`); nothing else writes there
    let buf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
    let old ← IO.setStderr (IO.FS.Stream.ofBuffer buf)
    let st ← IO.lazyPure fun _ => run P seed 120
    let _ ← IO.setStderr old
    let m := countMarks (String.fromUTF8! (← buf.get).data)
    -- the per-root plant must cost more than the shared roots whenever a World had two empty tries
    -- at once (the first turns, before any refusal is recorded), or the counter is blind
    let st := if m.plant > m.emptyRoot then
        { st with seen := "hash-count:empty-per-root" :: st.seen } else st
    -- cv 01a14afe-7380: every counted share against what it requires, never below it (a count below
    -- the requirement means the design changed and `Required` must be re-derived with it)
    let rowsIns := m.rowIns - m.rowInsBase
    let rowsRet := m.rowRet - m.rowRetBase
    let stemN := m.stemIns - m.stemBase
    let st := [("admission", m.admit, st.required.total), ("journal insert", m.probeInsert, st.probeInsertReq),
        ("journal prune", m.prune, st.pruneReq), ("refusal", m.refuse, st.refuseReq),
        ("row insert", rowsIns, st.rowInsReq), ("row retract", rowsRet, st.rowRetReq),
        ("stem insert", stemN, st.stemReq)].foldl (fun st (what, n, r) =>
          if n < r then failWith st s!"hash required: the {what} hashes counted {n}, below the {r} they require"
          else st) st
    -- the empty-per-insert plant: exactly one more hash per cell insert, and the admission with it
    -- reads above the requirement where the real one reads at it
    let plantN := m.admit - m.cells + m.plantInsert
    let st := if m.plantInsert = m.cells + st.cellInserts then st
      else failWith st s!"hash required: the empty-per-insert plant counted {m.plantInsert}, the cell write {m.cells} over {st.cellInserts} inserts"
    let st := if st.cellInserts > 0 && ratioUp plantN st.required.total > ratioUp m.admit st.required.total then
        { st with seen := "hash-required:empty-per-insert" :: st.seen } else st
    -- the re-walk plant: never below the batch, and the admission with it reads above the requirement
    -- on a seed where two of a turn's keys shared a path node
    let st := if m.rewalk < m.batch then
        failWith st s!"hash required: the re-walk plant counted {m.rewalk}, below the batch's {m.batch}" else st
    let rewalkN := m.admit - m.batch + m.rewalk
    let st := if ratioUp rewalkN st.required.total > ratioUp m.admit st.required.total then
        { st with seen := "hash-required:rewalk" :: st.seen } else st
    rewalkCounted := rewalkCounted + rewalkN
    -- the rows re-walk plant: never below the run, and the insert turns' rows share with it in place of
    -- the run reads above what they require
    let st := if m.rowsRewalk < m.rowsRun then
        failWith st s!"hash required: the rows re-walk plant counted {m.rowsRewalk}, below the run's {m.rowsRun}" else st
    let insShare := (m.rowIns - m.rowInsBase) + (m.stemIns - m.stemBase)
    let insReq := st.rowInsReq + st.stemReq
    let rowsRewalkN := insShare - m.rowsRun + m.rowsRewalk
    let st := if ratioUp rowsRewalkN insReq > ratioUp insShare insReq then
        { st with seen := "hash-required:rows-rewalk" :: st.seen } else st
    rowsRewalkCounted := rowsRewalkCounted + rowsRewalkN
    rowsInsReqAll := rowsInsReqAll + insReq
    -- the retract-seal plant: never below the run, and the retract turns' rows share with it in place
    -- of the run reads above what they require (cv 01a15460-e096)
    let st := if m.rowsRetSeal < m.rowsRetRun then
        failWith st s!"hash required: the retract-seal plant counted {m.rowsRetSeal}, below the run's {m.rowsRetRun}" else st
    let retShare := m.rowRet - m.rowRetBase
    let retSealN := retShare - m.rowsRetRun + m.rowsRetSeal
    let st := if st.rowRetracts > 0 && ratioUp retSealN st.rowRetReq > ratioUp retShare st.rowRetReq then
        { st with seen := "hash-required:rows-retract-seal" :: st.seen } else st
    retSealCounted := retSealCounted + retSealN
    let st := if m.retireHeadsRun = st.retireHeadsReq then st
      else failWith st s!"retirement rows counted {m.retireHeadsRun}, required {st.retireHeadsReq}"
    let st := if st.retireHeadsReq > 0 && m.retireHeadsSeal > m.retireHeadsRun then
        meet st "hash-required:heads-seal"
      else failWith st s!"heads-seal plant counted {m.retireHeadsSeal}, run {m.retireHeadsRun}"
    headsRun := headsRun + m.retireHeadsRun
    headsSeal := headsSeal + m.retireHeadsSeal
    headsReq := headsReq + st.retireHeadsReq

    req := req.add st.required
    counted := counted + m.admit
    plantCounted := plantCounted + plantN
    reqs := (reqs.1 + st.probeInsertReq, reqs.2.1 + st.pruneReq, reqs.2.2.1 + st.refuseReq,
      reqs.2.2.2.1 + st.rowInsReq, reqs.2.2.2.2.1 + st.rowRetReq, reqs.2.2.2.2.2 + st.stemReq)
    -- the two-verify plant must cost more than `judge` on a seed that recorded a refusal
    let st := if st.recorded > 0 && m.verifyTwice > m.verifyOnce then
        { st with seen := "verify-count:once" :: st.seen } else st
    -- exact, per seed: `judge` verifies at least once per recorded refusal (an authenticated call was
    -- verified somewhere), and the plant exactly once more per refusal whose verdict carried it
    -- the follower's re-derivation of each record (decode, then the same judge) verifies exactly as judge does
    let st := if m.verifyAudit = m.verifyOnce then st
      else failWith st s!"verify count: the re-derivation {m.verifyAudit} verifies, judge {m.verifyOnce}, over {st.recorded} recorded refusals"
    let st := if m.verifyOnce ≥ st.recorded && m.verifyTwice = m.verifyOnce + st.carried then st
      else failWith st s!"verify count: judge {m.verifyOnce} and the plant {m.verifyTwice} verifies over {st.recorded} recorded refusals, {st.carried} carried"
    verifies := verifies + m.verifyOnce
    auditVerifies := auditVerifies + m.verifyAudit
    let (a, b) := maxWork st.log
    work := (max work.1 a, max work.2 b)
    admitted := admitted + st.admitted
    weighed := weighed + st.weighed
    journal := (max journal.1 st.journalMax, journal.2.1 + st.journalScanned, journal.2.2 + st.journalTurns)
    refused := refused + st.refusedAsExpected
    restarts := restarts + st.restarts
    jhashes := (jhashes.1 + m.probeInsert, jhashes.2.1 + st.probeInserts, jhashes.2.2.1 + m.prune,
      jhashes.2.2.2 + st.prunes)
    rf := (rf.1 + m.refuse, rf.2.1 + st.recorded, rf.2.2.1 + st.refusalBytes, max rf.2.2.2.1 st.refusalMax,
      rf.2.2.2.2 + st.budgeted)
    rowsRootMarks := rowsRootMarks + m.rowsRoot
    emptyRootMarks := emptyRootMarks + m.emptyRoot
    plantRootMarks := plantRootMarks + m.plant
    proofBytes := (proofBytes.1 + st.proofBytes, proofBytes.2 + st.proofs)
    proofReqs := (proofReqs.1 + st.proofReq, proofReqs.2.1 + st.proofPlantSib, proofReqs.2.2 + st.proofPlantByte)
    stem := (stem.1 + (m.stemIns - m.stemBase), stem.2.1 + st.stemInserts, max stem.2.2 m.stemWorst)
    rw := (rw.1 + (m.rowIns - m.rowInsBase), rw.2.1 + st.rowInserts, rw.2.2.1 + (m.rowRet - m.rowRetBase),
      rw.2.2.2.1 + st.rowRetracts, rw.2.2.2.2.1 + st.rangeReads, rw.2.2.2.2.2 + st.rowsRead)
    -- cv 01a15107-2290: the proofs' wire bytes against what their paths require, never below it
    -- (a wire below the requirement means the layout changed and `Required.proofReq` must follow),
    -- and each plant above it where the real proofs read at it
    let st := if st.proofBytes < st.proofReq then
        failWith st s!"proof required: the proofs' wire bytes {st.proofBytes}, below the {st.proofReq} their paths require"
      else st
    let st := if st.proofs > 0 && ratioUp st.proofPlantSib st.proofReq > ratioUp st.proofBytes st.proofReq then
        { st with seen := "proof-required:extra-sibling" :: st.seen } else st
    let st := if st.proofs > 0 && ratioUp st.proofPlantByte st.proofReq > ratioUp st.proofBytes st.proofReq then
        { st with seen := "proof-required:sibling-byte" :: st.seen } else st
    seen := (st.seen ++ seen).eraseDups
    match st.failures.reverse with
    | [] => IO.println s!"PASS seed {seed}: admitted={st.admitted} refused-as-expected={st.refusedAsExpected} restarts={st.restarts}"
    | f :: _ =>
        bad := bad + 1
        IO.println s!"FAIL seed {seed}: {f}"
  IO.println s!"kernel-sim: seeds={seeds.length} admitted={admitted} refused-as-expected={refused} restarts={restarts} failing-seeds={bad}"
  IO.println s!"kernel-sim: record bytes = Turn.logWeight on {weighed} of {admitted} admitted turns"
  IO.println s!"kernel-sim: refusals recorded={rf.2.1} declined-refusalBudget={rf.2.2.2.2}"
  if (P.env.bytes P.zero).size = digestWeight && weighed != admitted then
    bad := bad + 1
    IO.println s!"FAIL log weight compared on {weighed} of {admitted} admitted turns"
  -- every planted refusal must have been met: a name the generator never reaches is not tested
  let unmet := (planted ++ plantedArms ++ (if control then [controlArm] else [])).filter fun n => !seen.contains n
  if !unmet.isEmpty && seeds.length ≥ 16 then
    bad := bad + 1
    IO.println s!"FAIL planted refusals never met: {unmet}"
  IO.println s!"WASTE admit cells-touched-per-turn {showRatio work.1}"
  IO.println s!"WASTE fold work-per-turn {showRatio work.2}"
  IO.println s!"kernel-sim: trie hashes of the run turns' admissions counted={counted} required={req.total} (cells {req.cells}, nullifiers {req.nullifiers}, journal {req.journal}, rows {req.rows}, refusals prune {req.refusals}, empty root {req.roots})"
  IO.println s!"kernel-sim: plant hash-required:empty-per-insert counted={plantCounted}: hashes-per-required {showRatio (ratioUp plantCounted req.total)}"
  IO.println s!"kernel-sim: plant hash-required:rows-rewalk (each row touch on the trie in turn, the rows run before cv 01a153a5-0e09) counted={rowsRewalkCounted} over the insert turns' rows requirement {rowsInsReqAll}: hashes-per-required {showRatio (ratioUp rowsRewalkCounted rowsInsReqAll)}"
  IO.println s!"kernel-sim: plant hash-required:rewalk (each key in turn, the fold before cv 01a15107-2281) counted={rewalkCounted}: hashes-per-required {showRatio (ratioUp rewalkCounted req.total)}"
  IO.println s!"kernel-sim: plant hash-required:rows-retract-seal (a retract seals the batch before it removes, uStore.drop before cv 01a15460-e096) counted={retSealCounted} over the retract turns' rows requirement {reqs.2.2.2.2.1}: hashes-per-required {showRatio (ratioUp retSealCounted reqs.2.2.2.2.1)}"
  IO.println s!"kernel-sim: retire heads counted={headsRun} required={headsReq}; plant seal-before-heads counted={headsSeal}: hashes-per-required {showRatio (ratioUp headsSeal headsReq)}"
  IO.println s!"WASTE admit retire-heads-hashes-per-required {showRatio (ratioUp headsRun headsReq)}"
  IO.println s!"kernel-sim: required: journal probe inserts {reqs.1} (counted {jhashes.1}), prunes {reqs.2.1} (counted {jhashes.2.2.1}), refusals {reqs.2.2.1} (counted {rf.1}), row inserts {reqs.2.2.2.1} (counted {rw.1}), row retracts {reqs.2.2.2.2.1} (counted {rw.2.2.1}), stem inserts {reqs.2.2.2.2.2} (counted {stem.1})"
  IO.println s!"WASTE admit hashes-per-required {showRatio (ratioUp counted req.total)}"
  IO.println s!"WASTE admit journal-insert-hashes-per-required {showRatio (ratioUp jhashes.1 reqs.1)}"
  IO.println s!"WASTE admit prune-hashes-per-required {showRatio (ratioUp jhashes.2.2.1 reqs.2.1)}"
  IO.println s!"WASTE admit journal-entries-per-window {showRatio (ratio journal.1 Bounds.windowMax)}"
  IO.println s!"WASTE admit journal-scanned-per-turn {showRatio (ratio journal.2.1 journal.2.2)}"
  IO.println s!"WASTE refuse hashes-per-required {showRatio (ratioUp rf.1 reqs.2.2.1)}"
  IO.println s!"WASTE refuse record-bytes-per-refusal {showRatio (ratio rf.2.2.1 rf.2.1)}"
  IO.println s!"WASTE refuse refusals-per-member-window {showRatio (ratio rf.2.2.2.1 1)}"
  IO.println s!"WASTE refuse verifies-per-refusal {showRatio (ratio verifies rf.2.1)}"
  IO.println s!"WASTE audit verifies-per-refusal {showRatio (ratio auditVerifies rf.2.1)}"
  IO.println s!"WASTE admit hashes-per-turn-rows-root {showRatio (ratio rowsRootMarks admitted)}"
  IO.println s!"WASTE admit row-insert-hashes-per-required {showRatio (ratioUp rw.1 reqs.2.2.2.1)}"
  IO.println s!"WASTE admit row-retract-hashes-per-required {showRatio (ratioUp rw.2.2.1 reqs.2.2.2.2.1)}"
  IO.println s!"WASTE admit rows-read-per-range-read {showRatio (ratio rw.2.2.2.2.2 rw.2.2.2.2.1)}"
  IO.println s!"WASTE admit hashes-per-turn-empty-root {showRatio (ratioUp emptyRootMarks admitted)}"
  -- the ABSOLUTE admission cost (ROOT, GATES-8): the per-required rows above move with the design
  -- they measure; this one is over the fixed seeds, so a costlier trie reads above its ceiling
  IO.println s!"WASTE admit trie-hashes-per-turn {showRatio (ratioUp counted admitted)}"
  IO.println s!"kernel-sim: plant hash-count:empty-per-root (the roots read with a hashOf per root) reads hashes-per-turn-empty-root {showRatio (ratioUp plantRootMarks admitted)}"
  IO.println s!"WASTE admit row-insert-stem-hashes-per-required {showRatio (ratioUp stem.1 reqs.2.2.2.2.2)}"
  if P.proofSize.isSome then
    IO.println s!"kernel-sim: proofs {proofBytes.2}: wire bytes {proofBytes.1}, required {proofReqs.1}; plant extra-sibling {proofReqs.2.1} ({showRatio (ratioUp proofReqs.2.1 proofReqs.1)}), plant sibling-byte {proofReqs.2.2} ({showRatio (ratioUp proofReqs.2.2 proofReqs.1)}, bytes-per-inclusion {showRatio (ratio proofReqs.2.2 proofBytes.2)})"
    IO.println s!"WASTE proof bytes-per-required {showRatio (ratioUp proofBytes.1 proofReqs.1)}"
    -- the ABSOLUTE proof size: bytes-per-required moves with the layout it reads, so a fatter
    -- layout still reads 1.000 there; over the fixed seeds this one reads above its ceiling
    IO.println s!"WASTE proof bytes-per-inclusion {showRatio (ratio proofBytes.1 proofBytes.2)}"
  IO.println s!"kernel-sim: stem probe: {stem.2.1} inserts, the most one insert hashed {stem.2.2} (KERNEL-49 (c)'s bound 2·(rowDepth+1) = {2 * (Bounds.rowDepth + 1)})"
  if rf.2.2.2.1 > Bounds.refusalsPerWindow then
    bad := bad + 1
    IO.println s!"FAIL a member had {rf.2.2.2.1} refusals recorded in one window (bound {Bounds.refusalsPerWindow})"
  if bad > 0 then return 1
  if seeds.length < 16 then
    IO.println s!"PLANTS NOT JUDGED ({seeds.length} seeds; the planted refusals need 16 or more)"
    return 3
  IO.println "ALL PASS"
  return 0

end Nanodregg.Kernel.Sim.Gen
