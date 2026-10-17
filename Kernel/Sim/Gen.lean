/-
# Kernel.Sim.Gen — the seeded generator, generic in its parameters

The generator, the Host stand-in, the follower and auditor checks of `Kernel.Sim`, over any
digest, hash, encodings and signature scheme (`Params`). Two instances run it: the toy
(`Kernel.Sim`: UInt64 digests, FNV, a hash "signature") and the deployed (`Kernel.Sim.Deployed`:
CODEC's digest, cSHAKE256, codecs and RFC 8032 Ed25519), so the pipeline is the same code and only
the parameters differ.
-/
import Kernel.Receive.Audit
import Kernel.Receive.Submit
import Kernel.Receive.Follow

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

/-- The law-program stub both instances run (`deny-all` refuses every act, `freeze` refuses writes
and invokes, anything else admits; method 0 sets the first state slot, the others make the calls
of `stubCalls`; method 5 reports one tick more than it was given). Each run uses one tick. LANG's
real program runs in `lang-journey`. -/
def program (digestOf : ByteArray → Option D) (width : Nat) : Program D :=
  { checkInstall := fun _ _ => .ok ()
    judge := fun look _ laws _ _ r =>
      forEx (fun l => match look l with
        | .ok (some cell) =>
            if cell.slots.get 0 = some denyAll then .error (.lawDenied l "deny-all")
            else if cell.slots.get 0 = some freeze ∧ frozenAct r.occasion then .error (.lawDenied l "freeze")
            else .ok ()
        | .ok none => .error (.missingCell l)
        | .error e => .error e) laws
    run := fun _ _ state method args r budget =>
      if method = 0 then .ok (state.set stateBase args, [], min 1 budget)
      else if method = 5 then .ok (state, [], budget + 1)
      else if method ≤ 6 then .ok (state, stubCalls digestOf width method args r budget, min 1 budget)
      else .error (.program "no such method") }

/-- What an instance supplies: its `Ctx` (whose `env` the generator hashes and encodes with), how
a secret becomes a public key and signs, a default digest, and a name for the report. -/
structure Params (D : Type) where
  name : String
  ctx : Ctx D
  pub : ByteArray → ByteArray
  sign : ByteArray → ByteArray → ByteArray
  zero : D

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
  log : List (Turn D) := []
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
  /-- KERNEL-23 (h): the slots the admitted turns changed, cells and nullifiers apart (their hashes
  are COUNTED, not modelled: `countingEnv`, `report`) -/
  cellSlots : Nat := 0
  nullSlots : Nat := 0
  /-- the call-tree arms (D5c) ran in this seed -/
  treeDone : Bool := false
  /-- admitted turns whose record bytes were compared with `Turn.logWeight` (at a 32-byte digest) -/
  weighed : Nat := 0
  /-- KERNEL-33's journal probe: the most entries any probe World held, the entries its prunes
  scanned, and the turns it admitted -/
  journalMax : Nat := 0
  journalScanned : Nat := 0
  journalTurns : Nat := 0

def nameOf {α : Type} [Repr α] (a : α) : String :=
  match (reprStr a).splitOn " " with
  | h :: _ => (h.splitOn ".").getLast!
  | [] => ""

def vname : Verdict D → String
  | .refused r => s!"refused {r.name}"
  | .rejected r => s!"rejected {r.name}"

def S.pinsFor (E : Env D) (w : World D) (ids : List D) : List (D × D) :=
  ids.eraseDups.map fun c => (c, pinOf E (w.live E c))

def signed (P : Params D) (st : State D) (m : Member D) (key : ByteArray) (pins : List (D × D)) (body : Body D) :
    Call D :=
  let u : Unsigned D :=
    { world := st.host.origin, member := m.id, key := P.pub key, notBefore := 0, validUntil := st.host.height + 1 + 100, pins,
      maxCharge := 1000000, body }
  { unsigned := u, signature := P.sign key (P.ctx.unsignedBytes u) }

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

/-- PLANT (the counter's tooth): `commitTrie` with the empty digest recomputed per insert, the
regression KERNEL-35 removed. The same map, more hashes; `report` must count more for it (arm
`hash-count:empty-per-insert`). -/
def plantCommitPerInsert (E : Env D) (w : World D) (t : Turn D) (posts : List (Post D)) : Cells D :=
  let S := trieSpec E
  let m := (posts.map Post.pair ++ bornEntries t).foldl
    (fun m p => m.insert S (.cell p.1) (.entry p.2)) w.trie
  t.nullifiers.foldl (fun m n => m.insert S (.nullifier n) .spent) m

/-- The counted calls for one admitted turn `w → w'`: the whole admission (`<A`), its trie write
without the nullifiers (`<C`, the cell share), and the plant (`<P`). Each result must be what the
uncounted call gives, or the counter changed the computation. -/
def countTurn (E : Env D) (st : State D) (w w' : World D) (t : Turn D) : State D :=
  let cE := countingEnv E
  let S := trieSpec E
  match check E w t with
  | .error _ => failWith st "hash count: an admitted turn does not re-check"
  | .ok posts =>
      let t0 := { t with nullifiers := [] }
      let a := dbgTrace "<A" fun _ => World.admit cE w t
      let c := dbgTrace "<C" fun _ => commitTrie cE w t0 posts
      let p := dbgTrace "<P" fun _ => plantCommitPerInsert cE w t posts
      let st := match a with
        | .ok w'' => if w''.root E == w'.root E then st
            else failWith st "hash count: the counted admission reached another root"
        | .error _ => failWith st "hash count: the counted admission refused an admitted turn"
      let st := if c.hashOf S == (commitTrie E w t0 posts).hashOf S then st
        else failWith st "hash count: the counted cell write reached another root"
      if p.hashOf S == w'.root E then st
      else failWith st "hash count: the per-insert plant reached another root"

/-- `report`'s side: the marks of one captured run, summed per bracket tag (`A`, `C`, `P`). -/
def countMarks (out : String) : Nat × Nat × Nat :=
  (out.splitOn "<").foldl (fun (a, c, p) seg =>
    let n := (seg.toList.filter (· == '#')).length
    match seg.toList.head? with
    | some 'A' => (a + n, c, p)
    | some 'C' => (a, c + n, p)
    | some 'P' => (a, c, p + n)
    | _ => (a, c, p)) (0, 0, 0)

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

/-- After an admitted turn `w → w'`: replay its inserts from `w`'s trie with `w'`'s leaves (the
replay must reach `w'`'s root, or a touched path was left unrehashed), count their hashes, prove
and verify every changed slot and one untouched one against `w'`'s root, each nullifier as absent
against `w`'s, and forge four proofs, each of which must fail to verify. -/
def checkRoot (P : Params D) (st : State D) (w w' : World D) (t : Turn D) : State D :=
  let E := P.env
  let S := trieSpec E
  let slots := changedSlots t
  let st := countTurn E st w w' t
  let (tr, st) := slots.foldl (fun (tr, st) s =>
    match w'.trie.get S s with
    | none => (tr, failWith st "root: a changed slot is absent after the turn")
    | some l =>
        let tr' := tr.insert S s l
        let st := match s with
          | .cell _ => { st with cellSlots := st.cellSlots + 1 }
          | .nullifier _ => { st with nullSlots := st.nullSlots + 1 }
        (tr', st)) (w.trie, st)
  let st := if tr.hashOf S == w'.root E then st
    else failWith st "root: replaying the turn's inserts does not reach the admitted root"
  let root := w'.root E
  let verifyAt := fun (st : State D) (s : Slot D) =>
    match w'.trie.get S s with
    | none => if Trie.verifyExclusion S root s (w'.trie.prove S s) then st
        else failWith st "root: an absent slot's exclusion proof does not verify"
    | some l => if Trie.verifyInclusion S root s (leafDigest E l) (w'.trie.prove S s) then st
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
    | s :: rest => ⟨p.term, (if s == E.hash domTrie "forged".toUTF8 then E.hash domTrie "forged2".toUTF8
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
              | .entry (.live _) => .entry .tomb
              | _ => .entry (.live ⟨0, .ram, []⟩)
            let st := if Trie.verifyInclusion S root s (leafDigest E other) p then
              failWith st "root: a proof verified a leaf the World does not hold"
            else meet st "proof-leaf:refused"
            -- the pre-turn proof of the same slot, against the post-turn root (a stale proof)
            let st := if Trie.verifyInclusion S root s (leafDigest E l) (w.trie.prove S s) then
              failWith st "root: a stale (pre-turn) proof verified against the new root"
            else meet st "proof-stale:refused"
            -- a proof longer than the trie's depth is refused before anything is hashed
            let long : Trie.Proof (Slot D) D := ⟨p.term, p.sibs ++ List.replicate (S.depth + 1) root⟩
            if Trie.verifyInclusion S root s (leafDigest E l) long then
              failWith st "root: a proof longer than the depth verified"
            else meet st "proof-overlong:refused"
  -- a retired cell claimed live: its old cell against the tombstone's path
  let st := t.touches.foldl (fun st x =>
    match x.act, w.live E x.cell with
    | .retire, some old =>
        if Trie.verifyInclusion S root (.cell x.cell) (leafDigest E (.entry (.live old))) (w'.trie.prove S (.cell x.cell))
        then failWith st "root: a tombstone was proved live"
        else meet st "proof-tomb-live:refused"
    | _, _ => st) st
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

/-- Submit a call on the Host path and judge the verdict. -/
def submit (P : Params D) (st : State D) (c : Call D) (expect : Expect) (what : String) : State D × Option (Turn D) :=
  let X := P.ctx
  let st := { st with steps := st.steps + 1, lastCall := some c }
  let fail := fun (got : String) =>
    ({ st with failures := s!"step {st.steps} {what}: expected {reprStr expect}, got {got}" :: st.failures }, none)
  match Receive.submit X st.host c with
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
        ({ st with host := w', log := st.log ++ [t], admitted := st.admitted + 1,
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
    creates.zipIdx.map (fun p => (bornId P.env txId p, p.1)), [], 0, ByteArray.empty⟩
  { t0 with charge := t0.weight }

/-- The value probes: forged turns no receiver derives, each refused by the kernel by name. -/
def probeValue (P : Params D) (st : State D) : State D :=
  let w := st.host
  match st.accounts with
  | [] => st
  | a0 :: _ =>
      let (acct, st) := pick st st.accounts a0
      match w.live P.env acct.1 with
      | none => st
      | some cell =>
          let seen := pinOf P.env (some cell)
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

/-- A refusal no receiver produces, met straight at the seal (the `planted` table says so): the
last call's first pin given two effects. -/
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
  | 19 => probeRom P (probeValue P st)
  | 23 => if st.treeDone then st else treeArms P st
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
          match w.journal[txIdOf P.ctx c]? with
          | some (h, _) => (submit P st c (.rejected "replayed") s!"replay@{h}").1
          | none => st
  | 7 => -- a stale pin: the owner claims the object is absent
      match st.objects with
      | [] => st
      | o :: _ =>
          let (obj, st) := pick st st.objects o
          let owner := (st.members.find? fun m => m.id = obj.2).getD (founder0 P st)
          let pins := (S.pinsFor P.env w [owner.id]) ++ [(obj.1, pinOf P.env none)]
          let c := signed P st owner owner.key pins (.write obj.1 [(0, nat 7)] none)
          let laws := match w.live P.env obj.1 with
            | some cell => (lawSlotsOf cell).filterMap fun (p : Nat × ByteArray) => P.ctx.digestOf p.2
            | none => []
          if laws.isEmpty then (submit P st c (.rejected "stale") "stale").1 else st
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
          (submit P st old (.refused "unknownKey") "old-key").1
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
          let back := ((w.live P.env gid).map Cell.weight).getD 0
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
      match st.log.getLast? with
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

def maxWork (log : List (Turn D)) : Nat × Nat :=
  log.foldl (fun (a, b) t => let (x, y) := turnWork t; (max a x, max b y)) (0, 0)

/-- Same contents and the same ROOT (the journal's TreeMap shape may differ; nothing else may). -/
def same (E : Env D) (a b : World D) : Bool :=
  a.trie.toList == b.trie.toList && a.root E == b.root E && a.journal.toList == b.journal.toList &&
  a.height == b.height && a.chain == b.chain && a.allowance == b.allowance && a.origin == b.origin

/-- A World rebuilt from its own listing, as a checkpoint decode does (CODEC-19): the trie by
`Trie.build` (KERNEL-23: it is the same trie, `build_toList`), the journal from its sorted list. -/
def reopened (E : Env D) (w : World D) : World D :=
  let trie := Trie.build (trieSpec E) (trieSpec E).depth 0 w.trie.toList
  let journal : Std.TreeMap D (Nat × D) compare := Std.TreeMap.ofList w.journal.toList compare
  { w with trie, journal }

def worldName : ByteArray := "sim".toUTF8

/-- HOST draws a genesis nonce from the OS; the Sim's is a function of the seed (KERNEL-24). -/
def nonceOf (seed : Nat) : ByteArray := s!"sim-nonce-{seed}".toUTF8

/-- The log up to its last write, that write's values replaced and its charge re-priced: a log
`fold` accepts (later turns, which pinned the honest value, are cut) and no signed call derives. -/
def forge (log : List (Turn D)) : Option (Nat × List (Turn D)) :=
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
  match (log.zipIdx.filter fun (t, _) => isWrite t).getLast? with
  | none => none
  | some (t, i) =>
      let t0 := { t with touches := t.touches.map forged }
      let t1 := { t0 with charge := t0.weight }
      some (i, log.take i ++ [t1])

/-- The genesis probe (KERNEL-31): past `Bounds.eventBytesMax` the raw codec truncates, so an
oversize founder key would give two geneses one origin with no hash collision. A third founder
whose key is one byte too long must be refused `founderKeyTooLong`, naming its index; the control
is the run's own genesis, which was admitted. -/
def probeGenesis (P : Params D) (st : State D) (founders : List (ByteArray × D)) : State D :=
  let long : ByteArray := ⟨Array.replicate (Bounds.eventBytesMax + 1) 7⟩
  let bad := founders ++ [(long, nextKeyDigest P.ctx (P.pub "f2-next".toUTF8))]
  match genesis P.ctx worldName (nonceOf 0) 100000000 bad with
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
      touches := [], creates := [], nullifiers := [], charge := 0, event := ByteArray.empty }
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
  let step := fun (acc : Except String (World D × Nat × Nat)) (i : Nat) =>
    match acc with
    | .error e => .error e
    | .ok (w, mx, scanned) =>
      let H := w.height + 1
      let scan := if H % W = 0 then w.journal.size + 1 else 0
      match World.admit P.env w (journalTurn P i H H) with
      | .ok w' =>
          if w'.journal.size < 3 * W then .ok (w', max mx w'.journal.size, scanned + scan)
          else .error s!"journal holds {w'.journal.size} entries at height {w'.height}"
      | .error r => .error s!"journal turn {i} refused {r.name}"
  match (List.range n).foldl step (.ok (World.genesis P.env P.zero 100000000, 0, 0)) with
  | .error e => failWith st s!"probe journal: {e}"
  | .ok (w, mx, scanned) =>
      let st := { st with journalMax := mx, journalScanned := scanned, journalTurns := n }
      let tx := fun i => P.env.hash "nanodregg/sim/journal-tx" (toString i).toUTF8
      let missing := (List.range n).filter fun i =>
        !journalForgets w.height (i + 1) && (w.journal[tx i]?).isNone
      if !missing.isEmpty then failWith st s!"probe journal: ids {missing.take 4} unanswered below journalForgets"
      else if (w.journal[tx 0]?).isSome then failWith st "probe journal: turn 0's entry was never pruned"
      else
        let H := w.height + 1
        let k := 2 * W + 5
        let st := journalExpect P st w (journalTurn P 0 1 1) "journal-expired" "outsideWindow"
        let st := journalExpect P st w (journalTurn P k (k + 1) (k + 1)) "journal-window-first" "outsideWindow"
        let st := journalExpect P st w (journalTurn P k H H) "journal-kept" "replayed"
        journalExpect P st w (journalTurn P 0 H H) "journal-reuse" "ok"

/-- One verdict of the carry probe, by name: `submit` on the carried World. -/
def carryExpect (P : Params D) (st : State D) (w : World D) (c : Call D) (what want : String) : State D :=
  let got := match Receive.submit P.ctx w c with
    | .ok _ => "ok"
    | .error v => match v with
      | .refused r => r.name
      | .rejected r => r.name
  if got = want then
    { st with refusedAsExpected := st.refusedAsExpected + 1, seen := s!"{what}:{want}" :: want :: st.seen }
  else failWith st s!"probe carry {what}: expected {want}, got {got}"

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
        w'.journal.toList == w.journal.toList) then failWith st "probe carry: the carried World differs"
    else if w'.origin == w.origin then failWith st "probe carry: the carried World kept the old origin"
    else
      let st := match st.log.getLast? with
        | none => st
        | some t => match X.decodeCall t.event with
          | none => failWith st "probe carry: the last logged event does not decode"
          | some c =>
              let want := (w.journal[t.txId]?).map Prod.fst
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

def run (P : Params D) (seed : Nat) (steps : Nat) : State D :=
  let rng : Rng := ⟨seed.toUInt64 * 0x2545F4914F6CDD1D + 1⟩
  let fk : List (ByteArray × ByteArray) :=
    [("f0".toUTF8, "f0-next".toUTF8), ("f1".toUTF8, "f1-next".toUTF8)]
  let X := P.ctx
  let founders := fk.map fun (k, n) => (P.pub k, nextKeyDigest X (P.pub n))
  match genesis X worldName (nonceOf seed) 100000000 founders with
  | .error r =>
      { rng, host := World.genesis P.env P.zero 0, members := [], failures := [s!"genesis refused {r.name}"] }
  | .ok g =>
  let members := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Member D)
  let holds := (List.range fk.length).map fun i =>
    (founderId X g.origin i, (⟨[founderGrantId X g.origin i], true, enrollMax⟩ : Holding D))
  let st0 : State D := { rng, host := g, members, holds }
  let st0 := probeJournal P (probeGenesis P st0 founders) seed
  -- install the deny-all law package first
  let f := founder0 P st0
  let c := signed P st0 f f.key (S.pinsFor P.env g [f.id]) (.install denyAll)
  let (st, t) := submit P st0 c .ok "install"
  let st := { st with denyPkg := t.bind fun t => (createdIds t).head? }
  let (st, t) := submit P st (signed P st f f.key (S.pinsFor P.env st.host [f.id]) (.install freeze)) .ok "install"
  let st := { st with freezePkg := t.bind fun t => (createdIds t).head? }
  let (st, t) := submit P st (signed P st f f.key (S.pinsFor P.env st.host [f.id]) (.install methods)) .ok "install"
  let st := { st with methodsPkg := t.bind fun t => (createdIds t).head? }
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
      -- a checkpoint reopen: every map rebuilt from its sorted contents (a different tree shape,
      -- the same World: Kernel.Proofs.Equiv says admit cannot tell)
      let w := reopened P.env st.host
      if same P.env w st.host then { st with host := w, restarts := st.restarts + 1 }
      else { st with failures := "checkpoint: the rebuilt trie differs (root or listing)" :: st.failures }
    else st) st
  -- the follower and the auditor, from genesis
  let st := match World.fold P.env g st.log with
    | .ok w =>
        if !same P.env w st.host then { st with failures := "follower differs" :: st.failures }
        else
          -- the Host's proofs verify against the follower's root (KERNEL-23 (g))
          let S := trieSpec P.env
          let ok := match st.log.getLast? with
            | none => true
            | some t => (changedSlots t).all fun s => match st.host.trie.get S s with
                | some l => Trie.verifyInclusion S (w.root P.env) s (leafDigest P.env l) (st.host.trie.prove S s)
                | none => false
          if ok then st else { st with failures := "follower: a Host proof does not verify at the follower's root" :: st.failures }
    | .error (i, r) => { st with failures := s!"follower refused at {i}: {r.name}" :: st.failures }
  let st := match audit P.ctx g st.log with
    | .ok w => if same P.env w st.host then st else { st with failures := "audit differs" :: st.failures }
    | .error (i, f) => { st with failures := s!"audit refused at {i}: {vname f}" :: st.failures }
  let st := probeCarry P st
  -- KERNEL-24: the same log's calls against a second genesis (same name and founders, another
  -- nonce) are each refused `wrongWorld`; another nonce, or the founders swapped, is another chain
  match genesis X worldName (nonceOf (seed + 1000000)) 100000000 founders with
  | .error r => failWith st s!"second genesis refused {r.name}"
  | .ok g2 =>
  let st := st.log.foldl (fun st t =>
    match X.decodeCall t.event with
    | none => { st with failures := "replay elsewhere: a logged event does not decode" :: st.failures }
    | some c =>
        match Receive.submit X g2 c with
        | .error (.refused .wrongWorld) =>
            { st with refusedAsExpected := st.refusedAsExpected + 1, seen := "wrongWorld" :: st.seen }
        | .error v => { st with failures := s!"replay elsewhere: got {vname v}" :: st.failures }
        | .ok _ => { st with failures := "replay elsewhere: admitted on a second World" :: st.failures }) st
  match genesis X worldName (nonceOf seed) 100000000 founders.reverse with
  | .error r => failWith st s!"swapped genesis refused {r.name}"
  | .ok swapped =>
  let st := if swapped.chain = g.chain ∨ g2.chain = g.chain then
      { st with failures := "genesis: swapped founders or another nonce gave the same chain" :: st.failures }
    else st
  -- a forged log: the writer changes what the last write of the log wrote (its event, the signed
  -- call, still says otherwise) and re-prices it, so `fold` accepts it; `audit` must not
  match forge st.log with
  | none => st
  | some (i, bad) =>
      match World.fold P.env g bad, audit P.ctx g bad with
      | .ok _, .error (j, .refused .eventMismatch) =>
          if i = j then { st with refusedAsExpected := st.refusedAsExpected + 1 }
          else { st with failures := s!"forgery at {i} named at {j}" :: st.failures }
      | .ok _, .error (j, f) => { st with failures := s!"forgery at {i}: audit said {vname f} at {j}" :: st.failures }
      | .ok _, .ok _ => { st with failures := s!"forgery at {i}: audit accepted" :: st.failures }
      | .error _, _ => { st with failures := s!"forgery at {i}: fold refused it (not a forgery test)" :: st.failures }

/-- The refusals the generator plants, each of which a run of 16 or more seeds must meet. Every
name is reached through a signed call on the Host path, except `duplicateEffect`, which no
receiver can produce and the probe meets straight at `sealTurn` (`probeSeal`), and
`notConserved`, `floorNotConserved`, `valueMalformed` and `overBound` (nine denominations), which
no receiver derives and `probeValue` meets straight at `World.admit` with forged turns, and
`founderKeyTooLong`, genesis's refusal, which `probeGenesis` meets at `genesis`. -/
def planted : List String :=
  ["wrongWorld", "lawDenied", "noGrant", "unknownKey", "replayed", "stale", "notPrecommitted", "notIssuer",
   "missingCell", "enrollSpent", "grantRight", "grantWidens", "unrooted", "duplicateEffect",
   "overflow", "sameAccount", "zeroAmount", "assetMismatch", "belowFloor", "spent",
   "notConserved", "floorNotConserved", "valueMalformed", "overBound", "notWell", "founderKeyTooLong"]

/-- The arms a run of 16 or more seeds must each reach with the named verdict (`what:verdict`): a
refusal name met somewhere else does not test the receiver this arm exercises. -/
def plantedArms : List String :=
  ["invoke-owner:ok", "invoke-no-grant:noGrant", "invoke-public:ok", "invoke-public-method-1:grantRight", "carve-public:noGrant",
   "law-self:lawDenied", "law:ok", "create-frozen:ok", "write:lawDenied", "write-no-grant:noGrant",
   "rom-id:notContentId", "genesis-founder-key:founderKeyTooLong",
   "proof-sibling:refused", "proof-leaf:refused", "proof-tomb-live:refused", "proof-spent-unspent:refused",
   "proof-stale:refused", "proof-overlong:refused", "proof-spent-empty:refused",
   "account-twice:idTaken", "account-for-other:ok", "transfer-ref-not-well:notWell",
   "object-pays:ok", "object-pays-twice:spent", "reenter:revisited", "call-not-callable:notCallable",
   "too-many-calls:tooManyCalls", "over-ticks:overTicks", "grant-to-object:ok", "call-chain:ok",
   "call-too-deep:callTooDeep", "journal-expired:outsideWindow", "journal-window-first:outsideWindow",
   "journal-kept:replayed", "journal-reuse:ok", "carry-name:nameTooLong", "carry-old-call:replayed",
   "carry-old-world:wrongWorld", "carry-new:ok", "hash-count:empty-per-insert"]

/-- `--seeds N` runs seeds `0 … N-1`; otherwise each argument is a seed. -/
def parseSeeds : List String → List Nat
  | ["--seeds", n] => List.range (n.toNat?.getD 64)
  | [] => List.range 64
  | args => args.filterMap String.toNat?

/-- Run seeds under `P` and report; 0 when every seed passes and every planted refusal is met. -/
def report (P : Params D) (seeds : List Nat) : IO UInt32 := do
  IO.println s!"kernel-sim under {P.name}"
  let mut bad := 0
  let mut admitted := 0
  let mut refused := 0
  let mut restarts := 0
  let mut work : Nat × Nat := (0, 0)
  let mut seen : List String := []
  let mut hashes : Nat × Nat × Nat × Nat := (0, 0, 0, 0)
  let mut weighed := 0
  let mut journal : Nat × Nat × Nat := (0, 0, 0)
  for seed in seeds do
    -- the run's trie hashes are counted off its stderr (`countingEnv`); nothing else writes there
    let buf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
    let old ← IO.setStderr (IO.FS.Stream.ofBuffer buf)
    let st ← IO.lazyPure fun _ => run P seed 120
    let _ ← IO.setStderr old
    let (ha, hc, hp) := countMarks (String.fromUTF8! (← buf.get).data)
    -- the plant must cost more whenever the run met an empty sibling, or the counter is blind
    let st := if hp > ha then { st with seen := "hash-count:empty-per-insert" :: st.seen } else st
    let (a, b) := maxWork st.log
    work := (max work.1 a, max work.2 b)
    admitted := admitted + st.admitted
    weighed := weighed + st.weighed
    journal := (max journal.1 st.journalMax, journal.2.1 + st.journalScanned, journal.2.2 + st.journalTurns)
    refused := refused + st.refusedAsExpected
    restarts := restarts + st.restarts
    hashes := (hashes.1 + hc, hashes.2.1 + st.cellSlots, hashes.2.2.1 + (ha - hc),
      hashes.2.2.2 + st.nullSlots)
    seen := (st.seen ++ seen).eraseDups
    match st.failures.reverse with
    | [] => IO.println s!"PASS seed {seed}: admitted={st.admitted} refused-as-expected={st.refusedAsExpected} restarts={st.restarts}"
    | f :: _ =>
        bad := bad + 1
        IO.println s!"FAIL seed {seed}: {f}"
  IO.println s!"kernel-sim: seeds={seeds.length} admitted={admitted} refused-as-expected={refused} restarts={restarts} failing-seeds={bad}"
  IO.println s!"kernel-sim: record bytes = Turn.logWeight on {weighed} of {admitted} admitted turns"
  if (P.env.bytes P.zero).size = digestWeight && weighed != admitted then
    bad := bad + 1
    IO.println s!"FAIL log weight compared on {weighed} of {admitted} admitted turns"
  -- every planted refusal must have been met: a name the generator never reaches is not tested
  let unmet := (planted ++ plantedArms).filter fun n => !seen.contains n
  if !unmet.isEmpty && seeds.length ≥ 16 then
    bad := bad + 1
    IO.println s!"FAIL planted refusals never met: {unmet}"
  IO.println s!"WASTE admit cells-touched-per-turn {showRatio work.1}"
  IO.println s!"WASTE fold work-per-turn {showRatio work.2}"
  IO.println s!"WASTE admit hashes-per-touched-cell {showRatio (ratio hashes.1 hashes.2.1)}"
  IO.println s!"WASTE admit hashes-per-nullifier {showRatio (ratio hashes.2.2.1 hashes.2.2.2)}"
  IO.println s!"WASTE admit journal-entries-per-window {showRatio (ratio journal.1 Bounds.windowMax)}"
  IO.println s!"WASTE admit journal-scanned-per-turn {showRatio (ratio journal.2.1 journal.2.2)}"
  if bad = 0 then IO.println "ALL PASS"
  return if bad = 0 then 0 else 1

end Nanodregg.Kernel.Sim.Gen
