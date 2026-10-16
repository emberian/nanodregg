/-
# Kernel.Sim — the seeded simulation: the Host path against the follower, with restarts

`lake exe sim --seeds N` runs N seeded scenarios. Each drives the REAL receive path
(`Receive.receive` then `World.admit`) with honest and adversarial calls, checks every verdict
against the one the generator built the call to get (by refusal NAME), restarts the "Host" from
a fold of its own log prefix at random points, and at the end requires

* the follower (`World.fold` from genesis over the admitted log) to reach the Host's World,
* the auditor (`Receive.audit`) to accept the same log and reach the same World,
* every planted mutation (stale pin, replay, wrong charge, stolen-key rotation, stranger, missing
  grant, deny-all law) to have been refused by its name.

Toy PARAMETERS in the real pipeline (memory: never toy code beside it): the digest is `UInt64`,
the hash FNV-1a, a signature is the hash of key ‖ message, and the program is a two-law stub
(`deny-all` refuses, anything else admits; method 0 sets the first state slot). The encodings of
turns and cells are the toy's own serialisation until CODEC's Turn/Cell codecs land; the Sim then
runs under the deployed `Env` as well.

The Host side here is incremental `admit` plus restart-by-fold: the stand-in for HOST's loop
(KERNEL K0), replaced by plugging `Host.Loop` into `step` when it exists.
-/
import Kernel.Receive.Audit
import Kernel.Receive.Submit
import Kernel.Receive.Follow

namespace Nanodregg.Kernel.Sim

open Nanodregg.Kernel Nanodregg.Kernel.Receive

abbrev D := UInt64

/-! ## Toy parameters -/

def fnv (b : ByteArray) : UInt64 :=
  b.foldl (fun h x => (h ^^^ x.toUInt64) * 1099511628211) 14695981039346656037

def u64le (x : UInt64) : ByteArray :=
  ⟨#[x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8,
     (x >>> 32).toUInt8, (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8]⟩

def ofLe (b : ByteArray) : Option UInt64 :=
  if b.size = 8 then
    some ((List.range 8).foldl (fun acc i => acc ||| ((b.get! i).toUInt64 <<< (8 * i).toUInt64)) 0)
  else none

def nat (n : Nat) : ByteArray := u64le n.toUInt64
def blob (b : ByteArray) : ByteArray := nat b.size ++ b
def many {α : Type} (f : α → ByteArray) (l : List α) : ByteArray :=
  l.foldl (fun acc x => acc ++ f x) (nat l.length)

def discByte : Discipline → ByteArray
  | .rom => nat 0 | .appendOnly => nat 1 | .ram => nat 2

def cellBytes (c : Cell) : ByteArray :=
  nat c.kind ++ discByte c.discipline ++ many (fun p => nat p.1 ++ blob p.2) c.slots

def opBytes : Op → ByteArray
  | .set k v => nat 0 ++ nat k ++ blob v
  | .erase k => nat 1 ++ nat k

def turnBytes (t : Turn D) : ByteArray :=
  u64le t.txId ++ nat t.notBefore ++ nat t.validUntil ++
  many (fun p => u64le p.1 ++ u64le p.2) t.pins ++ many cellBytes t.creates ++
  many (fun l => u64le l.cell ++ many opBytes l.ops) t.legs ++ many u64le t.retires ++
  many u64le t.nullifiers ++ nat t.charge ++ blob t.event

def env : Env D :=
  { hash := fun dom b => fnv (dom.toUTF8 ++ b), bytes := u64le, turnBytes, cellBytes }

def rightBytes : Right → ByteArray
  | .observe => nat 0 | .mutate => nat 1 | .invoke m => nat 2 ++ nat m

def optD : Option D → ByteArray
  | none => nat 0 | some d => nat 1 ++ u64le d

def bodyBytes : Body D → ByteArray
  | .enroll k n p => nat 0 ++ blob k ++ u64le n ++ blob p
  | .rotate k n => nat 1 ++ blob k ++ u64le n
  | .install p => nat 2 ++ blob p
  | .create p ls st => nat 3 ++ optD p ++ many u64le ls ++ many (fun q => nat q.1 ++ blob q.2) st
  | .write o es v => nat 4 ++ u64le o ++
      many (fun e => nat e.1 ++ match e.2 with | none => nat 0 | some b => nat 1 ++ blob b) es ++ optD v
  | .law o ls v => nat 5 ++ u64le o ++ many u64le ls ++ optD v
  | .invoke o m a b v => nat 6 ++ u64le o ++ nat m ++ blob a ++ nat b ++ optD v
  | .grant t g rs p => nat 7 ++ u64le t ++ u64le g ++ many rightBytes rs ++ optD p
  | .follow g p => nat 8 ++ u64le g ++ u64le p
  | .revoke g => nat 9 ++ u64le g

def unsignedBytes (u : Unsigned D) : ByteArray :=
  u64le u.member ++ blob u.key ++ nat u.notBefore ++ nat u.validUntil ++
  many (fun p => u64le p.1 ++ u64le p.2) u.pins ++ nat u.maxCharge ++ bodyBytes u.body

def toySign (key msg : ByteArray) : ByteArray := u64le (fnv (key ++ msg))

def denyAll : ByteArray := "deny-all".toUTF8

def program : Program D :=
  { checkInstall := fun _ _ => .ok ()
    judge := fun look _ laws _ _ _ =>
      forEx (fun l => match look l with
        | .ok (some cell) =>
            if cell.slots.get 0 = some denyAll then .error (.lawDenied l "deny-all") else .ok ()
        | .ok none => .error (.missingCell l)
        | .error e => .error e) laws
    run := fun _ _ state method args _ _ =>
      if method = 0 then .ok (state.set stateBase args) else .error (.program "no such method") }

/-- The Sim's call registry: a logged event's bytes map back to the call (the toy `decodeCall`
is a lookup by the event digest into the calls the Sim made; CODEC's real decoder replaces it). -/
structure Registry where
  calls : List (D × Call D) := []

def ctx (reg : Registry) : Ctx D :=
  { env, unsignedBytes, callBytes := fun c => unsignedBytes c.unsigned ++ blob c.signature,
    decodeCall := fun b => (reg.calls.find? fun p => p.1 = fnv b).map Prod.snd
    digestOf := ofLe, verify := fun key msg sig => toySign key msg == sig, program }

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

structure Member where
  id : D
  key : ByteArray
  nextKey : ByteArray

/-- What the generator expects a call to get. -/
inductive Expect
  | ok
  | refused (name : String)
  | rejected (name : String)
  deriving DecidableEq, Repr

structure State where
  rng : Rng
  reg : Registry
  /-- the Host's World and its admitted log -/
  host : World D
  log : List (Turn D) := []
  members : List Member
  objects : List (D × D) := []
  denyPkg : Option D := none
  fresh : Nat := 0
  lastCall : Option (Call D) := none
  steps : Nat := 0
  admitted : Nat := 0
  refusedAsExpected : Nat := 0
  restarts : Nat := 0
  failures : List String := []

def nameOf {α : Type} [Repr α] (a : α) : String :=
  match (reprStr a).splitOn " " with
  | h :: _ => (h.splitOn ".").getLast!
  | [] => ""

def S.pinsFor (w : World D) (ids : List D) : List (D × D) :=
  ids.eraseDups.map fun c => (c, pinOf env (w.live c))

def signed (st : State) (m : Member) (key : ByteArray) (pins : List (D × D)) (body : Body D) :
    Call D :=
  let u : Unsigned D :=
    { member := m.id, key, notBefore := 0, validUntil := st.host.height + 1 + 100, pins,
      maxCharge := 1000000, body }
  { unsigned := u, signature := toySign key (unsignedBytes u) }

def freshKey (st : State) (tag : String) : ByteArray × State :=
  ((s!"key-{tag}-{st.fresh}").toUTF8, { st with fresh := st.fresh + 1 })

/-- Submit a call on the Host path and judge the verdict. -/
def submit (st : State) (c : Call D) (expect : Expect) (what : String) : State × Option (Turn D) :=
  let X := ctx st.reg
  let reg := { calls := (fnv (X.callBytes c), c) :: st.reg.calls }
  let st := { st with reg, steps := st.steps + 1, lastCall := some c }
  let fail := fun (got : String) =>
    ({ st with failures := s!"step {st.steps} {what}: expected {reprStr expect}, got {got}" :: st.failures }, none)
  match Receive.submit X st.host c with
  | .error (.refused r) =>
      if expect = .refused (nameOf r) then ({ st with refusedAsExpected := st.refusedAsExpected + 1 }, none)
      else fail s!"refused {nameOf r}"
  | .error (.rejected r) =>
      if expect = .rejected (nameOf r) then ({ st with refusedAsExpected := st.refusedAsExpected + 1 }, none)
      else fail s!"rejected {nameOf r}"
  | .ok (t, w') =>
      if expect = .ok then
        ({ st with host := w', log := st.log ++ [t], admitted := st.admitted + 1 }, some t)
      else fail "admitted"

def pick {α : Type} (st : State) (l : List α) (d : α) : α × State :=
  let (i, rng) := st.rng.below l.length
  (l.getD i d, { st with rng })

def founder0 (st : State) : Member := st.members.headD ⟨0, ByteArray.empty, ByteArray.empty⟩

/-- One generated action. -/
def act (st : State) : State :=
  let (k, rng) := st.rng.below 10
  let st := { st with rng }
  let w := st.host
  match k with
  | 0 => -- enroll a newcomer, sponsored by a random member
      let (sp, st) := pick st st.members (founder0 st)
      let (key, st) := freshKey st "m"
      let (nk, st) := freshKey st "n"
      let X := ctx st.reg
      let possession := toySign key (possessionMessage X sp.id (nextKeyDigest X nk) key)
      let c := signed st sp sp.key (S.pinsFor w [sp.id]) (.enroll key (nextKeyDigest X nk) possession)
      let (st, t) := submit st c .ok "enroll"
      match t with
      | some t =>
          let id := (createdIds env t).headD 0
          { st with members := st.members ++ [⟨id, key, nk⟩] }
      | none => st
  | 1 => -- birth a data object; a birth under deny-all is judged by it and refused
      let (m, st) := pick st st.members (founder0 st)
      let (d, st) := st.rng.below 4 |> fun (x, r) => (x, { st with rng := r })
      let laws := if d = 0 then st.denyPkg.toList else []
      let c := signed st m m.key (S.pinsFor w (m.id :: laws)) (.create none laws [(stateBase, nat 0)])
      let (st, t) := submit st c (if laws.isEmpty then .ok else .refused "lawDenied") "create"
      match t with
      | some t => { st with objects := st.objects ++ [((createdIds env t).headD 0, m.id)] }
      | none => st
  | 3 => -- the owner puts an object under deny-all: judged by the laws in force (none: admitted;
         -- deny-all already: the repair is refused too)
      match st.objects, st.denyPkg with
      | o :: _, some deny =>
          let (obj, st) := pick st st.objects o
          let owner := (st.members.find? fun m => m.id = obj.2).getD (founder0 st)
          let laws := match w.live obj.1 with
            | some cell => (lawSlotsOf cell).filterMap fun (p : Nat × ByteArray) => ofLe p.2
            | none => []
          let denied := laws.any fun l => l = deny
          let c := signed st owner owner.key (S.pinsFor w (owner.id :: obj.1 :: deny :: laws))
            (.law obj.1 [deny] none)
          (submit st c (if denied then .refused "lawDenied" else .ok) "law").1
      | _, _ => st
  | 2 => -- the owner writes; under deny-all it must be lawDenied
      match st.objects with
      | [] => st
      | o :: _ =>
          let (obj, st) := pick st st.objects o
          let owner := (st.members.find? fun m => m.id = obj.2).getD (founder0 st)
          let laws := match w.live obj.1 with
            | some cell => (lawSlotsOf cell).filterMap fun (p : Nat × ByteArray) => ofLe p.2
            | none => []
          let denied := laws.any fun l => some l = st.denyPkg
          let c := signed st owner owner.key (S.pinsFor w (owner.id :: obj.1 :: laws))
            (.write obj.1 [(0, nat st.steps)] none)
          (submit st c (if denied then .refused "lawDenied" else .ok) "write").1
  | 4 => -- a member who does not own the object writes without a grant
      match st.objects with
      | [] => st
      | o :: _ =>
          let (obj, st) := pick st st.objects o
          match st.members.find? fun m => m.id ≠ obj.2 with
          | none => st
          | some m =>
              let c := signed st m m.key (S.pinsFor w [m.id, obj.1]) (.write obj.1 [(0, nat 1)] none)
              (submit st c (.refused "noGrant") "write-no-grant").1
  | 5 => -- a stranger (never enrolled) signs
      let (key, st) := freshKey st "stranger"
      let ghost : Member := ⟨fnv ("ghost".toUTF8 ++ key), key, key⟩
      let c := signed st ghost key (S.pinsFor w [ghost.id]) (.create none [] [])
      (submit st c (.refused "unknownKey") "stranger").1
  | 6 => -- replay the last call exactly
      match st.lastCall with
      | none => st
      | some c =>
          match w.journal[txIdOf (ctx st.reg) c]? with
          | some (h, _) => (submit st c (.rejected "replayed") s!"replay@{h}").1
          | none => st
  | 7 => -- a stale pin: the owner claims the object is absent
      match st.objects with
      | [] => st
      | o :: _ =>
          let (obj, st) := pick st st.objects o
          let owner := (st.members.find? fun m => m.id = obj.2).getD (founder0 st)
          let pins := (S.pinsFor w [owner.id]) ++ [(obj.1, pinOf env none)]
          let c := signed st owner owner.key pins (.write obj.1 [(0, nat 7)] none)
          let laws := match w.live obj.1 with
            | some cell => (lawSlotsOf cell).filterMap fun (p : Nat × ByteArray) => ofLe p.2
            | none => []
          if laws.isEmpty then (submit st c (.rejected "stale") "stale").1 else st
  | 8 => -- rotation: a thief's key is refused; the member's precommitted key is admitted
      let (m, st) := pick st st.members (founder0 st)
      let (thief, st) := freshKey st "thief"
      let X := ctx st.reg
      let bad := signed st m thief (S.pinsFor w [m.id]) (.rotate thief (nextKeyDigest X thief))
      let (st, _) := submit st bad (.refused "notPrecommitted") "thief-rotate"
      let (nk, st) := freshKey st "n"
      let good := signed st m m.nextKey (S.pinsFor st.host [m.id]) (.rotate m.nextKey (nextKeyDigest X nk))
      let (st, t) := submit st good .ok "rotate"
      match t with
      | some _ =>
          let members := st.members.map fun x => if x.id = m.id then ⟨x.id, x.nextKey, nk⟩ else x
          let st := { st with members }
          -- the old key is no longer the member's
          let old := signed st m m.key (S.pinsFor st.host [m.id]) (.create none [] [])
          (submit st old (.refused "unknownKey") "old-key").1
      | none => st
  | _ => -- a probe straight at admit: an admitted-shape turn with the wrong charge
      match st.log.getLast? with
      | none => st
      | some t =>
          let bad := { t with txId := t.txId + 1, charge := t.charge + 1 }
          match World.admit env w bad with
          | .error r =>
              if nameOf r = "chargeMismatch" ∨ nameOf r = "stale" ∨ nameOf r = "idTaken" then
                { st with steps := st.steps + 1, refusedAsExpected := st.refusedAsExpected + 1 }
              else { st with failures := s!"probe: got {nameOf r}" :: st.failures }
          | .ok _ => { st with failures := "probe: wrong charge admitted" :: st.failures }

/-- Same contents (TreeMap shapes may differ; contents may not). -/
def same (a b : World D) : Bool :=
  a.cells.toList == b.cells.toList && a.journal.toList == b.journal.toList &&
  a.spent.toList == b.spent.toList && a.height == b.height && a.chain == b.chain &&
  a.allowance == b.allowance

def worldName : ByteArray := "sim".toUTF8

def run (seed : Nat) (steps : Nat) : State :=
  let rng : Rng := ⟨seed.toUInt64 * 0x2545F4914F6CDD1D + 1⟩
  let fk : List (ByteArray × ByteArray) :=
    [("f0".toUTF8, "f0-next".toUTF8), ("f1".toUTF8, "f1-next".toUTF8)]
  let X := ctx {}
  let g := genesis X worldName 100000000 (fk.map fun (k, n) => (k, nextKeyDigest X n))
  let members := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X worldName i, k, n⟩ : Member)
  let st0 : State := { rng, reg := {}, host := g, members }
  -- install the deny-all law package first
  let f := founder0 st0
  let c := signed st0 f f.key (S.pinsFor g [f.id]) (.install denyAll)
  let (st, t) := submit st0 c .ok "install"
  let st := { st with denyPkg := t.bind fun t => (createdIds env t).head? }
  let st := (List.range steps).foldl (fun st _ =>
    let st := act st
    -- restart: the Host reopens by folding its own log from genesis
    let (r, rng) := st.rng.below 16
    let st := { st with rng }
    if r = 0 then
      match World.fold env g st.log with
      | .ok w => if same w st.host then { st with host := w, restarts := st.restarts + 1 }
          else { st with failures := "restart: reopened World differs" :: st.failures }
      | .error (i, r) => { st with failures := s!"restart: fold refused at {i}: {nameOf r}" :: st.failures }
    else st) st
  -- the follower and the auditor, from genesis
  let st := match World.fold env g st.log with
    | .ok w => if same w st.host then st else { st with failures := "follower differs" :: st.failures }
    | .error (i, r) => { st with failures := s!"follower refused at {i}: {nameOf r}" :: st.failures }
  match audit (ctx st.reg) g st.log with
  | .ok w => if same w st.host then st else { st with failures := "audit differs" :: st.failures }
  | .error (i, f) => { st with failures := s!"audit refused at {i}: {reprStr f}" :: st.failures }

/-- `--seeds N` runs seeds `0 … N-1`; otherwise each argument is a seed. -/
def parseSeeds : List String → List Nat
  | ["--seeds", n] => List.range (n.toNat?.getD 64)
  | [] => List.range 64
  | args => args.filterMap String.toNat?

def main (args : List String) : IO UInt32 := do
  let seeds := parseSeeds args
  let mut bad := 0
  let mut admitted := 0
  let mut refused := 0
  let mut restarts := 0
  for seed in seeds do
    let st := run seed 120
    admitted := admitted + st.admitted
    refused := refused + st.refusedAsExpected
    restarts := restarts + st.restarts
    match st.failures.reverse with
    | [] => IO.println s!"PASS seed {seed}: admitted={st.admitted} refused-as-expected={st.refusedAsExpected} restarts={st.restarts}"
    | f :: _ =>
        bad := bad + 1
        IO.println s!"FAIL seed {seed}: {f}"
  IO.println s!"kernel-sim: seeds={seeds.length} admitted={admitted} refused-as-expected={refused} restarts={restarts} failing-seeds={bad}"
  if bad = 0 then IO.println "ALL PASS"
  return if bad = 0 then 0 else 1

end Nanodregg.Kernel.Sim
