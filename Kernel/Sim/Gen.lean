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

/-- The two-law program stub both instances run (`deny-all` refuses, anything else admits;
method 0 sets the first state slot). LANG's real program runs in `lang-journey`. -/
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
  fresh : Nat := 0
  lastCall : Option (Call D) := none
  steps : Nat := 0
  admitted : Nat := 0
  refusedAsExpected : Nat := 0
  /-- every refusal name met as expected (the run requires each planted name at least once) -/
  seen : List String := []
  restarts : Nat := 0
  failures : List String := []

def nameOf {α : Type} [Repr α] (a : α) : String :=
  match (reprStr a).splitOn " " with
  | h :: _ => (h.splitOn ".").getLast!
  | [] => ""

def vname : Verdict D → String
  | .refused r => s!"refused {r.name}"
  | .rejected r => s!"rejected {r.name}"

def S.pinsFor (E : Env D) (w : World D) (ids : List D) : List (D × D) :=
  ids.eraseDups.map fun c => (c, pinOf E (w.live c))

def signed (P : Params D) (st : State D) (m : Member D) (key : ByteArray) (pins : List (D × D)) (body : Body D) :
    Call D :=
  let u : Unsigned D :=
    { member := m.id, key := P.pub key, notBefore := 0, validUntil := st.host.height + 1 + 100, pins,
      maxCharge := 1000000, body }
  { unsigned := u, signature := P.sign key (P.ctx.unsignedBytes u) }

def freshKey (st : State D) (tag : String) : ByteArray × State D :=
  ((s!"key-{tag}-{st.fresh}").toUTF8, { st with fresh := st.fresh + 1 })

/-- Submit a call on the Host path and judge the verdict. -/
def submit (P : Params D) (st : State D) (c : Call D) (expect : Expect) (what : String) : State D × Option (Turn D) :=
  let X := P.ctx
  let st := { st with steps := st.steps + 1, lastCall := some c }
  let fail := fun (got : String) =>
    ({ st with failures := s!"step {st.steps} {what}: expected {reprStr expect}, got {got}" :: st.failures }, none)
  match Receive.submit X st.host c with
  | .error (.refused r) =>
      if expect = .refused r.name then
        ({ st with refusedAsExpected := st.refusedAsExpected + 1, seen := r.name :: st.seen }, none)
      else fail s!"refused {r.name}"
  | .error (.rejected r) =>
      if expect = .rejected r.name then
        ({ st with refusedAsExpected := st.refusedAsExpected + 1, seen := r.name :: st.seen }, none)
      else fail s!"rejected {r.name}"
  | .ok (t, w') =>
      if expect = .ok then
        ({ st with host := w', log := st.log ++ [t], admitted := st.admitted + 1 }, some t)
      else fail "admitted"

def pick {α : Type} (st : State D) (l : List α) (d : α) : α × State D :=
  let (i, rng) := st.rng.below l.length
  (l.getD i d, { st with rng })

def founder0 (P : Params D) (st : State D) : Member D := st.members.headD ⟨P.zero, ByteArray.empty, ByteArray.empty⟩

def holdOf (st : State D) (m : D) : Holding D :=
  ((st.holds.find? fun p => p.1 = m).map Prod.snd).getD ⟨[], false, 0⟩

def setHold (st : State D) (m : D) (h : Holding D) : State D :=
  { st with holds := (m, h) :: st.holds.filter fun p => p.1 ≠ m }

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

/-- One generated action. -/
def act (P : Params D) (st : State D) : State D :=
  let (k, rng) := st.rng.below 15
  let st := { st with rng }
  let w := st.host
  match k with
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
              let id := (createdIds P.env t).headD P.zero
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
              let gid := (createdIds P.env t).headD P.zero
              let st := setHold st m.id { hm with left := hm.left - units }
              -- the grantee now acts through the new grant (its old one, if any, is forgotten;
              -- when the grantee is the granter, the carved grant replaces the spent one)
              setHold st ge.id ⟨gid :: hm.chain, n ≠ 3, units⟩
          | none => st
  | 1 => -- birth a data object; a birth under deny-all is judged by it and refused
      let (m, st) := pick st st.members (founder0 P st)
      let (d, st) := st.rng.below 4 |> fun (x, r) => (x, { st with rng := r })
      let laws := if d = 0 then st.denyPkg.toList else []
      let c := signed P st m m.key (S.pinsFor P.env w (m.id :: laws)) (.create none laws [(stateBase, nat 0)])
      let (st, t) := submit P st c (if laws.isEmpty then .ok else .refused "lawDenied") "create"
      match t with
      | some t => { st with objects := st.objects ++ [((createdIds P.env t).headD P.zero, m.id)] }
      | none => st
  | 3 => -- the owner puts an object under deny-all: judged by the laws in force (none: admitted;
         -- deny-all already: the repair is refused too)
      match st.objects, st.denyPkg with
      | o :: _, some deny =>
          let (obj, st) := pick st st.objects o
          let owner := (st.members.find? fun m => m.id = obj.2).getD (founder0 P st)
          let laws := match w.live obj.1 with
            | some cell => (lawSlotsOf cell).filterMap fun (p : Nat × ByteArray) => P.ctx.digestOf p.2
            | none => []
          let denied := laws.any fun l => l = deny
          let c := signed P st owner owner.key (S.pinsFor P.env w (owner.id :: obj.1 :: deny :: laws))
            (.law obj.1 [deny] none)
          (submit P st c (if denied then .refused "lawDenied" else .ok) "law").1
      | _, _ => st
  | 2 => -- the owner writes; under deny-all it must be lawDenied
      match st.objects with
      | [] => st
      | o :: _ =>
          let (obj, st) := pick st st.objects o
          let owner := (st.members.find? fun m => m.id = obj.2).getD (founder0 P st)
          let laws := match w.live obj.1 with
            | some cell => (lawSlotsOf cell).filterMap fun (p : Nat × ByteArray) => P.ctx.digestOf p.2
            | none => []
          let denied := laws.any fun l => some l = st.denyPkg
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
          let laws := match w.live obj.1 with
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
          | some t => { st with grants := st.grants ++ [((createdIds P.env t).headD P.zero, obj.1, ge.id, owner.id)] }
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
          let back := ((w.live gid).map Cell.weight).getD 0
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
              let laws := match w.live obj with
                | some cell => (lawSlotsOf cell).filterMap fun (p : Nat × ByteArray) => P.ctx.digestOf p.2
                | none => []
              let denied := laws.any fun l => some l = st.denyPkg
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
                if r.name = "chargeMismatch" ∨ r.name = "stale" ∨ r.name = "idTaken" then
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
def turnWork (E : Env D) (t : Turn D) : Nat × Nat :=
  let ids := createdIds E t
  let cells := t.touches.map Touch.cell
  let named := (cells ++ ids).eraseDups.length
  let cellLookups := t.touches.length + ids.length
  let changed := (t.touches.filter fun x => x.act != .keep).length
  let ops := cellLookups + 1 + t.nullifiers.length +
    (changed + ids.length + t.nullifiers.length + 1)
  (ratio cellLookups named, ratio ops (named + t.nullifiers.length + 1))

def maxWork (E : Env D) (log : List (Turn D)) : Nat × Nat :=
  log.foldl (fun (a, b) t => let (x, y) := turnWork E t; (max a x, max b y)) (0, 0)

/-- Same contents (TreeMap shapes may differ; contents may not). -/
def same (a b : World D) : Bool :=
  a.cells.toList == b.cells.toList && a.journal.toList == b.journal.toList &&
  a.spent.toList == b.spent.toList && a.height == b.height && a.chain == b.chain &&
  a.allowance == b.allowance

/-- A World rebuilt from its own sorted contents, as a checkpoint decode would. -/
def reopened (w : World D) : World D :=
  let cells : Std.TreeMap D Entry compare := Std.TreeMap.ofList w.cells.toList compare
  let journal : Std.TreeMap D (Nat × D) compare := Std.TreeMap.ofList w.journal.toList compare
  let spent : Std.TreeSet D compare := Std.TreeSet.ofList w.spent.toList compare
  { w with cells, journal, spent }

def worldName : ByteArray := "sim".toUTF8

/-- The log up to its last write, that write's values replaced and its charge re-priced: a log
`fold` accepts (later turns, which pinned the honest value, are cut) and no signed call derives. -/
def forge (log : List (Turn D)) : Option (Nat × List (Turn D)) :=
  let forged (x : Touch D) : Touch D := match x.act with
    | .write ops => { x with act := .write (ops.map fun o => match o with
        | .set k _ => .set k "forged".toUTF8
        | o => o) }
    | _ => x
  let isWrite (t : Turn D) := t.touches.any fun x => match x.act with
    | .write ops => ops.any fun o => match o with | .set _ _ => true | _ => false
    | _ => false
  match (log.zipIdx.filter fun (t, _) => isWrite t).getLast? with
  | none => none
  | some (t, i) =>
      let t0 := { t with touches := t.touches.map forged }
      let t1 := { t0 with charge := t0.weight }
      some (i, log.take i ++ [t1])

def run (P : Params D) (seed : Nat) (steps : Nat) : State D :=
  let rng : Rng := ⟨seed.toUInt64 * 0x2545F4914F6CDD1D + 1⟩
  let fk : List (ByteArray × ByteArray) :=
    [("f0".toUTF8, "f0-next".toUTF8), ("f1".toUTF8, "f1-next".toUTF8)]
  let X := P.ctx
  let g := genesis X worldName 100000000 (fk.map fun (k, n) => (P.pub k, nextKeyDigest X (P.pub n)))
  let members := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X worldName i, k, n⟩ : Member D)
  let holds := (List.range fk.length).map fun i =>
    (founderId X worldName i, (⟨[founderGrantId X worldName i], true, enrollMax⟩ : Holding D))
  let st0 : State D := { rng, host := g, members, holds }
  -- install the deny-all law package first
  let f := founder0 P st0
  let c := signed P st0 f f.key (S.pinsFor P.env g [f.id]) (.install denyAll)
  let (st, t) := submit P st0 c .ok "install"
  let st := { st with denyPkg := t.bind fun t => (createdIds P.env t).head? }
  let st := (List.range steps).foldl (fun st _ =>
    let st := act P st
    -- restart: the Host reopens by folding its own log from genesis
    let (r, rng) := st.rng.below 16
    let st := { st with rng }
    if r = 0 then
      match World.fold P.env g st.log with
      | .ok w => if same w st.host then { st with host := w, restarts := st.restarts + 1 }
          else { st with failures := "restart: reopened World differs" :: st.failures }
      | .error (i, r) => { st with failures := s!"restart: fold refused at {i}: {r.name}" :: st.failures }
    else if r = 1 then
      -- a checkpoint reopen: every map rebuilt from its sorted contents (a different tree shape,
      -- the same World: Kernel.Proofs.Equiv says admit cannot tell)
      { st with host := reopened st.host, restarts := st.restarts + 1 }
    else st) st
  -- the follower and the auditor, from genesis
  let st := match World.fold P.env g st.log with
    | .ok w => if same w st.host then st else { st with failures := "follower differs" :: st.failures }
    | .error (i, r) => { st with failures := s!"follower refused at {i}: {r.name}" :: st.failures }
  let st := match audit P.ctx g st.log with
    | .ok w => if same w st.host then st else { st with failures := "audit differs" :: st.failures }
    | .error (i, f) => { st with failures := s!"audit refused at {i}: {vname f}" :: st.failures }
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
receiver can produce and the probe meets straight at `sealTurn` (`probeSeal`). -/
def planted : List String :=
  ["lawDenied", "noGrant", "unknownKey", "replayed", "stale", "notPrecommitted", "notIssuer",
   "missingCell", "enrollSpent", "grantRight", "grantWidens", "unrooted", "duplicateEffect"]

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
  for seed in seeds do
    let st := run P seed 120
    let (a, b) := maxWork P.env st.log
    work := (max work.1 a, max work.2 b)
    admitted := admitted + st.admitted
    refused := refused + st.refusedAsExpected
    restarts := restarts + st.restarts
    seen := (st.seen ++ seen).eraseDups
    match st.failures.reverse with
    | [] => IO.println s!"PASS seed {seed}: admitted={st.admitted} refused-as-expected={st.refusedAsExpected} restarts={st.restarts}"
    | f :: _ =>
        bad := bad + 1
        IO.println s!"FAIL seed {seed}: {f}"
  IO.println s!"kernel-sim: seeds={seeds.length} admitted={admitted} refused-as-expected={refused} restarts={restarts} failing-seeds={bad}"
  -- every planted refusal must have been met: a name the generator never reaches is not tested
  let unmet := planted.filter fun n => !seen.contains n
  if !unmet.isEmpty && seeds.length ≥ 16 then
    bad := bad + 1
    IO.println s!"FAIL planted refusals never met: {unmet}"
  IO.println s!"WASTE admit cells-touched-per-turn {showRatio work.1}"
  IO.println s!"WASTE fold work-per-turn {showRatio work.2}"
  if bad = 0 then IO.println "ALL PASS"
  return if bad = 0 then 0 else 1

end Nanodregg.Kernel.Sim.Gen
