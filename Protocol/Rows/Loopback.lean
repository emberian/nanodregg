/-
# Protocol.Rows.Loopback — the member rows, in process

Each member row runs against a fresh writer (`Protocol.Rows.Writer`: HOST's loop on its own
thread) and, per actor, an in-process client that plays the parts `nd` and custody play, and runs
`host follow`'s machine (`Protocol.Command.start`/`step`) on the actor's own follow World:

* every step crosses the wire: the command is `commandFrame` bytes, each step `Reply.bytes`, each
  resume `resumeFrame` bytes, each one decoded back by the one reader before it is used;
* custody holds the actor's secret (`key:NAME:GEN`; its next is generation GEN+1) and answers
  `signResultFrame` with the run's key model: the public keys (`Params.pub`) and the signature
  (`Params.sign`) — the toy's (a secret is its own public key) or Ed25519 at the deployed parameters;
* a `host` step is relayed to the writer as a frame; a `submit` step is frozen as the actor's
  attempt and sent, and a lost reply is settled by `lookup` of the same bytes, never re-signed
  (the attempt store's rule, CLIENT-3);
* every operation sent on either socket is recorded, so the judge compares OBSERVED ops with the
  row's declared ones (`judge_members_pass_iff`).

The founders `sponsor` and `operator` are the genesis World (`Receive.genesis`, from the inputs they
hold). Any other actor first accepts the rows' FOUNDING INVITATION, the sponsor's at genesis, under
the sponsor's key (`Invite.accept`, PROTOCOL-42): its `Self.world` and its follow's first World are
what that invitation's signed inputs make, never the writer's World handed over. It is a stranger
(an id nobody enrolled) until a line binds its member id and its World grant. After a carry the
carried World has no invitation (it is made from a file), so an actor first used there takes the
carried World as given: trust on first use, by name (`rejoin` too).

The whole driver is generic in the digest `D`: a run is `run P …` under one `Rows.Params D`, the
toy's or the deployed (`rows --deployed`, PROTOCOL-50). Nothing in a row reads which.
-/
import Protocol.Rows.Writer
import Lang.Sim.Need
import Protocol.Rows.Judge
import Protocol.Command.Wire
import Host.Follow
import Protocol.Attempt
import Host.Carry
import Protocol.Invite
import Protocol.Use
import Protocol.Receipt

namespace Nanodregg.Protocol.Rows.Loopback

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Protocol.Command

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## The system a row runs, and its mutations -/

structure Sys (D : Type) [Ord D] where
  writer : Writer.Params D
  follow : Ctx D
  /-- after a lost reply the client signs afresh instead of looking up (a plant) -/
  resendFresh : Bool := false
  /-- every `withinMs` is 0 (a plant) -/
  zeroDeadline : Bool := false
  /-- custody advances when it signs a rotation, not on settlement (a plant) -/
  advanceOnSend : Bool := false
  /-- a second genesis draws the first one's nonce (a plant) -/
  nonceRepeats : Bool := false
  /-- the import is handed the file's own digest (a plant) -/
  importTrustsFile : Bool := false
  /-- a joiner takes an invitation's inputs unchecked (a plant) -/
  trustFirstUse : Bool := false
  /-- every actor's client signs as the sponsor (a plant) -/
  oneMember : Bool := false
  /-- a resident binds every described method as method 0 (a plant) -/
  guessMethod : Bool := false
  /-- the phone believes a receipt's stated answer (a plant) -/
  trustReceipt : Bool := false
  /-- the attempt store takes the Host's `declined` as final: the attempt settled `refused` (a plant,
  KERNEL-54: a stale is declined, and only follow's fold settles it) -/
  settleDecline : Bool := false
  /-- the attempt store ends an attempt on the Host's status, never asking follow (a plant) -/
  trustLookup : Bool := false
  /-- the operator's seal skips `Host.sealNow`: a restart and nothing sealed (a plant) -/
  sealIgnored : Bool := false
  /-- `read OBJ` prints the raw state slots (a plant, PROTOCOL-48) -/
  rawSlots : Bool := false
  /-- a page refused `pageIo` ends the command `refused pageIo`, exit 1 (a plant, PROTOCOL-49) -/
  pageIoFatal : Bool := false
  /-- `read OBJ REL K` drops its first row's line (a plant, PROTOCOL-51) -/
  dropRow : Bool := false
  /-- `read OBJ REL K` never checks K against the declared limit (a plant, PROTOCOL-51) -/
  noReadLimit : Bool := false
  /-- `nd`'s output for a method's refusal drops its reason: the bare `refused program` (a plant,
  cv 01a15039) -/
  flatProgram : Bool := false
  /-- a custody refusal of `signIncoming` ends the command by custody's name (a plant, PROTOCOL-56) -/
  maskIncoming : Bool := false
  /-- the attempt store ends `uncertain` with no payload, the confirm's stderr dropped (a plant,
  cv 01a150b1) -/
  dropHint : Bool := false
  /-- the reopen is handed the GENESIS base, not the newest, and replays the whole log (a plant,
  PROTOCOL-53) -/
  staleBase : Bool := false
  /-- the client runs every write command twice (a plant, PROTOCOL-53) -/
  twiceEach : Bool := false
  /-- an invoke's range is signed at the listing the actor's follow held before it caught up (a
  plant, item 4) -/
  staleRange : Bool := false
  /-- the client drops an invoke's `--range` (a plant, item 4) -/
  dropRange : Bool := false
  /-- follow takes the writer's first step as its base on a `beforeLog` and reads again (a plant,
  cv 01a151bc-6ef3) -/
  actOnBeforeLog : Bool := false
  /-- `read OBJ ?` drops its `doc` line (a plant, cv 01a151bc-6f0b) -/
  dropDoc : Bool := false
  /-- custody signs a cancel's message with `domCancel` dropped (a plant, PROTOCOL-63) -/
  cancelUndomained : Bool := false

def skipJudge (X : Ctx D) : Ctx D :=
  { X with program := { X.program with judge := fun _ _ _ _ _ _ => .ok () } }

/-- The keyed account id with its owner dropped: `accountId`'s hash sees only the asset (the
second half of `owner ‖ asset`, both digests of one width). -/
def accountByAsset (X : Ctx D) : Ctx D :=
  { X with env := { X.env with hash := fun dom b =>
      if dom = domAccount then X.env.hash dom (b.extract (b.size / 2) b.size) else X.env.hash dom b } }

/-- The run's system under the parameters `R`, mutated by a plant. -/
def sys (R : Rows.Params D) : Option Mutation → Sys D
  | none => { writer := { R, X := R.ctx }, follow := R.ctx }
  | some .openLog => { writer := { R, X := R.ctx, gateLog := false }, follow := R.ctx }
  | some .skipJudge => { writer := { R, X := skipJudge R.ctx }, follow := skipJudge R.ctx }
  | some .followVerifyAll =>
      { writer := { R, X := R.ctx }, follow := { R.ctx with verify := fun _ _ _ => true } }
  | some .forgetJournal => { writer := { R, X := R.ctx, forgetJournal := true }, follow := R.ctx }
  | some .resendFresh => { writer := { R, X := R.ctx }, follow := R.ctx, resendFresh := true }
  | some .zeroDeadline => { writer := { R, X := R.ctx }, follow := R.ctx, zeroDeadline := true }
  | some .advanceOnSend => { writer := { R, X := R.ctx }, follow := R.ctx, advanceOnSend := true }
  | some .lieTip => { writer := { R, X := R.ctx, lieTip := true }, follow := R.ctx }
  | some .forgeBase => { writer := { R, X := R.ctx, forgeBase := true }, follow := R.ctx }
  | some .unstatedExpiry => { writer := { R, X := R.ctx, unstatedExpiry := true }, follow := R.ctx }
  | some .ignoreNotBefore => { writer := { R, X := R.ctx, ignoreNotBefore := true }, follow := R.ctx }
  | some .forgottenRefused => { writer := { R, X := R.ctx, forgottenRefused := true }, follow := R.ctx }
  | some .nonceRepeats => { writer := { R, X := R.ctx }, follow := R.ctx, nonceRepeats := true }
  | some .accountByAsset =>
      { writer := { R, X := accountByAsset R.ctx }, follow := accountByAsset R.ctx }
  | some .writerForgetsSpent => { writer := { R, X := R.ctx, forgetSpent := true }, follow := R.ctx }
  | some .importTrustsFile => { writer := { R, X := R.ctx }, follow := R.ctx, importTrustsFile := true }
  | some .admitsRecorded => { writer := { R, X := R.ctx, admitsRecorded := true }, follow := R.ctx }
  | some .settleDecline => { writer := { R, X := R.ctx }, follow := R.ctx, settleDecline := true }
  | some .trustFirstUse => { writer := { R, X := R.ctx }, follow := R.ctx, trustFirstUse := true }
  | some .oneMember => { writer := { R, X := R.ctx }, follow := R.ctx, oneMember := true }
  | some .guessMethod => { writer := { R, X := R.ctx }, follow := R.ctx, guessMethod := true }
  | some .trustReceipt => { writer := { R, X := R.ctx }, follow := R.ctx, trustReceipt := true }
  | some .trustLookup => { writer := { R, X := R.ctx }, follow := R.ctx, trustLookup := true }
  | some .sealIgnored => { writer := { R, X := R.ctx }, follow := R.ctx, sealIgnored := true }
  | some .lieBase => { writer := { R, X := R.ctx, lieBase := true }, follow := R.ctx }
  | some .rawSlots => { writer := { R, X := R.ctx }, follow := R.ctx, rawSlots := true }
  | some .pageIoFatal => { writer := { R, X := R.ctx }, follow := R.ctx, pageIoFatal := true }
  | some .dropRow => { writer := { R, X := R.ctx }, follow := R.ctx, dropRow := true }
  | some .noReadLimit => { writer := { R, X := R.ctx }, follow := R.ctx, noReadLimit := true }
  | some .flatProgram => { writer := { R, X := R.ctx }, follow := R.ctx, flatProgram := true }
  | some .maskIncoming => { writer := { R, X := R.ctx }, follow := R.ctx, maskIncoming := true }
  | some .guessedBudget => { writer := { R := { R with pageBudget := 16384 }, X := R.ctx }, follow := R.ctx }
  | some .dropHint => { writer := { R, X := R.ctx }, follow := R.ctx, dropHint := true }
  | some .staleBase => { writer := { R, X := R.ctx }, follow := R.ctx, staleBase := true }
  | some .twiceEach => { writer := { R, X := R.ctx }, follow := R.ctx, twiceEach := true }
  | some .staleRange => { writer := { R, X := R.ctx }, follow := R.ctx, staleRange := true }
  | some .dropRange => { writer := { R, X := R.ctx }, follow := R.ctx, dropRange := true }
  | some .actOnBeforeLog => { writer := { R, X := R.ctx }, follow := R.ctx, actOnBeforeLog := true }
  | some .dropDoc => { writer := { R, X := R.ctx }, follow := R.ctx, dropDoc := true }
  | some .cancelUndomained => { writer := { R, X := R.ctx }, follow := R.ctx, cancelUndomained := true }

/-! ## Actors -/

def founders : List String := ["sponsor", "operator"]

/-- Custody's secret of generation `gen`. Its public key is the run's `Params.pub` of it (under the
toy parameters the secret itself; at the deployed ones the Ed25519 public key of its seed). -/
def secretOf (name : String) (gen : Nat) : ByteArray := s!"key:{name}:{gen}".toUTF8

/-- The public key of custody's secret of generation `gen`. -/
def keyOf (R : Rows.Params D) (name : String) (gen : Nat) : ByteArray := R.pub (secretOf name gen)

structure Actor (D : Type) [Ord D] where
  self : Self D
  /-- the actor's `host follow`: its World and any base download in progress -/
  follow : Command.Follow D
  /-- custody: current key generation `gen`; next is `gen + 1`, pending `gen + 2` -/
  gen : Nat := 0
  /-- the attempt store: the last call this actor froze -/
  last : Option ByteArray := none
  /-- custody signed a rotation with the next key; the next frozen call is the rotation attempt -/
  arming : Bool := false
  /-- the rotation attempt: its settlement as committed advances custody (CLIENT-13) -/
  armed : Option ByteArray := none

/-- Custody's secrets: the current key's, the next one's and the pending one's. -/
def Actor.key (n : String) (a : Actor D) : ByteArray := secretOf n a.gen
def Actor.next (n : String) (a : Actor D) : ByteArray := secretOf n (a.gen + 1)
def Actor.pending (n : String) (a : Actor D) : ByteArray := secretOf n (a.gen + 2)

/-- One line's measured run. -/
structure Timed where
  line : Nat
  ns : List Nat

/-- One measured invoke (THE BAR's WASTE lines): the machine ticks of the method run and its
extraction, the steps it requires (the reference derivations' sizes), the ticks under the plant
`wasteStep`, and the packages its closure loaded and re-checked. -/
structure Invoked where
  ticks : Nat
  required : Nat
  planted : Nat
  /-- the ticks with extraction run twice on the same value (cv 01a14abb-aa73) -/
  extracted : Nat
  pkgs : Nat

structure St (D : Type) [Ord D] where
  sys : Sys D
  host : Writer.Running D
  mem : Writer.Mem
  genesis : World D
  /-- the origin of the lineage's FIRST genesis: founder ids are names minted there, and a carry
  keeps them (KERNEL-40, opacity); never recompute them from a carried World's origin -/
  lineage : D
  /-- the lineage's FIRST genesis World (height 0): what a follower Store from before a carry holds -/
  first : World D
  carriedFile : Option ByteArray := none
  actors : List (String × Actor D) := []
  binds : List (String × String) := []
  ops : List Op := []
  kinds : List String := []
  conn : Nat := 0
  log : Array String := #[]
  times : Array Timed := #[]
  reopenNs : List Nat := []
  /-- each measured reopen: the segment bytes it read, the segment bytes past the newest base it
  had to read, and whether it was handed a base older than the newest -/
  reopenReads : List (Nat × Nat × Bool) := []
  /-- each invoke a client froze whose run the receiver admits: what it cost (`Invoked`), or why
  its required count failed (THE BAR is then broken by that name, never short one sample) -/
  invokes : Array (Except String Invoked) := #[]
  /-- every call the attempt store settled as committed, in order: the writer's log, as its clients
  sent it -/
  committed : Array ByteArray := #[]
  /-- the rows' founding invitation: the sponsor's, at genesis, pinning the genesis World -/
  invitation : ByteArray := ByteArray.empty
  /-- the stderr of the command that ended last (`ByteArray.empty` if it ended in the harness) -/
  lastErr : ByteArray := ByteArray.empty
  /-- the attempt's hint: the last confirm or probe `receipt CALL` stderr that was not empty and at
  most `Bounds.hintBytesMax` bytes, as nd's attempt store keeps it (cv 01a150b1) -/
  hint : ByteArray := ByteArray.empty

abbrev M (D : Type) [Ord D] := StateT (St D) IO

def X : M D (Ctx D) := do pure (← get).sys.follow

/-- The run's parameters. -/
def params : M D (Rows.Params D) := do pure (← get).sys.writer.R

def note (s : String) : M D Unit := modify fun st => { st with log := st.log.push s }

def sawOp (op : Op) : M D Unit :=
  modify fun st => if st.ops.contains op then st else { st with ops := st.ops ++ [op] }

/-- The receiver kind of a call: its `Body` constructor (Protocol.Rows' `kinds`). -/
def kindName : Body D → String
  | .enroll .. => "enroll" | .rotate .. => "rotate" | .install .. => "install"
  | .create .. => "create" | .write .. => "write" | .law .. => "law" | .invoke .. => "invoke"
  | .grant .. => "grant" | .revoke .. => "revoke"
  | .issue .. => "issue" | .account .. => "account" | .transfer .. => "transfer" | .credit .. => "credit"

/-- What an invoke's run costs, measured on the World the call was planned on (the actor's
follow, caught up to the writer's tip): the receiver's own inputs (`invokeRun` over the call's
pins), then LANG's `runMeasured`, whose first component IS the deployed `Program.run`. A call
whose run refuses costs nothing here (it is not admitted: `none`). For an admitted one, the
required steps (`Lang.Need.requiredOf`, the size of the run's reference derivation and of the
suspensions extraction forces, `Lang.Proofs.Need.required_counts_the_run`), and the ticks under
the plant: the method run on `Lang.Need.wasteStep` in place of the deployed step, which costs
two needless transitions per application. A count that fails is an error by name. -/
def measureInvoke (X : Ctx D) (w : World D) (c : Call D) : Option (Except String Invoked) :=
  match c.unsigned.body with
  | .invoke obj method args budget via =>
    let look := pinned X.env w c.unsigned.pins
    let rv := rowView X.env w c.unsigned
    match invokeRun X look c c.unsigned.member obj method via with
    | .ok (cell, p, r) =>
      match Lang.runMeasured X.env.bytes X.digestOf look rv p (stateOf cell) method args r budget with
      | .ok (_, _, _, ticks, pkgs) =>
        let text : Receive.Refusal D → String := fun | .program s => s | e => e.name
        let count := do
          let required ← Lang.Need.requiredOf X.env.bytes X.digestOf look rv p (stateOf cell) method
            args r budget
          let honest ← Lang.Need.runTicksBy X.env.bytes X.digestOf Lang.step look rv p (stateOf cell)
            method args r budget
          let wasted ← Lang.Need.runTicksBy X.env.bytes X.digestOf Lang.Need.wasteStep look rv p
            (stateOf cell) method args r budget
          let (once, twice) ← Lang.Need.extractTicksTwice X.env.bytes X.digestOf look rv p (stateOf cell)
            method args r budget
          if once ≠ ticks then throw (Receive.Refusal.program s!"extraction recount {once} is not the run's {ticks}")
          pure ({ ticks, required, planted := ticks - honest + wasted, extracted := twice, pkgs } : Invoked)
        some (count.mapError text)
      | .error _ => none
    | .error _ => none
  | _ => none

def sawCall (name : String) (call : ByteArray) : M D Unit := do
  let decoded := (← get).sys.writer.R.ctx.decodeCall call
  let k := match decoded with
    | some c => kindName c.unsigned.body
    | none => "undecodable"
  modify fun st => if st.kinds.contains k then st else { st with kinds := st.kinds ++ [k] }
  if let (some c, some a) := (decoded, (← get).actors.lookup name) then
    if let some m := measureInvoke (← get).sys.writer.X a.follow.world c then
      modify fun st => { st with invokes := st.invokes.push m }

def founderIndex (name : String) : Option Nat := founders.idxOf? name

/-- How a joiner decides an invitation: `Invite.accept` under the key it trusts; under the plant
`trustFirstUse`, the shape before PROTOCOL-42: the inputs as they arrive, signer and signature
unchecked. -/
def acceptAs (s : Sys D) (key bytes : ByteArray) : Except Invite.Refusal (Invite.Invitation D × World D) :=
  if s.trustFirstUse then
    match Invite.ofBytes s.follow bytes with
    | none => .error .badInvitation
    | some i => match Invite.startGenesis s.follow i.start with
      | .ok w => .ok (i, w)
      | .error r => .error r
  else Invite.accept s.follow key bytes

def flipLast (b : ByteArray) : ByteArray :=
  if h : 0 < b.size then b.set (b.size - 1) (b[b.size - 1] ^^^ 1) (by omega) else b

/-- A sponsor-signed invitation to the imported origin, using the retained export as IN. -/
def acceptCarried (st : St D) (wrongOrigin : Bool := false) : Except String (World D) := do
  let some file := st.carriedFile | throw "noCarry"
  let X := st.sys.follow
  let R := st.sys.writer.R
  let r ← (Host.Carry.read X.env R.dc file).mapError (·.name)
  let origin := if wrongOrigin then st.first.origin else st.genesis.origin
  let start := Invite.Start.carried origin Rows.Params.worldName (flipLast Rows.Params.nonce)
    r.head.fromOrigin r.head.height r.head.chain
  let some u := Invite.unsignedBytes X (Invite.startBytes X start)
      ⟨st.genesis.steps, R.keys.worldDigest (R.world.bytes st.genesis)⟩
      (founderId X st.lineage 0) (keyOf R "sponsor" 0) | throw "invitationTooLarge"
  let some b := Invite.bytes u (R.sign (secretOf "sponsor" 0) (Invite.message u)) | throw "invitationTooLarge"
  let (i, _) ← (Invite.acceptStart X (keyOf R "sponsor" 0) b).mapError (·.name)
  let .carried o name nonce _ _ _ := i.start | throw "notCarried"
  let pin := if st.sys.importTrustsFile then Host.Carry.Pin.digest (Host.Carry.digestOf file) else .origin o
  let (w, _) ← (Host.Carry.importWorld X R.dc name nonce pin file).mapError (·.2)
  pure w

def freshActor (name : String) : M D (Actor D) := do
  let st ← get
  let X := st.sys.writer.X
  -- a founder's World is its own genesis; a joiner's is what the founding invitation makes, or,
  -- after a carry, the World reconstructed under the sponsor-signed carried origin
  let w ← match founderIndex name with
    | some _ =>
      if st.carriedFile.isSome then
        match acceptCarried st with
        | .ok w => pure w
        | .error e => throw (IO.userError e)
      else pure st.genesis
    | none =>
      if st.carriedFile.isSome then
        match acceptCarried st with
        | .ok w => pure w
        | .error e => throw (IO.userError e)
      else
      match acceptAs st.sys (keyOf st.sys.writer.R "sponsor" 0) st.invitation with
      | .ok (_, w) => pure w
      | .error r => throw (IO.userError s!"the founding invitation refused {r.name}")
  let self : Self D := match founderIndex name with
    | some i => { world := w.origin, member := founderId X st.lineage i, grant := founderGrantId X st.lineage i,
                  window := 100 }
    | none => { world := w.origin, member := X.env.hash "nanodregg/rows/stranger/v1" name.toUTF8,
                grant := X.env.hash "nanodregg/rows/stranger-grant/v1" name.toUTF8, window := 100 }
  pure { self, follow := { world := w } }

def actor (name : String) : M D (Actor D) := do
  match (← get).actors.lookup name with
  | some a => pure a
  | none =>
      let a ← freshActor name
      modify fun st => { st with actors := st.actors ++ [(name, a)] }
      pure a

def setActor (name : String) (a : Actor D) : M D Unit :=
  modify fun st => { st with actors := st.actors.map fun (n, b) => if n = name then (n, a) else (n, b) }

/-- Bind `b` to `hex`; a bound member id, or a World grant bound as `NAME.grant`, becomes that
actor's. -/
def bind (b hex : String) : M D Unit := do
  modify fun st => { st with binds := (b, hex) :: st.binds }
  let some d := Text.ofHex hex >>= (← params).ctx.digestOf | return
  let (who, isFollow) := if b.endsWith ".grant" then ((b.dropEnd 6).toString, true) else (b, false)
  if (← get).actors.any (·.1 = who) then
    let a ← actor who
    setActor who (if isFollow then { a with self := { a.self with grant := d } }
                  else { a with self := { a.self with member := d } })

/-- The most `{@NAME}` one argument substitutes. -/
def substMax : Nat := 64

/-- Every `{@NAME}` inside a text argument replaced by the hex `NAME` is bound to (a seed naming a
member: `(owner #{@sponsor})`). -/
def substInner (binds : List (String × String)) : Nat → String → Except String String
  | 0, s => .ok s
  | fuel + 1, s =>
    match s.splitOn "{@" with
    | [_] => .ok s
    | pre :: rest =>
      let tail := "{@".intercalate rest
      match tail.splitOn "}" with
      | name :: after => match binds.lookup name with
        | some v => (substInner binds fuel ("}".intercalate after)).map (pre ++ v ++ ·)
        | none => .error s!"unbound @{name}"
      | [] => .error s!"unclosed in {s}"
    | [] => .ok s

/-- A line's argv as the member's shell would hand it to `nd`: `@NAME` is the hex bound to NAME,
`{@NAME}` the same inside a text, and `<PATH` the text of the file PATH in this tree (a shipped
package, `nd install "$(cat PATH)"`). -/
def subst (argv : List String) : M D (Except String (List String)) := do
  let binds := (← get).binds
  let mut out : Array String := #[]
  for a in argv do
    if a.startsWith "@" then
      match binds.lookup (a.drop 1).toString with
      | some v => out := out.push v
      | none => return .error s!"unbound {a}"
    else if a.startsWith "<" then
      match ← (IO.FS.readFile (a.drop 1).toString).toBaseIO with
      | .ok t => out := out.push t
      | .error e => return .error s!"{a}: {e}"
    else match substInner binds substMax a with
      | .ok t => out := out.push t
      | .error e => return .error e
  return .ok out.toList

/-- The first `id HEX`, `join HEX` or `invite HEX` a command printed. -/
def boundToken (out : String) : Option String :=
  (out.splitOn "\n").findSome? fun l =>
    match l.splitOn " " with
    | ["id", h] => some h
    | ["join", h] => some h
    | ["invite", h] => some h
    | ["receipt", h] => some h
    | _ => none

/-! ## Custody and the writer's socket -/

/-- Custody's answer to a sign step: `ok ‖ (key, next, signature)` (every step result is
`status ‖ payload`); `stolen` replaces the key it signs
with (a thief holding a victim's current key). -/
def signWith (R : Rows.Params D) (key next msg : ByteArray) : ByteArray :=
  match Text.fit Bounds.frameBytesMax (R.pub key), Text.fit Bounds.frameBytesMax (R.pub next),
      Text.fit Bounds.frameBytesMax (R.sign key msg) with
  | some k, some n, some s => ByteArray.mk #[Status.ok.code] ++ signResultFrame.bytes (k, n, s, ())
  | _, _, _ => ByteArray.empty

def precommitResult (R : Rows.Params D) (next pending : ByteArray) : ByteArray :=
  match Text.fit Bounds.frameBytesMax (R.pub next), Text.fit Bounds.frameBytesMax (R.pub pending) with
  | some n, some p => ByteArray.mk #[Status.ok.code] ++ precommitResultFrame.bytes (n, p, ())
  | _, _ => ByteArray.empty

/-- The actor's custody name and current key under a fault (a thief signs with a stolen key). -/
def custodyOf (name : String) (fault : Fault) : M D (String × Actor D × ByteArray) := do
  let a ← actor name
  match fault with
  | .stolenKey v => let va ← actor v; pure (name, a, va.key v)
  | _ =>
    if (← get).sys.oneMember then let sa ← actor "sponsor"; pure (name, a, sa.key "sponsor")
    else pure (name, a, a.key name)

/-- The member the actor's client signs as: its own, a victim's (`stolenKey`), or under the plant
`oneMember` the sponsor's. -/
def selfOf (name : String) (fault : Fault) : M D (Self D) := do
  match fault with
  | .stolenKey v => pure (← actor v).self
  | .wrongFollower o => pure (← actor o).self
  | _ => if (← get).sys.oneMember then pure (← actor "sponsor").self else pure (← actor name).self

/-- Custody settles its armed rotation on the attempt's END, which only the member's own follow
makes final (PROTOCOL-46): committed advances it, refused drops it; declined, open, contradicted or
uncertain keeps it armed (CLIENT-13, PROTOCOL-41). -/
def settle (name : String) (call : ByteArray) (a : Attempt.Action) : M D Unit := do
  let ac ← actor name
  if ac.armed = some call then
    match a with
    | .committed => setActor name { ac with gen := ac.gen + 1, armed := none }
    | .refused => setActor name { ac with armed := none }
    | _ => pure ()

/-- Custody's refusal of a step, as its result (`refused ‖ custodyRefusalLayout`: one byte, the
refusal's code), as the client's custody writes it. -/
def custodyRefused (r : CustodyRefusal) : ByteArray :=
  ByteArray.mk #[Status.refused.code, r.code]

/-- Custody's `signIncoming` (CLIENT-13 amended): only a read envelope's message, only while a
rotation is armed (in flight), signed by the incoming (next) key. -/
def signIncoming (name : String) (msg : ByteArray) : M D ByteArray := do
  let a ← actor name
  if msg.extract 0 domEnvelope.size ≠ domEnvelope then
    pure (custodyRefused .envelopeOnly)
  else if a.armed.isNone then pure (custodyRefused .notArmed)
  else pure (signWith (← params) (a.next name) (a.pending name) msg)

/-- Send one frame to the writer; its reply as `status ‖ payload`, or `none` if it has stopped. -/
def ask (op : Op) (payload : ByteArray) : M D (Option ByteArray) := do
  sawOp op
  let st ← get
  set { st with conn := st.conn + 1 }
  match ← st.host.ask ⟨UInt32.ofNat st.conn, op.code, payload⟩ with
  | some r => pure (some (ByteArray.mk #[r.status] ++ r.payload))
  | none => pure none

/-- How the rows' followers read a base: the run's World codec and the writer's own `worldDigest`. -/
def base (R : Rows.Params D) : Thin.Base (World D) :=
  ⟨R.world, World.steps, R.keys.worldDigest, Host.Cadence.deployed.worldBytesMax⟩

/-- Send one frame to the actor's `host follow` (`Host.Follow.answer`, the deployed per-frame
decision, on the actor's follow state); the step's bytes, or the name follow refused it by. What
follow would persist is not modelled here: the actor's state is in memory. -/
def followAsk (name : String) (self : Self D) (op : Op) (payload : ByteArray) :
    M D (Except String ByteArray) := do
  sawOp op
  let a ← actor name
  let st ← get
  set { st with conn := st.conn + 1 }
  let (fs', _, status, p) :=
    Host.Follow.answer (← X) (← params).dc (base (← params)) self a.follow ⟨UInt32.ofNat st.conn, op.code, payload⟩
  setActor name { a with follow := fs' }
  pure (if status = Status.ok.code then .ok p else .error (Command.hostName p))

/-! ## Transport faults on a log page -/


def editPage (f : List ByteArray → List ByteArray) (reply : ByteArray) : ByteArray :=
  match Command.hostReply reply with
  | some (.ok, p) =>
      match logReplyFrame.decode p with
      | .ok (l, n, c, t, th, bs, bd, ()) =>
          match Text.fitList Bounds.frameBytesMax (f (Text.unlist l)) with
          | some l' => ByteArray.mk #[Status.ok.code] ++ logReplyFrame.bytes (l', n, c, t, th, bs, bd, ())
          | none => reply
      | .error _ => reply
  | _ => reply

/-- A cancel event (tag 2) with the first byte of its signature (byte 9, after the tag and the
eight-byte length) flipped; any other event as it is. -/
def forgeCancelSig (e : ByteArray) : ByteArray :=
  if h : 9 < e.size then
    if e[0]'(by omega) = eventCancel then e.set 9 (e[9] ^^^ 1) (by omega) else e
  else e

def pageFault : Fault → ByteArray → ByteArray
  | .flipEvent i => editPage fun evs => evs.mapIdx fun j e => if j = i then flipLast e else e
  | .forgeCancel => editPage fun evs => evs.map forgeCancelSig
  | .dropLastEvent => editPage List.dropLast
  | .inflateExpired n => fun reply =>
      match Command.hostReply reply with
      | some (.refused, p) => match expiredHeight? p with
        | some h => ByteArray.mk #[Status.refused.code] ++ (ReadRefusal.expired (h + n)).payload
        | none => reply
      | _ => reply
  | _ => id

def coldFault : Fault → Bool
  | .flipEvent _ | .dropLastEvent | .cold | .inflateExpired _ | .forgeCancel => true
  | _ => false

/-! ## The attempt store -/

/-- A reply, as the attempt decision sees it (its status byte; no reply at all is `lost`). -/
def classify (res : ByteArray) : Attempt.Seen :=
  match Command.hostReply res with
  | some (.ok, _) => .committed
  | some (.refused, _) => .refused
  | some (.declined, _) => .declined
  | some (.uncertain, _) => .unknown
  | some (.absent, _) => .absent
  -- the connection ended with the request unanswered: as if the reply were lost
  | some (.closed, _) | none => .lost

/-- Requests one attempt may make in one run: every send, at most one lookup after each
(`Proofs.Attempt.next_after_lookup`) and one probe after that lookup (an absent lookup is confirmed
with follow before any resend, `Proofs.Attempt.next_absent_probes`), one confirm, and one more for
the decision that ends it. -/
def attemptFuel : Nat := 3 * Bounds.sendsMax + 3

/-- Follow's `settle` line in a `receipt CALL` output: what the attempt store sees, and its text. -/
def settleOf (out : String) : Option (Attempt.Seen × String) :=
  (out.splitOn "\n").findSome? fun l =>
    match l.splitOn " " with
    | "settle" :: w :: rest => (Attempt.settleSeen w).map (·, " ".intercalate (w :: rest))
    | _ => none

/-- The attempt's end as nd hands it to follow: `u8 Action.code ‖ payload`. -/
def ended (a : Attempt.Action) (payload : String) : ByteArray :=
  ByteArray.mk #[a.code] ++ payload.toUTF8

/-! ## One command -/

def outcomeOf (exit : UInt8) (err : ByteArray) : Expect :=
  let e := (String.fromUTF8? err).getD ""
  match CommandExit.ofCode? exit.toNat with
  | some .ok => .ok
  | some .refused => .refused (((e.trimAscii.toString.dropPrefix? "refused ").map (·.toString)).getD e)
  | some .uncertain => .uncertain
  | some .open => .open
  | some .hostContradicted =>
      .contradicted (((e.trimAscii.toString.dropPrefix? "hostContradicted ").map (·.toString)).getD e)
  | some .behind => .behind
  | some .declined => .declined (((e.trimAscii.toString.dropPrefix? "declined ").map (·.toString)).getD e)
  | some .pageIo => .pageIo
  | some .client | none => .refused s!"exit{exit.toNat}"

def statusOutcome (reply : ByteArray) : Expect :=
  match Command.hostReply reply with
  | some (.ok, _) => .ok
  | some (.absent, _) => .absent
  | some (.uncertain, p) => if p.isEmpty then .uncertain else .unsettled (Command.hostName p)
  | some (.refused, p) => .refused (Command.hostName p)
  | some (.declined, p) => .declined (Command.hostName p)
  -- a closed connection is not a verdict on the call
  | some (.closed, _) => .uncertain
  | none => .refused "badReply"

mutual
/-- Run `argv` as actor `name`: start, then every step through the wire until `done`. -/
def command (name : String) (argv : List String) (fault : Fault) : Nat → M D (Expect × String)
  | 0 => pure (.refused "tooDeep", "")
  | depth + 1 => do
      modify fun st => { st with lastErr := ByteArray.empty }
      let a ← actor name
      let gw := (← get).genesis
      let a := if coldFault fault then { a with follow := { world := gw } } else a
      setActor name a
      let self ← selfOf name fault
      let some argvF := (Text.fitList Bounds.argvBytesMax (argv.map String.toUTF8)).bind fun v =>
          if h : (Codec.Layout.codec Bounds.argvBytesMax (by decide) commandLayout).size (v, ()) ≤
              Bounds.argvBytesMax then some (⟨(v, ()), h⟩ : { v : Codec.Layout.Ty Bounds.argvBytesMax commandLayout //
                (Codec.Layout.codec Bounds.argvBytesMax (by decide) commandLayout).size v ≤ Bounds.argvBytesMax })
            else none
        | pure (.refused "argvPastBound", "")
      match ← followAsk name self .command (commandFrame.bytes argvF) with
      | .error n => pure (.refused n, "")
      | .ok b => steps name argv fault depth b Bounds.stepsPerCommandMax
termination_by d => (d, 0, 0)

/-- Feed a step's result back to follow, through the resume frame. -/
def resume (name : String) (argv : List String) (fault : Fault) (depth : Nat) (k result : ByteArray) :
    Nat → M D (Expect × String)
  | 0 => pure (.refused "tooManySteps", "")
  | fuel + 1 => do
      let some kf := Text.fit Bounds.frameBytesMax k | return (.refused "badState", "")
      let some rf := Text.fit Bounds.frameBytesMax result | return (.refused "badResult", "")
      let self ← selfOf name fault
      match ← followAsk name self .resume (resumeFrame.bytes (kf, rf, ())) with
      | .error n => pure (.refused n, "")
      | .ok b => steps name argv fault depth b fuel
termination_by fuel => (depth, fuel + 1, 0)

/-- Perform one step the follow machine asked for. -/
def steps (name : String) (argv : List String) (fault : Fault) (depth : Nat) (b : ByteArray) :
    Nat → M D (Expect × String)
  | 0 => pure (.refused "tooManySteps", "")
  | fuel + 1 => do
      match Reply.ofBytes b with
      | none => pure (.refused "badFrame", "")
      | some (.done exit out err) =>
          -- the plant: `pageIo` read as the old final refusal, verbatim (exit 1, `refused pageIo`)
          let (exit, err) := if (← get).sys.pageIoFatal && exit.toNat == CommandExit.pageIo.code then
              (CommandExit.refused.code.toUInt8, s!"refused {pageIoName}\n".toUTF8) else (exit, err)
          modify fun st => { st with lastErr := err }
          pure (outcomeOf exit err, (String.fromUTF8? out).getD "")
      | some (.sign msg k) =>
          let (n, a, key) ← custodyOf name fault
          -- the plant: a cancel's message signed without its domain (the bare transaction id)
          let msg := if (← get).sys.cancelUndomained && msg.extract 0 domCancel.size == domCancel then
              msg.extract domCancel.size msg.size else msg
          resume name argv fault depth k (signWith (← params) key (a.next n) msg) fuel
      | some (.precommit k) =>
          let a ← actor name
          resume name argv fault depth k (precommitResult (← params) (a.next name) (a.pending name)) fuel
      | some (.signNext msg k) =>
          let a ← actor name
          let r := signWith (← params) (a.next name) (a.pending name) msg
          setActor name (if (← get).sys.advanceOnSend then { a with gen := a.gen + 1 } else { a with arming := true })
          resume name argv fault depth k r fuel
      | some (.signIncoming msg k) =>
          -- `nd --stdio`'s custody refuses every rotation step (`client/src/custody.rs`)
          let r ← match fault with
            | .wrongFollower _ => pure (custodyRefused .noRotation)
            | _ => signIncoming name msg
          match (← get).sys.maskIncoming, Command.custodyResult (D := D) r with
          | true, .error e => pure (.refused e.name, "")
          | _, _ => resume name argv fault depth k r fuel
      | some (.host op p k) =>
          match ← ask op p with
          | none => pure (.refused "writerStopped", "")
          | some res =>
              let res := match fault with
                | .pageIo => if op = .log || op = .read then
                    ByteArray.mk #[Host.pageIoReply.1] ++ Host.pageIoReply.2 else res
                | _ => res
              resume name argv fault depth k (if op = .log then pageFault fault res else res) fuel
      | some (.submit call k) => do
          sawCall name call
          let a ← actor name
          setActor name { a with last := some call, arming := false,
                                 armed := if a.arming then some call else a.armed }
          match fault with
          | .race other otherArgv =>
              match ← subst otherArgv with
              | .error e => return (.refused e, "")
              | .ok av =>
                  let (o, _) ← command other av .none depth
                  if o ≠ .ok then return (.refused s!"race:{o.text}", "")
          | _ => pure ()
          match fault, (← get).sys.resendFresh with
          | .dropReply, true =>
              -- the plant: the reply is lost and the client signs the command afresh
              let _ ← ask .submit call
              command name argv .none depth
          | _, _ =>
              modify fun st => { st with hint := ByteArray.empty }
              match ← drive name call fault depth attemptFuel 0 none none none "" with
              | .error e => pure (.refused e, "")
              | .ok res => resume name argv fault depth k res fuel
termination_by fuel => (depth, fuel + 1, 0)

/-- The attempt store settles the frozen `call` with `Protocol.Attempt.next` deciding every
request (PROTOCOL-17, PROTOCOL-46): the rows run the decision CLIENT-3 runs, not a restatement of
it. The Host's status drives the loop; `confirm` and `probe` are the actor's own follow command
`receipt CALL`, whose `settle` line ends the attempt. Faults: `dropReply` loses the reply to the
FIRST submit after the writer took it; `lieLookup` does that and rewrites the Host's lookup `ok` as
`refused stale`; `neverForward` keeps every submit from reaching the writer. The attempt's end,
`u8 Action.code ‖ payload`, is what follow is resumed with; custody settles an armed rotation on
it. `host` is the Host's last word, `said` follow's settle text. -/
def drive (name : String) (call : ByteArray) (fault : Fault) (depth : Nat) :
    Nat → Nat → Option (Attempt.Request × Attempt.Seen) → Option ByteArray → Option Attempt.Seen →
      String → M D (Except String ByteArray)
  | 0, _, _, _, _, _ => pure (.error "attemptFuel")
  | fuel + 1, sends, last, reply, host, said => do
      let hostSaid (r : ByteArray) : Attempt.Seen := classify r
      let a := Attempt.next (decide (sends < Bounds.sendsMax)) last
      match a with
      | .submit =>
          match fault with
          | .neverForward => drive name call fault depth fuel (sends + 1) (some (.submit, .lost)) reply host said
          | _ =>
              match ← ask .submit call with
              | none => pure (.error "writerStopped")
              | some res =>
                  match fault, sends with
                  | .dropReply, 0 | .lieLookup, 0 =>
                      drive name call fault depth fuel (sends + 1) (some (.submit, .lost)) reply host said
                  | _, _ =>
                      drive name call fault depth fuel (sends + 1) (some (.submit, hostSaid res)) (some res) (some (hostSaid res)) said
      | .lookup =>
          match ← ask .lookup call with
          | none => pure (.error "writerStopped")
          | some res =>
              let res := match fault, Command.hostReply res with
                | .lieLookup, some (.ok, _) => ByteArray.mk #[Status.refused.code] ++ "stale".toUTF8
                | _, _ => res
              drive name call fault depth fuel sends (some (.lookup, hostSaid res)) (some res)
                (some (hostSaid res)) said
      | .confirm | .probe =>
          let req : Attempt.Request := if a = .confirm then .confirm else .probe
          if (← get).sys.trustLookup && a = .confirm then
            -- the plant: the Host's word taken as final
            let s := host.getD .lost
            let txt := match s, reply with
              | .refused, some r => match Command.hostReply r with
                | some (_, p) => Command.hostName p
                | none => ""
              | _, _ => s.name
            drive name call fault depth fuel sends (some (.confirm, s)) reply host txt
          else
            let (o, out) ← command name ["receipt", Text.toHex call] .none depth
            match (if o = .ok then settleOf out else none) with
            | some (s, txt) => drive name call fault depth fuel sends (some (req, s)) reply host txt
            | none =>
                -- nd's attempt store keeps the receipt's stderr: the last one not empty and in bound
                let e := (← get).lastErr
                if !e.isEmpty && e.size ≤ Bounds.hintBytesMax then modify fun st => { st with hint := e }
                drive name call fault depth fuel sends (some (req, .lost)) reply host said
      | .committed =>
          modify fun st => { st with committed := st.committed.push call }
          settle name call .committed
          pure (.ok (ended .committed said))
      | .refused => settle name call .refused; pure (.ok (ended .refused said))
      | .declined =>
          match reply.bind Command.hostReply with
          | some (_, p) =>
              if (← get).sys.settleDecline then
                -- the plant: the Host's decline taken as final, the attempt settled refused
                settle name call .refused
                pure (.ok (ended .refused s!"refused {(staleCode : Nat)}"))
              else pure (.ok (ended .declined (Command.hostName p)))
          | none => pure (.error "noReply")
      | .contradicted =>
          let f := match last with | some (_, s) => s.name | none => ""
          pure (.ok (ended .contradicted s!"{(host.getD .lost).name} {f}"))
      | .open => pure (.ok (ended .open ""))
      | .uncertain =>
          let st ← get
          pure (.ok (ByteArray.mk #[Attempt.Action.uncertain.code] ++ (if st.sys.dropHint then ByteArray.empty else st.hint)))
      | .badReply => pure (.ok (ended .badReply ""))
termination_by fuel => (depth, 0, fuel + 1)
end

/-! ## The operator's and the attempt store's acts -/

def nowNs : IO Nat := IO.monoNanosNow

/-- Stop the loop, open the Store cold (its base and the tail after it), start the loop on what it
opened to. The reopen's wall time is THE BAR's `reopen-ms`. With `sealFirst`, the stopped writer is
sealed between the stop and the reopen by the deployed act, `Host.sealNow` over the in-memory
Store's checkpoint: what `host seal STORE` does over the files (HOST-43), so the rows seal only as
an operator can. -/
def restart (sealFirst : Bool) : M D Expect := do
  let st ← get
  match ← st.host.stop with
  | .error e => pure (.refused s!"writerFailed {e}")
  | .ok (.eof, r0) =>
      if sealFirst && !st.sys.sealIgnored then
        match ← Host.sealNow (Writer.checkpoint st.sys.writer st.mem) (Writer.mark st.sys.writer) r0 with
        | .error f => return .refused f.name
        | .ok _ => pure ()
      let d ← st.mem.disk.get
      let bs ← st.mem.bases.get
      -- The plant targets the measured cold reopen, not the unmeasured setup seal.
      -- That reopen receives the genesis base instead of the newest durable base.
      let base := if st.sys.staleBase && !sealFirst then (bs.history[0]?.map (·.1)).getD bs.file else bs.file
      let t0 ← nowNs
      match Writer.reopenCounted st.sys.writer bs.headers bs.index base d.synced with
      | (.error f, _) => pure (.refused f)
      | (.ok r, n) =>
          let t1 ← nowNs
          st.mem.disk.set { synced := d.synced.extract 0 r.pos.offset }
          let h ← Writer.start st.sys.writer st.mem r
          let ns := if sealFirst then [] else [t1 - t0]
          let rd := if sealFirst then [] else [(n.tail, d.synced.size - r0.sealed.offset, base != bs.file)]
          modify fun st => { st with host := h, reopenNs := st.reopenNs ++ ns,
                                     reopenReads := st.reopenReads ++ rd }
          pure .ok
  | .ok (exit, _) => pure (.refused s!"writer{exit.name}")

/-- Open a copy of the Store whose base file has the byte at `off` flipped. -/
def reopenFlipped (off : Nat) : M D Expect := do
  let st ← get
  let d ← st.mem.disk.get
  let bs ← st.mem.bases.get
  match Writer.reopen st.sys.writer bs.headers bs.index (Host.Sim.flipByte bs.file off) d.synced with
  | .error f => pure (.refused f)
  | .ok _ => pure .ok

def retry (name : String) : M D Expect := do
  match (← actor name).last with
  | none => pure (.refused "noAttempt")
  | some call =>
      -- a probe of a call the attempt store already settled: ONE lookup of the same bytes, so a
      -- journal that forgot it answers `absent` here (reopen's plant), instead of the attempt
      -- decision resending it (which a forgotten journal would admit twice)
      match ← ask .lookup call with
      | none => pure (.refused "writerStopped")
      | some res => pure (statusOutcome res)

/-! ## A row -/

/-- A SECOND writer, from a genesis of the same name, allowance and founders as the rows' writer, and
the same nonce (`sameNonce`, or under the `nonceRepeats` plant: a restore of the same World) or
another one (another World). -/
def secondWriter (sameNonce : Bool) : M D (Except String (Writer.Running D)) := do
  let st ← get
  let X := st.sys.writer.X
  let R := st.sys.writer.R
  let nonce := if sameNonce || st.sys.nonceRepeats then Rows.Params.nonce else flipLast Rows.Params.nonce
  let fs := founders.map fun n => (keyOf R n 0, nextKeyDigest X (keyOf R n 1))
  let g ← match Receive.genesis X Rows.Params.worldName nonce Rows.Params.allowance fs with
    | .ok g => pure g
    | .error r => return .error s!"genesis refused {r.name}"
  match ← Writer.genesisStore st.sys.writer g with
  | .error e => return .error e
  | .ok (mem, r₀) => return .ok (← Writer.start st.sys.writer mem r₀)

/-- An invitation as a relay hands it on under `forgeInvite`: its nonce changed (the relay's own
World), its signature kept, or (`resign`) re-signed by the relay's own key. -/
def forgeInvite (R : Rows.Params D) (X : Ctx D) (resign : Bool) (b : ByteArray) : ByteArray :=
  match Invite.ofBytes X b with
  | none => b
  | some i =>
    let start := match i.start with
      | .genesis name nonce allowance fs => .genesis name (flipLast nonce) allowance fs
      | .carried o name nonce fromO height chain => .carried o name (flipLast nonce) fromO height chain
    let input := Invite.startBytes X start
    let key := if resign then keyOf R "relay" 0 else i.key
    match Invite.unsignedBytes X input i.pin i.sponsor key with
    | none => b
    | some u =>
      let sig := if resign then R.sign (secretOf "relay" 0) (Invite.message u) else i.signature
      (Invite.bytes u sig).getD b

/-- An argv with `--range REL K [PREFIX]` removed (up to `--via`, or the end). -/
def dropRangeFlag : List String → List String
  | [] => []
  | "--range" :: rest => rest.dropWhile (· ≠ "--via")
  | a :: rest => a :: dropRangeFlag rest

/-- The actor's command planned on its follow's World as it stands (no catching up: the World of its
last command), signed and submitted WITHOUT follow's own admission (`planUnchecked`, with the range
reads `rangesOf` lists there). The outcome is the writer's answer. -/
def forged (who : String) (av : List String) : M D (Expect × String) := do
  let a ← actor who
  let X ← X
  let w := a.follow.world
  let R ← params
  let key := R.pub (a.key who)
  match parse (D := D) X.digestOf (av.map String.toUTF8) with
  | .error r => pure (.refused r.name, "")
  | .ok cmd =>
    match body X a.self w ⟨key, R.pub (a.next who), ByteArray.empty⟩ cmd >>= fun b =>
        rangesOf X w cmd >>= fun rs => planUnchecked X a.self w key rs b with
    | .error r => pure (.refused r.name, "")
    | .ok (u, _) =>
      let call := X.callBytes ⟨u, R.sign (a.key who) (X.callMessage u)⟩
      sawCall who call
      -- the forged call is the actor's last: `retry` looks it up, `resubmit` sends it again
      setActor who { a with last := some call }
      match ← ask .submit call with
      | none => pure (.refused "writerStopped", "")
      | some res =>
          if classify res = .committed then
            modify fun st => { st with committed := st.committed.push call }
          pure (statusOutcome res, "")

/-- Run one act once; its outcome and what it printed. -/
def runAct (l : Line) : M D (Expect × String) := do
  match l.act with
  | .cmd argv =>
      match ← subst argv with
      | .error e => pure (.refused e, "")
      | .ok av =>
          -- the plants (item 4): an invoke's range signed at the actor's stale listing; the flag dropped
          if (← get).sys.staleRange && av.contains "--range" then return ← forged l.actor av
          let av := if (← get).sys.dropRange then dropRangeFlag av else av
          let (o, out) ← command l.actor av l.fault 4
          -- the plant: follow acts on the writer's `beforeLog`, taking its first step (the carried
          -- World) as the base on the writer's word, and reads again
          let (o, out) ← if (← get).sys.actOnBeforeLog && o == .refused "beforeLog" then do
              let a ← actor l.actor
              setActor l.actor { a with follow := { world := (← get).genesis } }
              command l.actor av l.fault 4
            else pure (o, out)
          -- the plant: a description with its `doc` line dropped
          let out := if (← get).sys.dropDoc && av.length == 3 && av.getLast? == some "?" then
              "\n".intercalate ((out.splitOn "\n").filter fun ln => !ln.startsWith "doc ")
            else out
          -- the plant: a client that runs every write command again (the line's outcome, output
          -- and binds are the first run's; only the work doubles)
          if (← get).sys.twiceEach && av.head? ≠ some "read" then
            discard <| command l.actor av l.fault 4
          let sy := (← get).sys
          -- the plant: the output of a method's refusal flattened to its verdict, the reason dropped
          if sy.flatProgram && o == .refused "program" then
            return (o, "\n".intercalate ((out.splitOn "\n").filter fun ln => !ln.startsWith "hint program:"))
          if sy.dropRow || sy.noReadLimit then
            let X ← X
            match parse (D := D) X.digestOf (av.map String.toUTF8) with
            | .ok (.rangeRead obj rel k pre) =>
                -- the plants: a reader that loses its first row; one that never checks K
                if sy.dropRow && o == .ok then
                  return (o, "\n".intercalate ((out.splitOn "\n").drop 1))
                if sy.noReadLimit && o == .refused "rangePastLimit" then
                  let w := (← actor l.actor).follow.world
                  match w.live X.env obj with
                  | none => return (o, out)
                  | some cell =>
                    match relationOf X w obj cell rel with
                    | .ok (i, d) =>
                        match rowLines X w obj i d rel k pre with
                        | .ok ts => return (.ok, String.join (ts.map (· ++ "\n")))
                        | .error r => return (.refused r.name, "")
                    | .error _ => return (o, out)
                return (o, out)
            | _ => return (o, out)
          if !sy.rawSlots || o != .ok then return (o, out)
          -- the plant: the object's raw state slots, the shape before PROTOCOL-48
          let X ← X
          match parse (D := D) X.digestOf (av.map String.toUTF8) with
          | .ok (.read obj _) =>
              match (← actor l.actor).follow.world.live X.env obj with
              | some cell => pure (o, String.join ((stateOf cell).map fun (k, v) =>
                  s!"{k - stateBase}={(String.fromUTF8? v).getD (Text.toHex v)}\n"))
              | none => pure (o, out)
          | _ => pure (o, out)
  | .restart => pure (← restart false, "")
  | .seal => pure (← restart true, "")
  | .readElsewhere sameNonce => do
      -- the actor's own log envelope, for its own World, to a SECOND writer (as replayLog's)
      let st ← get
      let a ← actor l.actor
      let X := st.sys.writer.X
      let upTo := a.self.window
      let R := st.sys.writer.R
      let sig := R.sign (a.key l.actor) (Command.envelopeMessage X a.self 0 upTo)
      let some p := Envelope.bytes X (Command.envelopeOf a.self 0 upTo
          ⟨R.pub (a.key l.actor), R.pub (a.next l.actor), sig⟩)
        | return (.refused "badState", "")
      match ← secondWriter sameNonce with
      | .error e => return (.refused e, "")
      | .ok h =>
          let r ← h.ask ⟨0, Op.log.code, p⟩
          let _ ← h.stop
          match r with
          | some r => pure (statusOutcome (ByteArray.mk #[r.status] ++ r.payload), "")
          | none => pure (.refused "writerStopped", "")
  | .forge argv => do
      match ← subst argv with
      | .error e => pure (.refused e, "")
      | .ok av => forged l.actor av
  | .carry rightDigest => do
      let st ← get
      match ← st.host.stop with
      | .error e => pure (.refused s!"writerFailed {e}", "")
      | .ok (.eof, r0) =>
        let X := st.sys.writer.X
        let R := st.sys.writer.R
        match Host.Carry.exportFile X.env R.dc r0.world with
        | .error f => do
            set { st with host := ← Writer.start st.sys.writer st.mem r0 }
            pure (.refused f.name, "")
        | .ok f =>
          let d := Host.Carry.digestOf f
          let want := if rightDigest || st.sys.importTrustsFile then d
            else match Codec.Digest.ofBytes? (flipLast d.bytes) with
              | some d' => d'
              | none => d
          match Host.Carry.importWorld X R.dc Rows.Params.worldName (flipLast Rows.Params.nonce) (.digest want) f with
          | .error (s, _) => do
              -- refused before anything is written: the old writer serves on
              set { st with host := ← Writer.start st.sys.writer st.mem r0 }
              pure (.refused s.name, "")
          | .ok (w', _) =>
            -- the carried World answers at the exported height, with the exported journal
            if w'.height ≠ r0.world.height ∨ w'.journal.toList ≠ r0.world.journal.toList then
              return (.refused "carryMoved", "")
            match ← Writer.genesisStore st.sys.writer w' with
            | .error e => pure (.refused e, "")
            | .ok (mem, r) =>
                let h ← Writer.start st.sys.writer mem r
                set { st with host := h, mem, genesis := w', carriedFile := some f }
                pure (.ok, "")
      | .ok (exit, _) => pure (.refused s!"writer{exit.name}", "")
  | .window n => do
      let a ← actor l.actor
      setActor l.actor { a with self := { a.self with window := n } }
      pure (.ok, "")
  | .acceptCarry wrongOrigin => do
      let a ← actor l.actor
      match acceptCarried (← get) wrongOrigin with
      | .error e => pure (.refused e, "")
      | .ok g =>
        setActor l.actor { a with self := { a.self with world := g.origin }, follow := { world := g } }
        pure (.ok, "")
  | .rejoinBehind => do
      let a ← actor l.actor
      let st ← get
      setActor l.actor { a with self := { a.self with world := st.genesis.origin }, follow := { world := st.first } }
      pure (.ok, "")
  | .replayLog sameNonce => do
      -- a SECOND writer from a genesis of the same name, allowance and founders, and the writer's
      -- committed calls submitted to it byte-identical, in order (OPS's cross-World replay)
      let st ← get
      if st.committed.isEmpty then return (.refused "noCommitted", "")
      match ← secondWriter sameNonce with
      | .error e => return (.refused e, "")
      | .ok h =>
          let mut outs : Array Expect := #[]
          for (call, i) in st.committed.toList.zipIdx do
            let r ← h.ask ⟨UInt32.ofNat i, Op.submit.code, call⟩
            outs := outs.push (match r with
              | some r => statusOutcome (ByteArray.mk #[r.status] ++ r.payload)
              | none => .refused "writerStopped")
          let _ ← h.stop
          let first := (outs[0]?).getD (.refused "noCommitted")
          match outs.toList.zipIdx.find? (fun (o, _) => decide (o ≠ first)) with
          | some (o, i) => pure (.refused s!"mixed:{i}:{o.text}", "")
          | none => pure (first, "")
  | .accept inv key => do
      match ← subst [s!"@{inv}", s!"@{key}"] with
      | .ok [ih, kh] =>
        match Text.ofHex ih, Text.ofHex kh with
        | some ib, some kb =>
          let st ← get
          let ib := match l.fault with
            | .forgeInvite resign => forgeInvite st.sys.writer.R st.sys.follow resign ib
            | _ => ib
          match acceptAs st.sys kb ib with
          | .error r => pure (.refused r.name, "")
          | .ok (_, w) =>
            let a ← actor l.actor
            setActor l.actor { a with self := { a.self with world := w.origin }, follow := { world := w } }
            pure (.ok, "")
        | _, _ => pure (.refused "badToken", "")
      | .ok _ => pure (.refused "badToken", "")
      | .error e => pure (.refused e, "")
  | .receiptOf owner => do
      let st ← get
      match (← actor owner).last >>= st.sys.follow.decodeCall with
      | none => pure (.refused "noAttempt", "")
      | some _ => command l.actor ["receipt", Text.toHex ((← actor owner).last.getD ByteArray.empty)] .none 4
  | .cancelOf owner => do
      let st ← get
      match (← actor owner).last >>= st.sys.follow.decodeCall with
      | none => pure (.refused "noAttempt", "")
      | some _ => command l.actor ["cancel", Text.toHex ((← actor owner).last.getD ByteArray.empty)] l.fault 4
  | .verify owner rc => do
      let st ← get
      let X := st.sys.follow
      let some c := (← actor owner).last >>= X.decodeCall | return (.refused "noAttempt", "")
      let some rb := st.binds.lookup rc >>= Text.ofHex | return (.refused s!"unbound {rc}", "")
      let some r := Receipt.ofBytes X.env st.sys.writer.R.dc rb | return (.refused "badReceipt", "")
      let r := match l.fault with
        | .forgeReceipt => { r with answer := .absent }
        | _ => r
      -- the phone's head: its own World's height and roots, nothing the receipt states
      let w := (← actor l.actor).follow.world
      let ans := if st.sys.trustReceipt then
          (if rootsDigest X.env r.root r.jroot r.rroot r.rowsroot = w.roots X.env then .ok r.answer else .error .headMismatch)
        else Receipt.check X.env w.height (w.roots X.env) (txIdOf X c) c.unsigned.notBefore r
      match ans with
      | .ok a => pure (.ok, Receipt.Answer.text X.env.bytes a)
      | .error e => pure (.refused e.name, "")
  | .used atLeast => do
      -- the member's own World, caught up; the calls the writer committed, as its clients sent them
      let (o, _) ← command l.actor ["sync"] .none 4
      if o ≠ .ok then return (.refused s!"sync:{o.text}", "")
      let st ← get
      let a ← actor l.actor
      let calls := st.committed.toList.filterMap st.sys.follow.decodeCall
      let n := (Use.shared st.sys.follow a.follow.world calls).length
      note s!"USE {l.actor} shared-objects {n} of {calls.length} committed calls"
      if atLeast ≤ n then pure (.ok, "") else pure (.refused s!"unshared:{n}", "")
  | .retry => pure (← retry l.actor, "")
  | .rerun => do
      match (← actor l.actor).last with
      | none => pure (.refused "noAttempt", "")
      | some call =>
          -- the next run of the open attempt: "sent, outcome lost"
          match ← drive l.actor call .none 4 attemptFuel 0 (some (.submit, .lost)) none none "" with
          | .error e => pure (.refused e, "")
          | .ok res =>
              -- step 4 is follow's: it settles the frozen call on the actor's own World (R7)
              let self ← selfOf l.actor .none
              match Command.settled (← X) self (← actor l.actor).follow.world ByteArray.empty call res with
              | .done exit out err => pure (outcomeOf exit err, (String.fromUTF8? out).getD "")
              | _ => pure (.refused "badFrame", "")
  | .resubmit => do
      match (← actor l.actor).last with
      | none => pure (.refused "noAttempt", "")
      | some call =>
          match ← ask .submit call with
          | none => pure (.refused "writerStopped", "")
          | some res =>
              if classify res = .committed then
                modify fun st => { st with committed := st.committed.push call }
              pure (statusOutcome res, "")
  | .reopenFlipped off => pure (← reopenFlipped off, "")

/-- Run a line `times` times; the first outcome that is not the declared one, else the declared
one. A run past `withinMs` (a liveness deadline) is `hang`. -/
def runLine (i : Nat) (l : Line) (times : Nat) : M D Expect := do
  let mut got := l.expect
  let mut ns : List Nat := []
  for j in List.range times do
    let t0 ← nowNs
    let (o, out) ← runAct l
    let dt := (← nowNs) - t0
    ns := ns ++ [dt]
    if j = 0 && o = .ok then
      if let some b := l.bind then
        if let some h := boundToken out then bind b h
        -- a description (`read OBJ ?`): each `method I LABEL …` line binds `b.LABEL` to I
        for ln in out.splitOn "\n" do
          match ln.splitOn " " with
          | "method" :: i :: lbl :: _ =>
              bind s!"{b}.{lbl}" (if (← get).sys.guessMethod then "0" else i)
          | _ => pure ()
    -- a line that checks what it prints shows it in the transcript
    if j = 0 && l.prints.isSome then
      for ln in out.splitOn "\n" do
        if ln ≠ "" then note s!"  | {ln}"
    let o := match l.prints with
      | some t => if o = l.expect && (if l.exact then out ≠ t else (out.splitOn t).length ≤ 1)
          then .refused "unprinted" else o
      | none => o
    let bound := if (← get).sys.zeroDeadline then l.withinMs.map fun _ => 0 else l.withinMs
    let o := match bound with
      | some ms => if o = l.expect ∧ dt > ms * 1000000 then .hang else o
      | none => o
    if o ≠ l.expect && got = l.expect then got := o
  let what := match l.act with
    | .cmd argv => String.intercalate " " (argv.map fun (a : String) => if a.length > 24 then (a.take 24).toString ++ "…" else a)
    | a => (repr a).pretty 120
  note s!"line {i} {l.actor}: {what} => {Expect.text got}"
  modify fun st => { st with times := st.times.push ⟨i, ns⟩ }
  pure got

/-- What a member row's run produced. -/
structure Result where
  observed : Observed
  log : Array String
  times : Array Timed
  reopenNs : List Nat
  reopenReads : List (Nat × Nat × Bool)
  invokes : Array (Except String Invoked)
  /-- the run's cost in deterministic units: frames sent on either socket, and the steps of the
  writer's World when it stopped -/
  frames : Nat
  steps : Nat

/-- Run a member row against a fresh deployment under the parameters `R` and the plant `m`;
`times` scales every repeated line. -/
def run (R : Rows.Params D) (m : Option Mutation) (lines : List Line) (times : Option Nat) : IO Result := do
  let s := sys R m
  let fs := founders.map fun n => (keyOf R n 0, nextKeyDigest s.writer.X (keyOf R n 1))
  let g ← match Receive.genesis s.writer.X Rows.Params.worldName Rows.Params.nonce Rows.Params.allowance fs with
    | .ok g => pure g
    | .error r => throw (IO.userError s!"genesis refused {r.name}")
  let (mem, r₀) ← match ← Writer.genesisStore s.writer g with
    | .ok m => pure m
    | .error e => throw (IO.userError s!"genesis: {e}")
  let host ← Writer.start s.writer mem r₀
  let go : M D (List Expect) := lines.zipIdx.mapM fun (l, i) =>
    runLine i l (if l.times > 1 then times.getD l.times else l.times)
  let hex (d : D) := Text.toHex (s.writer.X.env.bytes d)
  -- the World's origin inputs, as the founders hold them (`host genesis` prints them), and another
  -- World's (the nonce changed)
  let inputs := Invite.inputBytes s.writer.X Rows.Params.worldName Rows.Params.nonce Rows.Params.allowance fs
  let other := Invite.inputBytes s.writer.X Rows.Params.worldName (flipLast Rows.Params.nonce)
    Rows.Params.allowance fs
  -- the founding invitation: the sponsor's, pinning the genesis World
  let invitation ← match Invite.unsignedBytes s.writer.X inputs
      ⟨g.steps, (base R).digest (R.world.bytes g)⟩ (founderId s.writer.X g.origin 0) (keyOf R "sponsor" 0) with
    | some u => match Invite.bytes u (R.sign (secretOf "sponsor" 0) (Invite.message u)) with
      | some b => pure b
      | none => throw (IO.userError "the founding invitation does not fit")
    | none => throw (IO.userError "the founding invitation does not fit")
  let binds := founders.zipIdx.flatMap (fun (n, i) =>
    [(n, hex (founderId s.writer.X g.origin i)),
     (n ++ ".grant", hex (founderGrantId s.writer.X g.origin i))]) ++
    [("inputs", Text.toHex inputs), ("otherInputs", Text.toHex other)] ++
    (founders ++ ["newcomer"]).map fun n => (n ++ ".key", Text.toHex (keyOf R n 0))
  let (outcomes, st) ← go.run { sys := s, host, mem, genesis := g, lineage := g.origin, first := g, binds, invitation }
  let steps := match ← st.host.stop with
    | .ok (_, r) => r.world.steps
    | .error _ => 0
  pure ⟨{ outcomes, ops := st.ops, kinds := st.kinds }, st.log, st.times, st.reopenNs, st.reopenReads, st.invokes,
    st.conn, steps⟩

end Nanodregg.Protocol.Rows.Loopback
