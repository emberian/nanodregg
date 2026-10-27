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
import Protocol.Health

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
  /-- the attempt store ends an attempt on the Host's final refusal, never asking follow (a plant) -/
  trustLookup : Bool := false
  /-- `cancel CALL` ends `cancelled` on the writer's `refused cancelled`, never settling it on
  follow's World (a plant: follow's phase 10 before PROTOCOL-71) -/
  trustCancel : Bool := false
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
  /-- a relay hides the log from an invoke with `--range`: follow plans, by its own machine, at the
  listing it held before (a plant, item 4) -/
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
  /-- the client drops `sync --to`'s anchor: a catch-up that compares with nobody (a plant,
  PROTOCOL-74) -/
  ignoreAnchor : Bool := false
  /-- nd's re-run of an argv whose attempt is open plans afresh (a plant, A6: before CLIENT-37) -/
  rerunFresh : Bool := false

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
  | some .forgeCertificate => { writer := { R, X := R.ctx, forgeCertificate := true }, follow := R.ctx }
  | some .forkCertificate => { writer := { R, X := R.ctx, forkCertificate := true }, follow := R.ctx }
  | some .stripCertificate => { writer := { R, X := R.ctx, stripCertificate := true }, follow := R.ctx }
  | some .unstatedExpiry => { writer := { R, X := R.ctx, unstatedExpiry := true }, follow := R.ctx }
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
  | some .guessedBudget => { writer := { R, X := R.ctx, pageBudget := 16384 }, follow := R.ctx }
  | some .dropHint => { writer := { R, X := R.ctx }, follow := R.ctx, dropHint := true }
  | some .staleBase => { writer := { R, X := R.ctx }, follow := R.ctx, staleBase := true }
  | some .twiceEach => { writer := { R, X := R.ctx }, follow := R.ctx, twiceEach := true }
  | some .staleRange => { writer := { R, X := R.ctx }, follow := R.ctx, staleRange := true }
  | some .dropRange => { writer := { R, X := R.ctx }, follow := R.ctx, dropRange := true }
  | some .actOnBeforeLog => { writer := { R, X := R.ctx }, follow := R.ctx, actOnBeforeLog := true }
  | some .dropDoc => { writer := { R, X := R.ctx }, follow := R.ctx, dropDoc := true }
  | some .cancelUndomained => { writer := { R, X := R.ctx }, follow := R.ctx, cancelUndomained := true }
  | some .trustCancel => { writer := { R, X := R.ctx }, follow := R.ctx, trustCancel := true }
  | some .ignoreAnchor => { writer := { R, X := R.ctx }, follow := R.ctx, ignoreAnchor := true }
  | some .perFieldBudget =>
      { writer := { R, X := R.ctx, pageBudget := Bounds.frameBytesMax - 1024 }, follow := R.ctx }
  | some .forgesRefusal => { writer := { R, X := R.ctx, forgeRefusal := true }, follow := R.ctx }
  | some .rerunFresh => { writer := { R, X := R.ctx }, follow := R.ctx, rerunFresh := true }

/-! ## Actors -/

def founders : List String := ["sponsor", "operator"]

/-- Custody's secret of generation `gen`. Its public key is the run's `Params.pub` of it (under the
toy parameters the secret itself; at the deployed ones the Ed25519 public key of its seed). -/
def secretOf (name : String) (gen : Nat) : ByteArray := s!"key:{name}:{gen}".toUTF8

/-- The public key of custody's secret of generation `gen`. -/
def keyOf (R : Rows.Params D) (name : String) (gen : Nat) : ByteArray := R.pub (secretOf name gen)

/-- One frozen attempt as nd's attempt store holds it (`client/src/attempt.rs`): the argv it was
signed for, the call, follow's continuation at the submit step, the sends started, and whether the
member's own follow settled it. -/
structure Frozen where
  argv : List String
  call : ByteArray
  k : ByteArray
  sends : Nat := 0
  settled : Bool := false

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
  /-- the attempt store: every call this actor's nd froze, oldest first; the next run of an argv
  whose attempt is open continues it (CLIENT-37) -/
  attempts : List Frozen := []

/-- Custody's secrets: the current key's, the next one's and the pending one's. -/
def Actor.key (n : String) (a : Actor D) : ByteArray := secretOf n a.gen
def Actor.next (n : String) (a : Actor D) : ByteArray := secretOf n (a.gen + 1)
def Actor.pending (n : String) (a : Actor D) : ByteArray := secretOf n (a.gen + 2)

/-! ## A generated relay (DESIGN-QA Q6, `Protocol.Rows.Adversary`)

The adversary's moves on the writer's socket and on follow's continuations. The harness holds no
generator: `Protocol.Rows.Adversary` draws a TAPE of moves from a seed, and the harness plays one
move per exchange (`ask`) and one continuation choice per resume (`resume`). An empty tape is the
honest relay, the rows' own. -/

/-- An edit of a `log` page's events. -/
inductive EventEdit
  /-- the event at `i` (mod the page's length) has its last byte flipped -/
  | flip (i : Nat)
  /-- the page's last event is withheld -/
  | dropLast
  /-- the page's first event is withheld -/
  | dropFirst
  /-- the event at `i` is served twice -/
  | dup (i : Nat)
  /-- the page's first two events are served in each other's place -/
  | swap
  /-- every cancel event carries a flipped signature byte (a cancel the member never signed) -/
  | forgeCancel
  deriving Repr

/-- One move of the relay on one exchange with the writer. -/
inductive Move
  | pass
  /-- the request reaches the writer; its reply never reaches nd (the connection is closed) -/
  | drop
  /-- the request never reaches the writer; the connection is closed -/
  | withhold
  /-- the request reaches the writer twice; nd reads the second reply -/
  | duplicate
  /-- the reply's payload byte `i` (mod its size) is flipped -/
  | flip (i : Nat)
  /-- the reply's status byte is replaced -/
  | status (s : Status)
  /-- the request never reaches the writer; nd reads `s ‖ name` (a Host's word with nothing behind it) -/
  | answer (s : Status) (name : String)
  /-- the request reaches the writer; nd reads the PREVIOUS reply to this op (a stale or late reply) -/
  | replay
  /-- a `log` page's events edited -/
  | events (e : EventEdit)
  /-- a `log` page states its tip `extra` beyond the writer's (`0`: the page's own end, hiding the rest) -/
  | tip (extra : Nat)
  /-- a `log` page states its tip as the newest base -/
  | base
  /-- an `expired` refusal states a height `extra` past the writer's -/
  | expired (extra : Nat)
  /-- a `log` or `read` page is answered `pageIo` (the writer's IO failed; it serves on) -/
  | pageIo
  deriving Repr

def EventEdit.name : EventEdit → String
  | .flip i => s!"flip{i}" | .dropLast => "dropLast" | .dropFirst => "dropFirst" | .dup i => s!"dup{i}"
  | .swap => "swap" | .forgeCancel => "forgeCancel"

def Move.name : Move → String
  | .pass => "pass" | .drop => "drop" | .withhold => "withhold" | .duplicate => "duplicate"
  | .flip i => s!"flip{i}" | .status s => s!"status{s.code}" | .answer s n => s!"answer{s.code}:{n}"
  | .replay => "replay" | .events e => s!"events:{e.name}" | .tip n => s!"tip{n}" | .base => "base"
  | .expired n => s!"expired{n}" | .pageIo => "pageIo"

/-- The relay's tapes and what it did. -/
structure Relay where
  /-- one move per exchange with the writer, in order; past its end the relay is honest -/
  host : List Move := []
  /-- one choice per resume: `some i` hands follow, in place of its own continuation, the `i`th (mod
  their number) continuation follow handed this actor earlier; past its end, none -/
  resume : List (Option Nat) := []
  /-- the last reply the writer sent to each op (for `replay`) -/
  last : List (UInt8 × ByteArray) := []
  /-- the continuations follow handed each actor, oldest first -/
  ks : List (String × Array ByteArray) := []
  /-- every move made, in order (`op:move`; `k:I` for a swapped continuation) -/
  made : Array String := #[]

/-- One top-level `nd` run as the judge reads it (`Protocol.Rows.Adversary`), recorded when
`judging`: the actor, the argv, how it ended, the calls it froze or continued, every call-domain
message custody signed in it with the argv of the continuation that asked, and the actor's own
follow World and `Self` after it. -/
structure Seen (D : Type) [Ord D] where
  run : Nat
  actor : String
  argv : List String
  calls : List ByteArray
  signs : List (ByteArray × List ByteArray)
  world : World D
  self : Self D
  /-- the harness's outcome of the run -/
  outcome : Expect
  /-- the relay's moves while the run lasted (`Relay.made`'s entries) -/
  moves : List String

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
  /-- the generated relay (Q6); the default is the honest one -/
  relay : Relay := {}
  /-- record each nd run for the judge (`seen`, Q6) -/
  judging : Bool := false
  seen : Array (Seen D) := #[]
  /-- record the trace (Q5): every exchange nd makes on its two sockets, by run -/
  tracing : Bool := false
  /-- the trace's lines (`traceLine`), when `tracing` -/
  trace : Array String := #[]
  /-- the nd runs started so far: the next run's number -/
  runs : Nat := 0
  /-- the nd run each actor is in, and the depth its command's own steps run at -/
  runOf : List (String × Nat × Nat) := []
  /-- each run's last `done` at its own depth: its exit, stdout and stderr -/
  ended : List (Nat × UInt8 × ByteArray × ByteArray) := []
  /-- the calls each run froze or continued, and the call-domain messages signed in it (when judging) -/
  runCalls : List (Nat × ByteArray) := []
  runSigns : List (Nat × ByteArray × List ByteArray) := []

abbrev M (D : Type) [Ord D] := StateT (St D) IO

def X : M D (Ctx D) := do pure (← get).sys.follow

/-- The run's parameters. -/
def params : M D (Rows.Params D) := do pure (← get).sys.writer.R

def note (s : String) : M D Unit := modify fun st => { st with log := st.log.push s }

def sawOp (op : Op) : M D Unit :=
  modify fun st => if st.ops.contains op then st else { st with ops := st.ops ++ [op] }

/-- What an invoke's run costs, measured on the World the call was planned on (the actor's
follow, caught up to the writer's tip): the receiver's own inputs (`invokeRun` over the call's
pins), then LANG's `runMeasured`, whose first component IS the deployed `Program.run`. A call
whose run refuses costs nothing here (it is not admitted: `none`). For an admitted one, the
required steps (`Lang.Need.requiredOf`, the size of the run's reference derivation and of the
suspensions extraction forces, `Lang.Proofs.Need.required_counts_the_run`), and the ticks under
the plant: the method run on `Lang.Need.wasteStep` in place of the deployed step, which costs
two needless transitions per application. A count that fails is an error by name. -/
def measureInvoke (rc : Lang.ReceiptCheck) (X : Ctx D) (w : World D) (c : Call D) : Option (Except String Invoked) :=
  match c.unsigned.body with
  | .invoke obj method args budget via =>
    let look := pinned X.env w c.unsigned.pins
    let rv := rowView X.env w c.unsigned
    match invokeRun X look c c.unsigned.member none obj method via with
    | .ok (cell, p, r) =>
      match Lang.runMeasured X.env.bytes X.digestOf rc look rv p (stateOf cell) method args r budget with
      | .ok (_, _, _, ticks, pkgs) =>
        let text : Receive.Refusal D → String := fun | .program s => s | e => e.name
        let count := do
          let required ← Lang.Need.requiredOf X.env.bytes X.digestOf rc look rv p (stateOf cell) method
            args r budget
          let honest ← Lang.Need.runTicksBy X.env.bytes X.digestOf rc Lang.step look rv p (stateOf cell)
            method args r budget
          let wasted ← Lang.Need.runTicksBy X.env.bytes X.digestOf rc Lang.Need.wasteStep look rv p
            (stateOf cell) method args r budget
          let (once, twice) ← Lang.Need.extractTicksTwice X.env.bytes X.digestOf rc look rv p (stateOf cell)
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
    | some c => c.unsigned.body.kindName
    | none => "undecodable"
  modify fun st => if st.kinds.contains k then st else { st with kinds := st.kinds ++ [k] }
  if let (some c, some a) := (decoded, (← get).actors.lookup name) then
    if let some m := measureInvoke (← get).sys.writer.R.receipts (← get).sys.writer.X a.follow.world c then
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

/-- A sponsor-signed invitation to the imported World (its carry start under the authority the
carried World bears, PROTOCOL-85), using the retained export as IN. `wrongOrigin`: the start names a
trie root that is not the file's, so it names another World. -/
def acceptCarried (st : St D) (wrongOrigin : Bool := false) : Except String (World D) := do
  let some file := st.carriedFile | throw "noCarry"
  let X := st.sys.follow
  let R := st.sys.writer.R
  let r ← (Host.Carry.read X.env R.dc file).mapError (·.name)
  let auth := (authorityOf st.genesis).getD Authority.none
  let s := carryStartOf X Rows.Params.worldName (flipLast Rows.Params.nonce) r.head.fromOrigin r.carried auth
  let start := Invite.Start.carried (if wrongOrigin then { s with trieRoot := r.head.fromOrigin } else s) r.head.chain
  let some u := Invite.unsignedBytes X (Invite.startBytes X start)
      ⟨st.genesis.steps, R.keys.worldDigest (R.world.bytes st.genesis)⟩
      (founderId X st.lineage 0) (keyOf R "sponsor" 0) | throw "invitationTooLarge"
  let some b := Invite.bytes u (R.sign (secretOf "sponsor" 0) (Invite.message u)) | throw "invitationTooLarge"
  let (i, _) ← (Invite.acceptStart X (keyOf R "sponsor" 0) b).mapError (·.name)
  let .carried s _ := i.start | throw "notCarried"
  let pin := if st.sys.importTrustsFile then Host.Carry.Pin.digest (Host.Carry.digestOf file)
    else .origin (carryOriginOfStart X s)
  let (w, _) ← (Host.Carry.importWorld X R.dc s.name s.nonce pin (some s.auth) file).mapError (·.2)
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
    | ["health", h] => some h
    | ["attest", h] => some h
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
def send (op : Op) (payload : ByteArray) : M D (Option ByteArray) := do
  sawOp op
  let st ← get
  set { st with conn := st.conn + 1 }
  match ← st.host.ask ⟨UInt32.ofNat st.conn, op.code, payload⟩ with
  | some r =>
      let b := ByteArray.mk #[r.status] ++ r.payload
      if st.judging then
        modify fun st => { st with relay := { st.relay with
          last := (op.code, b) :: st.relay.last.filter (·.1 ≠ op.code) } }
      pure (some b)
  | none => pure none

/-! ## The trace (Q5)

A run that records (`tracing`) writes, for every `nd` invocation, the argv nd is handed, every
exchange nd makes on follow's socket and on the Host's (the request it sends, the reply it reads, or
`lost` when it reads none), and the command's end. That is nd's whole conversation: a Rust test
replays it against nd's own step loop and custody (`client/tests/trace.rs`), so what nd must send is
what this driver sent, never a test author's copy of it. -/

/-- A field of a trace line: the bytes in hex, `-` for none. -/
def hexOf (b : ByteArray) : String := if b.isEmpty then "-" else Text.toHex b

def traceLine (s : String) : M D Unit :=
  modify fun st => if st.tracing then { st with trace := st.trace.push s } else st

/-- A trace line for actor `name`'s run, when it is in one. -/
def traced (name : String) (line : Nat → String) : M D Unit := do
  if let some (n, _) := (← get).runOf.lookup name then traceLine (line n)

def firstByte (b : ByteArray) : UInt8 := if h : 0 < b.size then b[0] else 0

/-- An exchange on the Host's socket as nd saw it: the reply `status ‖ payload`, or `lost`. -/
def tracedHost (name : String) (op : Op) (req : ByteArray) (res : Option ByteArray) : M D Unit :=
  traced name fun n => match res with
    | some r => s!"host {n} {op.code} {hexOf req} {firstByte r} {hexOf (r.extract 1 r.size)}"
    | none => s!"host {n} {op.code} {hexOf req} lost"

/-- A `done` step at depth `depth` ends actor `name`'s run when the run's command steps there. -/
def sawDone (name : String) (depth : Nat) (exit : UInt8) (out err : ByteArray) : M D Unit := do
  if let some (n, top) := (← get).runOf.lookup name then
    if top = depth then
      modify fun st => { st with ended := (n, exit, out, err) :: st.ended.filter (·.1 ≠ n) }

/-- Run `act` as one `nd ARGV` of actor `name`, whose command's steps run at depth `top`: the trace's
`run` line, then what `act` exchanges, then the `end` line (`end N EXIT STDOUT STDERR`, or `end N
error` when the run stopped without follow's `done`, as nd stops on a transport or loop error). When
judging, the run is also recorded for the judge (`Seen`): its outcome, the calls it froze or
continued, the call-domain messages custody signed in it, the relay's moves while it lasted, and the
actor's follow World and `Self` after it. -/
def withRun (name : String) (argv : List String) (top : Nat) (act : M D (Expect × String)) :
    M D (Expect × String) := do
  let st ← get
  let n := st.runs
  let m0 := st.relay.made.size
  let prev := st.runOf.lookup name
  set { st with runs := n + 1, runOf := (name, n, top) :: st.runOf.filter (·.1 ≠ name) }
  traceLine s!"run {n} {name}{String.join (argv.map fun a => " " ++ hexOf a.toUTF8)}"
  let r ← act
  let st ← get
  traceLine (match st.ended.lookup n with
    | some (e, o, er) => s!"end {n} {e} {hexOf o} {hexOf er}"
    | none => s!"end {n} error")
  if st.judging then
    if let some a := st.actors.lookup name then
      let calls := (st.runCalls.filter (·.1 = n)).reverse.map (·.2)
      let signs := (st.runSigns.filter (·.1 = n)).reverse.map (·.2)
      let seen : Seen D := ⟨n, name, argv, calls, signs, a.follow.world, a.self, r.1,
        (st.relay.made.extract m0 st.relay.made.size).toList⟩
      modify fun st => { st with seen := st.seen.push seen }
  modify fun st => { st with
    ended := st.ended.filter (·.1 ≠ n)
    runCalls := st.runCalls.filter (·.1 ≠ n)
    runSigns := st.runSigns.filter (·.1 ≠ n)
    runOf := match prev with
      | some p => (name, p) :: st.runOf.filter (·.1 ≠ name)
      | none => st.runOf.filter (·.1 ≠ name) }
  pure r

/-- Update actor `name`'s frozen attempt of `call`. -/
def touchFrozen (name : String) (call : ByteArray) (f : Frozen → Frozen) : M D Unit := do
  let a ← actor name
  setActor name { a with attempts := a.attempts.map fun x => if x.call == call then f x else x }

/-- How the rows' followers read a base: the run's World codec and the writer's own `worldDigest`. -/
def base (R : Rows.Params D) : Thin.Base (World D) :=
  ⟨R.world, World.steps, R.keys.worldDigest, Host.Cadence.deployed.worldBytesMax⟩

/-- Send one frame to the actor's `host follow` (`Host.Follow.answer`, the deployed per-frame
decision, on the actor's follow state); the step's bytes, or the name follow refused it by. What
follow would persist is not modelled here: the actor's state is in memory. -/
def followAsk (name : String) (self : Self D) (op : Op) (payload : ByteArray) :
    M D (Except String ByteArray) := do
  sawOp op
  -- the client's transport: a body past the frame, as a whole, is never written (`write_body`'s
  -- `pastBound frameBytesMax`, PROTOCOL-70); before it the in-process rows passed frames the
  -- deployed transport refuses
  if !bodyFits payload then return .error "pastBound"
  let a ← actor name
  let st ← get
  set { st with conn := st.conn + 1 }
  let (fs', _, status, p) :=
    Host.Follow.answer (← X) (← params).dc (base (← params)) self a.follow ⟨UInt32.ofNat st.conn, op.code, payload⟩
  setActor name { a with follow := fs' }
  traced name fun n => s!"follow {n} {op.code} {hexOf payload} {status} {hexOf p}"
  -- and a reply past it is never read (`read_body`)
  if !bodyFits p then return .error "pastBound"
  pure (if status = Status.ok.code then .ok p else .error (Command.hostName p))

/-! ## Transport faults on a log page -/


def editPage (f : List ByteArray → List ByteArray) (reply : ByteArray) : ByteArray :=
  match Command.hostReply reply with
  | some (.ok, p) =>
      match logReplyFrame.decode p with
      | .ok (l, n, c, t, th, bs, bd, k, ()) =>
          match Text.fitList Bounds.frameBytesMax (f (Text.unlist l)) with
          | some l' => ByteArray.mk #[Status.ok.code] ++ logReplyFrame.bytes (l', n, c, t, th, bs, bd, k, ())
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
  | _ => id

/-- An `expired` refusal stating a height `extra` past the writer's (a man in the middle on the
member's path, PROTOCOL-27: the inflation buys a window in the future, never a longer one,
`Envelope.check_ok_within`); any other reply as it is. -/
def inflateExpiry (extra : Nat) (reply : ByteArray) : ByteArray :=
  match Command.hostReply reply with
  | some (.refused, p) => match expiredHeight? p with
    | some h => ByteArray.mk #[Status.refused.code] ++ (ReadRefusal.expired (h + extra)).payload
    | none => reply
  | _ => reply

/-- A relay that hides the writer's log: a `log` page answered as an EMPTY page at follow's own
position `w`, stated as the writer's tip (the plant `staleRange`: follow is never caught up, and its
own machine, admission included, plans on the World it holds). -/
def hideLog (X : Ctx D) (w : World D) (reply : ByteArray) : ByteArray :=
  match Command.hostReply reply with
  | some (.ok, p) =>
      match logReplyFrame.decode p with
      | .ok (_, _, _, _, _, bs, bd, k, ()) =>
          let f := Text.fit Bounds.frameBytesMax
          let base := match Text.ofU64 bs.1 with
            | some b => if b ≤ w.steps then bs.1 else Text.u64 0
            | none => Text.u64 0
          match Text.fitList Bounds.frameBytesMax [], f (Text.u64 w.steps), f (X.env.bytes w.chain),
              f (Text.u64 w.steps), f (Text.u64 w.height), f base with
          | some l, some n, some c, some t, some th, some b =>
              ByteArray.mk #[Status.ok.code] ++ logReplyFrame.bytes (l, n, c, t, th, b, bd, k, ())
          | _, _, _, _, _, _ => reply
      | .error _ => reply
  | _ => reply

def coldFault : Fault → Bool
  | .flipEvent _ | .dropLastEvent | .cold | .forgeCancel => true
  | _ => false

/-- `lieCancel`: the relay keeps a `cancel` from the writer and answers it `refused cancelled` itself
(PROTOCOL-71); `none` for any other fault or op (the frame goes to the writer). -/
def cancelLie (fault : Fault) (op : Op) : Option ByteArray :=
  match fault, op with
  | .lieCancel, .cancel => some (ByteArray.mk #[Status.refused.code] ++
      (Receive.Refusal.cancelled : Receive.Refusal D).name.toUTF8)
  | _, _ => none

/-- Whether the relay forwards a submit to the writer (`neverForward`: it never does). -/
def forwards : Fault → Bool
  | .neverForward => false
  | _ => true

/-- The faults under which the writer commits an attempt's FIRST submit and its reply is lost. -/
def losesFirstReply : Fault → Bool
  | .dropReply | .lieLookup => true
  | _ => false

/-- `lieLookup`: the Host's lookup `ok` for a committed call rewritten as `refused stale`
(PROTOCOL-46: the Host hints, follow settles); any other reply as it is. -/
def lookupLie (fault : Fault) (reply : ByteArray) : ByteArray :=
  match fault, Command.hostReply reply with
  | .lieLookup, some (.ok, _) => ByteArray.mk #[Status.refused.code] ++ "stale".toUTF8
  | _, _ => reply

/-! ## The relay's moves (Q6) -/

def eventEdit : EventEdit → List ByteArray → List ByteArray
  | .flip i, evs => evs.mapIdx fun j e => if j = i % evs.length then flipLast e else e
  | .dropLast, evs => evs.dropLast
  | .dropFirst, evs => evs.drop 1
  | .dup i, evs => (evs.mapIdx fun j e => if j = i % evs.length then [e, e] else [e]).flatten
  | .swap, a :: b :: rest => b :: a :: rest
  | .swap, evs => evs
  | .forgeCancel, evs => evs.map forgeCancelSig

/-- A `log` page whose stated tip or base is moved: `tip 0` states the page's own end as the tip
(the writer's height kept), `tip n` the writer's tip plus `n` in both units, `base` the tip as the
newest base. Any other reply as it is. -/
def tipEdit (m : Move) (reply : ByteArray) : ByteArray :=
  match Command.hostReply reply with
  | some (.ok, p) =>
      match logReplyFrame.decode p with
      | .ok (l, n, c, t, th, bs, bd, k, ()) =>
          let f := Text.fit Bounds.frameBytesMax
          match Text.ofU64 n.1, Text.ofU64 t.1, Text.ofU64 th.1, m with
          | some ns, some _, some hs, .tip 0 =>
              match f (Text.u64 ns), f (Text.u64 hs) with
              | some t', some h' => ByteArray.mk #[Status.ok.code] ++ logReplyFrame.bytes (l, n, c, t', h', bs, bd, k, ())
              | _, _ => reply
          | some _, some ts, some hs, .tip x =>
              match f (Text.u64 (ts + x)), f (Text.u64 (hs + x)) with
              | some t', some h' => ByteArray.mk #[Status.ok.code] ++ logReplyFrame.bytes (l, n, c, t', h', bs, bd, k, ())
              | _, _ => reply
          | _, _, _, .base => ByteArray.mk #[Status.ok.code] ++ logReplyFrame.bytes (l, n, c, t, th, t, bd, k, ())
          | _, _, _, _ => reply
      | .error _ => reply
  | _ => reply

/-- A page reply under a move: its events, its stated tip or base, or an `expired` height. -/
def pageEdit : Move → ByteArray → ByteArray
  | .events e => editPage (eventEdit e)
  | .tip n => tipEdit (.tip n)
  | .base => tipEdit .base
  | .expired n => inflateExpiry n
  | _ => id

/-- One exchange with the writer, through the relay: the tape's next move, or, past the tape's end,
the honest relay (`send`). -/
def ask (op : Op) (payload : ByteArray) : M D (Option ByteArray) := do
  let st ← get
  match st.relay.host with
  | [] => send op payload
  | m :: rest =>
    let prev := st.relay.last.lookup op.code
    set { st with relay := { st.relay with host := rest, made := st.relay.made.push s!"{op.name}:{m.name}" } }
    let closed := ByteArray.mk #[Status.closed.code] ++ CloseReason.idle.name.toUTF8
    let page := op = .log || op = .read
    match m with
    | .pass => send op payload
    | .drop => pure ((← send op payload).map fun _ => closed)
    | .withhold => sawOp op; pure (some closed)
    | .duplicate => discard <| send op payload; send op payload
    | .flip i => pure ((← send op payload).map fun r =>
        if r.size ≤ 1 then r else Host.Sim.flipByte r (1 + i % (r.size - 1)))
    | .status s => pure ((← send op payload).map fun r => if r.size = 0 then r else r.set! 0 s.code)
    | .answer s n => sawOp op; pure (some (ByteArray.mk #[s.code] ++ n.toUTF8))
    | .replay => do
        let r ← send op payload
        pure (match r, prev with | some _, some p => some p | _, _ => r)
    | .pageIo =>
        if page then do sawOp op; pure (some (ByteArray.mk #[Host.pageIoReply.1] ++ Host.pageIoReply.2))
        else send op payload
    | m => pure ((← send op payload).map fun r => if page then pageEdit m r else r)

/-- The continuation nd hands follow on a resume: its own, or under the relay's next choice one
follow handed this actor earlier (a swapped continuation). -/
def swapK (name : String) (k : ByteArray) : M D ByteArray := do
  let st ← get
  match st.relay.resume with
  | [] => pure k
  | c :: rest =>
    let pool := (st.relay.ks.lookup name).getD #[]
    let pick : Option Nat := match c with
      | some i => if pool.isEmpty then none else some (i % pool.size)
      | none => none
    let made := match pick with
      | some i => st.relay.made.push s!"k:{i}"
      | none => st.relay.made
    set { st with relay := { st.relay with resume := rest, made } }
    pure (match pick with | some i => pool[i]?.getD k | none => k)

/-- The most continuations the relay keeps per actor. -/
def keptKs : Nat := 64

/-- Keep the continuation a step of follow's carries (when judging: the relay's pool). -/
def keepK (name : String) (b : ByteArray) : M D Unit := do
  if !(← get).judging then return
  match Reply.ofBytes b >>= Reply.cont with
  | none => pure ()
  | some k => modify fun st =>
      let pool := ((st.relay.ks.lookup name).getD #[]).push k
      let pool := if pool.size > keptKs then pool.extract (pool.size - keptKs) pool.size else pool
      { st with relay := { st.relay with ks := (name, pool) :: st.relay.ks.filter (·.1 ≠ name) } }

/-- The run actor `name` is in, if any. -/
def runNow (name : String) : M D (Option Nat) := do pure (((← get).runOf.lookup name).map (·.1))

/-- A call this run froze or continued (when judging). -/
def noteCall (name : String) (call : ByteArray) : M D Unit := do
  if !(← get).judging then return
  if let some n ← runNow name then modify fun st => { st with runCalls := (n, call) :: st.runCalls }

/-- A call-domain message custody signed, with the argv of the continuation that asked (when judging). -/
def noteSign (name : String) (msg k : ByteArray) : M D Unit := do
  if !(← get).judging || msg.extract 0 domCall.size != domCall then return
  let argv := ((Command.State.ofBytes k).map (·.argv)).getD []
  if let some n ← runNow name then modify fun st => { st with runSigns := (n, msg, argv) :: st.runSigns }

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
      let k ← swapK name k
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
      keepK name b
      match Reply.ofBytes b with
      | none => pure (.refused "badFrame", "")
      | some (.done exit out err) =>
          -- the plant: `pageIo` read as the old final refusal, verbatim (exit 1, `refused pageIo`)
          let (exit, err) := if (← get).sys.pageIoFatal && exit.toNat == CommandExit.pageIo.code then
              (CommandExit.refused.code.toUInt8, s!"refused {pageIoName}\n".toUTF8) else (exit, err)
          modify fun st => { st with lastErr := err }
          sawDone name depth exit out err
          pure (outcomeOf exit err, (String.fromUTF8? out).getD "")
      | some (.sign msg k) =>
          noteSign name msg k
          let (n, a, key) ← custodyOf name fault
          -- the plant: a cancel's message signed without its domain (the bare transaction id)
          let msg := if (← get).sys.cancelUndomained && msg.extract 0 domCancel.size == domCancel then
              msg.extract domCancel.size msg.size else msg
          resume name argv fault depth k (signWith (← params) key (a.next n) msg) fuel
      | some (.precommit k) =>
          let a ← actor name
          resume name argv fault depth k (precommitResult (← params) (a.next name) (a.pending name)) fuel
      | some (.signNext msg k) =>
          noteSign name msg k
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
          -- `lieCancel`: the relay keeps the cancel from the writer and answers it `refused cancelled`
          let lie : Option ByteArray := cancelLie (D := D) fault op
          match ← (match lie with | some r => pure (some r) | none => ask op p) with
          | none => tracedHost name op p none; pure (.refused "writerStopped", "")
          | some res =>
              let res := match fault with
                | .pageIo => if op = .log || op = .read then
                    ByteArray.mk #[Host.pageIoReply.1] ++ Host.pageIoReply.2 else res
                | _ => res
              let st ← get
              -- what nd reads: the reply after every relay fault below
              let seen := if st.sys.staleRange && argv.contains "--range" && op = .log then
                  hideLog st.sys.follow ((st.actors.lookup name).map (·.follow.world) |>.getD st.genesis) res
                else res
              tracedHost name op p (some (if op = .log then pageFault fault seen else seen))
              -- the plant `trustCancel`: follow's old phase 10, `cancelled` on the writer's word
              if st.sys.trustCancel && op = .cancel &&
                  Command.hostReply res == some (.refused, (Receive.Refusal.cancelled : Receive.Refusal D).name.toUTF8) then
                return (.ok, "cancelled\n")
              -- the plant `staleRange`: a relay that hides the log from an invoke with `--range`
              let res := if st.sys.staleRange && argv.contains "--range" && op = .log then
                  hideLog st.sys.follow ((st.actors.lookup name).map (·.follow.world) |>.getD st.genesis) res
                else res
              resume name argv fault depth k (if op = .log then pageFault fault res else res) fuel
      | some (.submit call k) => do
          sawCall name call
          noteCall name call
          let a ← actor name
          setActor name { a with last := some call, arming := false,
                                 armed := if a.arming then some call else a.armed,
                                 attempts := a.attempts ++ [{ argv, call, k }] }
          match fault with
          | .race other otherArgv =>
              match ← subst otherArgv with
              | .error e => return (.refused e, "")
              | .ok av =>
                  -- another member's nd, run to its end between this command's signature and its submit
                  let (o, _) ← withRun other av (depth - 1) (command other av .none depth)
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
          touchFrozen name call fun f => { f with sends := f.sends + 1 }
          if !forwards fault then
              tracedHost name .submit call none
              drive name call fault depth fuel (sends + 1) (some (.submit, .lost)) reply host said
          else
              match ← ask .submit call with
              | none => tracedHost name .submit call none; pure (.error "writerStopped")
              | some res =>
                  if (losesFirstReply fault || fault matches .dropReplies) && sends = 0 then
                      tracedHost name .submit call none
                      drive name call fault depth fuel (sends + 1) (some (.submit, .lost)) reply host said
                  else
                      tracedHost name .submit call (some res)
                      drive name call fault depth fuel (sends + 1) (some (.submit, hostSaid res)) (some res) (some (hostSaid res)) said
      | .lookup =>
          if fault matches .dropReplies then
            tracedHost name .lookup call none
            drive name call fault depth fuel sends (some (.lookup, .lost)) reply host said
          else
          match ← ask .lookup call with
          | none => tracedHost name .lookup call none; pure (.error "writerStopped")
          | some res =>
              let res := lookupLie fault res
              tracedHost name .lookup call (some res)
              drive name call fault depth fuel sends (some (.lookup, hostSaid res)) (some res)
                (some (hostSaid res)) said
      | .confirm | .probe =>
          let req : Attempt.Request := if a = .confirm then .confirm else .probe
          if (← get).sys.trustLookup && a = .confirm && (match host with | some .refused => true | _ => false) then
            -- the plant: the Host's final refusal taken as final, never confirmed by follow
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
          touchFrozen name call fun f => { f with settled := true }
          settle name call .committed
          pure (.ok (ended .committed said))
      | .refused =>
          touchFrozen name call fun f => { f with settled := true }
          settle name call .refused; pure (.ok (ended .refused said))
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

/-- One `nd ARGV` of actor `name` (`client/src/run.rs`'s `run`, CLIENT-37). When an earlier run of the
same argv left its attempt open, this run IS that attempt: it is driven from where it stands (sent,
outcome lost, with the sends it has made), and follow is resumed with the attempt's own continuation
and its end, so follow is never asked to plan and nothing new is signed. When that end is `refused`
and follow agrees (`done` with exit `refused`: its own World holds the call refused or expired, so
nothing of it can land), the command is planned afresh. Otherwise follow plans the command. -/
def ndRun (name : String) (argv : List String) (fault : Fault) : M D (Expect × String) :=
  withRun name argv 3 do
    let a ← actor name
    let frozen := if (← get).sys.rerunFresh then none
      else a.attempts.reverse.find? fun f => f.argv == argv && !f.settled
    match frozen with
    | none => command name argv fault 4
    | some f =>
        noteCall name f.call
        modify fun st => { st with hint := ByteArray.empty }
        match ← drive name f.call fault 3 attemptFuel f.sends (some (.submit, .lost)) none none "" with
        | .error e => pure (.refused e, "")
        | .ok res =>
            let n := ((← get).runOf.lookup name).map (·.1)
            let r ← resume name argv fault 3 f.k res Bounds.stepsPerCommandMax
            let st ← get
            let followRefused := match n.bind (fun i => st.ended.lookup i) with
              | some (e, _, _) => e.toNat == CommandExit.refused.code
              | none => false
            if firstByte res == Attempt.Action.refused.code && followRefused then command name argv fault 4
            else pure r

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
  let g ← match Receive.genesis X Rows.Params.worldName nonce Rows.Params.allowance fs (Writer.authority R) with
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
      | .genesis name nonce allowance fs auth => .genesis name (flipLast nonce) allowance fs auth
      | .carried s chain => .carried { s with nonce := flipLast s.nonce } chain
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

/-- An argv with `sync --to`'s anchor dropped: the bare catch-up (PROTOCOL-74's plant). -/
def dropAnchor : List String → List String
  | ["sync", "--to", _] => ["sync"]
  | av => av

/-- A hostile client's call: `av` parsed and planned on the World `w` as it stands, under the member
`self` whose current and next public keys are `key` and `next`, and signed by `sign`, WITHOUT follow's
own admission (`planUnchecked`, the range reads `signedReads` lists); `refused NAME`'s name otherwise. -/
def forgedCall (X : Ctx D) (self : Self D) (w : World D) (key next : ByteArray)
    (sign : ByteArray → ByteArray) (av : List String) : Except String ByteArray :=
  match parse (D := D) X.digestOf (av.map String.toUTF8) with
  | .error r => .error r.name
  | .ok cmd =>
    match body X self w ⟨key, next, ByteArray.empty⟩ cmd >>= fun b =>
        signedReads X w cmd >>= fun rs => planUnchecked X self w key rs b with
    | .error r => .error r.name
    | .ok (u, _) => .ok (X.callBytes ⟨u, sign (X.callMessage u)⟩)

/-- The actor's command planned on its follow's World as it stands (no catching up: the World of its
last command), signed and submitted WITHOUT follow's own admission (`planUnchecked`, with the range
reads `signedReads` lists there). The outcome is the writer's answer. -/
def forged (who : String) (av : List String) : M D (Expect × String) := do
  let a ← actor who
  let R ← params
  match forgedCall (← X) a.self a.follow.world (R.pub (a.key who)) (R.pub (a.next who))
      (R.sign (a.key who)) av with
  | .error r => pure (.refused r, "")
  | .ok call =>
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
          let av := if (← get).sys.dropRange then dropRangeFlag av else av
          -- the plant (PROTOCOL-74): a client that compares with nobody
          let av := if (← get).sys.ignoreAnchor then dropAnchor av else av
          let (o, out) ← ndRun l.actor av l.fault
          -- the plant: follow acts on the writer's `beforeLog`, taking its first step (the carried
          -- World) as the base on the writer's word, and reads again
          let (o, out) ← if (← get).sys.actOnBeforeLog && o == .refused "beforeLog" then do
              let a ← actor l.actor
              setActor l.actor { a with follow := { world := (← get).genesis } }
              ndRun l.actor av l.fault
            else pure (o, out)
          -- the plant: a description with its `doc` line dropped
          let out := if (← get).sys.dropDoc && av.length == 3 && av.getLast? == some "?" then
              "\n".intercalate ((out.splitOn "\n").filter fun ln => !ln.startsWith "doc ")
            else out
          -- the plant: a client that runs every write command again (the line's outcome, output
          -- and binds are the first run's; only the work doubles)
          if (← get).sys.twiceEach && av.head? ≠ some "read" then
            discard <| ndRun l.actor av l.fault
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
          -- the operator re-states the World's own authority (KERNEL-79)
          let stated := some ((authorityOf r0.world).getD Authority.none)
          match Host.Carry.importWorld X R.dc Rows.Params.worldName (flipLast Rows.Params.nonce) (.digest want) stated f with
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
      | some _ => ndRun l.actor ["receipt", Text.toHex ((← actor owner).last.getD ByteArray.empty)] .none
  | .cancelOf owner => do
      let st ← get
      match (← actor owner).last >>= st.sys.follow.decodeCall with
      | none => pure (.refused "noAttempt", "")
      | some _ => ndRun l.actor ["cancel", Text.toHex ((← actor owner).last.getD ByteArray.empty)] l.fault
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
  | .verifyHealth owner hb => do
      let st ← get
      let X := st.sys.follow
      let some b := st.binds.lookup hb >>= Text.ofHex | return (.refused s!"unbound {hb}", "")
      let some r := Health.ofBytes X.env st.sys.writer.R.dc b | return (.refused "badHealth", "")
      let r := match l.fault with
        | .forgeReceipt => { r with answer := { r.answer with ticks := 0 } }
        | _ => r
      -- the checker's head: its own World's, nothing the receipt states
      let w := (← actor l.actor).follow.world
      let m := (← actor owner).self.member
      let ans := if st.sys.trustReceipt then
          (if rootsDigest X.env r.root r.jroot r.rroot r.rowsroot = w.roots X.env then .ok r.answer
           else .error .headMismatch)
        else Health.check X.env (Head.headOf X.env w) m r
      match ans with
      | .ok a => pure (.ok, a.text w.height)
      | .error e => pure (.refused e.name, "")
  | .used atLeast => do
      -- the member's own World, caught up; the calls the writer committed, as its clients sent them
      let (o, _) ← ndRun l.actor ["sync"] .none
      if o ≠ .ok then return (.refused s!"sync:{o.text}", "")
      let st ← get
      let a ← actor l.actor
      let calls := st.committed.toList.filterMap st.sys.follow.decodeCall
      let n := (Use.shared st.sys.follow a.follow.world calls).length
      note s!"USE {l.actor} shared-objects {n} of {calls.length} committed calls"
      if atLeast ≤ n then pure (.ok, "") else pure (.refused s!"unshared:{n}", "")
  | .retry => pure (← retry l.actor, "")
  | .rerun => do
      match (← actor l.actor).attempts.getLast? with
      | none => pure (.refused "noAttempt", "")
      | some f => ndRun l.actor f.argv .none
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
  /-- the trace (Q5), when the run recorded one: a `custody NAME CURRENT NEXT PENDING` line per actor
  (its key file's seeds of generations 0, 1 and 2), then the runs in the order they started -/
  trace : Array String := #[]

/-- A fresh deployment of the system `s`: the genesis World, its Store and the writer serving it,
the founding invitation and the founders' binds; no actor has run yet. -/
def setup (s : Sys D) : IO (St D) := do
  let R := s.writer.R
  let fs := founders.map fun n => (keyOf R n 0, nextKeyDigest s.writer.X (keyOf R n 1))
  let g ← match Receive.genesis s.writer.X Rows.Params.worldName Rows.Params.nonce Rows.Params.allowance fs (Writer.authority R) with
    | .ok g => pure g
    | .error r => throw (IO.userError s!"genesis refused {r.name}")
  let (mem, r₀) ← match ← Writer.genesisStore s.writer g with
    | .ok m => pure m
    | .error e => throw (IO.userError s!"genesis: {e}")
  let host ← Writer.start s.writer mem r₀
  let hex (d : D) := Text.toHex (s.writer.X.env.bytes d)
  -- the World's origin inputs, as the founders hold them (`host genesis` prints them), and another
  -- World's (the nonce changed)
  let inputs := Invite.inputBytes s.writer.X Rows.Params.worldName Rows.Params.nonce Rows.Params.allowance fs
    (Writer.authority R)
  let other := Invite.inputBytes s.writer.X Rows.Params.worldName (flipLast Rows.Params.nonce)
    Rows.Params.allowance fs (Writer.authority R)
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
    [("inputs", Text.toHex inputs), ("otherInputs", Text.toHex other), ("world", hex g.origin),
     ("chain0", hex g.chain), ("roots0", hex (g.roots s.writer.X.env))] ++
    (founders ++ ["newcomer"]).map fun n => (n ++ ".key", Text.toHex (keyOf R n 0))
  pure { sys := s, host, mem, genesis := g, lineage := g.origin, first := g, binds, invitation }

/-- Run a member row against a fresh deployment under the parameters `R` and the plant `m`;
`times` scales every repeated line. -/
def run (R : Rows.Params D) (m : Option Mutation) (lines : List Line) (times : Option Nat)
    (budget : Option Nat := none) (tracing : Bool := false) : IO Result := do
  let s := sys R m
  let s := match budget with
    | some b => { s with writer := { s.writer with pageBudget := b } }
    | none => s
  let st0 ← setup s
  let go : M D (List Expect) := lines.zipIdx.mapM fun (l, i) =>
    runLine i l (if l.times > 1 then times.getD l.times else l.times)
  let (outcomes, st) ← go.run { st0 with tracing }
  let steps := match ← st.host.stop with
    | .ok (_, r) => r.world.steps
    | .error _ => 0
  let seeds (n : String) : String := String.join ([0, 1, 2].map fun g => " " ++ hexOf (R.seedOf (secretOf n g)))
  let custody := st.actors.toArray.map fun (n, _) => "custody " ++ n ++ seeds n
  pure ⟨{ outcomes, ops := st.ops, kinds := st.kinds }, st.log, st.times, st.reopenNs, st.reopenReads, st.invokes,
    st.conn, steps, if tracing then custody ++ st.trace else #[]⟩

end Nanodregg.Protocol.Rows.Loopback
