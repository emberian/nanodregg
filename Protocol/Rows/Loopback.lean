/-
# Protocol.Rows.Loopback — the member rows, in process

Each member row runs against a fresh writer (`Protocol.Rows.Writer`: HOST's loop on its own
thread) and, per actor, an in-process client that plays the parts `nd` and custody play, and runs
`host follow`'s machine (`Protocol.Command.start`/`step`) on the actor's own follow World:

* every step crosses the wire: the command is `commandFrame` bytes, each step `Reply.bytes`, each
  resume `resumeFrame` bytes, each one decoded back by the one reader before it is used;
* custody holds the actor's toy key (`key:NAME`, next `next:NAME`) and answers `signResultFrame`;
* a `host` step is relayed to the writer as a frame; a `submit` step is frozen as the actor's
  attempt and sent, and a lost reply is settled by `lookup` of the same bytes, never re-signed
  (the attempt store's rule, CLIENT-3);
* every operation sent on either socket is recorded, so the judge compares OBSERVED ops with the
  row's declared ones (`judge_members_pass_iff`).

The founders `sponsor` and `operator` are the genesis World (`Receive.genesis`); any other actor is
a stranger (an id nobody enrolled) until a line binds its member id and its World grant.
-/
import Protocol.Rows.Writer
import Protocol.Rows.Judge
import Protocol.Command.Wire
import Host.Follow
import Protocol.Attempt

namespace Nanodregg.Protocol.Rows.Loopback

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Protocol.Command
open Nanodregg.Protocol.Rows.Sim (D)

/-! ## The system a row runs, and its mutations -/

structure Sys where
  writer : Writer.Params
  follow : Ctx D
  /-- after a lost reply the client signs afresh instead of looking up (a plant) -/
  resendFresh : Bool := false
  /-- every `withinMs` is 0 (a plant) -/
  zeroDeadline : Bool := false
  /-- custody advances when it signs a rotation, not on settlement (a plant) -/
  advanceOnSend : Bool := false
  /-- a second genesis draws the first one's nonce (a plant) -/
  nonceRepeats : Bool := false

def skipJudge (X : Ctx D) : Ctx D :=
  { X with program := { X.program with judge := fun _ _ _ _ _ _ => .ok () } }

/-- The keyed account id with its owner dropped: `accountId`'s hash sees only the asset (the
second half of `owner ‖ asset`, both digests of one width). -/
def accountByAsset (X : Ctx D) : Ctx D :=
  { X with env := { X.env with hash := fun dom b =>
      if dom = domAccount then X.env.hash dom (b.extract (b.size / 2) b.size) else X.env.hash dom b } }

def sys : Option Mutation → Sys
  | none => { writer := { X := Sim.ctx }, follow := Sim.ctx }
  | some .openLog => { writer := { X := Sim.ctx, gateLog := false }, follow := Sim.ctx }
  | some .skipJudge => { writer := { X := skipJudge Sim.ctx }, follow := skipJudge Sim.ctx }
  | some .followVerifyAll =>
      { writer := { X := Sim.ctx }, follow := { Sim.ctx with verify := fun _ _ _ => true } }
  | some .forgetJournal => { writer := { X := Sim.ctx, forgetJournal := true }, follow := Sim.ctx }
  | some .resendFresh => { writer := { X := Sim.ctx }, follow := Sim.ctx, resendFresh := true }
  | some .zeroDeadline => { writer := { X := Sim.ctx }, follow := Sim.ctx, zeroDeadline := true }
  | some .advanceOnSend => { writer := { X := Sim.ctx }, follow := Sim.ctx, advanceOnSend := true }
  | some .lieTip => { writer := { X := Sim.ctx, lieTip := true }, follow := Sim.ctx }
  | some .forgeBase => { writer := { X := Sim.ctx, forgeBase := true }, follow := Sim.ctx }
  | some .unstatedExpiry => { writer := { X := Sim.ctx, unstatedExpiry := true }, follow := Sim.ctx }
  | some .ignoreNotBefore => { writer := { X := Sim.ctx, ignoreNotBefore := true }, follow := Sim.ctx }
  | some .nonceRepeats => { writer := { X := Sim.ctx }, follow := Sim.ctx, nonceRepeats := true }
  | some .accountByAsset =>
      { writer := { X := accountByAsset Sim.ctx }, follow := accountByAsset Sim.ctx }
  | some .writerForgetsSpent => { writer := { X := Sim.ctx, forgetSpent := true }, follow := Sim.ctx }

/-! ## Actors -/

def founders : List String := ["sponsor", "operator"]

/-- Custody's toy key of generation `gen` (toy parameters: a key is its own public and secret). -/
def keyOf (name : String) (gen : Nat) : ByteArray := s!"key:{name}:{gen}".toUTF8

structure Actor where
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

def Actor.key (n : String) (a : Actor) : ByteArray := keyOf n a.gen
def Actor.next (n : String) (a : Actor) : ByteArray := keyOf n (a.gen + 1)
def Actor.pending (n : String) (a : Actor) : ByteArray := keyOf n (a.gen + 2)

/-- One line's measured run. -/
structure Timed where
  line : Nat
  ns : List Nat

structure St where
  sys : Sys
  host : Writer.Running
  mem : Writer.Mem
  genesis : World D
  actors : List (String × Actor) := []
  binds : List (String × String) := []
  ops : List Op := []
  kinds : List String := []
  conn : Nat := 0
  log : Array String := #[]
  times : Array Timed := #[]
  reopenNs : List Nat := []
  /-- each invoke a client froze: the machine ticks its run used and the packages it loaded and
  re-checked (`Lang.runMeasured` on the inputs `Kernel.Receive.invokeRun` derives) -/
  invokes : Array (Nat × Nat) := #[]
  /-- every call the attempt store settled as committed, in order: the writer's log, as its clients
  sent it -/
  committed : Array ByteArray := #[]

abbrev M := StateT St IO

def X : M (Ctx D) := do pure (← get).sys.follow

def note (s : String) : M Unit := modify fun st => { st with log := st.log.push s }

def sawOp (op : Op) : M Unit :=
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
whose run refuses costs nothing here (it is not admitted). -/
def measureInvoke (X : Ctx D) (w : World D) (c : Call D) : Option (Nat × Nat) :=
  match c.unsigned.body with
  | .invoke obj method args budget via =>
    let look := pinned X.env w c.unsigned.pins
    match invokeRun X look c c.unsigned.member obj method via with
    | .ok (cell, p, r) =>
      match Lang.runMeasured X.env.bytes X.digestOf look p (stateOf cell) method args r budget with
      | .ok (_, ticks, pkgs) => some (ticks, pkgs)
      | .error _ => none
    | .error _ => none
  | _ => none

def sawCall (name : String) (call : ByteArray) : M Unit := do
  let decoded := Sim.ctx.decodeCall call
  let k := match decoded with
    | some c => kindName c.unsigned.body
    | none => "undecodable"
  modify fun st => if st.kinds.contains k then st else { st with kinds := st.kinds ++ [k] }
  if let (some c, some a) := (decoded, (← get).actors.lookup name) then
    if let some m := measureInvoke (← get).sys.writer.X a.follow.world c then
      modify fun st => { st with invokes := st.invokes.push m }

def founderIndex (name : String) : Option Nat := founders.idxOf? name

def freshActor (name : String) : M Actor := do
  let st ← get
  let X := st.sys.writer.X
  let self : Self D := match founderIndex name with
    | some i => { world := st.genesis.origin, member := founderId X st.genesis.origin i, grant := founderGrantId X st.genesis.origin i,
                  window := 100 }
    | none => { world := st.genesis.origin, member := X.env.hash "nanodregg/rows/stranger/v1" name.toUTF8,
                grant := X.env.hash "nanodregg/rows/stranger-grant/v1" name.toUTF8, window := 100 }
  pure { self, follow := { world := st.genesis } }

def actor (name : String) : M Actor := do
  match (← get).actors.lookup name with
  | some a => pure a
  | none =>
      let a ← freshActor name
      modify fun st => { st with actors := st.actors ++ [(name, a)] }
      pure a

def setActor (name : String) (a : Actor) : M Unit :=
  modify fun st => { st with actors := st.actors.map fun (n, b) => if n = name then (n, a) else (n, b) }

/-- Bind `b` to `hex`; a bound member id, or a World grant bound as `NAME.grant`, becomes that
actor's. -/
def bind (b hex : String) : M Unit := do
  modify fun st => { st with binds := (b, hex) :: st.binds }
  let some d := Text.ofHex hex >>= Sim.digestOf | return
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
def subst (argv : List String) : M (Except String (List String)) := do
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

/-- The first `id HEX` or `join HEX` a command printed. -/
def boundToken (out : String) : Option String :=
  (out.splitOn "\n").findSome? fun l =>
    match l.splitOn " " with
    | ["id", h] => some h
    | ["join", h] => some h
    | _ => none

/-! ## Custody and the writer's socket -/

/-- Custody's answer to a sign step: `ok ‖ (key, next, signature)` (every step result is
`status ‖ payload`); `stolen` replaces the key it signs
with (a thief holding a victim's current key). -/
def signWith (key next msg : ByteArray) : ByteArray :=
  match Text.fit Bounds.frameBytesMax key, Text.fit Bounds.frameBytesMax next,
      Text.fit Bounds.frameBytesMax (Sim.sign key msg) with
  | some k, some n, some s => ByteArray.mk #[Status.ok.code] ++ signResultFrame.bytes (k, n, s, ())
  | _, _, _ => ByteArray.empty

def precommitResult (next pending : ByteArray) : ByteArray :=
  match Text.fit Bounds.frameBytesMax next, Text.fit Bounds.frameBytesMax pending with
  | some n, some p => ByteArray.mk #[Status.ok.code] ++ precommitResultFrame.bytes (n, p, ())
  | _, _ => ByteArray.empty

/-- The actor's custody name and current key under a fault (a thief signs with a stolen key). -/
def custodyOf (name : String) (fault : Fault) : M (String × Actor × ByteArray) := do
  let a ← actor name
  match fault with
  | .stolenKey v => let va ← actor v; pure (name, a, va.key v)
  | _ => pure (name, a, a.key name)

/-- Custody settles its armed rotation on the attempt's settlement: committed advances it,
refused drops it, absent or uncertain keeps it armed (CLIENT-13). -/
def settle (name : String) (call res : ByteArray) : M Unit := do
  let a ← actor name
  if a.armed = some call then
    match Command.hostReply res with
    | some (.ok, _) => setActor name { a with gen := a.gen + 1, armed := none }
    | some (.refused, _) => setActor name { a with armed := none }
    | _ => pure ()

/-- Send one frame to the writer; its reply as `status ‖ payload`, or `none` if it has stopped. -/
def ask (op : Op) (payload : ByteArray) : M (Option ByteArray) := do
  sawOp op
  let st ← get
  set { st with conn := st.conn + 1 }
  match ← st.host.ask ⟨UInt32.ofNat st.conn, op.code, payload⟩ with
  | some r => pure (some (ByteArray.mk #[r.status] ++ r.payload))
  | none => pure none

/-- How the rows' followers read a base: the Sim's World codec and the writer's own `worldDigest`. -/
def base : Thin.Base (World D) :=
  ⟨Sim.world, World.height, Host.Sim.keys.worldDigest, Writer.cadence.worldBytesMax⟩

/-- Send one frame to the actor's `host follow` (`Host.Follow.answer`, the deployed per-frame
decision, on the actor's follow state); the step's bytes, or the name follow refused it by. What
follow would persist is not modelled here: the actor's state is in memory. -/
def followAsk (name : String) (self : Self D) (op : Op) (payload : ByteArray) :
    M (Except String ByteArray) := do
  sawOp op
  let a ← actor name
  let st ← get
  set { st with conn := st.conn + 1 }
  let (fs', _, status, p) :=
    Host.Follow.answer (← X) base self a.follow ⟨UInt32.ofNat st.conn, op.code, payload⟩
  setActor name { a with follow := fs' }
  pure (if status = Status.ok.code then .ok p else .error (Command.hostName p))

/-! ## Transport faults on a log page -/

def flipLast (b : ByteArray) : ByteArray :=
  if h : 0 < b.size then b.set (b.size - 1) (b[b.size - 1] ^^^ 1) (by omega) else b

def editPage (f : List ByteArray → List ByteArray) (reply : ByteArray) : ByteArray :=
  match Command.hostReply reply with
  | some (.ok, p) =>
      match logReplyFrame.decode p with
      | .ok (l, h, c, t, ()) =>
          match Text.fitList Bounds.frameBytesMax (f (Text.unlist l)) with
          | some l' => ByteArray.mk #[Status.ok.code] ++ logReplyFrame.bytes (l', h, c, t, ())
          | none => reply
      | .error _ => reply
  | _ => reply

def pageFault : Fault → ByteArray → ByteArray
  | .flipEvent i => editPage fun evs => evs.mapIdx fun j e => if j = i then flipLast e else e
  | .dropLastEvent => editPage List.dropLast
  | .inflateExpired n => fun reply =>
      match Command.hostReply reply with
      | some (.refused, p) => match expiredHeight? p with
        | some h => ByteArray.mk #[Status.refused.code] ++ (ReadRefusal.expired (h + n)).payload
        | none => reply
      | _ => reply
  | _ => id

def coldFault : Fault → Bool
  | .flipEvent _ | .dropLastEvent | .cold | .inflateExpired _ => true
  | _ => false

/-! ## The attempt store -/

/-- A reply, as the attempt decision sees it (its status byte; no reply at all is `lost`). -/
def classify (res : ByteArray) : Attempt.Seen :=
  match Command.hostReply res with
  | some (.ok, _) => .committed
  | some (.refused, _) => .refused
  | some (.uncertain, _) => .unknown
  | some (.absent, _) => .absent
  -- the connection ended with the request unanswered: as if the reply were lost
  | some (.closed, _) | none => .lost

/-- Requests one attempt may make in one run: every send, and at most one lookup after each
(`Proofs.Attempt.next_after_lookup`), and one more for the decision that ends it. -/
def attemptFuel : Nat := 2 * Bounds.sendsMax + 2

/-- The attempt store settles the frozen `call` with `Protocol.Attempt.next` deciding every
request (PROTOCOL-17): the rows run the decision CLIENT-3 runs, not a restatement of it. Faults:
`dropReply` loses the reply to the FIRST submit after the writer took it; `neverForward` keeps
every submit from reaching the writer. The settling reply, `status ‖ payload`, is what follow is
resumed with; custody settles an armed rotation on it. -/
def drive (name : String) (call : ByteArray) (fault : Fault) :
    Nat → Nat → Option (Attempt.Request × Attempt.Seen) → Option ByteArray → M (Except String ByteArray)
  | 0, _, _, _ => pure (.error "attemptFuel")
  | fuel + 1, sends, last, reply => do
      match Attempt.next (decide (sends < Bounds.sendsMax)) last with
      | .submit =>
          match fault with
          | .neverForward => drive name call fault fuel (sends + 1) (some (.submit, .lost)) reply
          | _ =>
              match ← ask .submit call with
              | none => pure (.error "writerStopped")
              | some res =>
                  match fault, sends with
                  | .dropReply, 0 => drive name call fault fuel (sends + 1) (some (.submit, .lost)) reply
                  | _, _ => drive name call fault fuel (sends + 1) (some (.submit, classify res)) (some res)
      | .lookup =>
          match ← ask .lookup call with
          | none => pure (.error "writerStopped")
          | some res => drive name call fault fuel sends (some (.lookup, classify res)) (some res)
      | .committed | .refused | .absent =>
          match reply with
          | some r =>
              if classify r = .committed then
                modify fun st => { st with committed := st.committed.push call }
              settle name call r; pure (.ok r)
          | none => pure (.error "noReply")
      | .badReply => pure (.error Attempt.Action.badReply.name)
      | .uncertain =>
          -- the run stops unsettled: follow is told `uncertain`
          match reply with
          | some r => pure (.ok r)
          | none => pure (.ok (ByteArray.mk #[Status.uncertain.code]))

/-! ## One command -/

def outcomeOf (exit : UInt8) (err : ByteArray) : Expect :=
  let e := (String.fromUTF8? err).getD ""
  match exit.toNat with
  | 0 => .ok
  | 1 => .refused (((e.trimAscii.toString.dropPrefix? "refused ").map (·.toString)).getD e)
  | 2 => .uncertain
  | 3 => .absent
  | n => .refused s!"exit{n}"

def statusOutcome (reply : ByteArray) : Expect :=
  match Command.hostReply reply with
  | some (.ok, _) => .ok
  | some (.absent, _) => .absent
  | some (.uncertain, _) => .uncertain
  | some (.refused, p) => .refused (Command.hostName p)
  -- a closed connection is not a verdict on the call
  | some (.closed, _) => .uncertain
  | none => .refused "badReply"

mutual
/-- Run `argv` as actor `name`: start, then every step through the wire until `done`. -/
def command (name : String) (argv : List String) (fault : Fault) : Nat → M (Expect × String)
  | 0 => pure (.refused "tooDeep", "")
  | depth + 1 => do
      let a ← actor name
      let gw := (← get).genesis
      let a := if coldFault fault then { a with follow := { world := gw } } else a
      setActor name a
      let self ← match fault with
        | .stolenKey v => pure (← actor v).self
        | _ => pure a.self
      let some argvF := (Text.fitList Bounds.argvBytesMax (argv.map String.toUTF8)).bind fun v =>
          if h : (Codec.Layout.codec Bounds.argvBytesMax (by decide) commandLayout).size (v, ()) ≤
              Bounds.argvBytesMax then some (⟨(v, ()), h⟩ : { v : Codec.Layout.Ty Bounds.argvBytesMax commandLayout //
                (Codec.Layout.codec Bounds.argvBytesMax (by decide) commandLayout).size v ≤ Bounds.argvBytesMax })
            else none
        | pure (.refused "argvPastBound", "")
      match ← followAsk name self .command (commandFrame.bytes argvF) with
      | .error n => pure (.refused n, "")
      | .ok b => steps name argv fault depth b Bounds.stepsPerCommandMax
termination_by d => (d, 0)

/-- Feed a step's result back to follow, through the resume frame. -/
def resume (name : String) (argv : List String) (fault : Fault) (depth : Nat) (k result : ByteArray) :
    Nat → M (Expect × String)
  | 0 => pure (.refused "tooManySteps", "")
  | fuel + 1 => do
      let some kf := Text.fit Bounds.frameBytesMax k | return (.refused "badState", "")
      let some rf := Text.fit Bounds.frameBytesMax result | return (.refused "badResult", "")
      let a ← actor name
      let self ← match fault with
        | .stolenKey v => pure (← actor v).self
        | _ => pure a.self
      match ← followAsk name self .resume (resumeFrame.bytes (kf, rf, ())) with
      | .error n => pure (.refused n, "")
      | .ok b => steps name argv fault depth b fuel
termination_by fuel => (depth, fuel + 1)

/-- Perform one step the follow machine asked for. -/
def steps (name : String) (argv : List String) (fault : Fault) (depth : Nat) (b : ByteArray) :
    Nat → M (Expect × String)
  | 0 => pure (.refused "tooManySteps", "")
  | fuel + 1 => do
      match Reply.ofBytes b with
      | none => pure (.refused "badFrame", "")
      | some (.done exit out err) => pure (outcomeOf exit err, (String.fromUTF8? out).getD "")
      | some (.sign msg k) =>
          let (n, a, key) ← custodyOf name fault
          resume name argv fault depth k (signWith key (a.next n) msg) fuel
      | some (.precommit k) =>
          let a ← actor name
          resume name argv fault depth k (precommitResult (a.next name) (a.pending name)) fuel
      | some (.signNext msg k) =>
          let a ← actor name
          let r := signWith (a.next name) (a.pending name) msg
          setActor name (if (← get).sys.advanceOnSend then { a with gen := a.gen + 1 } else { a with arming := true })
          resume name argv fault depth k r fuel
      | some (.host op p k) =>
          match ← ask op p with
          | none => pure (.refused "writerStopped", "")
          | some res => resume name argv fault depth k (if op = .log then pageFault fault res else res) fuel
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
              match ← drive name call fault attemptFuel 0 none none with
              | .error e => pure (.refused e, "")
              | .ok res => resume name argv fault depth k res fuel
termination_by fuel => (depth, fuel + 1)
end

/-! ## The operator's and the attempt store's acts -/

def nowNs : IO Nat := IO.monoNanosNow

/-- Stop the loop, open the Store cold (its base and the tail after it), start the loop on what it
opened to. The reopen's wall time is THE BAR's `reopen-ms`. -/
def restart (sealFirst : Bool) : M Expect := do
  let st ← get
  match ← st.host.stop with
  | .error e => pure (.refused s!"writerFailed {e}")
  | .ok (.eof, r0) =>
      if sealFirst then
        match ← (Writer.checkpoint st.mem).write r0.world r0.pos (Host.sealEntries r0.sealed r0.index) r0.sealed.index with
        | .error f => return .refused f.name
        | .ok _ => pure ()
      let d ← st.mem.disk.get
      let bs ← st.mem.bases.get
      let t0 ← nowNs
      match Writer.reopen st.sys.writer bs.index bs.file d.synced with
      | .error f => pure (.refused f)
      | .ok r =>
          let t1 ← nowNs
          st.mem.disk.set { synced := d.synced.extract 0 r.pos.offset }
          let h ← Writer.start st.sys.writer st.mem r
          let ns := if sealFirst then [] else [t1 - t0]
          modify fun st => { st with host := h, reopenNs := st.reopenNs ++ ns }
          pure .ok
  | .ok (exit, _) => pure (.refused s!"writer{exit.name}")

/-- Open a copy of the Store whose base file has the byte at `off` flipped. -/
def reopenFlipped (off : Nat) : M Expect := do
  let st ← get
  let d ← st.mem.disk.get
  let bs ← st.mem.bases.get
  match Writer.reopen st.sys.writer bs.index (Host.Sim.flipByte bs.file off) d.synced with
  | .error f => pure (.refused f)
  | .ok _ => pure .ok

def retry (name : String) : M Expect := do
  match (← actor name).last with
  | none => pure (.refused "noAttempt")
  | some call =>
      -- a probe of a call the attempt store already settled: ONE lookup of the same bytes, so a
      -- journal that forgot it answers `absent` here (reopen's plant), instead of the attempt
      -- decision resending it (which a forgotten journal would admit twice)
      match ← ask .lookup call with
      | none => pure (.refused "writerStopped")
      | some res => settle name call res; pure (statusOutcome res)

/-! ## A row -/

/-- A SECOND writer, from a genesis of the same name, allowance and founders as the rows' writer, and
the same nonce (`sameNonce`, or under the `nonceRepeats` plant: a restore of the same World) or
another one (another World). -/
def secondWriter (sameNonce : Bool) : M (Except String Writer.Running) := do
  let st ← get
  let X := st.sys.writer.X
  let nonce := if sameNonce || st.sys.nonceRepeats then Sim.nonce else flipLast Sim.nonce
  let fs := founders.map fun n => (keyOf n 0, nextKeyDigest X (keyOf n 1))
  let g ← match Receive.genesis X Sim.worldName nonce Sim.allowance fs with
    | .ok g => pure g
    | .error r => return .error s!"genesis refused {r.name}"
  match ← Writer.genesisStore st.sys.writer g with
  | .error e => return .error e
  | .ok (mem, r₀) => return .ok (← Writer.start st.sys.writer mem r₀)

/-- Run one act once; its outcome and what it printed. -/
def runAct (l : Line) : M (Expect × String) := do
  match l.act with
  | .cmd argv =>
      match ← subst argv with
      | .error e => pure (.refused e, "")
      | .ok av => command l.actor av l.fault 4
  | .restart => pure (← restart false, "")
  | .seal => pure (← restart true, "")
  | .readElsewhere sameNonce => do
      -- the actor's own log envelope, for its own World, to a SECOND writer (as replayLog's)
      let st ← get
      let a ← actor l.actor
      let X := st.sys.writer.X
      let upTo := a.self.window
      let key := a.key l.actor
      let sig := Sim.sign key (Command.envelopeMessage X a.self 0 upTo)
      let some p := Envelope.bytes X (Command.envelopeOf a.self 0 upTo ⟨key, a.next l.actor, sig⟩)
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
      | .ok av =>
        let a ← actor l.actor
        let X ← X
        let w := a.follow.world
        let key := a.key l.actor
        match parse (D := D) X.digestOf (av.map String.toUTF8) with
        | .error r => pure (.refused r.name, "")
        | .ok cmd =>
          match body X a.self w ⟨key, a.next l.actor, ByteArray.empty⟩ cmd >>= fun b =>
              planUnchecked X a.self w key b with
          | .error r => pure (.refused r.name, "")
          | .ok (u, _) =>
            let call := X.callBytes ⟨u, Sim.sign key (X.unsignedBytes u)⟩
            sawCall l.actor call
            match ← ask .submit call with
            | none => pure (.refused "writerStopped", "")
            | some res =>
                if classify res = .committed then
                  modify fun st => { st with committed := st.committed.push call }
                pure (statusOutcome res, "")
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
  | .attest pin => do
      let w := (← actor l.actor).follow.world
      bind pin (Text.toHex (base.digest (Sim.world.bytes w)))
      bind s!"{pin}.h" (toString w.height)
      pure (.ok, "")
  | .retry => pure (← retry l.actor, "")
  | .reopenFlipped off => pure (← reopenFlipped off, "")

/-- Run a line `times` times; the first outcome that is not the declared one, else the declared
one. A run past `withinMs` (a liveness deadline) is `hang`. -/
def runLine (i : Nat) (l : Line) (times : Nat) : M Expect := do
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
  invokes : Array (Nat × Nat)

/-- Run a member row against a fresh deployment under `m`; `times` scales every repeated line. -/
def run (m : Option Mutation) (lines : List Line) (times : Option Nat) : IO Result := do
  let s := sys m
  let fs := founders.map fun n => (keyOf n 0, nextKeyDigest s.writer.X (keyOf n 1))
  let g ← match Receive.genesis s.writer.X Sim.worldName Sim.nonce Sim.allowance fs with
    | .ok g => pure g
    | .error r => throw (IO.userError s!"genesis refused {r.name}")
  let (mem, r₀) ← match ← Writer.genesisStore s.writer g with
    | .ok m => pure m
    | .error e => throw (IO.userError s!"genesis: {e}")
  let host ← Writer.start s.writer mem r₀
  let go : M (List Expect) := lines.zipIdx.mapM fun (l, i) =>
    runLine i l (if l.times > 1 then times.getD l.times else l.times)
  let hex (d : D) := Text.toHex (s.writer.X.env.bytes d)
  let binds := founders.zipIdx.flatMap fun (n, i) =>
    [(n, hex (founderId s.writer.X g.origin i)),
     (n ++ ".grant", hex (founderGrantId s.writer.X g.origin i))]
  let (outcomes, st) ← go.run { sys := s, host, mem, genesis := g, binds }
  let _ ← st.host.stop
  pure ⟨{ outcomes, ops := st.ops, kinds := st.kinds }, st.log, st.times, st.reopenNs, st.invokes⟩

end Nanodregg.Protocol.Rows.Loopback
