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

def skipJudge (X : Ctx D) : Ctx D :=
  { X with program := { X.program with judge := fun _ _ _ _ _ _ => .ok () } }

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

/-! ## Actors -/

def founders : List String := ["sponsor", "operator"]

/-- Custody's toy key of generation `gen` (toy parameters: a key is its own public and secret). -/
def keyOf (name : String) (gen : Nat) : ByteArray := s!"key:{name}:{gen}".toUTF8

structure Actor where
  self : Self D
  world : World D
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

def sawCall (call : ByteArray) : M Unit := do
  let k := match Sim.ctx.decodeCall call with
    | some c => kindName c.unsigned.body
    | none => "undecodable"
  modify fun st => if st.kinds.contains k then st else { st with kinds := st.kinds ++ [k] }

def founderIndex (name : String) : Option Nat := founders.idxOf? name

def freshActor (name : String) : M Actor := do
  let st ← get
  let X := st.sys.writer.X
  let self : Self D := match founderIndex name with
    | some i => { member := founderId X Sim.worldName i, grant := founderGrantId X Sim.worldName i,
                  window := 100 }
    | none => { member := X.env.hash "nanodregg/rows/stranger/v1" name.toUTF8,
                grant := X.env.hash "nanodregg/rows/stranger-grant/v1" name.toUTF8, window := 100 }
  pure { self, world := st.genesis }

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

def subst (argv : List String) : M (Except String (List String)) := do
  let binds := (← get).binds
  pure <| argv.mapM fun a =>
    if a.startsWith "@" then
      match binds.lookup (a.drop 1).toString with
      | some v => .ok v
      | none => .error s!"unbound {a}"
    else .ok a

/-- The first `id HEX` or `join HEX` a command printed. -/
def boundToken (out : String) : Option String :=
  (out.splitOn "\n").findSome? fun l =>
    match l.splitOn " " with
    | ["id", h] => some h
    | ["join", h] => some h
    | _ => none

/-! ## Custody and the writer's socket -/

/-- Custody's answer to a sign step: `(key, next, signature)`; `stolen` replaces the key it signs
with (a thief holding a victim's current key). -/
def signWith (key next msg : ByteArray) : ByteArray :=
  match Text.fit Bounds.frameBytesMax key, Text.fit Bounds.frameBytesMax next,
      Text.fit Bounds.frameBytesMax (Sim.sign key msg) with
  | some k, some n, some s => signResultFrame.bytes (k, n, s, ())
  | _, _, _ => ByteArray.empty

def precommitResult (next pending : ByteArray) : ByteArray :=
  match Text.fit Bounds.frameBytesMax next, Text.fit Bounds.frameBytesMax pending with
  | some n, some p => precommitResultFrame.bytes (n, p, ())
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
  | _ => id

def coldFault : Fault → Bool
  | .flipEvent _ | .dropLastEvent | .cold => true
  | _ => false

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
  | none => .refused "badReply"

mutual
/-- Run `argv` as actor `name`: start, then every step through the wire until `done`. -/
def command (name : String) (argv : List String) (fault : Fault) : Nat → M (Expect × String)
  | 0 => pure (.refused "tooDeep", "")
  | depth + 1 => do
      let a ← actor name
      let gw := (← get).genesis
      let a := if coldFault fault then { a with world := gw } else a
      setActor name a
      let self ← match fault with
        | .stolenKey v => pure (← actor v).self
        | _ => pure a.self
      sawOp .command
      let some argvF := (Text.fitList Bounds.argvBytesMax (argv.map String.toUTF8)).bind fun v =>
          if h : (Codec.Layout.codec Bounds.argvBytesMax (by decide) commandLayout).size (v, ()) ≤
              Bounds.argvBytesMax then some (⟨(v, ()), h⟩ : { v : Codec.Layout.Ty Bounds.argvBytesMax commandLayout //
                (Codec.Layout.codec Bounds.argvBytesMax (by decide) commandLayout).size v ≤ Bounds.argvBytesMax })
            else none
        | pure (.refused "argvPastBound", "")
      let argv' ← match commandFrame.decode (commandFrame.bytes argvF) with
        | .ok v => pure (Text.unlist v.1.1)
        | .error _ => return (.refused "badCommandFrame", "")
      let r := Command.start (← X) self a.world argv'
      steps name argv fault depth r Bounds.stepsPerCommandMax
termination_by d => (d, 0)

/-- Feed a step's result back to follow, through the resume frame. -/
def resume (name : String) (argv : List String) (fault : Fault) (depth : Nat) (k result : ByteArray) :
    Nat → M (Expect × String)
  | 0 => pure (.refused "tooManySteps", "")
  | fuel + 1 => do
      sawOp .resume
      let some kf := Text.fit Bounds.frameBytesMax k | return (.refused "badState", "")
      let some rf := Text.fit Bounds.frameBytesMax result | return (.refused "badResult", "")
      match resumeFrame.decode (resumeFrame.bytes (kf, rf, ())) with
      | .error _ => pure (.refused "badResumeFrame", "")
      | .ok (k', r', ()) =>
          let a ← actor name
          let self ← match fault with
            | .stolenKey v => pure (← actor v).self
            | _ => pure a.self
          let (w', _, reply) := Command.step (← X) self a.world k'.1 r'.1
          setActor name { a with world := w' }
          steps name argv fault depth reply fuel
termination_by fuel => (depth, fuel + 1)

/-- Perform one step the follow machine asked for. -/
def steps (name : String) (argv : List String) (fault : Fault) (depth : Nat) (r : Command.Reply) :
    Nat → M (Expect × String)
  | 0 => pure (.refused "tooManySteps", "")
  | fuel + 1 => do
      let some b := r.bytes | return (.refused "noFrame", "")
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
          sawCall call
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
          match fault with
          | .dropReply =>
              let _ ← ask .submit call
              if (← get).sys.resendFresh then command name argv .none depth
              else match ← ask .lookup call with
                | none => pure (.refused "writerStopped", "")
                | some res => settle name call res; resume name argv fault depth k res fuel
          | .neverForward =>
              match ← ask .lookup call with
              | none => pure (.refused "writerStopped", "")
              | some res => settle name call res; resume name argv fault depth k res fuel
          | _ =>
              match ← ask .submit call with
              | none => pure (.refused "writerStopped", "")
              | some res => settle name call res; resume name argv fault depth k res fuel
termination_by fuel => (depth, fuel + 1)
end

/-! ## The operator's and the attempt store's acts -/

def nowNs : IO Nat := IO.monoNanosNow

/-- Stop the loop, open the Store cold (its base and the tail after it), start the loop on what it
opened to. The reopen's wall time is THE BAR's `reopen-ms`. -/
def restart : M Expect := do
  let st ← get
  match ← st.host.stop with
  | .error e => pure (.refused s!"writerFailed {e}")
  | .ok (.eof, _) =>
      let d ← st.mem.disk.get
      let base := (← st.mem.bases.get).file
      let t0 ← nowNs
      match Writer.reopen st.sys.writer base d.synced with
      | .error f => pure (.refused f)
      | .ok r =>
          let t1 ← nowNs
          st.mem.disk.set { synced := d.synced.extract 0 r.pos.offset }
          let h ← Writer.start st.sys.writer st.mem r
          modify fun st => { st with host := h, reopenNs := st.reopenNs ++ [t1 - t0] }
          pure .ok
  | .ok (exit, _) => pure (.refused s!"writer{exit.name}")

/-- Open a copy of the Store whose base file has the byte at `off` flipped. -/
def reopenFlipped (off : Nat) : M Expect := do
  let st ← get
  let d ← st.mem.disk.get
  let base := (← st.mem.bases.get).file
  match Writer.reopen st.sys.writer (Host.Sim.flipByte base off) d.synced with
  | .error f => pure (.refused f)
  | .ok _ => pure .ok

def retry (name : String) : M Expect := do
  match (← actor name).last with
  | none => pure (.refused "noAttempt")
  | some call =>
      match ← ask .lookup call with
      | none => pure (.refused "writerStopped")
      | some res => settle name call res; pure (statusOutcome res)

/-! ## A row -/

/-- Run one act once; its outcome and what it printed. -/
def runAct (l : Line) : M (Expect × String) := do
  match l.act with
  | .cmd argv =>
      match ← subst argv with
      | .error e => pure (.refused e, "")
      | .ok av => command l.actor av l.fault 4
  | .restart => pure (← restart, "")
  | .retry => pure (← retry l.actor, "")
  | .reopenFlipped off => pure (← reopenFlipped off, "")

/-- Run a line `times` times; the first outcome that is not the declared one, else the declared
one. A run past `withinMs` is `overTime`. -/
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
      | some ms => if o = l.expect ∧ dt > ms * 1000000 then .refused "overTime" else o
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

/-- Run a member row against a fresh deployment under `m`; `times` scales every repeated line. -/
def run (m : Option Mutation) (lines : List Line) (times : Option Nat) : IO Result := do
  let s := sys m
  let fs := founders.map fun n => (keyOf n 0, nextKeyDigest s.writer.X (keyOf n 1))
  let g := Receive.genesis s.writer.X Sim.worldName Sim.allowance fs
  let mem ← match ← Writer.genesisStore g with
    | .ok m => pure m
    | .error e => throw (IO.userError s!"genesis: {e}")
  let host ← Writer.start s.writer mem (Writer.genesisResident g)
  let go : M (List Expect) := lines.zipIdx.mapM fun (l, i) =>
    runLine i l (if l.times > 1 then times.getD l.times else l.times)
  let hex (d : D) := Text.toHex (s.writer.X.env.bytes d)
  let binds := founders.zipIdx.flatMap fun (n, i) =>
    [(n, hex (founderId s.writer.X Sim.worldName i)),
     (n ++ ".grant", hex (founderGrantId s.writer.X Sim.worldName i))]
  let (outcomes, st) ← go.run { sys := s, host, mem, genesis := g, binds }
  let _ ← st.host.stop
  pure ⟨{ outcomes, ops := st.ops, kinds := st.kinds }, st.log, st.times, st.reopenNs⟩

end Nanodregg.Protocol.Rows.Loopback
