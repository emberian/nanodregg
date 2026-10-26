/-
# Web.Sim.Testground — a World in a browser tab: the writer and each member's follow, in process

The testground's kernel is the conformance rows' system (`Protocol.Rows.Writer`, `Host.Follow.answer`)
at the DEPLOYED parameters (`Protocol.Rows.Params.deployed`: the 32-byte digest, cSHAKE256, Ed25519,
KMAC256 Store tags), compiled to WebAssembly. A page is the client: it plays `nd`, the supervisor and
custody, exactly the parts `Protocol.Rows.Loopback` plays in process, and moves bytes only. Every
accept, refuse, plan, render and attempt decision is one of these exports' Lean:

* `tg_genesis ARGV` — `commandFrame` bytes of `[name, nonce, key₀, next₀, key₁, next₁, …]` (raw
  Ed25519 public keys): `Receive.genesis` at the deployed `Ctx`, a Store as `Host.Sim.memGenesis`
  leaves it, and one follow per founder whose World is that genesis; answers `host genesis`'s lines
  (`Host.Cli.genesisLines`), or `refused NAME`.
* `tg_host OP PAYLOAD` — one frame to the writer: `Host.serve`, the deployed loop (group commit, the
  seal cadence, whole-World bases), over the in-memory disk, run until its port is empty; answers
  `status ‖ payload` exactly as host.sock does.
* `tg_follow I OP PAYLOAD` — one frame to founder `I`'s `host follow` (`Host.Follow.answer`, the
  deployed per-frame decision); what follow would persist is held in memory, as the rows hold it.
* `tg_pub SEED`, `tg_sign SEED MSG` — custody's Ed25519 (CODEC's, RFC 8032), the page's custody
  calling it with seeds the page holds; follow never sees a seed.
* `tg_attempt SENDS_LEFT REQUEST SEEN` — `Protocol.Attempt.next`, the attempt store's decision.
* `tg_table` — the protocol table the page's codec reads (ops, statuses, step tags, layouts), from
  `Protocol.Table`: one source, never a hand-written copy.

It is a simulation in the README's sense (the real loop over an in-memory disk), so it is tooling:
no deployed module imports it (closure C9), and nothing a member trusts runs here.
-/
import Protocol.Rows.Writer
import Protocol.Rows.Deployed
import Host.Follow
import Host.Cli
import Protocol.Attempt
import Protocol.Command.Exit

namespace Nanodregg.Web.Sim.Testground

open Nanodregg.Codec Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Host

abbrev D := Digest

/-- The writer's parameters: the deployed rows parameters, no plant. -/
def P : Rows.Writer.Params D := { R := Rows.Params.deployed, X := Rows.Params.deployed.ctx }

/-- How a follow reads a base: the World codec and the writer's own base digest. -/
def base : Thin.Base (World D) :=
  ⟨P.R.world, World.steps, P.R.keys.worldDigest, Cadence.deployed.worldBytesMax⟩

/-- One founder's follow: who it serves and what it holds. -/
structure Member where
  self : Command.Self D
  follow : Command.Follow D

/-- The tab's World: the writer's Store and loop state, and every founder's follow. -/
structure Ground where
  mem : Rows.Writer.Mem
  res : Resident (World D)
  members : Array Member
  conn : Nat := 0

initialize ground : IO.Ref (Option Ground) ← IO.mkRef none

/-- `status ‖ payload`, as host.sock and follow.sock answer. -/
def reply (status : UInt8) (payload : ByteArray) : ByteArray := ByteArray.mk #[status] ++ payload

def refusedText (name : String) : ByteArray := reply Protocol.Status.refused.code name.toUTF8

/-- The tab's World has one writer and no certifiers (`Authority.none`): its heads are uncertified,
as every Store's is until the signing seed lands (TRUST T3). -/
def authority : Authority := Authority.none

/-- The founders of an argv: `(key, next)` pairs, the next committed as `nextKeyDigest`. -/
def foundersOf : List ByteArray → Option (List (ByteArray × D))
  | [] => some []
  | k :: n :: rest => (foundersOf rest).map ((k, nextKeyDigest P.X n) :: ·)
  | [_] => none

def genesisOf (argv : List ByteArray) : IO ByteArray := do
  let name :: nonce :: keys := argv | return refusedText "usage"
  let some fs := foundersOf keys | return refusedText "usage"
  match genesis P.X name nonce Rows.Params.allowance fs authority with
  | .error r => return refusedText r.name
  | .ok g =>
    match ← Rows.Writer.genesisStore P g with
    | .error e => return refusedText e
    | .ok (mem, res) =>
      let members := (List.range fs.length).toArray.map fun i =>
        { self := { world := g.origin, member := founderId P.X g.origin i,
                    grant := founderGrantId P.X g.origin i, window := Follow.window }
          follow := { world := g } : Member }
      ground.set (some { mem, res, members })
      let lines := Cli.genesisLines g nonce fs.length authority
      return reply Protocol.Status.ok.code ("\n".intercalate lines ++ "\n").toUTF8

/-- One frame through the deployed loop: a port whose queue holds the frame, served until it is
empty (`Exit.eof`); the replies it sent. -/
def serveOne (g : Ground) (f : Frame) : IO (Ground × Array Reply) := do
  let queue ← IO.mkRef #[f]
  let sent ← IO.mkRef (#[] : Array Reply)
  let back ← IO.mkRef (none : Option Frame)
  let pop : IO (Option Frame) := do
    match ← back.swap none with
    | some f => pure (some f)
    | none =>
      let q ← queue.get
      if h : 0 < q.size then queue.set (q.extract 1 q.size); pure (some q[0]) else pure none
  let port : Port :=
    { recv := pop, poll := pop, unread := fun f => back.set (some f)
      send := fun r => sent.modify (·.push r), close := pure () }
  let (_, res) ← serve (Rows.Writer.machine P) ⟨fun _ ts => Record.encode P.R.dc ts, Rows.Writer.mark P⟩
    P.R.keys.segment (Rows.Writer.checkpoint P g.mem) (Rows.Writer.cadence P)
    (Sim.memStore g.mem.disk none) (Rows.Writer.pager P g.mem) port Rows.Writer.limits 2 g.res
  return ({ g with res }, ← sent.get)

def hostOf (op : UInt8) (payload : ByteArray) : IO ByteArray := do
  let some g ← ground.get | return refusedText "noWorld"
  let (g, rs) ← serveOne { g with conn := g.conn + 1 } ⟨UInt32.ofNat g.conn, op, payload⟩
  ground.set (some g)
  match rs[0]? with
  | some r => return reply r.status r.payload
  | none => return refusedText "noReply"

def followOf (i : Nat) (op : UInt8) (payload : ByteArray) : IO ByteArray := do
  let some g ← ground.get | return refusedText "noWorld"
  let some m := g.members[i]? | return refusedText "noMember"
  let (fs', _, status, p) :=
    Follow.answer P.X P.R.dc base m.self m.follow ⟨UInt32.ofNat g.conn, op, payload⟩
  ground.set (some { g with conn := g.conn + 1, members := g.members.set! i { m with follow := fs' } })
  return reply status p

@[export tg_genesis] def tgGenesis (argv : ByteArray) : IO ByteArray :=
  match commandFrame.decode argv with
  | .ok v => genesisOf (Text.unlist v.1.1)
  | .error _ => pure (refusedText "undecodableCommand")

@[export tg_host] def tgHost (op : UInt8) (payload : ByteArray) : IO ByteArray := hostOf op payload

@[export tg_follow] def tgFollow (i : UInt32) (op : UInt8) (payload : ByteArray) : IO ByteArray :=
  followOf i.toNat op payload

@[export tg_pub] def tgPub (seed : ByteArray) : ByteArray := Ed25519.publicKey seed

@[export tg_sign] def tgSign (seed msg : ByteArray) : ByteArray := Ed25519.sign seed msg

/-! ## The table the page reads (one source: `Protocol.Table`, read off its `all` lists) -/

/-- A constructor's own word (`Step.signNext` ↦ `signNext`), as `Emit.Rust.ctorName` reads it. -/
def word {α : Type} [Repr α] (a : α) : String :=
  let w := ((toString (repr a)).splitOn ".").getLast!
  (w.replace "«" "").replace "»" ""

def jstr (s : String) : String := "\"" ++ s ++ "\""
def jarr (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"
def jobj (kvs : List (String × String)) : String :=
  "{" ++ ",".intercalate (kvs.map fun (k, v) => jstr k ++ ":" ++ v) ++ "}"

def jfield : Codec.Field → String
  | .byte n => jobj [("kind", jstr "byte"), ("name", jstr n)]
  | .u64 n => jobj [("kind", jstr "u64"), ("name", jstr n)]
  | .bytes n => jobj [("kind", jstr "bytes"), ("name", jstr n)]
  | .list n => jobj [("kind", jstr "list"), ("name", jstr n)]
  | .oneOf n cs => jobj [("kind", jstr "oneOf"), ("name", jstr n),
      ("cases", jarr (cs.map fun (c, b) => jobj [("name", jstr c), ("code", toString b.toNat)]))]
  | .u32 n => jobj [("kind", jstr "u32"), ("name", jstr n)]
  | .path n => jobj [("kind", jstr "path"), ("name", jstr n)]
  | .paths n => jobj [("kind", jstr "paths"), ("name", jstr n)]

def jlayout (l : Codec.Layout) : String := jarr (l.map jfield)

def jcodes {α : Type} [Repr α] (xs : List α) (code : α → Nat) : String :=
  jarr (xs.map fun a => jobj [("name", jstr (word a)), ("code", toString (code a))])

/-- The protocol table as JSON: ops, statuses, step tags with their layouts, the follow socket's
layouts, custody's refusals, the command exits, the attempt store's words and the bounds. -/
def table : String := jobj [
  ("ops", jarr (Op.all.map fun o => jobj [("name", jstr o.name), ("code", toString o.code.toNat)])),
  ("relayable", jarr (Op.relayable.map fun o => jstr o.name)),
  ("statuses", jcodes Protocol.Status.all (·.code.toNat)),
  ("steps", jarr (Step.all.map fun st => jobj [("name", jstr (word st)), ("code", toString st.code.toNat),
      ("layout", jlayout st.layout)])),
  ("command", jlayout commandLayout), ("resume", jlayout resumeLayout),
  ("signResult", jlayout signResultLayout), ("precommitResult", jlayout precommitResultLayout),
  ("custodyRefused", jlayout custodyRefusalLayout),
  ("custodyRefusals", jarr (CustodyRefusal.all.map fun r => jobj [("name", jstr r.name), ("code", toString r.code.toNat)])),
  ("commandExits", jcodes CommandExit.all CommandExit.code),
  ("attemptRequests", jarr (Attempt.Request.all.map fun r => jstr (word r))),
  ("attemptSeen", jarr (Attempt.Seen.all.map fun s => jstr s.name)),
  ("receiptWords", jarr ([Attempt.receiptWord, Attempt.headWord, Attempt.settleWord].map jstr)),
  ("settleSeen", jarr (Attempt.settleWords.filterMap fun w => (Attempt.settleSeen w).map fun s =>
      jarr [jstr w, jstr s.name])),
  ("attemptActions", jarr (Attempt.Action.all.map fun a => jobj [("name", jstr a.name), ("code", toString a.code.toNat)])),
  ("bounds", jobj [("frameBytesMax", toString Bounds.frameBytesMax), ("argvBytesMax", toString Bounds.argvBytesMax),
      ("stepsPerCommandMax", toString Bounds.stepsPerCommandMax), ("sendsMax", toString Bounds.sendsMax)])]

@[export tg_table] def tgTable (_ : Unit) : String := table

/-- `Protocol.Attempt.next`: `sendsLeft` (0/1), the last request and what its reply said as
indices of `Request.all` and `Seen.all` (`255`: nothing sent yet); the action's `code`, `badReply` for an index past the lists. -/
@[export tg_attempt] def tgAttempt (sendsLeft req seen : UInt8) : UInt8 :=
  if req = 255 then (Attempt.next (sendsLeft = 1) none).code else
    match Attempt.Request.all[req.toNat]?, Attempt.Seen.all[seen.toNat]? with
    | some r, some s => (Attempt.next (sendsLeft = 1) (some (r, s))).code
    | _, _ => Attempt.Action.badReply.code

end Nanodregg.Web.Sim.Testground
