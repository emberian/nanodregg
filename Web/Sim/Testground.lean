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
* `tg_lie NAME` — the writer tells one of the conformance rows' own lies from now on (`lies`): a
  writer plant runs `Host.serve` with the parameters `Loopback.sys` gives that mutation; a relay
  fault puts the rows' relay (`Loopback.pageFault`, `lookupLie`, `losesFirstReply`, `forwards`,
  `cancelLie`) between the members and the writer — in a hosted tab, around its socket (`tg_relay_pre`
  before it, `tg_relay_post` after: the same two halves the tab's own writer is wrapped in). `honest` ends it. `tg_lies` is the menu as JSON,
  each lie with the row that plants it and that row's expected outcome, read off `Protocol.rows`;
  `tg_lied` says whether the relay rewrote the last frame.
* `tg_cold I` — founder `I`'s follow starts again from the genesis World (the rows' `cold` lines).
* `tg_forge I ARGV SEED NEXT` — a hostile client's call (`Loopback.forgedCall`): ARGV planned on
  founder `I`'s World WITHOUT its follow's admission and signed with the seed it is handed; the page
  submits it like any call. `tg_text NAME` — a row's own package text (`Protocol.slot`, …).
* `tg_members I` — the members of founder `I`'s World as its own fold holds them (a hosted tab's roster).
* `tg_found INPUT I`, `tg_join INVITATION KEY`, `tg_self I MEMBER GRANT` — a HOSTED World (no
  writer in the tab; the page relays each member's writer frames to a real `host serve`): a founder's
  follow from the genesis inputs `host genesis` printed, a stranger's from an invitation accepted
  under the sponsor key the page trusts (`Invite.accept`), and its ids once a sponsor enrolled it.

It is a simulation in the README's sense (the real loop over an in-memory disk), so it is tooling:
no deployed module imports it (closure C9), and nothing a member trusts runs here.
-/
import Protocol.Rows.Writer
import Protocol.Rows.Deployed
import Protocol.Rows.Loopback
import Host.Follow
import Host.Cli
import Protocol.Attempt
import Protocol.Health
import Protocol.Command.Exit
import Lang.StdGen
import Lang.StdOffer

namespace Nanodregg.Web.Sim.Testground

open Nanodregg.Codec Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Host

abbrev D := Digest

/-- A lie the tab's writer tells: a conformance row's own plant, never a second implementation.
`writer m` runs the writer under the parameters `Loopback.sys` gives mutation `m`; `relay f` puts
the rows' relay fault `f` between every member and the writer. -/
inductive Lie
  | writer (m : Protocol.Mutation)
  | relay (f : Protocol.Fault)

/-- The menu: the lies whose rows catch them in a member's follow (the writer plants among them
leave every follower's `Ctx` the deployed one, `Loopback.sys`), and `neverForward`, the loss the
cancel lies need first. -/
def lies : List Lie :=
  [.relay (.flipEvent 0), .relay .dropLastEvent, .writer .forgesRefusal, .relay .lieLookup,
   .relay .lieCancel, .relay .forgeCancel, .relay .neverForward]

/-- A plant's word: its constructor's name, without arguments (`flipEvent 0` ↦ `flipEvent`). -/
def plantWord {α : Type} [Repr α] (a : α) : String :=
  let w := ((toString (repr a)).splitOn " ").head!
  ((w.splitOn ".").getLast!.replace "«" "").replace "»" ""

def Lie.word : Lie → String
  | .writer m => plantWord m
  | .relay f => plantWord f

/-- Where the rows plant a lie: the row, its line (counted from 0, as a row's `Plant.caught` counts) and the outcome the
row expects there, read off `Protocol.rows` (a writer plant: the row whose plant is that
mutation; a relay fault: the first line of any row that injects it). -/
def Lie.row : Lie → Option (String × Nat × String)
  | .writer m => Protocol.rows.findSome? fun r => match r.plant with
      | .caught m' n e => if plantWord m' = plantWord m then some (r.name, n, e.text) else none
      | _ => none
  | .relay f => Protocol.rows.findSome? fun r =>
      (r.lines.zipIdx.find? fun (l, _) => plantWord l.fault = plantWord f).map fun (l, i) =>
        (r.name, i, l.expect.text)

/-- The writer's parameters under a lie: `Loopback.sys`'s (no plant: the deployed rows parameters). -/
def writerOf : Option Lie → Rows.Writer.Params D
  | some (.writer m) => (Protocol.Rows.Loopback.sys Rows.Params.deployed (some m)).writer
  | _ => (Protocol.Rows.Loopback.sys Rows.Params.deployed none).writer

/-- The writer's parameters: the deployed rows parameters, no plant. -/
def P : Rows.Writer.Params D := writerOf none

/-- How a follow reads a base: the World codec and the writer's own base digest. -/
def base : Thin.Base (World D) :=
  ⟨P.R.world, World.steps, P.R.keys.worldDigest, Cadence.deployed.worldBytesMax⟩

/-- One founder's follow: who it serves and what it holds. -/
structure Member where
  self : Command.Self D
  follow : Command.Follow D
  /-- the steps this follow absorbed, each batch with the World it absorbed them onto (the last
  `seenMax` batches): what the page's Turn view re-derives a step from (`Web.Sim.Teach.tg_turn`) -/
  seen : Array (World D × List (Kernel.Step D)) := #[]

/-- The writer in the tab: its Store and its loop's state. -/
structure Writer where
  mem : Rows.Writer.Mem
  res : Resident (World D)

/-- The tab's World: the writer, when it runs in the tab, and every member's follow. A hosted World
(DESIGN-TESTGROUND §3.2) has no writer here: the page relays the members' writer frames to a real
`host serve`, and only the follows run in the tab. -/
structure Ground where
  writer : Option Writer
  members : Array Member
  conn : Nat := 0
  /-- the genesis World, where a cold follow starts -/
  genesis : World D
  /-- the lie the writer tells, `none` honest -/
  lie : Option Lie := none
  /-- the calls whose first reply the relay already lost (`losesFirstReply`: one per attempt) -/
  lost : Array ByteArray := #[]
  /-- the relay rewrote (or answered, or kept) the last frame -/
  lied : Bool := false

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

/-- The genesis World's head, as the rows bind it for a self-head seed (`Protocol.selfHeadSeed`'s
`{@chain0}` and `{@roots0}`, `Loopback`'s binds): `chain0 HEX`, `roots0 HEX`. -/
def head0Lines (g : World D) : List String :=
  [s!"chain0 {Text.toHex (P.X.env.bytes g.chain)}", s!"roots0 {Text.toHex (P.X.env.bytes (g.roots P.X.env))}"]

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
      ground.set (some { writer := some { mem, res }, members, genesis := g })
      let lines := Cli.genesisLines g nonce fs.length authority ++ head0Lines g
      return reply Protocol.Status.ok.code ("\n".intercalate lines ++ "\n").toUTF8

/-- One frame through the deployed loop: a port whose queue holds the frame, served until it is
empty (`Exit.eof`); the replies it sent. -/
def serveOne (g : Ground) (wr : Writer) (f : Frame) : IO (Ground × Array Reply) := do
  let P := writerOf g.lie
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
    P.R.keys.segment (Rows.Writer.checkpoint P wr.mem) (Rows.Writer.cadence P)
    (Sim.memStore wr.mem.disk none) (Rows.Writer.pager P wr.mem) port Rows.Writer.limits 2 wr.res
  return ({ g with writer := some { wr with res } }, ← sent.get)

/-- A lost reply, as the member's transport sees one: the connection closed, nothing said. -/
def lostReply : ByteArray := reply Protocol.Status.closed.code ByteArray.empty

/-- The relay's lie, if it tells one, and the op a frame names. -/
def faultOf (g : Ground) (op : UInt8) : Option (Protocol.Fault × Protocol.Op) :=
  match g.lie, Op.all.find? (·.code = op) with
  | some (.relay f), some o => some (f, o)
  | _, _ => none

/-- The relay BEFORE the writer: the answer it gives a frame itself (a cancel it answers on its own
word, `cancelLie`; a submit it never forwards, `forwards`), or `none`: the frame goes on to the writer. -/
def relayPre (g : Ground) (op : UInt8) : Option ByteArray := do
  let (f, o) ← faultOf g op
  match Protocol.Rows.Loopback.cancelLie (D := D) f o with
  | some r => some r
  | none => if o = .submit && !Protocol.Rows.Loopback.forwards f then some lostReply else none

/-- The relay AFTER the writer: the writer's reply `r` to a forwarded frame as the member receives
it (the first reply of a call lost, `losesFirstReply`; a page or a lookup rewritten, `pageFault`,
`lookupLie`), and the ground with the lost call remembered. -/
def relayPost (g : Ground) (op : UInt8) (payload r : ByteArray) : Ground × ByteArray :=
  match faultOf g op with
  | none => (g, r)
  | some (f, o) =>
    if o = .submit && Protocol.Rows.Loopback.losesFirstReply f && !g.lost.contains payload then
      ({ g with lost := g.lost.push payload }, lostReply)
    else if o = .log then (g, Protocol.Rows.Loopback.pageFault f r)
    else if o = .lookup then (g, Protocol.Rows.Loopback.lookupLie f r) else (g, r)

/-- The writer's answer to one frame, through the relay the lie puts in front of it: `relayPre`, the
tab's writer (`Host.serve`), `relayPost`. A hosted tab runs the same two halves around its socket. -/
def hostOf (op : UInt8) (payload : ByteArray) : IO ByteArray := do
  let some g ← ground.get | return refusedText "noWorld"
  let some wr := g.writer | return refusedText "noWriter"
  let g := { g with conn := g.conn + 1, lied := false }
  if let some r := relayPre g op then ground.set (some { g with lied := true }); return r
  let (g, rs) ← serveOne g wr ⟨UInt32.ofNat g.conn, op, payload⟩
  let r := match rs[0]? with
    | some r => reply r.status r.payload
    | none => refusedText "noReply"
  let (g, r') := relayPost g op payload r
  ground.set (some { g with lied := r' != r }); return r'

/-- A hosted tab's relay before its socket: `ok ‖ reply` when the relay answers the frame itself,
`ok` alone when the frame goes on to the writer. -/
@[export tg_relay_pre] def tgRelayPre (op : UInt8) : IO ByteArray := do
  let some g ← ground.get | return refusedText "noWorld"
  match relayPre g op with
  | some r => ground.set (some { g with lied := true }); return reply Protocol.Status.ok.code r
  | none => ground.set (some { g with lied := false }); return reply Protocol.Status.ok.code ByteArray.empty

/-- A hosted tab's relay after its socket: the writer's reply `R` as the member receives it. -/
@[export tg_relay_post] def tgRelayPost (op : UInt8) (payload r : ByteArray) : IO ByteArray := do
  let some g ← ground.get | return refusedText "noWorld"
  let (g, r') := relayPost g op payload r
  ground.set (some { g with lied := r' != r }); return r'

/-- How many absorbed batches a member keeps for the Turn view. -/
def seenMax : Nat := 64

def followOf (i : Nat) (op : UInt8) (payload : ByteArray) : IO ByteArray := do
  let some g ← ground.get | return refusedText "noWorld"
  let some m := g.members[i]? | return refusedText "noMember"
  let (fs', persist, status, p) :=
    Follow.answer P.X P.R.dc base m.self m.follow ⟨UInt32.ofNat g.conn, op, payload⟩
  let seen := match persist with
    | .steps ss@(_ :: _) =>
      let s := m.seen.push (m.follow.world, ss.map (·.1))
      if s.size > seenMax then s.extract (s.size - seenMax) s.size else s
    | _ => m.seen
  ground.set (some { g with conn := g.conn + 1, members := g.members.set! i { m with follow := fs', seen } })
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

/-! ## The lying writer, cold follows and a hostile client -/

def lieOf (name : String) : Option Lie := lies.find? (·.word = name)

/-- From now on the writer tells the lie `NAME` (`honest`: none); answers the name, or `refused
noLie`. A hosted tab has no writer of its own: a writer lie there is `refused noWriter`, and a relay
lie is told by the tab's relay around its socket (`tg_relay_pre`, `tg_relay_post`). -/
@[export tg_lie] def tgLie (name : ByteArray) : IO ByteArray := do
  let some g ← ground.get | return refusedText "noWorld"
  let n := (String.fromUTF8? name).getD ""
  if n = "honest" then ground.set (some { g with lie := none, lost := #[] }); return reply Protocol.Status.ok.code name
  match lieOf n with
  | some (.writer _) => if g.writer.isNone then return refusedText "noWriter" else
      ground.set (some { g with lie := lieOf n, lost := #[] }); return reply Protocol.Status.ok.code name
  | some l => ground.set (some { g with lie := some l, lost := #[] }); return reply Protocol.Status.ok.code name
  | none => return refusedText "noLie"

/-- Whether the relay rewrote, answered or kept the last frame sent to the writer. -/
@[export tg_lied] def tgLied (_ : Unit) : IO UInt8 := do
  pure (match ← ground.get with | some g => if g.lied then 1 else 0 | none => 0)

/-- The lies a MEMBER tells and the honest writer admits (a hostile client's `forge` line), by the
row that plants each: the row's first line after its first `forge` that does not end `ok` is where a
member's follow catches it. -/
def memberLies : List (String × String) := [("forkedPost", "selfHead")]

def memberLieRow (row : String) : Option (Nat × String) := do
  let r ← Protocol.rows.find? (·.name = row)
  let ls := r.lines.zipIdx
  let (_, f) ← ls.find? fun (l, _) => match l.act with | .forge _ => true | _ => false
  let (l, i) ← ls.find? fun (l, i) => i > f && l.expect ≠ .ok
  pure (i, l.expect.text)

/-- The whole menu: the writer's and the relay's lies, then the members'. -/
def menuJson : String := jarr (
  (lies.map fun l =>
    let kind := match l with | .writer _ => "writer" | .relay _ => "relay"
    jobj ([("name", jstr l.word), ("kind", jstr kind)] ++ match l.row with
      | some (r, n, e) => [("row", jstr r), ("line", toString n), ("expect", jstr e)]
      | none => [])) ++
  (memberLies.map fun (n, row) =>
    jobj ([("name", jstr n), ("kind", jstr "member")] ++ match memberLieRow row with
      | some (i, e) => [("row", jstr row), ("line", toString i), ("expect", jstr e)]
      | none => [])))

@[export tg_lies] def tgLies (_ : Unit) : String := menuJson

/-- Founder `I`'s follow starts again from the genesis World (a rows `cold` line). -/
@[export tg_cold] def tgCold (i : UInt32) : IO ByteArray := do
  let some g ← ground.get | return refusedText "noWorld"
  let some m := g.members[i.toNat]? | return refusedText "noMember"
  ground.set (some { g with members := g.members.set! i.toNat { m with follow := { world := g.genesis } } })
  return reply Protocol.Status.ok.code ByteArray.empty

/-- A hostile client's call (`Protocol.Rows.Loopback.forgedCall`): ARGV (`commandFrame` bytes) planned on
founder `I`'s follow World as it stands, without its follow's admission, signed with `SEED` (its
next key `NEXT`'s public key named); `ok ‖ call` for the page to submit, or `refused NAME`. -/
@[export tg_forge] def tgForge (i : UInt32) (argv seed next : ByteArray) : IO ByteArray := do
  let some g ← ground.get | return refusedText "noWorld"
  let some m := g.members[i.toNat]? | return refusedText "noMember"
  match commandFrame.decode argv with
  | .error _ => return refusedText "undecodableCommand"
  | .ok v =>
    match Protocol.Rows.Loopback.forgedCall P.X m.self m.follow.world (Ed25519.publicKey seed)
        (Ed25519.publicKey next) (Ed25519.sign seed) ((Text.unlist v.1.1).map fun b => (String.fromUTF8? b).getD "") with
    | .ok call => return reply Protocol.Status.ok.code call
    | .error r => return refusedText r

/-- A package's text as `install` reads it (`Lang.Print.package`, the printer the rows' `slot` uses). -/
def packageText (p : Lang.Package) : String := (Lang.Print.package p).getD ""

section Spin
open Nanodregg.Lang

/-- `go k` counts `k` down to 0, one step per tick-charged call: `fix` of the record `{go}`. -/
def spinGo : Term :=
  .get (.fix (.lam (.record [("go", .fn .nat .nat)]) (.record [("go", .lam .nat
    (.ite (.prim .eq (.var 0) (.nat 0)) (.nat 0) (.app (.get (.var 1) "go") (.prim .sub (.var 0) (.nat 1)))))]))) "go"

/-- The meter's demo package (KERNEL-68, DESIGN-OBS §1): one method `spin {n}` that counts `n` down
before it writes `n := 0`, so an invoke spends ticks in proportion to `n`; nothing else. A member
who spins near the signed budget sixteen times in one window has spent `Bounds.ticksPerWindow`, and
the next spin is the kernel's `ticksBudget`, naming the member. -/
def spinPackage : Package :=
  Std.pkgOf (.record [("n", .nat)]) []
    [("spin", .record [("n", .nat)], [], .lam (.record []) (.lam (.record [("n", .nat)]) (.lam (.record [("n", .nat)])
      (.lam reqTy (resultT (callsT []) (.record [("n", .app spinGo (.get (.var 1) "n"))]))))))]

end Spin

/-- A row's own texts by name: the package a scene installs and the seed it creates with, and the
journey's generators (§GN, `Lang.Std`): `boundedGenerator` (GN6–GN8: `generate {max}` installs a
record bounded at `max`) and `ownerGenerator` (GN9–GN11: `generate {}` installs a record only its
invoker may use); and the journey's offer (§LF), the tutorial's last step. -/
def texts : List (String × String) :=
  [("slot", Protocol.slot), ("selfHeadSeed", Protocol.selfHeadSeed),
   ("boundedGenerator", packageText (Lang.Std.boundedGenerator [("n", .nat)] "n")),
   ("ownerGenerator", packageText (Lang.Std.ownerGenerator [("n", .nat)])),
   ("spin", packageText spinPackage),
   -- the journey's offer (§LF, `Lang.Journey.Offer`): one term `price`, roles buyer and seller
   ("offer", match Lang.Std.offerPackage ["price"] ["buyer", "seller"] with
     | .ok p => packageText p
     | .error _ => "")]

@[export tg_text] def tgText (name : ByteArray) : ByteArray :=
  match texts.lookup ((String.fromUTF8? name).getD "") with
  | some t => reply Protocol.Status.ok.code t.toUTF8
  | none => refusedText "noText"

/-- The meter, read back from member `I`'s OWN fold as its HEALTH RECEIPT (DESIGN-OBS §1.5,
`Protocol.Health`): the receipt `nd receipt --health` prints, built from the member's follow's World,
written to its bytes, read back and CHECKED against that World's head (`Health.checkBytes`), so the page
shows what the receipt states and that it checks, never a number beside it. Lines: `ticks N`, `budget M`,
`refusals R`, `total T`, `height H`, `health HEX`, `checked ok` (or `checked NAME`). Nothing here asks the
writer. -/
@[export tg_meter] def tgMeter (i : UInt32) : IO ByteArray := do
  let some g ← ground.get | return refusedText "noWorld"
  let some m := g.members[i.toNat]? | return refusedText "noMember"
  let w := m.follow.world
  let E := P.X.env
  let some b := Health.bytes E P.R.dc (Health.build E w m.self.member) | return refusedText "badHealth"
  let (verdict, a) := match Health.checkBytes E P.R.dc (Head.headOf E w) m.self.member b with
    | .ok a => ("ok", a)
    | .error r => (r.name, Health.answerOf E w m.self.member)
  return reply Protocol.Status.ok.code
    (s!"ticks {a.ticks}\nbudget {Bounds.ticksPerWindow}\nrefusals {a.refusals}\ntotal {a.total}\n" ++
      s!"height {w.height}\nhealth {Text.toHex b}\nchecked {verdict}\n").toUTF8

/-! ## A hosted World: the follows in the tab, the writer elsewhere -/

/-- A member of a hosted World whose follow starts at `w` (no writer in the tab); `g` the tab's
ground when it is already this World's and holds no writer, else a new one. Answers its index. -/
def addMember (self : Command.Self D) (w : World D) : IO Nat := do
  let m : Member := { self, follow := { world := w } }
  match ← ground.get with
  | some g =>
    if g.writer.isNone && g.genesis.origin = w.origin then
      ground.set (some { g with members := g.members.push m }); return g.members.size
    else ground.set (some { writer := none, members := #[m], genesis := w }); return 0
  | none => ground.set (some { writer := none, members := #[m], genesis := w }); return 0

def hexOf (d : D) : String := Text.toHex (P.X.env.bytes d)

/-- The members of founder `I`'s World, read off its OWN fold: every live cell of kind `kindMember`
(`Receive.kindMember`), in trie order, one `member HEX` line each, then `height H`, then
`enrollLeft N` when the member's own grant carries an enrolment right (`Receive.enrollLeft`: the
count its next `enroll` would spend from). A hosted tab's roster is this: what its follow re-derived
from the log, not a list the writer or the guest-book keeps; a member the writer never logged is not
in it, and one it logged cannot be left out. The guest-book reads its own `enrollLeft` to keep a
floor for members who come back. -/
@[export tg_members] def tgMembers (i : UInt32) : IO ByteArray := do
  let some g ← ground.get | return refusedText "noWorld"
  let some m := g.members[i.toNat]? | return refusedText "noMember"
  let w := m.follow.world
  let ids := w.cellIds.filter fun c => (w.live P.X.env c).any (·.kind == kindMember)
  let lines := ids.foldl (fun acc c => acc ++ s!"member {hexOf c}\n") ""
  let left := match w.live P.X.env m.self.grant with
    | some cell => match enrollLeft m.self.grant cell with
      | .ok (_, n) => s!"enrollLeft {n}\n"
      | .error _ => ""
    | none => ""
  return reply Protocol.Status.ok.code s!"{lines}height {w.height}\n{left}".toUTF8

/-- A founder of a hosted World: its follow starts at the genesis its INPUT makes (the `input HEX`
`host genesis` prints, as a founder's own follow Store reproduces it, RUNBOOK §2b's residual), its
ids founder `I`'s. Answers `index N`, `origin`, `member`, `grant`, or `refused NAME`. -/
@[export tg_found] def tgFound (input : ByteArray) (i : UInt32) : IO ByteArray := do
  let some st := Invite.startOf P.X input | return refusedText "badInput"
  match Invite.startGenesis P.X st with
  | .error r => return refusedText r.name
  | .ok w =>
    let self : Command.Self D :=
      { world := w.origin, member := founderId P.X w.origin i.toNat,
        grant := founderGrantId P.X w.origin i.toNat, window := Follow.window }
    let n ← addMember self w
    return reply Protocol.Status.ok.code
      s!"index {n}\norigin {hexOf w.origin}\nmember {hexOf self.member}\ngrant {hexOf self.grant}\n".toUTF8

/-- A stranger joins a hosted World over an invitation (`Invite.accept`, PROTOCOL-42): its follow
starts at the World the invitation's signed inputs make, checked under the sponsor `KEY` the page
trusts, never the writer's World handed over. Its ids are placeholders until a sponsor enrolls it
(`tg_self`), as the rows' strangers' are. Answers `index`, `origin`, `sponsor`, or `refused NAME`. -/
@[export tg_join] def tgJoin (invitation key : ByteArray) : IO ByteArray := do
  match Invite.accept P.X key invitation with
  | .error r => return refusedText r.name
  | .ok (inv, w) =>
    let self : Command.Self D :=
      { world := w.origin, member := P.X.env.hash "nanodregg/testground/stranger/v1" key,
        grant := P.X.env.hash "nanodregg/testground/stranger-grant/v1" key, window := Follow.window }
    let n ← addMember self w
    return reply Protocol.Status.ok.code
      s!"index {n}\norigin {hexOf w.origin}\nsponsor {hexOf inv.sponsor}\n".toUTF8

/-- Member `I`'s ids once its sponsor enrolled it: `MEMBER` and `GRANT` as `enroll` and `grant world`
printed them (hex). -/
@[export tg_self] def tgSelf (i : UInt32) (member grant : ByteArray) : IO ByteArray := do
  let some g ← ground.get | return refusedText "noWorld"
  let some m := g.members[i.toNat]? | return refusedText "noMember"
  let dig (b : ByteArray) := (String.fromUTF8? b) >>= Text.ofHex >>= P.X.digestOf
  match dig member, dig grant with
  | some mm, some gg =>
    ground.set (some { g with members := g.members.set! i.toNat { m with self := { m.self with member := mm, grant := gg } } })
    return reply Protocol.Status.ok.code ByteArray.empty
  | _, _ => return refusedText "badId"

end Nanodregg.Web.Sim.Testground
