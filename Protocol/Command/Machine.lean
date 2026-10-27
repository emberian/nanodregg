/-
# Protocol.Command.Machine — what `host follow` does with a member's argv

`start` parses the argv and answers the first step; `step` takes the continuation `k` and the
result of the step it asked for and answers the next one, with follow's World after absorbing
any log the result carried. A write runs

  sign(envelope) → host(log, envelope) → [absorb: every logged step re-derived, PROTOCOL-4]
  → (page again, from the page's step count, until it is the writer's tip)
  → plan on the caught-up World → sign(callMessage u) → submit(call) → done

and a `read` stops after the catch-up; `init` needs no World (sign twice, print a join token).
The first envelope is valid for follow's own height + window, every later one for the tip the last
page stated + window. A member more than a window behind is refused `expired` with the writer's
height and re-signs ONCE a command for that height + window (`reSign`, PROTOCOL-19); a thin member's
`adopt` envelopes do the same, first for one window from height 0 (a pin names a step count).

`rotate` asks custody to `precommit` after the catch-up, plans the rotation to custody's NEXT key
(precommitting the digest of its PENDING key) and has it signed by `signNext`; custody advances on
its own settlement of the submit (CLIENT-13).

`invite INPUT` (PROTOCOL-42) catches up, checks that INPUT makes the member's own World, pins the
writer's newest base as follow verified it itself (PROTOCOL-47, `pinOf`: follow's own World at the
base's step count, the digest of its bytes; `noBase` / `baseMismatch` otherwise) and has custody
sign the invitation; it prints `invite HEX`.

`adopt INVITE KEY` (thin consent, PROTOCOL-14 A) takes its pin from an invitation `Invite.accept`
accepts under the sponsor key KEY, and pages the writer's newest base with `read`, one
signed envelope per page, `Protocol.Thin.accept` deciding each page; the download so far lives in
follow's state (`Follow.download`, memory only), and an adopted base replaces follow's World and is
handed back as `Persist.adopt` for follow to seal as its own newest base. From there every command
catches up from the base's step count like any other.

The log is a list of STEPS (KERNEL-47): admitted Turns and recorded refusals. Log positions count
steps, and follow binds on (steps, chain), as the kernel's `fold_reaches_host` does. Envelope windows
stay in heights: the page states the writer's tip in both units (PROTOCOL-41).

`sync --to STEPS:CHAIN` / `--attest` / `--check ATTEST` (PROTOCOL-74, `Protocol.Head`): the catch-up
compares follow's own fold with another member's stated position as it passes it (`Head.anchorCheck`
on each page's steps, re-derived from the argv at every step like every plan: `syncAnchor`), and
refuses `forkedWorld STEPS` by name when the chain there is another; `--attest` has custody sign
follow's own head at the tip (`attestTip`: the message is `Head.message` of follow's OWN World,
never a result's) and prints `attest HEX`; `--check` verifies the attestation's signature and World
before anything is sent and its signer's current key at the tip (`Head.signer`).

`cancel CALL` (PROTOCOL-63) catches up, checks on follow's World that the cancel records there, has
custody sign it and relays it; the writer's final answer (`refused cancelled`, or `ok`: the call was
admitted) is its word, so follow catches up AGAIN and ends by its own settlement of the call
(`cancelSettled`, PROTOCOL-71): `cancelled TXID` only when its own World records the cancel.

`k` holds only the argv, the phase and the results so far; every plan is RE-DERIVED from follow's
World at each step and the bytes it signs are compared with the ones custody signed (`planMoved`),
so a resumed call must match that re-derived plan (HOST-9's `resume_rederives`).
This does not authenticate the argv itself: adoption still requires the trusted sponsor-key
premise `Spec.keyFaithful`. A plan is offered for signature
only if follow's own World admits the Turn it derives (consent: `Protocol.Proofs.Command`).
-/
import Kernel.Receive.Rederive
import Protocol.Command.Verb
import Protocol.Envelope
import Protocol.Invite
import Protocol.Head
import Protocol.Command.Describe
import Protocol.Receipt
import Protocol.Settle
import Protocol.Attempt
import Protocol.Command.Exit
import Lang.Program

namespace Nanodregg.Protocol.Command

open Nanodregg.Codec Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- What one `host follow` knows about the member it serves. -/
structure Self (D : Type) where
  /-- the World this member was invited to (its genesis origin, KERNEL-24), from the member's own
  side — its own Store's genesis, built from the invitation — never from the Host it talks to.
  Every call and envelope it signs names it. -/
  world : D
  member : D
  /-- the member's World grant (observe; enroll, if it carries it), which its envelopes name and
  its enrolments spend (KERNEL-16) -/
  grant : D
  /-- how many heights a signed call or envelope stays valid -/
  window : Nat

/-- Why a command ends without its effect. -/
inductive Refusal (D : Type)
  | parse (r : ParseRefusal)
  /-- follow's own derivation refused the call -/
  | receive (r : Receive.Refusal D)
  /-- follow's own World rejects the derived Turn -/
  | reject (r : Reject D)
  /-- the Host refused, by its name -/
  | host (name : String)
  /-- the logged step at this log position does not re-derive on follow's World: an event that does
  not read (`eventOf`), or one `Receive.rederive` refuses `eventMismatch` (a call that does not
  decode, a Turn event that does not derive, a refusal event that `Receive.judge` does not record)
  (a kernel rejection of a derived Turn is refused by the kernel's own name, `reject`; a well-formed
  cancel event that `Receive.cancel` does not record by `receive cancelForged`: `ofVerdict`) -/
  | eventMismatch (step : Nat)
  | badState
  | badResult
  /-- follow's World moved between the plan custody signed and the submit -/
  | planMoved
  /-- read: a `KEY=VALUE` that does not hold -/
  | expect (key : Nat)
  | missingCell (cell : D)
  /-- the writer's stated step count and chain after a log page are not what follow's fold reached -/
  | chainMismatch (steps : Nat)
  /-- a log page carried more steps than `Bounds.pageStepsMax`, more than one follower record holds
  (HOST-41): refused before any of it is absorbed -/
  | pageTooLong (count : Nat)
  /-- the derivation asked for more cells than `Kernel.Bounds.touchesMax` -/
  | tooManyPins
  /-- a base download refused, by `Protocol.Thin`'s name -/
  | thin (r : Thin.Refusal)
  /-- custody refused the step, by its name (`CustodyRefusal`) -/
  | custody (r : CustodyRefusal)
  /-- `read OBJ ?`: some part of the object's description has no text (`Lang.Print`) -/
  | noText
  /-- an invitation refused by `Invite.accept`'s name, or one for another World (PROTOCOL-42) -/
  | invite (r : Invite.Refusal)
  /-- the writer refused the envelope `expired` at `height` after follow's one re-signed envelope
  of this command, or stated a height that a re-signed envelope would not cover (PROTOCOL-19) -/
  | expired (height : Nat)
  /-- a call's bytes that do not read back as the call: `receipt CALL` whose bytes do not decode as
  a signed call, or step 3's signed call whose canonical bytes do not decode to itself (the World
  would judge the call they decode to, not the one follow derived) -/
  | badCall
  /-- `read OBJ REL K`: the object's package declares no relation REL (a data object declares none) -/
  | unknownRelation (rel : String)
  /-- `read OBJ REL K`: K is past the relation's declared `limit` (PROTOCOL-51) -/
  | rangePastLimit (most : Nat)
  /-- `read OBJ REL K PREFIX`: PREFIX reads at none of the relation's prefix types -/
  | badPrefix
  /-- `invoke … --pin REL KEY`: KEY does not read at the relation's key type (CLIENT-35) -/
  | badKey
  /-- `sync --to` / `--check`: follow's own fold reached the anchor's step count with ANOTHER chain
  (`Head.anchorCheck`): this member and the member whose head that is hold two histories of one
  World (PROTOCOL-74; `Proofs.Head.forked_not_on_fold`). The page is refused and nothing of it
  kept, as a `chainMismatch` page is -/
  | forkedWorld (steps : Nat)
  /-- `sync --to` / `--check`: follow was already past the position when the command began. Its
  World holds only the current chain, so the comparison on the way cannot be made: the member
  BEHIND does it, or `host check STORE --anchor` on this member's own Store (PROTOCOL-74) -/
  | ahead (steps : Nat)
  /-- a page carried a member's post of ITS head of this World (`Std.head` with `world` this World's
  origin, `Head.selfPosts`) at a position follow's own fold reached on this page with ANOTHER chain
  (PROTOCOL-75; `Proofs.Head.forkedSelfPost_forked`). The page is KEPT (it is lawful on follow's
  fold), the command ends by name, and the post is the witness: its poster signed that head
  (`Proofs.Head.body_post`) -/
  | forkedPost (steps : Nat) (member : Option D)
  /-- `sync --check`: the attestation refused by `Protocol.Head`'s name -/
  | attest (r : Head.Refusal)
  /-- `adopt`: under an authority that names certifiers, the base the pin bound is not certified by
  the writer's certificate the page carried, by `Protocol.Head`'s name (`Head.certifiesWorld`,
  PROTOCOL-77.1); the download is dropped and nothing adopted -/
  | certified (r : Head.CertRefusal)

/-- A step answered to the client. -/
inductive Reply
  | done (exit : UInt8) (out err : ByteArray)
  | sign (message k : ByteArray)
  | host (op : Op) (payload k : ByteArray)
  | submit (call k : ByteArray)
  | precommit (k : ByteArray)
  | signNext (message k : ByteArray)
  | signIncoming (message k : ByteArray)
  deriving Inhabited

/-- The continuation a reply carries, if any. -/
def Reply.cont : Reply → Option ByteArray
  | .done .. => none
  | .sign _ k | .host _ _ k | .submit _ k | .precommit k | .signNext _ k | .signIncoming _ k => some k

variable {D : Type} [Ord D] [DecidableEq D]

/-- The refusal's name on the wire (law 7): the constructor, arguments dropped. PROTOCOL's own
constructors are named here; a receive refusal or a kernel rejection carries its owner's name
(`Receive.Refusal.name`, `Reject.name`, each with `name_injective`), and a parse refusal the
parser's. -/
def Refusal.name : Refusal D → String
  | .parse r => r.name
  | .receive r => r.name
  | .reject r => r.name
  | .host n => n
  | .eventMismatch _ => "eventMismatch"
  | .badState => "badState"
  | .badResult => "badResult"
  | .planMoved => "planMoved"
  | .expect _ => "expect"
  | .missingCell _ => "missingCell"
  | .tooManyPins => "tooManyPins"
  | .chainMismatch _ => "chainMismatch"
  | .pageTooLong _ => "pageTooLong"
  | .thin r => r.name
  | .custody r => r.name
  | .invite r => r.name
  | .noText => "noText"
  | .expired _ => "expired"
  | .badCall => "badCall"
  | .unknownRelation _ => "unknownRelation"
  | .rangePastLimit _ => "rangePastLimit"
  | .badPrefix => "badPrefix"
  | .badKey => "badKey"
  | .forkedWorld _ => "forkedWorld"
  | .ahead _ => "ahead"
  | .forkedPost .. => "forkedPost"
  | .attest r => r.name
  | .certified r => r.name

def refused (r : Refusal D) : Reply :=
  .done CommandExit.refused.code.toUInt8 ByteArray.empty s!"refused {r.name}\n".toUTF8
def printed (out : String) : Reply := .done CommandExit.ok.code.toUInt8 out.toUTF8 ByteArray.empty
/-- The catch-up read `Bounds.pagesPerCommandMax` pages and follow is still at log position
`steps`, the writer at `tip` steps: what was absorbed is kept, and the member runs the command
again. Not a refusal: its own end (`CommandExit.behind`, restart class), so a timer runs it again
(PROTOCOL-38). -/
def behind (steps tip : Nat) : Reply :=
  .done CommandExit.behind.code.toUInt8 ByteArray.empty s!"behind {steps} {tip}\n".toUTF8
/-- The writer refused the call by name and did NOT record it, so it is not final (PROTOCOL-41,
`Status.declined`): the attempt stays open. Printed `declined NAME`. -/
def declined (name : String) : Reply :=
  .done CommandExit.declined.code.toUInt8 ByteArray.empty s!"declined {name}\n".toUTF8
/-- The writer refused a page `pageIo` (HOST-48): its IO failed on that page and it serves on. "Not
now", never "never": the command ends restart-class (`CommandExit.pageIo`), what was absorbed is
kept, and the member runs it again. Printed `pageIo`. -/
def notServed : Reply :=
  .done CommandExit.pageIo.code.toUInt8 ByteArray.empty s!"{pageIoName}\n".toUTF8

/-! ## Follow's state -/

/-- What `host follow` holds between frames: its World, a base download in progress (thin
consent), and the newest writer base follow verified ITSELF (PROTOCOL-47): the step count a log
page stated as the writer's newest base, and the digest of follow's OWN World at that step count
(`Thin.Base.digest` over `Thin.Base.world`, the one digest the Host seals and a pin names). The
last two are memory only, never persisted: a restarted follow starts the download again, and has
verified no base until its fold next sits at the writer's stated base. -/
structure Follow (D : Type) [Ord D] where
  world : World D
  download : Option Thin.Download := none
  verified : Option (Nat × ByteArray) := none

/-- The part of `Follow` that lives in memory beside follow's Store (`Host.Follow.loop`'s ref). -/
structure Memory where
  download : Option Thin.Download := none
  verified : Option (Nat × ByteArray) := none

def Follow.memory {D : Type} [Ord D] (f : Follow D) : Memory := ⟨f.download, f.verified⟩

/-- What a step asks follow to make durable before it answers: the steps it absorbed (re-derived,
in log order; `[]` for most steps), or a base it adopted, which follow seals as its own newest base. -/
inductive Persist (D : Type) [Ord D]
  /-- the steps follow took (admitted Turns, recorded refusals), each with the roots digest of
  follow's World after it (`World.roots`: HOST-29, KERNEL-47), the shape of a batch record -/
  | steps (ss : List (Kernel.Step D × D))
  | adopt (w : World D)

/-! ## The continuation -/

def stateLayout : Layout := [.list "argv", .byte "phase", .list "acc"]

def stateFrame : Stream (Layout.Ty Bounds.frameBytesMax stateLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) stateLayout

structure State where
  argv : List ByteArray
  phase : UInt8
  acc : List ByteArray

def State.bytes (s : State) : Option ByteArray := do
  pure (stateFrame.bytes (← Text.fitList _ s.argv, s.phase, ← Text.fitList _ s.acc, ()))

def State.ofBytes (b : ByteArray) : Option State :=
  match stateFrame.decode b with
  | .ok (a, p, c, ()) => some { argv := Text.unlist a, phase := p, acc := Text.unlist c }
  | .error _ => none

/-- The `tried` field of an envelope-phase state (1: `[start, pages, upTo, tried]`, 2: `[start,
signed, pages, upTo, tried]`), as `step` reads it: bit 0 the one `expired` re-sign, bit 1 the
incoming key (`expiredBit`, `incomingBit`). -/
def State.tried (s : State) : Option Nat :=
  match s.phase, s.acc with
  | 1, [_, _, _, t] => Text.ofU64 t
  | 2, [_, _, _, _, t] => Text.ofU64 t
  | _, _ => none

/-- A step carrying the next state, or `badState` if the state does not fit a frame. -/
def next (s : State) (f : ByteArray → Reply) : Reply :=
  match s.bytes with
  | some k => f k
  | none => refused (D := D) .badState

/-! ## Custody's answer -/

structure Signed where
  key : ByteArray
  next : ByteArray
  signature : ByteArray

def Signed.ofBytes (b : ByteArray) : Option Signed :=
  match signResultFrame.decode b with
  | .ok (k, n, s, ()) => some ⟨k.1, n.1, s.1⟩
  | .error _ => none

def Signed.bytes (s : Signed) : Option ByteArray := do
  let f := Text.fit Bounds.frameBytesMax
  pure (signResultFrame.bytes (← f s.key, ← f s.next, ← f s.signature, ()))

/-- A reply as `u8 status ‖ payload`, the shape of every step result. -/
def hostReply (b : ByteArray) : Option (Status × ByteArray) :=
  if h : 0 < b.size then (Status.ofCode? b[0]).map (·, b.extract 1 b.size) else none

/-- The phases whose result is custody's: 1 (an envelope's or init's signature, by `sign` or
`signIncoming`), 2 for `init`
only (its possession signature; every other verb's phase 2 is a `log` reply), 3 (a call's
signature, by `sign` or `signNext`), 5 (`precommit`), 6 (an adopt envelope's signature), 8 (an
invitation's signature). -/
def custodyPhase (isInit : Bool) (phase : UInt8) : Bool :=
  phase == 1 || phase == 3 || phase == 5 || phase == 6 || phase == 8 || phase == 9 || phase == 11 ||
    (isInit && phase == 2)

/-- Custody's result (`u8 status ‖ payload`): ok hands on the payload, refused carries one of
`CustodyRefusal` by `custodyRefusalLayout`; anything else is `badResult`. -/
def custodyResult (b : ByteArray) : Except (Refusal D) ByteArray :=
  match hostReply b with
  | some (.ok, p) => .ok p
  | some (.refused, p) =>
      match custodyRefusalFrame.decode p with
      | .ok (c, ()) => match CustodyRefusal.ofCode? c.1 with
        | some r => .error (.custody r)
        | none => .error .badResult
      | .error _ => .error .badResult
  | _ => .error .badResult

/-- A step's result as the phase reads it: custody's unwrapped at a custody phase, the Host's as is. -/
def stepResult (isInit : Bool) (phase : UInt8) (result : ByteArray) : Except (Refusal D) ByteArray :=
  if custodyPhase isInit phase then custodyResult result else .ok result

/-- Custody's answer to `precommit`: its next and pending public keys. -/
def precommitOf (b : ByteArray) : Option (ByteArray × ByteArray) :=
  match precommitResultFrame.decode b with
  | .ok (n, p, ()) => some (n.1, p.1)
  | .error _ => none

/-! ## The plan -/

/-- The budget an invoke is signed for. -/
def invokeBudget : Nat := 100000
/-- Headroom of the signed price over the charge derived before the signature exists. -/
def chargeSlack : Nat := 4096

/-- Follow's own World as a pinned view: every cell it holds (planning reads the World it has
folded; the call's pins are discovered afterwards by `derivePins`). -/
def worldLook (E : Env D) (w : World D) : Pinned D := fun c => .ok (w.live E c)

/-- The package an invoke runs: the object's, if it is a live programmed object (KERNEL's
`packageOf`, `requireMethods`: the receiver's own refusals). -/
def invokedPackage (X : Ctx D) (w : World D) (obj : D) : Except (Refusal D) D :=
  match w.live X.env obj with
  | none => .error (.missingCell obj)
  | some cell => match packageOf X obj cell >>= requireMethods obj with
    | .ok p => .ok p
    | .error r => .error (.receive r)

/-- The call body of a command, on follow's World `w` (a seed or an argument TEXT is read there
at its package's type: `Lang.seedOf`, `Lang.argsOf`); `s` is the key it is signed with (for
`rotate`: the next key, and the pending key it precommits). -/
def body (X : Ctx D) (me : Self D) (w : World D) (s : Signed) : Cmd D → Except (Refusal D) (Body D)
  | .enroll j => .ok (.enroll j.key j.next j.possession me.grant)
  | .install p => .ok (.install p)
  | .create none ls => .ok (.create none ls [])
  | .create (some (p, t)) ls => match Lang.seedOf X.digestOf (worldLook X.env w) p t with
    | .ok seed => .ok (.create (some p) ls seed)
    | .error r => .error (.receive r)
  | .write o k v via => .ok (.write o [(k, some v)] via)
  | .law o ls via => .ok (.law o ls via)
  | .invoke o m a _ via => do
      let p ← invokedPackage X w o
      match Lang.argsOf X.digestOf (worldLook X.env w) p m a with
      | .ok args => .ok (.invoke o m args invokeBudget via)
      | .error r => .error (.receive r)
  | .grant t g rs via =>
      let target := match t with
        | .world => worldId X
        | .cell c => c
        | .account r => r.resolve X
      .ok (.grant target (g.getD (worldId X)) rs via)
  | .revoke g => .ok (.revoke g)
  | .rotate => .ok (.rotate s.key (nextKeyDigest X s.next))
  | .issue cap => .ok (.issue cap)
  | .account a o => .ok (.account a (o.getD me.member))
  | .transfer src dst n via once => .ok (.transfer src dst n via once)
  | .credit wl acct n via => .ok (.credit wl acct n via)
  -- `sync --post OBJ` (PROTOCOL-75): `post` of follow's OWN World's head on the member's head object,
  -- the head read off `w` here as it is re-read at every phase (`Proofs.Head.body_post`)
  | .post o => do
      let p ← invokedPackage X w o
      match Lang.argsOf X.digestOf (worldLook X.env w) p Head.postMethod (Head.headText X w) with
      | .ok args => .ok (.invoke o Head.postMethod args invokeBudget none)
      | .error r => .error (.receive r)
  | .init _ | .read _ _ | .describe _ | .rangeRead .. | .adopt _ _ | .sync _ | .invite _ | .receipt _ | .cancel _ =>
      .error .badState

/-- The row pin follow states for a row slot of its World (KERNEL-54): the leaf's digest, or absence
at its relation's floor, read from the rows trie it holds. -/
def rowPinAt (E : Env D) (w : World D) (key : RowKey D) : RowSlot D × D :=
  (.row key, rowPin E (headFloor E w.rows key.parent key.rel) (rowAt E w.rows (.row key)))

/-- What a command's plan signs beside what the derivation asks for: its range reads and the row
keys it pins (`signedReads`). Every other command signs none. -/
structure SignedReads (D : Type) where
  ranges : List (RangeRead D) := []
  points : List (RowKey D) := []

/-- Derive with the signature not yet known, pinning each cell, and each row (KERNEL-54: the
receiver's `rowUnpinned` names the row's key), the derivation asks for. A row already pinned and
asked for again is the receiver's own refusal (a pinned act on a slot no row pin can name), never a
loop. -/
def derivePins (X : Ctx D) (w : World D) : Nat → Unsigned D → Except (Refusal D) (Unsigned D × Turn D)
  | 0, _ => .error .tooManyPins
  | fuel + 1, u =>
      let look := pinned X.env w u.pins
      match (do keyRule look u; deriveTurn X look (rowView X.env w u) ⟨u, ByteArray.empty⟩) with
      | .error (.unpinned c) =>
          derivePins X w fuel { u with pins := u.pins ++ [(c, pinOf X.env (w.entry X.env c))] }
      | .error (.rowUnpinned parent rel k) =>
          if u.rowPins.any (fun p => p.1 = .row ⟨parent, rel, k⟩) then
            .error (.receive (.rowUnpinned parent rel k))
          else
            derivePins X w fuel { u with rowPins := u.rowPins ++ [rowPinAt X.env w ⟨parent, rel, k⟩] }
      | .error r => .error (.receive r)
      | .ok t => .ok (u, t)

/-- The call a member's body derives to on follow's World, with every pin it read and its price the
derived charge plus headroom, and the Turn it derives: `plan` before follow's own admission. A
client that skips that admission (a hostile one: the rows' `forge` act) signs exactly this. -/
def planUnchecked (X : Ctx D) (me : Self D) (w : World D) (key : ByteArray) (rd : SignedReads D)
    (b : Body D) : Except (Refusal D) (Unsigned D × Turn D) := do
  let u0 : Unsigned D :=
    -- the invitation's World (KERNEL-24): follow's own `receive` below refuses `wrongWorld` if
    -- the World it follows is not that one, so it never signs a call for another World
    { world := me.world
      member := me.member
      key := key
      notBefore := w.height
      validUntil := w.height + me.window
      pins := []
      -- the rows the command pins (`signedReads`, `--pin REL KEY`), each at follow's own World;
      -- the rows the derivation asks for (`rowUnpinned`) are added by `derivePins`
      rowPins := rd.points.map (rowPinAt X.env w)
      -- the range reads the command names (`signedReads`: follow's own listing at `w`); a method's
      -- range read with none signed is the receiver's `rangeUnpinned`, never derived here
      ranges := rd.ranges
      -- a ceiling no Turn exceeds (`admit_weight`), so the derivation reports the charge rather
      -- than refusing `overPrice`; the signed price is set from that charge below
      maxCharge := Kernel.Bounds.weightMax
      body := b }
  let (u1, t1) ← derivePins X w Kernel.Bounds.touchesMax u0
  let u := { u1 with maxCharge := t1.charge + chargeSlack }
  match deriveTurn X (pinned X.env w u.pins) (rowView X.env w u) ⟨u, ByteArray.empty⟩ with
  | .error r => .error (.receive r)
  | .ok t => .ok (u, t)

/-- The call follow asks custody to sign: `planUnchecked`, and only if follow's World admits the
Turn it derives. -/
def plan (X : Ctx D) (me : Self D) (w : World D) (key : ByteArray) (rd : SignedReads D) (b : Body D) :
    Except (Refusal D) (Unsigned D) :=
  match planUnchecked X me w key rd b with
  | .error r => .error r
  | .ok (u, t) => match World.admit X.env w t with
    | .error r => .error (.reject r)
    | .ok _ => .ok u

/-! ## Catching up -/

/-- A re-derivation's refusal (`Receive.rederive`) as follow's: the kernel's rejection by its own name
(a writer that admits a call it recorded refused is `refusedFinal`), `eventMismatch` at the log
position `pos`, any other by the receive layer's name (a well-formed cancel `Receive.cancel` does
not record: `cancelForged`). -/
def ofVerdict (pos : Nat) : Verdict D → Refusal D
  | .rejected r => .reject r
  | .refused .eventMismatch => .eventMismatch pos
  | .refused r => .receive r

/-- Re-derive one logged step on follow's World: read the page event back (`eventOf`; an event that
does not read is `eventMismatch` at its log position) and re-derive it by THE re-deriver,
`Receive.rederive` (a Turn by `submit`, a refusal by `judge`, a cancel by `cancel` under the
event's signature; KERNEL-60, PROTOCOL-60), the one kernel-sim, the journeys and the benches run too (`Receive.rederiveLog`). -/
def absorbStep (X : Ctx D) (w : World D) (e : ByteArray) : Except (Refusal D) (Kernel.Step D × World D) :=
  match eventOf e with
  | none => .error (.eventMismatch (w.steps + 1))
  | some ev => (Receive.rederive X w ev).mapError (ofVerdict (w.steps + 1))

/-- Absorb logged events, each re-derived (`absorbStep`, PROTOCOL-4). A writer that logged an event
which does not re-derive is caught here, at that log position. Also returns the steps it took, in
log order, each with the roots digest after it, so `host follow` persists exactly what it
re-derived (HOST-3) rather than re-running this loop. -/
def absorb (X : Ctx D) : World D → Array (Kernel.Step D × D) → List ByteArray →
    Except (Refusal D) (World D × Array (Kernel.Step D × D))
  | w, ts, [] => .ok (w, ts)
  | w, ts, e :: es =>
      match absorbStep X w e with
      | .ok (s, w') => absorb X w' (ts.push (s, World.roots X.env w')) es
      | .error r => .error r

/-- A log page (`logReplyLayout`): the events, the writer's step count and chain after the last of
them, and the writer's tip when it built the page, as a step count and a height. A tip below the
page's own position is not a page. -/
structure LogPage where
  events : List ByteArray
  steps : Nat
  chain : ByteArray
  tipSteps : Nat
  tipHeight : Nat
  /-- the writer's newest durable base when it built the page: its step count and digest -/
  baseSteps : Nat
  baseDigest : ByteArray

/-- A page's stated base past its stated tip is no base of that log: not a page. -/
def logPage (b : ByteArray) : Option LogPage :=
  match logReplyFrame.decode b with
  | .ok (l, n, c, t, th, bs, bd, ()) => do
      let steps ← Text.ofU64 n.1
      let tipSteps ← Text.ofU64 t.1
      let tipHeight ← Text.ofU64 th.1
      let baseSteps ← Text.ofU64 bs.1
      if steps ≤ tipSteps ∧ baseSteps ≤ tipSteps then
        some ⟨Text.unlist l, steps, c.1, tipSteps, tipHeight, baseSteps, bd.1⟩
      else none
  | .error _ => none

/-- Absorb a page and require follow's fold to reach the writer's stated step count and chain (the
pair the kernel's `fold_reaches_host` binds). A page of more steps than `Bounds.pageStepsMax` (one
follower record) is refused `pageTooLong` before any of it is absorbed (HOST-41). The fold is cut
at the writer's stated base step count `base` (PROTOCOL-47): the World follow's OWN fold sits at
there, if it does on this page (at its start, or after one of its steps), is returned beside the
page's end, from the one fold (`absorb` of the prefix, then of the rest from where it stopped). -/
def absorbPage (X : Ctx D) (w : World D) (evs : List ByteArray) (steps : Nat) (chain : ByteArray)
    (base : Nat) : Except (Refusal D) (World D × List (Kernel.Step D × D) × Option (World D)) :=
  if Bounds.pageStepsMax < evs.length then .error (.pageTooLong evs.length) else do
  let k := base - w.steps
  let (wb, tb) ← absorb X w #[] (evs.take k)
  let (w', ts) ← absorb X wb tb (evs.drop k)
  if w'.steps = steps ∧ X.env.bytes w'.chain = chain then
    pure (w', ts.toList, if wb.steps = base then some wb else none)
  else throw (.chainMismatch steps)

/-- What `invite` pins (PROTOCOL-47): the newest base follow verified itself, and only when the
writer's newest base, as the last page stated it, is that base with that digest. A base follow
never sat at (nothing verified, or an older one) is `noBase`; one at the same step count whose
stated digest is not follow's own is `baseMismatch`. The sponsor signs its OWN digest, never the
Host's claim. -/
def pinOf (verified : Option (Nat × ByteArray)) (baseSteps : Nat) (baseDigest : ByteArray) :
    Except Invite.Refusal Thin.Pin :=
  match verified with
  | some (s, d) =>
      if s ≠ baseSteps then .error .noBase
      else if d ≠ baseDigest then .error .baseMismatch
      else .ok ⟨s, d⟩
  | none => .error .noBase

def hostName (p : ByteArray) : String := (String.fromUTF8? p).getD "unnamed"

def whoami : ByteArray := "nanodregg/protocol/whoami/v1".toUTF8

/-! ## Rendering -/

def hex (X : Ctx D) (d : D) : String := Text.toHex (X.env.bytes d)

/-- A programmed object's package (PROTOCOL-48): loaded as every method run loads it
(`Lang.load`: the closure, each package decoded and re-checked by `Package.checkWith`), its state row,
and the value `Lang.readState` reads there from the cell's state slots: `Lang.runSetup`'s own front
half. `none` for a data object. -/
def objectPackage (X : Ctx D) (w : World D) (obj : D) (cell : Cell) :
    Except (Refusal D) (Option Lang.Package) := do
  match ← (packageOf X obj cell).mapError .receive with
  | none => pure none
  | some p =>
    let (L, g) ← (Lang.load X.digestOf (worldLook X.env w) Lang.closureDepthMax (X.env.bytes p)
      ⟨[], [], []⟩).mapError .receive
    let some pk := L.pkgs[g]? | throw (.receive (.program "closure"))
    pure (some pk)

/-- The object's state value at its package's state row (`objectPackage`, then `Lang.readState`);
`none` for a data object. -/
def stateValue (X : Ctx D) (w : World D) (obj : D) (cell : Cell) :
    Except (Refusal D) (Option (List (Lang.Label × Lang.Ty) × Lang.Data)) := do
  match ← objectPackage X w obj cell with
  | none => pure none
  | some pk =>
    let row := Lang.recordRow pk.state
    match Lang.readState X.digestOf row (stateOf cell) with
    | .ok d => pure (some (row, d))
    | .error e => throw (.receive (.program e))

/-- What `read OBJ` prints (PROTOCOL-48). A programmed object: ONE line, its state value printed by
`Lang.Print.data` at the package's state type, the text `Lang.Read.readData` reads back to that very
value (`Proofs.Command.readText_reads`); a state type that is not well formed, or a value with no
text, is `noText` (the printer never guesses). The `wf` refusal never fires for a loaded package
(`Package.checkWith` requires it: `Lang.Print.checkShape_wf`); it is what makes `readText_reads`
premise-free. A data object: its state slots, one `KEY=VALUE` line
each (keys relative to `stateBase`). -/
def readText (X : Ctx D) (w : World D) (obj : D) (cell : Cell) : Except (Refusal D) String := do
  match ← stateValue X w obj cell with
  | some (row, d) =>
    if (Lang.Ty.record row).wf then
      match Lang.Print.data d with
      | some t => pure (t ++ "\n")
      | none => throw .noText
    else throw .noText
  | none =>
    pure (String.join ((stateOf cell).map fun (k, v) =>
      s!"{k - stateBase}={(String.fromUTF8? v).getD (Text.toHex v)}\n"))

/-- `read`: after every expectation on the raw state slots holds, the object's `readText`. -/
def render (X : Ctx D) (w : World D) (obj : D) (expect : List (Nat × ByteArray)) : Reply :=
  match w.live X.env obj with
  | none => refused (D := D) (.missingCell obj)
  | some cell =>
      match expect.find? fun (k, v) => cell.slots.get (stateBase + k) != some v with
      | some (k, _) => refused (D := D) (.expect k)
      | none =>
          match readText X w obj cell with
          | .ok t => printed t
          | .error r => refused r

/-- The description's lines after its head (`Command.Describe`): the package's, or `data`, then each
further law package of the object with its laws. -/
def describeLines (X : Ctx D) (w : World D) (obj : D) (cell : Cell) : Except (Refusal D) (List String) := do
  let look := worldLook X.env w
  let pkg ← (packageOf X obj cell).mapError .receive
  let laws ← (lawsOf X obj cell).mapError .receive
  let ps ← match pkg with
    | none => pure ["data"]
    | some p =>
      let pk ← (Lang.readPackage look p).mapError .receive
      -- the package cell's bytes, which `readPackage` just decoded (its id is their digest, KERNEL-3)
      let core := ((w.live X.env p).bind fun c => c.slots.get 0).getD ByteArray.empty
      match packageLines (D := D) pk with
      | some ls => pure (s!"package {hex X p}" :: s!"core {Lang.Print.hex core}" :: ls)
      | none => throw .noText
  let ls ← laws.mapM fun l => do
    let lp ← (Lang.readPackage look l).mapError .receive
    pure (s!"law {hex X l}" ++ String.join (lp.laws.map (" " ++ ·)))
  pure (ps ++ ls)

/-- The lines of `read OBJ ?` (`Command.Describe`) for a live cell: its head, then `describeLines`. -/
def describeText (X : Ctx D) (w : World D) (obj : D) (cell : Cell) : Except (Refusal D) (List String) := do
  let ls ← describeLines X w obj cell
  pure (s!"object {hex X obj}" :: ((cell.slots.get slotOwner).map fun o => [s!"owner {Text.toHex o}"]).getD [] ++ ls)

/-- `read OBJ ?`: the object's self-description (`Command.Describe`), on follow's caught-up World.
Only an object describes itself (`wrongKind` otherwise: `invoke` runs only an object, KERNEL's
`invoke_ok`). Each line is printed with one line break after it, and the description is refused
`noText` unless no line holds a break of its own (`noBreak`), so a reader that splits it at breaks
reads back exactly the lines (HOSTING-43). -/
def describe (X : Ctx D) (w : World D) (obj : D) : Reply :=
  match w.live X.env obj with
  | none => refused (D := D) (.missingCell obj)
  | some cell =>
    if cell.kind ≠ kindObject then refused (D := D) (.receive (.wrongKind obj kindObject)) else
    match describeText X w obj cell with
    | .ok ls => if ls.all noBreak then printed (String.join (ls.map (· ++ "\n"))) else refused (D := D) .noText
    | .error r => refused (D := D) r

/-! ## `read OBJ REL K [PREFIX]` — a range read over a relation (PROTOCOL-51)

The rows of relation REL of the object's package whose key starts with PREFIX, at most K, through
THE range read a method's range read gets: `Kernel.rangeOf` on follow's caught-up World (a method's
is `Receive.rowView`'s, the same function), each row as data by `Lang.rangeRowData` (a method's
range slots are `Lang.relReads`', the same function), each printed on ONE line by `Lang.Print.data`
at the relation's row type (`Proofs.Command.rangeLines_reads`: every line reads back to its row, and
the lines are exactly the listing's rows, in its order, which is key-BYTE order by theorem
(`range_rows_exact`); whether that is a field's natural order is LANG's key wire, LANG-57). The refusals are the
method path's by name (`rangeUnpinned`, `keyWidth`, `rangeTooLong`, never truncated) and K past the
relation's declared `limit` (`rangePastLimit`). -/

/-- Relation `rel` of the object's package: its index (the kernel's `rel`) and its declaration. -/
def relationOf (X : Ctx D) (w : World D) (obj : D) (cell : Cell) (rel : String) :
    Except (Refusal D) (Nat × Lang.RelDecl) :=
  match objectPackage X w obj cell with
  | .error r => .error r
  | .ok none => .error (.unknownRelation rel)
  | .ok (some pk) =>
    match Lang.relIndex pk.rels rel, Lang.Row.find? rel pk.rels with
    | some i, some d => .ok (i, d)
    | _, _ => .error (.unknownRelation rel)

/-- PREFIX's bytes: `Lang.preBytes` (the key wire of the first `m` declared key fields), for the
first `m` whose prefix type (`Lang.preTy`) `Lang.Read.readData` reads the text at; no text: every
row (no bytes). -/
def prefixBytes (d : Lang.RelDecl) : Option String → Option ByteArray
  | none => some ByteArray.empty
  | some t =>
    (List.range (d.key.length + 1)).findSome? fun m =>
      match Lang.Read.readData (Lang.preTy d m) t with
      | .ok v => Lang.preBytes d m v
      | .error _ => none

/-- THE listing of relation `i` (declared `d`) under `obj` at most K, the K bound aside: the prefix's
bytes, the relation's key width and the rows, through `Kernel.rangeOf`. What `read OBJ REL K [PREFIX]`
prints (`rowLines`) and what `invoke … --range REL K [PREFIX]` signs (`invokeRange`) are this one
listing, never a second derivation. -/
def rangeListing (X : Ctx D) (w : World D) (obj : D) (i : Nat) (d : Lang.RelDecl) (most : Nat)
    (pre : Option String) : Except (Refusal D) (ByteArray × Nat × List (RowSlot D × RowLeaf)) :=
  match prefixBytes d pre with
  | none => .error .badPrefix
  | some pb =>
    match rangeOf X.env w.rows obj i pb most with
    | none => .error (.receive (.rangeUnpinned obj i))
    | some (width, lo) =>
      if pb.size ≤ width then
        match lo with
        | none => .error (.receive (.rangeTooLong obj))
        | some l => .ok (pb, width, l)
      else .error (.reject (.keyWidth obj))

/-- The rows' lines of relation `i` (declared `d`) under `obj`, the K bound aside. -/
def rowLines (X : Ctx D) (w : World D) (obj : D) (i : Nat) (d : Lang.RelDecl) (rel : String)
    (most : Nat) (pre : Option String) : Except (Refusal D) (List String) :=
  match rangeListing X w obj i d most pre with
  | .error r => .error r
  | .ok (_, _, l) =>
          match Lang.rangeRowData X.digestOf rel d l with
          | .error r => .error (.receive r)
          | .ok ds =>
            -- a refusal (`noText`), never an acceptance; `checkRel` makes it unreachable for an
            -- installed package (`keyTy d` and `d.val` are checked wf), not proved here; it is what
            -- makes `rangeLines_reads` premise-free
            if (Lang.rowTy d).wf then
              match ds.mapM Lang.Print.data with
              | some ts => .ok ts
              | none => .error .noText
            else .error .noText

/-- `read OBJ REL K [PREFIX]`'s lines: K within the relation's declared `limit`, then `rowLines`. -/
def rangeLines (X : Ctx D) (w : World D) (obj : D) (cell : Cell) (rel : String) (most : Nat)
    (pre : Option String) : Except (Refusal D) (List String) :=
  match relationOf X w obj cell rel with
  | .error r => .error r
  | .ok (i, d) => if most ≤ d.limit then rowLines X w obj i d rel most pre else .error (.rangePastLimit most)

/-- The range read an invoke signs (item 4, ROOT ruled): `--range REL K [PREFIX]`'s one range,
relation REL of the object's package under the object, K within the relation's declared `limit` as
`read OBJ REL K` (`rangePastLimit`), pinned at `rangeListing`'s rows on follow's World `w` by THE
pin admission recomputes (`Kernel.rangePin` at the relation's floor). -/
def invokeRange (X : Ctx D) (w : World D) (o : D) (rel : String) (most : Nat) (pre : Option String) :
    Except (Refusal D) (RangeRead D) :=
  match w.live X.env o with
  | none => .error (.missingCell o)
  | some cell =>
    match relationOf X w o cell rel with
    | .error r => .error r
    | .ok (i, d) =>
      if most ≤ d.limit then
        match rangeListing X w o i d most pre with
        | .error r => .error r
        | .ok (pb, width, l) =>
          .ok { parent := o, rel := i, pre := pb, most,
                seen := rangePin X.env o i width pb (headFloor X.env w.rows o i) l }
      else .error (.rangePastLimit most)

/-- The object and relation an invoke's `--pin` names: `REL` is a relation of the invoked object
`o`; `OBJ/REL` (OBJ a digest in hex) is a relation of another object, a peer whose row the method
reads through the call's view (the offer's fuse reads its peer's offer row: `Lang.Std.offer`,
CLIENT-50). A text whose part before `/` is not a digest names a relation of `o`. -/
def pinTarget (X : Ctx D) (o : D) (rel : String) : D × String :=
  match rel.splitOn "/" with
  | [h, r] => match Text.ofHex h >>= X.digestOf with
    | some d => (d, r)
    | none => (o, rel)
  | _ => (o, rel)

/-- The row an invoke's `--pin [OBJ/]REL KEY` pins (CLIENT-35): relation REL of the object's package
under the object (the invoked one, or OBJ: `pinTarget`), at KEY's bytes (KEY read at the relation's
key type by LANG's reader, its bytes LANG's key wire, `Lang.keyBytes`: the bytes a method's edit of
that key writes). The plan pins it at follow's World (`rowPinAt`), so a method's point read is
handed that row, present or absent. -/
def invokePoint (X : Ctx D) (w : World D) (o₀ : D) (p : String × String) : Except (Refusal D) (RowKey D) :=
  let (o, rel) := pinTarget X o₀ p.1
  match w.live X.env o with
  | none => .error (.missingCell o)
  | some cell =>
    match relationOf X w o cell rel with
    | .error r => .error r
    | .ok (i, d) =>
      match Lang.Read.readData (Lang.keyTy d) p.2 with
      | .error _ => .error .badKey
      | .ok v =>
        match Lang.keyBytes d v with
        | some k => .ok ⟨o, i, k⟩
        | none => .error .badKey

/-- What a command's plan signs beside the derivation's asks (`SignedReads`): an invoke's
`--range` (`invokeRange`) and its `--pin`s (`invokePoint`), in order. Every other command signs
none. -/
def signedReads (X : Ctx D) (w : World D) : Cmd D → Except (Refusal D) (SignedReads D)
  | .invoke o _ _ rd _ => do
    let ranges ← match rd.range with
      | none => pure []
      | some (rel, most, pre) => do pure [← invokeRange X w o rel most pre]
    let points ← rd.points.mapM (invokePoint X w o)
    pure { ranges, points }
  | _ => .ok {}

/-- `read OBJ REL K [PREFIX]` on follow's caught-up World: one line per row. -/
def rangeRender (X : Ctx D) (w : World D) (obj : D) (rel : String) (most : Nat) (pre : Option String) :
    Reply :=
  match w.live X.env obj with
  | none => refused (D := D) (.missingCell obj)
  | some cell =>
    match rangeLines X w obj cell rel most pre with
    | .ok ts => printed (String.join (ts.map (· ++ "\n")))
    | .error r => refused (D := D) r

/-- A text a program gave, on ONE line (a law or a method cannot add lines to the member's output). -/
def oneLine (s : String) : String := (s.replace "\n" " ").replace "\r" " "

/-- What to do next, for the refusals that have an answer (DELVETALK-LEARNINGS §4.3): printed on
stdout beside `refused NAME` on stderr, so the name stays the verdict and the hint is text. -/
def hint (X : Ctx D) : Refusal D → Option String
  | .reject (.stale c) => some s!"hint stale {hex X c}: this cell moved under the call; read it and run the command again"
  -- the law's own words (at most `Lang.reasonMax` bytes), on ONE line: a law cannot add lines
  | .receive (.lawDenied l why) => some s!"hint lawDenied {hex X l}: {oneLine why}"
  -- a method's own refusal by its name (LANG-51's `refuse T "why"`: the Bell's `notResident`), as LANG
  -- states it (`Lang.faultText`, at most `Lang.reasonMax` bytes), on ONE line (cv 01a15039)
  | .receive (.program why) => some s!"hint program: {oneLine why}"
  -- a method reads a relation by range and the call signs none (LANG-22's structured refusal)
  | .receive (.rangeUnpinned _ _) =>
      some "hint rangeUnpinned: this method reads a relation by range; pass --range REL K [PREFIX]"
  | .host "stale" => some "hint stale: the World moved before the call landed; run the command again (it re-plans)"
  | .thin (.baseMoved _) => some "hint baseMoved: the writer's newest base is not at the invitation's pin; ask your sponsor for a fresh invitation"
  | .invite .noBase => some "hint noBase: follow has not verified the writer's newest base; the operator runs host seal STORE (writer stopped), then invite again"
  | .invite .baseMismatch => some "hint baseMismatch: the writer states a base that is not this member's own World there; do not invite through this writer"
  | .host "lawDenied" => some "hint lawDenied: a law refused the call; `read OBJ ?` names the object's laws"
  | .host "unknownKey" => some "hint unknownKey: run nd sync: a rotation may have landed"
  -- the writer's log begins after follow's height (HOST-61): follow reports it and never adopts a base
  -- on the writer's word (cv 01a151bc-6ef3)
  | .host "beforeLog" =>
      some "hint beforeLog: the writer's log starts at a base; join it with an invitation that pins that base (nd adopt)"
  -- an argv the parser refused: the verb's grammar, the list of verbs, the reader's reason (CLIENT-51)
  | .parse (.usage _ u) => some s!"hint usage: nd {u}; quote an argument that holds spaces: \"two words\""
  | .parse (.unknownVerb _) | .parse .noVerb =>
      some s!"hint commands: {" · ".intercalate (Verb.all.map usage)}"
  | .parse (.badPackage why) => some s!"hint badPackage: {oneLine why}"
  | .parse (.badDigest _) => some "hint badDigest: an id is 64 lowercase hex digits, as create, install and grant print it"
  | _ => none

/-- `refused r`, with its hint on stdout when it has one. -/
def refusedAt (X : Ctx D) (r : Refusal D) : Reply :=
  match hint X r with
  | some h => .done CommandExit.refused.code.toUInt8 s!"{h}\n".toUTF8 s!"refused {r.name}\n".toUTF8
  | none => refused (D := D) r

/-- What a committed write prints: its transaction id and every cell it created. -/
def receipt (X : Ctx D) (t : Turn D) : String :=
  s!"tx {hex X t.txId}\n" ++ String.join ((createdIds t).map fun d => s!"id {hex X d}\n")

/-! ## Expiry (PROTOCOL-19) -/

/-- The writer refused an envelope signed for `upTo` as `expired` at `height`. Follow re-signs
the same request ONCE per command (`tried`), for `height + window`; a second `expired`, or a
stated height the first envelope already covered (the writer contradicts itself), ends the command
`expired`. So a command signs at most one envelope per page plus one. -/
def reSign (me : Self D) (tried : Bool) (upTo height : Nat) : Except (Refusal D) Nat :=
  if !tried && upTo < height && height + me.window < 2 ^ 64 then .ok (height + me.window)
  else .error (.expired height)

/-! ## The machine -/

/-- The one message follow signs for an envelope: read from `start`, good for the one window of
heights ending at `upTo` (PROTOCOL-27). Every `upTo` follow chooses is a height it signs from plus
`me.window` (its own, the stated tip, the stated `expired` height, the pin's), so the window starts
at that height. -/
def envelopeMessage (X : Ctx D) (me : Self D) (start upTo : Nat) : ByteArray :=
  Envelope.message X me.world me.member me.grant start (upTo - me.window) upTo

/-- The envelope follow sends: `envelopeMessage`'s fields, signed. -/
def envelopeOf (me : Self D) (start upTo : Nat) (s : Signed) : Envelope D :=
  { world := me.world, member := me.member, grant := me.grant, start, notBefore := upTo - me.window,
    validUntil := upTo,
    key := s.key, signature := s.signature }

/-- The envelope a thin member signs for the base page at byte `offset`, valid until `upTo`
(first the pin's height + window; after an `expired`, the writer's stated height + window). -/
def adoptEnvelope (X : Ctx D) (me : Self D) (upTo offset : Nat) : ByteArray :=
  envelopeMessage X me offset upTo

/-- The pin an `adopt` takes: that of an invitation `Invite.acceptStart` accepts under the trusted `key`,
to the member's own World (re-derived at every step from the argv, like every plan). -/
def adoptPin (X : Ctx D) (me : Self D) (inv key : ByteArray) : Except (Refusal D) (Invite.Invitation D) :=
  match Invite.acceptStart X key inv with
  | .error r => .error (.invite r)
  | .ok (i, o) => if o = me.world then .ok i else .error (.invite .otherWorld)

/-- `invite`'s check of its INPUT: the inputs decode and make the member's own World. -/
def inviteInput (X : Ctx D) (me : Self D) (input : ByteArray) : Except (Refusal D) Unit :=
  match Invite.startOf X input with
  | none => .error (.invite .badInvitation)
  | some start =>
    match Invite.startOrigin X start with
    | .error r => .error (.invite r)
    | .ok o => if o = me.world then .ok () else .error (.invite .otherWorld)

/-! ## The incoming key (PROTOCOL-46, CLIENT-13 amended)

A rotation can land while custody has not yet settled it (its `ok` lost): the writer then refuses
the old key's envelope `unknownKey`, and the confirm that would settle custody could never read.
So a command of a verb that signs no call (`readOnly`) asks custody ONCE to sign its envelope with
the ARMED rotation's incoming key (`signIncoming`), and every later envelope of that command too.
`tried`'s bit 0 is the one `expired` re-sign, bit 1 the incoming key. A second `unknownKey` ends the
command by the writer's word (`unknownKeyEnd`); so does ANY custody refusal of the `signIncoming`
step (`custodyEnd`, ROOT's rule (a), PROTOCOL-56): custody's refusal only says why the retry could not
happen (`notArmed`: no rotation in flight; `noRotation`: `nd --stdio`'s custody, which holds none),
never what the writer said. A write is never retried: its plan would be signed by the old key against an envelope the
incoming key signed; it ends `refused unknownKey` with the hint to sync. -/

/-- The verbs that sign no call: the only ones whose envelope may be signed by the incoming key. -/
def readOnly : Cmd D → Bool
  | .read _ _ | .describe _ | .rangeRead .. | .sync _ | .receipt _ => true
  | _ => false

/-- The verbs whose step 3 submits a call (`plan` at the log's tip, `rotate` from phase 5): the only
ones a phase-4 continuation settles. A continuation is the client's bytes, never a witness, so a
phase-4 state under any other verb is `badState`, never a settlement: `cancel CALL` ends `ok` only by
its own settlement (`cancelSettled`, PROTOCOL-71). -/
def submits : Cmd D → Bool
  | .init _ | .adopt .. | .invite _ | .cancel _ => false
  | c => !readOnly c

def incomingBit : Nat := 2
def expiredBit : Nat := 1

/-- How the writer's `unknownKey` ends a command once the incoming key cannot help: a verb that signs
no call by the bare name, a write with the hint to sync. -/
def unknownKeyEnd (X : Ctx D) (cmd : Cmd D) : Reply :=
  if readOnly cmd then refused (D := D) (.host "unknownKey") else refusedAt X (.host "unknownKey")

/-- The envelope's signing step: by the incoming key once `tried` has bit 1. -/
def envelopeSign (tried : Nat) (m k : ByteArray) : Reply :=
  if tried &&& incomingBit = 0 then .sign m k else .signIncoming m k

/-- The writer refused an envelope (phase 2): `expired` re-signs once (`reSign`); `unknownKey` to a
verb that signs no call re-signs once by the incoming key; `pageIo` ends the command restart-class
(`notServed`, HOST-48); anything else ends the command by name. -/
def envelopeRefused (X : Ctx D) (me : Self D) (argv : List ByteArray) (cmd : Cmd D)
    (startB pagesB upToB triedB p : ByteArray) : Reply :=
  match expiredHeight? p, Text.ofU64 startB, Text.ofU64 upToB, Text.ofU64 triedB with
  | none, some h, some upTo, some tried =>
      if p = ReadRefusal.unknownKey.payload then
        if readOnly cmd && tried &&& incomingBit == 0 then
          next (D := D) ⟨argv, 1, [startB, pagesB, upToB, Text.u64 (tried ||| incomingBit)]⟩ fun k =>
            .signIncoming (envelopeMessage X me h upTo) k
        else unknownKeyEnd X cmd
      else if p = pageIoName.toUTF8 then notServed
      else refusedAt X (.host (hostName p))
  | some height, some h, some upTo, some tried =>
      match reSign (D := D) me (tried &&& expiredBit ≠ 0) upTo height with
      | .error r => refused (D := D) r
      | .ok upTo' =>
          next (D := D) ⟨argv, 1, [startB, pagesB, Text.u64 upTo', Text.u64 (tried ||| expiredBit)]⟩ fun k =>
            envelopeSign tried (envelopeMessage X me h upTo') k
  | _, _, _, _ => refused (D := D) .badState

/-- KERNEL-54, the attempt side (PROTOCOL-15's conditions 1 and 2): is the call stale BEHIND on
follow's own fold? Only the member's OWN call for its own World (custody signs only what follow
planned, and `plan` signs `notBefore` = the planning World's height and pins from that World, a
World of follow's fold), planned at a height follow has reached (`notBefore ≤ w.height`: every World
of one height holds the same entries, refusal steps change none), that follow's World declines
`stale` by the Host's OWN order (KERNEL-66, PROTOCOL-73): the call's authority (`signedBy`), then its
pins against the World (`checkPins`), before any receiver runs. One definition with the Host's
`submit` (`Proofs.Command.staleBehind_declined`): a moved pin is `stale` whatever a receiver would
say of the World as it is now. Before PROTOCOL-73 this read `receive` first, so a call whose receiver
also refused on the new World was not stale here while the Host declined it `stale`, and the
settlement stayed `open`. A stale pin observed on the fold stays stale at every World the fold
reaches (`Kernel.stale_behind_forever`). A planning height follow has not reached (AHEAD), another
member's call (unplaceable), a call whose authority the World refuses, or pins that agree: `false`,
and the settlement stays `open`. -/
def staleBehind (X : Ctx D) (me : Self D) (w : World D) (c : Call D) : Bool :=
  decide (c.unsigned.member = me.member) && decide (c.unsigned.world = me.world) &&
    decide (c.unsigned.notBefore ≤ w.height) &&
    match signedBy X w c false with
    | .error _ => false
    | .ok () =>
      match checkPins X.env w c.unsigned.pins c.unsigned.rowPins c.unsigned.ranges with
      | .error _ => true
      | .ok () => false

/-- A range read's pin inputs at a World: its listing's range-pin input at the relation's width and
floor there, then each listed row's leaf input (a range pin embeds its rows' leaf digests); none
where the relation has no head or the listing is past `most`. -/
def rangePresAt (E : Env D) (w : World D) (q : RangeRead D) : List (String × ByteArray) :=
  match headOf E w.rows q.parent q.rel with
  | none => []
  | some (_, _, _, _, width, _) =>
    match rangeRows E w.rows q.parent q.rel width q.pre q.most with
    | none => []
    | some l => rangePre E q.parent q.rel width q.pre (headFloor E w.rows q.parent q.rel) l :: leafPres l

/-- The pin preimages the BEHIND finality names: for every cell the call pins, its entry's pin
input at the planning World and at the later one; for every row it pins, its row pin input at
both; for every range it reads, its range-pin and leaf inputs at both (`rangePresAt`). An explicit
list: a collision among these is a collision of the deployed hash on inputs the two Worlds hold. -/
def behindPres (E : Env D) (w₀ w' : World D) (u : Unsigned D) : List (String × ByteArray) :=
  u.pins.flatMap (fun p => [pinPre E (w₀.entry E p.1), pinPre E (w'.entry E p.1)]) ++
    (u.rowPins.flatMap fun p => match p.1 with
      | .row key => [rowPre (headFloor E w₀.rows key.parent key.rel) (rowAt E w₀.rows (.row key)),
          rowPre (headFloor E w'.rows key.parent key.rel) (rowAt E w'.rows (.row key))]
      | .head .. => []) ++
    u.ranges.flatMap fun q => rangePresAt E w₀ q ++ rangePresAt E w' q

/-- The member's settlement of a call on follow's World: the receipt's answer, the journal's
reach, follow's own fold's `staleBehind` (KERNEL-54) and the window (`Settle.ofReceipt`). -/
def settleOf (X : Ctx D) (me : Self D) (w : World D) (c : Call D) : Settle.Verdict D :=
  Settle.ofReceipt (journalForgets w.height c.unsigned.notBefore) (staleBehind X me w c)
    w.height c.unsigned.validUntil (Receipt.build X.env w (txIdOf X c)).answer

/-- The `receipt CALL` lines: the receipt, the head it was built at (`head STEPS HEIGHT ROOTS CHAIN`:
what a foreign World posts into `Std.head`, PROTOCOL-75), and the settlement. -/
def receiptText (X : Ctx D) (dc : Stream D) (me : Self D) (w : World D) (c : Call D) : Option String :=
  let r := Receipt.build X.env w (txIdOf X c)
  let v := settleOf X me w c
  (Receipt.bytes X.env dc r).map fun b =>
    s!"{Attempt.receiptWord} {Text.toHex b}\n{Attempt.headWord} {w.steps} {w.height} {hex X (w.roots X.env)} {hex X w.chain}\n" ++
      s!"{Attempt.settleWord} {v.text X.env.bytes}\n"

def receiptLines (X : Ctx D) (dc : Stream D) (me : Self D) (w : World D) (cb : ByteArray) : Reply :=
  match X.decodeCall cb with
  | none => refused (D := D) .badCall
  | some c =>
      match receiptText X dc me w c with
      | some t => printed t
      | none => refused (D := D) .badState

/-! ## `sync` (PROTOCOL-74) -/

/-- What `sync` prints at the tip: follow's World's height, chain and roots. -/
def syncLines (X : Ctx D) (w : World D) : String :=
  s!"height {w.height}\nchain {hex X w.chain}\nroots {hex X (w.roots X.env)}\n"

/-- The anchor a `sync` compares against, re-derived from the argv at every step (the continuation
cannot steer it): `--to`'s stated pair, or the attested head of a `--check` whose bytes verify
(`Head.verified`; one that does not is refused at `start`, and again here if a continuation names
it); `none` for every other command. -/
def syncAnchor (X : Ctx D) (me : Self D) : Cmd D → Option (Nat × ByteArray)
  | .sync (.to steps chain) => some (steps, chain)
  | .sync (.check b) => (Head.verified X me.world b).toOption.map fun a => (a.head.steps, X.env.bytes a.head.chain)
  | _ => none

/-- A page absorbed (`absorbPage`), then, for `sync --to` / `--check`, walked against the anchor from
follow's position before it (`Head.anchorCheck`): another chain at the anchor's step count is
`forkedWorld`, the page refused and nothing of it kept, as a `chainMismatch` page is (PROTOCOL-74:
the fork is evidence, and follow does not walk onto it under this command; a plain `sync` does). -/
def absorbSync (X : Ctx D) (me : Self D) (cmd : Cmd D) (w : World D) (evs : List ByteArray) (steps : Nat)
    (chain : ByteArray) (base : Nat) :
    Except (Refusal D) (World D × List (Kernel.Step D × D) × Option (World D)) :=
  match absorbPage X w evs steps chain base with
  | .error r => .error r
  | .ok (w', ts, wb) =>
    match syncAnchor X me cmd with
    | some (s, c) =>
        if Head.anchorCheck X.env s c w.steps w.chain ts = .forked then .error (.forkedWorld s)
        else .ok (w', ts, wb)
    | none => .ok (w', ts, wb)

/-- The reply a page's self-head posts force, else `r` (PROTOCOL-75): `forkedPost` when a member's
post of its head of this World sits at a position follow's fold reached on this page with another
chain (`Head.forkedSelfPost`). The page itself is kept by the caller (`moved`: it is lawful on
follow's fold; the fork is the poster's or the writer's), the command ends by name, and the next
command proceeds past the post. A top-level function, not a match in `step`: `step_world`'s blanket
split pays per match of `step`'s body; irreducible, so no reply-shape proof over `step` unifies
through it (two stuck matchers cost what a constructor mismatch does not): they read it by
`postOr_cases` and the elims beside it. -/
@[irreducible] def postOr (X : Ctx D) (w : World D) (ts : List (Kernel.Step D × D)) (w' : World D) (r : Reply) : Reply :=
  match Head.forkedSelfPost X w ts w' with
  | some (s, m) => refused (D := D) (.forkedPost s m)
  | none => r

/-- `shared` or `unreached` at the tip: the anchor's step count against follow's. `start` refused to
begin past the anchor (`ahead`), and every page on the way compared the chain there
(`forkedWorld` otherwise), so reaching the anchor's step count at the tip means follow's fold
passed it with the anchor's chain. -/
def anchorLine (steps : Nat) (w : World D) (who : String) : String :=
  (if steps ≤ w.steps then s!"shared {steps}" else s!"unreached {steps}") ++ who ++ "\n"

/-- The `sync` tip. `--attest`: the message custody signs is `Head.message` of follow's OWN World's
head, with the member and the key the writer took for this command's envelope
(`Proofs.Head.attestTip_sign`); the result is printed at phase 11. -/
def attestTip (X : Ctx D) (me : Self D) (w : World D) (argv : List ByteArray) (signedB : ByteArray) : Reply :=
  match Signed.ofBytes signedB with
  | none => refused (D := D) .badState
  | some s =>
      match Head.unsignedBytes X.env (Head.headOf X.env w) me.member s.key with
      | none => refused (D := D) .badState
      | some u => next (D := D) ⟨argv, 11, [signedB, u]⟩ fun k => .sign (Head.message u) k

def syncTip (X : Ctx D) (me : Self D) (w : World D) (argv : List ByteArray) (signedB : ByteArray) :
    SyncMode → Reply
  | .tip => printed (syncLines X w)
  | .to steps _ => printed (anchorLine steps w "" ++ syncLines X w)
  | .check b =>
      match Head.verified X me.world b with
      | .error r => refused (D := D) (.attest r)
      | .ok a =>
          match Head.signer X w a with
          | .error r => refused (D := D) (.attest r)
          | .ok () => printed (anchorLine a.head.steps w s!" {hex X a.member}" ++ syncLines X w)
  | .attest => attestTip X me w argv signedB

/-- Phase 11: custody's signature over the attestation; printed `attest HEX`. -/
def attestDone (signedB u result : ByteArray) : Reply :=
  match Signed.ofBytes signedB, Signed.ofBytes result with
  | some s, some s2 =>
      if s2.key ≠ s.key then refused (D := D) .badResult else
      match Head.bytes u s2.signature with
      | some b => printed s!"attest {Text.toHex b}\n"
      | none => refused (D := D) .badState
  | _, _ => refused (D := D) .badResult

/-- The name a settled refusal prints: the recorded code's (`settle refused CODE`), or the one word
the settlement is (`expired`). -/
def settledName (txt : String) : String :=
  match txt.splitOn " " with
  | ["refused", c] => (c.toNat?.bind Receive.codeName).getD s!"code{c}"
  | [w] => w
  | _ => "refused"

/-- One refusal of every name follow's own machine prints but the Host's (`host`, a string Lean
does not produce): a receive refusal and a kernel rejection are named by their owners' tables
instead (`hintNames`). Arguments are placeholders; a name drops them. -/
def hintReps : List (Refusal Nat) :=
  [.eventMismatch 0, .badState, .badResult, .planMoved, .expect 0, .missingCell 0, .tooManyPins,
   .chainMismatch 0, .pageTooLong 0, .noText, .expired 0, .badCall, .unknownRelation "",
   .rangePastLimit 0, .badPrefix, .badKey, .forkedWorld 0, .ahead 0, .forkedPost 0 none] ++
  Head.Refusal.all.map Refusal.attest ++ Head.CertRefusal.all.map Refusal.certified ++
  ([.argvPastBound 0, .notUtf8 0, .noVerb, .unknownVerb "", .usage "" "", .badDigest "", .badNumber "",
    .badRight "", .badToken "", .badExpect "", .badPackage "", .badAccount "", .badOnce ""] :
    List ParseRefusal).map Refusal.parse ++
  ([.badPage, .baseMoved 0, .baseMismatch, .pageMismatch, .baseTooLarge 0, .baseUndecodable,
    .notBehind 0, .notAtGenesis 0, .incomplete 0 0, .wrongWorld] : List Thin.Refusal).map Refusal.thin ++
  CustodyRefusal.all.map Refusal.custody ++
  (([.badInvitation, .notSponsor, .pinMismatch, .otherWorld, .noBase, .baseMismatch, .carried] : List Invite.Refusal) ++
    ([.nameTooLong, .nonceTooLong, .tooManyFounders, .founderKeyTooLong 0, .founderNextTooLong 0,
      .tooManyCertifiers, .certifierTooLong 0, .repeatedCertifier 0, .badThreshold,
      .allowanceTooLarge] : List GenesisRefusal).map Invite.Refusal.inputs).map Refusal.invite

/-- The names a hint may carry: every `refused NAME` follow's machine prints but the Host's word
(`Proofs.Command.hintNames_complete`). -/
def hintNames : List String :=
  hintReps.map Refusal.name ++ Receive.refusalNames ++ Receive.rejectNames

/-- Where the first line of `p` ends, scanning from `i` with `fuel` bytes left: the first newline's
index, or the end. -/
def lineEnd (p : ByteArray) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i => if h : i < p.size then (if p[i] == 10 then i else lineEnd p fuel (i + 1)) else i

/-- A payload's first line: its bytes before the first newline. -/
def firstLine (p : ByteArray) : ByteArray := p.extract 0 (lineEnd p p.size 0)

/-- The hint an attempt's `uncertain` end carries (cv 01a150b1, PROTOCOL-55's finding): the payload
is the stderr of follow's `receipt CALL` for the attempt's confirm or probe, as the attempt store
handed it. It is read only when it is at most `Bounds.hintBytesMax` bytes and its first line is byte
for byte `refused NAME` with NAME one of `hintNames`; anything else (another text, a Host name that
is not in the table, none) is no hint. What is printed is the table's name, never the payload's
bytes (`Proofs.Command.confirmHint_iff`); a Host name equal to a table name (`refused stale`
relayed) is printed as that name. -/
def confirmHint (p : ByteArray) : Option String :=
  if p.size ≤ Bounds.hintBytesMax then
    hintNames.find? fun n => decide (firstLine p = ("refused " ++ n).toUTF8)
  else none

/-- What an `uncertain` end prints on stdout beside `uncertain` on stderr: the hint, or nothing. -/
def uncertainOut (p : ByteArray) : ByteArray :=
  match confirmHint p with
  | some n => s!"hint confirm: refused {n}\n".toUTF8
  | none => ByteArray.empty

/-- Follow's own settlement, on its CURRENT World `w`, of the call it handed out to submit at step 3
(the bytes step 3 put in the continuation): `none` when they do not decode as a call. -/
def ownSettle (X : Ctx D) (me : Self D) (w : World D) (cb : ByteArray) : Option (Settle.Verdict D) :=
  (X.decodeCall cb).map (settleOf X me w)

/-- An end the attempt store claims final (`claim`: committed or refused) that follow's own World
does not hold: `hostContradicted CLAIM FOLLOWSAID`, the attempt left open, as when the Host's word is
contradicted (PROTOCOL-46); call bytes that do not decode are not a result of step 3. -/
def attemptContradicted (X : Ctx D) (claim : String) : Option (Settle.Verdict D) → Reply
  | some v => .done CommandExit.hostContradicted.code.toUInt8 ByteArray.empty
      s!"hostContradicted {claim} {v.text X.env.bytes}\n".toUTF8
  | none => refused (D := D) .badResult

/-- Step 4's result is the attempt's end, `u8 Action.code ‖ payload` (PROTOCOL-46). Committed and
refused are FOLLOW's to say: the end is the attempt store's (nd's loop over `Attempt.next`, which
follow does not run), so a final it claims is checked against `ownSettle` on follow's own World, the
World the attempt's confirm or probe just caught up: `committed` is answered `ok` only when that
World's settlement of the submitted call is committed, `refused` only when it is refused or expired
(printed by follow's own verdict), anything else is `hostContradicted`. `open` and
`hostContradicted` restart; an `uncertain` end prints the refusal that caused it when its payload
names one (`uncertainOut`). -/
def settled (X : Ctx D) (me : Self D) (w : World D) (out cb result : ByteArray) : Reply :=
  if h : 0 < result.size then
    let txt := (String.fromUTF8? (result.extract 1 result.size)).getD ""
    match Attempt.Action.all.find? (·.code == result[0]) with
    | some .committed =>
        match ownSettle X me w cb with
        | some (.committed _ _) => .done CommandExit.ok.code.toUInt8 out ByteArray.empty
        | v => attemptContradicted X "committed" v
    | some .refused =>
        match ownSettle X me w cb with
        | some (.refused code) =>
            refusedAt X (.host (settledName ((Settle.Verdict.refused code : Settle.Verdict D).text X.env.bytes)))
        | some .expired => refusedAt X (.host "expired")
        | v => attemptContradicted X "refused" v
    | some .declined => declined txt
    | some .open => .done CommandExit.open.code.toUInt8 ByteArray.empty "open\n".toUTF8
    | some .contradicted =>
        .done CommandExit.hostContradicted.code.toUInt8 ByteArray.empty s!"hostContradicted {txt}\n".toUTF8
    | some .uncertain =>
        .done CommandExit.uncertain.code.toUInt8 (uncertainOut (result.extract 1 result.size)) "uncertain\n".toUTF8
    | some .badReply => .done CommandExit.client.code.toUInt8 ByteArray.empty "badReply\n".toUTF8
    | _ => refused (D := D) .badResult
  else refused (D := D) .badResult

/-- A live member cell, grant cell or authority cell: the kinds a genesis builds
(`Receive.genesisEntries`: the founders' members and grants, then the authority, KERNEL-69) and the
only ones a step-0 World holds. Any member, grant or authority passes, not only this lineage's. -/
def genesisLeaf : Leaf → Bool
  | .entry (.live cell _) => cell.kind == kindMember || cell.kind == kindGrant || cell.kind == kindAuthority
  | _ => false

/-- Follow's World is a step-0 World of members, grants and the authority: no step folded, and every
cell a member cell, a World grant or the authority cell. Two Worlds follow can hold are that: the one a genesis builds, a joiner's
before its adopt (`genesisWorld_atGenesis`: the founders' cells are there at step 0, so "no cell"
refused every honest adopt), and one carried at height 0 (`carryWorld_atGenesis`: `carryWorld` sets
`steps` to the carried height), a re-invited member's. It is NOT "a World this joiner's genesis
built" (PROTOCOL-67 as amended). Either holds no object (`atGenesis_object`), so no package fact is
about it. An adopt replaces follow's World only then (`notAtGenesis`), checked at `start` and again at
the step that adopts (PROTOCOL-67). -/
def atGenesis (w : World D) : Bool :=
  w.steps == 0 && w.trie.toList.all fun p => genesisLeaf p.2

def start (X : Ctx D) (me : Self D) (f : Follow D) (argv : List ByteArray) : Reply :=
  let w := f.world
  -- every verb but `init` and `adopt`: the envelope, signed for follow's own height + window
  let catchUp : Reply :=
    let upTo := w.height + me.window
    next (D := D) ⟨argv, 1, [Text.u64 w.steps, Text.u64 0, Text.u64 upTo, Text.u64 0]⟩ fun k =>
      .sign (envelopeMessage X me w.steps upTo) k
  match parse X.digestOf argv with
  | .error r => refusedAt X (.parse r)
  | .ok (.init _) => next (D := D) ⟨argv, 1, []⟩ fun k => .sign whoami k
  | .ok (.adopt inv key) =>
      match adoptPin X me inv key with
      | .error r => refused (D := D) r
      | .ok i =>
      let pin := i.pin
      if !atGenesis w then refused (D := D) (.thin (.notAtGenesis w.steps)) else
      if pin.steps ≤ w.steps then refused (D := D) (.thin (.notBehind w.steps)) else
      let off := Thin.offset pin f.download
      -- the pin names a log position, not a height, and follow is at genesis: sign one window
      -- from height 0; a writer further on refuses it `expired` with its height and follow
      -- re-signs once (`reSign`)
      let upTo := me.window
      next (D := D) ⟨argv, 6, [Text.u64 off, Text.u64 0, Text.u64 upTo, Text.u64 0]⟩ fun k =>
        .sign (adoptEnvelope X me upTo off) k
  -- `sync --to` / `--check`: a position follow is already past cannot be compared on the way (its
  -- World holds only the current chain): refused `ahead`, and nothing is sent. A `--check` whose
  -- bytes do not verify is refused by name before anything is sent
  | .ok (.sync (.to steps _)) =>
      if steps ≤ w.steps then refused (D := D) (.ahead steps) else catchUp
  | .ok (.sync (.check b)) =>
      match Head.verified X me.world b with
      | .error r => refused (D := D) (.attest r)
      | .ok a => if a.head.steps ≤ w.steps then refused (D := D) (.ahead a.head.steps) else catchUp
  | .ok _ => catchUp

/-- Step 4 of a command that submitted a call: `settled`; under any other verb `badState` (a phase-4
continuation is the client's bytes, never a witness, `submits`). -/
def settleStep (X : Ctx D) (me : Self D) (w : World D) (cmd : Cmd D) (out cb result : ByteArray) : Reply :=
  if submits cmd then settled X me w out cb result else refused (D := D) .badState

/-- `cancel CALL`, phase 9: custody's signature over the call's cancel message, decided on follow's
own World by the writer's own function (`Receive.cancel`) BEFORE anything is sent. A cancel that
World records is relayed as the `cancel` op, its payload THE tag-2 encoding (`cancelEvent`, the
bytes the log will serve); one it declines is refused here by the kernel's name (a cancel of a call
that is not the member's own is `badSignature`, one outside the call's window `outsideWindow`, one
already recorded `refusedFinal`) and never sent (`Proofs.Command.sendCancel_host`). -/
def sendCancel (X : Ctx D) (w : World D) (argv : List ByteArray) (cb result : ByteArray) : Reply :=
  match Signed.ofBytes result, X.decodeCall cb with
  | some s, some c =>
      match Receive.cancel X w c s.signature with
      | .recorded .. => next (D := D) ⟨argv, 10, []⟩ fun k => .host .cancel (cancelEvent s.signature cb) k
      | .declined (.refused r) => refusedAt X (.receive r)
      | .declined (.rejected r) => refusedAt X (.reject r)
      | .admitted .. => refused (D := D) .badState
  | none, _ => refused (D := D) .badResult
  | _, none => refused (D := D) .badCall

/-- Bits 2 and 3 of an envelope phase's `tried`, set only on `cancel CALL`'s second catch-up: the
writer answered the cancel `refused cancelled` (it says it recorded the cancel) or `ok` (it says the
call was already admitted), and this catch-up is the member's settlement of that answer on its OWN
World (PROTOCOL-71). Disjoint from `expiredBit` and `incomingBit`, which `envelopeRefused` ORs in. -/
def saidCancelledBit : Nat := 4
def saidCommittedBit : Nat := 8

/-- `cancel CALL`'s second catch-up, from follow's own World as `start` begins one, its `tried`
naming the writer's claim `said` (`saidCancelledBit` or `saidCommittedBit`). -/
def cancelCatchUp (X : Ctx D) (me : Self D) (w : World D) (argv : List ByteArray) (said : Nat) : Reply :=
  let upTo := w.height + me.window
  next (D := D) ⟨argv, 1, [Text.u64 w.steps, Text.u64 0, Text.u64 upTo, Text.u64 said]⟩ fun k =>
    .sign (envelopeMessage X me w.steps upTo) k

/-- `cancel CALL`, phase 10: the writer's answer to the `cancel` op (HOST-18's Serve arm). Its two
final claims are the writer's word, never the member's (PROTOCOL-46, PROTOCOL-71): `refused
cancelled` (the cancel recorded) and `ok` (the call already admitted, so the cancel did nothing) each
start a second catch-up from follow's own World, its `tried` naming the claim (`saidCancelledBit`,
`saidCommittedBit`), and the command ends at its tip by follow's own settlement (`cancelSettled`).
A decline ends it `declined NAME` (nothing recorded); any other refusal `refused NAME`; `uncertain
NAME` (the journal no longer answers) ends it `uncertain`. -/
def cancelAnswer (X : Ctx D) (me : Self D) (w : World D) (argv : List ByteArray) (result : ByteArray) :
    Reply :=
  match hostReply result with
  | some (.refused, p) =>
      if hostName p = (Receive.Refusal.cancelled : Receive.Refusal D).name then
        cancelCatchUp X me w argv saidCancelledBit
      else refusedAt X (.host (hostName p))
  | some (.ok, _) => cancelCatchUp X me w argv saidCommittedBit
  | some (.declined, p) => declined (hostName p)
  | some (.uncertain, p) =>
      .done CommandExit.uncertain.code.toUInt8 ByteArray.empty s!"uncertain {hostName p}\n".toUTF8
  | _ => refused (D := D) .badResult

/-- The code a recorded cancel carries (`Receive.cancel` records `refused cancelled`). -/
def cancelledCode : Nat := (Receive.Verdict.refused (Receive.Refusal.cancelled) : Receive.Verdict D).code

/-- `cancel CALL` at the tip of its second catch-up: the writer's claim (`saidCancelled`: the cancel
recorded; else the call admitted) checked against follow's own settlement of the call on the World it
just caught up to (PROTOCOL-71, the class PROTOCOL-64 closed at step 4). `ok`, printing `cancelled
TXID`, only when the writer said cancelled AND that World settles the call `refused cancelled`;
`refused committed` only when the writer said admitted AND that World settles it committed; anything
else `hostContradicted CLAIM FOLLOWSAID` (`attemptContradicted`), the call's attempt left open. -/
def cancelSettled (X : Ctx D) (me : Self D) (w : World D) (c : Call D) (saidCancelled : Bool) : Reply :=
  match saidCancelled, settleOf X me w c with
  | true, .refused code =>
      if code = cancelledCode (D := D) then printed s!"cancelled {hex X (txIdOf X c)}\n"
      else attemptContradicted X "cancelled" (some (.refused code))
  | false, .committed .. => refusedAt X (.host "committed")
  | true, v => attemptContradicted X "cancelled" (some v)
  | false, v => attemptContradicted X "committed" (some v)

/-- `cancel CALL` at the tip of a catch-up: the first one (no claim in `tried`) asks custody to sign the
cancel message, phase 9; the second one (`tried` names the writer's claim) ends by follow's own
settlement (`cancelSettled`, PROTOCOL-71). -/
def cancelTip (X : Ctx D) (me : Self D) (w : World D) (argv : List ByteArray) (cb triedB : ByteArray) : Reply :=
  match X.decodeCall cb, Text.ofU64 triedB with
  | none, _ => refused (D := D) .badCall
  | some _, none => refused (D := D) .badState
  | some c, some t =>
      if t &&& (saidCancelledBit ||| saidCommittedBit) = 0 then
        next (D := D) ⟨argv, 9, []⟩ fun k => .sign (X.cancelMessage c) k
      else cancelSettled X me w c (t &&& saidCancelledBit ≠ 0)

/-- Did the state ask custody for `signIncoming`? An envelope phase (1) whose `tried` has the
incoming bit. It holds EXACTLY when the step that handed the state on asked `signIncoming`:
`Proofs.Incoming.step_signIncoming_asked` (every `signIncoming` comes with it) and
`step_asked_signIncoming` (it comes only with `signIncoming`). -/
def askedIncoming (st : State) : Bool :=
  st.phase == 1 && match st.tried with
    | some t => t &&& incomingBit != 0
    | none => false

/-- A refused custody step ends the command (ROOT's rule (a), PROTOCOL-56): a refusal of the
`signIncoming` step hands back the writer's own refusal (`unknownKeyEnd`), whatever custody's name
was; every other custody refusal ends it by custody's name. -/
def custodyEnd (X : Ctx D) (cmd : Cmd D) (st : State) : Refusal D → Reply
  | .custody c => if askedIncoming st then unknownKeyEnd X cmd else refused (D := D) (.custody c)
  | r => refused (D := D) r

/-- One step: the continuation, the result of the step it asked for, and follow's state. It
answers follow's state after the step, what to persist (a log page's Turns, re-derived; a base it
adopted; `[]` for every other step), and the next reply. `B` is how an adopted base is read
(its World codec and the digest a pin names); `dc` is the digest codec a receipt is written in. -/
def step (X : Ctx D) (dc : Stream D) (B : Thin.Base (World D)) (me : Self D) (f : Follow D) (kb result : ByteArray) :
    Follow D × Persist D × Reply :=
  let w := f.world
  let same (r : Reply) : Follow D × Persist D × Reply := (f, .steps [], r)
  match State.ofBytes kb, parse X.digestOf ((State.ofBytes kb).map (·.argv) |>.getD []) with
  | none, _ => same (refused (D := D) .badState)
  | some _, .error r => same (refused (D := D) (.parse r))
  | some st, .ok cmd =>
      let again (phase : UInt8) (acc : List ByteArray) (f : ByteArray → Reply) : Reply :=
        next (D := D) ⟨st.argv, phase, acc⟩ f
      -- the phases that asked custody (sign, signNext, precommit) get `status ‖ payload` from it:
      -- a refusal ends the command by custody's name, an ok hands on its payload
      let isInit := match cmd with | .init _ => true | _ => false
      match stepResult (D := D) isInit st.phase result with
      | .error r => same (custodyEnd X cmd st r)
      | .ok result =>
      match cmd, st.phase, st.acc with
      -- init: learn the key, sign the possession, print the token
      | .init sponsor, 1, [] =>
          match Signed.ofBytes result with
          | none => same (refused (D := D) .badResult)
          | some s =>
              same (again 2 [result] fun k =>
                .sign (possessionMessage X sponsor (nextKeyDigest X s.next) s.key) k)
      | .init _, 2, [first] =>
          match Signed.ofBytes first, Signed.ofBytes result with
          | some s0, some s1 =>
              if s1.key = s0.key then
                same (printed s!"join {Text.toHex (Join.bytes X.env.bytes
                  { key := s0.key, next := nextKeyDigest X s0.next, possession := s1.signature })}\n")
              else same (refused (D := D) .badResult)
          | _, _ => same (refused (D := D) .badResult)
      -- every other verb: the envelope, signed; ask for the log (page `pages` of this command)
      | _, 1, [startB, pagesB, upToB, triedB] =>
          match Signed.ofBytes result, Text.ofU64 startB, Text.ofU64 upToB with
          | some s, some h, some upTo =>
              match Envelope.bytes X (envelopeOf me h upTo s) with
              | some p => same (again 2 [startB, result, pagesB, upToB, triedB] fun k => .host .log p k)
              | none => same (refused (D := D) .badState)
          | _, _, _ => same (refused (D := D) .badResult)
      -- the log: absorb the page; page again until the tip; then read, or plan and ask for the
      -- signature
      | _, 2, [startB, signedB, pagesB, upToB, triedB] =>
          match hostReply result with
          | some (.ok, p) =>
              match logPage p, Text.ofU64 pagesB with
              | none, _ | _, none => same (refused (D := D) .badResult)
              | some pg, some pages =>
                  -- a page short of the tip that carries nothing would be asked for again forever
                  if pg.events.isEmpty && pg.steps < pg.tipSteps then same (refused (D := D) .badResult) else
                  match absorbSync X me cmd w pg.events pg.steps pg.chain pg.baseSteps with
                  | .error r => same (refused (D := D) r)
                  | .ok (w', ts, wb) =>
                      -- follow's own World at the writer's stated base, its digest by the one
                      -- digest a pin names; the newest such base replaces the last (PROTOCOL-47)
                      let v := match wb with
                        | some wb => some (wb.steps, B.digest (B.world.bytes wb))
                        | none => f.verified
                      let moved (w' : World D) (ts : List (Kernel.Step D × D)) (r : Reply) :
                          Follow D × Persist D × Reply :=
                        ({ f with world := w', verified := v }, .steps ts, postOr X w ts w' r)
                      if pg.steps < pg.tipSteps then
                        if Bounds.pagesPerCommandMax ≤ pages + 1 then
                          moved w' ts (behind pg.steps pg.tipSteps)
                        -- the next envelope covers the tip the writer stated, so a follower
                        -- behind by more than a window is not refused on every page
                        else moved w' ts (again 1 [Text.u64 pg.steps, Text.u64 (pages + 1),
                            Text.u64 (pg.tipHeight + me.window), triedB] fun k =>
                          envelopeSign ((Text.ofU64 triedB).getD 0)
                            (envelopeMessage X me pg.steps (pg.tipHeight + me.window)) k)
                      else
                      match cmd, Signed.ofBytes signedB with
                      | .read obj ex, _ => moved w' ts (render X w' obj ex)
                      | .describe obj, _ => moved w' ts (describe X w' obj)
                      | .rangeRead obj rel k pre, _ => moved w' ts (rangeRender X w' obj rel k pre)
                      | .sync mode, _ => moved w' ts (syncTip X me w' st.argv signedB mode)
                      -- the receipt for a signed call, against the World follow just caught up to,
                      -- and the member's settlement of it (PROTOCOL-46)
                      | .receipt cb, _ => moved w' ts (receiptLines X dc me w' cb)
                      -- cancel: custody signs the cancel message of the call (`domCancel ‖ txId`)
                      -- cancel: custody signs the cancel message of the call (`domCancel ‖ txId`);
                      -- after the writer's final answer, follow settles it here (`cancelTip`)
                      | .cancel cb, _ => moved w' ts (cancelTip X me w' st.argv cb triedB)
                      | .rotate, some _ => moved w' ts (again 5 [] fun k => .precommit k)
                      -- invite: the inputs make this World; pin the newest base follow verified
                      -- itself (`pinOf`), sign with the key the writer just took for this
                      -- member's envelope
                      | .invite input, some s =>
                          match inviteInput X me input with
                          | .error r => moved w' ts (refused (D := D) r)
                          | .ok () =>
                          match pinOf v pg.baseSteps pg.baseDigest with
                          | .error r => moved w' ts (refusedAt X (.invite r))
                          | .ok pin =>
                            match Invite.unsignedBytes X input pin me.member s.key with
                            | none => moved w' ts (refused (D := D) .badState)
                            | some u => moved w' ts (again 8 [signedB, u] fun k => .sign (Invite.message u) k)
                      | _, some s => match body X me w' s cmd, signedReads X w' cmd with
                        | .error r, _ => moved w' ts (refusedAt X r)
                        | _, .error r => moved w' ts (refusedAt X r)
                        | .ok b, .ok rs =>
                          match plan X me w' s.key rs b with
                          | .error r => moved w' ts (refusedAt X r)
                          | .ok u => moved w' ts (again 3 [signedB, X.callMessage u] fun k =>
                              .sign (X.callMessage u) k)
                      | _, none => moved w' ts (refused (D := D) .badState)
          | some (.refused, p) => same (envelopeRefused X me st.argv cmd startB pagesB upToB triedB p)
          | _ => same (refused (D := D) .badResult)
      -- the call's signature: re-plan, compare with what was signed, check the call reads back, submit
      | _, 3, [signedB, ub] =>
          match Signed.ofBytes signedB, Signed.ofBytes result with
          | some s, some s2 => match body X me w s cmd, signedReads X w cmd with
            | .error r, _ => same (refused (D := D) r)
            | _, .error r => same (refused (D := D) r)
            | .ok b, .ok rs =>
              if s2.key ≠ s.key then same (refused (D := D) .badResult) else
              match plan X me w s.key rs b with
              | .error r => same (refusedAt X r)
              | .ok u =>
                  if X.callMessage u ≠ ub then same (refused (D := D) .planMoved) else
                  let c : Call D := ⟨u, s2.signature⟩
                  -- the bytes submitted read back as THIS call, or the World would judge another
                  if X.decodeCall (X.callBytes c) ≠ some c then same (refused (D := D) .badCall) else
                  match receive X w c with
                  | .error r => same (refusedAt X (.receive r))
                  | .ok t => same (again 4 [(receipt X t).toUTF8, X.callBytes c] fun k =>
                      .submit (X.callBytes c) k)
          | _, _ => same (refused (D := D) .badResult)
      -- rotate: custody's next and pending keys; plan the rotation to `next`, signed by `next`
      | .rotate, 5, [] =>
          match precommitOf result with
          | none => same (refused (D := D) .badResult)
          | some (nk, pk) =>
              let s : Signed := ⟨nk, pk, ByteArray.empty⟩
              match s.bytes, body X me w s .rotate with
              | some sb, .ok b =>
                  match plan X me w s.key {} b with
                  | .error r => same (refused (D := D) r)
                  | .ok u => same (again 3 [sb, X.callMessage u] fun k =>
                      .signNext (X.callMessage u) k)
              | _, _ => same (refused (D := D) .badState)
      -- `sync --attest`: custody's signature over follow's own head; printed `attest HEX`
      | .sync .attest, 11, [signedB, u] => same (attestDone (D := D) signedB u result)
      -- the settlement, of a call this command submitted
      | cmd, 4, [out, cb] => same (settleStep X me w cmd out cb result)
      -- cancel: custody's signature, decided on follow's own World before it is sent
      | .cancel cb, 9, [] => same (sendCancel X w st.argv cb result)
      -- cancel: the writer's answer; its final claims are settled by a second catch-up
      | .cancel _, 10, [] => same (cancelAnswer X me w st.argv result)
      -- adopt: the envelope for the page at `off`, signed; ask for the base page
      | .adopt _ _, 6, [offB, pagesB, upToB, triedB] =>
          match Signed.ofBytes result, Text.ofU64 offB, Text.ofU64 upToB with
          | some s, some off, some upTo =>
              match Envelope.bytes X (envelopeOf me off upTo s) with
              | some p => same (again 7 [offB, pagesB, upToB, triedB] fun k => .host .read p k)
              | none => same (refused (D := D) .badState)
          | _, _, _ => same (refused (D := D) .badResult)
      -- adopt: one base page, decided by `Thin.accept`; the next page, or the World adopted
      | .adopt inv key, 7, [offB, pagesB, upToB, triedB] =>
          match adoptPin X me inv key with
          | .error r => same (refused (D := D) r)
          | .ok i =>
          let pin := i.pin
          let drop (r : Thin.Refusal) : Follow D × Persist D × Reply :=
            ({ f with download := none }, .steps [], refusedAt X (.thin r))
          match Text.ofU64 offB, Text.ofU64 pagesB, Text.ofU64 upToB, Text.ofU64 triedB with
          | some off, some pages, some upTo, some tried =>
            match hostReply result with
            | some (.ok, p) =>
                match Thin.Page.ofBytes p with
                | none => drop .badPage
                | some page =>
                    if off ≠ Thin.offset pin f.download then drop .pageMismatch else
                    match Thin.accept B pin f.download page with
                    | .error r => drop r
                    | .ok (.done w') =>
                        -- adopt replaces follow's World: only one that still holds nothing. `start`
                        -- checked it, but other commands' pages may have moved it since, and a
                        -- continuation is no witness of what `start` saw (HOSTING-43)
                        if !atGenesis w then drop (.notAtGenesis w.steps) else
                        -- the pin binds the World's bytes, origin included; this says so by name
                        if w'.origin ≠ me.world then drop .wrongWorld else
                        -- the writer's certificate of the base, under the base's own authority
                        -- (PROTOCOL-77.1): asked only when that authority names certifiers
                        match Head.certifiesWorld X w' page.certificate with
                        | .error r => ({ f with download := none }, .steps [], refusedAt X (.certified r))
                        | .ok () =>
                        ({ world := w', download := none, verified := none }, .adopt w',
                          printed s!"adopted {pin.steps} {Text.toHex pin.digest}\n")
                    | .ok (.more d) =>
                        let f' := { f with download := some d }
                        if Bounds.pagesPerCommandMax ≤ pages + 1 then
                          (f', .steps [], refused (D := D) (.thin (.incomplete d.got.size d.total)))
                        else (f', .steps [], again 6 [Text.u64 d.got.size, Text.u64 (pages + 1), upToB, triedB]
                          fun k => .sign (adoptEnvelope X me upTo d.got.size) k)
            | some (.refused, p) =>
                match expiredHeight? p with
                | none => same (if p = pageIoName.toUTF8 then notServed else refused (D := D) (.host (hostName p)))
                | some height =>
                    match reSign (D := D) me (tried ≠ 0) upTo height with
                    | .error r => same (refused (D := D) r)
                    | .ok upTo' => same (again 6 [offB, pagesB, Text.u64 upTo', Text.u64 1] fun k =>
                        .sign (adoptEnvelope X me upTo' off) k)
            | _ => same (refused (D := D) .badResult)
          | _, _, _, _ => same (refused (D := D) .badState)
      -- invite: custody's signature over the invitation, by the key the envelope was signed with
      | .invite _, 8, [signedB, u] =>
          match Signed.ofBytes signedB, Signed.ofBytes result with
          | some s, some s2 =>
              if s2.key ≠ s.key then same (refused (D := D) .badResult) else
              -- custody's signature is checked here, not first at the joiner
              if !X.verify s2.key (Invite.message u) s2.signature then same (refused (D := D) .badResult) else
              match Invite.bytes u s2.signature with
              | some b => same (printed s!"invite {Text.toHex b}\n")
              | none => same (refused (D := D) .badState)
          | _, _ => same (refused (D := D) .badResult)
      | _, _, _ => same (refused (D := D) .badState)

end Nanodregg.Protocol.Command
