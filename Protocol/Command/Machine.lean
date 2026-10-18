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

`invite INPUT` (PROTOCOL-42) catches up, checks that INPUT makes the member's own World, pins that
World (its step count, the digest of its bytes) and has custody sign the invitation; it prints
`invite HEX`.

`adopt INVITE KEY` (thin consent, PROTOCOL-14 A) takes its pin from an invitation `Invite.accept`
accepts under the sponsor key KEY, and pages the writer's newest base with `read`, one
signed envelope per page, `Protocol.Thin.accept` deciding each page; the download so far lives in
follow's state (`Follow.download`, memory only), and an adopted base replaces follow's World and is
handed back as `Persist.adopt` for follow to seal as its own newest base. From there every command
catches up from the base's step count like any other.

The log is a list of STEPS (KERNEL-47): admitted Turns and recorded refusals. Log positions count
steps, and follow binds on (steps, chain), as the kernel's `fold_reaches_host` does. Envelope windows
stay in heights: the page states the writer's tip in both units (PROTOCOL-41).

`k` holds only the argv, the phase and the results so far; every plan is RE-DERIVED from follow's
World at each step and the bytes it signs are compared with the ones custody signed (`planMoved`),
so `k` cannot steer what is signed (HOST-9's `resume_rederives`). A plan is offered for signature
only if follow's own World admits the Turn it derives (consent: `Protocol.Proofs.Command`).
-/
import Kernel.Receive.Submit
import Protocol.Command.Verb
import Protocol.Envelope
import Protocol.Invite
import Protocol.Command.Describe
import Protocol.Receipt
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
  /-- the logged step at this log position does not re-derive on follow's World: a Turn event that
  does not derive, or a refusal event that `Receive.judge` does not record (a kernel rejection of a
  derived Turn is refused by the kernel's own name, `reject`) -/
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

/-- A step answered to the client. -/
inductive Reply
  | done (exit : UInt8) (out err : ByteArray)
  | sign (message k : ByteArray)
  | host (op : Op) (payload k : ByteArray)
  | submit (call k : ByteArray)
  | precommit (k : ByteArray)
  | signNext (message k : ByteArray)
  deriving Inhabited

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

/-! ## Follow's state -/

/-- What `host follow` holds between frames: its World, and a base download in progress (thin
consent: in memory only, never persisted, so a restarted follow starts the download again). -/
structure Follow (D : Type) [Ord D] where
  world : World D
  download : Option Thin.Download := none

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

/-- The phases whose result is custody's: 1 (an envelope's or init's signature), 2 for `init`
only (its possession signature; every other verb's phase 2 is a `log` reply), 3 (a call's
signature, by `sign` or `signNext`), 5 (`precommit`), 6 (an adopt envelope's signature), 8 (an
invitation's signature). -/
def custodyPhase (isInit : Bool) (phase : UInt8) : Bool :=
  phase == 1 || phase == 3 || phase == 5 || phase == 6 || phase == 8 || (isInit && phase == 2)

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
  | .invoke o m a via => do
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
  | .init _ | .read _ _ | .describe _ | .adopt _ _ | .sync | .invite _ | .receipt _ => .error .badState

/-- Derive with the signature not yet known, pinning each cell the derivation asks for. -/
def derivePins (X : Ctx D) (w : World D) : Nat → Unsigned D → Except (Refusal D) (Unsigned D × Turn D)
  | 0, _ => .error .tooManyPins
  | fuel + 1, u =>
      let look := pinned X.env w u.pins
      match (do keyRule look u; deriveTurn X look ⟨u, ByteArray.empty⟩) with
      | .error (.unpinned c) =>
          derivePins X w fuel { u with pins := u.pins ++ [(c, pinOf X.env (w.live X.env c))] }
      | .error r => .error (.receive r)
      | .ok t => .ok (u, t)

/-- The call a member's body derives to on follow's World, with every pin it read and its price the
derived charge plus headroom, and the Turn it derives: `plan` before follow's own admission. A
client that skips that admission (a hostile one: the rows' `forge` act) signs exactly this. -/
def planUnchecked (X : Ctx D) (me : Self D) (w : World D) (key : ByteArray) (b : Body D) :
    Except (Refusal D) (Unsigned D × Turn D) := do
  let u0 : Unsigned D :=
    -- the invitation's World (KERNEL-24): follow's own `receive` below refuses `wrongWorld` if
    -- the World it follows is not that one, so it never signs a call for another World
    { world := me.world
      member := me.member
      key := key
      notBefore := w.height
      validUntil := w.height + me.window
      pins := []
      -- a ceiling no Turn exceeds (`admit_weight`), so the derivation reports the charge rather
      -- than refusing `overPrice`; the signed price is set from that charge below
      maxCharge := Kernel.Bounds.weightMax
      body := b }
  let (u1, t1) ← derivePins X w Kernel.Bounds.touchesMax u0
  let u := { u1 with maxCharge := t1.charge + chargeSlack }
  match deriveTurn X (pinned X.env w u.pins) ⟨u, ByteArray.empty⟩ with
  | .error r => .error (.receive r)
  | .ok t => .ok (u, t)

/-- The call follow asks custody to sign: `planUnchecked`, and only if follow's World admits the
Turn it derives. -/
def plan (X : Ctx D) (me : Self D) (w : World D) (key : ByteArray) (b : Body D) :
    Except (Refusal D) (Unsigned D) :=
  match planUnchecked X me w key b with
  | .error r => .error r
  | .ok (u, t) => match World.admit X.env w t with
    | .error r => .error (.reject r)
    | .ok _ => .ok u

/-! ## Catching up -/

/-- The step a page event states: byte 0 then the signed call of an admitted Turn, byte 1 then
the signed call of a recorded refusal (PROTOCOL-41). -/
def eventTurn : UInt8 := 0
def eventRefusal : UInt8 := 1

/-- Re-derive one logged step on follow's World by the Host's own decision functions: a Turn event
by `Receive.submit` (receive, then admit), a refusal event by `Receive.judge`, which must RECORD it
(the follower's `auditRefusal` rule). A Turn that derives but the kernel rejects is refused by the
kernel's name (a writer that admits a call it recorded refused is caught `refusedFinal`); anything
else that does not re-derive is `eventMismatch` at its log position. -/
def absorbStep (X : Ctx D) (w : World D) (e : ByteArray) : Except (Refusal D) (Kernel.Step D × World D) :=
  let pos := w.steps + 1
  if h : 0 < e.size then
    match X.decodeCall (e.extract 1 e.size) with
    | none => .error (.eventMismatch pos)
    | some c =>
        if e[0] = eventTurn then
          match submit X w c with
          | .ok (t, w') => .ok (.turn t, w')
          | .error (.rejected r) => .error (.reject r)
          | .error (.refused _) => .error (.eventMismatch pos)
        else if e[0] = eventRefusal then
          match judge X w c with
          | .recorded _ r w' => .ok (.refusal r, w')
          | _ => .error (.eventMismatch pos)
        else .error (.eventMismatch pos)
  else .error (.eventMismatch pos)

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

def logPage (b : ByteArray) : Option LogPage :=
  match logReplyFrame.decode b with
  | .ok (l, n, c, t, th, ()) => do
      let steps ← Text.ofU64 n.1
      let tipSteps ← Text.ofU64 t.1
      let tipHeight ← Text.ofU64 th.1
      if steps ≤ tipSteps then some ⟨Text.unlist l, steps, c.1, tipSteps, tipHeight⟩ else none
  | .error _ => none

/-- Absorb a page and require follow's fold to reach the writer's stated step count and chain (the
pair the kernel's `fold_reaches_host` binds). A page of more steps than `Bounds.pageStepsMax` (one
follower record) is refused `pageTooLong` before any of it is absorbed (HOST-41). -/
def absorbPage (X : Ctx D) (w : World D) (evs : List ByteArray) (steps : Nat) (chain : ByteArray) :
    Except (Refusal D) (World D × List (Kernel.Step D × D)) :=
  if Bounds.pageStepsMax < evs.length then .error (.pageTooLong evs.length) else do
  let (w', ts) ← absorb X w #[] evs
  if w'.steps = steps ∧ X.env.bytes w'.chain = chain then pure (w', ts.toList)
  else throw (.chainMismatch steps)

def hostName (p : ByteArray) : String := (String.fromUTF8? p).getD "unnamed"

def whoami : ByteArray := "nanodregg/protocol/whoami/v1".toUTF8

/-! ## Rendering -/

def hex (X : Ctx D) (d : D) : String := Text.toHex (X.env.bytes d)

/-- `read`: the object's state slots, one `KEY=VALUE` line each (keys relative to `stateBase`),
after every expectation holds. -/
def render (E : Env D) (w : World D) (obj : D) (expect : List (Nat × ByteArray)) : Reply :=
  match w.live E obj with
  | none => refused (D := D) (.missingCell obj)
  | some cell =>
      match expect.find? fun (k, v) => cell.slots.get (stateBase + k) != some v with
      | some (k, _) => refused (D := D) (.expect k)
      | none =>
          printed (String.join ((stateOf cell).map fun (k, v) =>
            s!"{k - stateBase}={(String.fromUTF8? v).getD (Text.toHex v)}\n"))

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
      match packageLines (D := D) pk with
      | some ls => pure (s!"package {hex X p}" :: ls)
      | none => throw .noText
  let ls ← laws.mapM fun l => do
    let lp ← (Lang.readPackage look l).mapError .receive
    pure (s!"law {hex X l}" ++ String.join (lp.laws.map (" " ++ ·)))
  pure (ps ++ ls)

/-- `read OBJ ?`: the object's self-description (`Command.Describe`), on follow's caught-up World. -/
def describe (X : Ctx D) (w : World D) (obj : D) : Reply :=
  match w.live X.env obj with
  | none => refused (D := D) (.missingCell obj)
  | some cell =>
    let head := s!"object {hex X obj}\n" ++
      ((cell.slots.get slotOwner).map fun o => s!"owner {Text.toHex o}\n").getD ""
    match describeLines X w obj cell with
    | .ok ls => printed (head ++ String.join (ls.map (· ++ "\n")))
    | .error r => refused (D := D) r

/-- What to do next, for the refusals that have an answer (DELVETALK-LEARNINGS §4.3): printed on
stdout beside `refused NAME` on stderr, so the name stays the verdict and the hint is text. -/
def hint (X : Ctx D) : Refusal D → Option String
  | .reject (.stale c) => some s!"hint stale {hex X c}: this cell moved under the call; read it and run the command again"
  -- the law's own words (at most `Lang.reasonMax` bytes), on ONE line: a law cannot add lines
  | .receive (.lawDenied l why) => some s!"hint lawDenied {hex X l}: {(why.replace "\n" " ").replace "\r" " "}"
  | .host "stale" => some "hint stale: the World moved before the call landed; run the command again (it re-plans)"
  | .thin (.baseMoved _) => some "hint baseMoved: the writer's newest base is not at the invitation's pin; ask your sponsor for a fresh invitation"
  | .host "lawDenied" => some "hint lawDenied: a law refused the call; `read OBJ ?` names the object's laws"
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

/-- The pin an `adopt` takes: that of an invitation `Invite.accept` accepts under the trusted `key`,
to the member's own World (re-derived at every step from the argv, like every plan). -/
def adoptPin (X : Ctx D) (me : Self D) (inv key : ByteArray) : Except (Refusal D) (Invite.Invitation D) :=
  match Invite.accept X key inv with
  | .error r => .error (.invite r)
  | .ok (i, g) => if g.origin = me.world then .ok i else .error (.invite .otherWorld)

/-- `invite`'s check of its INPUT: the inputs decode and make the member's own World. -/
def inviteInput (X : Ctx D) (me : Self D) (input : ByteArray) : Except (Refusal D) Unit :=
  match genesisInput.decode input with
  | .error _ => .error (.invite .badInvitation)
  | .ok (name, nonce, allowance, fs) =>
    match Invite.foundersOf X fs with
    | none => .error (.invite .badInvitation)
    | some founders =>
      if originOf X name nonce allowance founders = me.world then .ok () else .error (.invite .otherWorld)

def start (X : Ctx D) (me : Self D) (f : Follow D) (argv : List ByteArray) : Reply :=
  let w := f.world
  match parse X.digestOf argv with
  | .error r => refused (D := D) (.parse r)
  | .ok (.init _) => next (D := D) ⟨argv, 1, []⟩ fun k => .sign whoami k
  | .ok (.adopt inv key) =>
      match adoptPin X me inv key with
      | .error r => refused (D := D) r
      | .ok i =>
      let pin := i.pin
      if w.steps ≠ 0 then refused (D := D) (.thin (.notAtGenesis w.steps)) else
      if pin.steps ≤ w.steps then refused (D := D) (.thin (.notBehind w.steps)) else
      let off := Thin.offset pin f.download
      -- the pin names a log position, not a height, and follow is at genesis: sign one window
      -- from height 0; a writer further on refuses it `expired` with its height and follow
      -- re-signs once (`reSign`)
      let upTo := me.window
      next (D := D) ⟨argv, 6, [Text.u64 off, Text.u64 0, Text.u64 upTo, Text.u64 0]⟩ fun k =>
        .sign (adoptEnvelope X me upTo off) k
  | .ok _ =>
      let upTo := w.height + me.window
      next (D := D) ⟨argv, 1, [Text.u64 w.steps, Text.u64 0, Text.u64 upTo, Text.u64 0]⟩ fun k =>
        .sign (envelopeMessage X me w.steps upTo) k

/-- One step: the continuation, the result of the step it asked for, and follow's state. It
answers follow's state after the step, what to persist (a log page's Turns, re-derived; a base it
adopted; `[]` for every other step), and the next reply. `B` is how an adopted base is read
(its World codec and the digest a pin names). -/
def step (X : Ctx D) (B : Thin.Base (World D)) (me : Self D) (f : Follow D) (kb result : ByteArray) :
    Follow D × Persist D × Reply :=
  let w := f.world
  let same (r : Reply) : Follow D × Persist D × Reply := (f, .steps [], r)
  let moved (w' : World D) (ts : List (Kernel.Step D × D)) (r : Reply) : Follow D × Persist D × Reply :=
    ({ f with world := w' }, .steps ts, r)
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
      | .error r => same (refused (D := D) r)
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
                  match absorbPage X w pg.events pg.steps pg.chain with
                  | .error r => same (refused (D := D) r)
                  | .ok (w', ts) =>
                      if pg.steps < pg.tipSteps then
                        if Bounds.pagesPerCommandMax ≤ pages + 1 then
                          moved w' ts (behind pg.steps pg.tipSteps)
                        -- the next envelope covers the tip the writer stated, so a follower
                        -- behind by more than a window is not refused on every page
                        else moved w' ts (again 1 [Text.u64 pg.steps, Text.u64 (pages + 1),
                            Text.u64 (pg.tipHeight + me.window), triedB] fun k =>
                          .sign (envelopeMessage X me pg.steps (pg.tipHeight + me.window)) k)
                      else
                      match cmd, Signed.ofBytes signedB with
                      | .read obj ex, _ => moved w' ts (render X.env w' obj ex)
                      | .describe obj, _ => moved w' ts (describe X w' obj)
                      | .sync, _ => moved w' ts (printed
                          s!"height {w'.height}\nchain {hex X w'.chain}\nroots {hex X (w'.roots X.env)}\n")
                      -- the receipt for a transaction id, against the World follow just caught up to
                      | .receipt tx, _ => moved w' ts (match Receipt.bytes X.env (Receipt.build X.env w' tx) with
                          | some b => printed s!"receipt {Text.toHex b}\n"
                          | none => refused (D := D) .badState)
                      | .rotate, some _ => moved w' ts (again 5 [startB, signedB] fun k => .precommit k)
                      -- invite: the inputs make this World; pin it as it stands, sign with the
                      -- key the writer just took for this member's envelope
                      | .invite input, some s =>
                          match inviteInput X me input with
                          | .error r => moved w' ts (refused (D := D) r)
                          | .ok () =>
                            match Invite.unsignedBytes X input ⟨w'.steps, B.digest (B.world.bytes w')⟩
                                me.member s.key with
                            | none => moved w' ts (refused (D := D) .badState)
                            | some u => moved w' ts (again 8 [signedB, u] fun k => .sign (Invite.message u) k)
                      | _, some s => match body X me w' s cmd with
                        | .error r => moved w' ts (refusedAt X r)
                        | .ok b =>
                          match plan X me w' s.key b with
                          | .error r => moved w' ts (refusedAt X r)
                          | .ok u => moved w' ts (again 3 [startB, signedB, X.callMessage u] fun k =>
                              .sign (X.callMessage u) k)
                      | _, none => moved w' ts (refused (D := D) .badState)
          | some (.refused, p) =>
              match expiredHeight? p, Text.ofU64 startB, Text.ofU64 upToB, Text.ofU64 triedB with
              | none, _, _, _ => same (refused (D := D) (.host (hostName p)))
              | some height, some h, some upTo, some tried =>
                  match reSign (D := D) me (tried ≠ 0) upTo height with
                  | .error r => same (refused (D := D) r)
                  | .ok upTo' => same (again 1 [startB, pagesB, Text.u64 upTo', Text.u64 1] fun k =>
                      .sign (envelopeMessage X me h upTo') k)
              | some _, _, _, _ => same (refused (D := D) .badState)
          | _ => same (refused (D := D) .badResult)
      -- the call's signature: re-plan, compare with what was signed, submit
      | _, 3, [startB, signedB, ub] =>
          match Signed.ofBytes signedB, Signed.ofBytes result with
          | some s, some s2 => match body X me w s cmd with
            | .error r => same (refused (D := D) r)
            | .ok b =>
              if s2.key ≠ s.key then same (refused (D := D) .badResult) else
              match plan X me w s.key b with
              | .error r => same (refusedAt X r)
              | .ok u =>
                  if X.callMessage u ≠ ub then same (refused (D := D) .planMoved) else
                  let c : Call D := ⟨u, s2.signature⟩
                  match receive X w c with
                  | .error r => same (refusedAt X (.receive r))
                  | .ok t => same (again 4 [startB, signedB, ub, (receipt X t).toUTF8] fun k =>
                      .submit (X.callBytes c) k)
          | _, _ => same (refused (D := D) .badResult)
      -- rotate: custody's next and pending keys; plan the rotation to `next`, signed by `next`
      | .rotate, 5, [startB, _] =>
          match precommitOf result with
          | none => same (refused (D := D) .badResult)
          | some (nk, pk) =>
              let s : Signed := ⟨nk, pk, ByteArray.empty⟩
              match s.bytes, body X me w s .rotate with
              | some sb, .ok b =>
                  match plan X me w s.key b with
                  | .error r => same (refused (D := D) r)
                  | .ok u => same (again 3 [startB, sb, X.callMessage u] fun k =>
                      .signNext (X.callMessage u) k)
              | _, _ => same (refused (D := D) .badState)
      -- the settlement
      | _, 4, [_, _, _, out] =>
          match hostReply result with
          | some (.ok, _) => same (.done CommandExit.ok.code.toUInt8 out ByteArray.empty)
          | some (.refused, p) => same (refusedAt X (.host (hostName p)))
          | some (.declined, p) => same (declined (hostName p))
          | some (.absent, _) => same (.done CommandExit.absent.code.toUInt8 ByteArray.empty "absent\n".toUTF8)
          | some (.uncertain, _) => same (.done CommandExit.uncertain.code.toUInt8 ByteArray.empty "uncertain\n".toUTF8)
          -- a settlement is never `closed`: the client settles a closed connection by lookup
          | some (.closed, _) | none => same (refused (D := D) .badResult)
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
                        -- the pin binds the World's bytes, origin included; this says so by name
                        if w'.origin ≠ me.world then drop .wrongWorld else
                        ({ world := w', download := none }, .adopt w',
                          printed s!"adopted {pin.steps} {Text.toHex pin.digest}\n")
                    | .ok (.more d) =>
                        let f' := { f with download := some d }
                        if Bounds.pagesPerCommandMax ≤ pages + 1 then
                          (f', .steps [], refused (D := D) (.thin (.incomplete d.got.size d.total)))
                        else (f', .steps [], again 6 [Text.u64 d.got.size, Text.u64 (pages + 1), upToB, triedB]
                          fun k => .sign (adoptEnvelope X me upTo d.got.size) k)
            | some (.refused, p) =>
                match expiredHeight? p with
                | none => same (refused (D := D) (.host (hostName p)))
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
