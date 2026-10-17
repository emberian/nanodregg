/-
# Protocol.Command.Machine — what `host follow` does with a member's argv

`start` parses the argv and answers the first step; `step` takes the continuation `k` and the
result of the step it asked for and answers the next one, with follow's World after absorbing
any log the result carried. A write runs

  sign(envelope) → host(log, envelope) → [absorb: every logged event re-derived, PROTOCOL-4]
  → (page again, from the page's height, until it is the writer's tip)
  → plan on the caught-up World → sign(unsignedBytes u) → submit(call) → done

and a `read` stops after the catch-up; `init` needs no World (sign twice, print a join token).
The first envelope is valid for follow's own height + window, every later one for the tip the last
page stated + window. A member more than a window behind is refused `expired` with the writer's
height and re-signs ONCE a command for that height + window (`reSign`, PROTOCOL-19); a thin member's
`adopt` envelopes do the same from the pin's height.

`rotate` asks custody to `precommit` after the catch-up, plans the rotation to custody's NEXT key
(precommitting the digest of its PENDING key) and has it signed by `signNext`; custody advances on
its own settlement of the submit (CLIENT-13).

`adopt HEIGHT DIGEST` (thin consent, PROTOCOL-14 A) pages the writer's newest base with `read`, one
signed envelope per page, `Protocol.Thin.accept` deciding each page; the download so far lives in
follow's state (`Follow.download`, memory only), and an adopted base replaces follow's World and is
handed back as `Persist.adopt` for follow to seal as its own newest base. From there every command
catches up from the base's height like any other.

`k` holds only the argv, the phase and the results so far; every plan is RE-DERIVED from follow's
World at each step and the bytes it signs are compared with the ones custody signed (`planMoved`),
so `k` cannot steer what is signed (HOST-9's `resume_rederives`). A plan is offered for signature
only if follow's own World admits the Turn it derives (consent: `Protocol.Proofs.Command`).
-/
import Kernel.Receive.Submit
import Protocol.Command.Verb
import Protocol.Envelope

namespace Nanodregg.Protocol.Command

open Nanodregg.Codec Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- What one `host follow` knows about the member it serves. -/
structure Self (D : Type) where
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
  /-- the logged event at this height does not derive on follow's World -/
  | eventMismatch (height : Nat)
  | badState
  | badResult
  /-- follow's World moved between the plan custody signed and the submit -/
  | planMoved
  /-- read: a `KEY=VALUE` that does not hold -/
  | expect (key : Nat)
  | missingCell (cell : D)
  /-- the writer's stated height and chain after a log page are not what follow's fold reached -/
  | chainMismatch (height : Nat)
  /-- the derivation asked for more cells than `Kernel.Bounds.touchesMax` -/
  | tooManyPins
  /-- the catch-up read `Bounds.pagesPerCommandMax` pages and follow is still at `height`, the
  writer at `tip`: what was absorbed is kept, and the member runs the command again -/
  | behind (height tip : Nat)
  /-- a base download refused, by `Protocol.Thin`'s name -/
  | thin (r : Thin.Refusal)
  /-- custody refused the step, by its name (`CustodyRefusal`) -/
  | custody (r : CustodyRefusal)
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
  | .behind _ _ => "behind"
  | .thin r => r.name
  | .custody r => r.name
  | .expired _ => "expired"

def refused (r : Refusal D) : Reply := .done 1 ByteArray.empty s!"refused {r.name}\n".toUTF8
def printed (out : String) : Reply := .done 0 out.toUTF8 ByteArray.empty

/-! ## Follow's state -/

/-- What `host follow` holds between frames: its World, and a base download in progress (thin
consent: in memory only, never persisted, so a restarted follow starts the download again). -/
structure Follow (D : Type) [Ord D] where
  world : World D
  download : Option Thin.Download := none

/-- What a step asks follow to make durable before it answers: the Turns it absorbed (re-derived,
in log order; `[]` for most steps), or a base it adopted, which follow seals as its own newest base. -/
inductive Persist (D : Type) [Ord D]
  | turns (ts : List (Turn D))
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
signature, by `sign` or `signNext`), 5 (`precommit`), 6 (an adopt envelope's signature). -/
def custodyPhase (isInit : Bool) (phase : UInt8) : Bool :=
  phase == 1 || phase == 3 || phase == 5 || phase == 6 || (isInit && phase == 2)

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

/-- The call body of a command; `s` is the key it is signed with (for `rotate`: the next key, and
the pending key it precommits). -/
def body (X : Ctx D) (me : Self D) (s : Signed) : Cmd D → Option (Body D)
  | .enroll j => some (.enroll j.key j.next j.possession me.grant)
  | .install p => some (.install p)
  | .create ls => some (.create none ls [])
  | .write o k v via => some (.write o [(k, some v)] via)
  | .law o ls via => some (.law o ls via)
  | .invoke o m a via => some (.invoke o m a invokeBudget via)
  | .grant t g rs via => some (.grant (t.getD (worldId X)) g rs via)
  | .revoke g => some (.revoke g)
  | .rotate => some (.rotate s.key (nextKeyDigest X s.next))
  | .init _ | .read _ _ | .adopt _ => none

/-- Derive with the signature not yet known, pinning each cell the derivation asks for. -/
def derivePins (X : Ctx D) (w : World D) : Nat → Unsigned D → Except (Refusal D) (Unsigned D × Turn D)
  | 0, _ => .error .tooManyPins
  | fuel + 1, u =>
      let look := pinned w u.pins
      match (do keyRule look u; dispatch X look ⟨u, ByteArray.empty⟩ u.body) with
      | .error (.unpinned c) =>
          derivePins X w fuel { u with pins := u.pins ++ [(c, pinOf X.env (w.live c))] }
      | .error r => .error (.receive r)
      | .ok t => .ok (u, t)

/-- The call follow asks custody to sign: derived on follow's World with every pin it read, its
price the derived charge plus headroom, and only if follow's World admits the Turn. -/
def plan (X : Ctx D) (me : Self D) (w : World D) (key : ByteArray) (b : Body D) :
    Except (Refusal D) (Unsigned D) := do
  let u0 : Unsigned D :=
    { member := me.member
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
  match dispatch X (pinned w u.pins) ⟨u, ByteArray.empty⟩ u.body with
  | .error r => .error (.receive r)
  | .ok t => match World.admit X.env w t with
    | .error r => .error (.reject r)
    | .ok _ => .ok u

/-! ## Catching up -/

/-- Absorb logged events: each re-derived on follow's World by the Host's own decision function
(`Receive.submit` = receive, then admit). A writer that logged an event which does not derive is
caught here, at that height (PROTOCOL-4). Also returns the Turns it derived, in log order, so
`host follow` persists exactly what it re-derived (HOST-3) rather than re-running this loop. -/
def absorb (X : Ctx D) : World D → Array (Turn D) → List ByteArray →
    Except (Refusal D) (World D × Array (Turn D))
  | w, ts, [] => .ok (w, ts)
  | w, ts, e :: es =>
      match X.decodeCall e with
      | none => .error (.eventMismatch (w.height + 1))
      | some c => match submit X w c with
        | .ok (t, w') => absorb X w' (ts.push t) es
        | .error _ => .error (.eventMismatch (w.height + 1))


/-- A log page: the events, the writer's height and chain after the last of them, and the
writer's tip when it built the page. A tip below the page's own height is not a page. -/
def logPage (b : ByteArray) : Option (List ByteArray × Nat × ByteArray × Nat) :=
  match logReplyFrame.decode b with
  | .ok (l, h, c, t, ()) => do
      let n ← Text.ofU64 h.1
      let tip ← Text.ofU64 t.1
      if n ≤ tip then some (Text.unlist l, n, c.1, tip) else none
  | .error _ => none

/-- Absorb a page and require follow's fold to reach the writer's stated height and chain. -/
def absorbPage (X : Ctx D) (w : World D) (evs : List ByteArray) (height : Nat) (chain : ByteArray) :
    Except (Refusal D) (World D × List (Turn D)) := do
  let (w', ts) ← absorb X w #[] evs
  if w'.height = height ∧ X.env.bytes w'.chain = chain then pure (w', ts.toList)
  else throw (.chainMismatch height)

def hostName (p : ByteArray) : String := (String.fromUTF8? p).getD "unnamed"

def whoami : ByteArray := "nanodregg/protocol/whoami/v1".toUTF8

/-! ## Rendering -/

def hex (X : Ctx D) (d : D) : String := Text.toHex (X.env.bytes d)

/-- `read`: the object's state slots, one `KEY=VALUE` line each (keys relative to `stateBase`),
after every expectation holds. -/
def render (w : World D) (obj : D) (expect : List (Nat × ByteArray)) : Reply :=
  match w.live obj with
  | none => refused (D := D) (.missingCell obj)
  | some cell =>
      match expect.find? fun (k, v) => cell.slots.get (stateBase + k) != some v with
      | some (k, _) => refused (D := D) (.expect k)
      | none =>
          printed (String.join ((stateOf cell).map fun (k, v) =>
            s!"{k - stateBase}={(String.fromUTF8? v).getD (Text.toHex v)}\n"))

/-- What a committed write prints: its transaction id and every cell it created. -/
def receipt (X : Ctx D) (t : Turn D) : String :=
  s!"tx {hex X t.txId}\n" ++ String.join ((createdIds X.env t).map fun d => s!"id {hex X d}\n")

/-! ## Expiry (PROTOCOL-19) -/

/-- The writer refused an envelope signed for `upTo` as `expired` at `height`. Follow re-signs
the same request ONCE per command (`tried`), for `height + window`; a second `expired`, or a
stated height the first envelope already covered (the writer contradicts itself), ends the command
`expired`. So a command signs at most one envelope per page plus one. -/
def reSign (me : Self D) (tried : Bool) (upTo height : Nat) : Except (Refusal D) Nat :=
  if !tried && upTo < height && height + me.window < 2 ^ 64 then .ok (height + me.window)
  else .error (.expired height)

/-! ## The machine -/

/-- The envelope a thin member signs for the base page at byte `offset`, valid until `upTo`
(first the pin's height + window; after an `expired`, the writer's stated height + window). -/
def adoptEnvelope (X : Ctx D) (me : Self D) (upTo offset : Nat) : ByteArray :=
  Envelope.message X me.member me.grant offset upTo

def start (X : Ctx D) (me : Self D) (f : Follow D) (argv : List ByteArray) : Reply :=
  let w := f.world
  match parse X.digestOf argv with
  | .error r => refused (D := D) (.parse r)
  | .ok (.init _) => next (D := D) ⟨argv, 1, []⟩ fun k => .sign whoami k
  | .ok (.adopt pin) =>
      if w.height ≠ 0 then refused (D := D) (.thin (.notAtGenesis w.height)) else
      if pin.height ≤ w.height then refused (D := D) (.thin (.notBehind w.height)) else
      let off := Thin.offset pin f.download
      let upTo := pin.height + me.window
      next (D := D) ⟨argv, 6, [Text.u64 off, Text.u64 0, Text.u64 upTo, Text.u64 0]⟩ fun k =>
        .sign (adoptEnvelope X me upTo off) k
  | .ok _ =>
      let upTo := w.height + me.window
      next (D := D) ⟨argv, 1, [Text.u64 w.height, Text.u64 0, Text.u64 upTo, Text.u64 0]⟩ fun k =>
        .sign (Envelope.message X me.member me.grant w.height upTo) k

/-- One step: the continuation, the result of the step it asked for, and follow's state. It
answers follow's state after the step, what to persist (a log page's Turns, re-derived; a base it
adopted; `[]` for every other step), and the next reply. `B` is how an adopted base is read
(its World codec and the digest a pin names). -/
def step (X : Ctx D) (B : Thin.Base (World D)) (me : Self D) (f : Follow D) (kb result : ByteArray) :
    Follow D × Persist D × Reply :=
  let w := f.world
  let same (r : Reply) : Follow D × Persist D × Reply := (f, .turns [], r)
  let moved (w' : World D) (ts : List (Turn D)) (r : Reply) : Follow D × Persist D × Reply :=
    ({ f with world := w' }, .turns ts, r)
  match State.ofBytes kb, parse X.digestOf ((State.ofBytes kb).map (·.argv) |>.getD []) with
  | none, _ => same (refused (D := D) .badState)
  | some _, .error r => same (refused (D := D) (.parse r))
  | some st, .ok cmd =>
      let again (phase : UInt8) (acc : List ByteArray) (f : ByteArray → Reply) : Reply :=
        next (D := D) ⟨st.argv, phase, acc⟩ f
      -- the phases that asked custody (sign, signNext, precommit) get `status ‖ payload` from it:
      -- a refusal ends the command by custody's name, an ok hands on its payload
      let isInit := match cmd with | .init _ => true | _ => false
      match (if custodyPhase isInit st.phase then custodyResult (D := D) result else .ok result) with
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
              let e : Envelope D :=
                { member := me.member
                  grant := me.grant
                  start := h
                  validUntil := upTo
                  key := s.key
                  signature := s.signature }
              match Envelope.bytes X e with
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
              | some (evs, height, chain, tip), some pages =>
                  -- a page short of the tip that carries nothing would be asked for again forever
                  if evs.isEmpty && height < tip then same (refused (D := D) .badResult) else
                  match absorbPage X w evs height chain with
                  | .error r => same (refused (D := D) r)
                  | .ok (w', ts) =>
                      if height < tip then
                        if Bounds.pagesPerCommandMax ≤ pages + 1 then
                          moved w' ts (refused (D := D) (.behind height tip))
                        -- the next envelope covers the tip the writer stated, so a follower
                        -- behind by more than a window is not refused on every page
                        else moved w' ts (again 1 [Text.u64 height, Text.u64 (pages + 1),
                            Text.u64 (tip + me.window), triedB] fun k =>
                          .sign (Envelope.message X me.member me.grant height (tip + me.window)) k)
                      else
                      match cmd, Signed.ofBytes signedB with
                      | .read obj ex, _ => moved w' ts (render w' obj ex)
                      | .rotate, some _ => moved w' ts (again 5 [startB, signedB] fun k => .precommit k)
                      | _, some s => match body X me s cmd with
                        | none => moved w' ts (refused (D := D) .badState)
                        | some b =>
                          match plan X me w' s.key b with
                          | .error r => moved w' ts (refused (D := D) r)
                          | .ok u => moved w' ts (again 3 [startB, signedB, X.unsignedBytes u] fun k =>
                              .sign (X.unsignedBytes u) k)
                      | _, none => moved w' ts (refused (D := D) .badState)
          | some (.refused, p) =>
              match expiredHeight? p, Text.ofU64 startB, Text.ofU64 upToB, Text.ofU64 triedB with
              | none, _, _, _ => same (refused (D := D) (.host (hostName p)))
              | some height, some h, some upTo, some tried =>
                  match reSign (D := D) me (tried ≠ 0) upTo height with
                  | .error r => same (refused (D := D) r)
                  | .ok upTo' => same (again 1 [startB, pagesB, Text.u64 upTo', Text.u64 1] fun k =>
                      .sign (Envelope.message X me.member me.grant h upTo') k)
              | some _, _, _, _ => same (refused (D := D) .badState)
          | _ => same (refused (D := D) .badResult)
      -- the call's signature: re-plan, compare with what was signed, submit
      | _, 3, [startB, signedB, ub] =>
          match Signed.ofBytes signedB, Signed.ofBytes result with
          | some s, some s2 => match body X me s cmd with
            | none => same (refused (D := D) .badState)
            | some b =>
              if s2.key ≠ s.key then same (refused (D := D) .badResult) else
              match plan X me w s.key b with
              | .error r => same (refused (D := D) r)
              | .ok u =>
                  if X.unsignedBytes u ≠ ub then same (refused (D := D) .planMoved) else
                  let c : Call D := ⟨u, s2.signature⟩
                  match receive X w c with
                  | .error r => same (refused (D := D) (.receive r))
                  | .ok t => same (again 4 [startB, signedB, ub, (receipt X t).toUTF8] fun k =>
                      .submit (X.callBytes c) k)
          | _, _ => same (refused (D := D) .badResult)
      -- rotate: custody's next and pending keys; plan the rotation to `next`, signed by `next`
      | .rotate, 5, [startB, _] =>
          match precommitOf result with
          | none => same (refused (D := D) .badResult)
          | some (nk, pk) =>
              let s : Signed := ⟨nk, pk, ByteArray.empty⟩
              match s.bytes, body X me s .rotate with
              | some sb, some b =>
                  match plan X me w s.key b with
                  | .error r => same (refused (D := D) r)
                  | .ok u => same (again 3 [startB, sb, X.unsignedBytes u] fun k =>
                      .signNext (X.unsignedBytes u) k)
              | _, _ => same (refused (D := D) .badState)
      -- the settlement
      | _, 4, [_, _, _, out] =>
          match hostReply result with
          | some (.ok, _) => same (.done 0 out ByteArray.empty)
          | some (.refused, p) => same (refused (D := D) (.host (hostName p)))
          | some (.absent, _) => same (.done 3 ByteArray.empty "absent\n".toUTF8)
          | some (.uncertain, _) => same (.done 2 ByteArray.empty "uncertain\n".toUTF8)
          -- a settlement is never `closed`: the client settles a closed connection by lookup
          | some (.closed, _) | none => same (refused (D := D) .badResult)
      -- adopt: the envelope for the page at `off`, signed; ask for the base page
      | .adopt _, 6, [offB, pagesB, upToB, triedB] =>
          match Signed.ofBytes result, Text.ofU64 offB, Text.ofU64 upToB with
          | some s, some off, some upTo =>
              let e : Envelope D :=
                { member := me.member, grant := me.grant, start := off,
                  validUntil := upTo, key := s.key, signature := s.signature }
              match Envelope.bytes X e with
              | some p => same (again 7 [offB, pagesB, upToB, triedB] fun k => .host .read p k)
              | none => same (refused (D := D) .badState)
          | _, _, _ => same (refused (D := D) .badResult)
      -- adopt: one base page, decided by `Thin.accept`; the next page, or the World adopted
      | .adopt pin, 7, [offB, pagesB, upToB, triedB] =>
          let drop (r : Thin.Refusal) : Follow D × Persist D × Reply :=
            ({ f with download := none }, .turns [], refused (D := D) (.thin r))
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
                        ({ world := w', download := none }, .adopt w',
                          printed s!"adopted {pin.height} {Text.toHex pin.digest}\n")
                    | .ok (.more d) =>
                        let f' := { f with download := some d }
                        if Bounds.pagesPerCommandMax ≤ pages + 1 then
                          (f', .turns [], refused (D := D) (.thin (.incomplete d.got.size d.total)))
                        else (f', .turns [], again 6 [Text.u64 d.got.size, Text.u64 (pages + 1), upToB, triedB]
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
      | _, _, _ => same (refused (D := D) .badState)

end Nanodregg.Protocol.Command
