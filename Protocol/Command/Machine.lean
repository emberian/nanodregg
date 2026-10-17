/-
# Protocol.Command.Machine — what `host follow` does with a member's argv

`start` parses the argv and answers the first step; `step` takes the continuation `k` and the
result of the step it asked for and answers the next one, with follow's World after absorbing
any log the result carried. A write runs

  sign(envelope) → host(log, envelope) → [absorb: every logged event re-derived, PROTOCOL-4]
  → plan on the caught-up World → sign(unsignedBytes u) → submit(call) → done

and a `read` stops after the catch-up; `init` needs no World (sign twice, print a join token).

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
  /-- the member's follow grant, which its envelopes name -/
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

/-- A step answered to the client. -/
inductive Reply
  | done (exit : UInt8) (out err : ByteArray)
  | sign (message k : ByteArray)
  | host (op : Op) (payload k : ByteArray)
  | submit (call k : ByteArray)
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

def refused (r : Refusal D) : Reply := .done 1 ByteArray.empty s!"refused {r.name}\n".toUTF8
def printed (out : String) : Reply := .done 0 out.toUTF8 ByteArray.empty

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

/-! ## The plan -/

/-- The budget an invoke is signed for. -/
def invokeBudget : Nat := 100000
/-- Headroom of the signed price over the charge derived before the signature exists. -/
def chargeSlack : Nat := 4096

def body (me : Self D) : Cmd D → Option (Body D)
  | .enroll j => some (.enroll j.key j.next j.possession)
  | .follow g => some (.follow g me.grant)
  | .install p => some (.install p)
  | .create ls => some (.create none ls [])
  | .write o k v via => some (.write o [(k, some v)] via)
  | .law o ls via => some (.law o ls via)
  | .invoke o m a via => some (.invoke o m a invokeBudget via)
  | .grant t g rs => some (.grant t g rs none)
  | .revoke g => some (.revoke g)
  | .init _ | .read _ _ => none

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
      maxCharge := 0
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
caught here, at that height (PROTOCOL-4). -/
def absorb (X : Ctx D) : World D → List ByteArray → Except (Refusal D) (World D)
  | w, [] => .ok w
  | w, e :: es =>
      match X.decodeCall e with
      | none => .error (.eventMismatch (w.height + 1))
      | some c => match submit X w c with
        | .ok (_, w') => absorb X w' es
        | .error _ => .error (.eventMismatch (w.height + 1))

def hostReply (b : ByteArray) : Option (Status × ByteArray) :=
  if h : 0 < b.size then (Status.ofCode? b[0]).map (·, b.extract 1 b.size) else none

/-- A log page: the events, and the writer's height and chain after the last of them. -/
def logPage (b : ByteArray) : Option (List ByteArray × Nat × ByteArray) :=
  match logReplyFrame.decode b with
  | .ok (l, h, c, ()) => (Text.ofU64 h.1).map fun n => (Text.unlist l, n, c.1)
  | .error _ => none

/-- Absorb a page and require follow's fold to reach the writer's stated height and chain. -/
def absorbPage (X : Ctx D) (w : World D) (evs : List ByteArray) (height : Nat) (chain : ByteArray) :
    Except (Refusal D) (World D) := do
  let w' ← absorb X w evs
  if w'.height = height ∧ X.env.bytes w'.chain = chain then pure w' else throw (.chainMismatch height)

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

/-! ## The machine -/

def start (X : Ctx D) (me : Self D) (w : World D) (argv : List ByteArray) : Reply :=
  match parse X.digestOf argv with
  | .error r => refused (D := D) (.parse r)
  | .ok (.init _) => next (D := D) ⟨argv, 1, []⟩ fun k => .sign whoami k
  | .ok _ =>
      next (D := D) ⟨argv, 1, [Text.u64 w.height]⟩ fun k =>
        .sign (Envelope.message X me.member me.grant w.height (w.height + me.window)) k

/-- One step: the continuation, the result of the step it asked for, and follow's World. -/
def step (X : Ctx D) (me : Self D) (w : World D) (kb result : ByteArray) : World D × Reply :=
  let same (r : Reply) : World D × Reply := (w, r)
  match State.ofBytes kb, parse X.digestOf ((State.ofBytes kb).map (·.argv) |>.getD []) with
  | none, _ => same (refused (D := D) .badState)
  | some _, .error r => same (refused (D := D) (.parse r))
  | some st, .ok cmd =>
      let again (phase : UInt8) (acc : List ByteArray) (f : ByteArray → Reply) : Reply :=
        next (D := D) ⟨st.argv, phase, acc⟩ f
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
      -- every other verb: the envelope, signed; ask for the log
      | _, 1, [startB] =>
          match Signed.ofBytes result, Text.ofU64 startB with
          | some s, some h =>
              let e : Envelope D :=
                { member := me.member
                  grant := me.grant
                  start := h
                  validUntil := h + me.window
                  key := s.key
                  signature := s.signature }
              match Envelope.bytes X e with
              | some p => same (again 2 [startB, result] fun k => .host .log p k)
              | none => same (refused (D := D) .badState)
          | _, _ => same (refused (D := D) .badResult)
      -- the log: absorb it, then read, or plan and ask for the signature
      | _, 2, [startB, signedB] =>
          match hostReply result with
          | some (.ok, p) =>
              match logPage p with
              | none => same (refused (D := D) .badResult)
              | some (evs, height, chain) =>
                  match absorbPage X w evs height chain with
                  | .error r => same (refused (D := D) r)
                  | .ok w' =>
                      match cmd, body me cmd, Signed.ofBytes signedB with
                      | .read obj ex, _, _ => (w', render w' obj ex)
                      | _, some b, some s =>
                          match plan X me w' s.key b with
                          | .error r => (w', refused (D := D) r)
                          | .ok u => (w', again 3 [startB, signedB, X.unsignedBytes u] fun k =>
                              .sign (X.unsignedBytes u) k)
                      | _, _, _ => (w', refused (D := D) .badState)
          | some (.refused, p) => same (refused (D := D) (.host (hostName p)))
          | _ => same (refused (D := D) .badResult)
      -- the call's signature: re-plan, compare with what was signed, submit
      | _, 3, [startB, signedB, ub] =>
          match body me cmd, Signed.ofBytes signedB, Signed.ofBytes result with
          | some b, some s, some s2 =>
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
          | _, _, _ => same (refused (D := D) .badResult)
      -- the settlement
      | _, 4, [_, _, _, out] =>
          match hostReply result with
          | some (.ok, _) => same (.done 0 out ByteArray.empty)
          | some (.refused, p) => same (refused (D := D) (.host (hostName p)))
          | some (.absent, _) => same (.done 3 ByteArray.empty "absent\n".toUTF8)
          | some (.uncertain, _) => same (.done 2 ByteArray.empty "uncertain\n".toUTF8)
          | none => same (refused (D := D) .badResult)
      | _, _, _ => same (refused (D := D) .badState)

end Nanodregg.Protocol.Command
