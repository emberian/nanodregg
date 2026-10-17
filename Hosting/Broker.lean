/-
# Hosting.Broker — every decision of the provider-key broker (HOSTING-12)

`decide` answers one resident's ask: refused by name, or granted with the upstream request LEAN
printed and the worst case charged to the window. The charge is final (nothing is settled or
refunded): the input is bounded by the body's bytes, the output by the `max_tokens` Lean printed,
so the provider cannot bill past it, given that a token is at least one byte (a platform fact of
the provider's tokenizer, decisions/hosting.md HOSTING-12).

The meter is broker memory. A broker life opens every meter at its start window with `spent = cap`
(`Broker.start`), so a restart never refunds a window: `Proofs.Broker.start_window_free`.
-/
import Hosting.BrokerWire

namespace Nanodregg.Hosting.Broker

namespace Bounds

/-- The most output tokens one ask may request, whatever an allowance says. -/
def tokensCeiling : Nat := 32768

/-- The most messages one ask may carry. -/
def messagesMax : Nat := 256

/-- The largest upstream body Lean prints: a verdict frame's other fields fit in the rest. -/
def bodyMax : Nat := frameMax - 4096

/-- An allowance's cap (and so every charge) is below this, so a charge fits the wire's u64. -/
def capMax : Nat := 2 ^ 63

end Bounds

/-- A model a resident may call, the operator key slot that pays for it, and its price. -/
structure Model where
  name : ByteArray
  keySlot : UInt32
  /-- micro-units of money per 1000 tokens, input and output alike -/
  microPerKTok : Nat
  deriving DecidableEq

/-- What the operator allows one resident, per window of `windowMs` operator milliseconds. -/
structure Allowance where
  windowMs : Nat
  cap : Nat
  maxTokens : Nat
  models : List Model
  deriving DecidableEq

/-- One resident's spend in its current window. -/
structure Meter where
  window : Nat
  spent : Nat
  deriving DecidableEq

structure Entry where
  resident : ByteArray
  allowance : Allowance
  meter : Meter

/-- The broker: the latest operator time it accepted, and one entry per resident. -/
structure Broker where
  last : Nat
  entries : List Entry

def windowOf (a : Allowance) (now : Nat) : Nat := now / a.windowMs

/-- A broker life starting at operator time `t0`: every resident's start window counts as spent. -/
def Broker.start (t0 : Nat) (rs : List (ByteArray × Allowance)) : Broker :=
  { last := t0, entries := rs.map fun (r, a) => ⟨r, a, ⟨windowOf a t0, a.cap⟩⟩ }

/-- A later window starts empty; an earlier or equal one keeps the meter. -/
def Meter.roll (m : Meter) (w : Nat) : Meter := if m.window < w then ⟨w, 0⟩ else m

/-- The worst-case charge of `tokens` tokens, rounded up (`Proofs.Broker.cost_worst`). A model
priced 0 is refused `allowanceMalformed`: a free call on the operator's key is unbounded spend. -/
def cost (md : Model) (tokens : Nat) : Nat := (tokens * md.microPerKTok + 999) / 1000

/-! ## The upstream request, printed -/

namespace Json

def hexDigit (n : Nat) : UInt8 := if n < 10 then (48 + n).toUInt8 else (87 + n).toUInt8

/-- `acc` followed by the bytes that stand for `x` inside a JSON string: `\"`, `\\`, `\u00XX` for
a control byte, else `x` itself (UTF-8 multi-byte sequences pass through). -/
def esc (acc : ByteArray) (x : UInt8) : ByteArray :=
  if x == 34 then (acc.push 92).push 34
  else if x == 92 then (acc.push 92).push 92
  else if x < 32 then
    (((((acc.push 92).push 117).push 48).push 48).push (hexDigit (x.toNat / 16))).push (hexDigit (x.toNat % 16))
  else acc.push x

/-- `acc ‖ "` ‖ the escaped bytes of `b` ‖ `"`. -/
def str (acc b : ByteArray) : ByteArray := (b.data.foldl esc (acc.push 34)).push 34

def lit (acc : ByteArray) (s : String) : ByteArray := acc ++ s.toUTF8

def message (acc : ByteArray) (role : String) (t : ByteArray) : ByteArray :=
  lit (str (lit acc ("{\"role\":\"" ++ role ++ "\",\"content\":")) t) "}"

def messages (acc : ByteArray) : List (String × ByteArray) → ByteArray
  | [] => acc
  | [(r, t)] => message acc r t
  | (r, t) :: ms => messages (lit (message acc r t) ",") ms

end Json

/-- The provider an allowance's key slots call: its request target, the fixed header lines, and the
name of the header that carries the key. -/
structure Upstream where
  target : ByteArray
  headers : ByteArray
  keyHeader : ByteArray

/-- Anthropic's Messages API. -/
def anthropic : Upstream :=
  ⟨"/v1/messages".toUTF8, "anthropic-version: 2023-06-01\r\ncontent-type: application/json\r\n".toUTF8,
   "x-api-key".toUTF8⟩

def roleName : UInt8 → Option String
  | 0 => some "user"
  | 1 => some "assistant"
  | _ => none

def utf8 (b : ByteArray) : Bool := (String.fromUTF8? b).isSome

/-- The JSON body of an ask: `{"model":…,"max_tokens":…[,"system":…],"messages":[…]}`, every value
printed here from the ask's fields, so no field the resident sent is forwarded unread. -/
def requestBody (ask : Ask) : Except Refusal ByteArray := do
  let n := ask.texts.length
  if n = 0 ∨ n ≠ ask.roles.size ∨ Bounds.messagesMax < n then throw .messagesMalformed
  unless utf8 ask.model && utf8 ask.system && ask.texts.all utf8 do throw .textNotUtf8
  let msgs ← (ask.roles.data.toList.zip ask.texts).mapM fun (r, t) =>
    match roleName r with
    | some rn => pure (rn, t)
    | none => throw .messagesMalformed
  let head := Json.lit (Json.lit (Json.str (Json.lit .empty "{\"model\":") ask.model) ",\"max_tokens\":")
    (Nat.repr ask.maxTokens)
  let withSys := if ask.system.size = 0 then head else Json.str (Json.lit head ",\"system\":") ask.system
  pure (Json.lit (Json.messages (Json.lit withSys ",\"messages\":[") msgs) "]}")

/-! ## The decision -/

/-- What a grant gives keybroker. -/
structure Grant where
  keySlot : UInt32
  charged : Nat
  body : ByteArray
  deriving DecidableEq

/-- THE decision for one ask from resident `r` at operator time `now`. -/
def decide (b : Broker) (now : Nat) (r : ByteArray) (ask : Ask) : Except Refusal (Broker × Grant) := do
  if now < b.last then throw .clockRegressed
  let some e := b.entries.find? (·.resident == r) | throw .noAllowance
  let a := e.allowance
  if a.windowMs = 0 ∨ Bounds.capMax ≤ a.cap then throw .allowanceMalformed
  let some md := a.models.find? (·.name == ask.model) | throw .modelNotAllowed
  if md.microPerKTok = 0 then throw .allowanceMalformed
  if ask.maxTokens = 0 then throw .tokensZero
  if min a.maxTokens Bounds.tokensCeiling < ask.maxTokens then throw .tokensOver
  let body ← requestBody ask
  if Bounds.bodyMax < body.size then throw .requestTooLarge
  let m := e.meter.roll (windowOf a now)
  let c := cost md (body.size + ask.maxTokens)
  if a.cap < m.spent + c then throw .overSpend
  let e' := { e with meter := ⟨m.window, m.spent + c⟩ }
  pure ({ last := now, entries := b.entries.map fun x => if x.resident == r then e' else x },
        ⟨md.keySlot, c, body⟩)

/-- One `decide` frame and the ask frame after it, as `hosting-broker` runs them: the next broker
and the verdict to write. A refusal leaves the broker unchanged. -/
def step (b : Broker) (r : ByteArray) (now : Nat) (askBytes : ByteArray) : Broker × Verdict :=
  match Wire.decodeAsk askBytes with
  | .error _ => (b, .refuse .badAsk)
  | .ok ask =>
    match decide b now r ask with
    | .ok (b', g) => (b', .grant g.keySlot g.charged anthropic.target anthropic.headers anthropic.keyHeader g.body)
    | .error why => (b, .refuse why)

end Nanodregg.Hosting.Broker
