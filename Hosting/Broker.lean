/-
# Hosting.Broker — every decision of the provider-key broker (HOSTING-12)

`decide` answers one resident's ask: refused by name, or granted with the upstream request LEAN
printed and the worst case charged to the window. The charge is final (nothing is settled or
refunded): the input is bounded by the body's bytes, the output by the `max_tokens` Lean printed,
so the provider cannot bill past it, given that a token is at least one byte (a platform fact of
the provider's tokenizer, decisions/hosting.md HOSTING-12).

The meter is broker memory, one per allowance. An allowance is ONE meter: one resident, one model,
its key slot, its price, its window and its cap (HOSTING-13). The broker learns the World's
allowances by `Broker.follow`: an allowance it already held, unchanged, keeps its meter; any other
(new, or changed in any field) is opened at the follow's time with `spent = cap`, so a restart or
an operator's change never refunds a window: `Proofs.Broker.start_window_refused`.

Which provider a model is, and so which TLS host keybroker must verify, is Lean's table
(`providerOf`), never the resident's word and never the operator's dial address (HOSTING-15).
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

/-- How often keybroker and nd-members ask their decider which residents the World holds, in ms:
liveness only (a socket appears within a tick of the decider seeing a grain's birth). Emitted
`DECIDER_TICK_MS` (CLIENT-40). -/
def tickMs : Nat := 200

end Bounds

/-- What the operator allows one resident on one model, per window of `windowMs` operator
milliseconds: the key slot that pays, the price, the cap and the most tokens one ask may request.
A resident with several models has several allowances; its total spend is the sum of their caps. -/
structure Allowance where
  model : ByteArray
  keySlot : Nat
  /-- micro-units of money per 1000 tokens, input and output alike -/
  microPerKTok : Nat
  windowMs : Nat
  cap : Nat
  maxTokens : Nat
  deriving DecidableEq

/-- One resident's spend in its current window. -/
structure Meter where
  window : Nat
  spent : Nat
  deriving DecidableEq

structure Entry where
  resident : ByteArray
  allowance : Allowance
  /-- the operator time this broker life first held this allowance -/
  since : Nat
  meter : Meter

/-- The broker: the latest operator time it accepted, the key slots keybroker holds a key for, and
one entry per allowance of the World. -/
structure Broker where
  last : Nat
  keys : List Nat
  entries : List Entry

def windowOf (a : Allowance) (now : Nat) : Nat := now / a.windowMs

/-- An allowance first held at `t`: its window at `t` counts as spent. -/
def Entry.opened (t : Nat) (r : ByteArray) (a : Allowance) : Entry := ⟨r, a, t, ⟨windowOf a t, a.cap⟩⟩

/-- The broker once the World's allowances are `rs` (resident, allowance), at operator time `now`.
An entry for the same resident and the same allowance, field for field, keeps its meter; every
other is opened at `max now last`, spent to its cap. So a changed allowance is a new budget whose
first window grants nothing that costs (decisions/hosting.md HOSTING-13). -/
def Broker.follow (b : Broker) (now : Nat) (rs : List (ByteArray × Allowance)) : Broker :=
  let t := max now b.last
  { last := t, keys := b.keys,
    entries := rs.map fun (r, a) =>
      match b.entries.find? (fun e => e.resident == r && e.allowance == a) with
      | some e => e
      | none => Entry.opened t r a }

/-- A broker life starting at operator time `t0` with `keys` in hand: every start window is spent. -/
def Broker.start (t0 : Nat) (keys : List Nat) (rs : List (ByteArray × Allowance)) : Broker :=
  Broker.follow ⟨t0, keys, []⟩ t0 rs

/-- A later window starts empty; an earlier or equal one keeps the meter. -/
def Meter.roll (m : Meter) (w : Nat) : Meter := if m.window < w then ⟨w, 0⟩ else m

/-- The worst-case charge of `tokens` tokens, rounded up (`Proofs.Broker.cost_worst`). A model
priced 0 is refused `allowanceMalformed`: a free call on the operator's key is unbounded spend. -/
def cost (a : Allowance) (tokens : Nat) : Nat := (tokens * a.microPerKTok + 999) / 1000

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

/-- A provider: the TLS host keybroker verifies the certificate for (and sends as SNI and `Host:`),
its request target, the fixed header lines, and the name of the header that carries the key. -/
structure Upstream where
  host : ByteArray
  target : ByteArray
  headers : ByteArray
  keyHeader : ByteArray
  deriving DecidableEq

/-- Anthropic's Messages API. -/
def anthropic : Upstream :=
  ⟨"api.anthropic.com".toUTF8, "/v1/messages".toUTF8,
   "anthropic-version: 2023-06-01\r\ncontent-type: application/json\r\n".toUTF8, "x-api-key".toUTF8⟩

/-- The provider table: a model whose name starts with a row's prefix is served by that row's
provider. A model in no row is refused `noProvider`, so there is no default host. -/
def providers : List (ByteArray × Upstream) := [("claude-".toUTF8, anthropic)]

/-- Whether `p` is a prefix of `b`. -/
def startsWith (b p : ByteArray) : Bool := decide (p.size ≤ b.size) && b.extract 0 p.size == p

/-- The provider of `model`: the first row of `providers` whose prefix it starts with. -/
def providerOf (model : ByteArray) : Option Upstream :=
  (providers.find? fun x => startsWith model x.1).map Prod.snd

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
  upstream : Upstream
  charged : Nat
  body : ByteArray
  deriving DecidableEq

/-- Whether entry `x` is the meter of resident `r` on `model`. -/
def Entry.is (r model : ByteArray) (x : Entry) : Bool := x.resident == r && x.allowance.model == model

/-- An allowance that cannot be applied: a zero window, a cap past `capMax`, a price of 0 (a free
call on the operator's key is unbounded spend), or a key slot past the wire's u32. -/
def Allowance.malformed (a : Allowance) : Bool :=
  a.windowMs == 0 || decide (Bounds.capMax ≤ a.cap) || a.microPerKTok == 0 || decide (2 ^ 32 ≤ a.keySlot)

/-- THE decision for one ask from resident `r` at operator time `now`. -/
def decide (b : Broker) (now : Nat) (r : ByteArray) (ask : Ask) : Except Refusal (Broker × Grant) := do
  if now < b.last then throw .clockRegressed
  unless b.entries.any (·.resident == r) do throw .noAllowance
  let e ← match b.entries.filter (Entry.is r ask.model) with
    | [] => throw .modelNotAllowed
    | [e] => pure e
    | _ => throw .allowanceAmbiguous
  let a := e.allowance
  if a.malformed then throw .allowanceMalformed
  let up ← match providerOf a.model with
    | some u => pure u
    | none => throw .noProvider
  unless b.keys.contains a.keySlot do throw .keyMissing
  if ask.maxTokens = 0 then throw .tokensZero
  if min a.maxTokens Bounds.tokensCeiling < ask.maxTokens then throw .tokensOver
  let body ← requestBody ask
  if Bounds.bodyMax < body.size then throw .requestTooLarge
  let m := e.meter.roll (windowOf a now)
  let c := cost a (body.size + ask.maxTokens)
  if a.cap < m.spent + c then throw .overSpend
  let e' := { e with meter := ⟨m.window, m.spent + c⟩ }
  pure ({ b with last := now, entries := b.entries.map fun x => if Entry.is r ask.model x then e' else x },
        ⟨a.keySlot.toUInt32, up, c, body⟩)

/-- One `decide` frame and the ask frame after it, as `hosting-broker` runs them: the next broker
and the verdict to write. A refusal leaves the broker unchanged. -/
def step (b : Broker) (r : ByteArray) (now : Nat) (askBytes : ByteArray) : Broker × Verdict :=
  match Wire.decodeAsk askBytes with
  | .error _ => (b, .refuse .badAsk)
  | .ok ask =>
    match decide b now r ask with
    | .ok (b', g) =>
      (b', .grant g.keySlot g.charged g.upstream.host g.upstream.target g.upstream.headers g.upstream.keyHeader g.body)
    | .error why => (b, .refuse why)

/-- One ask as `hosting-broker` admits it (HOSTING-26): only a resident the World holds is decided
(`residents`: the socket names of its born, unremoved resident grains); any other socket's ask is
refused `notResident` and leaves the broker unchanged. A socket whose grain was removed is closed by
keybroker when it learns so; an ask already on its open connection meets this. -/
def admit (residents : List ByteArray) (b : Broker) (r : ByteArray) (now : Nat) (askBytes : ByteArray) :
    Broker × Verdict :=
  if residents.contains r then step b r now askBytes else (b, .refuse .notResident)

end Nanodregg.Hosting.Broker
