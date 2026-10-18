/-
# Hosting.BrokerWire — the frames of the provider-key broker (HOSTING-12)

Three parties: the resident (asks on its own socket), `keybroker` (Rust: sockets, the key file,
upstream bytes) and `hosting-broker` (Lean: every decision). All frames are `Codec.Tagged` over the
one Layout family, so keybroker's reader and writer are printed from these lists (law 2). On every
pipe and socket a frame is `u32le len ‖ payload`, `1 ≤ len ≤ Bounds.frameMax`.

    ask       ask      1  model, maxTokens : u32, system, roles (one byte per message), texts : list
    request   decide   1  resident, atMs : u64          (followed by the resident's ask frame, unread)
              residents 2 atMs : u64                    (which sockets to serve: HOSTING-26)
    verdict   grant    1  keySlot : u32, charged : u64, host, target, headers, keyHeader, body
              refuse   2  brokerRefusal : Refusal
              residents 3 names : list                  (the answer to `residents`)
    answer    answer   1  status : u32, body             (the upstream's status and body)
              refused  2  brokerRefusal : Refusal

keybroker never decodes an ask: it puts a `decide` frame naming the socket's resident in front of
the ask's bytes and hands both to Lean. So identity is the socket, and the only decoder of what a
resident sent is Lean's. A `grant` carries the upstream request Lean printed (the provider's TLS
host, target, extra headers, the NAME of the key header, the JSON body); keybroker adds the key's
bytes and nothing else. `host` is the name keybroker sends as SNI and `Host:` and verifies the
provider's certificate for, so the operator's dial address chooses where bytes go and Lean's table
chooses whom they must reach (HOSTING-15). Which sockets keybroker serves is Lean's too: it asks
`residents` and binds exactly the names the decider answers, the resident grains the World holds
(HOSTING-26; no operator list).
This module imports no decision, so the emitter's closure is the Codec family and these lists.
-/
import Codec.Layout

namespace Nanodregg.Hosting.Broker

open Nanodregg.Codec

namespace Bounds

/-- The largest frame payload on any broker pipe or socket, in bytes; also every field's bound.
An ask's texts, and an upstream answer's body, are at most this. -/
def frameMax : Nat := 131072

private theorem frameMax_fits : frameMax < 2 ^ 32 := by decide

/-- The most resident sockets one keybroker serves: a `residents` answer of this many 64-byte names
fits one frame (`Proofs.Broker.residents_encode`). A World holding more ends the decider
`residentsPastBound` by name, never a silent truncation. -/
def residentsMax : Nat := 1024

end Bounds

/-- Why the broker refuses an ask, by name (law 7). `Broker.decide` refuses every case but keybroker's
(`keyEchoed`, `upstreamFailed`, `busy`, `tlsCertificate`, `tlsHostname`, `tlsProtocol`, `peerRefused`, mapped from its
transport outcomes by an exhaustive match);
`keyMissing` is both: Lean refuses a slot keybroker has no key for, and keybroker re-checks it. -/
inductive Refusal
  /-- no allowance names this resident -/
  | noAllowance
  /-- the allowance cannot be applied: a zero-length window, a cap past `capMax`, a price of 0, a key slot past u32 -/
  | allowanceMalformed
  /-- the operator's clock went backwards -/
  | clockRegressed
  /-- the ask does not decode -/
  | badAsk
  /-- no allowance of this resident names the asked model -/
  | modelNotAllowed
  /-- an ask for no tokens -/
  | tokensZero
  /-- more tokens than the allowance or `Broker.Bounds.tokensCeiling` permits -/
  | tokensOver
  /-- no messages, a role byte that is neither user nor assistant, or roles and texts of different lengths -/
  | messagesMalformed
  /-- a system or message text that is not UTF-8 -/
  | textNotUtf8
  /-- the worst-case charge does not fit the window's remaining allowance -/
  | overSpend
  /-- the upstream request Lean prints does not fit one verdict frame -/
  | requestTooLarge
  /-- the key file has no key for the allowance's slot (Lean refuses it before any charge) -/
  | keyMissing
  /-- keybroker: the upstream answer contained the key; the answer is withheld -/
  | keyEchoed
  /-- keybroker: the upstream could not be reached or answered past `frameMax` -/
  | upstreamFailed
  /-- keybroker: this resident already has an ask in flight -/
  | busy
  /-- two allowances the operator holds name this resident and model: which meter is meant is not
  the broker's to guess (the operator revokes one) -/
  | allowanceAmbiguous
  /-- the asked model is in no row of Lean's provider table (`Broker.providerOf`): no host to verify -/
  | noProvider
  /-- keybroker: the provider's certificate does not chain to an operator anchor, or is invalid -/
  | tlsCertificate
  /-- keybroker: the provider's certificate is valid but not for the host Lean named -/
  | tlsHostname
  /-- keybroker: the TLS session failed for any other reason (version, alert, a close without
  `close_notify`); the upstream's own text is never relayed -/
  | tlsProtocol
  /-- keybroker: the connecting process is not the hosted uid with SOCKDIR's group (`SO_PEERCRED`,
  HOSTING-17): nothing it sent is read -/
  | peerRefused
  /-- the asking socket's resident is no resident grain of the World (it was removed, or never
  was): its socket is being closed, and nothing is decided for it (HOSTING-26) -/
  | notResident
  deriving DecidableEq, Repr

namespace Refusal

def all : List Refusal :=
  [noAllowance, allowanceMalformed, clockRegressed, badAsk, modelNotAllowed, tokensZero, tokensOver,
   messagesMalformed, textNotUtf8, overSpend, requestTooLarge, keyMissing, keyEchoed, upstreamFailed, busy,
   allowanceAmbiguous, noProvider, tlsCertificate, tlsHostname, tlsProtocol, peerRefused, notResident]

def code : Refusal → UInt8
  | noAllowance => 0 | allowanceMalformed => 1 | clockRegressed => 2 | badAsk => 3
  | modelNotAllowed => 4 | tokensZero => 5 | tokensOver => 6 | messagesMalformed => 7
  | textNotUtf8 => 8 | overSpend => 9 | requestTooLarge => 10 | keyMissing => 11 | keyEchoed => 12
  | upstreamFailed => 13 | busy => 14 | allowanceAmbiguous => 15 | noProvider => 16
  | tlsCertificate => 17 | tlsHostname => 18 | tlsProtocol => 19 | peerRefused => 20
  | notResident => 21

def name : Refusal → String
  | noAllowance => "noAllowance" | allowanceMalformed => "allowanceMalformed"
  | clockRegressed => "clockRegressed" | badAsk => "badAsk" | modelNotAllowed => "modelNotAllowed"
  | tokensZero => "tokensZero" | tokensOver => "tokensOver" | messagesMalformed => "messagesMalformed"
  | textNotUtf8 => "textNotUtf8" | overSpend => "overSpend" | requestTooLarge => "requestTooLarge"
  | keyMissing => "keyMissing"
  | keyEchoed => "keyEchoed" | upstreamFailed => "upstreamFailed" | busy => "busy"
  | allowanceAmbiguous => "allowanceAmbiguous" | noProvider => "noProvider"
  | tlsCertificate => "tlsCertificate" | tlsHostname => "tlsHostname" | tlsProtocol => "tlsProtocol"
  | peerRefused => "peerRefused" | notResident => "notResident"

def ofCode? (b : UInt8) : Option Refusal := all.find? (·.code == b)

end Refusal

/-- A resident's ask, decoded. `roles[i]` is message `i`'s role (0 user, 1 assistant). -/
structure Ask where
  model : ByteArray
  maxTokens : Nat
  system : ByteArray
  roles : ByteArray
  texts : List ByteArray
  deriving DecidableEq

/-- What Lean tells keybroker for one ask. -/
inductive Verdict
  /-- call the upstream over TLS verified for `host`: `POST target`, `Host: host`, the `headers`
  lines, `keyHeader: <the slot's key>`, `body` -/
  | grant (keySlot : UInt32) (charged : Nat) (host target headers keyHeader body : ByteArray)
  | refuse (why : Refusal)
  /-- the resident grains whose sockets keybroker must serve, by socket name (`Controller.dirOf`) -/
  | residents (names : List ByteArray)
  deriving DecidableEq

/-- What keybroker asks: a decision for an ask on a resident's socket (its ask frame follows), or
which residents to serve. -/
inductive Request
  | decide (resident : ByteArray) (atMs : Nat)
  | residents (atMs : Nat)

namespace Wire

private def refusalField : Field := .oneOf "brokerRefusal" (Refusal.all.map fun r => (r.name, r.code))

def askCases : Tagged :=
  [("ask", 1, [.bytes "model", .u32 "maxTokens", .bytes "system", .bytes "roles", .list "texts"])]

def requestCases : Tagged :=
  [("decide", 1, [.bytes "resident", .u64 "atMs"]),
   ("residents", 2, [.u64 "atMs"])]

def verdictCases : Tagged :=
  [("grant", 1, [.u32 "keySlot", .u64 "charged", .bytes "host", .bytes "target", .bytes "headers",
     .bytes "keyHeader", .bytes "body"]),
   ("refuse", 2, [refusalField]),
   ("residents", 3, [.list "names"])]

def answerCases : Tagged :=
  [("answer", 1, [.u32 "status", .bytes "body"]),
   ("refused", 2, [refusalField])]

abbrev AskTy := Tagged.Ty Bounds.frameMax askCases
abbrev RequestTy := Tagged.Ty Bounds.frameMax requestCases
abbrev VerdictTy := Tagged.Ty Bounds.frameMax verdictCases

def askCodec : Stream AskTy := Tagged.codec Bounds.frameMax Bounds.frameMax_fits askCases
def requestCodec : Stream RequestTy := Tagged.codec Bounds.frameMax Bounds.frameMax_fits requestCases
def verdictCodec : Stream VerdictTy := Tagged.codec Bounds.frameMax Bounds.frameMax_fits verdictCases

def bytes? (b : ByteArray) : Option (Bytes Bounds.frameMax) :=
  if h : b.size ≤ Bounds.frameMax then some ⟨b, h⟩ else none

private theorem contains_of_mem (r : Refusal) :
    ((Refusal.all.map fun r => (r.name, r.code)).map Prod.snd).toArray.contains r.code = true := by
  simp only [List.contains_toArray, List.elem_eq_mem, decide_eq_true_eq, List.map_map]
  exact List.mem_map.mpr ⟨r, by cases r <;> decide, rfl⟩

private theorem refusal_of_contains (b : UInt8)
    (h : ((Refusal.all.map fun r => (r.name, r.code)).map Prod.snd).toArray.contains b = true) :
    (Refusal.ofCode? b).isSome = true := by
  simp only [List.contains_toArray, List.elem_eq_mem, decide_eq_true_eq, List.map_map] at h
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp h
  cases r <;> rfl

def askOf : AskTy → Ask
  | ⟨⟨0, _⟩, (m, n, s, r, t, ())⟩ =>
    { model := m.val, maxTokens := n.toNat, system := s.val, roles := r.val, texts := t.val.toList.map (·.val) }

/-- The resident's ask from its frame payload; a refusal names the offset and the case. -/
def decodeAsk (b : ByteArray) : Except Codec.Refusal Ask := (askCodec.decode b).map askOf

/-- A request from keybroker: a `decide` header (the socket's resident and keybroker's clock), or a
`residents` question (keybroker's clock). -/
def decodeRequest (b : ByteArray) : Except Codec.Refusal Request :=
  (requestCodec.decode b).map fun
    | ⟨⟨0, _⟩, (r, t, ())⟩ => .decide r.val t.toNat
    | ⟨⟨1, _⟩, (t, ())⟩ => .residents t.toNat

def verdictWire? : Verdict → Option VerdictTy
  | .grant k c hs t h kh b => do
    if hc : c < 2 ^ 64 then
      let hs ← bytes? hs; let t ← bytes? t; let h ← bytes? h; let kh ← bytes? kh; let b ← bytes? b
      pure ⟨⟨0, by decide⟩, (k, ⟨c, hc⟩, hs, t, h, kh, b, ())⟩
    else none
  | .refuse why => pure ⟨⟨1, by decide⟩, (⟨why.code, contains_of_mem why⟩, ())⟩
  | .residents names => do
    let a ← names.mapM bytes?
    if h : a.toArray.size ≤ Bounds.frameMax then pure ⟨⟨2, by decide⟩, (⟨a.toArray, h⟩, ())⟩ else none

def verdictOf : VerdictTy → Verdict
  | ⟨⟨0, _⟩, (k, c, hs, t, h, kh, b, ())⟩ => .grant k c.toNat hs.val t.val h.val kh.val b.val
  | ⟨⟨1, _⟩, (why, ())⟩ => .refuse ((Refusal.ofCode? why.val).get (refusal_of_contains _ why.property))
  | ⟨⟨2, _⟩, (ns, ())⟩ => .residents (ns.val.toList.map (·.val))

/-- A verdict's payload, when it fits one frame. -/
def encodeVerdict (v : Verdict) : Option ByteArray := do
  let w ← verdictWire? v
  let b := verdictCodec.bytes w
  if b.size ≤ Bounds.frameMax then some b else none

end Wire
end Nanodregg.Hosting.Broker
