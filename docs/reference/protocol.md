# The member protocol

This document specifies the member protocol of nanodregg at `main` `276ded8`.
Its notation is [the conventions](../spec/0-conventions.md).
[`kernel.md`](kernel.md) specifies the World, the Turn, the signed call, `receive`, `submit`, `judge`, `World.admit`, `World.refuse` and the kernel's refusal names; this document uses them and does not restate them.

The document has eight parts.
Part 1 names the parties, their channels and what each trusts.
Part 2 gives the wire: frames, operations, payloads and the writer's answer to each.
Part 3 gives the follower's step function as a state machine.
Part 4 lists what the follower checks before custody signs.
Part 5 defines heads, attestations and certificates.
Part 6 states what the tree proves about forks, and what it does not.
Part 7 defines receipts.
Part 8 lists the theorems that state properties of the protocol.

## 0 Notation particular to this document

`‹b›` is `u32le(|b|) · b`, a byte string behind its length.
`⟦b₁, …, bₙ⟧` is `u32le(n) · ‹b₁› · … · ‹bₙ›`, a list of byte strings behind its count.
`u64le(n)` is `n` as eight bytes, least significant first (`Codec/Stream.lean` `Stream.u64`).
A *layout* is a list of named fields, encoded as the concatenation of its fields in order (`Codec/Layout.lean` `Layout.codec`).
A field `byte` is `u8`; `u64` is `u64le`; `bytes` is `‹b›`; `list` is `⟦…⟧`; `oneOf` is one byte from a fixed set, any other byte refused `badTag`.
Each `bytes` and `list` field is bounded on its own by the bound its codec names, `Bounds.frameBytesMax` unless this document says otherwise (`Codec/Layout.lean` `Field.codec`).
A number that a layout carries as `bytes` holds `u64le(n)` behind its length, twelve bytes in all (`Protocol/Command/Text.lean` `Text.u64`).

The judgement forms of this document are:

| form | reading | Lean |
|---|---|---|
| `me ⊢ F, argv ⟹₀ r` | follow, serving member `me` in state `F`, answers argv `argv` with reply `r` | `Protocol/Command/Machine.lean` `start` |
| `me ⊢ F, k, res ⟹ F', p, r` | follow answers continuation `k` and step result `res` with state `F'`, persistence `p` and reply `r` | `Protocol/Command/Machine.lean` `step` |
| `W ⊢ op b ↦ a` | the writer, at World `W`, answers a request of operation `op` and payload `b` with answer `a` | `Host/Serve.lean` `handle` |
| `W ⊢ e envelope-ok` | the read envelope `e` passes on `W` | `Protocol/Envelope.lean` `Envelope.check` |
| `W ⊢ ev ⇝ s, W'` | the logged event `ev` re-derives on `W` to step `s` and World `W'` | `Kernel/Receive/Rederive.lean` `rederive` |
| `W ⊢ pg ⇝ W', t, W_b` | the page `pg` absorbs on `W` to World `W'` with steps `t`, cut at the writer's stated base `W_b` | `Protocol/Command/Machine.lean` `absorbPage` |

`F` ranges over follow states, `k` over continuations, `res` over step results, `r` over replies, `p` over persistence, `c` over signed calls, `u` over unsigned calls, `pg` over log pages.
`F.W` is follow's World.

## 1 Parties, channels and trust

### 1.1 Parties

| party | process | holds | role |
|---|---|---|---|
| member | `nd` (`client/src/bin/nd.rs`) | custody: current key, next key, the holding of the next secret; the attempt store | signs bytes it is handed; freezes calls; carries frames between the two sockets |
| follower | `host follow STORE MEMBER_HEX GRANT_HEX` (`Host/Follow.lean` `loop`) | the member's own Store and the World folded from it | parses argv, catches up, plans, settles; decides every step |
| writer | `host serve STORE` (`Host/Serve.lean` `machine`) | the World's one log | judges each signed call once; serves log pages and base pages |
| sponsor | a member that runs `enroll` and `invite` | its member key | enrols a join token; signs an invitation that pins a base |
| resident | a hosted member served by `nd --stdio` (`client/src/stdio.rs`) | a one-record custody | runs member verbs; custody refuses `precommit` and `signNext` by `noRotation` (`Protocol/Table.lean` `CustodyRefusal.noRotation`) |

A follower serves one member.
Its identity is `Self` (`Protocol/Command/Machine.lean` `Self`): the World's origin, the member, the member's World grant and a window.
`host follow` builds `Self` from its own Store's genesis origin, the two arguments and `Follow.window` = 128 (`Host/Cli.lean`, `Host/Follow.lean` `window`).
The origin comes from the member's own Store, never from the writer.

### 1.2 Channels

Two sockets carry the protocol (`Protocol/Table.lean` `Socket`, `Op.socket`).

| socket | served by | operations |
|---|---|---|
| `host.sock` | the writer | `submit`, `lookup`, `read`, `log`, `cancel` |
| `follow.sock` | the follower | `command`, `resume` |

`nd` opens both.
`ND_FOLLOW_SOCK` and `ND_HOST_SOCK` override their paths (`client/src/bin/nd.rs`).
A supervisor, `nd-supervise`, accepts client connections on a socket and multiplexes them onto its child's standard input and output as the child wire (§2.2).

### 1.3 Who decides

The Lean decides.
`nd` sends its argv to follow unread, performs each step follow returns, and echoes the continuation back (`client/src/run.rs`).
The steps are: sign exact bytes, relay a frame to `host.sock`, submit a frozen call through the attempt store, make sure a pending key exists, or print and exit (§3.2).
The attempt store chooses its next request by `Attempt.next` (`Protocol/Attempt.lean`), emitted as a table into the client (`Attempt.table`).
The client bounds a command at `Bounds.stepsPerCommandMax` = 64 steps and a frozen call at `Bounds.sendsMax` = 8 sends.
Rust holds two decisions the Lean does not: which attempt an argv resumes, and whether a resumed attempt that ends refused is planned again (§3.18).

### 1.4 What each party trusts

This section restates `docs/TRUST.md`.

* The writer orders the World's history.
  A member checks that history by re-deriving every event against its own World (`Kernel/Receive/Rederive.lean` `rederive`, §3.7).
* A member trusts its own executable, the codecs, the digest and signature functions, and its custody.
* The operator reads every byte of the World.
  Membership is the confidentiality boundary (`decisions/protocol.md` PROTOCOL-3).
* A thin member trusts the sponsor key it holds out of band and the history before the pinned base (§3.12).
  The theorem for member history carries this as the premise `keyFaithful` (§8).
* A receipt shows an answer against a given set of roots.
  It does not authenticate the head that carries those roots (§7).
* A certificate shows that the holder of a listed key endorsed a head.
  It does not show that the head is lawful (§5.3).
* Comparing heads detects a split only across a comparison path that the split does not cut (§6).

## 2 The wire

### 2.1 Frames

A frame is the same on either socket, in either direction (`Protocol/Frames.lean` `socketFrame`).

```
frame   ::= u32le(n) · body                 n = |body|, n ≤ Bounds.frameBytesMax
body    ::= u8(op) · payload                a request
          | u8(status) · payload            a reply
```

`Bounds.frameBytesMax` is 262144.
The bound applies to the body as a whole: its first byte and every field together (`Protocol/Frames.lean` `bodyFits`, PROTOCOL-70).

```
b = u32le(n) · b'    n ≤ Bounds.frameBytesMax    |b'| ≥ n    n ≥ 1
─────────────────────────────────────────────────────────────────  F-Frame    Stream.bytesOf, bodyParts?
frame b = (b'[0], b'[1 … n−1])
```

A reader takes four bytes as the body's length.
A length past `Bounds.frameBytesMax` is refused `pastBound` before any body byte is read.
A stream that ends inside the length or the body is refused `truncated`.
A body of length 0 carries no first byte; the client refuses it `empty` (`Protocol/Frames.lean` `bodyParts?`).

The rows of `gates/codec-vectors.tsv` at site `wire/frame` pin Lean's verdict on these bytes; `client/tests/vectors.rs` decodes the same bytes in Rust.

| bytes | verdict |
|---|---|
| `0100000007` | body `07`: first byte 7 (`cancel` as a request), empty payload |
| `00000000` | refused `empty` |
| `01000400` | refused `pastBound 0 262144 262145`: the length 262145 exceeds the bound |
| `010000` | refused `truncated 0 4`: three bytes cannot hold the length |
| `0a000000010203` | refused `truncated 4 10`: the length says 10, three bytes follow |
| `02000000050609` | refused `trailing 6`: decoded as one buffer, a byte remains after the frame |
| (empty) | refused `truncated 0 4` |

### 2.2 The child wire

Between a supervisor and its child (`host serve`, or `nd-attach`) a frame carries a connection identifier (`Host/Wire.lean`).

```
child-frame ::= u32le(n) · u32le(conn) · u8(x) · payload      5 ≤ n ≤ Bounds.childBodyMax
```

`Bounds.childBodyMax` is `Bounds.frameBytesMax + 4` = 262148.
Toward the child, `x` is a request's op code or `hangupCode` = 255 (`Protocol/Table.lean` `hangupCode`).
A hang-up says connection `conn` has ended; its payload is the name of a `CloseReason` (§2.9).
The child acknowledges a hang-up with `closed ‖ the same name` (`Protocol/Table.lean` `ack`; `Host/Serve.lean` `hangUpAnswer`).
A hang-up whose payload names no reason is refused `badHangup`.
Toward the supervisor, `x` is a status byte.
The child stops reading, by a name of `Host.Stop`, on a body outside `5 ≤ n ≤ Bounds.childBodyMax` (`badLength`), on a stream that ends inside a frame (`truncated`), at a frame boundary (`eof`), on a read error (`readFailed`), or when its frame budget is spent (`lifetime`) (`Host/Wire.lean` `readFrame`).

Rows at site `wire/child`:

| bytes | verdict |
|---|---|
| `0900000003000000ff69646c65` | connection 3, byte 255 (hang-up), payload `idle` |
| `09000000090000000466756c6c` | connection 9, byte 4, payload `full`: as a reply, `closed full` |
| `0400000001000000` | refused `badLength 4`: a body with no byte after the connection |
| `05000400` | refused `pastBound 0 262148 262149` |

### 2.3 Status bytes

Every reply on either socket begins with a status byte (`Protocol/Table.lean` `Status`).

| status | code | meaning |
|---|---|---|
| `ok` | 0 | answered; for `lookup`, committed |
| `refused` | 1 | refused by name; the payload is the name; for `submit` and `lookup`, final |
| `uncertain` | 2 | the writer cannot say whether the call committed |
| `absent` | 3 | `lookup` only: the call is not in the log and may still land |
| `closed` | 4 | the supervisor closed the connection; the payload is a `CloseReason` name |
| `declined` | 5 | refused by name and not recorded; not final |

A byte outside the table decodes to nothing (`Status.ofCode?`).

### 2.4 Operations

Seven operations exist (`Protocol/Table.lean` `Op`).

| op | code | socket | effect | request payload | receiver named in the table |
|---|---|---|---|---|---|
| `submit` | 1 | host | write | signed call bytes | `Nanodregg.Kernel.Receive.judge` |
| `lookup` | 2 | host | read | signed call bytes | `Nanodregg.Kernel.World.journalAt` |
| `read` | 3 | host | read | read envelope; `start` is a byte offset | `Nanodregg.Host.Page.basePage` |
| `log` | 4 | host | read | read envelope; `start` is a step count | `Nanodregg.Host.Page.kept` |
| `command` | 5 | follow | read | `commandLayout` | `Nanodregg.Protocol.Command.start` |
| `resume` | 6 | follow | read | `resumeLayout` | `Nanodregg.Protocol.Command.step` |
| `cancel` | 7 | host | write | `cancelEvent sig call` | `Nanodregg.Kernel.Receive.cancel` |

Only `submit` and `cancel` may append to the log (`Protocol/Proofs/Table.lean` `effect_write_iff`), and both are on `host.sock` (`write_on_host`).
Op codes and receivers are injective (`code_injective`, `receiver_injective`).
No op code equals `hangupCode` (`hangup_not_op`).
The receiver column is data: no gate resolves it, and `receiver_injective` is the only theorem that reads it. Each name is the declaration at the centre of the answer; the declarations the writer runs are those of §2.7.

### 2.5 Payloads

The payloads on `follow.sock` (`Protocol/Table.lean`):

```
commandLayout  = [list argv]
resumeLayout   = [bytes k, bytes result]
```

A `command` payload larger than `Bounds.argvBytesMax` = 132096 is refused `pastBound` (`Protocol/Frames.lean` `commandFrame`).
`Bounds.argvBytesMax` is `2 · Kernel.Bounds.eventBytesMax + 1024`, so `receipt CALL` with the call in hex fits for every call the kernel admits (`Protocol/Proofs/Command.lean` `receipt_argv_fits`).

The reply to `command` or `resume` is `ok · step`, where `step` is a step frame (§3.2), or `refused · NAME` for a frame follow refuses before or after the machine (§3.17).

The payloads on `host.sock`:

```
envelopeLayout        = [bytes world, bytes member, bytes grant, bytes from, bytes notBefore,
                         bytes validUntil, bytes key, bytes signature]
logReplyLayout        = [list events, bytes steps, bytes chain, bytes tipSteps, bytes tipHeight,
                         bytes baseSteps, bytes baseDigest, bytes certificate]
readReplyLayout       = [bytes steps, bytes total, bytes digest, bytes chain, bytes bytes,
                         bytes certificate]
expiredRefusalLayout  = [bytes refusal, u64 height]
```

`submit` and `lookup` carry the call's canonical bytes (`kernel.md`).
`cancel` carries `cancelEvent sig call` (§2.8).
`log` and `read` carry a read envelope (§2.6).

The `ok` reply to `submit`, `lookup` or `cancel` of a committed call is a receipt: `u64le(height) · turn digest` (`Host/Serve.lean` `receipt`).
The `ok` reply to `log` is a log page in `logReplyLayout`.
The `ok` reply to `read` is a base page in `readReplyLayout`.
Every other reply payload is a name in UTF-8, except a `log` or `read` refused `expired`, whose payload is `expiredRefusalLayout`: `‹"expired"›` then the writer's height (`Protocol/Envelope.lean` `ReadRefusal.payload`).
That payload's first byte is 7; no name begins with byte 7 (`Protocol/Proofs/Envelope.lean` `expired_payload_head`).

A log page lists steps from the requested step count, in log order.
`steps` and `chain` are the writer's step count and chain after the page's last step.
`tipSteps` and `tipHeight` are the writer's tip when it built the page.
`baseSteps` and `baseDigest` are the writer's newest durable base.
`certificate` is the writer's certificate of that base's head, or empty when the writer holds none or it exceeds `Bounds.certificateBytesMax` = 1424 (`Host/Page.lean` `pageCert`).
The follower reads a page with `logPage`, which refuses a page whose `steps` or `baseSteps` exceeds `tipSteps` (`Protocol/Command/Machine.lean` `logPage`).

A base page carries World bytes `[start, start + len)` of the writer's newest base, with that base's step count, total size, digest and chain, and the writer's certificate of the base's head (`Host/Page.lean` `basePage`).
The digest is `Hash.digest "nanodregg/host/base-digest/v1"` of the World bytes (`Host/Keys.lean` `domBaseDigest`).

### 2.6 The read envelope

A read envelope asks the writer to serve the log, or the newest base, to a member (`Protocol/Envelope.lean` `Envelope`).
Its signed message is:

```
Envelope.message(world, member, grant, start, notBefore, validUntil)
  = "nanodregg/protocol/read-envelope/v3" · bytes(world) · bytes(member) · bytes(grant)
    · u64le(start) · u64le(notBefore) · u64le(validUntil)
```

`bytes(d)` is a digest's canonical bytes (`kernel.md`).

```
e.world = W.origin
e.validUntil ≤ e.notBefore + Kernel.Bounds.windowMax
currentKey(W, e.member) = e.key
verify(e.key, Envelope.message(e.world, e.member, e.grant, e.start, e.notBefore, e.validUntil), e.signature)
mayFollow(W, e.member, e.grant)
e.notBefore ≤ W.height
W.height ≤ e.validUntil
──────────────────────────────────────────────────────────────  E-Ok    Envelope.check
W ⊢ e envelope-ok
```

The writer checks the premises in the order written and refuses at the first that fails.
The refusals, in that order, are `wrongWorld`, `wideWindow`, `unknownKey`, `badSignature`, `noFollowGrant`, `notYet` and `expired H` with `H` = `W.height` (`ReadRefusal`).
An envelope that does not decode is refused `badEnvelope`.
`Kernel.Bounds.windowMax` is 1024.
`currentKey` is the slot key of a live member cell (`Protocol/Envelope.lean` `currentKey`).
`mayFollow` holds when the grant is a live World grant held by the member, carrying `observe`, every link up to a founder's root grant live (`Kernel/Receive/Follow.lean` `mayFollow`).
`Protocol/Proofs/Envelope.lean` `Envelope.check_ok_iff` restates the rule as an equivalence.
`Envelope.check_ok_within` bounds what a replayed envelope reads to one window of heights.
`Envelope.check_expired_authenticated` says the writer states its height in `expired` only to the current key of a live member whose follow grant is live.

### 2.7 The writer's answer

The writer answers each frame from its World as the current batch has advanced it (`Host/Serve.lean` `handle`).
An answer is a reply, a commit of one step with a reply, or a deferral to the page builder.
Every committed step is `World.step`'s (`Host/Proofs/Serve.lean` `machine_commits`).

The writer's decision for `submit`:

```
decodeCall(b) = none
────────────────────────────────────  W-Submit-Undecodable    handle, FrameRefusal.undecodableCall
W ⊢ submit b ↦ declined undecodableCall

decodeCall(b) = c    W.journalAt(txId c) = (h, d)
────────────────────────────────────────────  W-Submit-Journaled    handle
W ⊢ submit b ↦ ok (u64le(h) · d)

decodeCall(b) = c    not journaled    no recorded refusal at txId c    journalForgets(W.height, c.notBefore)
──────────────────────────────────────────────────────────────────────────  W-Submit-Forgotten    handle, forgotten
W ⊢ submit b ↦ uncertain forgotten

decodeCall(b) = c    not journaled    ¬(no recorded refusal ∧ journalForgets)    judge(W, c) = admitted t W'
──────────────────────────────────────────────────────────────────────────  W-Submit-Admit    handle
W ⊢ submit b ↦ commit (turn t) W' ; ok (u64le(W'.height) · turnDigest t)

… judge(W, c) = recorded v r W'    verdictReply(W, c, recorded v r W') = (s, n)
──────────────────────────────────────────────────────────────────────────  W-Submit-Record    handle, Settle.verdictReply
W ⊢ submit b ↦ commit (refusal r) W' ; s n

… judge(W, c) = declined v    verdictReply(W, c, declined v) = (s, n)
──────────────────────────────────────────────────────────────────────────  W-Submit-Decline    handle, Settle.verdictReply
W ⊢ submit b ↦ s n
```

`journalForgets(H, nb)` holds when `nb + 2 · Kernel.Bounds.windowMax ≤ H` (`Kernel/World.lean` `journalForgets`).
`judge` is the kernel's one decision on a call: admitted, refused and recorded, or refused and declined (`Kernel/Receive/Submit.lean` `judge`, `kernel.md`).

The status of a refused reply is one rule (`Protocol/Settle.lean` `verdictReply`):

| outcome | status | name |
|---|---|---|
| `recorded v` | `refused` | `v`'s name |
| `declined v`, the call's id holds a recorded refusal with code `k` | `refused` | `codeName k` |
| `declined v`, `c.validUntil ≤ W.height` | `refused` | `v`'s name |
| `declined v`, otherwise | `declined` | `v`'s name |

A reply is `refused` exactly when the refusal is recorded now, was recorded before, or the call's window has passed (`Protocol/Proofs/Settle.lean` `final_iff_recorded`).

The writer's decision for `lookup`, after decoding (`declined undecodableCall` otherwise):

| condition, first that holds | reply |
|---|---|
| the journal holds `(h, d)` at `txId c` | `ok u64le(h) · d` |
| the refusals hold code `k` at `txId c` | `refused (codeName k)`; `refusedFinal` if `k` has no name |
| `journalForgets(W.height, c.notBefore)` | `uncertain forgotten` |
| `c.validUntil ≤ W.height` | `refused expired` (`Host/Proofs/Serve.lean` `lookup_expired_final`) |
| otherwise | `absent` |

The writer's decision for `cancel`: the payload must begin with byte `eventCancel` = 2 and read by `cancelParts` into a signature `sig` and call bytes that decode to a call `c`; otherwise `declined undecodableCall`.
A journaled call answers `ok` with its receipt.
An unrecorded call past `journalForgets` answers `uncertain forgotten`.
Otherwise the writer decides once with `Receive.cancel(W, c, sig)` (`Kernel/Receive/Submit.lean` `cancel`): `recorded` commits the cancel record and answers by `verdictReply` (`refused cancelled`); `declined` answers by `verdictReply` and commits nothing (`Host/Proofs/Serve.lean` `step_cancel`).

The writer's decision for `log` and `read`: an envelope that decodes and passes (§2.6) defers to the page builder with `start`; a refusal answers `refused · ReadRefusal.payload`.
The page builder answers `ok` with a page, or `refused` with a name of `Host.Page.Fault`: `corrupt`, `badIndex`, `tooLarge`, `pastEnd`, `shortBase`, `beforeLog`, `checkpointed` (`Host/Deployed.lean` `pager`).
A page whose IO failed is refused `pageIo`; the writer serves on (`Host/Loop.lean` `pageIoReply`).

`command` and `resume` on `host.sock` are refused `wrongSocket`; an unknown byte is refused `unknownOp`.
A frame refusal is `declined` when it decided nothing about a call (`undecodableCall`, `stopped`) and `refused` otherwise (`Host/Serve.lean` `FrameRefusal.final`).

### 2.8 Page events

A log page carries each step as an event (`Protocol/Table.lean` `eventBytes`).

```
event ::= 00 · call                          an admitted Turn
        | 01 · call                          a recorded refusal, no cancel signature
        | 02 · u64le(n) · sig · call         a recorded cancel; 0 < n = |sig| ≤ Kernel.Bounds.cancelBytesMax
```

`Kernel.Bounds.cancelBytesMax` is 64.
`eventOf` reads an event back and gives nothing for an empty event, another first byte, or a tag-2 event whose length does not read, is 0, exceeds the bound, or runs past the event (`cancelParts`).
The `cancel` op's payload is the tag-2 encoding, the same bytes the log serves (`cancelEvent`).

### 2.9 Closes

A supervisor closes a connection with `closed · NAME`, and nothing follows on it (`Protocol/Table.lean` `CloseReason`).

| name | when |
|---|---|
| `idle` | silent at a frame boundary with no request in flight for `Bounds.idleMsMax` = 300000 ms |
| `frameStalled` | a started frame incomplete after `Bounds.frameMsMax` = 30000 ms |
| `frameRefused` | a frame past `Bounds.frameBytesMax`, or an empty one |
| `replyBacklog` | a reply arrived while the previous one was unread |
| `replyWriteFailed` | a reply write failed or exceeded `Bounds.replyWriteMsMax` = 30000 ms |
| `replyTimeout` | a request had no reply for `Bounds.replyMsMax` = 120000 ms |
| `full` | `Bounds.connectionsMax` = 64 connections open, or `Bounds.peerConnectionsMax` = 8 at `nd-attach` |
| `ended` | `nd-attach`: a frame for a connection that already ended |
| `unreachable` | nothing behind the socket answers |
| `peerLeft` | the client ended its stream at a frame boundary (named to the child) |
| `peerRefused` | the peer's credentials are not the ones the supervisor was started for |

A close is not a verdict on a request in flight.
A frozen call in flight at a close is unsettled, and its attempt goes on by `lookup`.
`Bounds.replyMsMax < Bounds.idleMsMax` (`Protocol/Proofs/Table.lean` `Bounds.reply_within_idle`).

### 2.10 Bounds

| bound | value | bounds |
|---|---|---|
| `Bounds.frameBytesMax` | 262144 | one frame body |
| `Bounds.argvBytesMax` | 132096 | one `command` payload |
| `Bounds.stepsPerCommandMax` | 64 | steps the client takes for one command |
| `Bounds.sendsMax` | 8 | sends of one frozen call |
| `Bounds.pagesPerCommandMax` | 28 | log or base pages one catch-up reads |
| `Bounds.pageStepsMax` | 64 (`Host.recordTurnsMax`) | steps one log page carries |
| `Bounds.pageBytesMax` | 128289 | event bytes of one log page; World bytes of one base page |
| `Bounds.certificateBytesMax` | 1424 | a certificate on a log page |
| `Bounds.pageCertifiersMax` | 16 | signatures in a certificate on a log page |
| `Bounds.hintBytesMax` | 512 | an `uncertain` end's hint payload |
| `Bounds.replyMsMax` | 120000 | the client's wait for one reply |

`Bounds.pageBytesMax` is `Bounds.frameBytesMax` less the `resume` framing (9), the `log` reply framing (1553) and the largest page-asking continuation (132293), so a page and the continuation that asked for it fit one frame (`Protocol/Proofs/FrameFit.lean` `resume_frame_fits`).
Every event the kernel admits fits a page (`Host/Proofs/Page.lean` `budget_fits_event`).
`2 · Bounds.pagesPerCommandMax + 5 ≤ Bounds.stepsPerCommandMax` (`Protocol/Proofs/Table.lean` `Bounds.pages_fit_steps`).

## 3 The follower's step function

### 3.1 State

Follow holds three things between frames (`Protocol/Command/Machine.lean` `Follow`).

```
Follow ::= { W : World, download : Download?, verified : (nat × bytes)? }
```

`W` is follow's World.
It is persisted in the member's Store.
`download` is a base download in progress (§3.12); `verified` is the newest writer base follow verified itself, as its own step count and the digest of its own World there (§3.13).
Both live in memory only (`Memory`); a restarted follow has neither.

A *continuation* `k` is the encoding of a state (`State`, `stateLayout`):

```
stateLayout = [list argv, byte phase, list acc]
```

`k` holds the argv, the phase and the results so far, and nothing else.
The client echoes `k` and never reads it.
At every step follow decodes `k` and parses its argv again; every plan is derived again from follow's World.
`k(argv, φ, acc)` below names the bytes of that state.
A state whose encoding exceeds a frame is refused `badState` (`next`).

### 3.2 Steps out

Follow answers each frame with one step (`Protocol/Command/Machine.lean` `Reply`; tags `Protocol/Table.lean` `Step`; layouts `Step.layout`).

| step | tag | fields | what the client does |
|---|---|---|---|
| `done` | 0 | `byte exit, bytes stdout, bytes stderr` | prints, exits with `exit` |
| `sign` | 1 | `bytes message, bytes k` | custody signs `message` with the current key |
| `host` | 2 | `oneOf op, bytes payload, bytes k` | sends `op payload` to `host.sock`; `op` ∈ `Op.relayable` = {`lookup`, `read`, `log`, `cancel`} |
| `submit` | 3 | `bytes call, bytes k` | freezes `call` as an attempt and drives it to an end (§3.18) |
| `precommit` | 4 | `bytes k` | custody makes sure a pending key exists |
| `signNext` | 5 | `bytes message, bytes k` | custody signs with the next key and arms the rotation |
| `signIncoming` | 6 | `bytes message, bytes k` | custody signs an envelope message with the armed rotation's incoming key |

`submit` is not relayable: a call reaches the writer only through the attempt store (`Op.relayable`).
A step that does not fit one frame has no bytes, and follow refuses the frame `stepTooLarge` (`Protocol/Command/Wire.lean` `Reply.bytes`; `Host/Follow.lean` `answer`).
`Reply.ofBytes` is the client's one reading of a step (`Protocol/Proofs/Wire.lean` `Reply.ofBytes_bytes`).

### 3.3 Results in

A `resume` carries the continuation and the result of the step it asked for (`resumeLayout`).

| step asked | result |
|---|---|
| `host` | the writer's reply: `u8 status · payload` |
| `sign`, `signNext`, `signIncoming` | `ok · signResultLayout`, or `refused · custodyRefusalLayout` |
| `precommit` | `ok · precommitResultLayout`, or `refused · custodyRefusalLayout` |
| `submit` | `u8 (Attempt.Action.code a) · payload`, the attempt's end |

```
signResultLayout      = [bytes key, bytes next, bytes signature]
precommitResultLayout = [bytes next, bytes pending]
custodyRefusalLayout  = [oneOf refusal]
```

`signResultLayout` gives custody's current key, its next key and the signature (`Signed`).
For `signNext`, `key` is the next key and `next` the pending key.
A custody refusal is one of `fileRefused`, `exists`, `shape`, `holdingAbsent`, `noPending`, `rotationInFlight`, `mismatch`, `io`, `envelopeOnly`, `noRotation`, `notArmed` (`CustodyRefusal`).

### 3.4 Commands and phases

`parse` reads an argv into a command (`Protocol/Command/Verb.lean` `parse`, `Cmd`).
An argv whose encoding exceeds `Bounds.argvBytesMax` is refused `argvPastBound`.
`Verb.usage` gives each verb's form.
`sync --post OBJ` parses to the command `post OBJ`; `read OBJ ?` to `describe OBJ`; `read OBJ REL K [PREFIX]` to `rangeRead`.

Commands fall in four classes.

| class | commands | Lean |
|---|---|---|
| read-only: sign no call | `read`, `describe`, `rangeRead`, `sync`, `receipt` | `readOnly` |
| submitting: plan, sign and submit one call | `enroll`, `install`, `create`, `write`, `law`, `invoke`, `grant`, `retire`, `rotate`, `issue`, `account`, `transfer`, `credit`, `post` | `submits` |
| signing without submitting | `init`, `invite`, `cancel` | |
| adopting | `adopt` | |

The phase in a continuation says which result the next `resume` carries.

| phase | acc | result awaited | commands |
|---|---|---|---|
| 1 | `[start, pages, upTo, tried]` | custody's signature of a read envelope | all but `init`, `adopt` |
| 1 | `[]` | custody's signature of `whoami` | `init` |
| 2 | `[start, signed, pages, upTo, tried]` | the writer's reply to `log` | all but `init`, `adopt` |
| 2 | `[first]` | custody's signature of the join message | `init` |
| 3 | `[signed, msg]` | custody's signature of a call message | submitting |
| 4 | `[out, call]` | the attempt's end | submitting |
| 5 | `[]` | custody's `precommit` answer | `rotate` |
| 6 | `[off, pages, upTo, tried]` | custody's signature of a base envelope | `adopt` |
| 7 | `[off, pages, upTo, tried]` | the writer's reply to `read` | `adopt` |
| 8 | `[signed, unsigned]` | custody's signature of an invitation | `invite` |
| 9 | `[]` | custody's signature of a cancel | `cancel` |
| 10 | `[]` | the writer's reply to `cancel` | `cancel` |
| 11 | `[signed, unsigned]` | custody's signature of an attestation | `sync --attest` |

Numbers in `acc` are `u64le` byte strings.
`tried` is a bit set: the value 1 (`expiredBit`) records the one re-sign after `expired`; 2 (`incomingBit`) the incoming key; 4 (`saidCancelledBit`) and 8 (`saidCommittedBit`) the writer's answer to a `cancel` (§3.14).
Phases 1, 3, 5, 6, 8, 9 and 11, and phase 2 of `init`, await custody (`custodyPhase`).

An envelope message for a catch-up is

```
envelopeMessage(me, start, upTo) = Envelope.message(me.world, me.member, me.grant, start, upTo − me.window, upTo)
```

so every envelope follow signs is good for one window of heights ending at `upTo` (`envelopeMessage`).

### 3.5 Start

```
parse(argv) = error r
──────────────────────────────────────  S-Parse    start
me ⊢ F, argv ⟹₀ refused (parse r)

parse(argv) = ok (init s)
──────────────────────────────────────  S-Init    start
me ⊢ F, argv ⟹₀ sign(whoami, k(argv, 1, []))

parse(argv) = ok (adopt inv key)    adoptPin(me, inv, key) = ok i
atGenesis(F.W)    F.W.steps < i.pin.steps    off = Thin.offset(i.pin, F.download)
──────────────────────────────────────────────────────────────  S-Adopt    start, adoptPin
me ⊢ F, argv ⟹₀ sign(envelopeMessage(me, off, me.window), k(argv, 6, [off, 0, me.window, 0]))

parse(argv) = ok (sync (to s c))    s ≤ F.W.steps
──────────────────────────────────────  S-Ahead    start
me ⊢ F, argv ⟹₀ refused (ahead s)

parse(argv) = ok cmd    cmd not init, not adopt    (cmd = sync (to s c) ⇒ F.W.steps < s)
(cmd = sync (check b) ⇒ Head.verified(me.world, b) = ok a ∧ F.W.steps < a.head.steps)
U = F.W.height + me.window
──────────────────────────────────────────────────────────────  S-CatchUp    start
me ⊢ F, argv ⟹₀ sign(envelopeMessage(me, F.W.steps, U), k(argv, 1, [F.W.steps, 0, U, 0]))
```

A parse refusal ends the command before anything is signed (S-Parse).
`init` asks custody to sign the constant `whoami` = `"nanodregg/protocol/whoami/v1"` to learn its keys (S-Init).
`adopt` takes its pin from an invitation that verifies under the trusted key `key` and makes the member's own World (`adoptPin`, §3.12); it refuses by the invitation's name, `notAtGenesis` when follow's World is not a step-0 World of members, grants and the authority (`atGenesis`), and `notBehind` when follow is already at or past the pin.
`sync --to` and `sync --check` refuse `ahead` at a position follow has already passed, and `--check` refuses by `Head.Refusal`'s name an attestation that does not verify; nothing is sent (S-Ahead).
Every other command starts a catch-up from follow's own step count, with an envelope good for one window from follow's own height (S-CatchUp).

### 3.6 Catch-up

Before any phase rule, follow decodes `k` (`badState` otherwise), parses its argv (the parse refusal otherwise), and, at a custody phase, unwraps custody's result (`stepResult`).
A custody result `refused · r` ends the command `refused r`, except at a phase 1 whose `tried` holds `incomingBit`, which ends it as the writer's `unknownKey` (`custodyEnd`, `unknownKeyEnd`; PROTOCOL-56).
Any other custody result is `badResult`.
In every rule below a refusal leaves `F` unchanged and persists nothing.

```
Signed(res) = s    e = envelopeOf(me, start, upTo, s)
──────────────────────────────────────────────────────────────  C-Log    step
me ⊢ F, k(argv, 1, [start, pages, upTo, tried]), res ⟹
     F, [], host(log, Envelope.bytes e, k(argv, 2, [start, res, pages, upTo, tried]))
```

Custody's signature becomes a read envelope for the log from `start` (C-Log).

At phase 2 the writer's reply is one of three shapes.
`ok · p` with `logPage p = pg` is a page (§3.7); `ok` with a payload that is not a page is `badResult`.
`refused · p` is an envelope refusal:

```
p = expired H    tried & expiredBit = 0    upTo < H    H + me.window < 2⁶⁴
──────────────────────────────────────────────────────────────  C-Expired    envelopeRefused, reSign
me ⊢ F, k(argv, 2, [start, signed, pages, upTo, tried]), refused · p ⟹
     F, [], envelopeSign(tried, envelopeMessage(me, start, H + me.window), k(argv, 1, [start, pages, H + me.window, tried | expiredBit]))

p = unknownKey    readOnly(cmd)    tried & incomingBit = 0
──────────────────────────────────────────────────────────────  C-Incoming    envelopeRefused
me ⊢ F, k(argv, 2, [start, signed, pages, upTo, tried]), refused · p ⟹
     F, [], signIncoming(envelopeMessage(me, start, upTo), k(argv, 1, [start, pages, upTo, tried | incomingBit]))
```

`envelopeSign(t, m, k)` is `sign(m, k)` when `t & incomingBit = 0` and `signIncoming(m, k)` otherwise.
A writer more than a window ahead of follow's height refuses `expired` with its height; follow re-signs once per command for that height plus a window (C-Expired, PROTOCOL-19).
A second `expired`, or a stated height the first envelope covered, ends the command `refused expired`.
A read-only command whose envelope the writer refuses `unknownKey` re-signs once with the incoming key of an armed rotation (C-Incoming, PROTOCOL-46).
A second `unknownKey`, or `unknownKey` to a command that signs a call, ends it `refused unknownKey`.
`pageIo` ends the command with exit `pageIo` and keeps what was absorbed (`notServed`).
Any other name ends the command `refused NAME`.
A reply of any other status is `badResult`.

### 3.7 Absorbing a page

Follow re-derives every event of a page on its own World with the one re-deriver (`Kernel/Receive/Rederive.lean` `rederive`; PROTOCOL-4).

```
decodeCall(b) = c    submit(W, c) = ok (t, W')
──────────────────────────────────────  R-Turn    rederive
W ⊢ turn b ⇝ turn t, W'

decodeCall(b) = c    judge(W, c) = recorded v r W'
──────────────────────────────────────  R-Refusal    rederive
W ⊢ refusal b ⇝ refusal r, W'

decodeCall(b) = c    cancel(W, c, sig) = recorded v r W'
──────────────────────────────────────  R-Cancel    rederive
W ⊢ cancel sig b ⇝ refusal r, W'
```

A Turn event re-derives by the writer's `submit`; a refusal event by `judge`, which must record it; a cancel event by `cancel` under the event's signature, which must record it.
An event that does not read (`eventOf`), a call that does not decode, a Turn the receive layer refuses, or a refusal `judge` does not record, is `eventMismatch` at log position `W.steps + 1` (`absorbStep`, `ofVerdict`).
A kernel rejection of a derived Turn is refused by the kernel's own name, for example `refusedFinal` for a writer that admits a call it recorded refused.
A cancel event `cancel` does not record is `cancelForged`.
`Kernel/Proofs/Rederive.lean` `rederiveLog_iff` states what the re-deriver decides of a log.

```
|pg.events| ≤ Bounds.pageStepsMax    j = pg.baseSteps − W.steps
W ⊢ take j pg.events ⇝* W_b, t_b    W_b ⊢ drop j pg.events ⇝* W', t
W'.steps = pg.steps    bytes(W'.chain) = pg.chain
──────────────────────────────────────────────────────────────  A-Page    absorbPage
W ⊢ pg ⇝ W', t_b ++ t, (W_b if W_b.steps = pg.baseSteps)
```

`⇝*` is `absorb`: the events in order, each step paired with the roots digest of the World after it.
A page of more than `Bounds.pageStepsMax` = 64 events is refused `pageTooLong` before any event is absorbed.
A page whose stated step count or chain is not follow's fold is refused `chainMismatch`.
The fold is cut at the writer's stated base: when follow's own fold passes `pg.baseSteps` on this page, the World there is returned beside the page's end (PROTOCOL-47).

Under `sync --to` and `sync --check` the page is also walked against the anchor (`absorbSync`, `syncAnchor`):

```
W ⊢ pg ⇝ W', t, W_b    syncAnchor(me, cmd) = (s, c)    anchorCheck(s, c, W.steps, W.chain, t) = forked
──────────────────────────────────────────────────────────────  A-Forked    absorbSync
the page is refused forkedWorld s
```

`anchorCheck` advances the chain over the page's steps from follow's position and compares it with `c` at step count `s` (§6.2).
A `forked` walk refuses the page and keeps nothing of it.

Phase 2 with a page:

```
hostReply(res) = (ok, p)    logPage(p) = pg    ¬(pg.events = [] ∧ pg.steps < pg.tipSteps)
F.W ⊢ pg ⇝ W', t, W_b  (absorbSync)
v = (W_b.steps, digest(bytes W_b)) if W_b exists, else F.verified
F' = F with W := W', verified := v
──────────────────────────────────────────────────────────────  C-Page    step, postOr
me ⊢ F, k(argv, 2, [start, signed, pages, upTo, tried]), res ⟹ F', steps t, postOr(F.W, t, W', pg.certificate, r₀)
```

where `r₀` is

| condition | `r₀` |
|---|---|
| `pg.steps < pg.tipSteps` and `Bounds.pagesPerCommandMax ≤ pages + 1` | `behind(pg.steps, pg.tipSteps)` |
| `pg.steps < pg.tipSteps` otherwise | `envelopeSign(tried, envelopeMessage(me, pg.steps, pg.tipHeight + me.window), k(argv, 1, [pg.steps, pages + 1, pg.tipHeight + me.window, tried]))` |
| `pg.steps = pg.tipSteps` | the tip's reply for `cmd` (§3.8) |

A page that is short of the tip and carries no event is `badResult`; it would be asked for again without end.
A page that does not absorb is refused by the name of §3.7, and follow keeps nothing of it.
A page that absorbs is kept: follow's World becomes its end, and its steps are persisted before the reply (§3.17).
A page short of the tip asks for the next page, with an envelope good for the tip the page stated plus a window.
After `Bounds.pagesPerCommandMax` = 28 pages the command ends `behind STEPS TIP`, keeping what it absorbed.

`postOr` overrides `r₀` when the page proves a fork (`Protocol/Command/Machine.lean` `postOr`):

| condition, first that holds | reply |
|---|---|
| a member's post of its head of this World sits at a step count the page walks, and follow's fold reached it with another chain (`Head.forkedSelfPost`) | `refused forkedPost` |
| the page's certificate verifies under follow's World's authority and certifies a step count the page walks, which follow's fold reached with another chain (`Head.forkedCertified`) | `refused forkedCertified` |
| otherwise | `r₀` |

In both fork replies the page stays absorbed: it is lawful on follow's fold, and the fork is the poster's or the writer's.

### 3.8 The tip

At `pg.steps = pg.tipSteps` follow is at the writer's tip, at World `W'`, and `r₀` depends on the command.

| command | `r₀` | Lean |
|---|---|---|
| `read OBJ [KEY=VALUE…]` | every expectation holds on the object's state slots, then its state as one line of text; refusals `missingCell`, `expect`, `noText` | `render` |
| `read OBJ ?` | the object's self-description; refusals `missingCell`, `wrongKind`, `noText` | `describe` |
| `read OBJ REL K [PREFIX]` | one line per row of the range; refusals `unknownRelation`, `rangePastLimit`, `badPrefix`, `rangeUnpinned`, `rangeTooLong`, `keyWidth`, `noText` | `rangeRender` |
| `sync`, `sync --to`, `sync --check`, `sync --attest` | §3.15 | `syncTip` |
| `receipt CALL`, `receipt --health [MEMBER]` | §7 | `receiptLines` |
| `cancel CALL` | §3.14 | `cancelTip` |
| `rotate` | `precommit(k(argv, 5, []))` | |
| `invite INPUT` | §3.13 | `inviteInput`, `pinOf` |
| every other submitting command | §3.9 | `body`, `signedReads`, `plan` |

### 3.9 Planning and the call signature

At the tip a submitting command is planned on follow's World `W'`.

```
Signed(signed) = s    body(me, W', s, cmd) = ok b    signedReads(W', cmd) = ok rs
plan(me, W', s.key, rs, b) = ok u
──────────────────────────────────────────────────────────────  P-Plan    step, plan
tip r₀ = sign(callMessage(u), k(argv, 3, [signed, callMessage(u)]))
```

`plan` is defined in §4.1.
A refusal of `body`, `signedReads` or `plan` ends the command `refused NAME`, with a hint on standard output when one exists (`refusedAt`, `hint`).
The key a call names is the key that signed this command's envelope, which the writer accepted (`s.key`).

```
Signed(signed) = s    Signed(res) = s₂    s₂.key = s.key
body(me, F.W, s, cmd) = ok b    signedReads(F.W, cmd) = ok rs    plan(me, F.W, s.key, rs, b) = ok u
callMessage(u) = msg    c = ⟨u, s₂.signature⟩    decodeCall(callBytes(c)) = some c
receive(F.W, c) = ok t
──────────────────────────────────────────────────────────────  P-Submit    step
me ⊢ F, k(argv, 3, [signed, msg]), res ⟹ F, [], submit(callBytes(c), k(argv, 4, [receipt(t), callBytes(c)]))
```

At phase 3 follow plans the call again on its current World and compares the message with the one custody signed.
A different message is `planMoved`: follow's World moved between the two steps, or the continuation is not the one follow handed out.
A signing key other than the envelope's is `badResult`.
Call bytes that do not decode to the same call are `badCall` (PROTOCOL-69).
Follow derives the Turn with `receive`, which checks the signature (`kernel.md`); a refusal ends the command by the receive layer's name.
`receipt(t)` is the text a committed call prints: `tx TXID` and one `id ID` line per created cell.

### 3.10 Settlement

The client hands step 4 the attempt's end (§3.18).
Follow checks a final end against its own World (`settled`, PROTOCOL-46, PROTOCOL-64).
`ownSettle(W, cb)` is `settleOf(me, W, c)` for the call `c` that `cb` decodes to.

| attempt end `a` | condition on follow's World | reply | exit |
|---|---|---|---|
| `committed` | `ownSettle` is `committed h td` | `done ok`, printing `out` | `ok` |
| `committed` | otherwise `v` | `hostContradicted committed V` | `hostContradicted` |
| `refused` | `ownSettle` is `refused code` | `refused NAME`, `NAME` = `codeName code`, or `codeK` when code `K` has no name (`settledName`) | `refused` |
| `refused` | `ownSettle` is `expired` | `refused expired` | `refused` |
| `refused` | otherwise `v` | `hostContradicted refused V` | `hostContradicted` |
| `declined` | | `declined NAME`, the writer's name | `declined` |
| `open` | | `open` | `open` |
| `contradicted` | | `hostContradicted TEXT` | `hostContradicted` |
| `uncertain` | | `uncertain`, with `hint confirm: refused NAME` on standard output when the payload's first line names a refusal of `hintNames` | `uncertain` |
| `badReply` | | `badReply` | `client` |
| any other code | | `refused badResult` | `refused` |

A phase-4 continuation under a command that does not submit is `badState` (`settleStep`, `submits`).
Follow says `ok` for a write only when its own World journals the call (`Spec/Proofs/Claims.lean` `Consent.okCommitted`).

The settlement of a call on a World is one function (`Protocol/Settle.lean` `ofReceipt`, `Protocol/Command/Machine.lean` `settleOf`).
Its input is the answer of the receipt follow builds on its own World (§7.1).

```
answer = committed h td                                              ⟹ committed h td
answer = refused h code m,   c.validUntil ≤ h + 2 · windowMax          ⟹ refused code
answer = refused h code m,   otherwise                                ⟹ open
answer = absent,   journalForgets(W.height, c.notBefore)              ⟹ forgotten
answer = absent,   c.validUntil ≤ W.height                            ⟹ expired
answer = absent,   staleBehind(me, W, c)                              ⟹ refused staleCode
answer = absent,   otherwise                                          ⟹ open
```

The cases are tried in the order written.
`staleBehind(me, W, c)` holds when `c` is the member's own call for its own World, planned at a height follow has reached, its authority passes on `W` (`signedBy`), and its pins fail on `W` (`checkPins`): the writer's own order (`staleBehind`, PROTOCOL-73).
`Protocol/Proofs/Command.lean` `staleBehind_declined` ties it to the writer's `submit`.
`staleCode` is the code a stale refusal would carry; the kernel never records it (`Kernel/Receive/Submit.lean` `staleCode`).
The settlement is printed as `committed H TD`, `refused CODE`, `expired`, `open` or `forgotten` (`Settle.Verdict.text`).
`committed`, `refused` and `expired` are final; `open` and `forgotten` are not (`Protocol/Proofs/Settle.lean` `settle_final_never_admits`, `settle_open_not_final`; `Protocol/Proofs/Behind.lean` `staleBehind_final`).

### 3.11 Rotation

```
precommitOf(res) = (nk, pk)    s = ⟨nk, pk, ε⟩
body(me, F.W, s, rotate) = ok (rotate nk (nextKeyDigest pk))    plan(me, F.W, nk, {}, b) = ok u
──────────────────────────────────────────────────────────────  P-Rotate    step
me ⊢ F, k(argv, 5, []), res ⟹ F, [], signNext(callMessage(u), k(argv, 3, [Signed.bytes s, callMessage(u)]))
```

`rotate` asks custody for its next and pending keys after the catch-up (§3.8), plans the rotation to the next key, precommitting the digest of the pending key, and has the next key sign it.
Phase 3 then runs P-Submit with `s.key` = the next key.
Custody advances its keys only on its own settlement of that attempt as committed (`Protocol/Table.lean` `Step.signNext`).

### 3.12 Adoption

A thin member starts from a base the writer serves, pinned by an invitation (PROTOCOL-14, PROTOCOL-42).

```
Signed(res) = s    e = envelopeOf(me, off, upTo, s)
──────────────────────────────────────────────────────────────  T-Read    step
me ⊢ F, k(argv, 6, [off, pages, upTo, tried]), res ⟹ F, [], host(read, Envelope.bytes e, k(argv, 7, [off, pages, upTo, tried]))
```

At phase 7 follow takes the pin again from the argv (`adoptPin`), reads the base page (`Thin.Page.ofBytes`; `badPage` otherwise), requires `off` = `Thin.offset(pin, F.download)` (`pageMismatch` otherwise), and decides the page with `Thin.accept` (`Protocol/Thin.lean` `accept`).

`Thin.accept(pin, dl, pg)` checks, in order:

| check | when it fails |
|---|---|
| `pg.steps = pin.steps` | `baseMoved` |
| `pg.digest = pin.digest` | `baseMismatch` |
| `pg.total ≤ B.bytesMax` | `baseTooLarge` |
| a held download for this pin has the same total | `pageMismatch` |
| `pg.bytes` nonempty and within the total | `pageMismatch` |
| the bytes so far reach the total | `more`: the download grows, no refusal |
| the assembled bytes hash to `pin.digest` | `baseMismatch` |
| the bytes decode to a World | `baseUndecodable` |
| that World's step count is `pin.steps` | `baseMismatch` |

```
Thin.accept(pin, F.download, pg) = done W'
atGenesis(F.W)    W'.origin = me.world    Head.certifiesWorld(W', pg.certificate) = ok
──────────────────────────────────────────────────────────────  T-Adopt    step
me ⊢ F, k(argv, 7, acc), ok · p ⟹ ⟨W', none, none⟩, adopt W', done ok "adopted STEPS DIGEST"

Thin.accept(pin, F.download, pg) = more d    pages + 1 < Bounds.pagesPerCommandMax
──────────────────────────────────────────────────────────────  T-More    step
me ⊢ F, k(argv, 7, [off, pages, upTo, tried]), ok · p ⟹
     F with download := d, [], sign(envelopeMessage(me, |d.got|, upTo), k(argv, 6, [|d.got|, pages + 1, upTo, tried]))
```

A download that exhausts the page budget ends `refused incomplete` and is kept in memory.
`atGenesis` is checked again at the step that adopts, since other commands may have moved follow's World since `start` (`notAtGenesis`).
An adopted World of another origin is `wrongWorld`.
Under an authority that names certifiers, the writer's certificate must certify exactly the adopted World's head; under one that names nobody, nothing is asked (`Head.certifiesWorld`, PROTOCOL-77.1, §5.3).
A refusal by `Thin.accept`, `notAtGenesis`, `wrongWorld` or a certificate refusal drops the download; `incomplete` keeps it, and so does a refusal of the writer's reply.
The adopted World replaces follow's World and is sealed as follow's own newest base before the reply (§3.17).
A `read` refused `expired` re-signs once, as C-Expired does; `pageIo` ends the command `pageIo`.

### 3.13 Invitation

At the tip, `invite INPUT` checks that `INPUT` decodes as a start and makes the member's own World (`inviteInput`; `badInvitation`, the genesis refusal's name, or `otherWorld`).
It pins the newest base follow verified itself (`pinOf`):

```
F'.verified = (s, d)    s = pg.baseSteps    d = pg.baseDigest
──────────────────────────────────────  I-Pin    pinOf
pin = ⟨s, d⟩
```

A base follow never sat at is `noBase`; one at the stated step count whose stated digest is not follow's own is `baseMismatch`.
The sponsor signs its own digest, never the writer's claim.
Follow asks custody to sign `Invite.message(u)` for the invitation's unsigned bytes `u` (input, pin, sponsor member, envelope key), at phase 8.
At phase 8 follow requires the signing key to be the envelope's and verifies the signature itself, then prints `invite HEX` (`badResult` otherwise).

### 3.14 Cancel

`cancel CALL` closes a member's own call that is sent but not settled (PROTOCOL-63, PROTOCOL-71).
It runs two catch-ups.

At the tip of the first catch-up (`tried & (saidCancelledBit | saidCommittedBit) = 0`), follow asks custody to sign `cancelMessage(c)` = `"nanodregg/kernel/cancel-signature" · bytes(txId c)`, at phase 9 (`cancelTip`).

```
Signed(res) = s    decodeCall(cb) = c    cancel(F.W, c, s.signature) = recorded …
──────────────────────────────────────────────────────────────  X-Send    sendCancel
me ⊢ F, k(argv, 9, []), res ⟹ F, [], host(cancel, cancelEvent(s.signature, cb), k(argv, 10, []))
```

Follow decides the cancel on its own World with the writer's function before anything is sent.
A cancel follow's World declines ends the command by the kernel's name and is never sent (`Protocol/Proofs/Command.lean` `sendCancel_host`): `badSignature` for another member's call, `outsideWindow`, `refusedFinal` for a call already recorded.

At phase 10 the writer's answer starts the second catch-up or ends the command (`cancelAnswer`):

| writer's reply | follow |
|---|---|
| `refused cancelled` | second catch-up with `tried` = `saidCancelledBit` |
| `ok` | second catch-up with `tried` = `saidCommittedBit` |
| `declined NAME` | `declined NAME` |
| `refused NAME`, another name | `refused NAME` |
| `uncertain NAME` | `uncertain NAME`, exit `uncertain` |
| anything else | `refused badResult` |

At the tip of the second catch-up follow settles the call on its own World (`cancelSettled`):

| writer said | `settleOf(me, W', c)` | reply |
|---|---|---|
| cancelled | `refused cancelledCode` | `done ok`, printing `cancelled TXID` |
| committed | `committed …` | `refused committed` |
| cancelled | anything else `v` | `hostContradicted cancelled V` |
| committed | anything else `v` | `hostContradicted committed V` |

`cancel CALL` ends `ok` only when follow's own World holds the cancel record (`Consent.cancelOk`, §8).

### 3.15 Sync

At the tip `syncTip` answers by the mode.

| mode | reply |
|---|---|
| `sync` | `height H`, `chain C`, `roots R` of `W'` |
| `sync --to S:C` | `shared S` when `S ≤ W'.steps`, else `unreached S`; then the three lines |
| `sync --check A` | the attestation verifies again, its signer is a live member whose current key signed it (`Head.signer`; `notMember`, `staleKey`); then `shared S MEMBER` or `unreached S MEMBER`, and the three lines |
| `sync --attest` | custody signs `Head.message(u)` for `u` = the attestation bytes of `headOf(W')`, the member and the envelope key, at phase 11 |

At phase 11 follow requires the signing key to be the envelope's and prints `attest HEX` (`attestDone`).
`shared S` at the tip follows from two checks: `start` refused a position already passed, and every page on the way walked the anchor without a `forked` result (§6.2).
`sync --post OBJ` is a submitting command: its body is `invoke OBJ post` with the text of `headOf(W')` (`Head.headText`, `Head.postMethod`).

### 3.16 Ends

A command ends with `done exit stdout stderr` (`Protocol/Command/Exit.lean` `CommandExit`; classes `Protocol/Exit.lean` `CommandExit.cls`).

| end | code | standard error | class |
|---|---|---|---|
| `ok` | 0 | (output on standard output) | done |
| `refused` | 1 | `refused NAME` | fatal |
| `uncertain` | 2 | `uncertain` | restart |
| `behind` | 51 | `behind STEPS TIP` | restart |
| `client` | 52 | nd's own failure; `badReply` | restart |
| `declined` | 53 | `declined NAME` | restart |
| `open` | 54 | `open` | restart |
| `hostContradicted` | 55 | `hostContradicted CLAIM FOLLOWSAID` | restart |
| `pageIo` | 57 | `pageIo` | restart |

A `refused NAME` may carry a hint line on standard output (`hint`).
The names `refused` prints are the parse refusals, the receive refusals and kernel rejections (`kernel.md`), the writer's names, and follow's own: `eventMismatch`, `badState`, `badResult`, `planMoved`, `expect`, `missingCell`, `tooManyPins`, `chainMismatch`, `pageTooLong`, `noText`, `expired`, `badCall`, `unknownRelation`, `rangePastLimit`, `badPrefix`, `badKey`, `forkedWorld`, `ahead`, `forkedPost`, `forkedCertified`, and the names of `Head.Refusal`, `Head.CertRefusal`, `Thin.Refusal`, `CustodyRefusal` and `Invite.Refusal` (`Refusal.name`, `hintReps`).

What each settlement-class end says:

| end | meaning | final |
|---|---|---|
| `done ok` (submitting) | follow's World journals the call | yes |
| `refused NAME` after step 4 | follow's World holds the call's recorded refusal, or the window has passed, or the call is stale behind | yes |
| `refused planMoved` | the plan moved before submission; nothing was submitted | yes, nothing sent |
| `declined NAME` | the writer refused by name and recorded nothing; the attempt stays open | no |
| `open` | every send answered `absent`, the window is live; the attempt stays open | no |
| `uncertain` | nothing settled this run; the attempt stays frozen | no |
| `hostContradicted` | the writer's word disagrees with follow's World; the attempt stays open | no |
| `behind` | the catch-up hit its page budget; progress is kept | not a settlement |
| `pageIo` | the writer's IO failed on a page; progress is kept | not a settlement |

### 3.17 The follow loop

`host follow` reads one frame at a time from its supervisor (`Host/Follow.lean` `loop`, `answer`).

| frame | answer |
|---|---|
| `command` payload decodes by `commandFrame` | `start` |
| `resume` payload decodes by `resumeFrame` | `step` |
| `command` or `resume` that does not decode | `refused undecodableCommand` / `refused undecodableResume` |
| a hang-up | `closed NAME` |
| another op | `refused wrongSocket` |
| an unknown byte | `refused unknownOp` |

A step persists before it is answered.
`steps t` with `t` nonempty appends `t` to follow's own Store as one batch record (`Host.append`); a failed append answers `uncertain` and stops the loop.
`adopt W'` seals `W'` as follow's own newest base; a failed seal answers `uncertain` and stops the loop.
A step whose reply has no bytes is refused `stepTooLarge` after its persistence (HOST-77).
Follow's memory (`download`, `verified`) moves only after the persistence.

The loop also compares positions follow had already passed before the page (`behindOr`):

| condition, first that holds | reply |
|---|---|
| a post on the page names a step count at or below follow's position before the page, and follow's Store holds another chain there (`Head.behindPosts`, `Head.forkedBehindPost`) | `refused forkedPost` |
| the page's certificate certifies a step count at or below follow's position before the page, and follow's Store holds another chain there (`Head.behindCertified`) | `refused forkedCertified` |
| otherwise | the step's reply |

A step count below the oldest file follow's Store keeps is not compared.

### 3.18 The attempt store and resumption

A `submit` step hands the client a signed call.
The client writes the call to its attempt directory once, before any byte leaves, and drives it with `submit` and `lookup` of the same bytes, and `confirm` and `probe` by `receipt CALL` on its own follow (`Protocol/Attempt.lean`).
`Attempt.next(sendsLeft, last)` chooses the next request from the last request and what its reply said.

| last request | seen | action |
|---|---|---|
| none | | `submit` |
| `submit` or `lookup` | `committed`, `refused` | `confirm` |
| `submit` or `lookup` | `declined` | end `declined` |
| `submit` | `unknown` (`uncertain`), `lost` | `lookup` |
| `lookup` | `unknown`, `lost` | end `uncertain` |
| `lookup` | `absent` | `probe` |
| `confirm` or `probe` | `committed` | end `committed` |
| `confirm` or `probe` | `refused` (includes `expired`) | end `refused` |
| `probe` | `open` | `submit` while sends remain; else end `open` |
| `confirm` | `open`, `forgotten` | end `contradicted` |
| `probe` | `forgotten` | end `uncertain` |
| `confirm` or `probe` | `lost` | end `uncertain` |
| any other pair | | end `badReply` |

`seen` for `submit` and `lookup` is the writer's status byte; for `confirm` and `probe` it is the first word of follow's `settle` line (`settleSeen`).
Only follow's word ends an attempt `committed` or `refused` (`Protocol/Proofs/Attempt.lean` `next_final`).
The end and its payload are step 4's result (§3.10).

An attempt left open by one run is resumed by running the same argv again.
The client keys attempts by the argv's `command` encoding, resumes follow with the attempt's own continuation and its end, and does not ask follow to plan (`client/src/run.rs` `run`).
When the resumed attempt ends `refused` and follow answers `refused`, the client starts the command afresh with `command`.
These two rules are Rust's.
A command repeated after its attempt settled signs a new call: the argv does not identify an intent.

## 4 What the member checks before signing

### 4.1 Before a call is offered

Follow offers custody a call message only through P-Plan, P-Rotate and P-Submit.
Before P-Plan, these hold.

1. The argv parses (`parse`).
2. Follow is at the writer's tip as the last page stated it, and every event on the way re-derived on follow's World (§3.7).
3. The call's body reads on follow's World (`body`): a seed or an argument text reads at the package's type (`Lang.seedOf`, `Lang.argsOf`), and an invoked object is a live programmed object (`invokedPackage`; `missingCell` or the receive layer's name).
4. The reads the command names are listed on follow's World (`signedReads`): an invoke's `--range` at THE range listing (`invokeRange`) and its `--pin`s at follow's rows (`invokePoint`).
5. The unsigned call is derived on follow's World (`planUnchecked`, below).
6. Follow's World admits the derived Turn (`plan`; the kernel's rejection by name otherwise).

```
u₀ = { world = me.world, member = me.member, key = key,
       notBefore = W.height, validUntil = W.height + me.window,
       pins = [], rowPins = [rowPinAt(W, x) | x ∈ rs.points], ranges = rs.ranges,
       maxCharge = Kernel.Bounds.weightMax, body = b }
derivePins(W, Kernel.Bounds.touchesMax, u₀) = ok (u₁, t₁)
u = u₁ with maxCharge := t₁.charge + chargeSlack
deriveTurn(pinned(W, u.pins), rowView(W, u), ⟨u, ε⟩) = ok t
World.admit(W, t) = ok W''
──────────────────────────────────────────────────────────────  P-Derive    plan, planUnchecked
plan(me, W, key, rs, b) = ok u
```

`derivePins` derives the Turn with no signature, on a view that holds only the pinned cells.
Each cell the derivation asks for (`unpinned c`) is pinned at follow's entry for it, and the derivation runs again.
Each row the derivation asks for (`rowUnpinned`) is pinned at follow's row; a row asked for twice is the receive layer's `rowUnpinned`.
A cell the Turn would create that follow's World already holds is pinned, and the pin is kept when the Turn then no longer creates it.
After `Kernel.Bounds.touchesMax` = 512 rounds the plan is refused `tooManyPins`.
Any other refusal of the derivation is the receive layer's name.
The signed price is the derived charge plus `chargeSlack` = 4096.
`Kernel.Bounds.weightMax` is `4 · Kernel.Bounds.eventBytesMax`.
The call names follow's own World, so follow's derivation refuses `wrongWorld` if the World it follows is another.

At phase 3 follow plans again and requires the same message, the envelope's key, call bytes that read back as the call, and a `receive` that passes (P-Submit).

### 4.2 The shapes custody is asked to sign

Every message a member key signs begins with its own domain, and every pair of domains differs at a byte both hold (`Protocol/Proofs/Domains.lean`).

| shape | message | domain | asked by | Lean |
|---|---|---|---|---|
| planned call | `callMessage(u)` | `nanodregg/kernel/call-signature` | P-Plan (`sign`), P-Rotate (`signNext`) | `Ctx.callMessage` |
| read envelope | `Envelope.message(me.world, me.member, me.grant, …)` | `nanodregg/protocol/read-envelope/v3` | S-CatchUp, C-Expired, C-Incoming, C-Page, S-Adopt, T-More | `envelopeMessage` |
| join consent | `joinMessage(origin, sponsor, next, key)` | `nanodregg/kernel/join/v1` | `init`, phase 1 | `joinMessage` |
| invitation | `Invite.message(u)` | `nanodregg/protocol/invitation/v2` | `invite`, tip | `Invite.message` |
| head attestation | `Head.message(u)` | `nanodregg/protocol/head/v1` | `sync --attest`, tip | `Head.message` |
| cancel | `cancelMessage(c)` | `nanodregg/kernel/cancel-signature` | `cancel`, tip of the first catch-up | `Ctx.cancelMessage` |
| identity probe | `whoami` | `nanodregg/protocol/whoami/v1` | `init`, `start` | `whoami` |

A World's certifier signs an eighth shape, `certifyMessage` under `nanodregg/protocol/certify/v1`; no member key signs it (§5.3).
Every envelope follow offers names the member's own World, member and grant; only `start` and the step offer messages.

Two claims state the list for `step` (`Spec/Proofs/Sign.lean`).
`Consent.signs`: every call-domain message a step offers is `callMessage(u)` for the `u` that `plan` produced on follow's World after the step, from the `body` and `signedReads` of the command the continuation's argv parses to; `u.member` is `me.member`; and that World admits the derived Turn.
`Consent.signShapes`: every message a step offers is a planned call, an envelope of the member's own World, member and grant, a join consent, an invitation, a head attestation or a cancel.
The claims cover `step` and not `start`, which offers `whoami` and the first envelope.
They do not authenticate the argv: the continuation is client-held bytes (§8, the premise on the continuation's argv).

### 4.3 What custody checks

Custody is Rust (`client/src/custody.rs`); its refusals are the Lean table's names (`CustodyRefusal`).
Custody reads a key file only if it is a regular file, owned by the effective user and private to it (`fileRefused`).
It signs the bytes it is handed and adds nothing.
An observer custody signs only read envelope messages (`envelopeOnly`).
A resident's custody refuses `precommit` and `signNext` (`noRotation`).
`signIncoming` is refused `notArmed` with no armed rotation and `envelopeOnly` for a message that is not an envelope.

## 5 Heads, attestations and certificates

### 5.1 Heads

A head is one World's position (`Protocol/Head.lean` `Head`).

```
Head ::= { origin : digest, steps : nat, height : nat, roots : digest, chain : digest }
headOf(W) = ⟨W.origin, W.steps, W.height, W.roots, W.chain⟩
```

`steps` counts admitted Turns and recorded refusals; `height` counts admitted Turns (`kernel.md`).
`roots` is the digest of the cells', journal's, refusals' and rows' roots, what a receipt is checked against (§7).
`chain` is what binds a log: two folds from one World that agree on step count and chain are one log, or two of their link inputs collide (`Kernel/Proofs/Fold.lean` `fold_head_binds`).

### 5.2 Attestations

An attestation is a member's signed statement that its own follow's fold sits at a head.

```
unsignedLayout     = [bytes origin, u64 steps, u64 height, bytes roots, bytes chain, bytes member, bytes key]
attestationLayout  = [bytes unsigned, bytes signature]
Head.message(u)    = "nanodregg/protocol/head/v1" · u
```

```
ofBytes(b) = a    a.head.origin = origin    verify(a.key, Head.message(a.unsigned), a.signature)
──────────────────────────────────────────────────────────────  H-Verified    Head.verified
Head.verified(origin, b) = ok a

currentKey(W, a.member) = a.key
──────────────────────────────────────  H-Signer    Head.signer
Head.signer(W, a) = ok
```

The refusals are `badAttestation`, `otherWorld`, `badHeadSignature` for `verified`, and `notMember`, `staleKey` for `signer` (`Head.Refusal`).
An attestation states what one member holds.
It is not an authority over the World.
Follow makes one only of its own World's head (`attestTip`; `Protocol/Proofs/Head.lean` `attestTip_sign`).

### 5.3 Certificates

A World's authority is fixed at its genesis (`Kernel/Receive/Follow.lean` `Authority`).

```
Authority ::= { certifiers : bytes*, threshold : nat }
Authority.none = { certifiers = [], threshold = 0 }
```

The genesis input carries the authority, and the World's origin is the digest of that input (`originOf`), so the origin commits to the authority.
The genesis refuses a threshold of zero with certifiers listed, or a threshold past their count, as `badThreshold`, and a repeated certifier as `repeatedCertifier` (`checkGenesis`).
The genesis World holds the authority as one ROM cell of kind `kindAuthority` (`authorityCell`), and `authorityOf(W)` reads it back; a World with two such cells or none has no authority (`authorityOf`).
On every World an honest log folds to from a checked genesis, `authorityOf` is the genesis authority (`Kernel/Proofs/AuthorityOf.lean` `authorityOf_honest_fold`).

A certificate is a head signed by certifiers (`Protocol/Head.lean`).

```
certifiedLayout    = [bytes origin, u64 steps, u64 height, bytes roots, bytes chain]
certificateLayout  = [bytes certified, list signers, list signatures]
certifyMessage(x)  = "nanodregg/protocol/certify/v1" · x
```

`signers` are indices into the authority's list, each as `u64le` bytes; `signatures` are read in step with them.

```
A.threshold > 0    certificateOfBytes(b) = c    c.head.origin = origin
the pairs (i, s) of c.sigs are walked in order: A.certifiers[i] = k, i not seen before, verify(k, certifyMessage(c.certified), s)
the number of signers walked ≥ A.threshold
──────────────────────────────────────────────────────────────  H-Certified    Head.certified
Head.certified(A, origin, b) = ok c
```

The refusals are `noAuthority` (threshold 0), `badCertificate`, `otherWorld`, `unlisted i`, `repeated i`, `badCertifySignature i` and `belowThreshold` (`CertRefusal`).
`Protocol/Proofs/Head.lean` `certified_ok` restates what an accepted certificate is.
`certified_intersect`: when fewer than two thresholds of certifiers are listed, two certified heads were both signed by one listed certifier.
`certified_equivocation`: two such heads at one step count with different chains name a certifier that signed both.

```
authorityOf(W) = A    A.threshold = 0
──────────────────────────────────────  H-Cert-None    Head.certifiesWorld
Head.certifiesWorld(W, b) = ok

authorityOf(W) = A    A.threshold > 0    Head.certified(A, W.origin, b) = ok c    c.head = headOf(W)
──────────────────────────────────────────────────────────────  H-Cert-World    Head.certifiesWorld
Head.certifiesWorld(W, b) = ok
```

A World with no single authority cell is refused `noAuthority`; a certificate of another head is refused `otherHead`.
`certifiesWorld_ok` and `certifiesWorld_none` state the two rules.

Three consumers check certificates.

| consumer | check | on failure |
|---|---|---|
| thin adoption, `adopt` (T-Adopt) | `Head.certifiesWorld(W', pg.certificate)` on the World the pin binds | `refused` by the `CertRefusal` name; nothing adopted |
| a follower's page (C-Page, §3.17) | `Head.pageCertified(W, b)` under follow's own World's authority, then the certified chain against follow's fold | `refused forkedCertified`; an unverified certificate is evidence of nothing and is ignored |
| a stranger (`host certified INPUT_HEX CERT`) | `Certified.check(input, cert)`: decode the input; a genesis input makes its genesis, a carried start has its authority checked and its origin recomputed (`carryOriginOfStart`, PROTOCOL-85); then `Head.certified` under that authority for that origin | `badInput`, the genesis refusal, or the `CertRefusal` name |

`Protocol/Proofs/Certified.lean` `stranger_ok` states what the stranger learns: the head is certified by the threshold of distinct certifiers the input lists, for the World that input makes (a genesis's, or a carry's).

The writer produces a certificate only when started with `host serve --certify SOCK` or `host seal --certify SOCK`, through keybroker (`Host/Cli.lean`); `docs/TRUST.md` states that the deployed units do not pass that option.
A writer with no certificate serves an empty field.

What a certificate shows, restating `docs/TRUST.md`:
a certificate shows that the holder of a listed key endorsed a head, and gives evidence when that key signs two heads at one step count.
It does not show that the head is lawful: the key holder can sign one fabricated head per step count.
Until the writer's key can rotate to a precommitted successor, and its signer can restart without losing what it signed, a stolen certify key signs any head of its World for as long as that World is believed, a lost key certifies nothing again, and no consumer has an authenticated rule for finding a successor (in flight: DESIGN-TRUST §4.4c).

### 5.4 Thin adoption under a sponsor pin and a certificate

An invitation is a sponsor's signed statement of a start and a pin (`Protocol/Invite.lean`).

```
unsignedLayout     = [bytes input, u64 steps, bytes digest, bytes sponsor, bytes key]
invitationLayout   = [bytes unsigned, bytes signature]
Invite.message(u)  = "nanodregg/protocol/invitation/v2" · u
Pin ::= { steps : nat, digest : bytes }
```

`input` is one start encoding: a genesis input, or a carried start: the carry input its origin is the digest of, then the anchor's chain (`startInput`, `Start`, PROTOCOL-85).

```
ofBytes(b) = inv    inv.key = trusted    verify(inv.key, Invite.message(inv.unsigned), inv.signature)
startOrigin(inv.start) = ok o    o = me.world
──────────────────────────────────────────────────────────────  T-Pin    adoptPin, Invite.acceptStart
adoptPin(me, b, trusted) = ok inv
```

The refusals are `badInvitation`, `notSponsor`, `pinMismatch`, the genesis refusal's name and `otherWorld` (`Invite.Refusal`).
`startOrigin` of a genesis start builds the genesis, so the joiner computes the origin, and with it the authority, from the signed input; nothing is taken from the writer.
`trusted` is the sponsor key in the argv, `adopt INVITE KEY`.
The member obtains it out of band; the follower cannot tell whether the argv's key is the one the member trusts (premise `keyFaithful`, §8).

Adoption then downloads the newest base and accepts it only under T-Adopt: the bytes hash to the pin, decode to a World at the pin's step count with the member's origin, follow's World is a step-0 World, and, when the adopted World's authority names certifiers, the writer's certificate certifies exactly its head (PROTOCOL-77.1).
Without certifiers, adoption rests on the sponsor pin alone.
The certificate is checked beside the pin, under the authority read off the pinned World; it does not replace the pin.
From the adopted World on, the member is an ordinary follower; what it trusts is the history before the pin.

## 6 Fork consistency, as stated

### 6.1 What is not claimed

No claim of the tree states fork consistency at the level of operations (`decisions/protocol.md` PROTOCOL-82; `Spec/README.md`).
A signed call names no prefix of the history its signer saw (`kernel.md`, the unsigned call).
A writer can therefore hold two branches and admit one member's call on both, when its pins agree on both.
Neither fork-linearizability, nor fork-sequential consistency, nor fork* holds.
What holds is prefix agreement for members who compare heads, stated below.
The route to an operation-level property, a signer's head in every call compared by every follower, is in flight (PROTOCOL-82, decision 5); it is not on `main`.

### 6.2 The anchor check

Comparison walks a page's steps against a stated head `(s, c)` from follow's position `(n, ch)` (`Protocol/Head.lean` `anchorCheck`).

```
anchorCheck(s, c, n, ch, [])                   = unreached
anchorCheck(s, c, n, ch, (t, r) :: rest)       = shared      if n + 1 = s and bytes(stepLink(ch, t, r)) = c
                                               = forked      if n + 1 = s and bytes(stepLink(ch, t, r)) ≠ c
                                               = anchorCheck(s, c, n + 1, stepLink(ch, t, r), rest)   otherwise
```

`stepLink` advances the chain over one step and the roots digest after it, as the kernel's fold does (`kernel.md`).
A walk from `n` reaches every step count `s` with `n < s ≤ n + |ts|` (`Spec/Proofs/Fork.lean` `anchorCheck_reached`).

`Protocol/Proofs/Head.lean` `anchor_binds`: if follow's World is a fold of `l₀` from a start `g`, a page prefix `pre` reaches the anchor's step count with the anchor's chain, and the anchor is the head of a fold of `lg` from the same `g`, then `l₀ ++ pre = lg`, or two inputs of the two folds' chains collide.
`forked_not_on_fold`: a `forked` walk shows that follow's log up to the anchor is not the other fold's log.

### 6.3 Comparison paths

| path | who states the head | where follow compares | refusal |
|---|---|---|---|
| `sync --to STEPS:CHAIN` | the argv | each page walked from follow's position (A-Forked) | `forkedWorld STEPS`, page not kept |
| `sync --check ATTEST` | another member's attestation, carried outside the writer | each page walked; at the tip, the signer's current key | `forkedWorld STEPS`; `Head.Refusal` names |
| `sync --post OBJ` | a member's post of its own head into a `Std.head` object of this World, carried by the writer | each page that carries the post: walked (`forkedSelfPost`), or at or behind follow's position against follow's Store (`forkedBehindPost`) | `forkedPost`, page kept |
| the writer's certificate on each `log` page | the writer's certify key | walked (`forkedCertified`), or at or behind follow's position against follow's Store (`behindCertified`) | `forkedCertified`, page kept |

`sync --to` and `sync --check` compare only a position ahead of follow when the command begins; a position already passed is refused `ahead`, and `host check STORE --anchor STEPS:CHAIN` compares it on the member's own Store (`Host/Cli.lean`).
A post at a step count past the page's end is compared by nobody (`Spec/README.md`, premise of A2′).
A step count below the oldest file follow's Store keeps is not compared (§3.17).
A thin member cannot compare below its adopted base.
The writer can withhold posts indefinitely, and silence proves nothing (`docs/TRUST.md`).
A `Std.head` object records two disagreeing posts at one step count as `forked`, and is then frozen (`Lang/StdHead.lean`).

### 6.4 The claims

`Spec/Proofs/Fork.lean` states two claims over one frame of follow.
Both are named `ForkConsistent` on `main`; PROTOCOL-82 decision 6 renames the claim for what it states, and the rename is in flight.

```
ForkConsistent(S) ≜
  ∀ me F F' k res t r,  S.follow(me, F, k, res) = (F', steps t, r) →
  ∀ g wg l₀ lg m,
    S.fold(g, l₀) = ok F.W  →  S.fold(g, lg) = ok wg  →
    (wg.steps, bytes wg.chain, m) ∈ Head.selfPosts(F'.W, t)  →
    F.W.steps < wg.steps  →  wg.steps ≤ F'.W.steps  →
      ( l₀ ++ take(wg.steps − F.W.steps, t) = lg
        ∨ CollidesAmong(foldPres(g, l₀ ++ take(wg.steps − F.W.steps, t)) ++ foldPres(g, lg)) )
    ∨ ( ∃ (s, c, m') ∈ Head.selfPosts(F'.W, t), a prefix of t folds F.W to v with v.steps = s, bytes v.chain ≠ c,
        and r = refused (forkedPost s m') )
```

A frame that absorbs a page carrying another fold's self-head post, at a step count the page walks, either holds that fold's log up to there, up to a collision among a listed set, or ends `refused forkedPost` with a post its own fold passed with another chain.
Top theorem: `top_forkConsistent`.
Floor: `floor_forkConsistent`, the follower that replaces `forkedPost` by its ordinary reply (`postBlind`).

Its premises, exactly:
* follow's World and the poster's World are folds from one start `g`;
* the post is one `Head.selfPosts` reads off the page: a `Std.head` object of this World touched by a step of the page;
* `F.W.steps < wg.steps`: a post at or behind follow's position is compared by the follow loop (`behindOr`), which is not a field of `System`;
* `wg.steps ≤ F'.W.steps`: a post past the page's end is compared by nobody.

```
ForkConsistent.sync(S) ≜
  ∀ me F F' k res t r st s c,
    State.ofBytes(k) = st  →  parse(st.argv) = ok (sync (to s c))  →
    S.follow(me, F, k, res) = (F', steps t, r)  →
  ∀ g wg l₀ lg,
    S.fold(g, l₀) = ok F.W  →  S.fold(g, lg) = ok wg  →  wg.steps = s  →  bytes wg.chain = c  →
    F.W.steps < s  →  s ≤ F'.W.steps  →
      l₀ ++ take(s − F.W.steps, t) = lg  ∨  CollidesAmong(foldPres(g, l₀ ++ take(s − F.W.steps, t)) ++ foldPres(g, lg))
```

A `sync --to STEPS:CHAIN` frame that moves follow's World from below the stated step count to it or past it holds the other fold's log up to there, up to a collision among the two folds' listed link inputs.
Top theorem: `top_forkConsistent_sync`.
Floor: `floor_forkConsistent_sync`, the follower that reads every `sync --to` as `sync` (`syncBlind`).
The claim covers `sync --to`; it does not cover `sync --check`, `forkedCertified` or `behindOr`.

## 7 Receipts

### 7.1 Local receipts

A receipt answers what happened to a call, against a head's height and roots (`Protocol/Receipt.lean`).

```
Answer  ::= committed h td | refused h code m | absent
Receipt ::= { txId, root, jroot, rroot, rowsroot : digest, answer : Answer,
              jpath : journal trie proof, rpath : refusals trie proof }
```

`build(W, x)` reads the journal and the refusals at transaction id `x` and proves both paths on `W`.

```
r.txId = x    rootsDigest(r.root, r.jroot, r.rroot, r.rowsroot) = roots    answerOf(H, x, nb, r) = ok a
──────────────────────────────────────────────────────────────  RC-Check    Receipt.check
Receipt.check(H, roots, x, nb, r) = ok a
```

`answerOf` requires, for `committed h td`, an inclusion of `(h, td)` at `x` in the journal; for `refused h code m`, an inclusion of the refusal at `x` and an exclusion of `x` from the journal; for `absent`, `journalForgets(H, nb)` false and exclusions from both.
The refusals are `otherTx`, `headMismatch`, `pathMismatch`, `forgotten`, and `badReceipt` for bytes that do not decode (`Receipt.Refusal`).
The check trusts nothing the receipt states.

The wire form (`Receipt.layout`):

```
[byte answer, u64 a, u64 b, bytes turn, bytes txId, bytes root, bytes jroot, bytes rroot, bytes rowsroot, bytes jpath, bytes rpath]
```

`answer` is 0 for committed (`a` = height, `turn` = turn digest), 1 for refused (`a` = height, `b` = code, `turn` = the charged member), 2 for absent.

`receipt CALL` prints three lines (`receiptText`):

```
receipt HEX
head STEPS HEIGHT ROOTS CHAIN
settle VERDICT
```

`HEX` is the receipt built on follow's World after catch-up; the head is that World's; `VERDICT` is `settleOf` (§3.10).
The attempt store reads the third line's first word (`settleSeen`).
`Protocol/Proofs/Receipt.lean` `check_build`: a built receipt checks against the World's own head.

### 7.2 Health receipts

A health receipt states three counters of a member against a head (`Protocol/Health.lean`).

| counter | key | bound |
|---|---|---|
| `ticks` | the member's meter in window `refusalWindow(height + 1)` (`ticksKey`) | `Kernel.Bounds.ticksPerWindow` |
| `refusals` | the member's recorded refusals in window `refusalWindow(height)` (`countKey`) | `Kernel.Bounds.refusalsPerWindow` = 16 |
| `total` | the World's recorded refusals in that window (`totalKey`) | `Kernel.Bounds.refusalsPerWindowMax` = 16384 |

`refusalWindow(H)` is `H / Kernel.Bounds.windowMax`.
The receipt carries the four roots and one path per counter: an inclusion of the count when it is positive, an exclusion of its key when it is zero.

```
r.member = m    rootsDigest(r.root, r.jroot, r.rroot, r.rowsroot) = h.roots
each counter's path verifies at the key computed from h.height and h.origin
──────────────────────────────────────────────────────────────  HC-Check    Health.check
Health.check(h, m, r) = ok r.answer
```

The windows come from the head, never from the receipt.
The refusals are `badHealth`, `otherMember`, `headMismatch`, `pathMismatch` (`Health.Refusal`).
`receipt --health [MEMBER]` prints `health HEX`, the `head` line, and `ticks N of B in window W`, `refusals N of B in window W`, `total N of B in window W` (`healthText`).
Nothing is signed and nothing is asked of the writer beyond the catch-up.
`Protocol/Proofs/Health.lean` `check_sound`: a health receipt that checks against a World's own head states that World's three counters, or a listed input collides.
No claim of `Spec` mentions health receipts.

### 7.3 Foreign receipts

A law of World B reads a receipt of World A against a head of A that B holds in a `Std.head` object (`Protocol/Foreign.lean` `check`; PROTOCOL-65).

```
headView(cell) = at world chain height rootsB steps    decode(rootsB) = roots
Receipt.ofBytes(rb) = r    Receipt.check(height, roots, r.txId, 0, r) = ok (committed h td)
──────────────────────────────────────────────────────────────  FR-Check    Foreign.check
Foreign.check(cell, rb) = ok ⟨h, bytes td, bytes r.txId⟩
```

The refusals are `notHead`, `forkedHead`, `badReceipt`, `notCommitted` for a `refused` or `absent` answer, and the names of `Receipt.check`.
The deployed Lang program reads receipts through this check (`Host/Deployed.lean` `X`; `Spec/Proofs/Foreign.lean` `deployed_program_reads`).

`Spec/Proofs/Foreign.lean` `HeadOf(S, cell, wA)`: the cell's `at` head's roots are `wA`'s roots digest.
`Foreign(S)`: for any log `l` that folds a genesis World of A to `wA`, a receipt the check shows against a cell with `HeadOf(S, cell, wA)` names a transaction admitted in `l`, at the height shown with the turn digest shown, or the hash collides among the receipt's root inputs, `wA`'s, and the journal path's inclusion inputs.
`HeadOf` is a premise.
It says the held head belongs to a fold of A; it does not say the head is A's latest.
Heads are posted by grantees and are not signed by A's writer, so nothing in the tree discharges `HeadOf` (`Spec/README.md`).

## 8 Theorems

Each claim below is a `Prop` over `System` (`Spec/System.lean`), the record of deployed entry points; `deployed d` fills it with the definitions the binaries run (`Spec/System.lean` `deployed`).
Each has a top theorem `top_* : Claim (deployed d)` and a floor `floor_*` that refutes it on a lazy system (`Spec/README.md`).

| § | claim | file | states, in one sentence | premises | top theorem |
|---|---|---|---|---|---|
| C(i) | `Consent.signs` | `Spec/Proofs/Sign.lean` | every call-domain message a follow step offers custody is the call `plan` produced on follow's World from the continuation's command, the member's own, admitted there | the continuation's argv is not authenticated | `top_consent_signs` |
| C(i) | `Consent.signShapes` | `Spec/Proofs/Sign.lean` | every message a follow step offers custody is a planned call, an own-World envelope, a join consent, an invitation, a head attestation or a cancel | as above; `start` not covered | `top_consent_signShapes` |
| C(ii) | `Consent.okCommitted` | `Spec/Proofs/Claims.lean` | a step that ends a command `done ok` at phase 4 leaves follow at a World that journals the call the continuation carries | the tie of that call to the argv is owed | `top_consent_okCommitted` |
| C(ii) | `Consent.cancelOk` | `Spec/Proofs/Claims.lean` | a `cancel CALL` step that ends `done ok` leaves follow at a World that settles the call `refused cancelled`, holds no journal entry for it and holds its cancel record | | `top_consent_cancelOk` |
| C(iii) | `Consent.final` | `Spec/Proofs/Claims.lean` | a settlement `expired`, or `refused` other than `stale`, is never contradicted: no extension's `submit` admits the call | `RefusalsCanon`, `JournalCanon` | `top_consent_final` |
| C(iii) | `Consent.staleFinal` | `Spec/Proofs/Claims.lean` | a call follow planned on a World of its fold and settles `refused stale` is admitted on no extension, up to a collision among its pin inputs (`behindPres`) | `CellsFit`, `RowsCanon`, `RowsOk` at the planning World; `RefusalsCanon`, `JournalCanon` | `top_consent_staleFinal` |
| A1 | `OneHistory.member` | `Spec/Proofs/Claims.lean`, `Spec/Proofs/Member.lean` | per frame, follow's World is an audited extension of the one it held, or an adoption, only from a step-0 World, of a base the trusted sponsor pinned for the member's own World with its certificate checked; along a run from the member's own start every World is `Kept` | `keyFaithful` | `top_oneHistory_member` |
| A1′ | `Agree.pageAbsorbs` | `Spec/Proofs/Agree.lean` | the writer's page of what one batch staged, handed to follow at its log phase, moves follow to the World the writer keeps | call bytes round-trip; `RowsCanon`; the batch fits one page; the page is at the tip; not `init`, no anchor | `top_agree_pageAbsorbs` |
| A2 | `OneHistory.pair` | `Spec/Proofs/Claims.lean` | two folds from one World that agree on step count and chain are one World, up to a collision among their link inputs | | `top_oneHistory_pair` |
| A2′ | `ForkConsistent` | `Spec/Proofs/Fork.lean` | §6.4 | the post's step inside the walk; folds from one start | `top_forkConsistent` |
| A2′ | `ForkConsistent.sync` | `Spec/Proofs/Fork.lean` | §6.4 | the anchor inside the walk; folds from one start | `top_forkConsistent_sync` |
| §7 | `ReceiptTruth` | `Spec/Proofs/Receipt.lean` | a receipt the check answers against a genesis-folded World's own head is its journal entry, its recorded refusal, or the absence of both, up to a collision among the receipt's listed inputs | | `top_receiptTruth` |
| §9 | `Foreign` | `Spec/Proofs/Foreign.lean` | §7.3 | `HeadOf` | `top_foreign` |
| D2 | `Durable.follower` | `Spec/Proofs/Durable2.lean` | every step of follow that persists steps persists a rooted run of the system's kernel from follow's World to its next | | `top_durable_follower` |
| G2 | `Shown.onlyFollowers` | `Spec/Proofs/Claims.lean` | the writer defers a frame to the page builder only past `Envelope.check`: a live follow grant chain, the member's current key, a verifying signature | covers the `defer` arm only | `top_shown` |

The premises, as `Spec/README.md` names them:

* `keyFaithful(S, trusted, k)` (`Spec/Proofs/Claims.lean`): every continuation that parses as `adopt INVITE KEY` names `trusted`.
  Under an arbitrary relay A1 is false: a forged continuation makes a fresh member adopt any base the forger pinned.
  Keeping the command's state inside follow removes it (in flight: TOPLEVEL-SPEC §11.2).
* `HeadOf` (§9): the held head's roots are those of a fold of A from A's genesis.
  Writer-signed step-indexed heads would remove it (in flight: TOPLEVEL-SPEC §9).
* The post's step inside the walk (A2′): `F.W.steps < wg.steps ≤ F'.W.steps`.
* The continuation's argv (C(i), C(ii)): the claims say "the continuation's command"; that it is the member's command is owed with `keyFaithful`.
* Canonical tries (`RefusalsCanon`, `JournalCanon`, `RowsCanon`, `CellsFit`): true of every World a Store opens to.

Component theorems the rules of this document cite:

| theorem | file | states |
|---|---|---|
| `Envelope.check_ok_iff` | `Protocol/Proofs/Envelope.lean` | E-Ok as an equivalence |
| `Envelope.check_ok_within` | `Protocol/Proofs/Envelope.lean` | a passing envelope reads only inside one window of heights |
| `Envelope.check_expired_authenticated` | `Protocol/Proofs/Envelope.lean` | `expired` states the height only to an authenticated live follower |
| `final_iff_recorded` | `Protocol/Proofs/Settle.lean` | a submit reply is `refused` exactly when the refusal is or was recorded, or the window passed |
| `next_final` | `Protocol/Proofs/Attempt.lean` | an attempt ends `committed` or `refused` only on follow's `confirm` or `probe` |
| `settle_final_never_admits` | `Protocol/Proofs/Settle.lean` | a settlement `refused` (record arm) or `expired` is admitted on no extension |
| `staleBehind_final` | `Protocol/Proofs/Behind.lean` | the stale arm's finality |
| `step_persists_admitted` | `Protocol/Proofs/Command.lean` | what a step persists is a rooted fold of follow's own `World.step` |
| `sendCancel_host` | `Protocol/Proofs/Command.lean` | follow relays a cancel only when its own World records it |
| `anchor_binds`, `forked_not_on_fold` | `Protocol/Proofs/Head.lean` | §6.2 |
| `certified_ok`, `certified_intersect`, `certified_equivocation`, `certifiesWorld_ok` | `Protocol/Proofs/Head.lean` | §5.3 |
| `stranger_ok` | `Protocol/Proofs/Certified.lean` | §5.3 |
| `accept_done` | `Protocol/Proofs/Thin.lean` | an accepted base's World bytes hash to the pin's digest and its step count is the pin's |
| `check_build` | `Protocol/Proofs/Receipt.lean`, `Protocol/Proofs/Health.lean` | a built receipt checks against its World's head |
| `check_sound` | `Protocol/Proofs/Health.lean` | §7.2 |
| `foreign_receipt_sound` | `Protocol/Proofs/Foreign.lean` | the lemma under `top_foreign` |
| `resume_frame_fits` | `Protocol/Proofs/FrameFit.lean` | a page and its continuation fit one frame |
| `fold_head_binds` | `Kernel/Proofs/Fold.lean` | one `(steps, chain)` from one start is one log, up to a collision |
