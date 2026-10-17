# decisions/codec.md — BUILD-CODEC

## CODEC-0 · The row attacked: CODEC is a library below KERNEL, plus one module above it (2026-10-16)
**Decision.** `Codec/` has two parts. The core (`Codec.Refusal`, `Codec.Digest`, `Codec.Stream`, and
next `Codec.Hash`/`Codec.Tag`) imports nothing from the tree. The codecs of KERNEL's types (Turn, Cell,
World, the checkpoint delta) and the deployed `Kernel.Env` will live in one module, `Codec/Deployed.lean`,
which imports Kernel; nothing in Kernel imports it. The Rust emitter is NOT in Codec (`Emit/`, which
imports Protocol), so Codec never sits above Protocol.
**Alternatives.** (a) Fold Codec into Kernel (Turn's codec is Kernel data). (b) Keep the Turn/World codecs
in Kernel and have Codec export only combinators. (c) Put the emitter inside Codec.
**Why.** Kernel is generic over `Env` (hash + bytes), so its theorems state collisions as disjuncts and
the sim can run toy parameters. A Codec dependency inside Kernel would end that. (b) gives Kernel a
second job, wire formats, beside the transition. (c) creates a Codec → Protocol → Codec cycle the day
Protocol frames with Codec.
**Critique.** `Codec/Deployed.lean` is a module of CODEC that tracks every KERNEL shape change, so two
owners edit in lockstep. If KERNEL churns Turn, CODEC's file churns too.
**Meta-critique.** minidregg had a "codecs layer" too. I may be keeping the row because it existed. The
honest test is that the combinators and their proofs are 860 lines no other layer needs to read, and
the coupling to Kernel is one module.
Status: open.

## CODEC-1 · One codec structure; its laws are a separate Prop (2026-10-16)
**Decision.** `Stream α = {shape, put : α → ByteArray → ByteArray, get : ByteArray → Nat → Except
Refusal (α × Nat)}` (def module). `Lawful c : Prop = put_eq ∧ get_of_occurs ∧ occurs_of_get` lives in
`Codec/Proofs/Stream.lean`, with one theorem per combinator (`product_lawful ha hc : Lawful (product a c)`).
**Alternatives.** Bundle the laws as fields (minidregg's `StreamCodec.decodePrefix_encode`, and
codec-shapes' `encode_decodePrefix` field). Or keep two structures (minidregg's `LawfulCodec` beside
`StreamCodec`: twin C3).
**Why.** Law 8 (defs and proofs split): a proof edit rebuilds nothing downstream of the defs. Bundled
fields put a proof in every codec definition, and every combinator's def-module would import the proof
machinery.
**Critique.** A codec can now exist without a proof. Whoever needs canonicity (the tag registry, the
Store, the follower) must demand `Lawful c` as an argument. If nothing demands it, an unproved codec
ships. Mitigation: `Codec.Tag` only registers a codec together with its `Lawful` proof, so every
persisted or framed codec is proved.
**Meta-critique.** I chose the unbundled form partly because it made the proofs easy to write one combinator
at a time. That is the author's convenience, not the reader's.
Status: open.

## CODEC-2 · Canonicity is stated as "the consumed bytes ARE the encoding" (2026-10-16)
**Decision.** `occurs_of_get : get b i = ok (v, j) → j = i + |bytes v| ∧ b.extract i j = bytes v`
(OccursAt), plus `get_of_occurs` (wherever `bytes v` occurs, get reads v). Whole-input:
`decode_eq_ok_iff : decode b = ok v ↔ b = bytes v`.
**Alternatives.** Round trip only (`decode ∘ encode = id`): minidregg's law, which admitted 22
non-canonical decoders (CODEC-SHAPES). Or `encode_decodePrefix : decodePrefix bytes = some (v, s) →
encode v ++ s = bytes` (codec-shapes, over List).
**Why.** The occurrence form composes by offset (product/array just add offsets), never copies, and
needs no List. Together with `decode_eq_ok_iff` it means no caller ever re-encodes to check.
**Critique.** It says nothing about refusals: a decoder that refuses valid bytes for the wrong reason
(truncated where it should say pastBound) is still Lawful. The refusal NAME is unproved.
**Meta-critique.** I proved what was cheap to state over ByteArray's extract lemmas. A refusal-kind
theorem is the next obligation if a row depends on which refusal is reported.
Status: open.

## CODEC-3 · Bounds live in the value types (2026-10-16)
**Decision.** `Bytes max := {b // b.size ≤ max}`, `Bounded max α := {a : Array α // a.size ≤ max}`, with
`max < 2^32` an argument of `bytesOf`/`array`. A length or count past `max` is refused (`pastBound`)
before anything is read or allocated.
**Alternatives.** Plain ByteArray/Array, with the bound checked at decode only. Then `put` of an
oversized value writes bytes that `get` refuses, and the round-trip law is false for some values.
**Why.** The law holds for every value of the type. A value past its bound cannot be built, so it cannot
be written (TigerStyle: the bound is static and enforced at the boundary).
**Critique.** Every producer must construct the subtype with a proof, which pushes size reasoning into
KERNEL and HOST call sites. Some will reach for `⟨b, by sorry⟩`-shaped shortcuts, or for
`if h : … then … else panic`.
**Meta-critique.** Types-carry-bounds is my preference from the TigerStyle law. Whether the friction pays
for itself is measured by how many call sites need a runtime check anyway.
Status: open.

## CODEC-4 · Integers are fixed width, little-endian; no variable-length naturals (2026-10-16)
**Decision.** `u8`, `u32`, `u64`, all little-endian. No base-255 or varint naturals.
**Alternatives.** Big-endian (sorts lexicographically = numerically). Or LEB128 varints (compact).
**Why.** The client (`u32le` frames), Host/Log and Kernel/World were already LE. LE is native on every
target, so a future zero-copy read is a load. Fixed width has exactly one spelling per value, so there
is no minimal-encoding rule to prove. Varints are where minidregg's non-canonical decoders lived.
**Critique.** Byte order no longer equals numeric order, so a byte-sorted index of integer keys would need
BE. Today nothing sorts integers by bytes (digests are compared as bytes, and they are not integers).
**Meta-critique.** I first wrote BE out of habit and switched once I saw three layers already on LE.
Following the majority is not a reason. The real reason is "nothing sorts by integer bytes".
Status: open.

## CODEC-5 · Every codec carries its Shape; tags are content-addressed from it (2026-10-16)
**Decision.** `Stream.shape : Shape` (unit | u8 | u32 | u64 | digest | bytes max | option | product | sum |
array max | refine name | framed tag). Next commit: `Tag.of label c := H(tag-domain, label ‖ bytes(shape))`,
and `framed (Tag.of …) c`. A structural change to a codec moves its tag and every parent's tag, and
`StoreEpoch = H(sorted tags of persisted codecs)` moves with them. No hand-written tag literal, no
census, no fingerprint pins, no `/vN` chains.
**Alternatives.** minidregg's 637 registered literals + census + 635 fingerprint pins
(DELETE-CODEC-20261016). Or hand-versioned labels.
**Why.** The census and the pins exist only because tags were typed by hand. Computing the tag from the
shape removes the whole mechanism.
**Critique.** `refine` hides a function. Changing what a refinement accepts without changing its `name`
does not move the tag, which is a silent reinterpretation, the exact sin. The name is the one
hand-maintained piece. Option: require refinements to be drawn from a closed enumeration
(bool, enum-of-n) whose shape is structural.
**Meta-critique.** Content addressing is fashionable here (KERNEL-3 too). The test is whether two lanes
changing two codecs ever touch one shared line. They don't.
Status: open.

## CODEC-6 · Hash and MAC: Keccak in Lean (SHA3-256 / cSHAKE256 / KMAC256), domain by customization (2026-10-16)
**Decision (next commit).** `Codec.Hash`: Keccak-f[1600] over `UInt64` lanes; `cshake256 (domain : String)
(msg : ByteArray) : Digest`; `kmac256 (key : Digest) (domain : String) (msg) : Digest` for HOST's log seal.
Vectors from NIST SP 800-185 / FIPS 202 as named theorems (`by native_decide` + the census, where the
kernel cannot evaluate a permutation).
**Alternatives.** BLAKE3 (3–5× faster, keyed mode built in). SHA-256 + HMAC. An FFI to a C library
(EverCrypt).
**Why.** One primitive family gives both the hash and the MAC. It is what minidregg deployed, so its
spec is known. FFI would put unverified C in the TCB, and the charter forbids Rust/C deciding digests.
**Critique.** A Lean Keccak is slow (minidregg measured ~17 k instr/permutation before scalar
replacement, HP-7). If the hot path hashes every leg, this is the floor of THE BAR. BLAKE3 would be the
right choice if speed dominates and nobody needs SP 800-185 compatibility. Nobody does.
**Meta-critique.** Familiarity with minidregg's cSHAKE. The deciding measurement (permutations per
write × instr/permutation against the 5 s bar) is not taken yet.
**Measured (2026-10-16, Codec/Hash.lean, Apple M-series laptop, compiled `lake` exe, one core).** A first
version with a `Vector UInt64 25` state ran at 0.6 MB/s (every lane boxed, ~200 µs per permutation).
The landed version keeps 25 unboxed `UInt64` fields in a structure, with one round unrolled (generated from
the FIPS 202 ρ/π tables): **184 MB/s on a 1 MiB message (5.7 ms/MiB), 2.2 µs for a 200-byte digest**
(≈ 0.7 µs per permutation). At THE BAR (1000 records of ~4 KB) that is ~4 MB, about 22 ms of hashing,
against the 5 s budget. The base MAC of a 0.7 MB World is ~4 ms, about one fsync. The NIST
vectors (SHA3-256 "" and "abc", cSHAKE256 Sample #4, KMAC256 Sample #4) are theorems closed by
`decide +kernel` (7.6 s for all four), with no native_decide.
Status: open. The speed critique is answered for THE BAR. BLAKE3 stays the alternative if a profile
ever shows hashing on top.

## CODEC-7 · Ask of KERNEL: domains are a hash argument, not a byte prefix (2026-10-16)
**Decision (proposed).** `Env.hash : (domain : String) → ByteArray → D`, deployed as cSHAKE256's
customization string. This replaces `E.hash (tagTurn ++ bytes)`.
**Why.** `tag ++ bytes` separates domains only if no tag is a prefix of another tag followed by
attacker-chosen bytes. That holds today by inspection, not by construction. cSHAKE's customization is
encoded with its length, so it separates by construction.
**Critique.** It changes KERNEL's Env and every theorem that mentions `E.hash`. KERNEL may prefer to keep
the prefix and prove the tags prefix-free (a decidable fact about a closed list).
**Meta-critique.** Prefix-freeness is a decidable property of seven literals. A theorem would be cheaper
than an interface change. I prefer the interface because it cannot regress.
Status: open (KERNEL to answer in decisions/kernel.md).

## CODEC-8 · The follow payloads are layouts as data; every field is self-delimiting (2026-10-16)
**Decision.** The step frames (`Step.layout`), `commandLayout` and `resumeLayout` are `Codec.Layout`
data in Protocol/Table.lean. Field kinds are `byte | bytes | list`, every byte-string is `u32le len ‖
bytes`, and the bound is the frame's. `Codec.Layout.codec` turns a layout into the one Stream, and
`Stream.tagged` reads the step tag and then that step's layout. `Emit.Rust` prints `generated::layout::
{Command, Resume, Step}` with `decode`/`encode` that follow the Lean codec byte for byte (same
order, bounds, refusals and offsets). **Wire change accepted by ROOT:** the continuation `k` (in
sign/host/submit) and `resume.result` are length-prefixed fields, no longer "the rest of the
payload". CLIENT's successor deletes client/src/wire.rs (CLIENT-10) and uses `generated::layout`.
`resume.result` is the signature for `sign`, or the Host reply `u8 status ‖ payload` for host/submit,
opaque to the codec.
**Alternatives.** Keep `k…` as the rest of the payload (CLIENT-10's layout). Or a per-step hand
codec in Protocol.
**Why.** A field that is "the rest" is not a prefix codec. Its bytes depend on what follows it, so
`get_of_occurs` cannot hold and the layout could not be proved canonical. With every field
self-delimiting, `Step.frame_lawful` follows from the combinator theorems with no new proof.
**Critique.** 4 extra bytes per k/result. Field types are untyped bytes: `op` is a raw byte, not
`Op`, and `result`'s inner structure is not in the layout. A follow that sends an unknown op inside
a `host` step is caught by the Host, not by this codec.
**Meta-critique.** I made the layout as simple as the client's existing reader. A typed layout
(op ∈ Op) would let the codec refuse more, and I deferred it because nothing yet depends on it.
Status: open.

## CODEC-9 · The one recursive codec is a depth-bounded tree; LANG refines it (answers LANG-14) (2026-10-16)
**Decision.** `Codec/Tree.lean`: `Tree = node (tag : UInt8) (payload : ByteArray) (children : List Tree)`,
on the wire as `u8 tag ‖ u32le |payload| ‖ payload ‖ u32le |children| ‖ child*`.
`Stream.tree max depth : Stream (Tree.Fitting max depth)` (`{t // t.fits max depth = true}`, a Bool test, so the def-module exports no Prop). A reader nests at most `depth` levels and
refuses deeper input as `tooDeep` before reading it. Payloads and child lists of more than `max`
are refused as `pastBound`. The decoder returns its `fits` proof as it reads, so there is no second
pass. `tree_lawful` (Codec/Proofs/Tree.lean) is canonicity for every tree.
A recursive type (LANG's `Term`, `Ty`, `Data`) becomes a codec as
`Stream.refine "lang/term" (Stream.tree max depth) ofTree toTree`, where `toTree : Term → Tree.Fitting max depth`
writes each constructor as a node: its tag, its scalar fields as a payload written with the ordinary
codecs, and its subterms as children. Its Lawful proof is `refine_lawful tree_lawful …` plus LANG's two
inverse lemmas (`ofTree (toTree x) = some x`, and `ofTree t = some x → toTree x = t`, by induction
on terms). No stream reasoning is needed.
**Alternatives.** A fixpoint combinator over `Stream → Stream` (approximations `step^n ⊥`, with
canonicity relativized to depth). Every combinator theorem would need a depth-relative twin. Or
LANG's own `Lang/Wire.lean` (LANG-14, a second codec shape).
**Why.** The recursion and its proofs live in one place, the size-checking happens once, and every
recursive type pays only an inverse proof.
**Critique.** The tree shape is untyped: the tag-to-constructor map and the payload layout live in
LANG's `toTree`, not in the `Shape`. So `Tag.of` sees only `refine "lang/term" (tree max depth)`, and a
change to the term encoding moves the tag only if LANG changes the refine name. This is CODEC-5's
weakness, in its largest instance. A per-node payload costs 4 length bytes even when empty.
**Meta-critique.** I picked the generic s-expression because it was the smallest thing I could prove once.
A typed fixpoint would carry more of the structure into the Shape. I have not measured whether the
simpler proof is worth the opaque tag.
Status: open (LANG to adopt; LANG/Wire.lean's readers become `ofTree`).

## CODEC-10 · Every codec knows its size; `oneOf` and `within` bounds; the argv total is Lean's (2026-10-16)
**Decision.** (1) `Stream` gains `size : α → Nat`, and `Lawful` gains `size_eq : c.size v = (c.bytes v).size`,
so a value's encoded length is computed structurally without encoding it. HOST asked for this for
`worldBytesMax`, and `within` needs it. (2) `Stream.oneOf codes : Stream {b // codes.contains b}` refuses
any byte outside `codes` as `badTag`. It is the layout field `.oneOf name [(case, code)]`, which emits a
Rust `enum` with `code`/`from_code` (PROTOCOL-9 finding 1: a `host` step's op must not be `submit`).
(3) `Stream.within limit c : Stream {v // c.size v ≤ limit}` is a total bound over separately bounded
fields, refused `pastBound offset limit got`. `Protocol.commandFrame` is `within argvBytesMax`, and the
emitted `Command::decode/encode` apply the same check at the same point, so the Rust side no longer
decides it (CLIENT-2).
**Alternatives.** Measure with `(c.bytes v).size`, which re-encodes to check (minidregg's sin, W8). Or
check the total only in the Rust client.
**Critique.** `size` is a second computation of the length that must agree with `put`. The law
proves it agrees, but every new combinator now owes one more proof. `within` checks after decoding the
fields, so an over-total argv is read (bounded by the frame) before it is refused.
**Meta-critique.** I added `size` because two asks needed it at once. A single user would have
justified a local helper instead of a field on the one structure.
Status: open.

## CODEC-11 · Ed25519 verification in pure Lean (RFC 8032, cofactored), measured; no C (2026-10-16)
**Decision.** `Codec/Ed25519.lean`: `Ed25519.verify (pk msg sig : ByteArray) : Bool`, RFC 8032 §5.1.7 with the
cofactored check `[8]([S]B − [k]A) = [8]R`. It refuses `S ≥ L`, a point encoding with `y ≥ p`, and a point that
does not decompress (x² has no root, or x = 0 with the sign bit set). Field elements are ten unboxed
`UInt64` limbs (radix 2^25.5). The 100-term product is generated, folded by 2^255 ≡ 19, and every
intermediate stays below 2^63 for limbs below 2^27. `[S]B − [k]A` is one Shamir pass of 253
doublings. `Codec/Sha512.lean` is FIPS 180-4. Proofs: RFC 8032 TEST 1 and TEST 2 verify, a tampered TEST 2
does not, and SHA-512("abc"), all by `decide +kernel`. The kernel runs the whole verification
(~1 min per vector).
**Measured (this Mac, compiled, one core).** A first version on `Nat` (GMP) ran 7.0 ms/verify, so 1000
verifies took 7 s: over THE BAR's 5 s write budget. The limb version runs **381 µs/verify: 1000 verifies
in 0.38 s**. HACL*/EverCrypt (ROOT's fallback) is therefore not needed.
**Alternatives.** HACL*'s verified Ed25519 as an extern_lib (~50 µs). libsodium (unverified C: excluded).
Or Nat arithmetic with windowing (still ~3 ms).
**Critique.** The limb arithmetic has no proof of correctness against the field. Its evidence is the
RFC vectors and agreement with a Nat reference during development. A carry bug that only some
operands trigger (limb overflow past 2^64) would not show on three vectors. The bound argument
(limbs < 2^27 ⇒ products < 2^63) was checked by exhaustive-bound arithmetic in a script, not in Lean.
HACL* would bring a machine-checked proof of exactly this code path. The verifier is not constant
time, which does not matter for verification (no secrets).
**Meta-critique.** "Pure Lean" was the default the charter wrote. I met the speed bar and stopped, and
I did not price proving `Fe.mul` correct, which is the obligation that would make this better than the
fallback rather than merely Lean.
Status: open (owed: `Fe.mul`/`carry` correctness theorems against `Nat` mod p).

## CODEC-12 · KERNEL's values are encoded by codecs lawful ON their bounds (2026-10-16)
**Decision.** KERNEL keeps plain `Nat`/`List`/`ByteArray` and checks bounds in `World.admit`
(`checkBounds`, KERNEL-14: counters < 2^64, kinds < 2^32). So `Codec/Kernel.lean` codecs are total
writers over the raw types (`nat64`, `nat32`, `rawBytes max`, `rawList max c`, Codec/Raw.lean), proved
`LawfulOn Fits` (Codec/Proofs/Raw.lean, Codec/Proofs/Kernel.lean): a value within its bounds reads back
from its bytes, and every value read is within its bounds and was spelled exactly one way.
`checkBounds_fits` makes every admitted Turn fit, so `turnBytes_injective` holds for admitted turns, and
`decodeCall_callBytes` / `eq_callBytes_of_decodeCall` give the Ctx its inverse and its canonicity.
Bounds on the wire are KERNEL's own (touchesMax, opsPerWriteMax, createsMax, …). Inside a call, every
list and byte string is bounded by `eventBytesMax` (a call is one event).
**Alternatives.** Bounded types in KERNEL (CODEC-3's preference). KERNEL-2 declined: its window
arithmetic stays in `Nat`, and the premise is checked where it enters. Or `Lawful` over subtypes with
`pmap`-heavy back maps, which costs the same proofs for every kernel value.
**Critique.** `put` of an out-of-bounds value silently truncates (a u32 count of a longer list). The
type does not stop anyone encoding an unchecked Turn, so a digest of an unchecked turn can collide
with another's. Every use is safe only after `checkBounds`. `Fits` restates KERNEL's bounds; if
KERNEL changes a bound without CODEC, `checkBounds_fits` stops building, which is loud, not silent.
**Meta-critique.** I took KERNEL's no-subtypes choice as given rather than arguing harder for
types. The truncation hazard above is the price, and a typed Turn would not have it.
Status: open.

## CODEC-14 · The World codec: canonical bytes, read back up to `Equiv` (HOST-14's base) (2026-10-16)
**Decision.** `Codec/World.lean`: `world dc : Stream (World D)` = `cells ‖ journal ‖ spent ‖ height ‖ chain ‖
allowance`, each map as its entries in ascending key order (`toList`), each read back only if
strictly ascending (`ascendingList`, refused `rejected … "kernel/ascending"` otherwise), and rebuilt by
`ofList`. `Codec/Proofs/World.lean`: `world_decode_bytes` (a fitting World decodes from its bytes to an
`Equiv` World), `eq_bytes_of_world_decode` (exact canonicity: decoded ⇒ the bytes are the encoding),
`world_bytes_equiv` (`Equiv` Worlds have equal bytes, so a base's digest is a function of contents).
`(world dc).size w` is the encoded length from the entries without encoding (HOST's `worldBytesMax`).
`batch max dc` is the segment's batch record, `(turns ≤ max) × chain`, with `batch_lawfulOn`.
**Alternatives.** A `Lawful` (=) law, which is impossible: `TreeMap =` depends on insertion order, and a
reopened World is never `=` the live one (KERNEL's `World.Equiv`). Or encode the trees' shapes, which
would make two equal Worlds byte-distinct: anti-canonical.
**Critique.** The decoder rebuilds three TreeMaps by `ofList` (O(n log n)). A bulk-load from sorted
input would be O(n), and HOST measures it at reopen. `worldMax = 2^32 − 1` entries per map is a wire
bound, not a policy bound. HOST's `worldBytesMax` is the real one.
**Meta-critique.** The sorted-list uniqueness lemma was proved here from Std's membership lemmas,
so a Std upgrade that renames them breaks this module, not KERNEL's.
Status: open.

## CODEC-15 · One deployed Env/Ctx; the digest order is the byte arrays' (2026-10-16)
**Decision.** `Codec/Deployed.lean`: `env : Env Digest` (hash = cSHAKE256 with the domain as customization,
bytes = the 32 bytes, turn/cell bytes = `Codec.Kernel`), `ctx program : Ctx Digest` (+ unsigned/call bytes,
`decodeCall`, `digestOf = Digest.ofBytes?`, `verify = Ed25519.verify`), and `world` (the checkpoint codec).
`Ord Digest` is `compare` on the byte arrays (lexicographic), so `Std.TransOrd`/`LawfulEqOrd` are the
array order's laws pulled back (Codec/Proofs/Digest.lean). The hand-written `compareFrom` is deleted.
`Codec/Proofs/Deployed.lean` proves the premises KERNEL's theorems take for this instance.
**Alternatives.** Keep a hand-written byte loop and prove its laws (more code, same order). Or order by
the big-endian `Nat` (forms a bignum per comparison).
**Critique.** `Array.compareLex` is generic code, possibly slower than a 32-byte unrolled compare on
the TreeMap hot path. That has not been measured.
**Meta-critique.** Reusing the library's lawful order was chosen because it made the proofs free.
Status: open.

## CODEC-13 · The tree's lengths and counts are canonical LEB128 varints (answers LANG-2's framing ask) (2026-10-16)
**Decision.** `Codec/Varint.lean`: `varint : Stream Nat`, base-128 little-endian with a continuation bit,
at most five bytes, values below 2^32. A decoder refuses an overlong spelling (a final 0 byte after a
continuation: `rejected … "varint/overlong"`), a sixth byte, and values ≥ 2^32. `varint_lawfulOn`
(Codec/Proofs/Varint.lean) gives one spelling per value. `Stream.tree`'s payload length and child count are
varints, and the tag stays one byte.
**Measured (the same package, LANG's `Journey.owned`, 217 nodes).** u32 framing: **2529 bytes**
(9 bytes of framing per node). Varint framing: **1227 bytes** (−51%, ~3 bytes per node), against
~1181 for LANG's former hand codec. The largest package one 64 KiB cell holds roughly doubles back.
**Flag day.** Every tree's bytes change (all of LANG's package/term/type encodings). Nothing is
persisted yet; LANG and HOST re-emit nothing; Lang builds unchanged against it.
**Alternatives.** u16 lengths (3 bytes framing below 64 KiB but a hard 65535 cap). Or a per-node
"small" flag byte. Varint is the standard, and it is canonical once overlong spellings are refused.
**Critique.** Varints are where minidregg's non-canonical decoders lived. Here the canonicity is a
theorem (overlong refused, shortest form only), but a varint reader is a loop with five arithmetic
shapes where u32 had one. LANG's "a data sum's arm i costs i+1 bytes" is LANG's nested-sum encoding,
not this framing: `Stream.tagged`/`choice` (one tag byte for n arms) is the fix on LANG's side.
**Meta-critique.** I resisted varints in CODEC-4 for the frame layer and still do there. The tree is
different because its nodes are tiny and numerous. I took the measurement as permission to make
the exception.
Status: open.

## CODEC-16 · Tags are content-addressed, with a proof that shapes never share bytes (2026-10-16)
**Decision.** `Codec/Tag.lean`: `Shape.put` writes a shape canonically. Each constructor is a byte, and every number
and length is an unbounded LEB128 varint, so there is no width cap. `Tag.of label c =
Hash.digest "nanodregg/codec/tag/v1" (Tag.message label c.shape)`. `Codec/Proofs/Tag.lean`:
`Shape.put_prefix` (prefix-free: shape bytes followed by anything determine the shape and the rest),
`Shape.put_injective`, `Tag.message_injective`, and `Tag.of_eq`: equal tags mean equal label and shape,
or a cSHAKE256 collision on two distinct messages. Use: a Store stamps each record kind with the
tag of the codec that wrote it, and an open under codecs with other tags refuses by name (CODEC-5).
**Alternatives.** Hand-written `/vN` labels plus a census (minidregg's 637 tags and 635 fingerprint pins).
Or a hash of the codec's source text, which moves on any reformat.
**Critique.** The shape cannot see inside `refine`'s functions, so a semantic change behind an
unchanged refine name keeps its tag. The kernel codecs name each refinement (`kernel/turn`,
`kernel/op`, …). Nothing checks that a name changes when its function does. No HOST file stamps a
tag yet; until one does, this is machinery without a consumer.
**Meta-critique.** I proved prefix-freeness before anyone consumes tags because it was the honest
precondition of "a tag collision is a hash collision". The consumer (HOST's Store header) is the
part that makes it matter, and it is HOST-3's.
Status: open (HOST to stamp `Tag.of` of `Deployed.world` and `batch` into base/segment headers).

### CODEC-14 addendum · World encode/decode measured (2026-10-16)
Measured on HOST-3's BAR-shaped World (each record: a 2-slot cell with a 128-byte value, plus a
journal entry), compiled, this Mac, best of 5, one process per size. 290 KB: encode 0.40 ms,
decode 3.1 ms. 29 MB: 102 ms / 687 ms. 87 MB: 263 ms / 1.57 s. That is 3 ns/B encode at both large
sizes, so linear: one `toList` and one `foldl` per map, a unique buffer, geometric growth. The superlinear
1.5 s at 87 MB that HOST-3 first saw is run-to-run variance in a long-lived process: a bare
`TreeMap.foldl` over the same 3e5-node map varied 8–55 ms there. It is not an algorithmic term. The
generic codec is ~8× a raw memcpy of the same bytes (32 ms at 87 MB), so a proven-equal specialized
writer is the lever if a seal ever binds. Decode (~20 ns/B, the `ofList` rebuild) is the cold-reopen
term.

## CODEC-17 · An Ed25519 signer beside the verifier, as test tooling (2026-10-16)
**Decision.** `Ed25519.publicKey seed` and `Ed25519.sign seed msg` (RFC 8032 §5.1.5–5.1.6) in Codec/Ed25519.lean,
with RFC 8032 TEST 1 (key and signature), TEST 2 (key and signature), and `verify (publicKey s) m (sign s m)`
on TEST 2 as kernel-checked theorems (Codec/Proofs/Ed25519Sign.lean). KERNEL's simulation signs with it.
Custody signs in Rust, and nothing deployed calls `sign`.
**Alternatives.** A copy inside Kernel.Sim. Or a fake verifier in the Sim (no real signatures).
**Critique.** A signer in a deployed library tempts a later layer to sign in Lean with a secret held by
the Host, which is a custody question (pause list). It is not constant time. Its checks cost ~13 min
of kernel reduction in one leaf proof module.
**Meta-critique.** I built it because the Sim needed real signatures and a twin in Kernel would be worse.
Status: open (custody ruling stays CLIENT's).

## CODEC-18 · The field arithmetic is proved, not sampled (CODEC-11's owed theorems; CODEC-2, 2026-10-17)
**Decision.** `Codec/Proofs/Field.lean`. `Fe.Carried` (limbs 0, 1, 2, 4, 6, 8 below 2^26; 3, 5, 7, 9 below
2^25) is the invariant every operation returns. For carried inputs: `mul_toNat`
(`(f.mul g).toNat = f.toNat * g.toNat % p`), `add_toNat`, `sub_toNat` (`(f + p − g) % p`), `sq_toNat`,
`ofNat_spec` (`x < 2^255 ⇒ toNat = x % p`, carried), `carry_toNat`/`carry_carried` (any limbs below
2^63), `eq_iff`; and each result is carried again. Then `Point.add/double/neg/mul2_carried`,
`pow_carried`, `B_carried`, `decodePoint_carried`: every element `verify` computes satisfies the premise,
so the theorems cover the whole computation, not chosen inputs. The schoolbook identity
`mul_identity` (product of the two limb sums = the folded sum + p · the folded-away part) is a ring
identity GENERATED from `Fe.mul`'s own source text (the generator asserts every coefficient against the
limb positions: 1 or 2 below the fold, 19 or 38 above) and closed by `grind`. The no-overflow facts
(each row below 267 · 2^52 < 2^61) are `omega` over the products as atoms, one row at a time.
Tooth: `mul_needs_carried` — limbs of 2^40 wrap 2^64 and the product is wrong, by `decide +kernel`, so
the premise is not decoration.
**Alternatives.** HACL*'s verified field (an extern C TCB). Keep the vectors-only evidence. Prove it
on a `Nat`-limb model and argue the `UInt64` code agrees (a twin).
**Why.** The theorems are about the deployed `UInt64` definitions, with no new definition in the def
module (adding a `Fe.raw` there would rebuild the 13-minute kernel-checked sign proofs for nothing).
**Critique.** This proves the FIELD, not the CURVE: that `Point.add` is the Edwards addition law, that
`mul2` computes `[a]P + [b]Q`, and that decompression is the RFC's square root are still evidenced by
the RFC vectors only. A wrong formula with correct field arithmetic passes every theorem here. The
group-law proof is the next obligation if Ed25519 verification is ever claimed as verified rather than
"verified arithmetic, tested formulas".
**Meta-critique.** I proved the part the brief named (Fe.mul/carry) and stopped at the boundary where
the proof stops being mechanical. The curve law is exactly the "hard part" a phase ordering avoids;
it is recorded here so it is not mistaken for done.
Status: open (owed: Edwards addition law and `mul2` correctness against a Nat-coordinate spec). NOT YET LANDED:
the arithmetic part checks; the `*_carried` section for points is being reworked onto `Point.ladder` (CODEC-20).

## CODEC-19 · The trie World codec: entries in trie order, rebuilt by `build`, refused unless canonical (CODEC-2, 2026-10-17; design, waits on KERNEL-23 part 2)
**Decision.** When `World.cells` (cells + nullifiers, KERNEL-23) is a `Trie.T`, the World codec writes
the trie's `toList` (left-to-right by key bits) and the decoder rebuilds with `build S S.depth 0 l`
(each node hashed once, O(n) hashes; no node hash is ever read from the wire), then refuses
`rejected … "kernel/trie-order"` unless `(build l).toList.map fst = l.map fst` and each leaf's keys are
distinct. Canonicity is then exact by construction (`bytes t = encode t.toList = encode l = b`); no
order on keys has to be proved consistent with the bit routing. Read-back is EXACT (=, not
`Equiv`) given KERNEL's history-independence lemma `build S S.depth 0 t.toList = t` for every reachable
trie; asked of KERNEL-4.
**Alternatives.** (a) Rebuild by insertion (`insertAll`): n·depth hashes, seconds at HOST's 3e5-entry
Worlds. (b) Check strict ascent under a byte comparator: needs a proof that the comparator matches
`Spec.bit`, a second statement of the order. (c) Encode the tree with its hashes: a second shape of the
same contents, and a decoder that trusts hashes.
**Why.** The check is generic in `Spec`, costs one key comparison per entry, and leaves no order to keep
in agreement with the routing.
**Critique.** `build` filters each level, O(n · depth) list work (depth ≈ log n for a sparse key set,
but up to `S.depth` for adversarially chosen keys sharing long prefixes: the base is written by the
Host itself, so its keys are hashes, but a malicious base would cost 256 filter passes per entry
before refusal). The equality check runs after the build, so a non-canonical base is fully built
before it is refused (bounded by the base's size bound).
**Meta-critique.** I picked the check that is cheapest to PROVE; its runtime cost is a second key
pass I have not measured against the decode itself.
Status: open (built at the KERNEL-23 flag day).

## CODEC-20 · The RFC 8032 checks are staged, so no proof module peaks above ~3 GB (CODEC-2, 2026-10-17; GATES-2's ask via ROOT)
**Decision.** `Point.mul2` is now `Point.ladder … Point.zero`, where `ladder P Q PQ R a b n` runs the Shamir ladder
from a given point `R`, and `Point.step` is one bit (a pure refactor: the same doublings and additions in the
same order). `Fe` and `Point` derive `DecidableEq`. `Codec/Proofs/Ed25519Stage.lean`: `ladder_add` (n + k bits =
the top n, then the low k, from that result), `mul2_of_chunks` (61 or 64 bits, then three chunks of 64),
`verify_eq` (what `verify` is once sizes, S and both decompressions are known), and `publicKey_eq` / `sign_eq`
(what they are once `expand` is known, proved symbolically). One module per vector,
`Codec/Proofs/Ed25519/{Test1, Test2, Tampered}.lean`: every theorem keeps its statement (test1, test2,
test2_tampered, publicKey_test1/2, sign_test1/2, verify_sign_test2), proved through literal intermediate points.
Each literal is checked, not trusted: a private `decide +kernel` lands the real definition exactly on it (one
chunk per declaration). The literals were printed by a scratch `#eval` that is not in the tree.
**Measured (hbox, `/usr/bin/time -v lake env lean`, maxrss / wall).** Before: Codec/Proofs/Ed25519.lean 9.15 GB /
5:22 (TEST 1 alone 8.55 GB / 1:46); Ed25519Sign ~11–14 GB (GATES-2's slot kills; not re-measured). After:
Test1 2.56 GB / 2:33, Test2 2.83 GB / 2:21, Tampered 2.36 GB / 0:55. A first staging that unfolded `sign` by
`simp only [sign, he]` on the CONCRETE seed timed out in the kernel at 16.4 GB: the unfolding has to be proved
once, symbolically (`sign_eq`), and then rewritten.
**Alternatives.** (a) Split modules only: measured useless (one declaration is the peak). (b) `native_decide`:
trusts the compiler for what the kernel can check (law 6 says only where the compiler must be trusted). (c) Drop
the sign vectors: they are the only check that `sign` is RFC 8032.
**Critique.** The literal points are ~1600 numerals of proof text that move whenever the ladder's order or the
limb representation changes; regenerating needs the scratch printer, which is not in the tree. A change to `Fe`'s
carry would make every literal wrong, and the proofs would go red (loud, never silently wrong).
**Meta-critique.** I chased the memory number GATES asked for. The deeper fix is the CURVE proofs (CODEC-18's
owed group law), after which a vector proves only the RFC's specific outputs, not the ladder's arithmetic.
Status: open.
