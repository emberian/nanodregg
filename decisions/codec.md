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
**As landed (10-17).** `Fe.Carried` and `Point.Carried` are STRUCTURES, not conjunctions: as a `def`, every
`exact` that compared `(P.add Q).X.Carried` with a field lemma unfolded the limbs of a symbolic product
(20 GB, heartbeat timeouts); as structures elaboration never looks inside, and the whole module checks in
20 s / 1.35 GB. Landed: carry/mul/add/sub/sq/ofNat/zero/one/eq_iff, the tooth, `pow_carried`,
`point_add/double/neg/zero_carried`, `step_carried`, `ladder_carried`, `mul2_carried`. NOT landed:
`B_carried` and `decodePoint_carried` (the latter's `split at h` over the unfolded decoder still reaches 21 GB);
until then the field theorems cover the ladder from carried inputs, and the base point and decompressed points
are carried by inspection, not by theorem.
**Addendum (10-17).** `B_carried` and `decodePoint_carried` landed. The decoder's 21 GB was zeta: its `let` chain
named `x` once, but `x` is built from `u`, `v`, `v3`, `v7`, and inlining the lets makes the proof term a TREE
of the DAG (each Fe expression duplicated wherever it is used), which the kernel then re-checks. The fix was
in the def module: `decodePoint` is now a composition of small functions (`candidateFrom`, `rootCheck`,
`sqrtRatio`, `recoverX`, `signed`), each taking computed values as ARGUMENTS, so sharing survives and each
lemma is about variables (the module checks in 18 s / 1.25 GB). The computation is unchanged.
Status: open (owed: the Edwards addition law and `mul2` correctness against a Nat-coordinate spec).

## CODEC-19 · The trie World codec: entries in trie order, rebuilt by `build`, refused unless canonical (CODEC-2, 2026-10-17; built at KERNEL-23 part 2, 7c43273)
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
**As built (7c43273, KERNEL-7's flag day; CODEC-3's follow-up).** The check as landed is stronger than the
design: `cells` refuses unless the rebuilt trie's listing EQUALS the decoded listing (keys and leaves,
`t.toList == l`) and no leaf holds a key twice (`leavesNodup`); before it, `fitList` refuses
`kernel/leaf-fit` unless every slot holds the leaf of its kind. Read-back is exact for the trie
(`build_toList`, CODEC-2's history independence). Teeth (`Codec/Proofs/WorldTooth.lean`, over
`Kernel.Sim`'s toy env, `decide +kernel`): the canonical two-slot listing decodes and lists back the same
entries; the same entries swapped are refused `kernel/trie-order`; a nullifier slot holding a cell entry
is refused `kernel/leaf-fit`. And `world_decode_cellsFit`: every live cell of a decoded World is in
`Cell.Fits`, so a reopened base carries the kernel's `World.CellsFit` from the codec (KERNEL-31 proves
admission keeps it). The critique stands: the build runs before the refusal, and its list work is
unmeasured.
Status: built.

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

## CODEC-21 · Sandbox paths, u32 fields and tagged frames in the one Layout family (HOSTING's ask; CODEC-2, 2026-10-17)
**Decision.** (1) `Codec/Path.lean`: `clean` (nonempty, ≤ `componentMax` = 64, not `.`/`..` (`reserved`), none
of the `forbidden` bytes 47/0), `join` (components joined by `/`), `split`, `fits max p`. All index the bytes
directly (no `List UInt8`, law 3) and are structural, so they reduce in the kernel: `decide` over literal paths
works, which HOSTING's proofs need. `Codec/Proofs/Path.lean`: `join_split` (every byte string is the join of
its split), `split_join` (clean components survive), `clean_free`, and the tooth `split_join_needs_clean`.
(2) `Field.u32`, `Field.path` (value: `{p : List ByteArray // Path.fits max p}`, wire: the joined bytes as a
`bytesOf`, refused `rejected … "path/badComponent"`), `Field.paths`; `pathCodec_lawful`, so every layout with
them stays lawful and canonical. (3) `Codec.Tagged := List (String × UInt8 × Layout)` with `Tagged.codec`,
`Tagged.codec_lawful` under the premise that codes are distinct, and the tooth that without it the first
case wins. (4) Emit: the Step enum is now one instance of `taggedEnum`; `taggedFile` prints a whole
generated file (bounds, cursor, the path rule from `Path`'s constants, one enum per tagged family). Rust
identifiers are snake_case. client/src/generated.rs is byte-identical.
**Alternatives.** A nested list of components on the wire (Rust would join, deciding the spelling). A path as
a raw string checked only in Rust (a second copy of the rule). HOSTING writing its own frame codec (a twin
of the layout family).
**Why.** The joined form is what the sandbox consumes, so Rust passes bytes through. The rule is defined
once in Lean, and the Rust copy is printed from Lean's constants.
**Critique.** The Rust `path_clean` is printed from constants, but its CONTROL FLOW (split, all, the four
tests) is hand-written in the emitter: a change to `clean`'s logic that keeps the constants would not move
it. There is no differential theorem between the two. `split` is O(n) extracts and allocates per component,
and is used only by the decoder.
**Meta-critique.** I matched the names HOSTING's handoff already expected, which steered the value type to a
component list (and so required `split` and its proofs) rather than the joined bytes, the simpler type.
The wiring of `--hosting` waits on HOSTING-2's `Hosting/Wire.lean`.
Status: open.

## CODEC-22 · The carried state's version is its tag, not a policy (OPS-P1; CODEC-2, 2026-10-17)
**Decision.** `Codec.Kernel.carried E dc : Stream (Carried D)` reuses `cells E dc` (the trie listing, with its
`kernel/leaf-fit` and `kernel/trie-order` refusals) for KERNEL-29's `Carried`, under refine
`kernel/carried/v1`. An export file stamps `Tag.of "kernel/carried" carried`; an import compares the stamp
before decoding and refuses `shapeMismatch` by name. The import's check is byte equality of carried bytes
(the codec is canonical).
**Alternatives.** OPS-P1's: a carried codec versioned by hand, changed only on an explicit carry flag day. Or
a second reader of the old carried shape (law 1 forbids it).
**Why.** The carried bytes embed the cell, entry, slot and leaf codecs, so a hand version can say "unchanged"
while the bytes changed. The content-addressed tag cannot. A World-codec change that leaves those codecs alone
keeps the tag (the carry crosses that flag day), and one that changes them refuses the carry loudly; that
flag day is a plain re-genesis.
**Critique.** The tag cannot see inside refine functions (CODEC-5): a semantic change to the trie-order check
that keeps the names would keep the stamp. Carry across a cell-spelling change is impossible by design, which
an operator may find surprising; the refusal must say so.
**Meta-critique.** I prefer the mechanism I already built (Tag.of) to a new rule, which is the familiar-tool
bias; the test is that it removes a promise someone would have to keep.
Status: accepted by OPS-2 (7f7b6da); built after KERNEL-29's Carried lands.
**Built (CODEC-5, 2026-10-18, on KERNEL-29 b8e0f82).** `Codec/World.lean`: `carriedWire E dc` = `cells E dc ‖
nat64 allowance ‖ nat64 height ‖ ascendingList Bounds.journalMax Prod.fst (dc ‖ nat64 ‖ dc)` (KERNEL-29's
`Carried` = {trie, allowance, height, journal}; the same order as KERNEL's `carryInput`), and `carried E dc`
under refine `kernel/carried/v1`. `Codec/Proofs/Carried.lean`: `carriedWire_lawfulOn`, `carriedWire_decode_iff`
(on the wire, `decode b = .ok x ↔ b = bytes x` exactly), `carried_decode_iff` (canonicity of the state: for a
fitting `c`, `b` decodes to a state `CarriedEquiv` to `c` ↔ `b = bytes c`), `eq_bytes_of_carried_decode`,
`carried_decode_bytes`, `carried_bytes_equiv` (so HOST's byte equality on import IS contents equality),
`carried_decode_canon` (the decoded trie is `Trie.Canon`, every slot holds its kind's leaf), `carried_fits`
(the carried state of a `World.CodecFits` World with `journal.size < Bounds.journalMax` — every reached World,
`Kernel.reach_journal_bounded` — is in the codec's domain). Teeth (Codec/Proofs/WorldTooth.lean, `decide +kernel`
over `Kernel.Sim`): `carried_reads_ascending_journal`, `carried_refuses_swapped_journal` and
`carried_refuses_repeated_txId` (both refused `kernel/ascending` by name); the trie's own plants are CODEC-19's.
**Critique (built).** Canonicity of the decoded STATE is up to `CarriedEquiv`, not `=`: the journal is a `TreeMap`
whose balancing is not its contents, so two maps with one listing can be unequal terms. Everything else (the
trie, both counters) is `=`, the wire is exact, and the bytes are a function of the contents
(`carried_bytes_equiv`), which is what the import's byte comparison needs. Making it `=` would need KERNEL to
carry the journal as a sorted list rather than a `TreeMap`.

### Review · LEDGER's `Stream.i64` (b2d60e7), CODEC-2 10-17
`i64 = refine "i64" u64 (some ∘ toInt64) toUInt64` and `i64_lawful` via `refine_lawful u64_lawful` with
both inverse laws: a bijection on 8 bytes, so canonicity is exact and nothing is refused. The shape is
`refine "i64" u64`, distinct from `u64`'s, so a field moving from u64 to i64 moves its tag. Accepted.

## CODEC-23 · The curve formulas are proved over the field: every point `verify` computes is on edwards25519, and add/double are the Edwards law (CODEC-18's owed curve half, part 1; CODEC-3, 2026-10-17)
**Decision.** `Codec/Proofs/Curve.lean`. The value map `⟦f⟧ := (f.toNat : Fin p)` (written out as the cast in the module: a proof module exports no notation) is a ring map on carried
elements (`val_mul`, `val_add`, `val_sub`, `val_sq`, `val_d2 : ⟦d2⟧ = 2⟦d⟧`), so every coordinate of `P.add Q`
and `P.double` is a polynomial in the inputs' values (`point_add_vals`, `point_double_vals`). `Point.OnCurve P`
(a structure Prop: carried, `X Y = Z T`, `Y² − X² = Z² + d T²` in `ℤ/p`, the extended twisted Edwards curve with
`a = −1`). In extended coordinates the curve is closed under the RFC's formulas with NO division and no
`Z ≠ 0` (checked first with a Gröbner reduction: the result's curve equation lies in the ideal of the inputs'
`ext` and `curve` equations; in the `Z`-only form `(Y² − X²) Z² = Z⁴ + d X² Y²` it does not, only after
multiplying by `(Z₁Z₂)²`, which would need `ℤ/p` to be a field). Proved: `point_add_onCurve`,
`point_double_onCurve`, `point_neg_onCurve`, `point_zero_onCurve`, `step/ladder/mul2_onCurve`, `B_onCurve`
(by kernel arithmetic on the RFC constants), `rootCheck_solves` (what `rootCheck` returns solves `v r² = u`,
using `⟦√−1⟧² = −1`), `signed_onCurve`, `decodePoint_onCurve`. And the laws: `point_add_law` —
`X₃ (Z₁²Z₂² + d X₁X₂Y₁Y₂) = Z₃ (X₁Y₂ + X₂Y₁) Z₁Z₂` and `Y₃ (Z₁²Z₂² − d X₁X₂Y₁Y₂) = Z₃ (Y₁Y₂ + X₁X₂) Z₁Z₂`, i.e.
`x₃ = (x₁y₂ + x₂y₁)/(1 + d x₁x₂y₁y₂)`, `y₃ = (y₁y₂ + x₁x₂)/(1 − d x₁x₂y₁y₂)` — and `point_double_law` (the same
with `P = Q`). Each ring identity is proved once over any `Lean.Grind.CommRing` by `grind` and instantiated at
`Fin p`. Tooth: `add_law_needs_ext` — `(4, 5, 3, 0)` satisfies the curve half but not `X Y = Z T`, and the
addition law's `x` equation is false for it (`decide +kernel`, no axioms), so `ext` is a load-bearing premise.
Cost: the module checks in ~2 s / 0.77 GB (a leaf; nothing imports it).
**Alternatives.** (a) Prove `p` prime and work in a field, stating the laws affinely (`x₃ = …/…`). Needed for
the remaining half (below), not for this one: the cross-multiplied statements say the same where the
denominators are units, and need no primality. (b) Keep the RFC vectors as the only evidence for the formulas.
(c) A Nat-coordinate spec `def` beside the deployed one, compared by a differential theorem — a second
definition of the curve, refused (law 1); the spec here is the curve EQUATION, which is not a computation.
**Why.** CODEC-18 proved the field and named the curve as the gap: a wrong formula with correct field
arithmetic passed every theorem. Now a wrong addition, doubling or decompression formula fails `point_add_law`,
`point_double_law` or `decodePoint_onCurve`.
**Critique.** This is the curve LAW, not yet the GROUP: (1) completeness — that the denominators
`1 ± d x₁x₂y₁y₂` (the `F`, `G` of the RFC formula, so `Z₃`) are never zero — needs `p` prime and `d` a
non-square mod `p`; without it, `Z₃ = 0` would make both law equations hold trivially. (2) `mul2 P Q PQ a b n =
[a]P + [b]Q` needs associativity of the law on projective classes (a much larger polynomial certificate, with
`Z ≠ 0` cancellations, so again the field). (3) That `verify`'s final projective comparison of `[8]` multiples is
the RFC's cofactored check is then a corollary. Until (1)–(3), the honest claim is "verified field, verified
formulas (every point on the curve, each step the Edwards law), ladder by vectors".
**Meta-critique.** The cross-multiplied form is exactly where a vacuous statement could hide (`Z₃ = 0` satisfies
it), and I stopped there because the next step needs a primality certificate for 2^255 − 19 in Lean core with
no Mathlib. That is a cost estimate, not a constraint: it is CODEC-23 part 2, the next codec obligation after
the owed flag-day work, and it is recorded here so this half is not read as the group law.
**Part 2 (CODEC-3, 2026-10-17): completeness.** `Codec/Prime.lean` (def): `powMod`, structural square-and-multiply.
`Codec/Proofs/Prime.lean`: `IsPrime`, `powMod_spec`, and `pratt` — if `qs` are primes with product `n − 1`,
`a^(n−1) ≡ 1` and `a^((n−1)/q) ≢ 1` for each `q`, then `n` is prime — proved in core Lean with no library
(the order of `a` is exactly `n − 1`; its powers are `n − 1` distinct nonzero residues, hence all of them
by a counting lemma `card_lt`; so a proper divisor of `n` is a unit, and a unit dividing `n` is 1); with
`pratt_fermat`. `p_prime` / `p_fermat`: `2^255 − 19` by a 52-node certificate tree generated offline
(sympy `factorint`/`primitive_root`) and checked node by node by `decide +kernel` (4 s, 1.2 GB).
Tooth `fermat_alone_is_not_prime`: 341 passes `2^340 ≡ 1` and fails the order condition.
`Codec/Proofs/Complete.lean`: `fin_inv` (`Fin p` is a field, inverse `x^(p−2)`), `d_nonsquare` (Euler:
`powMod d ((p−1)/2) p = p − 1`, and a square would give 1 by Fermat), `sqrtM1_sq`; `complete_affineR`
(Bernstein–Lange: with `−1 = i²` and `d` a non-square, `(d x₁x₂y₁y₂)² ≠ 1` on the curve), its projective
forms `add_properR` / `double_properR`, and `Point.Proper` (on the curve, `Z ≠ 0`) kept by
add/double/neg/zero/step/ladder/mul2, with `B_proper` and `decodePoint_proper`. So the cross-multiplied
laws of part 1 are the affine Edwards law at every point `verify` computes. Tooth
`onCurve_admits_degenerate`: `(0,0,0,0)` satisfies the curve equations and its sum has `Z = 0`, so the
`Z ≠ 0` of `Proper` is what makes the laws non-vacuous. Lesson (kernel): a defeq goal `(P.neg.Z …) = (P.Z …)`
left to `exact` makes the kernel try structure eta on `Point.neg P =?= P`, which unfolds the limb
arithmetic (20 GB, deep recursion); reduce the projection first (`unfold; dsimp only`).
**Critique of part 2.** Still not the GROUP: `mul2 P Q PQ a b n = [a]P + [b]Q` needs associativity of
the law on projective classes (and that `PQ = P.add Q` is what `verify` passes), and `verify`'s final
check is then the RFC's cofactored equation. The primality proof trusts `decide +kernel` (the kernel's
GMP-accelerated `Nat` arithmetic), as every literal check here does.
**Part 3 (CODEC-4, 2026-10-17): the group, the ladder, the RFC equation.** `Codec/Proofs/Group.lean`:
`Point.Affine P x y` (proper, `X = x Z`, `Y = y Z`): every proper point names exactly one affine point
(`affine_exists`, `affine_unique`), on the affine curve (`affine_curve`), and `add`/`double` name the affine
Edwards sum (`add_affine`, `double_affine`; denominators units by `affine_dens` from completeness).
`Point.Same P Q` (both proper, `P.eq Q = true` — the deployed check) is an equivalence, a congruence for
`add`, and on it `add` is commutative, associative (`same_add_assoc`), has identity `Point.zero`, inverse
`neg` (`same_neg_add`), and `double P` is `P.add P`. Associativity is ONE ring identity with the
denominators cleared (`assoc_polyR`: 48 monomials of degree 18 after expansion; sympy reduces it to 0 by the
three curve equations with cofactors of 16/64/40 terms) which `grind` closes from the curve equations alone in
~1 s, so no certificate is stored; `assoc_affR` cancels the (unit) denominators. CODEC-3's failed attempt
kept 13 inverse variables as hypotheses; clearing them first is what makes it small.
`Codec/Proofs/Ladder.lean`: `[m] P := Nat.repeat (·.add P) m Point.zero` (no new definition: the spec is
the deployed `add`), `rep_add`, `rep_distrib`, `rep_congr`, `same_interchange`, `same_d3` (three doublings
are `[8]`); `ladder_spec` (the ladder from the identity is `[a mod 2^n] P + [b mod 2^n] Q`), `mul2_spec` (for
`a, b < 2^n` it is `[a] P + [b] Q`, given `PQ` projectively `P.add Q`); `rfc_iff` and `verify_iff`:
`verify pk msg sig = true` ↔ `pk` 32 bytes, `sig` 64, `S < L`, both points decode, and
`[8][S]B = [8]R + [8][k]A` (as `Point.Same`), `k = leNat (SHA-512(sig[0,32) ‖ pk ‖ msg)) 0 64 % L` — RFC 8032
§5.1.7's cofactored group equation. Teeth: `assoc_needs_curve` (off the curve the cleared identity is false,
`decide +kernel`, no axioms) and `mul2_needs_bound` (with `n = 0` the ladder returns the identity, which is
not `[1] B`, since `B`'s `x ≠ 0`). Axioms: propext, Classical.choice, Quot.sound. Cost: Group ~7 s / 1.1 GB,
Ladder ~1 s / 0.8 GB (leaves). Lesson: a goal `Nat.repeat (·.add P) (m+1) z = (… m …).add P` left to defeq
(`show`, `exact`, structural recursion over two different points) makes the unifier unfold `Point.add`
(heartbeat timeout); unfold `Nat.repeat` by its equations (`simp only [Nat.repeat]`) and use `induction`.
**Critique of part 3.** (1) The group is the curve's points up to projective equality; nothing here says `B`
has order `L`, so `[S]B` for `S ≥ L` and the reduction `k mod L` are the RFC's choices, not theorems about the
subgroup. (2) `verify_iff` states the equation over the DECODED points; that `decodePoint` is RFC 8032 §5.1.3
(the right square root, sign rule, the `y ≥ p` refusal) is proved only as far as Curve.lean goes (the point
is on the curve), not as an inverse of `encodePoint`. (3) The spec `[m] P` is `m` deployed additions, so it is
only as good as `add` — but `add` is pinned to the Edwards law by `add_affine`, so this is the law, not a twin.
(4) SHA-512 is trusted as computed by `Sha512.hash` (vectors only).
**Meta-critique.** I stopped at the RFC's equation and not at "accepts exactly the signatures `sign` makes",
because that needs (2) and the group order of `B`, a computation of `[L]B` through the ladder in the kernel
that sits on the CODEC-20 memory boundary; it is the next codec obligation, recorded here so `verify_iff` is
not read as signature correctness.
**Part 3b (CODEC-4): the order of B.** `Codec/Proofs/Ed25519/Order.lean`: `B_order : Point.Same ([L] B) 0`.
The deployed ladder over `L`'s 253 bits is run in four `decide +kernel` chunks through literal intermediate
points (`mul2_of_chunks`, the CODEC-20 shape: 1.6 GB, 55 s for the module), and `mul2_spec` turns that into
`[L] B`. Tooth `B_not_small`: `[8] B ≠ 0`, so the order is not the cofactor's. This closes critique (1) above
for `B` (`L` prime is RFC 8032's statement; its primality is not proved here). The intermediate literals were
printed by evaluating the deployed ladder (hbox logs/codec4-order.lean) and are checked, not trusted.
`L` prime: `Codec/Proofs/PrimeL.lean`, `Prime.L_prime : IsPrime Ed25519.L` (a 35-node Pratt tree over the
known factorization of `L − 1`, built by `pratt_check` as `p_prime` was; 0.9 GB, 5 s).
**Part 4 (CODEC-5, 2026-10-18): decode ∘ encode and signature correctness — CODEC-23 is COMPLETE.**
`Codec/Proofs/Ed25519/Bytes.lean`: `leNat_le32Bytes` (reading `le32Bytes n` back is `n mod 2^256`), `leNat_lt`
(32 bytes spell a number below `2^256`, so the sign bit is 0 or 1), `leNat_append_left/right`, `le32Bytes_size`.
`Codec/Proofs/Ed25519/Decode.lean`: `pow_toNat` / `pow_val` (`Fe.pow` is the power of the value; powers are taken
through `Nat`, never `Fin`'s unary `npow`), `inv_val` (`Fe.inv` inverts every unit, Fermat), `sqrtRatio_some` (if
`u = v x²`, `v ≠ 0`, the candidate `u v³ (u v⁷)^((p−5)/8) = x^((p+3)/4)` satisfies `v c² = ±u` by Euler's criterion,
`x^((p−1)/2) = ±1`, so `rootCheck` returns), `den_ne_zero` (`d y² + 1 ≠ 0` since `d` is a non-square and `−1` a
square), `recoverX_root` (what `recoverX` returns is `±x`), `signed_some`, and the two halves of the RFC 8032
§5.1.3 specification: `decodePoint_affine` — what decode returns names the affine `(x, y)` with `y = n mod 2^255
< p`, on the curve, `x` of the sign bit's parity — and `decodePoint_some` — for every such `(x, y)` decode returns a
point naming it. Together: decode accepts exactly the RFC's encodings and returns the RFC's point (the root of the
right parity; `x = 0` with sign 1 refused because no `x` of value 0 is odd; `y ≥ p` refused).
`Codec/Proofs/Ed25519/Sign.lean`: `encode_affine` (a proper point names the `(x, y)` `encodePoint` writes),
`decode_encode` (an honestly encoded proper point decodes to itself projectively, whatever bytes follow),
`baseMul_same` (`baseMul k = [k] B`), `rep_mul` (`[m n] P = [m][n] P`), `rep_mod_L` (`[m] B = [m mod L] B`, from
`B_order`), `rfc_holds`, and **`sign_verifies : verify (publicKey seed) msg (sign seed msg) = true`** for every
seed and message. Tooth: `decode_flipped_sign` — a point with `x ≠ 0` encoded with the sign bit flipped decodes
to its negation, which is not the point — and `B_sign_bit_needed`, that instance at `B` (`B_x_ne_zero` by kernel
arithmetic), so the sign rule is load-bearing and the premise is satisfiable.
What the Ed25519 chain now proves end to end, all kernel-checked: the field (`mul/add/sub/ofNat_toNat`, CODEC-18),
`p` prime (`p_prime`), `L` prime (`L_prime`), the curve (every point verify computes is on it, add/double are the
Edwards law, `Point.Proper` kept by every step; `d` non-square, completeness), the group law (associative,
commutative, identity, inverse, `same_add_assoc`), the ladder (`mul2_spec`: `[a]P + [b]Q`), `verify_iff`
(verify is the cofactored RFC equation), `B_order` (`[L]B = 0`), decode ∘ encode (`decodePoint_affine`,
`decodePoint_some`, `decode_encode`), and signature correctness (`sign_verifies`). Axioms of `sign_verifies`,
`decode_encode`, `decodePoint_affine/some`, `B_sign_bit_needed`: propext, Classical.choice, Quot.sound (no
`native_decide`, no `sorry`). Cost: Bytes / Decode / Sign each check in under 3 s at ≤ 0.78 GB maxrss (leaves; no
literal point next to literal bytes, so far below CODEC-20's line).
**Critique of part 4.** (1) SHA-512 is still trusted as computed by `Sha512.hash` (RFC vectors only); signature
correctness does not depend on it (any function would do), but unforgeability is not a theorem here and cannot
be without a hardness assumption. (2) `sign_verifies` is about Lean's `sign`, the test-tooling signer; the deployed
signer is custody's Rust, and the bridge is the RFC vectors and the cross-checks, not a theorem. (3) `verify` is
cofactored: `verify_iff` + `sign_verifies` say it accepts honest signatures and exactly the cofactored equation;
the stricter non-cofactored check is not what is deployed, by design (CODEC-11).
**Meta-critique.** The last gap was priced as "sqrtRatio with a 2^252 exponent near the CODEC-20 memory line"; it
was not near it at all, because every fact here is symbolic (a power is `Nat` exponent algebra, Fermat is the
existing `fin_fermat`). The memory line binds literal points next to literal bytes, and decode ∘ encode has none.
Status: parts 1–4 built; CODEC-23 complete.

## CODEC-24 · The broker frames are a second generated file, `emit-broker` (HOSTING-3's ask; CODEC-3, 2026-10-17)
**Decision.** `Emit/Broker.lean` prints `launcher/src/broker_generated.rs` by `Rust.taggedFile` from
`Hosting.Broker.Wire.{askCases, requestCases, verdictCases, answerCases}` as `wire::{Ask, Request, Verdict,
Answer}`, with `FRAME_MAX = Broker.Bounds.frameMax` (131072, the frame and every field bound) and the
15-case refusal table as `wire::BrokerRefusal` (with `name()`). Its own exe `emit-broker` (only `main`)
and its own `gates/generated.tsv` row. `taggedEnum` now prints struct variants the way rustfmt does:
when every variant's `{ fields }` body fits rustfmt's `struct_variant_width` (35), each is one line;
otherwise all are vertical. The two existing generated files are byte-identical.
**Alternatives.** One file with two bounds (taggedFile takes one `max`: the field readers would need a bound
per family). `emit-hosting` writing both files, chosen by the path argument (an output that depends on its
file name). Running rustfmt over the output in the gate (a second tool in the generated check).
**Why.** One file per bound keeps `taggedFile` unchanged. The generated check compares bytes, so the file
must already be rustfmt's shape.
**Critique.** The rustfmt rule is copied, not derived: it was measured against rustfmt 1.10 on these files
(the all-or-nothing variant rule and width 35), and a rustfmt version that changes it shows up as a fmt red
in the crate, not in the generated gate. Both files define `wire` and `FRAME_MAX`. They are separate Rust
modules, so this is not a collision, but a reader has to check which `FRAME_MAX` is in scope.
**Meta-critique.** I matched rustfmt's output rather than making the emitter's layout independent of rustfmt,
because the crate's fmt check is HOSTING's gate and a generated file has to pass it.
Status: built.

## CODEC-25 · `Cell.Fits` is emitted for the phone: `cell_fits::{KIND_LIMIT, SLOTS_MAX, SLOT_KEY_LIMIT, VALUE_BYTES_MAX, fits}` (CLIENT-3's need; CODEC-4, 2026-10-17)
**Decision.** `client/src/generated.rs` gains `pub mod cell_fits`: the four bounds of the cell codec's domain
as `u64` constants read from `Kernel.Bounds` (`kindLimit`, `slotsPerCellMax`, `slotKeyLimit`,
`valueBytesMax`), and `fits(kind, &[(key, value_len)])`, their conjunction. `Codec.Kernel.cell_fits_iff_bounds`
states `Cell.Fits` in exactly those names (so the emitted numbers are the predicate's, not a copy), and
`cell_fits_kind_strict` is the tooth: kind `kindLimit` is outside, `kindLimit - 1` inside.
**Alternatives.** Constants only, CLIENT writing the conjunction (a hand rule in Rust). A Lean `Bool`
`Cell.fits` with a decide-equivalence theorem, printed as Rust (the printer would still be a template). Moving
`Cell.Fits` into a def module (it is a `Prop` in a proof module by C3; nothing deployed needs a `Bool`).
**Why.** The phone must refuse what the codec cannot carry with no bound of its own (law 2); the numbers come
from one table and the theorem pins the predicate to that table.
**Critique.** The Rust conjunction is a template, like `path_clean` (CODEC-21): the numbers are tied to
`Cell.Fits` by a theorem, the control flow (`<` vs `<=`, which list length) is not. The tooth catches a `<=`
for the kind only by the reader's comparison, not mechanically. `fits` takes value lengths, not bytes, so a
caller can pass a wrong length.
**Meta-critique.** I chose the template over a Lean-evaluated test table because the predicate has four
clauses and the differential theorem I owe for `path_clean` (CODEC-21) is the general fix for both; this
adds a second instance of the same debt rather than a new kind.
Status: DELETED (ROOT's ruling on CLIENT-16). `cell_fits` had no caller: a leaf refusal is a decision, so it
belongs to Lean's leaf decoder, and the phone reads through that decoder. What replaced it is a theorem:
`Codec.Kernel.leaf_decode_cellFit : leaf.decode b = .ok l → l.CellFit Cell.Fits ∧ b = leaf.bytes l`
(Codec/Proofs/World.lean, from `leaf_lawfulOn`), with the tooth `leaf_decode_refuses_misfit` (no bytes decode
to a leaf holding a kind-2^32 cell). `cell_fits_iff_bounds` and `cell_fits_kind_strict` went with it, because
nothing in Lean used them.
**Critique of the first version.** I emitted a predicate before asking whether anything would call it. An
emitted check with no caller cannot go red, which is the no-op-for-later that the charter forbids.

## CODEC-26 · A turn's record is exactly `Turn.logWeight` bytes (KERNEL-32's numbers; CODEC-4, 2026-10-17)
**Decision.** `Codec.Kernel.turn_size_logWeight : (∀ d, dc.size d = 32) → (turn dc).size t = t.logWeight`, for EVERY
turn (no `Fits` premise: `size` is structural), from `op_size` (`Op.weight`: set 9 + v, erase 5), `act_size`
(`Act.logWeight`), `cell_size` (`Cell.weight` = 9 + `Slots.weight`), `touch_size` (`Touch.weight`), and
`foldl_add_size` (a list's size is its u32 header plus the sum). Deployed: `Codec.Deployed.turnBytes_size :
(env.turnBytes t).size = t.logWeight` (through `LawfulOn.size_eq`). Tooth `turn_size_needs_digest32`: with a
length-prefixed digest the empty turn is 44 bytes against a weight of 72, so the 32-byte premise carries content.
**Alternatives.** `≤` (what Admit.lean's docblock used to claim without a proof): an over-charge would be
invisible. A Rust or sim comparison only: KERNEL-8's `Gen.checkLogWeight` (3883 of 3883) is evidence, and this
is the theorem behind it.
**Why.** KERNEL-2 chose equality, so the charge for the log is the log's size, not a bound on it. KERNEL-32 moved
the weights to the codec's numbers, and this pins them there: if either side changes, this proof breaks.
**Critique.** `size` is the codec's size FUNCTION. That it is the byte count of `bytes` is `LawfulOn.size_eq`,
which holds for the lawful deployed digest (used in `turnBytes_size`) but is not a premise of the generic
theorem. The equality is for the record, not for what the World grows (`Turn.growth`), which has no codec.
**Meta-critique.** I stated the generic theorem over `size`, not `bytes.size`, so it holds for every turn with no
fit premise. The deployed corollary carries the bytes meaning.
Status: built.

## CODEC-27 · The emitted `path_clean` is checked against Lean's decoder on every commit (CODEC-21's critique; CODEC-4, 2026-10-17)
**Decision.** `emit-hosting` prints `wire::PATH_VECTORS`: 19 paths (the empty path; leading, trailing and doubled
separators; `.`/`..` alone and inside; `...`, `.a`, `a.`, a backslash; components of `componentMax` and
`componentMax + 1` bytes; NUL inside), each with the verdict `(Path.split v).all Path.clean` that the
emitter computes. `path_clean` becomes `pub`, `launcher/tests/path_vectors.rs` asserts `path_clean(v) == ok` on
every row, and `gates/runs.tsv` row `cargo:launcher:path_vectors` runs it in every judge.
`Codec.Path.fits_split : fits max (split b) = ((split b).all clean && decide (b.size ≤ max))` states the decoder's
whole condition in the Rust shape (the `bytes(max)` bound, then the components). Mutation measured: `<=` →
`<` against `COMPONENT_MAX` fails the test on the 64-byte row.
**Alternatives.** A Lean theorem about the Rust text (Lean does not read Rust). Generating the Rust control
flow from Lean's `clean` definition (a printer from Lean terms to Rust: a much larger emitter whose output
would still be checked only by reading it). Vectors in a `#[cfg(test)]` module of generated.rs (no judge runs a
crate's unit tests; a test nobody runs cannot go red).
**Why.** CODEC-21 left the Rust rule tied to Lean by inspection only. Now any drift on the edge cases the
vectors name goes red in the judge.
**Critique.** Vectors are finitely many inputs. A Rust rule that agrees on all 19 and differs elsewhere passes, so
this is a differential test, not a proof. The rows are chosen to hit each conjunct of `clean` and each split
case, but that coverage is a claim I made by reading, not a theorem. Found on the way: the compiled emitter
misprints the Lean literal `"a\x00b"` as bytes `a, 0x0b`, because Lean 4.30's C backend emits it inside a C
string, where `\x` escapes are greedy (checked in the emitted C). The NUL row is therefore built from bytes. No
Lean source in this repo has `\xHH` followed by a hex digit (grep).
**Meta-critique.** I took the vector route because it puts the check in the judge today. A Lean-to-Rust printer
for `clean` would remove the template, but it is a bigger and differently-risky emitter. I recorded it as the
alternative rather than deferring it as "the real fix", because a printer's output is also only checked by
running it.
Status: built.

## CODEC-28 · A refinement's lawfulness theorem is its check; the census refuses a refinement without one (CODEC-5/16's gap; CODEC-6, 2026-10-17)
**The question first: which refinements can change what they mean while their shape stays the same?**
There are 26 refine sites in the tree, counted by the census itself, not by grep: Codec 22, Host 3, Lang 1.
They fall into two classes.

*Filtering* (`accept` refuses some inner values; the predicate is what the refinement adds):
`bool` (u8 ∈ {0,1}) · `kernel/discipline` (u8 < 4) · `kernel/ascending` (keys strictly ascend under `Ord D`)
· `kernel/leaf-fit` (every slot holds its kind's leaf, KERNEL's `Leaf.fits`) · `kernel/trie-order` (the listing
is `Trie.Canon (trieSpec E)`'s own) · `path/badComponent` (`Path.fits`) · `lang/data: no value` (nothing).

*Iso* (`accept` is total and `back` is its inverse; the refinement only names the wire's positions):
`i64` · `kernel/entry` · `kernel/slot` · `kernel/leaf` · `kernel/op` · `kernel/cell` · `kernel/act` ·
`kernel/touch` · `kernel/turn` · `kernel/right` · `kernel/acct-ref` · `kernel/body` · `kernel/unsigned/v2` ·
`kernel/call` · `kernel/world/v3` · `kernel/carried/v1` · `host/entry` · `host/base` · `host/carried-head`.

All 26 already had a canonicity theorem (`LawfulOn Q c` / `Lawful c`) except `host/base`, which HOST-9 landed
at 40fe056 for this census. `kernel/world` and `kernel/carried` are canonical up to `Equiv`, through
`world_decode_bytes` and `carried_decode_iff`. No refinement's `accept` disagrees with its stated predicate
today, so there is no defect to fix forward.

**Finding.** Option (a) of CODEC-5's handoff was already mostly built. `LawfulOn Q c` determines a decoder
completely: `decode b = .ok v ↔ Q v ∧ b = bytes v` (`LawfulOn.decode_eq_ok_iff`). What was missing is the
theorem that this pins `accept`, plus a check that no refinement goes without it.
`Codec/Proofs/Refine.lean`, `refine_accept_iff`: if the inner codec is lawful on `P` and `refine name c accept
back` is lawful on `R` (with `R y → P (back y)`), then for every inner value `x` with `P x`,
`accept x = some y ↔ x = back y ∧ R y`. So changing what `accept` admits without changing `R` breaks the
theorem; that is a proof break, not a broken promise. The teeth are the three ways an edit goes wrong:
- `refine_not_lawful_of_refuses`: an `R`-value is refused.
- `refine_not_lawful_of_admits`: a non-`R` value is admitted.
- `refine_not_lawful_of_respells`: a second spelling is admitted.

`Codec/Proofs/RefineTooth.lean` instantiates them, at `Kernel.Sim`'s parameters, on the mutation a careless
edit would make. Each mutant keeps its name, so it keeps its shape and tag, and each is proved not lawful on
the predicate its theorem states.
- `bool_tooth`: nonzero reads as true.
- `discipline_tooth`: ≥ 3 reads as value.
- `ascending_tooth`: the check is dropped and a repeated key is admitted.
- `leafFit_tooth`: the check is dropped and a nullifier holding an entry is admitted.
- `trieOrder_tooth`: build kept, listing check dropped, so a swapped listing is a second spelling.
- `slot_tooth`: the kinds are swapped in `accept` alone.

**The gate.** `Census/Refines.lean` `#refine_census "gates/refines-allow.tsv" <libs>` runs from gates/census.py
in the same environment as the axiom census, agreed with GATES-2. A refine site is a definition whose body, under
its lambdas, is `Stream.refine "<literal>" …` or a `Stream.mk` whose shape is `Shape.refine "<literal>" …`.
Each site needs a theorem whose conclusion, after its binders, is `Lawful (c …)` or `LawfulOn P (c …)`, with
`c` as the head constant and `P` not syntactically `fun _ => False`. An allow row names the theorems that
state the site's decode, and the census checks that each one exists and has `decode (c …)` in its type. A
row that matches no site, or one for a site that has its own theorem, is red. Today:
`REFINE-CENSUS ok: 26 refine sites, 24 with a lawfulness theorem, 2 by allow row`.
Plants, run on a scratch module, each red by name:
- `refine site …plantBool ("plant/bool") has no lawfulness theorem`;
- a theorem about another codec (`plant_other : Lawful bool`) leaves plantBool red, and named in an allow row
  for `i64` it is `states no decode of …i64`;
- `allow row is stale: …bool has its own lawfulness theorem`.

**What the content tag covers now, and what it still cannot see.** A tag is `H(label, shape)`, and a
refinement contributes only its name to the shape. With every refinement carrying a lawfulness theorem, the
tag plus the tree's theorems now cover:
- the byte grammar (the shape);
- every refinement's accepted set, as its theorem states it. Changing what `accept` admits means editing a
  theorem statement in a Codec proof module, which is where the name sits.

It still cannot see three things.
1. **A relabelling.** If `accept` and `back` are changed together so their composite stays lawful on the same
   predicate, the shape, the name, the tag and every theorem all stay the same. `slot_relabel_unseen` proves
   that one exists: `slot` with cell and nullifier swapped in both functions is lawful on the same predicate,
   has the same shape, and writes `.cell 0` as different bytes, so a stored cell slot would be read back as a
   nullifier. The exposure is every iso refinement with two same-typed positions:
   - slot: cell/nullifier;
   - right: observe/mutate and invoke/enroll;
   - act: keep/retire;
   - turn and unsigned: notBefore/validUntil/charge, world/member;
   - touch: cell/seen;
   - world, carried, host/base, host/entry, carried-head: their Nat and digest fields;
   - bool and discipline: their codes;
   - i64: any bijection of 8 bytes.

   Only a theorem that restates `back` could pin these, and that would be a twin of the definition.
2. **A predicate that is relative to another layer's definitions.** `kernel/trie-order`'s `Q` is
   `Trie.Canon (trieSpec E)`, `kernel/leaf-fit`'s is KERNEL's `Leaf.fits`, and `kernel/ascending`'s is `Ord D`.
   A KERNEL edit to `trieSpec` (depth, bit order) changes what `kernel/trie-order` accepts, the Codec theorem
   still proves, and the tag stays. Owed next, as CODEC-28's second step: a deployed theorem that
   `kernel/trie-order` accepts exactly the listings strictly ascending by (kind, id bytes) with each slot
   holding its kind's leaf, stated without `Trie`. A routing change then breaks a Codec theorem.
3. **Hand versions inside names.** `kernel/world/v3`, `kernel/carried/v1` and `kernel/unsigned/v2` are option
   (b) living on inside the content-addressed scheme. They are deleted in the World's next flag day (the
   journal refusal agreed with KERNEL-10, 10-17), where the tag moves anyway. From then on, each refinement's
   name is the name it refuses with.

**Alternatives.**
- (b) A version in each name, bumped by hand. That is a promise, and the three survivors above show it decays
  into decoration.
- (c) A gate that hashes the refine functions' elaborated terms (or source) into the tag. It does see a
  relabelling. But it couples every tag to proof-irrelevant refactors (KERNEL-35's emptyHash change would have
  rotated every trie tag), it reaches transitively into other layers' definitions, and its terms move with the
  toolchain. Every false positive forces a re-genesis and kills the carry across a flag day that CODEC-22 keeps
  on purpose.
- (d) A semantic pin keyed by tag: for each codec, the decoded `repr` of bytes sampled deterministically from
  its shape, with the gate refusing when the repr changes under an unchanged tag. This would see relabellings
  that (a) cannot. But it is a pin table, which is what CODEC-5 deleted. It needs `Repr` for every kernel type.
  It sees only what one sample distinguishes, and it moves on a field RENAME. Put to ROOT as the one open fork;
  ROOT ruled: BUILD it, as a detector (below).

**Why (a).** It turns the accepted-set half of the promise into a check, with no table, no hash, and no
coupling to refactors. The theorems it rests on were already the codecs' canonicity proofs, so the new
machinery is one lemma, its teeth, and a census.

**Critique.** (a) detects a careless edit, not a deliberate one. Someone who changes `accept` and its predicate
together, under the same name, gets green theorems and an unmoved tag. The census makes that edit land in a
proof module, next to the name, but nothing forces the rename. A relabelling (1) passes everything. The
census recognises refine sites syntactically: a codec built by a helper that wraps `refine` behind a
non-literal name, the way `Stream.refine` itself does, is not a site. Today the only such helpers are the
combinators, which are generic in the name. And a `LawfulOn P` with a vacuous but not literally-False `P` would
pass the census; the second-agent statement read (law 6) is what catches that.
**Meta-critique.** I came in expecting to write 26 new theorems and found 24 already standing. The pull was to
write them anyway, because "a theorem per refine" was the brief. Restating what `LawfulOn` already says would
have been 26 twins. The bias that remains is the one CODEC-22 named: I favour the mechanism I already have
(content tags plus canonicity) and priced (d) as a pin table partly because CODEC-5 rejected pins. That
rejection was about pins as IDENTITY, and (d) would be a pin as DETECTOR, so the fork is real and ROOT's.
Status: built (census, refine_accept_iff, teeth, and (d) below); step 2 (trie-order stated in bytes) and the version-suffix
deletion are in progress.
**Built: (d) as a detector (ROOT ruling, 10-17).** The rule it enforces: **a change of meaning under the same bytes bumps
the label.** CODEC-5's rejection stands for pins as identity (the tag is the identity). This table's only power is to
go red. `Emit/Vectors.lean` is the `codec-vectors` exe, and gates/generated.tsv runs its `--check` on every commit.
`gates/codec-vectors.tsv` holds 69 vectors of the census's 26 sites: one per constructor of each sum, two for each
record. Each vector is bytes encoded from values drawn from `Kernel.Sim`'s generator, seeded by the site's name (none
written by hand), plus the site's tag and the decoded text. The kernel codecs are taken at Sim's parameters. The one
printer is `print`: `ok` + the value's `Repr` on one line (field and constructor names), or `refused` + the refusal.
A trie is printed as its listing and a journal as its list, so a hash or balancing change is not a change of meaning.
- `--check`: for every row under the site's current tag, the bytes must decode to the pinned text. Otherwise red:
  `MEANING CHANGED under the same tag …: rename the refinement`. A site with no row under its current tag, a stale
  tag, or a row naming no site is also red.
- `--write`: keeps every row whose tag did not move VERBATIM and draws fresh rows only for a moved or new tag. Re-running
  the generator therefore cannot launder a relabelling.

Plants, run in wt/codec and reverted:
- `kernel/slot` relabelled under the same name (`slot_relabel_unseen`'s swap): RED (12). Both slot vectors went red,
  and so did every site containing a slot (leaf-fit, trie-order, world, carried, host/base).
- the same, after `--write`: still RED (12).
- the same swap renamed `kernel/slot/relabelled`: `--check` first says `no vector under its current tag … stale tag`.
  `--write` then re-pins exactly host/base, kernel/carried, kernel/leaf-fit, kernel/slot, kernel/trie-order and
  kernel/world (the re-genesis set the rename implies), and `--check` is ok.

**Critique (d).**
- It is a differential detector. A relabelling of two positions that hold EQUAL values in every vector is not seen.
  The values are 64-bit draws, so two fields collide only by chance, but an empty list or `none` pins nothing about
  its element type. The generators therefore draw at least one element for tries, journals and paths, and options
  are drawn both ways across the vectors.
- The text is `Repr`, so a field or namespace RENAME in KERNEL turns the table red under an unchanged tag. The table
  then demands a label bump for a change that is not one of meaning. That cost is accepted: the bump is a rebuild.
- A hand edit of a same-tag row's text would hide a relabelling from `--check`. Closing that needs the gate to compare
  the candidate's table with its parent's: rows keyed by (site, tag) are immutable. GATES-3 is asked.
- Only Sim's instantiation is pinned. A relabelling that only the deployed digest codec could show does not exist,
  because the sites are generic in `dc`.
- The decoded column is only as strong a witness as the printer (GATES-3): `Repr` could print two values alike. For
  the kernel types it is derived (constructor and field names, every field), and a `ByteArray` prints as hex.
  The one weakening is the World: its trie is printed as its listing, which is exactly the trie codec's content.
**Flag day: the World journal (KERNEL-39, agreed with KERNEL-10 at 129bb73; CODEC-6, 10-17).**
- The World's wire is refined by a named predicate: `journalWire E dc = refine "kernel/journal" (worldWire E dc)
  (journalFits height journal)`, and `world`'s shape is `.refine "kernel/world" (journalWire E dc).shape`.
- The journal list is bounded by `Bounds.journalMax`, not `worldMax`, so an oversized journal is refused `pastBound`
  before one entry is read.
- `World.CodecFits` gains `journalFits w.height w.journal.toList = true`, which KERNEL's `journalFits_of_ok`
  discharges for every `JournalOk` World. Its journal bound is now `journalMax`.
- `world_decode_journalOk` (generic, and deployed with no premise) shows a decoded base is `World.JournalOk`. The list
  checked at decode IS the decoded map's own `toList` (`toList_ofList_of_sorted`, from the strict ascent the same
  decoder checked), which is KERNEL-10's vacuity condition.
- Teeth (WorldTooth): `world_refuses_future_entry` and `world_refuses_shared_height` (both `rejected 0 "kernel/journal"`,
  through KERNEL's `journalFits_future` / `_twice`), `world_reads_windowed_journal`, and
  `world_refuses_oversized_journal` (`pastBound`). `journalFits` sorts with `List.mergeSort`, which the kernel does
  not reduce, so these teeth go through `world_decode_wire_ok` / `_refused` rather than `decide`.
- The hand versions are deleted: `kernel/world/v3` → `kernel/world`, `kernel/carried/v1` → `kernel/carried`,
  `kernel/unsigned/v2` → `kernel/unsigned`. From now on every refinement's name is the name it refuses with.
- The refine census also requires every site to have codec vectors.

What re-emits: gates/codec-vectors.tsv re-pins exactly kernel/unsigned, kernel/call, kernel/world, kernel/carried and
host/base, and adds kernel/journal (71 vectors, 27 sites). What re-geneses: every Store, because its base stamp
(`Base.shapeStamp`, over the World codec's tag) moved. What refuses to load: an old base refuses `shapeMismatch` by
stamp before decoding. An old carried export file refuses by its stamp (the carried tag moved with the rename),
and so does a base whose journal is outside the window (`kernel/journal`).

## CODEC-29 · `kernel/trie-order` is the order of the bytes, stated without the trie (CODEC-28 step 2; CODEC-7, 2026-10-17, agreed with KERNEL-10)
**Decision.** The predicate behind the trie-order refinement was KERNEL-relative: `Trie.Canon (trieSpec E)`. A change to
`slotBit` or `byteBit` would therefore have moved which listings decode, and every Codec theorem would have stayed
green. Three proof modules now restate it in bytes.
- `Codec/Proofs/TrieOrder.lean`, the generic half:
  - `BitLt S d k k'` means that at the first bit in `[d, depth)` where k and k' differ, k's bit is clear.
  - `build_listing_iff`: under `Trie.SepAt S d l`, `(build l).toList = l ∧ leavesNodup (build l)` holds exactly when
    `l.Pairwise (BitLt S d)` holds on its keys. The proof is by the recursion of `build`. At a node, the listing is
    its bit-d-clear filter followed by its bit-d-set filter. At depth, two keys in one leaf would contradict SepAt.
  - `cells_get_ok`, `cells_get_refused` (`rejected i "kernel/trie-order"`) and `cells_get_ordered`, all under
    `Trie.Separates`.
- `Codec/Proofs/SlotOrder.lean`, the bytes half:
  - `compare_lt_iff_bits`: for two byte strings of one size, `compare` is `.lt` exactly when, at the first differing
    `byteBit` (MSB of byte 0 first), the first string's bit is clear. Two lemmas build it. `nat_lt_of_testBit`
    proves it from div/mod by a power of two. `first_bit_diff` proves it by strong recursion.
  - `SlotBefore E s s'` puts cells before nullifiers, then compares the ids' bytes with `compare`. No trie appears.
  - `bitLt_trieSpec_iff (hE : E.Lawful n)` shows `BitLt (trieSpec E) 0 ↔ SlotBefore E`.
  - The cells theorems are restated over `SlotBefore`.
- `Codec/Proofs/TrieOrderDeployed.lean`:
  - `trieOrder_iff`: given `fitList.get b i = ok (l, j)`, `cells.get b i = ok (build l, j)` holds exactly when
    `l.Pairwise SlotBefore env`. `slotBefore_iff` shows that `SlotBefore env` is the kind first, then `Digest`'s
    `compare`.
  - `trieOrder_refuses` and `trieOrder_accepted`.
  - Teeth, over the ids lo = 01 00… and hi = 80 00…:
    - `cells_refuses_bytes_descending`: the listing hi, lo decodes to `rejected 0 "kernel/trie-order"`.
    - `cells_reads_bytes_ascending`: the listing lo, hi reads back.
    - `lsbRouting_refuted`: a routing that reads each id byte low bit first falsifies the order theorem, and its own
      check admits hi, lo, which the deployed codec refuses.
- maxrss is 0.77 GB per module, about 2 s each, which is the import floor.
**Contract (KERNEL-10).** Routing stays a kernel decision. A deliberate change to `slotBit`, `byteBit` or `trieDepth` lands
as `kernel!` together with the Codec re-proof of `bitLt_trieSpec_iff` and a re-pin of the vectors. It cannot pass silently.
No tag moves, no vectors change, and nothing re-emits or re-geneses.
**Critique.**
- (1) The theorem pins the order relative to `E.bytes`. A lawful Env whose `bytes` permuted the digest's bytes would
  route "by its bytes" yet differ from `Digest.compare` on the raw digest. At deployment `env.bytes = Digest.bytes`
  (`slotBefore_iff` is `Iff.rfl`), so the deployed statement is the real one.
- (2) `Pairwise` is the strong form. The adjacent (`Chain'`) form follows by transitivity and is not stated, because
  nothing consumes it.
- (3) The teeth use the deployed digest and no `Sim`. Every `decide` there evaluates `byteBit` only. `Array.compareLex`
  is well-founded and is never reduced: `lo_hi` goes through `compare_lt_iff_bits`.
**Meta-critique.** "A routing change breaks a Codec theorem" is only a detector if someone reads the break as a meaning
change rather than a proof to patch. The real guard is the vectors: a routing change moves which listings decode, and
`codec-vectors --check` refuses the old trie-order rows under the unchanged tag. The theorem names what changed. The
vectors refuse it.

## CODEC-30 · Law-6 read of the two Equiv allow rows (GATES-3's request; CODEC-7, 2026-10-17)
**Read.** gates/refines-allow.tsv excuses `kernel/world` and `kernel/carried` from a plain lawfulness theorem. For each row
I read the theorems it names:
- `world_decode_bytes` (hd, `World.CodecFits E PD w`): `∃ w', (world E dc).decode ((world E dc).bytes w) = .ok w' ∧ w'.Equiv w`.
- `eq_bytes_of_world_decode`: `(world E dc).decode b = .ok w → b = (world E dc).bytes w`.
- `carried_decode_iff` (hd, `Carried.CodecFits`): `(∃ c', (carried E dc).decode b = .ok c' ∧ CarriedEquiv c' c) ↔ b = (carried E dc).bytes c`.
- `eq_bytes_of_carried_decode`: whatever decodes is exactly its own bytes.
Each row names theorems that state `decode` of the excused constant (the census checks the head constant). Neither theorem
is a `P → P` restatement: both go through `journalWire_lawfulOn` / `carriedWire_lawfulOn`, which carry the
`kernel/journal`, `kernel/ascending` and `kernel/trie-order` checks. `World.Equiv` is `=` on the trie, height, chain,
allowance and origin, and `TreeMap.Equiv` on the journal.
**Is Equiv the right relation? Yes, for the type KERNEL carries.** `World.journal : Std.TreeMap D (Nat × D) compare`.
Two TreeMaps with one key set can differ in balancing: `ofList` of the sorted listing and the map a fold built by
`insert`/`erase` are generally not `=`. So `decode ∘ bytes = id` is false, and a plain `Lawful`/`LawfulOn` theorem is
unprovable for this type. The direction that matters is `eq_bytes_of_*_decode`, which is exact (`=` on bytes). So the
bytes are a function of the contents, and the codec is canonical.
**Could `=` be reached?** Only if KERNEL changed the journal's type to a canonical representation. Candidates are a
strictly sorted list (a subtype), or the journal as a second `Trie.T`, whose `build_toList` already gives `=`. Then the
allow rows go and plain `LawfulOn` theorems replace them. That is KERNEL's call (lookup cost: the journal is at most
`Bounds.journalMax` entries and read on every admission), so I state it here rather than decide it. The allow rows stand.
**Critique.** An allow row is a standing exception, and exceptions accrete. Both rows exist for one reason, the
`TreeMap`. If KERNEL ever moves the journal into a canonical type, both rows must be deleted in that commit. The
census makes this automatic: a row that excuses a site with a plain lawfulness theorem is an error.
**Meta-critique.** "TreeMap balancing is not contents" is true, but it is also the kind of argument that keeps a
weaker statement because it is the one we have. The test is whether any consumer needs `=` on a decoded World. Today
none does: every kernel theorem over a decoded base takes `World.Equiv` congruences (`live_congr`, `root_congr`), or
reads the trie, which is `=`.

## CODEC-31 · The journal is a trie on the wire too; decode ∘ bytes = id for the World and the carried state; both allow rows deleted (KERNEL-41 (a′) with KERNEL-12; CODEC-7, 2026-10-17)
**Decision.**
- **One listing refinement for both tries.**
  - `listingAccept S` (Codec/World.lean) builds the trie from the listing and keeps it iff it lists that listing back with no
    key twice in a leaf.
  - `cells = refine "kernel/trie-order" (fitList dc) (listingAccept (trieSpec E)) toList`, whose shape and tag are
    unchanged.
  - `journalTrie = refine "kernel/journal-order" (rawList journalMax (dc × nat64 × dc)) (listingAccept (journalSpec E)) toList`.
  - One accept function serves two literal sites, so the refine census still sees each site. A wrapper def would have
    hidden both from `siteName?`.
  - `trieListing_lawfulOn` (generic) has `cells_lawfulOn` and `journalTrie_lawfulOn` as instances.
  - `trieListing_get_ok`, `_refused` and `_ordered` (generic, over `Separates`) have the cells and journal restatements
    as instances.
- **The journal's order is the id bytes.**
  - `bitLt_journalSpec_iff (hE)` shows `BitLt (journalSpec E) 0 k k' ↔ compare (E.bytes k).data (E.bytes k').data = .lt`.
  - The `journalTrie_get_*` lemmas follow from it, over `JournalBefore`.
  - Deployed: `journalOrder_iff` (accepted iff strictly ascending by `Digest` compare) and `journalOrder_refuses`
    (`rejected i "kernel/journal-order"`).
- **The kernel's `kernel/ascending` is deleted**, together with `ascendingList`, `ascendingBy`, `ascendingList_lawfulOn`, the
  sorted-TreeMap lemmas and `ascending_tooth`.
  - It checked ascent by `compare` on D, which agrees with the trie's byte order at the deployed Digest but not
    generically.
  - At Sim (u64, little-endian bytes) the two orders differ, so one of the two checks would have refused valid journals
    or been vacuous.
- **`kernel/journal` stays.** It is `journalFits` over the journal trie's own `toList`. Canonicity does not imply the
  window facts.
- **World and carried.**
  - `world = refine "kernel/world" (journalWire E dc) (some ∘ ofWire) toWire` and `carried` likewise.
  - `ofWire` and `carriedOfWire` are now pure tuple maps with no `E`, which replaces KERNEL-12's scaffold.
  - `world_lawfulOn : LawfulOn (World.CodecFits E PD) (world E dc)` and `carried_lawfulOn` are plain lawfulness theorems.
    `World.CodecFits` gains `JournalTrieFits`: the journal trie is canonical and its listing is within bounds.
  - `world_decode_bytes` and `carried_decode_bytes` are `= .ok w` exactly. `world_decode_iff` and `carried_decode_iff`
    are `decode b = .ok w ↔ b = bytes w`.
  - `world_bytes_equiv`, `carried_bytes_equiv`, `CarriedEquiv` and `ofWire_toWire_equiv` are deleted, since `World.Equiv`
    is deleted by KERNEL.
  - Both gates/refines-allow.tsv rows are deleted. The census now counts 27 sites, all 27 with a lawfulness theorem and
    0 allowed.
- **JournalOk from the codec.**
  - `world_decode_journalOk` and `world_get_journalOk` (generic and deployed; the latter is HOST-11's ask, at any
    offset) give `w.JournalOk E` from KERNEL's `journalOk_of_fits` (Canon from the rebuild, `journalFits` from the
    refusal).
  - `carried_decode_journalCanon`.
  - `carried_fits` drops its `journal.size < journalMax` premise, because `JournalTrieFits` carries the bound.
- **`kernel/carried-journal` (HOST-11 found this one).** Before this, nothing on the carry path refused a carried journal
  outside the window of the carried height: the carried codec had no `kernel/journal`, and KERNEL's `checkCarry` has
  none either. So a file with a future entry passed `importWorld`, genesis-wrote a Store, and its reopen then refused
  `baseUndecodable`.
  - `carried` is now refined by `carriedJournalWire = refine "kernel/carried-journal" carriedWire (journalFits height
    journal.toList)`, so the World's check now runs on the carry path too.
  - `Carried.CodecFits` gains the `journalFits` conjunct. `carried_fits` takes it from `World.CodecFits`.
  - `carried_decode_journalFits` and `carried_decode_wire_refused` are added.
  - Teeth: `carried_refuses_future_entry` (`rejected 0 "kernel/carried-journal"`) and `carried_reads_windowed_journal`.
  - The name differs from the World's `kernel/journal` because the vectors table keys on the refinement name.
- **`batch`** is `List (Turn × (D × D))`, carrying both roots after each turn (scaffold kept). `batch_lawfulOn` follows it.
- **Teeth.**
  - Deployed: `journal_refuses_ids_descending` and `journal_reads_ids_ascending`.
  - Sim: `carried_reads_ordered_journal`, plus `carried_refuses_swapped_journal` and `carried_refuses_repeated_txId`
    (both `kernel/journal-order`).
  - `journalOrder_tooth`: a check-less `kernel/journal-order` respells.
  - The journal-window teeth are restated over the trie (`world_refuses_future_entry`, `_shared_height`,
    `world_reads_windowed_journal`).
- **maxrss:** about 0.78 GB per module; TrieOrderDeployed is 1.08 GB.

**Flag day.**
- Shapes that changed: the World wire's journal part (`kernel/ascending` became `kernel/journal-order`), so the
  `kernel/journal`, `kernel/world`, `kernel/carried` and `host/base/index-count` tags move. The cells' `kernel/trie-order`
  tag does not move.
- Re-emitted: gates/codec-vectors.tsv re-pins exactly those four sites, adds `kernel/journal-order` and drops
  `kernel/ascending` adds `kernel/carried-journal` (71 vectors, 27 sites). The generated Rust files are unchanged (checked).
- Re-genesis: every Store (KERNEL-41's roots and chain move anyway).
- Refuses to load: an old base refuses `shapeMismatch` by stamp, and an old carried export refuses by its stamp.

**Critique.**
- (1) `listingAccept` is shared and the sites are literal. A third trie would add a third site by the same one-liner,
  which the census sees. The census still cannot see a site built through a wrapper def, so whoever writes one blinds
  it. That is GATES' to close if it matters: the census could follow defs whose body is `refine <bound name> …`.
- (2) The journal-order teeth that need the order relation are stated at the deployed digest. Sim teeth go through
  `decide +kernel` on two-entry tries, which is small.
- (3) `JournalTrieFits` puts the height bound (< 2^64) in the codec's domain. Reached Worlds need KERNEL's
  `admit_height_lt` and `journal_height_le` to place a folded World in it, so HOST's export completeness still waits on
  that composition (Host/Proofs/Carry's named gap).

**Meta-critique.** I was tempted to keep `kernel/ascending` beside the trie check "for the deployed reading", which
would have been two checks that agree only at one parameter: exactly the twin the charter forbids. The order theorem
gives the deployed reading without a second check.

## CODEC-32 · The refusals are a third trie on the wire; the World carries its step count; the log record is a list of steps (KERNEL-44 / KERNEL-47 with KERNEL-14; CODEC-8, 2026-10-18)
**Decision.**
- **The refusals' listing, by the one listing refinement.**
  - `refusalSlot = refine "kernel/refusal-slot" (choice 2 (dc | dc × u64))`, which is `tx id | count member win`, kind byte as in
    `refusalKeyBytes`.
  - `refusalLeaf = refine "kernel/refusal-leaf" (choice 2 (nat64 × nat64 | nat64))`, which is `refused h code | count n`.
  - `refusalsTrie = refine "kernel/refusal-order" (rawList worldMax (refusalSlot × refusalLeaf)) (listingAccept (refusalSpec E)) toList`.
    It is the third literal site over `listingAccept`, so the census sees it. `refusalsTrie_lawfulOn` is an instance
    of `trieListing_lawfulOn`.
  - The wire bound is `worldMax`, as for the cells. The kernel's real bound is per member: at most
    `refusalsPerWindow` (16) refused leaves per member per window, kept at most three windows, plus one count per
    member. That is `members × (3·16 + 1)` live leaves, which the wire does not restate. A member count has no
    static bound, so a static wire bound would be a second, weaker statement of the same fact.
  - There is no separate fit site. `refusalsFits` refuses every misfit pairing (tx/count, count/refused), and it
    runs on the World.
- **Order in bytes (the CODEC-29 contract).**
  - `bitLt_refusalSpec_iff (hE)`: `BitLt (refusalSpec E) 0 k k' ↔ compare (refusalKeyBytes E k) (refusalKeyBytes E k') = .lt`.
    `refusalKeyBytes_size` gives `9 + n` bytes, and depth 328 ≥ 8·41.
  - `refusalsTrie_get_ok / _refused / _ordered` restate it over `RefusalBefore`, under KERNEL's `refusals_separate`.
  - Deployed: `refusalOrder_iff` (accepted iff strictly ascending by key bytes) and `refusalOrder_refuses`
    (`rejected i "kernel/refusal-order"`).
  - The window's eight bytes are little-endian, so two count keys of one member order by the window's LOW byte
    first. That is the bytes' order, not the numbers', and nothing reads it as a number order.
- **The World wire** is `cells ‖ journal ‖ refusals ‖ height u64 ‖ steps u64 ‖ chain ‖ allowance u64 ‖ origin`. The
  refinement chain, each step a named refusal:
  - `kernel/journal`: `journalFits` (unchanged predicate);
  - `kernel/refusals`: KERNEL's `refusalsFits height refusals.toList`. Every key holds its kind's leaf. A refused
    call sits at `1 ≤ h ≤ height+1`, inside its kept window, with `h, code < 2^64`. A count is for the current
    window and `1 ≤ n ≤ 16`;
  - `kernel/refusals-disjoint`: KERNEL's `refusalsDisjoint`. No transaction id is both recorded refused and
    journaled (`fold_refusalsDisjoint`). It costs one journal lookup per refused leaf. This was the vacuity
    read's ask, closed with KERNEL-14;
  - `kernel/steps`: `height ≤ steps`, KERNEL's `fold_height_le_steps`. Genesis has 0 ≤ 0, and a carry sets
    steps := height;
  - `kernel/world-budget`: `weight + allowance < 2^64`. The predicate is unchanged, because the refusals are not
    storage (KERNEL-44: they are bounded per member, not charged).
  - `refineIf_lawfulOn` is the one lemma for the three `if q x then some x else none` checks.
- **`World.CodecFits` is a structure with named fields**: cells, journal, refusals, height, stepsLt, chain, budget,
  origin, journalFits, refusalsFits, refusalsDisjoint and steps. Field to site:
  - cells: kernel/leaf-fit and kernel/trie-order;
  - journal: kernel/journal-order;
  - refusals: kernel/refusal-order;
  - journalFits: kernel/journal;
  - refusalsFits: kernel/refusals;
  - refusalsDisjoint: kernel/refusals-disjoint;
  - steps: kernel/steps;
  - budget: kernel/world-budget.
  Each refine check has exactly one field. The other fields (height, stepsLt, chain, origin) are the u64 and
  digest codecs' domains.
  `stepsLt` (the u64 bound) is kept by admission: KERNEL's `checkSteps` and `fold_steps_lt`. That fix came out of
  the vacuity read: admission did not bound steps until then. The positional conjunction moved every projection whenever a part
  was added, and broke HOST's consumers silently by index. The rows day adds a `rows` field and moves no projection.
- **What a decoded World carries:**
  - `world_decode_refusalsOk` and `world_get_refusalsOk` (generic and deployed) give KERNEL's `World.RefusalsOk`,
    from `refusalsOk_of_fits`;
  - `world_decode_refusalsDisjoint` / `world_get_refusalsDisjoint`, and `world_decode_height_le_steps` /
    `world_get_height_le_steps`, all both generic and deployed;
  - `refusalLeaf_fits_of_refusalsFits`: on a reached World, `refusalsFits` already bounds every leaf counter, so
    HOST's export completeness needs only the listing length.
- **The log record.**
  - `refused = refine "kernel/refused" (dc × dc × nat64 × nat64 × nat64 × rawBytes callMax)`;
  - `step = refine "kernel/step" (choice 2 (turn | refused))`;
  - `batch : List (Step D × D)`: each step paired with `World.roots` after it, the ONE roots digest of KERNEL-47
    amendment 3. The end chain is still derivable.
  - `checkRefusedBounds_fits`: every refusal KERNEL records is in the refused codec's domain.
- **Carried: unchanged.** Carry carries no refusals (KERNEL-44), and `Receive.carry` sets `refusals := .empty`,
  `steps := height`. The carried wire's shape and tag do not move. `carried_fits` reads the new structure.
- **Teeth** (Codec/Proofs/WorldTooth.lean, at Sim, by `decide +kernel` through the wire lemmas):
  - `world_reads_refusals_at_budget`: a count of 16 reads back;
  - `world_refuses_count_past_budget`: 17 is refused `kernel/refusals`. This is the boundary pair, and also a
    vector;
  - `world_refuses_future_refusal`: refused at height 9 in a World at height 7, refused `kernel/refusals`;
  - `world_refuses_misfit_refusal`: a tx key holding a count, refused `kernel/refusals`;
  - `world_refuses_height_past_steps`: height 7 with 6 steps, refused `kernel/steps`. Its twin is
    `world_reads_height_eq_steps`;
  - `world_refuses_refused_and_journaled` (`kernel/refusals-disjoint`), with its twin
    `world_reads_refused_not_journaled`;
  - window edges, each paired:
    - `world_reads_refusal_at_next_height` (h = height+1) against `world_refuses_future_refusal`;
    - `world_reads_refusal_at_window_edge` (2049 at height 4096) against `world_refuses_stale_refusal` (2048);
    - `world_reads_current_window_count` against `world_refuses_past_window_count`;
  - `world_refuses_zero_count`, `world_refuses_misfit_count_key` and `world_refuses_refusal_at_zero`;
  - `refusals_refuses_swapped_listing` (`kernel/refusal-order`) and `refusals_reads_canonical_listing`.
- **Vectors.** Eight new sites, each with its lawfulness theorem: kernel/refusal-slot, kernel/refusal-leaf,
  kernel/refusal-order, kernel/refusals, kernel/refusals-disjoint, kernel/steps, kernel/refused and kernel/step.
  Boundary pairs:
  - `kernel/refusals`: counts 16 and 17;
  - `kernel/steps`: steps = height, and height − 1;
  - `kernel/refusals-disjoint`: a refused id unjournaled, and the same id journaled.
  The table holds 95 vectors over 35 sites, and the refine census counts 35/35 with 0 allow rows.

**Flag day.**
- Shapes that changed: the World wire (a refusals listing and a steps u64) and the batch record (`Step × roots
  digest` replaces `Turn × (root, journalRoot)`).
- Tags that move:
  - `kernel/journal` and `kernel/world-budget`, through their inner wire. The name stays: the vectors gate asks
    for a rename only when meaning moves under an unchanged tag;
  - `host/base/index-count`, and the batch record's stamp;
  - the new sites listed above.
- Tags that do not move: `kernel/carried`, `kernel/carried-journal`, `kernel/journal-order` and `kernel/trie-order`.
- Re-emitted:
  - gates/codec-vectors.tsv re-pins the moved sites and adds the eight new ones;
  - client/src/generated.rs gains `status::DECLINED` and the `Declined` action rows. Those come from PROTOCOL-8's
    half, through the unedited generator;
  - launcher/src/generated.rs and broker_generated.rs are unchanged.
- Re-genesis: every Store. The roots and chain move anyway: `headLink` gained a tag byte and `rootsDigest`.
- Refuses to load: an old base refuses `shapeMismatch` by its stamp. An old batch record refuses by its stamp.
  An old carried export still IMPORTS, because its shape is unchanged and a carry starts a new chain.

**Critique.**
- (1) The codec accepts two Worlds that no fold reaches. Both are deferred as cv 01a14da3-3e7a (`refusalsCounted`
  plus `fold_refusalsCounted`, KERNEL's):
  - (a) more tx leaves than `steps − height`. Each tx leaf costs one refusal step, and genesis and carry start
    empty with steps = height;
  - (b) current-window counts whose sum differs from the number of current-window tx leaves. A base could drop
    a member's count and reset that member's budget while keeping its tx leaves. Stating this per member needs
    the member in the tx leaf, or a count-sum statement, plus trie-cardinality lemmas.
  Each would be one more refine site with teeth once KERNEL has the fold theorem.
- (2) Pruning keeps every refused leaf of the window just closed and drops every count from that window. So on
  every reached World, the current window's counts sum to exactly the number of tx leaves with
  `refusalWindow (h − 1) = refusalWindow height`. That sum is checkable once KERNEL proves it (1b, cv
  01a14da3-3e7a). The per-member split is NOT checkable, because a tx leaf does not carry its member. The chain
  commits it; the codec cannot recompute it.
- (3) `World.CodecFits` becoming a structure is a consumer break for HOST (Host/Proofs/Deployed). HOST-12 rewrites
  those positional projections by name once, and never again.

**Meta-critique.** I was about to rename `kernel/world-budget` because the brief said "the tag MOVED where meaning
moved". But the rename rule exists for meaning moving under an UNCHANGED tag. Here the shape moves the tag anyway,
and the budget's meaning is unchanged. Renaming would have been ceremony that teaches the next reader the wrong
rule.

## CODEC-33 · The rows on the wire: a fourth trie, the turn's row touches and range reads, and the kernel's own byte functions as codec sites (KERNEL-46/48 with KERNEL-15/16 and LANG-14; CODEC-9, 2026-10-18)
**Decision.**
- **The kernel's byte functions ARE codec bytes (ROOT's ruling on the kernel-functions vectors).** Rather than a
  separate table of function outputs, each of KERNEL's three byte functions is proved equal to a lawful codec's
  bytes, so it is a refine site like any other: the census finds it, it carries a lawfulness theorem, and its
  vectors sit in `gates/codec-vectors.tsv` under the same immutability rule.
  - `rowKeyBytes E s = (rowKey dc).bytes s` (`rowKeyBytes_eq`), site `kernel/row-key`:
    `dc × nat8 rel × choice 2 (unit | bytes8 keyBytesMax)`, i.e. `parent ‖ rel ‖ 0` or `parent ‖ rel ‖ 1 ‖ |k| ‖ k`.
  - `rowLeafBytes l = rowLeaf.bytes l` (`rowLeafBytes_eq`, for every leaf), site `kernel/row-leaf`:
    `choice 2 (nat64⁵ × bool | nat64 × rawBytes valueBytesMax)`. KERNEL-48 gave the row value a u32 length
    prefix for this (CODEC-9's ask A); before it the value was trailing and no codec spelled it.
  - `rangePinBytes E p rel w pre l = (rangePinWire dc).bytes (p, rel, w, pre, l.map (key, rowDigest leaf))`
    (`rangePinBytes_eq`), site `kernel/range-pin`: `dc × nat8 × oneOf #[1] × nat8 × bytes8 keyBytesMax ×
    rawList rowsPerRelationMax (rowKey × dc)`. KERNEL-48 factored `rangePinBytes` out of `rangePin` and made its
    count four bytes (ask B), so the listing is rawList's.
  - What follows from lawfulness, named: `rowKeyBytes_inj` / `rowKeyBytes_decode`, `rowLeafBytes_inj` /
    `rowLeafBytes_decode`, `rangePinBytes_inj` / `rangePinBytes_decode`. Injective on the domain (relation and
    width below 256, key and prefix ≤ keyBytesMax = 128, value ≤ valueBytesMax, counters < 2^64, ≤ 4096 rows),
    and the bytes read back. A range pin binds the parent, relation, width, prefix and the listing of (key, leaf
    DIGEST): a leaf is bound through `rowDigest`, i.e. up to a collision of the hash, and that is the claim.
  - Two primitives: `nat8` (shape `u8`, LawfulOn `< 256`) and `bytes8 max` (a one-byte length, new Shape
    constructor `bytes8`, code 17; `Shape.put_prefix` extended). Every existing shape's bytes are unchanged, so no
    existing tag moved for this.
- **The turn** (`kernel/turn`): `… ‖ event ‖ rows ‖ ranges`, `rows = rawList rowsMax rowTouch`,
  `ranges = rawList rangesMax rangeRead`.
  - `kernel/row-act`: `choice 5` in constructor order (keep | insert amt v | upsert amt v | retract |
    declare limit cap width retract); `kernel/row-touch`: `rowKey × option dc × rowAct`; `kernel/range-read`:
    `dc × nat8 × bytes8 keyBytesMax × nat64 × dc`.
  - `Turn.Fits` gains both lists; `checkBounds_fits` reaches them because KERNEL-48 moved the rows' syntactic wire
    bounds into `checkBounds` (ask C): every admitted turn is in the codec's domain, so `turnBytes` stays
    injective on admitted turns.
  - CODEC-26 holds: `turn_size_logWeight` is re-proved with KERNEL's `RowSlot.weight`, `RowAct.logWeight`,
    `RowTouch.weight`, `RangeRead.weight` (ask D). Its tooth now reads 52 bytes against a log weight of 80.
- **The call** (`kernel/unsigned`): `… ‖ body ‖ rowPins ‖ ranges` (LANG-14), `rowPins = rawList callMax (rowKey × dc)`,
  `ranges = rawList callMax rangeRead`; `Unsigned.Fits` gains both.
- **The World wire**: `cells ‖ journal ‖ refusals ‖ rows ‖ height ‖ steps ‖ chain ‖ allowance ‖ origin`.
  - `rowsTrie = refine "kernel/row-order" (rawList worldMax (rowKey × rowLeaf)) (listingAccept (rowSpec E)) toList`,
    the fourth instance of the one listing refinement. The wire bound is `worldMax`, as for the refusals: a reached
    World holds ≤ 4096 rows per relation and ≤ 256 relations per live parent, but the parents have no static
    bound, so a static rows bound would restate the map bound, weaker.
  - Refine chain: … `kernel/steps` → `kernel/rows` (KERNEL's `rowsFits E rows.toList`: kind, rel < 256,
    key ≤ 128, limit ≤ 4096, width ≤ 128, count ≤ limit, sum ≤ cap < 2^64, amt < 2^64, value ≤ valueBytesMax,
    ascending by key bytes) → `kernel/rows-headed` (`rowsHeaded`: every row has its head at the head's width,
    every head's count and sum are its rows') → `kernel/rows-parented` (`rowsParented E trie rows`, which KERNEL-17 added to KERNEL-48 at CODEC-9's ask:
    every relation's parent is a live cell; added from the vacuity read, the class of `kernel/refusals-disjoint`:
    no fold reaches a relation under an absent or retired parent, since a head is born only under a cell its turn
    creates and KERNEL-17's `dropHeads` removes a retired parent's heads) → `kernel/world-budget`.
  - Every check reads the wire through `ofWire` BY NAME (`(ofWire x).height`, …), not by tuple position: the next
    part added moves no check.
  - `kernel/world-budget` reads `World.weight + allowance < 2^64`, and `World.weight` is now
    `cellsWeight + rowsWeight` (KERNEL-16). The predicate's meaning moved with the weight; the tag moves anyway
    with the wire, so no rename (CODEC-32's meta-critique).
- **`World.CodecFits` gains ONE field**, `rows : RowsCodecFits E PD w.trie w.rows`, a structure with one field
  per site: `listing` (kernel/row-key, kernel/row-leaf, kernel/row-order), `fits` (kernel/rows), `headed`
  (kernel/rows-headed), `parented` (kernel/rows-parented). No existing projection moved.
- **Carried** (KERNEL-46: rows are state, carried whole): `cells ‖ allowance ‖ height ‖ journal ‖ rows`, refined
  `kernel/carried-journal` → `kernel/carried-rows` → `kernel/carried-rows-headed` →
  `kernel/carried-rows-parented` → `kernel/carried`.
  `Carried.CodecFits` became a structure (cells, allowance, height, journal, journalFits, rows) in the same move.
  `carried_fits` reads the World's rows field. `carried_decode_rows`: an import never genesis-writes a Store whose
  base the World codec would refuse `kernel/rows`, `kernel/rows-headed` or `kernel/rows-parented`.
- **Order in bytes, at variable width** (`Codec.Proofs.RowOrder`, the one new proof):
  - `compare_lt_iff_bits_differIn`: for two byte strings that differ at a byte inside both, `compare` is the order
    of the first differing bit (which then lies inside both). `compare_lt_of_bits_at` generalizes CODEC-29's
    lemma to unequal sizes.
  - `rowKeyBytes_differIn`: two different keys within bounds differ at a byte inside both, because the rows key
    codec is lawful, so no key's bytes begin another's (prefix-freedom is a consequence of `rowKey_lawfulOn`, not
    a separate argument).
  - `rows_separateOn` (KERNEL's, Kernel/Proofs/RowsSep.lean; Codec's twin deleted by CODEC-10) / `rows_sepAt`:
    separation on the keys' DOMAIN. `Trie.Separates (rowSpec E)` over all
    `RowSlot` is false (`byte8` truncates rel mod 256; a 256-byte key writes length 0; keys past 128 bytes run past
    `rowDepth`); CODEC-9 reported it and KERNEL-48 now says "on its domain". The listing theorems got `_sep`
    variants that take separation of the listing's keys (`trieListing_get_ok_sep` / `_refused_sep` /
    `_ordered_sep`); the rows codec's decoded keys are in the domain by construction.
  - `bitLt_rowSpec_iff`, `rowsTrie_get_ok` / `_refused` / `_ordered` over `RowBefore`; deployed `rowOrder_iff`,
    `rowOrder_refuses`, `rowKeyBytes_inj`.
- **Teeth** (Codec/Proofs/WorldTooth.lean, Sim, each plant with its accepted twin):
  - `world_refuses_sum_past_cap` (one row of 41 under cap 40, `kernel/rows`) against `world_reads_sum_at_cap` (40);
  - `world_refuses_uncounted_row` (`kernel/rows-headed`) against `world_reads_counted_row`;
  - `world_refuses_orphan_relation` (no cell 1, `kernel/rows-parented`) against `world_reads_counted_row`;
  - `world_reads_declared_relation` (a head with no rows);
  - `rows_refuses_swapped_listing` (`kernel/row-order`) against `rows_reads_canonical_listing`;
  - `rowKey_refuses_wide_key` (a length byte of 129, `pastBound 128 129`) against `rowKey_reads_widest_key` (any
    128-byte key);
  - carried: `carried_refuses_sum_past_cap` (`kernel/carried-rows`), `carried_refuses_uncounted_row`
    (`-headed`), `carried_refuses_orphan_relation` (`-parented`), against `carried_reads_counted_row`;
  - `rows_kindByte_needed` (KERNEL-17's ask): without the kind byte, the head of relation 7 under parent 1 and
    that relation's row with the empty key are two in-domain keys whose bits agree everywhere, so
    `rows_separateOn` rests on the kind byte.
- **Vectors.** Thirteen new sites: kernel/row-key, row-leaf, row-act, row-touch, range-read, range-pin, row-order,
  rows, rows-headed, rows-parented, carried-rows, carried-rows-headed, carried-rows-parented. The table holds 140
  vectors over 48 sites (`--write` from main's table, then `--check` ok). Boundary pairs:
  - `kernel/row-key`: a key of 128 bytes reads back, 129 is refused `pastBound 128 129` at its length byte;
  - `kernel/range-read`: a prefix of 128 bytes, and 129 refused `pastBound`;
  - `kernel/rows` and `kernel/carried-rows`: one row whose amount is the cap (40), and one past (41);
  - `kernel/rows-headed` and `kernel/carried-rows-headed`: a head counting its one row, and counting two;
  - `kernel/rows-parented` and `kernel/carried-rows-parented`: a relation under a live cell, and the same rows
    without that cell.
  Drawn Worlds and carried states put their relations only under their own live cells (`liveIds`).
  ROOT's boundary pairs were named in kernel refusals (`keyWidth` at 128/129, `rangeTooLong` at k/k+1). The codec
  cannot refuse those: `keyWidth` is a key not at its RELATION's width and `rangeTooLong` is a listing longer than
  the signer's `most`, both judged against the World by admission. What the codec refuses is the wire bound
  (`pastBound` past 128), and that is the pair in the table; `keyWidth` and `rangeTooLong` are KERNEL's teeth.

- **Memory shape (CODEC-20).** maxrss under `lake env lean`: Codec/Proofs/Rows 0.75 GB, RowOrder 0.75, Kernel 0.75,
  World 0.75, Carried 0.75, WorldTooth 1.13 (was 0.78; the rows teeth build Sim tries of depth 1304 by `decide +kernel`).

**Flag day.**
- Shapes that changed: the turn record (rows, ranges), the signed call (rowPins, ranges), the World wire (a rows
  listing), the carried wire (a rows listing), `rowLeafBytes` (the value's length prefix) and `rangePinBytes` (a
  four-byte count).
- Tags that move (measured: exactly these rows changed under `--write`): `kernel/turn`, `kernel/unsigned`,
  `kernel/call`, `kernel/step`, every World-wire site (kernel/journal, kernel/refusals, kernel/refusals-disjoint,
  kernel/steps, kernel/world-budget), `kernel/carried-journal`, `kernel/carried`, `host/base/index-count`, and the
  thirteen new sites. No other row of main's table changed. An old carried
  export now refuses by its stamp (unlike CODEC-32, where it still imported).
- Re-emitted: gates/codec-vectors.tsv (`--write` from main's table). Re-genesis: every Store (the roots digest gained
  the rows root; the turn and call bytes moved).
- Refuses to load: an old base (`shapeMismatch` by stamp), an old batch record, an old carried export.

**Critique.**
- (1) `rowsFits`'s ascending clause restates what `kernel/row-order` already enforces on a decoded listing (the
  trie's order IS the bytes' order, `bitLt_rowSpec_iff`). It is KERNEL's predicate, checked as one; the cost is
  one comparison per entry.
- (2) That admission keeps `rowsFits` / `rowsHeaded` / `rowsParented` (`World.RowsOk`, `admit_rowsOk`,
  `fold_rowsOk`, `head_sum`) is KERNEL-17's, in Kernel/Proofs/RowsHead.lean. HOST's export completeness
  (`carriedFits_of_kept`) reads the rows off `Kept` through it. Until it lands, export re-reads its own file and
  refuses rather than writes a bad one.
- (3) `Unsigned.Fits` gained `rowPins` and `ranges`, and nothing proves an admitted call is in that domain. It
  needs no proof: a call is only ever decoded from the wire, and the decoder refuses anything outside it.

**Meta-critique.** The first plan for the kernel-functions vectors was a second table of function outputs keyed
by an Emit-side label. That would have been a second detector with its own label discipline, and a label nobody
bumps when the function changes. Proving each function equal to a codec's bytes made it an ordinary site: the tag
moves when the shape moves, and the census already requires the theorem.

## CODEC-34 · A reached World's rows are in the codec's domain (HOST-12's export completeness; CODEC-10, 2026-10-18, against KERNEL-17's `World.RowsOk`)

**Decision.** `Codec.Kernel.rowsCodecFits_of_ok` (Codec/Proofs/RowsReached.lean): over a lawful digest codec
writing a lawful `Env`'s bytes, a World with `RowsCanon E`, `RowsOk E` and at most `worldMax` listed rows has
`RowsCodecFits E (fun _ => True) w.trie w.rows`. Deployed: `Codec.Deployed.rowsCodecFits_of_ok` (at
`Receive.deployed_lawful`, `digestCodec_bytes`) and `Deployed.genesis_rowsCodecFits` (the premises meet at
genesis) and `Deployed.fold_rowsCodecFits` (every World the deployed fold reaches from genesis, with
RowsCanon and RowsOk discharged by KERNEL's `deployed_fold_rowsOk`; only the listing bound is the caller's). `RowsOk` hands over `rowFits` (hence both entry domains), `rowsHeaded` and `rowsParented`; the one
field it does not is the listing's ascending key bytes, drawn from canonicity: `build_listing_iff` at
`Trie.build_toList` gives bit order, `bitLt_rowSpec_iff` makes it `compare` order on the key bytes, and
`toList_lt_of_compare_lt` (with `byteArray_toList_eq`) makes that the `List` order `ascendingBytes` decides.
No new refine site, no tag moves, no vector moves.

**Tooth.** `rowsCodecFits_needs_order`: two empty heads of one parent, swapped in one (non-canonical) leaf,
pass `rowFits` and `rowsHeaded` and the length bound, and fit no `RowsCodecFits` for any `PD` and any cells;
in order they pass `rowsFits`. Dropping the canonicity premise is refuted by order alone.

**Also.** `rowsListing` (the rows listing codec) moved from Codec/Proofs/RowOrder.lean into Codec/World.lean
(a proof module exported an abbrev: closure C3), and `rowsTrie` now refines it by name: one shape, not two.

**Critique.** `hlen` stays the caller's: `RowsOk` bounds rows per relation, not the listing, since parents are
not statically bounded. HOST discharges it at export (the writer refuses past `worldMax` as the reader does).
Vacuity read (second agent): LAND; both its optional additions taken (the genesis instance, the tooth's note).

## CODEC-35 · The trie day, codec half: a proof's path carries its bits; the listings did not move (KERNEL-49 (a), CODEC-11, 2026-10-18)

**Decision.** KERNEL-49 (a) compresses the one trie: a node branches at the first bit its keys disagree on and its
hash commits that bit as a u16, so a proof's sibling is `(bit, digest)`.
- **The proof wire is a codec.** `Codec.Kernel.proof S kc dc : Stream (Trie.Proof K D)` (Codec/World.lean) =
  `option (rawList worldMax (kc × dc)) ‖ rawList S.depth (nat16 × dc)`, read back only when `Trie.ascends S 0 sibs`
  (each bit at least one past the last, below `S.depth`: the check `verifyInclusion` / `verifyExclusion` make before
  hashing), refused `kernel/proof` by name otherwise. A NEW refine site (new tag). New primitive `Shape.u16` (tag code 18,
  `Shape.put_prefix` extended) and `Stream.nat16` (two bytes LE, `nat16_lawfulOn` on `< 2^16`).
  `Codec/Proofs/TrieProof.lean`: `proof_lawfulOn` (exact on `ProofFits`: entries and digests in their codecs' domains,
  at most `worldMax` entries, bits ascending; the length and u16 bounds follow from the ascent, `ascends_length`,
  `ascends_lt`), `proof_decode_ascends`, `proof_get_refused`. PROTOCOL agreed (PROTOCOL-11 → PROTOCOL-12): the receipt
  carries it as `.bytes "jpath"` / `.bytes "rpath"` in place of jterm/jkeys/jdigests/jsibs and their r-twins (one
  codec, not a Layout list plus a bits list that could disagree).
- **The listings did not move, by theorem and by plant.** `build_listing_iff` keeps its statement over the compressed
  `build` (now proved via `build_listing_iff_le`, fuel `S.depth - d ≤ f`, splitting at `splitBit`: `splitBit_none` /
  `_some`, `bitLt_skip` (on keys agreeing on `[d, b)`, BitLt from d is BitLt from b), `sepAt_skip` / `_side` / `_sub`,
  `mem_build`): the accepted listings are exactly those in bit order, a fact about keys, not shapes. So every
  listing statement (`listing_check_iff`, `trieListing_get_*`, `cells_get_*`, SlotOrder, RowOrder, TrieOrderDeployed's
  `trieOrder_iff` … `rowOrder_iff`, RowsReached) is text-unchanged and re-checked. `Codec/Proofs/ListingPin.lean`: six
  plants, each the PRE-day bytes of one vector (`kernel/trie-order` 1, `journal-order` 1, `refusal-order` 1,
  `row-order` 0 (a head and three rows sharing the 280-bit stem), `steps` 0 (a whole World), `carried` 1) reproduced
  by the compressed `Trie.insert` in reverse order (`decide +kernel`). And `codec-vectors --write` into an EMPTY file
  (every site drawn fresh through the new trie) equals the table byte for byte except the new site.
- **Adapted, no statement changed:** `leavesNodup` (node pattern), `leavesNodup_of_routed` (Routed's new node clause),
  `nodup_of_leavesNodup_build` (cased on `splitBit`).

**Teeth** (Codec/Proofs/WorldTooth.lean, Sim, plant beside its twin): `proof_refuses_past_depth` (one sibling at bit
`journalDepth`) against `proof_reads_deepest_bit` (`journalDepth - 1`); `proof_refuses_repeated_bit` (bits 5, 5)
against `proof_reads_ascending_bits` (5, 6).

**Vectors.** One new site, `kernel/proof` (under `journalSpec Sim.env`): a drawn journal's inclusion proof, an
absent id's proof, and the boundary pair (bit 255 read back, bit 256 refused `kernel/proof`). 144 vectors / 49 sites,
`--write` from main's table then `--check` ok; no other row moved.

**Flag day (codec's part).** The proof wire is new (the receipt re-cut is PROTOCOL's); an old receipt refuses on
parse. Every root re-geneses (KERNEL's). The World, carried, rows, journal and refusals listings, and every vector
under an unchanged tag, are byte-identical. No generated Rust table moves (no name moved; five emits `--check` rc 0).

**Critique.** `proof` reads a leaf's entries as a list (at most `worldMax`), though at the deployed specs a canonical
leaf holds one key: a singleton term would make the wire smaller but put a "leaves hold one key" premise on the
receipt's round trip. The sibling list's `S.depth` bound is implied by the ascent and kept only so a reader stops at
the count. `kernel/proof` checks shape, not hashes: a well-formed proof can still fail to climb to the root, which is
the verifier's job, not the codec's.

## CODEC-36 · A package's codec is a refine site, so the vectors gate sees a new Lang tag (cv 01a14e58-1586; CODEC-11 with LANG-15's yes, 2026-10-19)

**The gap.** LANG-51 added a term tag (`refuse`, 17) and a primitive (`lenLe`, 11). Bytes that used to be refused now
read as a package. The vectors gate saw none of it: a package was decoded by `packageStream` (the generic
`Codec.Tree`) followed by `packageOf` written out by hand, so it was not a refine site. The tree's shape cannot see tags,
so no tag moved either.

**Decision.**
- `Lang.Wire.packageCodec := refine "lang/package" packageStream (packageOf ·.val) packageFit`.
  - `packageFit p` is `packageTree p` when that fits. Otherwise it is a fixed refused node, which is never written:
    `encodePackage` writes only a package that is `packageWire` and fits.
  - `encodePackage` writes `packageCodec.bytes p`, the same bytes as before.
  - `decodePackage` keeps its own order, the whole-input check before `packageOf`, so every verdict is unchanged
    (LANG-15's condition). `decodePackage_eq_codec` proves it accepts exactly what `packageCodec.decode` accepts.
- Theorems in Lang/Proofs/Wire.lean:
  - `packageCodec_lawfulOn`: lawful on exactly `packageWire ∧ fits`.
  - `decodePackage_eq_ok_iff`: statement unchanged.
  - `packageCodec_get_refused`: every tree `packageOf` does not read is refused by name.
  - Teeth: `package_refuses_unknown_term_tag` against `package_reads_known_term_tag`.

**Vectors (43, LANG-15's set).**
- One row per term tag 0–17, type tag 0–7 and primitive 0–11.
- One row per package section: imports; a relation with every option set; one with none; methods and laws.
- The boundary rows: term tag 18, type tag 8 and primitive 12, each refused `lang/package`. When Lang gives one of
  them a meaning, its row flips from refused to read under an unchanged tag, the gate goes red, and the label must
  move (`lang/package/2`, …). That is how a new tag is announced.

**Flag day.** None. No byte, verdict or stored package changes, and nothing re-geneses. The lang-journey run is GREEN;
ledger-sim and hosting-sim 1–3 report ALL PASS, including the byte-identity rows E0/E0s/G0/G0s/A0/A0s.

**Critique.** The boundary rows catch the NEXT tag only, so a Lang change that adds two tags flips one row; that is
enough to go red. A change of meaning inside an existing tag (a field read differently) is caught only by the rows
that use that tag, so each tag has one row, not a sweep of its payloads.

- **2026-10-19, KERNEL-50 (KERNEL-19, ROOT for CODEC):** the World-wire refine chain is now journal → refusals → refusals-disjoint → steps → **refusals-counted** → rows → rows-headed → rows-parented → world-budget. `kernel/refusals-counted` (`countedWire`, `countedWire_lawfulOn`) refuses a base whose window counts are not its records (KERNEL-50 `refusalsCounted`). `kernel/refusal-leaf` gains the charged member (`refused h code member`), so its tag moves with the meaning. Vectors re-emitted for the moved families; the boundary pair is a counted World and the same World with one charge moved.

## CODEC-37 · Versions on the wire: a u64 varint, the entry and rows leaf carry it, the pin preimages keep eight bytes (KERNEL-54 with KERNEL-21; CODEC-12, 2026-10-19)

**The ask.** KERNEL-54 (ROOT, shape N) puts a per-cell write counter in `Entry.live`, a version in every row leaf and a
floor in every relation head, each below `Bounds.counterLimit` = 2^64. The weight charges the 8-byte bound; the disk
pays a varint. Today's `Stream.varint` stops at 2^32.

**Decision.**
- `Stream.varint64 : Stream Nat` (`Shape.varint64`, shape code 20): LEB128, shortest form, below 2^64, at most ten
  bytes. It is `varintOf 10 (2^64)`; `varint` is now `varintOf 5 (2^32)`, the same reader (`getVarint width limit`) and
  the same bytes and refusals as before, so no varint-carrying tag moved. One proof serves both
  (`varintOf_lawfulOn`). Canonicity exact: `varint64_decode_iff` (`decode b = ok v ↔ v < 2^64 ∧ b = bytes v`).
  Width: `varint64_size_le` (≤ 10, the number KERNEL-55's `worldBytesMax` reads) and `varint64_size_max` (2^64 − 1
  is ten bytes: the bound is tight). So the World's bytes are bounded by its weight plus two bytes per version, not by
  its weight.
- `kernel/entry`: live = 0 ‖ version varint64 ‖ cell (the order of `leafBytes`), tomb = 1. `entry_lawfulOn`,
  `entry_decode_iff`; tooth `leaf_decode_refuses_version` (no bytes decode to a live leaf at version 2^64) beside
  `leaf_decode_refuses_misfit`.
- `kernel/row-leaf` (the World's rows listing): a head's floor after its retract byte and a row's version after its
  amt, both varint64; every other counter stays u64. `rowLeaf_lawfulOn`, `rowLeaf_decode_iff`.
- `kernel/row-leaf-hashed` (new site): the same fields with the floor and version as u64, which is KERNEL's
  `rowLeafBytes`, the row pin's preimage. `rowLeafBytes_eq`/`_inj`/`_decode` moved onto it (`rowLeafBytes_decode`'s
  statement now names `rowLeafHashed`). Two codecs for one value is deliberate: the preimage is fixed-width so a
  pin is a function of the eight-byte bound, the disk is what the counter reached; they share `rowLeafOfWire` /
  `rowLeafToWire` and `RowLeafWireFits`, and differ only in the two counters' spelling.
- `kernel/range-pin`: the relation's floor (u64, as `rangePinBytes`) after the prefix. `rangePinWire_lawfulOn`,
  `rangePinBytes_eq`/`_inj`/`_decode` re-proved with the floor.
- The 13 compile-only placeholders K20-K left in Codec/World.lean, Codec/Kernel.lean, Codec/Proofs/{Rows,World}.lean
  are replaced; `ListingPin`'s cells and rows plants re-pinned by hand with versions 300 / floor 2 / versions 0, 128,
  300 (the pre-day bytes with exactly the varint bytes inserted; the World and carried plants hold no live entry and
  no row, so they are unchanged); WorldTooth/RowsReached take the new constructor arities at version and floor 0.

**Vectors.** New sites `varint64` (8 rows: 0, 127, 128, 2^64 − 1 read back; 2^64 `pastBound`, an eleventh byte
`pastBound 10 11`, `80 00` `varint/overlong`, `80` `truncated`) and `kernel/row-leaf-hashed` (3). Boundary rows
through the codecs: `kernel/entry` (version 2^64 − 1 read back; 2^64, an eleventh byte and `80 00` refused at
offset 1), `kernel/row-leaf` (2^64 − 1 as a row version and as a head floor read back; each spelled 2^64 or overlong
refused, the version also eleven bytes long), `kernel/row-leaf-hashed` and `kernel/range-pin` (the floor at
2^64 − 1 read back, the same input one byte short refused `truncated`: an eight-byte field has no larger value).
`codec-vectors --write` into an empty file reproduces the table byte for byte. Re-pinned because their tags moved: entry, leaf, leaf-fit, trie-order, row-leaf,
row-order, range-pin, rows, rows-headed, rows-parented, journal, refusals, refusals-disjoint, steps,
refusals-counted, world-budget, carried, carried-journal, carried-rows, carried-rows-headed,
carried-rows-parented, host/base/index-count. NOT re-pinned: touch, turn, unsigned, call, refused, step, proof — their
shapes hold no leaf and `Kernel.Sim` draws their pins as digests, so their tags and rows are unchanged; the deployed
pin VALUES change, which no vector pins. No kernel refusal name is generated into Rust (the names reach clients as
strings from Lean), so `staleRecorded`, `missingRow` and `overBound .version` add no generated line; the five emits
check unchanged.

**Flag day (with KERNEL-54's `kernel!`).** Moves: the entry, leaf, row-leaf and range-pin shapes, so every World,
carried and base tag; every Store and carried file stamped with the old tags refuses to open by its stamp (never
reinterpreted); re-genesis.

**Critique.** The disk and the preimage now spell the same leaf two ways; a future field added to one and not the
other would be a twin. The guard is structural: both refine the one `RowLeafF` through the one `rowLeafOfWire`, so a new
field must be added to both wires to type-check. The varint makes weight ≥ bytes false for versions at or past 2^56
(nine and ten bytes); the bound that holds is `varint64_size_le`, and HOST's base rows measure the actual.

## CODEC-38 · The World's refusals total on the wire: a third refusals key kind, the cap's boundary pair (KERNEL-55 part 2, R1, with KERNEL-22; CODEC-13, 2026-10-19)

**Shape.** KERNEL-22's R1 adds `RefusalSlot.total (origin) (win)`, key bytes `[2] ‖ origin ‖ u64 win`, leafed by the
existing `count n`. `kernel/refusal-slot` becomes `choice 3`: arm 2 = `product dc u64`, the same body as a member's
count (arm 1), so the wire key is the key bytes' kind byte then the same fixed-width body. No leaf kind is added
(`kernel/refusal-leaf` is unchanged, its tag and rows stay as they are).
- `RefusalSlot.Fits`, `RefusalSlotWireFits`, `refusalSlotWire_lawfulOn` and `refusalSlot_lawfulOn` take the third
  arm. `refusalLeaf_fits_of_refusalsFits` takes `Bounds.refusalsPerWindowMax` into its simp set, because `refusalFits`
  now bounds a total by it.
- Canonicity of the three-kind order: `refusalKeyBytes_kind_lt` (SlotOrder) says a key of a lower kind sorts below
  one of a higher kind at any `Env`, whatever the digests and windows, so a canonical listing holds `tx`, then
  `count`, then the `total`. The order theorem `refusalOrder_iff` is unchanged: it is stated over `refusalKeyBytes`
  and holds for the third kind because `refusalKeyBytes_size` is still `1 + n + 8`.
- Teeth. In TrieOrderDeployed (deployed digest): `refusals_refuses_total_before_count`, where a total listed
  before a count with the SAME digest and window is refused `kernel/refusal-order` by name (only the kind byte
  orders them), and `refusals_reads_count_before_total`, the accepted twin. In WorldTooth (Sim):
  `refusalsFits_total_at_cap` (a total of C = 16384 passes the listing check), `world_refuses_total_past_cap`
  (C + 1 is refused `kernel/refusals`), `world_refuses_total_over_records` (a total of 4 over 3 records is refused
  `kernel/refusals-counted`, though `kernel/refusals` admits it), `world_refuses_missing_total` (records this
  window with no total are refused `kernel/refusals-counted`) and `world_refuses_stray_total` (a second total
  under a digest other than the origin, which `refusalsFits` admits because it reads no origin, is refused
  `kernel/refusals-counted`). Between them the three counted teeth guard each clause of the total arm: the
  count, the presence and the origin. Not toothed by the codec: the clauses capping the two previous windows at
  C records each. A plant there needs C + 1 records; `decide` should not hold that, and no vector row should. Every accepted WorldTooth World with a record this
  window now carries its total (`atCount`, `charged`, and the next-height and not-journaled twins).

**Vectors.** The `kernel/refusals` site gains the cap's boundary pair: a drawn World whose window total is exactly
`Bounds.refusalsPerWindowMax` is read back, and the same World at C + 1 is refused `kernel/refusals` by name.
`kernel/refusals-counted` gains a row: the counted World with its total one over its records, refused by name.
`kernel/refusal-slot` draws all three kinds, and `kernel/refusal-order` and every drawn World carry the total
their records make (`totalOf`; `addRecord` makes `commitRefusals`' three inserts). Re-pinned because their tags
moved (each holds `refusalSlot`): refusal-slot, refusal-order, journal, refusals, refusals-disjoint, steps,
refusals-counted, rows, rows-headed, rows-parented, world-budget, host/base/index-count. 228 vectors over 54 sites.
`codec-vectors --write` into an empty file reproduces the table byte for byte. The carried sites hold no refusals,
so they did not move. No Rust table carries a World tag, and the five emits check unchanged.

**What is not a vector.** A records-backed World at the cap (C records, C counts) is outside what a vector row or
`decide` should hold. The cap's pair is therefore the listing check alone; that the total equals its records is
`kernel/refusals-counted`'s, toothed at small counts.

**Flag day (with KERNEL-22's `kernel!`).** Moved: the refusal-slot shape, and with it every World and base tag.
Every Store stamped with the old World tag refuses to open by its stamp, and the chain re-geneses. The carried
shape is unchanged.

## CODEC-39 · A World's encoded size, exactly, against its weight; the slack is 54/49 (cv 01a150a3-2523; CODEC-13 with HOST-14 and KERNEL-22, 2026-10-19)

**What.** The bridge KERNEL-55 needs. KERNEL bounds a reached World's weight by its genesis allowance
(`allowance_bounds_world`), and HOST's `worldBytesMax` bounds its encoded size. The statement was agreed with
HOST-14, who reads it in `reached_size_le`, and with KERNEL-22, who accepted the factor.
- `Codec/WorldSize.lean` (def-module) holds the measures, named in `Codec.Kernel`:
  - `entrySlack = (54, 49)`;
  - `worldFixed = 104`: four list headers, height/steps/allowance u64, chain and origin;
  - `journalBytes` (72 per entry);
  - `refusalsBytes` (per entry: tx 82, count/total 50, a misfit pairing up to 90);
  - `liveCount`, `tombCount`, `spentCount`, `rowsCount` and `versionBytes`.
- `Codec/Proofs/WorldSize.lean`:
  - `world_size_eq` is exact, with only a 32-byte digest premise:
    `size + 8·(live + rows) = weight + worldFixed + journalBytes + refusalsBytes + 3·(live + tomb) + 2·spent + versionBytes`.
    Every byte has a term. `world_bytes_size_eq` is the same statement for the bytes.
  - `world_size_le`, on `World.CodecFits`: `49·size ≤ 54·weight + 49·(journalBytes + refusalsBytes + worldFixed)`.
    `world_size_le_div` is the floor form, and `world_size_le_deployed` is the bound at the deployed codec.
  - `refusalsBytes_eq_of_fits` / `_le_of_fits`, on `refusalsFits`: `82·tx + 50·(others)`. HOST discharges the counts
    from KERNEL-55 R1's `refusals_bounded` / `refusals_length_le`.
- Why 54/49 and not the pre-54 35/32: `World.weight` charges each version 8 bytes (`counterWeight`), and the wire
  writes it as a u64 varint of 1 to 10 bytes. An empty live cell weighs 49 (32 id, 8 version, 9 cell) and writes 54
  at a version ≥ 2^63.
  - A tombstone is 35/32, a spent nullifier 34/32 and a head 86/84.
  - A row costs at most weight + 2, over a weight of at least 56.
- Tooth: `world_size_slack_tight` (generic; `_deployed` at the deployed codec). `slackWorld`, one empty live cell at
  version 2^63, is in `World.CodecFits` and meets the bound with equality (`49·158 = 54·49 + 49·104`). For every
  ratio a/b below 54/49, the bound at (a, b) is false for it.
- The module imports `Kernel.Proofs.Weight`, so that `Entry.weight`'s equation lemmas have one home. Without it the
  census import failed on `Entry.weight.eq_1`, realized in both modules.
- Vacuity read: no vacuous statement. Its flags were taken: the tooth now carries the CodecFits witness and every
  ratio; the docstrings cite the kernel bound rather than restating it; the measures and the witness `slackWorld` live in a def-module (C3), so HOST can name them.

**Flag day:** none. No wire, tag or vector moves, and nothing re-geneses.
