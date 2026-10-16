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
Status: open. Measure before the Host's hot path depends on it.

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
