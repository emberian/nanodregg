> record copy of redregg/work/DELETE-CODEC-20261016.md, 2026-10-16; the lane logs stay in redregg

# DELETE-CODEC — codec/wire layer deletion dossier (SHORT; cut off by ROOT's re-tasking to BUILD-CODEC)

DISCOVER-CODEC, 2026-10-16. Tree: main 2c27b08b (detached worktree), lane tip gh/lane/codec-shapes e317c181
(extracted via git archive into scratch). READ = counted on that tree with rg/grep; DERIVED = computed from READ
counts; ASSUMED = inference. Nothing built. Truncated: ROOT redirected this agent to build nanodregg Codec/.

## Numbers NOW (seed for a size ratchet) — main 2c27b08b, dirs Compiler Kernel Host Theory Pred

| metric | main | lane e317c181 | how |
|---|---|---|---|
| `@[persisted_codec_tag]` entries | 637 (585 String, 49 List UInt8, 3 Nat) | 635 fingerprinted | READ Compiler/PersistedCodecTags.lean |
| `"DREGG…"` literal sites, Lean C/K/H | 1,567 (611 in registry, 956 outside) | — | READ rg |
| distinct `"DREGG…"` strings, Lean C/K/H | 827 (≈216 not registered) | — | READ/DERIVED |
| `"DREGG…"` literals in Rust native/ | 334 sites, 230 distinct | — | READ; TWINS.md: 65 dual labels, 33 unregistered |
| tags owned by a Host-closure module | 605 / 637; other 32 owned by registry identifier or numeric-byte spelling | — | DERIVED (reach.py vs scripts/gates/host-closure.pin) |
| version chains kept side by side in the registry | 21 stems / 47 tags (LIFECYCLE-* v1..v3, SPK-*, FN/NATIVE-PREFIX, RESOURCE/TRANSACTION 10+13, DURABLE.SEED 1+2) | — | DERIVED |
| retired-frame defs (`retired*Frame/Wire`) | 31 in 30 names | — | READ |
| per-version refusal theorems (`vN_*_refused`, `retired_*_refused`, …) | 91 | — | READ; each is an instance of `framed_refuses_prefix` |
| codec carriers (structures) | 9: StreamCodec, LawfulCodec, StoreCodec.Wire, CellState.Materializer(+Total), ProtectedCell.Spec, DurableCheckpointCodec.Framed, TurnOfIntent.Codec, FramedWalRefinement.FrameCodec, RequestWire | same | READ |
| StreamCodec-typed defs | 880 | 891 | READ |
| LawfulCodec-typed defs | 402 (73 hand `where`, 61 strict wrapper, 48 toLawful, 220 alias) | 366 (37 hand, 3 strict, ~300 stream-derived) | DERIVED |
| canonicity field `encode_decodePrefix` | 0 | 144 sites (field of StreamCodec: all stream codecs) | READ |
| strictCodec / framedRaw / rawCodec uses | 139 / 63 / 46 | 12 / 0 / 4 | READ |
| `List UInt8` lines | 5,119 | 5,136 | READ |
| `ByteArray` lines | 376 | 420 | READ |
| `abbrev Bytes := List UInt8` | 3 | 3 | READ |
| Digest types | 5 (C1: Nat Digest, Digest256 Fin, Blob 32, Fin 32→Fin 256, Selvage) | 5 | ARCH §6.10 C1 |
| files mentioning `Digest` | 516 | 515 | READ |
| `digestStream` (Nat digest, base-255) uses | 812 | 810 | READ |
| `Digest256` lines / `to/ofDigest256` bridges | 37 / 25 | same | READ |
| Migration/carry modules in Host closure decoding OLD deployment shapes (3b1f628a Store2, PayCell v4) | 20 (LegacyContentCarry 606 l, LegacyStoreCarry 268, NeutralPolicyCarry 375, PayCellLegacyV4 447, SourceAgreementLegacyCodec 189, Carried* …) | — | READ host-closure.pin; no journey row names carry (READ grep journey.sh/journey.d) |

## Three biggest deletions (DERIVED)

1. **Hand tag literals + registry + census → content-addressed tags.** 637 registry lines + 956 inline literals +
   the census elaborator (148 l) + 635 fingerprint pins + version chains (47 tags) + 31 retired frames + 91
   per-version refusal theorems. Replaced by `tag = H(label ‖ structural descriptor)`, one general theorem "a
   frame ≠ mine refuses", and StoreEpoch = H(sorted tags) (today StoreEpoch also carries 4 hand labels beside the
   content hash: stateKey, logTag, accumulator, commands — a twin of schemaRefs, `DurableCheckpointCodec.lean:194`).
2. **Eight extra codec carriers → one StreamCodec.** LawfulCodec becomes `StreamCodec.toLawful` only (37–73 hand
   instances restate); Wire/Materializer/Spec/Framed/FrameCodec/RequestWire/TurnOfIntent.Codec become StreamCodecs
   over their types. Strict re-encode wrappers already die on the lane.
3. **Old-shape decoders (migration twins).** The 20 carry/legacy modules decode a retired deployment's bytes —
   forbidden by the doctrine (old shapes refuse, never reinterpret). Re-genesis deletes them; no row exercises them.

Plus: List UInt8 → ByteArray (5,119 lines), Nat digest + digestStream (812 uses) → Digest256 32 fixed bytes,
Rust: hiding.rs hand cSHAKE/KMAC, client_consent stream_nat, spk-host v4 retry encoders, private-backend codec,
mini-sdk contracts — generate from Lean or call the codec child (TWINS.md on hbox).

## The one flag day
One re-genesis: every tag changes spelling (content-addressed), digests change encoding (32 bytes, not base-255),
StoreEpoch becomes one hash. Every Store, fixture Store (7 j1 Stores), golden vector (mini-sdk golden/intents.json),
Rust literal refuses. ORDER, rows covering each, and per-tag persisted/transient table: NOT DONE (re-tasked).
Scratch data: /private/tmp/claude-501/-Users-ember-dev-breadstuffs/b3795e84-08d4-436c-9079-91d4e05687e9/scratchpad/dcodec/{reach.json,tags.tsv}.
