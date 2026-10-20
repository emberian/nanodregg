> record copy of redregg/work/PRIVACY-DESIGN-BRIEF.md, 2026-10-17; the lane logs stay in redregg

# PRIVACY-DESIGN-BRIEF — per-cell blinding custody (D8) for nanodregg, read against the project's history

Reader brief for Ember and ROOT, 2026-10-17. Read-only pass. Tags: **[read]** = read at the cited
place this session; **[inferred]** = my conclusion, not stated by any document. nanodregg paths are
`hbox:/tank/dregg-build/nanodregg/main/…` (main at the time of reading). Note: there is no
`decisions/transport.md`; D8 lives in `redregg/work/nanodregg-scout/ASSEMBLY-transport-consent.md`
§1 C2 and §3 D8, and in `TRANSPORT-LOG.md:33` [read].

---

## 0. The question, and the one-paragraph answer

D8 as written: "the blinding key is a custody question for Ember … C2's option 2 plus the corrections
in §1 C2, written as a KEY-CUSTODY entry in decisions/client.md by CLIENT, not built." Its
META-CRITIQUE: "'It's on the pause list' is a comfortable reason to drop the hardest piece. … If [a
ruling] does not arrive within a week, the absence has become a deferral" [read: ASSEMBLY §3 D8].
PROTOCOL-3 (ruled 10-16): "per-cell hiding/blinding from members is a DECLARED ABSENCE for v1, tied
to the blinding-key custody question open with Ember" [read: decisions/protocol.md PROTOCOL-3].

Short answer (§5 in full): rule option (a) now as a stated threat model rather than an absence. Design
option (b) in its per-object form, with the key in a separate custody record and laws barred from
blinded slots by a theorem. Build it at a named trigger. Do not build host-held per-cell blinding (the
minidregg K-NARROW-HIDE shape): in nanodregg it could hide cells from members only by breaking
follow-consent.

---

## 1. What "privacy" meant across the dregg project, in order

| # | era / doc | what it was | hidden from whom | status then |
|---|---|---|---|---|
| 1 | Bread, ≤05-26: `.docs-history-noclaude/privacy-architecture.md` | anonymous-credential parity (Idemix/BBS+): unlinkable multi-show, issuer anonymity (`BlindedMerklePoseidon2StarkAir`), **predicate proofs** over hidden attributes (Gap 4), selective disclosure (Gap 5); Phase 6 "federation privacy" (encrypted turns under a threshold key / validium blind ordering / full ZK) | **verifiers** of a presentation; Phase 6: the **federation (validators)** | target state; Gap 2 "Turns submitted to the federation are in cleartext" [read] |
| 2 | Bread: `.docs-history-noclaude/federation-privacy.md` | "the ordering service knows everything … a panopticon": commit-then-reveal with ZK validity proofs + Bloom conflict sets, HE, TEE, threshold delayed reveal; recommends layered privacy | the **validators / operator** | design only [read: §Problem Statement, §Recommended Architecture] |
| 3 | Bread: `old-docs/design-network-privacy.md` | Dandelion++, two-bucket padding, then Tor for inter-federation, then a Sphinx mix layer; mixing at the gossip layer | the **network** (IP, timing, size) | staged plan, Phase 1 "NOW" [read] |
| 4 | Bread: `old-docs/intent-privacy-assessment.md` | "Is dregg's intent system private enough? Short answer: No." Public MatchSpecs, PIR only real in DownloadAll, commit-reveal *creates* correlated events | **gossip peers, executor, network** | assessment [read] |
| 5 | Bread: `old-docs/defi-privacy-comparison.md` | notes vs Zcash/Namada: no value commitments, no binding sigs, no memos, no viewing keys; "the executor (block producer) sees amounts" | the **executor** and observers | gap list [read] |
| 6 | Bread, 05-23: `plans/blinded-queue-design.md` | note-spending pattern applied to queues: commitments in, nullifiers out | the **relay/operator** (which entry was consumed) | design; "Admin/operator queues: the admin IS the operator; hiding from yourself is pointless" (§8) [read] |
| 7 | Bread, 05-23: `plans/captp-privacy-analysis.md` | do hosting nodes learn swiss numbers? "By design." The federation is the vat; "For hosted cells, capability security is ONLY against external adversaries … This is not a bug. This is the correct architecture." Escape hatch: make the cell **sovereign** | **external adversaries only**; never the host | analysis, "No fix is needed" [read: §§1–7] |
| 8 | Bread, 05-23: `plans/privacy-governance-fluidity.md` | private migration (stealth addresses), private governance (ring-signature votes, blind proposals), sovereign→hosted "executor learns ALL cell state?" via FHE / MPC / **selective disclosure** (recommended); a 3-tier Pareto frontier: hosted = "Zero privacy, maximum speed", sovereign = full privacy from the federation, max-privacy | source/target **federations**, **voters' coercers**, the **executor** | analysis + priority list [read: §§3, 5, 7] |
| 9 | Bread, 05-24: `audits/AUDIT-privacy.md` | claim → mechanism → delivered? across blinded endpoints, sealing, `Commitment<T>`, sovereign cells, voting, Midnight, encrypted turns, wire | everyone; the audit's question | audit (§2 below) [read] |
| 10 | Bread, 06-28: `extension/PRIVACY.md` | the Cipherclerk's user privacy policy: keys never leave the device; AES-256-GCM at rest under PBKDF2; only connection is the configured node | **us / third parties** (data collection) | shipped policy [read] |
| 11 | Bread: `wasm/src/privacy.rs` | browser bindings: stealth addresses, Pedersen value commitments + conservation/range proofs, sealed intents (SSE), bearer caps, `make_cell_sovereign`, proof composition, facet masks (25 `pub fn`) | observers of addresses/amounts | API surface; header says "Privacy and advanced feature WASM bindings" [read: lines 1–5, pub fn list] |
| 12 | Bread, 07-20→07-25: shielded pool (#10) + apex | Zcash-style notes on a BabyBear STARK; seams #15/#16/#17; the decision and redesign (§2) | **everyone incl. the executor** (amounts, owners) | proof complete in Lean; pool never held value [read] |
| 13 | Mini, 10-01: K-NARROW-HIDE + K-HIDE-ROTATE (`claudesplosion/planning/privacy/k-narrow-hide.md`, `k-hide-rotate.md`; `minidregg/native/resource-client/src/hiding.rs`) | **the per-cell blinding precedent**: a per-cell blinding derived by the OWNER's client (`KMAC256(cSHAKE256("DREGG.CLIENT.BLIND/v1", seed), cell id)`), sent once at birth, stored as a reserved entry in the cell; salted leaves so a narrowed reader can verify the root without the uncovered entries; ratcheted at every write | **other (narrowed) readers** and holders of roots/receipts, "**It does not hide them from the operator.**" | built on a branch, journey KH green; "ember's direction today …: build the hiding root, with custody held by the cell's owner" [read: k-narrow-hide.md §0–§2] |
| 14 | Mini, 10-01→10-04: PRIVATE-CELL / private rooms (`minidregg/docs/PRIVATE-CELL.md`, `PRIVATE-ROOMS-DESIGN.txt`) | client-sealed values: `XChaCha20-Poly1305` under a per-room epoch key drawn fresh by the founder's client, wrapped to members (hybrid X25519 + ML-KEM-768) in the room's `keys` cell; blinded commitment; AAD binds room, cell, address, epoch; 64-byte padding; "laws see only counts and byte sizes" | **the operator** (honest-but-curious primary, active secondary) | devnet quality, "privacy not audited" [read] |
| 15 | Mini, 10-01: `PRIVACY-OBJECT-ARCHITECTURE-2026-10-01.md`, research `2026-10-02-private-objects/` | private programmable objects: three contracts to settle first (message effect, audience transitions, extensibility); "decide whether the first private object is an opaque client-interpreted value with public authorization, or whether the service must enforce a hidden application predicate" | operator, members, recipients, network | study, "not an accepted architecture" [read: §3E, §4] |
| 16 | Mini, 10-01: K-PRED-HASHEQ (`k-hasheq.md`) | **predicate blinding** by commit–reveal at the kernel: a law checks a full-width cSHAKE256 commitment against a later reveal | everyone until the reveal | lane report [read: first 20 lines] |
| 17 | Mini: `TRAFFIC-PRIVACY-PROFILE-P1.md`, `ASYNC-NATIVE-CUSTODY.md` | the cohort mix: which honest member sent which request, among ≥2 honest contributions per epoch; padded mailboxes, cover traffic | a **network observer** | "Devnet quality. Privacy not audited." "No fixed-schedule privacy … claim follows" [read] |
| 18 | nanodregg, 10-16→17 | PROTOCOL-3 whole-log gating; LEDGER: "Every follower sees every balance (no privacy: declared absent)"; D8 | members (by grant only) | declared absence [read: protocol.md PROTOCOL-3; ledger.md] |

The through-line [inferred]: across 18 items "privacy" meant five different adversaries: network,
verifier, other members, executor/operator, and later readers of a root. Every design that hid
anything from the **executor/host** did it by not letting the host execute: sovereign self-execution
plus a STARK (Bread), or client sealing with laws that judge only sizes (Mini PRIVATE-CELL). No
design ever let a host judge state it could not read, except through a proof system.

---

## 2. What was learned, the hard way

1. **The shielded pool never held value.** "Value has NEVER entered the pool. There is no mint, no
   shield, no genesis. Inputs are proven against a WIRE `merkle_root` whose siblings are witness data
   … Outputs are … a Ristretto point with **no note commitment**, so even shielded→shielded outputs
   are UNSPENDABLE … **The pool is a proof-composition demo.**" [read: memory
   `project-shielded-apex-campaign.md`; `docs/DESIGN-shielded-value-on-ramp.md` §0 verdict 1]. L0's
   append was prover-written, so `AccumulatorSound` was FALSE and "harmless ONLY because `root8()`
   is committed nowhere"; L1 "would RELOCATE #15, not close it" [read: same memory].
2. **The ∃-image vacuity.** `IsCommittedNote leaf := ∃ v as ow rd, leaf ≡ hash[…]` holds of every
   field element under `C6Surjective`, so `NoteAccumulatorCR` held for every root "including today's
   prover-written one". It became a standing falsifier for the class [read: same memory].
3. **The apex was vacuous at BabyBear via two floors.** `unfoolability_guarantee` and
   `deployed_system_secure` are vacuous: four of five commitment-floor binders are refuted at
   BabyBear width, and `RestHashIffFrame` is refuted with no hypotheses at all, by Cantor. "a clean
   axiom set is NOT content" [read: memory `project-circuit-soundness-apex.md` READ FIRST]. MEMORY.md
   names the two floors: "hash weld VESTIGIAL, `CommitSurface`-injective the REAL terminal one"
   [read: index line]. The floor-free restatement "does NOT de-vacuum the apex … EXISTENCE is
   floor-free, UNIQUENESS is not" [read: same file, SITE 3].
4. **What the privacy audit found** (05-24): the components are real (sealed box, hiding
   commitments, unlinkable presentations), but "**Hosted cells are cleartext to their federation
   executor.**" The `FieldVisibility` flag only shaped `public_field_view()`, and the executor
   read and wrote fields in cleartext. `EncryptedTurn` was "exported but never consumed".
   `consume_private` "accepts any non-empty `spending_proof`". The trustless-intent threshold scheme
   was a placeholder. The README oversold ("Fully Private" covered ~20% of the metadata surface).
   The audit's own question 6 is our question: "for hosted cells: is there any path to executor-blind
   state transitions, or is the model 'if you want privacy from the executor, become a sovereign
   cell'?" [read: AUDIT-privacy.md §5, §11, §13 Q6, §14].
5. **What the redesign decision chose, and why** (07-20). Three seams: #15 the wire-supplied
   `merkle_root` (theft), #16 a value link that ran only in tests (inflation), and #17 a
   PQ posture overstated while the only no-mint gate was Shor-broken Ristretto. Ember chose
   "**B now + A (redesign)**": downgrade the overstated posture comments at once, and route the
   transfer through the ring-clearing apex as a scheduled project, because one weld closes all three
   seams on Poseidon2 [read: DECISION-shielded-redesign §Decision]. The plan then found that "a
   single shielded transfer is *not* a ring/swap" [read: PLAN §0]. The reconciliation found "the
   committed tree the pin binds to does not exist … 'Route through the apex' closes nothing until that
   accumulator exists" [read: DESIGN-shielded-apex-tree-reconciliation, intro]. The on-ramp design
   showed L4 had "no satisfiable instance" [read: on-ramp §0 verdict 3].
6. **Marked as mistakes in the documents:** the PQ-posture comments (#17, "a lie in the tree"
   [read: DECISION TL;DR]); the "~2^185" vs 2^92.7 framing (CLAUDE.md); E8's CG-3 "TAUTOLOGICAL
   self-check — both sides prover-filled" [read: shielded memory]; the deleted "~100-bit security"
   line in blinded-queue §10 [read]; the whole-note swap substrate's five absent relations,
   "active security seams, not documentation niceties" [read: whole-note-swap §What this relation
   does not prove]; the `wasm` stealth-key "SECOND copy of the phrase-hash bug" [read: privacy.rs
   header]; the dark-value one-felt join "(birthday ~2^15.5)" [read: dark-value §3.1]; and Mini's
   r18 room intake, which "would replace an honest always-refuse with a dishonest one" [read:
   PRIVATE-ROOMS-DESIGN §0].
7. **The 10-01 consequence for everything after:** no proof system in Mini's admission. "Nothing
   friend-facing needs it: re-execution, access control, **client-side encryption + commit-reveal**,
   and conservation cover every property in PLACE/PAY/MUD/PRIVACY/NOCK" [read: memory
   `project-no-proof-system-in-mini-admission.md`]. That decision closes every Bread route that hid
   state from the host (sovereign+STARK, encrypted turns with validity proofs, selective-disclosure
   STARKs). In nanodregg the only remaining shape that hides from the host is **client sealing**
   [inferred].
8. **The minidregg blinding precedent was honest about its limits.** "The Host holds each cell's
   blinding (it must, to serve openings), so the salts hide uncovered entries from OTHER READERS,
   not from the operator" [read: hiding.rs header]. Its custody was never fully closed:
   the opcode-13 "codec-child call returning a cell's blinding hands the blinding key to the Lean
   child", "Key custody (pause item 1)" [read: RECOVERY-20261016.md item 15; CODEC-SHAPES-LOG:110].
   "The separate blinding-ratchet work … does not hide values from the Host holding the blinding"
   [read: PRIVACY-OBJECT-ARCHITECTURE §3E].

---

## 3. What per-cell blinding would mean in nanodregg, concretely

**What the Host sees today** [read unless marked]:
- **Every cell's bytes.** A cell is `{kind, discipline, slots : ascending (Nat × ByteArray)}`. The
  kernel header says "What the bytes mean … is not the kernel's business" (Kernel/Cell.lean). The
  receivers read owner, package, laws and state from slots (`objectCell`: `slotPackage`,
  `slotOwner`, `lawSlots`, `state`; Kernel/Receive/Derive.lean).
- **Every event.** A Turn carries the call's bytes as its `event`, signature included
  (K2(f), KERNEL-14). The log is permanent, and `log` serves "the signed calls from the height"
  (PROTOCOL-12). A `write`'s edits therefore sit in plaintext in signed call bytes forever.
- **Every read envelope's window and every member's reads.** Each `log`/`read` request carries
  `(world, member, grant, from, notBefore, validUntil, key, signature)`. The Host checks it in
  arrival order inside `admitBatch` (HOST-11, PROTOCOL-12/27/29), so it learns who read from which
  height and when. `read` serves pages of the WHOLE newest base (PROTOCOL-14 A, HOST-15), never one
  cell.
- **Every follower sees what the Host sees.** Each friend runs their own `host follow` over the
  whole log (CLIENT-12), gated only by an observe/follow grant (PROTOCOL-3, KERNEL-20). Balances are
  included: "no privacy: declared absent" (ledger.md).
- **Refusals leave no record** (HOST-8: "The Host keeps no record of refusals"). That is privacy
  only by accident: a refused write's plaintext reached the Host's memory anyway [inferred].
- The network sees ssh: friends reach the box through CLIENT-12 option B (forced-command
  `nd-attach`) [read: client.md CLIENT-12; ASSEMBLY §0]. The Store key is integrity-only: "It does
  NOT protect against anyone who can write STORE" (HOST-16).

**If a cell's content were blinded** (client sealing, the only shape §2.7 leaves) [inferred, from
the cited sources]:
- *Bytes the Host stops seeing:* the plaintext of the **blinded state slots** only. It cannot be
  every slot: owner, package and law slots, the grant slots and value cells are read by the kernel
  and the receivers (`ownerAuthority`, `lawsOf`, `Kernel.Value` reads denomination, balance and
  floor). The plaintext must also leave the **event**: the client seals before signing, so the
  signed call carries ciphertext. Otherwise the log leaks what the cell hides.
- *Bytes the Host still sees:* cell ids, kinds, the writer's key and principal, heights, the
  slot-key layout, ciphertext lengths (pad to buckets, as PRIVATE-CELL's 64-byte blocks do), the
  grant graph, every read envelope, and timing. That is the same residual list PRIVATE-CELL names
  [read: PRIVATE-CELL "The operator still sees"].
- *What the cell root commits to:* the **ciphertext**. KERNEL-30's leaf is
  `E.hash domLeaf (kind byte ‖ cellBytes)` over the slots as stored, so a randomized AEAD envelope
  makes the leaf hiding with no trie change. KERNEL-23(b) anticipated "a leaf commits a commitment
  instead of a digest" for hiding [read]. With sealing that becomes unnecessary: the digest of a
  nonce-bearing ciphertext is already a hiding commitment. A commitment to *plaintext* (a salted
  leaf, minidregg style) would serve only hiding from members while the Host holds plaintext, which
  §4(e1) rejects.
- *What a read envelope answers:* unchanged, because envelopes gate whole-log/whole-base access by
  grant. "Read refused" for members becomes "read yields ciphertext", which is PROTOCOL-3's option
  (b) verbatim: "confidentiality is by encryption only (sealed leaves, private-room ciphertext)"
  [read]. Rows J5/K10/KH would be restated as decryption rows.
- *What a law can judge — the tension:* a law runs inside `receive` on the Host and inside every
  follower's `rederive` (PROTOCOL-4). `write` hands the judge `old` and `new` state. `law` runs the
  laws in force on `.relaw`, and then (KERNEL-27, the **second judge**) runs the ADDED laws on the
  same `stateOf cell` as `.adopt laws'`. `invoke` runs the package's method on the state (Derive.lean
  `write`/`law`/`invokeRun`). Over blinded state the second judge reads ciphertext. KERNEL-27's own
  motivating law is quorum, whose adopt arm "checks that the state's proposal names exactly the
  incoming ids", and it can only work if the proposal sits in a **clear** slot. A method can never
  run on a blinded state: the Host cannot compute `new`. So blinding needs a split: laws and methods
  read clear slots only, blinded slots are opaque to every judge, and an invariant over blinded
  content is enforced by nobody. Honest clients can only *detect* a violation after decrypting.
  PRIVACY-OBJECT-ARCHITECTURE states it: "A kernel-visible envelope/version check cannot prove that
  an authorized writer never deliberately disclosed plaintext; state the honest-client encryption
  obligation precisely" [read: §4 Decision B]. C2's fact 2 states the follower half: "For a law that
  reads blinded state, a keyless follower cannot `rederive` … its consent weakens to structure plus
  pins" [read: ASSEMBLY §1 C2].
- *What carry and export carry:* ciphertext, verbatim. `Carried = {trie, allowance, height,
  journal}` binds the trie by root (KERNEL-29, `carry_inj`). Ids are names (KERNEL-40). So nothing
  re-encrypts at a carry, and a key rotation is never a carry. AAD that binds the World origin would
  break at a carry, because the origin changes. The AAD must bind the **lineage's first origin**
  (KERNEL-40's namespace) plus cell id, slot and key epoch [inferred].
- *Who holds the key:* depends on the shape (§4).

---

## 4. The options

Cost key: **K** = a kernel theorem changes statement or gains a premise. **new** = a new theorem.
Rows marked "none" were checked against C2's fact 1, "Ciphertext as opaque slot bytes needs zero
change to `pinOf`, `Cell.weight`, discipline or the journal" [read].

### (a) No blinding; the Host sees everything — stated as the threat model
- *Custody:* none. The operator and every follow-granted member see every byte. ssh hides it from the
  network. A member who must not see a cell must not hold a follow grant (PROTOCOL-3 (a)).
- *Proof cost:* zero theorems. Text changes: PROTOCOL-3's status moves from "declared absence" to a
  ruled non-goal with a trigger. Delete KERNEL-23's forward promise ("the same structure later serves
  per-cell hiding"), because a forward promise is a no-op kept for later (CLAUDE.md). Keep J5/K10/KH
  as whole-log gating rows.
- *Honest reading:* this is the CapTP analysis's answer, "the federation IS your trusted vat" [read].
  It is also what nanodregg is today.

### (b) Member-held keys in the member's custody; the Host stores ciphertext; content laws only client-side
Two granularities. **(b1) per cell:** a key per cell, the D8/C2 shape. **(b2) per object or room,
with epochs:** the PRIVATE-CELL shape, a fresh epoch key drawn by the founder's client and wrapped to
members in a keys cell. I recommend (b2). Per-cell keys multiply wraps and rotations by the number of
cells, and audiences are per object [inferred].
- *Custody:* a new secret in nd's custody. Where it lives is the real question. CLIENT-8: "no process
  that parses log bytes can read the seed" [read]. The decrypting process parses log bytes, so the
  blinding key **must not be derived from the seed inside a parsing process**. Minidregg derived it
  from the seed (`DREGG.CLIENT.BLIND/v1`), which in nanodregg would put seed-equivalent material in
  the parser [inferred]. Choices: a separate record (`ws/blind`, CLIENT-15's one custody read and
  CLIENT-19's directory chain), or a custody step that decrypts and returns plaintext (custody
  becomes a parser of hostile AEAD frames). A **hosted** member (Hermes) has no offline. Its key sits
  on the operator's box, "Option 1 by another name" (CLIENT-13 [read]), so (b) **cannot hide a hosted
  resident's content from the operator** [inferred]. The observer record (CLIENT-22/23) signs
  envelopes only and would hold no blinding key; a sealed observer then follows ciphertext [inferred].
- *Proof cost:*
  - Trie, fold, carry: none. `slot_inclusion_sound`, `live_inclusion_sound`, `head_read_sound`,
    `prove_verifies`, `fold_reaches_host`, `chain_binds`, `carry_inj`, `fold_world_weight`,
    `admit_canon` and the journal theorems (KERNEL-41 (a′)) are all byte-generic over slots.
  - Fits: `Cell.Fits` / `leaf_decode_cellFit` (KERNEL-34, CODEC-4) are unchanged in statement, but
    sealing overhead (nonce, tag, padding) is charged against `slotsPerCellMax` = 1024 slots and the
    slot byte bound, which changes the weight rows (KERNEL-32 charges bytes) [read: Bounds.lean].
  - **new (LANG): `judge_blind`.** Every occasion's judge (birth, write, relaw, adopt, invoke) is
    invariant under any change to blinded slots. It is the twin of KERNEL-40's `check_origin_blind`.
    Without it a law that reads a blinded slot is judging ciphertext silently, a fail-open of the
    `minted-gating-defaults-to-silence` class. KERNEL-27's second judge is exactly where this bites:
    the adopt arm must be proved blind or refused on blinded objects.
  - **new (KERNEL/LANG): `invoke` on an object with blinded state refuses by name** (e.g.
    `blindedState`): methods compute `new`, and the Host cannot.
  - **new (LEDGER): value cells carry no blinded slot.** `Kernel.Value` reads three slots and
    `fold_floors_held` / conservation are sums over plaintext. A value cell with a blinded slot is
    refused at birth, and the theorem says no reached World holds one.
  - **K (PROTOCOL):** rows J5/K10/KH change meaning, so PROTOCOL-3's status and `every_op_has_a_row`
    are re-scoped. A decryption row and its plant: the Host moves a ciphertext to another cell or
    slot, and the member's open refuses by name (the AAD binding).
  - **new (CLIENT/CODEC, law 2):** the envelope (AAD composition, padding, the epoch-key wrap
    format) is decided in Lean. C2's corrections apply: "the PRF is `Codec.Hash.mac` (KMAC256) …
    encryption and tag keys are split; `pre` is derived in Lean, never chosen by the caller; the Host
    never holds the key" [read]. A wrap to a member needs a KEM. PRIVATE-CELL used hybrid X25519 +
    ML-KEM-768, which is new primitive code in either language [read; cost inferred].
  - The phone's head read: `deployed_head_read_sound_bytes` (KERNEL-34) is unchanged. It proves the
    ciphertext leaf against the head, and the phone needs the member key to show it [inferred].
- *What it buys:* the operator and non-key followers see ciphertext and metadata. Key holders see
  everything, including past epochs (PRIVATE-CELL's residual).

### (c) Blinding at the transport only (hidden from the network, not the host)
- *Custody:* ssh keys, already present. Every friend's link to the box is ssh (CLIENT-12 B), and the
  local hop is a unix socket.
- *Proof cost:* zero; it exists [inferred]. What (c) would *add* is covering the other places Store
  bytes travel: `host export` artifacts and backups (HOST-28/34) and hbox→cloud copies. That is
  at-rest encryption, which is (d)'s mechanism without (d)'s claim.
- *Honest reading:* (c) is (a) plus a fact already true. It answers Bread's network-privacy line
  (items 3, 17) only for content, not for timing or size; no padding or cover exists in nanodregg.

### (d) A per-World operator-held key (hidden from members and the network, not the operator)
- *Custody:* the operator, beside or replacing HOST-16's Store key, which today is integrity-only and
  by law "Nothing ever derives authority, consent or a member's identity from this key" [read].
- *Proof cost:* the Host decrypts at open, and the kernel is unchanged. But PROTOCOL-4 says "follow
  must re-run the receiver on every logged event", and HOST-7 makes consent `host follow`. If members
  lack the key they cannot fold, so **every member's consent collapses to trusting the Host** (the
  thin case HOST-7a calls a declared absence). If members get the key, it hides from no member
  [inferred]. Hiding from members without encryption is already PROTOCOL-3 (a): withhold the follow
  grant.
- *Honest reading:* (d)'s only real content is confidentiality at rest (a stolen disk, a backup, a
  cloud provider's snapshot). Worth doing for that reason under its true name, if a Store ever sits
  on a disk the operator does not control [inferred].

### (e) What the documents propose that is none of these
- **(e1) Host-held per-cell blinding with salted leaves** (Mini K-NARROW-HIDE + K-HIDE-ROTATE,
  owner-derived, Ember-directed 10-01). It hides uncovered entries from narrowed readers, not from the
  operator. In nanodregg it needs (i) a per-cell `read` (PROTOCOL-14 B, unbuilt, "phone" question)
  and (ii) a `log` that does not hand members the plaintext events. (ii) is PROTOCOL-3 (c), "a
  per-member projection (redacted frames + proofs), which is a proof system … and a second log shape"
  [read]. **So in nanodregg (e1) hides from members only by ending follow-consent.** Not
  recommended [inferred].
- **(e2) Commit–reveal predicates** (K-PRED-HASHEQ). A clear slot holds a full-width commitment, a
  law checks a later reveal, and the Host judges at the reveal. This is the one way a host-judged law
  can involve hidden content, and it composes with (a) or (b). It costs a LANG primitive and its
  theorem [read: k-hasheq.md; composition inferred].
- **(e3) Sovereign self-execution / shielded notes / encrypted turns with validity proofs / FHE /
  MPC / TEE** (Bread items 1, 2, 8, 12). Each needs a proof system or hardware trust in admission.
  They are excluded by the 10-01 decision and by the shielded pool's measured outcome (§2.1–2.3).
- **(e4) Selective-disclosure projection** ("the cell has 10 fields; the executor needs to verify
  only 2 … provide a STARK proof that the unrevealed fields are consistent", governance-fluidity
  §3C [read]). The non-proof version of (e4) is (b)'s clear/blinded slot split, with the clear
  slots doing the work the "revealed" fields did [inferred].

---

## 5. Recommendation for ROOT, with its trigger

**Recommendation.** Rule **(a)** for v1 now, as a decision with a threat model, not an absence. The
Host operator and every follow-granted member see every byte; ssh hides content from the network;
a member is kept out of a World only by holding no follow grant. "Hosted state is visible to its
host" is the answer Bread reached twice (CapTP analysis, privacy audit) and Mini reached once (the
10-01 no-proof decision). Ruling it ends D8's deferral clock honestly. Pre-commit the *design* of
**(b2)**:
- per-object epoch keys, drawn fresh by the founder's client and wrapped to members;
- held in a custody record separate from the seed (CLIENT-8 forbids seed material in the decrypting
  process);
- laws and methods confined to clear slots by a `judge_blind` theorem that covers KERNEL-27's second
  judge;
- `invoke` refused on blinded state, and value cells never blinded;
- ciphertext bound by AAD to the lineage origin, cell, slot and epoch.

Build (b2) when the trigger fires, not before. Do not build host-held per-cell blinding (e1). Name
at-rest encryption separately if a Store ever leaves a disk the operator controls.

**Trigger** (sharper than "something a member would not show the operator"): **the first World in
which a member who is not the operator writes, from a device that member controls, content they would
not show the operator.** Two clarifications [inferred]:
- A hosted Hermes never meets this condition, because its key would live on the operator's box
  (CLIENT-13), so no hosted-resident World fires it.
- THE BAR (two friends + hosted Hermes) fires it as soon as one friend uses the World for anything
  private from Ember. Ask the friends before building THE BAR's rows, not after.

File the trigger as a cv task under ROOT, so the "later" is a tracked obligation.

**Three questions for Ember that no document answers:**
1. **Is the operator a trusted vat?** For nanodregg v1, does a member's content need to be hidden
   from the person running the box, or is "your host sees your World" the product's stated deal
   (CapTP: "You trust your hosting federation as you would trust your vat")? Every option above
   follows from this one sentence.
2. **May a private object have content laws?** Under (b) no Host or follower can enforce any rule
   over blinded content; writers with the key can write anything, and others only detect. Is that
   acceptable for the first private object? The alternative is the hidden-predicate path, which
   needs a proof system (refused 10-01) or commit–reveal at a public moment (e2). PRIVACY-OBJECT-
   ARCHITECTURE §3E asked this and left it open.
3. **Where does a member's blinding key live, and what does losing it cost?** Options: a record
   separate from the seed (CLIENT-13's Option 2 logic), recovery by escrow to a sponsor (minidregg's
   `--escrow-to-sponsor` "lets your sponsor sign as you" [read: PRIVATE-CELL]), or none (lost key =
   lost history). Should a kicked member keep the epochs they already held (PRIVATE-CELL's residual)
   or is revocation expected to reach the past (impossible without the operator re-sealing, which
   makes it option d)?
