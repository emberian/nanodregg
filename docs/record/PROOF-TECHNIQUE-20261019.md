> record copy of redregg/work/PROOF-TECHNIQUE-20261019.md, 2026-10-19; the lane logs stay in redregg

# PROOF TECHNIQUE — what nanodregg's theorem families are, what calculus they are groping toward, and one worked instance (2026-10-19)

Scholar's report for Ember and ROOT. Read-only, no builds. Source tree: hbox `/tank/dregg-build/nanodregg/main`
at `8ad3982` (KERNEL-18's last landing). Every claim is marked **[read]** with a pointer (file, decision
number, or log line) or **[inferred]**. Counts are from `grep` over the tree at that commit and are
approximate to ±3 where a regex could miss a multi-line header.

Ember's sentence (10-19): *"I constantly despair at how primitive the proof techniques we're using are
compared to the program logics and other algebras I used to study."* This document says, concretely,
where that despair is earned, where it is not, and what one lane-day buys.

The short version: the SUBJECT of the theorems is right (they are about `World.admit` itself, never a
model: `Kernel/Proofs/Admit.lean` header [read]; dregg2 stated the same facts about a model and a
refinement square it never closed: `metatheory/Dregg2/Spec/ExecRefinement.lean` "full simulation diagram
OPEN" [read]). The TECHNIQUE is a hand restatement of six or seven moves, each written out again per
field, per trie, per instance. The moves are instances of named calculi. The cheapest one to lift is
the frame rule, and lifting it costs zero premises on the cell side and deletes four twins.

---

## 1. THE INVENTORY

### 1.1 The families, per layer

SIZE.md: 3734 theorems, 170 proof-modules, 0 sorry [read: `SIZE.md`]. By layer (my `grep -c "^theorem"`,
10-19): Kernel/Proofs 897, Lang/Proofs 1060, Codec/Proofs 800, Host/Proofs 281, Protocol/Proofs 212.

| layer / family | count | shape of the statement | recurring premises | what a restatement day touches |
|---|---|---|---|---|
| **Kernel · admission** (`Admit.lean`, 22) | 22 | `World.admit E w t = .ok w' → ⟨fact about t, w, w'⟩` via `admit_ok : ∃ posts, Checked ∧ w' = commit` [read] | none on cell facts; `JournalCanon` on the journal ones (`admit_journaled`, `commit_journalAt`) [read] | every check added to `checkWith` adds a field to `structure Checked` and a `⟨⟩, -,` to ~30 `obtain` patterns [read: `Checked` 13 fields; `checkWith_rows`'s 23-component obtain] |
| **Kernel · frame / monotone** (`Frame.lean`, 28) | 28 | "a slot outside the turn's touches/creates/nullifiers reads as before"; "ROM live stays live"; "spent stays spent" | **none** (since KERNEL-49 amendment 1: `get_insert` premise-free) [read: decisions/kernel.md "KERNEL-49 RULED"; `Frame.lean`] | KERNEL-11 (touches replace pins/legs): `admit_frame`'s premise re-worded; KERNEL-47: every `fold_*` gained a `refuse_*` case [read: K11, K47 "Price"] |
| **Kernel · fold / chain** (`Fold.lean`, 27; `Refuse.lean`, 37) | 64 | `World.fold E w l = .ok w' → P w'` by induction on `l`; `chain_binds`: equal chains ⇒ equal logs ∨ `Collision` | `hE : E.Lawful n` on everything that opens a hash; `Bounded` turns for `TurnBytesInjOn` [read: `chain_binds`, `Lawful.lean`] | KERNEL-47 measured it: `World.fold` named on **149 lines in 35 files**, every one re-typed `List Turn → List Step` [read: K47 "Why not a second fold"] |
| **Kernel · conservation** (`Weight.lean` 20, `Budget.lean` 8, `Value.lean` 43) | 71 | equalities and potentials: `w'.weight + t.logWeight + w'.allowance = w.weight + w.allowance`; `valueSum` unchanged; `< 2^64` kept | `Canon ∧ Slotted ∧ RowsCanon` on anything that sums a trie [read: `admit_conserves`, `fold_conserves`, `fold_budget_lt`] | the rows day: six theorems gained `RowsCanon` (enumerated, discharged at Deployed) [read: K48 "Premise spread (priced)"] |
| **Kernel · the four tries** (`Trie.lean` 111, `TrieMap` 19, `TrieRetain` 14, `TrieOrder` 7) | 151 | exact-map lemmas (`get_insert`, `get_retainAt`), canonicity (`Canon := Routed ∧ WF ∧ Shape`), ADS soundness (`inclusion_sound … ∨ Coll`) | `WF`, `Routed`, `Shape`, `Canon` in the predicted places: insert is free, retain and inclusion take Canon/Routed [read: `Trie.lean` header] | the trie day restated **97** statements with "no cell reader gained a premise" as ROOT's condition 1 [read: KERNEL-LOG 1131–1140; K49 RULED] |
| **Kernel · per-trie World wrappers** (`Cells` 35, `Journal` 53, `JournalHead` 11, `Refusals` 39, `RefusalsHead` 26, `Rows` 31, `RowsHead` 55, `RowsRange` 46, `RowsSep` 12, `RowsComm` 45) | 353 | the SAME five facts per trie: separation of keys, `*Canon` kept by genesis/admit/refuse/fold, `*Ok` kept, head-read soundness, pins bind | `World.Canon` / `JournalCanon` / `RefusalsCanon` / `RowsCanon`, the `*Ok`/`*Fits` bundles, `hE` [read: the four headers; `RefusalsHead.lean` header calls itself "the twin of `JournalHead`"] | each new trie instance re-does the family by hand: KERNEL-41 (journal), 44/47 (refusals), 46/48 (rows) [read] |
| **Kernel · deployed corollaries** (`RootedDeployed` 21, `LedgerDeployed` 1, `RowsRangeDeployed` 1, `CarryRooted` 2) | 25 | `genesis … = .ok g → fold env g l = .ok w → ⟨generic theorem with every premise discharged⟩` | discharges by `deployed_lawful`, `deployed_reach : Canon ∧ CellsFit`, `reach_journalOk` [read: `RootedDeployed.lean` 26–104] | one per generic theorem somebody wants at the phone; written by hand each time |
| **Kernel · receivers** (`Receive` 13, `Audit` 5, `Authority` 13, `Rooted` 29, `Origin` 19, `Carry` 20, `Ledger` 28) | 127 | `receive X w c = .ok t → ⟨what t is⟩`; `receive_congr`: equal pinned view ⇒ equal derivation; `Honest`; `WorldRooted` kept | `Ctx.Lawful`, `hE`, `CarryFits` | KERNEL-24/29/40 each a flag day of the receive signature |
| **Lang · semantics** (`BigStep` 6, `Agree` ?, `Complete` ?, `Derives` 6, `Need` 34, `NeedComplete` 15, `Sound` ?, `Meaning` ?) | ~120 | machine ⟷ reference: `run_bigStep` / `bigStep_run`; `bigStep_deterministic`; sized derivations `Derives … n`; `required_lt_ticks` | typing (`LibTy`, `StateTy`), `checked` | **this family is already a calculus** (a big-step relation, soundness + completeness of the CEK machine, a cost-annotated derivation): the one place nothing is groping [read: the four headers] |
| **Lang · laws** (`Std` 86, `StdTeeth` 59, `StdFits` 51, `Receiver` 41, `LawRun` 9 = 246; ROOT's "247") | ~247 | `Admits lib law rq n o → ⟨post-condition on rq, n, o⟩` where `Admits := ∃ cenv w, BigStep … (.ok (.inj "ok" w))` [read: `Std.lean` 186] | `rq.field "occasion" = some occ`, `IsChange occ`, Nodup labels, `digestOf (bytesOf law) = some law` [read: `bounded_spec`, `judgeOne_quorum_change`] | LANG-19/KERNEL-27 (`.adopt` as a fifth Occasion): every law's bytes changed, "the 85 law theorems keep their statements" [read: decisions/lang.md 1285] |
| **Lang · provenance / liveness** (`Provenance` 61, `CallLive` 47, `PrintWire` 38, `Print` ?) | ~250 | `ValLits P` preserved by `step`/`run`/`force`/`extract`; "refused only for a non-digest field" | `Ctx.Lawful` (LANG-46) | one `*_lits` lemma per value former (`tl_lam … tl_ite`, 10) and per machine phase (6) [read: `Provenance.lean` index] |
| **Codec** (800) | 800 | `Lawful c` / `LawfulOn P c` (put/size/get-of-occurs/occurs-of-get); canonicity `decode b = .ok v ↔ b = bytes v`; per-shape `*Fits` and `*_lawfulOn` | `P` the domain predicate, composed by product/sum/refine/array | one `Fits` + one `lawfulOn` per wire shape (World.lean alone: 66 of them) [read: `Codec/Proofs/World.lean` index] |
| **Host** (281) | 281 | open/seal/backup round trips: `openWith … = .ok ⟨same World, 0 records, no torn tail⟩`; `Kept` bundle of nine invariants | `Kept` (Canon, Slotted, CellsFit, JournalOk, height<2^64, budget, RowsCanon, RowsOk, RefusalsOk, Disjoint) [read: `Host/Proofs/Deployed.lean` 358] | every new World field or trie adds a `Kept` field and a `kept_admit`/`kept_refuse` case |
| **Protocol** (212) | 212 | receipts: `check … = .ok (.committed h td) → journalAt = some (h, td) ∨ Collision`; settle: `final_iff_recorded`; command: `plan_admits` | `JournalCanon`, `RefusalsCanon`, `hE`, the u64 bound on claimed heights | the trie day re-cut the receipt wire (u16 per sibling) [read: K49 RULED] |

### 1.2 The recurring MOVES in the proofs (each named once, then counted)

1. **Fold induction with an invariant.** 48 theorems named `fold_*` in Kernel/Proofs; 16 of them go through
   the one scheme `fold_keeps (P := …)` (`Refuse.lean` 167 [read]); ~32 are written out by hand because
   their conclusion is not `P w'` but a RELATION to the start state (`fold_value : valueSum w' = valueSum w`,
   `fold_conserves : w'.weight + Σ log + w'.allowance = w.weight + w.allowance`, `fold_nullifiers` over
   indices, `fold_refused_retains` with a height bound) [read: `grep -c "^theorem fold_"`; `fold_value`,
   `fold_conserves` bodies].
2. **"Preserved through genesis / admit / refuse / fold / carry."** Every invariant is five theorems:
   `genesis_X`, `admit_X`, `refuse_X`, `fold_X`, `carry_X` (and often `receive_genesis_X`). Instances:
   `Canon`, `Slotted`, `CellsFit`, `JournalOk`, `JournalCanon`, `RefusalsOk`, `RefusalsCanon`,
   `RefusalsDisjoint`, `RowsCanon`, `RowsOk`, `WorldRooted`, `RomContent`, `origin` — 13 invariants × ~5
   ≈ 65 theorems of one shape [read: the indexes of Cells/Journal/Refusals/Rows/RowsHead/Rooted/Origin].
3. **A congruence under a pin.** "What a check reads is only the pinned view": `receive_congr`
   (`Receive.lean` 38), `touchCheck_congr` (private, `RowsComm.lean` 692), `check_journal_congr`
   (`Journal.lean` 392), `diverge_congr` (Trie). Four hand statements of locality [read].
4. **A two-order commutation with structural equality of tries.** `admit_comm` (`RowsComm.lean` 853):
   both orders admit; cells and rows read the same at every slot; the head moves additively; and
   `admit_comm_rows` lifts pointwise-equal rows to `=` through `rows_ext` (canonical + separated keys)
   [read]. 1030 lines for one theorem, including its own private frame lemmas (`commit_cell_frame`,
   `commitTrie_out`, `view_row_out`) that duplicate `Frame.lean`'s [read: lines 639, 840, 101].
5. **Canonicity as an iff.** `decode_eq_ok_iff : decode b = .ok v ↔ b = bytes v` from `Lawful c`
   (`Codec/Proofs/Stream.lean` 98); `world_decode_iff` at Deployed under `CodecFits`; `journalOk_of_fits` /
   `journalFits_of_ok`, `refusalsOk_of_fits` / `refusalsFits_of_ok`, `rowsHeaded_iff`: a Prop invariant
   shown equal to the Bool predicate a decoder checks [read].
6. **A deployed corollary with the premise discharged.** `deployed_*` (25) = generic theorem applied at
   `deployed_lawful`, `deployed_reach`, `reach_journalOk`. Hand-written per theorem [read: `RootedDeployed`].
7. **A tooth per theorem.** Each statement ships a refutation of its own premise or a plant: `under_needs_shape`,
   `inclusion_needs_routed`, `refusalDigest_wraps`, `plant_refusals_unseparated`, `range_rows_erase_not_exact`,
   `Env.Lawful.refutable`, Lang's `Teeth.lean` ("the soundness theorems cannot see a machine that computes
   the WRONG value of the right type") [read]. This move is correct and is the one the memories demanded
   (`feedback-prove-the-floor-false`); it is not a calculus, it is hygiene, and it should survive any migration.
8. **The `∨ Collision` escape.** Every hash-opening statement ends in `∨ Collision E.hash` / `∨ Coll S` with an
   exhibited pair, never an axiom (K1: "collision as an explicit disjunct") [read: DECISIONS.md K1; `Fold.lean` 19].

The restatement days measured by the KERNEL lanes: K47 149 lines/35 files (fold over Step), K49 97
statements (trie compression), K41 ~15 theorems gained `JournalCanon` (journal as a second trie instance)
and the rejected K41 (a) would have put `Canon` on ~150 cell readers [read: `minted-price-premises-not-only-cost.md`;
K41 PORTED "Premise spread"]. The lesson the lanes drew — "price premises, not hashes" — is the lesson a
calculus is for: a frame rule stated ONCE is priced once.

---

## 2. WHAT THEY ARE GROPING TOWARD

For each: the logic; which moves above it names; which theorems become instances of ONE scheme; how many
hand restatements it subsumes; the premise it takes once.

### 2.1 Separation logic: footprints, the frame rule, locality  (moves 1-pt, 3, 4)

- **Pins are footprints.** A Turn names every cell it reads or writes exactly once (`Touch := {cell, seen, act}`,
  KERNEL-11 [read]); a row touch names its slot; a range read names a prefix. The footprint of `t` is a
  function of `t` alone. `admit_pins`/`stale_refused` say the precondition is "the footprint reads what the
  signer saw" — a *points-to* assertion `c ↦ seen` for every touch [read: `Admit.lean` 127, 136].
- **`admit_frame` IS the frame rule** for the cells trie, with the footprint written out inline as two
  hypotheses (`∀ x ∈ t.touches, x.cell = c → x.act = .keep` and `c ∉ createdIds t`) [read: `Frame.lean`].
  `refuse_frame` is the frame rule for a transition with empty cell footprint [read: `Refuse.lean` 23].
- **`touchCheck_congr`, `receive_congr`, `check_journal_congr` are LOCALITY** (a check's verdict depends
  only on its footprint). Frame + locality are the two halves of the small-footprint semantics that make
  the separation-logic frame rule sound; nanodregg proves both, separately, per check, per trie.
- **`admit_comm` is the disjoint-footprint commutation**, the standard corollary (two local actions with
  separated footprints commute). Its 11-conjunct `RowsCommFoot` is the disjointness of two footprints spelled
  out field by field [read: `RowsComm.lean` 661]. The additive heads (`count + insN t₁ + insN t₂`) are a
  *counting permission* / PCM resource in CSL terms: the head is shared, composed by `+`, with
  `RowsFitTogether` the compatibility (`≤ limit`, `≤ cap`) of the composition [read; this naming is mine].
- **The four tries are a separating conjunction of four roots.** `rootsDigest E root jroot rroot wroot` and
  `rootsDigest_inj` (injective or collision) [read: `Cells.lean` 381]; `refuse_frame` moves one conjunct and
  leaves three; a Turn moves cells+journal+rows and leaves refusals except at a prune height.
- **Instances of one scheme** (`Frame` over `(World, Foot t)`, §3): `admit_frame`, `commitTrie_entry`,
  `commit_cell_frame` (private twin), `commitTrie_out` (private twin), `insertAll_get_of_not_mem`,
  `insertAll_get_nullifier`, `spendAll_get_cell`, `admit_rom`, `fold_rom`, `admit_nullifiers.2`, `admit_live`
  (the contrapositive on live cells), `admit_romContent`, `refuse_entry`/`refuse_live`/`refuse_isSpent`/
  `refuse_journalAt`/`refuse_rows`, `rowStep_get_other`, `view_row_out`, `insertAll_live`, `commit_live`,
  `touchCheck_entry` (RowsHead): **~22 hand statements** [read: the indexes]. The premise it takes once:
  NONE on cells (because `get_insert` is premise-free after K49 amendment 1), `RowsCanon` for the rows
  conjunct (retract is `retainAt`, whose `get_retainAt` is at Canon), `JournalCanon` for the journal conjunct
  (`pruneJournal_get` at Canon) [read: `Rows.lean` 58, `Admit.lean` 185, 230].

### 2.2 A Hoare / weakest-precondition calculus for `admit`  (moves 1, 2, 7)

- `World.admit` is `check` then `commit`; `Checked E w t posts` is literally the strongest precondition
  of `commit` as a 13-field `structure … : Prop` [read: `Admit.lean` 20]. Every `admit_X` theorem is
  `{Checked ∧ P} commit {Q}`; every `fold_X` is the Kleene-star rule; `fold_keeps` is the invariant rule
  stated for unary `P` only.
- **What a Turn's specification would be:** `{ ∀ x ∈ t.touches, x.cell ↦ x.seen ∗ journal(txId) ↦ ∅ ∗
  allowance ≥ charge ∗ … } admit t { touched cells ↦ posts ∗ born ↦ creates ∗ nullifiers ↦ spent ∗
  journal(txId) ↦ (h+1, td) ∗ allowance' = allowance + credit − charge }` — i.e. `Checked` is the pre,
  `commitWith` the post, and every `admit_*` in `Admit.lean`/`Weight.lean`/`Frame.lean` is one conjunct of
  that one triple written as a separate theorem [inferred from the statements].
- **Laws as postconditions.** Lang's `Admits lib law rq n o` is `wp(law)(ok)` written as an existential
  over `BigStep`; `quorum_change`, `bounded_spec`, the 86 `Std` theorems are each `Admits … → post` for one
  law × one occasion, each proved by hand through `Meaning.lean`'s inversion lemmas [read: `Std.lean` 186,
  593]. A `wp : Term → (Data → Prop) → Prop` computed structurally over Core4 (which has `BigStep` and
  `bigStep_deterministic` already, so `wp` is definable as `∀ r, BigStep … r → post r` and the inversion
  lemmas become its structural clauses) would make each law theorem `wp_quorum : wp (quorumLaw …) P ↔ P'`
  — one lemma per TERM FORMER (there are ~10: `tl_lam … tl_ite`'s list) instead of one per law × occasion.
  Subsumes: the inversion half of ~86 Std theorems and the `*_lits` family's structure (Provenance's
  `ValLits P` is `wp` for a value predicate) [inferred; the count of per-law theorems is read].
- **The second judge (KERNEL-27) is sequential composition:** the laws in force judge `relaw laws'`, then
  each ADDED law judges `adopt laws'` on the unchanged state; a two-step spec `{P} judge₁ {Q} · {Q} judge₂ {R}`
  [read: K27 and its LANG-4 amendment].
- Premise taken once: the typing premise `StateTy`/`LibTy` (already what `step_sound` takes) [read: `Sound.lean` 147].

### 2.3 Refinement / simulation: what "discharged at Deployed" is  (move 6)

- There is NO Sim ⊑ Deployed. GATES-14 deleted the toy; `kernel-sim` runs `World.admit` under
  `Deployed.params` (CODEC's digest, cSHAKE, Ed25519) and `countingEnv E` is `E` with `dbgTrace "#"` on
  trie-domain hashes, returning `E.hash` unchanged [read: `Kernel/Sim/Main.lean`, `Deployed.lean`, `Gen.lean` 244].
  The Sim is an *instrumented instance*, not a second model; KERNEL-36: "the trie hash rows are INSTRUMENTS".
- What the pattern actually is: **parametricity over `Env`.** Generic theorems quantify over every
  `E` with `hE : E.Lawful n` (five fields, `Lawful.lean` [read]); `deployed_lawful : env.Lawful 32` is the
  one instance; `deployed_*` are *applications*, not simulation lemmas. KERNEL-37 did the right thing by
  bundling the loose `hsz/hb/hcb/ht` premises into one structure (KERNEL-LOG 551: "7× hsz, 6× hb, 5× hcb,
  4× ht replaced by hE" [read]).
- The REAL refinements in the tree, each proved as an equality or an iff, none named as a refinement:
  (a) spec ⊑ impl inside the kernel: `World.admit_eq_admitImpl` (`@[csimp]`, `World.lean`) — the specified
  transition (commit recomputes rows) equals the compiled one (rows committed once) [read];
  (b) Host ⊑ Kernel: `step_submit` ("the step is `Receive.submit`'s", K33), `fold_foldlM`, `open_sound`
  ("the opened World is the fold of a record list whose encoding is literally the bytes") [read: `Open.lean`
  header]; the Host's `Kept` bundle IS the reach invariant written as a structure [read: `Deployed.lean` 358];
  (c) follower ⊑ writer: `audit_ok : audit X w l = .ok w' ↔ fold … ∧ Honest X w l` and `fold_det`,
  `fold_reaches_host` [read: `Audit.lean` 113];
  (d) Lang: `run_bigStep` + `bigStep_run` — machine ≡ reference, the one textbook-shaped refinement [read].
- Which theorems become simulation lemmas if the Host's loop is given a `Refines` relation: `step_submit`,
  `absorbStep_step`, `step_persists_folds`, `openWith_world`, `sealed_opens`, `genesis_reopens`,
  `import_reopens`, `openWith_backup` (the backup theorem is "every instant of a live Store refines the
  fold") — ~10 Host/Protocol theorems whose statement is today "equals the fold of …" [read: the indexes].
  Premise once: `Kept` (the Host already has it).

### 2.4 The algebra of receipts and pins  (moves 5, 8)

- **The trie is an authenticated dictionary and the receipt is an ADS proof** (Miller et al., "Authenticated
  data structures, generically"): `Trie.Spec K V D` is the generic structure, `inclusion_sound`/`exclusion_sound`
  the generic soundness, `prove_includes`/`prove_excludes` completeness [read: `Trie.lean` header]. Nanodregg
  HAS the generic lemma. The duplication is one level up: `slot_inclusion_sound`, `journal_inclusion_sound`,
  `refusal_inclusion_sound` + `_exclusion_sound` + `prove_verifies/absent` + `head_*_read/absent` +
  `deployed_*` = the same eight theorems × three tries (`RefusalsHead` names itself the twin of `JournalHead`)
  ≈ **24 + 21 deployed forms** of ONE `HeadRead` scheme over a structure `{spec, root projection,
  body-injectivity, Fits}` [read: the three headers and `RootedDeployed`]. Premise once: `hE`, the trie's
  `Canon`, and the per-instance `leafBody_inj` (which differs: journal needs `0 < n`, refusals do not; cells
  need `cellBytes_injOn Fits`) [read: JournalHead/RefusalsHead headers].
- **Roots form a commutative monoid action.** `build_toList`, `trie_ext`, `rows_ext`, `retainAt_eq_build`:
  a canonical trie is a function of its ENTRY SET, so `root (insert k v t)` is an action of the free
  commutative monoid on `K × V` and `admit_comm_trie` is its commutativity on disjoint keys [read:
  `TrieRetain.lean` header, `RowsSep.lean` 772]. The "proof wire" is algebraically a Merkle path in that
  action's quotient; the receipt is a membership witness for one generator. The pin (`pinOf`, `rowPin`,
  `rangePin`) is a content address: the SAME monoid at depth 0 [read: `World.lean` 304, 487, 537].
- `carry_inj` (origin commits to name, nonce, roots, allowance, height, journal listing ∨ collision) and
  `genesis_inj` are injectivity of a product of commitments: again `rootsDigest_inj`'s shape [read: `Carry.lean` 131].

### 2.5 Rely-guarantee for the follower  (moves 1, 6)

- `Honest X w l` is a RELY: "every logged step is `receive`/`judge` of its own event on the World where
  it arrived" [read: `Audit.lean` 37]. `audit_ok` says the follower's verdict is the fold under that rely.
  `chain_binds`/`fold_head_binds`/`fold_reaches_host` are the GUARANTEE: one signed `(steps, chain)`
  fixes the log ∨ collision [read: `Fold.lean` header; K47 amendment 1 replaced height by steps].
- **PROTOCOL-46 "the Host hints, follow settles"** makes the client's rely on the Host EMPTY: a settlement
  is `Settle.ofReceipt` over the member's own follow's World; the Host's status byte only drives the loop
  [read: decisions/protocol.md 1307]. So the environment for the client is the log, and the rely is
  `Honest` plus the window arithmetic (`journalForgets`), never the Host's word. `final_iff_recorded`,
  `final_recorded`, `declined_open`, `settle_final_never_admits` are the guarantee at the attempt store
  [read: `Settle.lean` header].
- Premise once: `Honest` (already one definition). What is missing is the composition rule: today
  `audit_rooted` (Rooted), `deployed_audit_rooted`, `derived_once` and `submit_once` each re-prove "under
  `Honest`, the writer's per-step fact lifts to the follower" by hand; an `honest_keeps (P)` scheme (the
  rely-guarantee invariant rule, `fold_keeps` under a rely) subsumes ~6 [read: the indexes; the count is mine].

### 2.6 Refusals: by name, totally  (move 7, law 7)

- `Reject D` has 79 constructors [read: SIZE "refusal constructors 79"]; `Reject.name_injective`,
  `Refusal.name_injective`, `ParseRefusal.name_injective`, `codeName_code` make "refused by name" a total
  injection into strings/codes [read]. The ordering is the `Except` monad's first-error monoid over the
  check list in `checkWith` (14 checks in one fixed order [read: `World.lean` `checkWith`]); the verdict is the
  FIRST failing check, and `stale_named`'s `pre ++ x :: post` + "every `pre` touch passes" premise is the
  proof obligation of exactly that monoid [read: `Admit.lean` 149].
- The brief's "join-semilattice" is a weaker fit than the real structure: refusals are not joined, they are
  ordered lexicographically by check position. What would be a calculus: a per-check characterization
  scheme `check_i w t = .error r ↔ P_i r` (today: `touchCheck_stale`, `checkSteps_refuses`,
  `refusedBounds_window`, `checkRefusal_facts`, `pinOf_forged` — 5 of 14 checks characterized [read]) and
  ONE generic "first failure" lemma, from which `stale_named`, `replay_named`, `admit_refusedFinal`,
  `refuse_window`, `admitted_elsewhere_refused` (5 hand proofs) are instances. Premise once: the check
  order, as data (it already is: `checkWith`'s `do` block).
- KERNEL-47's amendment 5 (early `outsideWindow` is not final, late is) shows the refusal set is NOT flat:
  finality is a second predicate over names (`Verdict`, `judge : admitted | recorded | declined`) [read].
  That predicate is the thing to make total and prove by name, not a lattice.

### 2.7 Parametricity / naturality for the codec  (move 5)

- `Lawful c` is a partial isomorphism between `α` and the byte strings `{bytes v}`; `decode_eq_ok_iff`
  is its canonicity; `LawfulOn P c` restricts the domain; `product_lawfulOn`, `sum_lawful`, `refine_lawful`,
  `array_lawful`, `tagged_lawful` are the functorial closure [read: `Stream.lean`, `Raw.lean` 15, `Rows.lean` 29].
  This is already an algebra of codecs (a category with products, sums, refinement as pullback).
- What is hand-restated: the DOMAIN predicates. `Codec/Proofs/World.lean` holds 20 `*Fits` predicates and
  20 `*_lawfulOn` theorems, one per wire shape (`CellsFits`, `JournalTrieFits`, `RefusalsTrieFits`,
  `RowsTrieFits`, `HeadedWireFits`, `ParentedWireFits`, …) [read: index]. The naturality that would
  subsume them: `LawfulOn (P ∘ f) (c.comap f)` and `LawfulOn (P ×ₚ Q) (c ×ₛ d)`, so that `World.CodecFits`
  is COMPUTED from the field codecs' domains rather than declared and then proved to match. ~20 theorems
  become instances; premise once: each primitive codec's `Lawful` (already proved: `u8_lawful … digest_lawful`).
- The iff `journalOk_of_fits`/`journalFits_of_ok` (and the refusals, rows twins) is the Bool↔Prop reflection
  of a domain predicate; a `Decidable`-style `Reflects` lemma per `*Fits` is the scheme (3 instances today).

---

## 3. THE WORKED EXAMPLE: the frame rule

### 3.1 Before (hand), as landed

`Kernel/Proofs/Frame.lean` [read, verbatim statements]:

```lean
theorem admit_frame {E : Env D} {w w' : World D} {t : Turn D} {c : D}
    (h : World.admit E w t = .ok w') (hl : ∀ x ∈ t.touches, x.cell = c → x.act = .keep)
    (hc : c ∉ createdIds t) : w'.entry E c = w.entry E c := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  have hcp : c ∉ (bornEntries t).map Prod.fst := by … (6 lines)
  have hpc : c ∉ (posts.map Post.pair).map Prod.fst := by … (5 lines, via posts_touched)
  unfold World.entry
  rw [show (commit E w t posts).trie = commitTrie E w t posts from rfl, commitTrie_entry hpc hcp]

theorem admit_rom … (h : World.admit E w t = .ok w') (hlive : w.live E c = some cell)
    (hrom : cell.discipline = .rom) : w'.live E c = some cell := by
  obtain ⟨posts, hk, _⟩ := admit_ok h
  have hf := admit_frame h (rom_keep hk hlive hrom) (live_not_created hk hlive)
  unfold World.live at hlive ⊢; rw [hf]; exact hlive

theorem admit_nullifiers … (h : World.admit E w t = .ok w') :
    (∀ n ∈ t.nullifiers, w.isSpent E n = false ∧ w'.isSpent E n = true) ∧
      ∀ n, w.isSpent E n = true → w'.isSpent E n = true := by
  obtain ⟨_, hk, rfl⟩ := admit_ok h
  refine ⟨fun n hn => ⟨?_, spendAll_spent_of_mem hn⟩, fun n hn => commitTrie_spent hn⟩ …
```

and the private twins in `Kernel/Proofs/RowsComm.lean` [read]:

```lean
private theorem commit_cell_frame … (hk : Checked E w t posts)
    (hnw : ∀ x ∈ t.touches, x.cell = c → x.act = .keep) (hnb : c ∉ createdIds t) :
    (commit E w t posts).trie.get (trieSpec E) (.cell c) = w.trie.get (trieSpec E) (.cell c)
private theorem commitTrie_out … (h : ¬(c ∈ (posts.map Post.pair).map Prod.fst ∨ c ∈ createdIds t)) :
    (commitTrie E w' t posts).get (trieSpec E) (.cell c) = w'.trie.get (trieSpec E) (.cell c)
```

Premise count of the three corollaries, before: `admit_frame` 0 invariants (h, two footprint facts);
`admit_rom` 0; `admit_nullifiers` 0. `rowStep_get_other` (`Rows.lean` 450) takes `Trie.Canon (rowSpec E) 0 r`
[read]; `commit_journalAt` (`Admit.lean` 230) takes `JournalCanon` [read].

### 3.2 After: the footprint and the frame, as one scheme

Pseudo-Lean, typed against the real signatures (`Touch`, `Act`, `Turn.creates/nullifiers/rows`, `Slot`,
`RowSlot`, `World.entry/isSpent/journalAt/rowAt` are the landed names). It would live in a proof-module
(§4.1 says why), e.g. `Kernel/Proofs/Logic/Frame.lean`.

```lean
/-- The cell-trie footprint of a turn, as a Prop (no computable list: GATES-2 C3 forbids a non-Prop
    def in a proof-module, and a Prop is all the rule needs). -/
inductive CellFoot (t : Turn D) : Slot D → Prop
  | touched {x} (hx : x ∈ t.touches) (hne : x.act ≠ .keep) : CellFoot t (.cell x.cell)
  | born {c} (hc : c ∈ createdIds t) : CellFoot t (.cell c)
  | spent {n} (hn : n ∈ t.nullifiers) : CellFoot t (.nullifier n)

/-- The rows-trie footprint: the touched slots and the heads of touched rows (the head is a shared
    counter; it is INSIDE the footprint, which is why `admit_comm` needs the additive clause). -/
inductive RowFoot (t : Turn D) : RowSlot D → Prop
  | slot {x} (hx : x ∈ t.rows) : RowFoot t x.slot
  | head {x key} (hx : x ∈ t.rows) (hs : x.slot = .row key) : RowFoot t (.head key.parent key.rel)
  | dropped {x} (hx : x ∈ t.touches) (hr : x.act = .retire) {rel} : RowFoot t (.head x.cell rel)

/-- Frame: what is outside the footprint is unchanged. Stated per trie, with each conjunct carrying
    ONLY the premise its trie's get-lemma needs. -/
structure Frame (E : Env D) (w w' : World D) (t : Turn D) : Prop where
  cells   : ∀ s, ¬ CellFoot t s → w'.trie.get (trieSpec E) s = w.trie.get (trieSpec E) s
  rows    : w.RowsCanon E → ∀ s, ¬ RowFoot t s → w'.rowAt E s = w.rowAt E s
  journal : w.JournalCanon E → ∀ k, k ≠ t.txId →
              w'.journalAt E k = if (w.height + 1) % Bounds.windowMax = 0
                                 then (w.journalAt E k).filter (kept (w.height + 1)) else w.journalAt E k
  origin  : w'.origin = w.origin

/-- THE frame rule. One proof: `admit_ok`, then `commitTrie_entry` / the rows fold / `commit_journalAt`. -/
theorem admit_Frame {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') : Frame E w w' t

/-- Locality, the other half (today: touchCheck_congr, receive_congr, check_journal_congr). -/
theorem check_local {E : Env D} {w w' : World D} {t : Turn D}
    (hc : ∀ s, CellFoot t s ∨ (∃ x ∈ t.touches, s = .cell x.cell) → w'.trie.get (trieSpec E) s = w.trie.get (trieSpec E) s)
    (hr : ∀ s, RowFoot t s → w'.rowAt E s = w.rowAt E s) (hj : w'.journalAt E t.txId = w.journalAt E t.txId)
    (hh : w'.height = w.height ∧ w'.allowance = w.allowance ∧ w'.steps = w.steps ∧ w'.origin = w.origin) :
    check E w' t = check E w t
```

### 3.3 The three corollaries as instances (one line each)

```lean
theorem admit_frame (h : World.admit E w t = .ok w')
    (hl : ∀ x ∈ t.touches, x.cell = c → x.act = .keep) (hc : c ∉ createdIds t) :
    w'.entry E c = w.entry E c :=
  congrArg (fun o => o.bind Leaf.entry?) ((admit_Frame h).cells (.cell c) (not_cellFoot_of hl hc))

theorem admit_rom (h : World.admit E w t = .ok w') (hlive : w.live E c = some cell) (hrom : cell.discipline = .rom) :
    w'.live E c = some cell := by
  obtain ⟨_, hk, _⟩ := admit_ok h
  simpa [World.live, hlive] using admit_frame h (rom_keep hk hlive hrom) (live_not_created hk hlive)

theorem admit_nullifiers_mono (h : World.admit E w t = .ok w') (n : D) (hn : w.isSpent E n = true) :
    w'.isSpent E n = true := by
  by_cases hm : n ∈ t.nullifiers
  · exact spendAll_spent_of_mem hm ▸ … -- inside the footprint: the write itself (unchanged lemma)
  · simpa [World.isSpent] using (admit_Frame h).cells (.nullifier n) (fun f => by cases f <;> contradiction) ▸ hn
```

`admit_rom` keeps its text and its two helper lemmas (`rom_keep`, `live_not_created` are about `Checked`,
not about the frame). `commit_cell_frame` and `commitTrie_out` are deleted (they are `(admit_Frame …).cells`
at `.cell c`); `refuse_frame` becomes `refuse_Frame : Frame E w w' ⟨empty footprint⟩` or stays as is (its
proof is `rfl`-shaped, 4 lines; no gain). `rowStep_get_other` stays as the per-step lemma the `rows`
conjunct is proved from; `view_row_out` (RowsComm, private) is deleted.

### 3.4 The premise count, honestly

| | premises before | premises after | note |
|---|---|---|---|
| `admit_Frame` (the rule) | — | **0** on `.cells`, `.origin`; `RowsCanon` INSIDE `.rows`; `JournalCanon` INSIDE `.journal` | the premises are hypotheses of the conjunct, not of the theorem: a reader of `.cells` discharges nothing |
| `admit_frame` | 0 (h, hl, hc) | 0 | unchanged statement; proof 14 lines → 1 |
| `admit_rom` | 0 | 0 | unchanged statement; proof 4 → 2 |
| `admit_nullifiers` (.2) | 0 | 0 | unchanged statement |
| `rowStep_get_other` / a new `admit_row_other` | `Canon (rowSpec E) 0 r` | `RowsCanon` (same fact at the World) | no new premise; today there is NO admit-level rows frame by name (I find `rowStep_get_other` and the private `view_row_out`; `foldRows_pins` carries the composition inline) [read: Rows/RowsHead/RowsComm/RowsSep indexes] |
| `commit_journalAt` | `JournalCanon` | `JournalCanon` | unchanged; it IS `.journal` |

**Does the frame rule need `Canon`?** No. **`RowsCanon`?** Only in the rows conjunct, where the landed
lemma already takes it (retract is `retainAt`; `get_retainAt` is stated at Canon [read: `TrieRetain.lean` 281]).
**`Slotted`?** No. The one place I would have expected a premise and found none: `get_insert` on the
path-compressed trie, which K49 amendment 1 made premise-free by giving `getAt` the `rep` check that
`insAt` splits on ("a pure-bits `getAt` would have put `Routed` on ~60 Frame/Value/Weight uses" [read:
KERNEL-LOG 1174; K49 RULED "Amendment 1"]). That decision is what makes the frame rule free; it was taken
for exactly this reason by a lane counting premises, and it is the strongest evidence in the tree that the
lanes already think in frames and only lack the word.

**Is the rule stated as ONE theorem a premise-spread hazard?** It would be, if `Frame` were a flat
conjunction taking `RowsCanon ∧ JournalCanon` at the top: every cell reader applying it would inherit
both (the K41 (a) mistake, one level up). The structure-with-local-hypotheses shape above is the fix, and
the vacuity reader's check is: "no field of `Frame` whose subject is the cells trie takes a premise". If
a lane cannot keep that, state three theorems (`admit_cellFrame`, `admit_rowFrame`, `admit_journalFrame`)
and no structure; the subsumption count is the same.

**Discharged at Deployed?** Nothing new to discharge: `deployed_reach` already gives `Canon ∧ CellsFit`;
`RowsCanon` and `JournalCanon` are in `Kept` and in `reach_journalOk`/`fold_rowsCanon` [read].

**What `admit_comm` becomes.** Its 1030 lines reduce by the ~200 that re-prove frame and locality
(`commit_cell_frame`, `commitTrie_out`, `touchCheck_congr`, `mapEx_congr`, `view_row_out`, `commitTrie_base`,
`commitTrie_nul`, `insertAll_get_base`, `spendAll_get_nul`, ~9 private lemmas [read: index]) and its
statement gains a reading: `RowsCommFoot t₁ t₂ ↔ ∀ s, ¬(CellFoot t₁ s ∧ CellFoot t₂ s) ∧ ∀ s, ¬(RowFoot t₁ s ∧
RowFoot t₂ s) outside heads`. The additive-head clause stays: it is the PCM, not the frame.

**The tooth of the frame rule** (law 6, "prove the floor false"): (i) `cellFoot_needs_born`: with `born`
dropped from `CellFoot`, `admit_Frame.cells` is false (a born cell reads `some` after, `none` before) — a
concrete turn by `decide`; (ii) `rowFoot_needs_head`: with `head` dropped, `.rows` is false (an insert
bumps the head's count); (iii) the sim plant from K23 (g) ("leave a touched path unrehashed ⇒ follower/Host
root red") is the runtime twin and already exists [read: K23 (g)]. (i) and (ii) are the refutable floors;
`admit_Frame` is then satisfiable (`two_rains`'s turns) and refutable and not provable with a smaller footprint.

---

## 4. THE MIGRATION

### 4.1 What to build first, and where it may live

1. **`Kernel/Proofs/Logic/Frame.lean`** (§3): `CellFoot`, `RowFoot`, `Frame`, `admit_Frame`, `refuse_Frame`,
   `check_local`, the two teeth; delete the four twins; re-prove the ~22 instances as one-liners. **1–2
   lane-days** (one lane, serial: the file is a hub).
   - It MUST be a proof-module: GATES-2 C3 refuses a def-module exporting a `Prop`-typed definition
     ("statements belong in a Proofs module") and C4 refuses a def-module importing a proof-module
     [read: `gates/closure.py` 8–20, 76–80]. So the footprint is a `Prop` (`inductive … : Slot D → Prop`),
     not a `List (Slot D)`; a computable footprint would have to live in `Kernel/World.lean` and be deployed
     code (C9), which nothing needs.
   - Law 8's hub metric (`max dependents of a non-foundation module`, 213 today, no ceiling [read: SIZE.md])
     rises for whichever proof modules import it; a proof-only edit to it rebuilds every importer (GATES-2
     measured this on v4.30.0 [read]). The scheme file must therefore be small and stable: statements and
     the rule, no instance corollaries (those stay where they are).
2. **`Kernel/Proofs/Logic/Fold.lean`:** `fold_keeps` already exists; add `fold_hom (f) : (∀ w t w', admit → f w' = f w) → (refuse → f w' = f w) → f (fold) = f w` and `fold_potential (f cost) : f w' + cost t = f w` → the sum form. Instances: `fold_value`, `fold_floors_held`, `fold_origin`, `fold_romContent`, `fold_conserves`, `fold_charge`, `fold_height`/`fold_steps` (potentials with cost 1) — **8–10 hand inductions**, ~1 lane-day.
3. **`Kernel/Proofs/Logic/HeadRead.lean`:** a structure `HeadInstance E := {S : Trie.Spec, rootOf : World D → D, Fits, body_inj : …}` and ONE `head_read_sound`/`head_absent_sound`/`prove_verifies`/`prove_absent`/`deployed_*` family over it; `Cells`, `JournalHead`, `RefusalsHead` become three instances (the per-instance premise differs: `0 < n` for the journal; `RefusalLeaf.Fits` for refusals — those stay in the instance record). **~45 theorems → 8 + 3 instances; 2 lane-days**; the vacuity reader reads the eight statements once and the three records.
4. **Codec `Fits` naturality** (§2.7): `LawfulOn.comap`, `LawfulOn.prod`, and `World.CodecFits` computed. ~20 theorems; 2 lane-days; CODEC's lane.
5. **Lang `wp`** (§2.2): a design question for Ember first (§5 Q3); 3–5 lane-days if yes.
6. **Named refinements** (§2.3): a `Refines` record for Host ⊑ Kernel over `Kept`; the existing equalities
   become its fields. 1 lane-day; mostly renaming, which is why it goes last.

### 4.2 How the vacuity readers read instance theorems

The readers' job (law 6: "identity carriers, `P → P`, empty premises" [read: CHARTER]) does not change
on the instances, because their STATEMENTS do not change (§3.4: every corollary keeps its text). What
changes is the proof length, which the reader never judged. Two new obligations:

- read the SCHEME's statement once, with the K41 question: "which field takes which premise, and does any
  cell-side field take a trie-wide one?" (the structure-with-local-hypotheses shape makes this a per-field
  read);
- read the scheme's teeth (the `*_needs_*` floors) as the satisfiable-and-refutable check that the memories
  demand of every new predicate (`feedback-prove-the-floor-false`): a `Frame` with a footprint too large is
  trivially true (`CellFoot := fun _ => True` makes `.cells` vacuous). The tooth `cellFoot_needs_born` is
  what stops that; the reader asks for it by name.

A HOLD a reader could raise, and should: "the instance's one-line proof is `(admit_Frame h).cells …`;
show me that `CellFoot` is not larger than the inline hypotheses were." That is `not_cellFoot_of` in §3.3,
an iff between the old inline footprint and the new inductive one — write it, and the reader reads it.

### 4.3 What the gates say

- **SIZE** (law 12): `theorems` counts every `theorem` including private ones (`gates/size.py` 134 counts
  `tree.THEOREM_KINDS` over all decls [read]); the frame day is +~6 (scheme, locality, two teeth, the iff)
  −4 twins −~9 RowsComm privates: a net FALL, which needs no `SIZE:` line. `Lean proof-modules` +1 needs one.
  `max dependents` may rise; it has no ceiling; the message says why.
- **WASTE**: untouched. No deployed definition changes; the frame rule is a proof-side fact about
  `commitTrie`. The hash rows (`cells-touched-per-turn 1.0` etc.) are instruments over the same code
  [read: `gates/waste.tsv`].
- **Axiom census** (GATES-4): unchanged. The schemes are proved by the same tactics over the same
  definitions; no `native_decide`, no new allow row [read: `gates/axioms-allow.tsv` has 4 rows, all Hosting/Lang].
- **Closure** C3/C4: satisfied by the proof-module placement (§4.1); C9 (deployed def-module must not
  import tooling) irrelevant.
- **The landing clone's gate run** judges the candidate by the parent's gates and its own (GATES-3); a
  frame day that only moves proofs cannot red a sim, a row or a vector.

### 4.4 What NOT to do

- **No Mathlib, no Batteries** (GATES-1, LANG-15 [read]). Every scheme above is `Prop`-structures and
  plain inductions; nothing needs `Finset`, `Iris`, or a separation-logic library. The temptation will be
  to reach for an `iProp`-style framework for §2.1; refuse it — the tree's frame rule is a theorem about
  one concrete transition, not a logic to be instantiated, and a framework is a second World of assertions.
- **No proof system in admission.** Ember's scope call (memory `project-no-proof-system-in-mini-admission`):
  runs are checked by re-execution; the vat dabbles only. None of §2 changes what `admit` CHECKS; the wp
  of §2.2 is a proof-side computation over `BigStep`, never a verifier the kernel runs.
- **No second World, no second fold, no spec model beside `World.admit`.** KERNEL-47 refused a second fold
  for the right reason ("a theorem over a turn-only fold never matches a real run"); the same reason refuses
  an abstract transition system that `admit` would be shown to refine. dregg2 did that and its refinement
  square stayed open while its "real theorems were TOY models" [read: `project-verified-system.md` index
  line; `ExecRefinement.lean` header]. The calculus must be DERIVED over the landed definition (memory
  `feedback-iterate-inside-the-substrate-not-beside-it`), which is what every scheme in §2 is.
- **No computable footprint in deployed code** (§4.1); no `#guard` (law 6); no `partial` (law 4).
- **Do not restate the 246 law theorems before Q3 is answered.** They keep their statements through
  flag days today (LANG-19/K27: "the 85 law theorems keep their statements" [read]); a wp migration that
  changes their text is a restatement day of its own, and it is the one item here that is a design fork
  (CLAUDE.md pause item 4), not a cleanup.

### 4.5 Cost, in lane-days and premises

| item | lane-days | theorems subsumed | premises added to landed statements |
|---|---|---|---|
| Frame + locality (§3) | 1–2 | ~22 (4 deleted) | **0** |
| fold_hom / potential | 1 | ~8–10 | 0 |
| HeadRead instances | 2 | ~45 → 11 | 0 (the per-instance `0 < n` / `Fits` move into the instance record, same strength) |
| Codec Fits naturality | 2 | ~20 | 0; CodecFits becomes computed, so a vacuity read of the composition |
| Rely-guarantee `honest_keeps` | 0.5 | ~6 | 0 |
| First-failure refusal lemma + per-check characterizations | 1.5 | 5 proofs; 9 new per-check iffs | 0 |
| Lang wp (if Q3 = yes) | 3–5 | the inversion half of ~86 | 0 on statements; the `wp` definition is a new Prop reader |
| Named refinement records | 1 | 0 (renames) | 0 |

Total ≈ 12–15 lane-days for everything but the wp; ~100 hand restatements become instances; no landed
cell-reader statement changes; no premise spreads. The restatement-day cost that motivates all of it: K47's
149 lines/35 files and K49's 97 statements were each ONE lane-day of mechanical edits plus a reader; a frame
rule turns the next such day's Frame/Value/Weight/RowsComm share into re-proving one scheme.

---

## 5. THREE QUESTIONS FOR EMBER, AS A PROOF ENGINEER

**Q1 · Which logic should the receivers speak?** Today a receiver's contract is `receive_ok` (eight
conjuncts about the Turn it emits) plus `receive_congr` (locality over the pinned view) [read: `Receive.lean`
38, 120]. The two candidate presentations: (a) a *Hoare triple over the pinned view* — `{ view ⊨ P } receive c
{ t with CellFoot t ⊆ pins c ∧ Q }`, with `receive_congr` the locality lemma of that triple and the laws'
`Admits` its postcondition (§2.2); (b) a *separation-logic spec* where a call carries `c ↦ seen` for every pin
and `receive` is a local action whose frame is everything unpinned (`unpinned` is already the refusal by
name for reading outside the footprint [read: `Call.lean` header]). (a) is cheaper and matches `Checked`;
(b) makes "a derivation depends only on what the signer saw" the rule rather than a theorem. Which do you
want the receivers' theorems stated in — and should `unpinned` be the frame's refusal or stay a receiver fact?

**Q2 · Should Sim ⊑ Deployed be a theorem or a plant?** There is no Sim semantics to refine (§2.3); the
real question is the Host ⊑ Kernel and follower ⊑ writer squares, which today are equalities and iffs
(`step_submit`, `audit_ok`, `open_sound`, `sealed_opens_deployed`) plus runtime checks in the sim (`same`,
`reopened`: four tries' listings and roots compared after every seed [read: `Gen.lean` 1274–1290]). Naming them
as a `Refines` record buys a reader one place to look and buys the gates nothing. The hash-cost side is the
sharper fork: Lang already has a cost calculus (`Derives … n`, `required_lt_ticks` — a theorem that the
counter is the derivation size); the kernel's hash counts are instruments by ruling (KERNEL-36). A
hash-annotated `insAt` would make `hashes-per-touched-cell ≤ ⌈log₂ n⌉ + 2` a THEOREM and the WASTE row its
measurement. Do you want kernel cost in the logic (as Lang's is), or kept as instruments?

**Q3 · Should laws get a `wp`?** `Admits` is an existential over `BigStep`; `bigStep_deterministic` makes
`wp law post := ∀ r, BigStep … r → post r` a function of the term; `Meaning.lean`'s inversion lemmas are
its structural clauses in disguise. A `wp` changes how 246 law theorems are PROVED, not what they say; a
`wp`-calculus (`wp_app`, `wp_case`, `wp_get`, …, one per former) would let a law author state `wp law P` and
discharge it by `simp [wp]` where today each `quorum_*`/`bounded_*`/`allowlist_*` is a hand derivation. The
cost is the one Lang module that then every law proof imports (a hub) and a second notion of "the law
means" beside `Admits` (law 1: delete `Admits` or define it as `wp law (· = ok)`). Is that the logic you
would rather the laws be proved in — and, if yes, is `Admits := wp … ok` the one definition?

---

### Pointers used (all read on hbox `main` at 8ad3982 unless noted)
`CHARTER.md`; `decisions/kernel.md` K7, K11, K23, K27, K33, K41 (+AMENDED, PORTED), K44, K46, K47, K48, K49 (+RULED);
`DECISIONS.md` K1, K2; `decisions/gates.md` GATES-1/2/4; `decisions/lang.md` LANG-15, 1285; `decisions/protocol.md` PROTOCOL-46;
`Kernel/World.lean` (1040–1373), `Kernel/Turn.lean`, `Kernel/Trie.lean`, `Kernel/Bounds.lean`;
`Kernel/Proofs/{Admit,Frame,Fold,Refuse,Refusals,RefusalsHead,Cells,CellsFit,Journal,JournalHead,Weight,Budget,Value,Carry,
Rooted,RootedDeployed,Receive,Audit,Origin,Rows,RowsHead,RowsRange,RowsComm,RowsSep,Trie,TrieMap,TrieRetain,Lawful}.lean`
(headers + theorem indexes; full text of Frame, Rows, RowsSep; statements quoted above);
`Kernel/Sim/{Main,Deployed,Shadow}.lean`, `Kernel/Sim/Gen.lean` 170–260, 1270–1295; `Kernel/Receive/{Call,Audit,Follow}.lean` headers;
`Lang/Proofs/{BigStep,Agree,Complete,Meaning,Canon,Sound,Std,Receiver,Need,NeedComplete,Derives,Provenance,CallLive,LawRun,PrintWire,Teeth,Invoke}.lean` headers/indexes;
`Protocol/Proofs/{Receipt,Settle,Command,Judge}.lean`; `Host/Proofs/{Deployed,Seal,Backup,Open,Loop,Follow}.lean`;
`Codec/Proofs/{Stream,Raw,Deployed,World}.lean`; `gates/{closure.py,census.py,size.py,axioms-allow.tsv,ceilings.tsv,waste.tsv}`; `SIZE.md`.
Local: `~/dev/redregg/work/KERNEL-LOG.md` (350–370, 540–560, 1125–1226); memories `minted-price-premises-not-only-cost`,
`feedback-honest-label-hides-transmutable-mediocrity`, `project-lean-must-be-the-implementation`, `project-statement-audit-campaign`;
`~/dev/breadstuffs/HORIZONLOG.md` 17182–17203; `metatheory/docs/DREGG-CALCULUS.md` §0, `metatheory/CLAIMS.md` §17/§230, `Dregg2/Spec/ExecRefinement.lean` header.
