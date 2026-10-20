> record copy of redregg/work/DECISIONS-20261021.md, 2026-10-21; the lane logs stay in redregg

# DECISIONS — decision cards for Ember's open calls (SCHOLAR-DECISIONS, 2026-10-21)

> **CORRECTION (2026-10-21, Ember, recorded by ROOT-DOCS).** This brief's framing of breadstuffs is wrong and
> out of date: card R2's "breadstuffs = the PoA main line (the only thing with users) + a quarry + a museum" and the summary line that would have written it into both READMEs. Ember: "PoA actually isn't even a real or running thing, so the idea that breadstuffs is
> PoA mainline is hilarious and extremely wrong/out of date … breadstuffs is where our whole system we built
> lives and we've been splintering out into these side projects (mini, nano) for diversity and continued focused
> exploration while the whole breadstuffs system waits there to be either resumed or truly composted into the
> next version of robigalia." Read every PoA / main-line / quarry / museum sentence below against that.

Read-only pass. Nothing built, nothing landed. Tags: **MEASURED** = a command or file:line read this session on
hbox main `/tank/dregg-build/nanodregg/main` (tip be8ee18, GATES-20d) or in `~/dev/redregg/work/`; **READ** = a
document's claim, cited; **ASSUMED** = mine or ROOT's, unverified. "A re-genesis is not a cost" throughout
(CLAUDE.md); a premise added to a landed theorem IS (memory: price premises, not only cost).

Eight cards, then "ALREADY RULED 10-17 (do not re-ask)". Each ends with the one line Ember can give.

---

## CARD 1 · THE CHECKPOINT DEFAULT (pause item 11)

**QUESTION.** Does a Store keep its segment from genesis, or only the segment behind the newest N sealed bases,
and under which NAMED premise does a follower open from a base it did not seal?

**TODAY (MEASURED).**
- A Store is `key | seg.log | index.log | base.world`; `base.world` is THE newest sealed base, replaced atomically
  through `base.tmp` (Host/Store.lean:9, :77). ONE base is kept. seg.log and index.log append from the origin frame
  and are never pruned: zero hits for `retainBases|checkpointed|retention|CheckpointTrusted` in decisions/host.md
  after KERNEL-44 (host.md:1977→end), and `retainBases` exists in NO code file (git grep; only kernel.md:1855
  "proposed 4"). KERNEL-44 Part 1 (refusals) LANDED 38d94e1; Part 2 (the checkpoint rule) is design only.
- Replay at restart is bounded already: open reads one base + at most `tailMax = 2·cadence + frameMax`, cadence =
  `max(1 MiB, base/4)` (Host/Bounds.lean:105-127). The journal is pruned to `journalMax = 3·windowMax = 3072`
  (Kernel/Bounds.lean:41); refusals kept ≤ 3 windows (`keptRefusal`, Kernel/Proofs/Refuse.lean:216). A thin member
  catches up from a served base + tail (PROTOCOL-14 A); `adopt INVITE KEY` takes a sponsor-signed pin (PROTOCOL-42).
- What is still O(history) (KERNEL-44 Part 2, READ; confirmed by code): `host check` (`historyClean` from
  `segmentInitial`, Host/Check.lean:139,157), a backup (`backupOrder` copies whole seg+index; RUNBOOK §4), a NEW
  follower auditing from genesis (`host follow` re-derives every Turn INCLUDING methods — LANG-44's correction: that
  is the unbounded part of replay), and disk.
- Scale today: `worldBytesMax` derived 91,914,346 B (HOST-57); a base at the bound reopens in 56.3 s at load 12–15,
  "reported not gated, needs a quiet box" (PERF-10, STALL-WATCH 00:55Z 10-21). THE BAR = 1000 records.
- Ember's words (10-17 (8), STALL-WATCH:676): refusals recorded; "a state pruning / checkpointing story is wanted
  ('the amount of replay is too damn high') … replay bounded by the sealed base (already: cold catch-up from the
  base) — state what remains unbounded."

**WHAT THE PAUSE ITEM WOULD DROP (READ kernel.md KERNEL-44 Part 2).** Segment bytes before the oldest of
`retainBases` (4) sealed bases; seg.log becomes `seg.<k>.log` per base, each opened by a MAC'd checkpoint frame
`(height, chain, base digest)`; `log` before the retained range refused `checkpointed H`; `host check` verifies from
the oldest retained frame and prints `retained_from=H`; a follower or backup older than that must start from a
served base. The chain still binds the dropped prefix (anyone who archived it can prove it). LOST: a fresh party
re-deriving the prefix from THIS Store. Premise spread: `fold_reaches_host` unchanged in statement; the `deployed_*`
reached-World theorems gain "a base World is reached", discharged on the writer (sealed from its own fold + MAC)
and NOT for a received base → named `CheckpointTrusted`; backup theorems (`openWith_backup/_cut/_restart`) restated
over the file sequence; `historyClean` = "clean from the oldest checkpoint". New refusals by name: `checkpointed H`,
`checkpointCorrupt`, `storeMissing`.

**The conflation to see.** "Replay too damn high" names a NEW follower's cold audit from genesis. Dropping segments
does not fix that: a follower that will not fold from genesis already has the thin path (served base + sponsor pin)
and already trusts the base. Dropping segments buys only DISK and `host check`/backup TIME, and costs the writer's
own Store its audit-from-genesis property. The thin adopt is CheckpointTrusted under another name today (a signed
pin, no fold); NAMING the premise is a correction, not a weakening. The weakening is only the drop.

**OPTIONS.**
- **A · retain from genesis (status quo, written down).** Refuses nothing new. Loses: disk grows per batch for ever;
  `host check`, backup and a from-genesis follower stay O(history). Premises: 0. Nothing to build.
- **B · retain N bases, default 4 (KERNEL-44 as proposed).** Refuses `log` before H, `checkpointCorrupt`,
  `storeMissing`. Loses: fresh-party audit from genesis on every deployed Store unless an archive role keeps the
  prefix (the hosted follower; HOSTING-30 (B) is its trigger). Premises: `CheckpointTrusted` on every open from a
  received base; the backup/historyClean restatements. A flag day (every Store re-geneses; free).
- **C · retain by bytes.** Same mechanism and premises as B with a disk knob; the cut falls at base positions anyway.
  B under another name.
- **D · operator-chosen with a floor; mechanism built; default keep-everything.** `retain` is a Node value rendered by
  Ops.Units (`--check` refuses below a floor of 2 bases by name); default ∞; `CheckpointTrusted` named NOW in every
  follower open from a received base (thin adopt, carry rejoin, a hosted follower's join), with a row planting it
  (a received base whose World is not the fold → the premise is what admits it, visibly). Premises: as B, but the
  drop is OFF by default so every deployed Store keeps its genesis property until an operator chooses otherwise.
- **D′ · D with the drop DEFERRED behind a measured trigger.** Name `CheckpointTrusted` now (cheap, true already);
  build `seg.<k>.log` rotation + the drop only when a deployed Store's seg.log or `host check` time passes a number
  the RUNBOOK states. Today nothing measured says disk hurts (1000 records × ≤ 64 KiB events; World ≤ 92 MB).

**PRIOR ART.** Mini: SQLite keeps the whole log, `durable_checkpoint` keeps the latest two (DURABLE-STORE; READ via
NANO-VS-MINI §3.5); STATE-AT at-reads from the nearest KEPT checkpoint for speed (kept FLAT 15 ms vs 27,853 ms from
genesis at 10k; STALL-WATCH:114) — a performance move, never a retention one. delvetalk: "Nothing forgets, and nothing
can be made to"; `viewAt` rebuilds any past version (DELVETALK-LEARNINGS §3.6). Nano already forgets history by law 1
at a carry ("a checkpoint is a carry made by hand", KERNEL-44).

**ROOT'S LEAN (10-18, READ):** approve the mechanism, retention operator-set in RUNBOOK, default keep-everything,
`CheckpointTrusted` named in every follower's open, a row planting it (= D). **Scholar's amendment:** D′ — the premise
and its row now, the rotation when a number asks for it; the archive role = the hosted follower, stated in OPS.

**THE ONE LINE.** "D′: name `CheckpointTrusted` + its row now; default keep-everything; floor 2 bases; build the
segment drop when a deployed Store's seg.log or `host check` passes a RUNBOOK number; the hosted follower is the
archive." (Or plain "A: keep everything, name the premise" if the mechanism itself is unwanted.)

---

## CARD 2 · BLINDING (per-cell hiding; PRIVACY-DESIGN-BRIEF, 31 KB, read whole)

**QUESTION.** Does nano v1 hide any cell content from the Host, and if not, is "the Host sees every byte" a RULED
threat model with a trigger, or an absence that keeps a deferral clock running?

**TODAY (MEASURED).** No blinding exists: `git grep -i blind` over decisions+Kernel+Lang+Protocol+Host+Hosting hits
only theorem names (`check_origin_blind`) and plant prose. README.md:38 "per-cell hiding is not designed".
decisions/protocol.md PROTOCOL-3 status still reads "DECLARED ABSENCE for v1, tied to the blinding-key custody
question open with Ember". No cv task holds a trigger (`cv task list` grep blind|privacy|seal: 0 of 33).
**But Ember already ruled it** (STALL-WATCH:681, 10-18 04:25Z, the scope call): "the operator is a trusted vat → the
privacy brief's (a) stands for v1 (no blinding; host sees every byte; stated with its threat model; the member-sealing
design (b2) pre-committed behind its trigger)". The ruling is in the log and has not reached the repo.

**THE BRIEF'S OPTIONS (READ §4).** (a) none; threat model stated; 0 theorems; delete KERNEL-23's forward promise.
(b1) per-cell member keys / (b2) per-OBJECT epoch keys wrapped to members (PRIVATE-CELL shape; recommended over b1).
(c) transport only = (a) + ssh, exists. (d) operator-held per-World key = at-rest encryption under its true name;
hides from no member without ending follow-consent. (e1) Mini K-NARROW-HIDE host-held salted leaves: in nano hides
from members ONLY by ending follow-consent → not recommended. (e2) commit–reveal predicates (composes with a/b; a
LANG primitive). (e3) proof systems/FHE/TEE: excluded 10-01. (e4) selective disclosure = (b)'s clear/blinded split.

**WHAT (b2) COSTS IN PREMISES (READ §4(b)).** Trie/fold/carry/journal theorems: none (byte-generic). Fits: unchanged
statements, weight rows move. NEW: LANG `judge_blind` (every occasion's judge, incl. KERNEL-27's second judge,
invariant under blinded slots — without it a law judging ciphertext is a fail-open), `invoke` refused `blindedState`,
LEDGER "value cells carry no blinded slot" at birth + theorem; PROTOCOL re-scopes J5/K10/KH to decryption rows + an
AAD plant; CLIENT/CODEC: envelope, AAD = (lineage origin, cell, slot, epoch), a KEM wrap (X25519 + ML-KEM-768 = new
primitive code in Lean). Custody: a record SEPARATE from the seed (CLIENT-8: no seed material in a process that
parses log bytes; Mini derived it from the seed — not portable).

**WHAT IT BUYS.** Ciphertext to the operator and to non-key followers; metadata, lengths, grant graph, timing stay
visible. NOT for a hosted Hermes (its key sits on the operator's box, CLIENT-13) — THE BAR's resident never benefits.

**THE OPCODE-13 CUSTODY QUESTION (CODEC-SHAPES-LOG, Mini).** "A codec-child call returning a cell's blinding hands
the blinding key to the Lean child." It is a MINIDREGG item; nano has no opcode 13, no per-cell blinding and no
Lean child that parses log bytes with a key. Under (a) it is MOOT for nano; under (b2) the brief's rule answers it
(the key never enters a parsing process). Minidregg is FINISH-ONLY: close it there as "not ported".

**THREE QUESTIONS THE BRIEF ASKED EMBER.** Q1 (is the operator a trusted vat?) — ANSWERED 10-18: yes. Q2 (may a
private object have content laws? under (b) no judge can enforce one) and Q3 (where the key lives; what losing it
costs; does revocation reach the past?) — only due when the trigger fires; put them IN the trigger task.

**THE TRIGGER (READ §5):** the first World in which a member who is not the operator writes, from a device that
member controls, content they would not show the operator. Ask the friends before THE BAR's rows, not after.

**PRIOR ART.** Bread reached "hosted cells are cleartext to their executor" twice (CapTP analysis, AUDIT-privacy);
Mini once (the 10-01 no-proof decision). The shielded pool never held value.

**ROOT'S LEAN.** Close as RULED (a): one decision entry (PROTOCOL-3 status → "ruled non-goal, threat model stated,
trigger filed", or a PROTOCOL-5x entry), README:38 reworded, KERNEL-23's forward promise deleted, ONE cv task holding
the (b2) design pointer + trigger + Q2/Q3. Nothing built. (e1) never ported.

**THE ONE LINE.** "(a) ruled and written: PROTOCOL-3 status, README, KERNEL-23's promise; the (b2) trigger + Q2/Q3
filed as one cv task; opcode-13 custody closed as not-ported."

---

## CARD 3 · NANO-VS-MINI / THE REPOS DECISION (NANO-VS-MINI-20261017.md, 35 KB, read whole; NANO-VS-BREADSTUFFS §5)

**QUESTION.** Where does minidregg's spec role end, is breadstuffs declared PoA-main-line + quarry + museum in
writing, and do the decision-bearing records in `~/dev/redregg/work/` move into the nanodregg repo?

**WHAT THE PAPER ASKED (READ §0, §6).** (1) Is nano going well? (2) are the semantics aligned? (3) what is the real
difference? (4) should nano become a component inside Mini? Answers: yes at the part it chose (kernel + skeleton,
not the product); aligned at the core, diverged on purpose in the language (call-by-value, no activities/reflection,
monomorphic) and in carry (state only, never history); ~10× in scope; NO — only libraries come out cleanly.
Recommendation: (c) now → (a): Mini = spec, nano grows to cover it, then Mini's product moves onto nano's kernel.
Flip triggers: (i) THE BAR passes on a quiet box over sockets with two friends, one REMOTE over ssh, + a hosted
Hermes doing model-backed work; (ii) one real Mini `.obend` app runs on nano's core without a heap machine.

**ANSWERED BY EVENTS SINCE (MEASURED from STALL-WATCH / the continuation).**
- Mini FINISH-ONLY ruled 10-17; burst5 torn down 10-18; Mini main 334316df; Mini open cv tasks 429 → 137.
- Trigger (ii), the language question: CappedTally ported by hand 10-18 (LANG-45: one reply 33 steps / 47 ticks,
  nothing exponential; the real loss = the `add` delta → LANG-44 rows + capped sum, landed as the rows day 42c261b);
  CoAuthor ruled (LANG-50: 2,464 chars vs Mini 7,896); the Bell written in the surface by a person and used by a
  resident (LANG-52/58). No heap machine, no activities came back. **(ii) fired for two programs.**
- Trigger (i): HOSTING-27 THE REAL RESIDENT (a Lean exe) landed 10-20; resident rows write the World through
  `nd --stdio` (HOSTING-25, MEASURED inside the grain). ROOT's phrase "runs a real resident under THE BAR" is
  **ASSUMED-BY-ROOT**: THE BAR is NOT measured on a quiet box (bar.sh v2 PENDING a box, the friends' machines and a
  cache drop; PERF-10's 56.3 s at load is "reported not gated"); no remote friend, no model-backed Hermes (the PIN
  and the KEY). **(i) has not fired.**
- The delvetalk comparison Ember asked for today is DONE in DELVETALK-LEARNINGS.md (10-17) and mostly landed: §4.1
  surface (LANG-50), §4.2 relations (LANG-44 rows day), §4.3 self-description + next-step refusals (PROTOCOL-44/54/58),
  §4.4 receipts + recorded refusals (KERNEL-44/47, PROTOCOL-45), §4.5 forms (surface), §4.7 use row (PROTOCOL-43,
  scripted). Left: §4.6 rules-and-wants (card 8) and delvetalk's "nothing forgets" vs nano's windowed forgetting
  (card 1). Nothing in delvetalk2 overturns (c)→(a).

**WHAT REMAINS FOR EMBER.**
- **R1 · where Mini's spec role ends.** The charter: spec = journey ROWS + SIMULATION + THE BAR + meaningful theorem
  statements. NANO-VS-MINI §4.1–4.2 lists the Mini rows/steps with NO nano row (rooms, documents, chat, seats, fleet,
  the pay rail, sshe2e, Nock, privacy, agreement). Options: (a) Mini is spec for EVERYTHING until nano covers it
  (status quo; Mini's 137 tasks keep a tree alive that nobody develops); (b) Mini is spec for exactly the rows nano's
  `replaces` fields claim + a named short list of product areas Ember wants next (documents? rooms? the pay rail?),
  and the rest of Mini is museum now. Premises: none; this is scope. Lean: (b), because §5.3's caution (2) says
  several `replaces` lists already claim more than their rows exercise — a spec nobody will restate is a museum piece.
- **R2 · breadstuffs in writing** (NANO-VS-BREADSTUFFS §5, READ): breadstuffs = the PoA main line (the only thing with
  users) + a quarry of specs restated by theorem + a museum; "no lane is briefed to port X from breadstuffs"; PoA
  moves when nano runs one real app under THE BAR. Nothing since changes it; the declaration has not been written
  into either repo. Lean: write it (one paragraph in breadstuffs' README + a line in nanodregg's).
- **R3 · one repo or two (ASSUMED-BY-ROOT that Ember wants this decided now).** MEASURED: `redregg/work` = 283 files,
  45 `*-LOG.md`, 1.5 GB (packs; `resume/` 3.7 MB); nanodregg `decisions/` = 17,635 lines in 10 files, 564 commits,
  public AGPL. Options: (a) everything stays in redregg (private operational record; the repo points at it) — the
  repo's decisions cite files a reader of the public repo cannot open; (b) the DECISION-BEARING briefs (NANO-VS-MINI,
  NANO-VS-BREADSTUFFS, PRIVACY-DESIGN-BRIEF, DELVETALK-LEARNINGS, STAND-INS, MINI-CONCEPTS-IN-NANO, this file) move to
  `nanodregg/docs/record/` as dated read-only files; lane logs, STALL-WATCH and packs stay in redregg; (c) all of
  redregg/work into the repo — 1.5 GB of agent chatter in a public tree. Lean: (b) — law 10 says a decision's inputs
  are examined; an input a reader cannot open is not examinable. Caveat: the briefs name hbox paths and agent ids;
  fine for a record.

**PRIOR ART.** Bread → Mini and Mini → nano both left the older tree quietly keeping lanes because nobody said it had
stopped (NANO-VS-BREADSTUFFS §5, measured: 140 breadstuffs commits in September after "reference material").

**ROOT'S LEAN.** (c)→(a) stands with trigger (i) still open; R1 = (b); R2 = write it; R3 = (b).

**THE ONE LINE.** "(c)→(a) stands; Mini is spec only for the rows nano claims plus [documents / rooms / pay: name
them]; breadstuffs declared PoA-main + quarry + museum in both READMEs; decision briefs move to nanodregg
docs/record, lane logs stay in redregg."

---

## CARD 4 · THE CHARTER SCOPE PARAGRAPH

**QUESTION.** What paragraph is owed to CHARTER.md, and in what words?

**TODAY (MEASURED).** Ember's call, STALL-WATCH:681 (10-18 04:25Z): "nanodregg only ever at most DABBLES in proof
systems; it is the semi-trusted vat prototype, 'well along the way'; a dynamical playground / exploration for dregg
semantics starting from single-node." ROOT: "A Scope paragraph for CHARTER.md drafted for Ember's wording; lands as
a root commit when confirmed." CHARTER.md on hbox main contains no "scope" (grep 0; last charter commits b781e1c,
29ab506 touched law 4 and the read-only checkout); the draft is not in redregg/work (grep "semi-trusted vat": only
STALL-WATCH) — it lived in ROOT's pruned context. Drafted fresh below, in the laws' register, to sit between the
opening paragraph and `## Laws`.

**DRAFT.**

> ## Scope (Ember, 2026-10-18)
>
> nanodregg is the semi-trusted-vat prototype: one writer per Store, members who consent by re-execution, an
> operator who sees every byte. It is a dynamical playground for dregg semantics, started from a single node, and
> it is well along the way. Three things are OUT of scope by ruling, not by omission:
>
> 1. **Proof systems.** nanodregg at most dabbles. Admission is re-execution; the proof slot stays empty; no
>    circuit, STARK or accumulator enters the TCB. breadstuffs' lineage holds the proof stack. A proof-system idea
>    enters nano only as a spec restated in `decisions/` with both critiques, behind a named trigger.
> 2. **Hiding from the Host.** The operator is a trusted vat. The Host and every follow-granted member see every
>    byte; ssh hides content from the network; a member is kept out of a World by holding no follow grant
>    (PROTOCOL-3). Member sealing per object is DESIGNED (PRIVACY-DESIGN-BRIEF (b2)) and built only when a member
>    who is not the operator writes, from a device they control, content they would not show the operator.
> 3. **Multi-node agreement.** One writer per Store; followers re-derive (law 1, PROTOCOL-4). An agreement mesh
>    arrives, if ever, as a restated spec behind the trigger "a second writer for one World", never as a port.
>
> A lane briefed to "add a proof", "hide it from the Host" or "replicate the writer" is briefed against this
> paragraph; the brief is wrong, not the charter. The meta-critique below applies here too: a scope chosen to
> avoid a hard part is the smell; this one is chosen because the hard parts it excludes are measured failures of
> the two trees before it (the apex vacuous at BabyBear; Mini's empty proof slot; the agreement mesh with one host).

**ROOT'S LEAN.** Land as a root commit once Ember accepts or edits; the same commit closes PROTOCOL-3's status
(card 2) so the charter and the decision say one thing.

**THE ONE LINE.** "Scope paragraph accepted as drafted [or: with these edits …]; land it with PROTOCOL-3's status."

---

## CARD 5 · THE CUSTODY EXTENSIONS SINCE HOSTING-17 (ratify the bundle)

**QUESTION.** Is the custody fence AS BUILT today (HOSTING-17 RATIFIED 10-17 + everything that touched it since)
still the fence Ember ratified — nothing widened without a name?

**THE FENCE AS BUILT (READ decisions/hosting.md HOSTING-17/20/25/32, client.md CLIENT-26..32, ops.md OPS-15).**
- *Who runs as what.* `nd`: host serve, keybroker + its decider, nd-members, every nd-supervise child (`nd --stdio`,
  `host follow`). `nd-hosted`: grain-launch, the controller, every grain. `nd ∉ group nd-hosted`; a sandbox escape is
  the hosted uid and reads no key, writes no Store (HOSTING-17 §1).
- *Which keys reach where.* Provider key `/etc/nd/keybroker/provider.key` nd 0600, read by keybroker alone; a grain
  gets allowances, never the key. Member seeds: `/srv/nd-members/<l>/members/<id>`, an nd 0700 tree OUTSIDE the
  hosted tree (HOSTING-32); written only by that member's own `nd --stdio` child; hidden from every grain plan. A
  resident's follower Store `/srv/nd-members/<l>/follow/<id>/store` is written only by its `host follow` child; the
  stdio child cannot reach it (write set + `--hide STATE`, planted). Per-follower OBSERVE-ONLY member key held by nd
  (HOSTING-17 §7). Sponsor key = a FILE under the StrictModes chain, the invitation an untrusted argument, never one
  blob (CLIENT-26). Store key integrity-only (HOST-16). No process that parses log bytes holds a seed (CLIENT-8).
- *Who may connect.* A grain: exactly `[BROKER/<g>/broker.sock, MEMBER/<g>/nd.sock]` (`plan_sockets_max` = 2,
  `plan_sockets_own/_disjoint`; grain-launch `foreignPath` 69), both 0660 nd:nd-hosted inside setgid 02710 dirs,
  SO_PEERCRED uid = nd-hosted AND gid, else `peerRefused` (HOSTING-17 §2–3, HOSTING-25). host.sock stays nd-only: the
  less-trusted side never initiates to the writer (HOSTING-20's direction principle). `nd --stdio`: connect =
  [host.sock, its own follow.sock], verbs = World verbs minus rotate/adopt/init, `invite` off-surface, custody
  refuses `noRotation` (CLIENT-24/29). One spawner for every `host` nd starts: `join::confined` →
  `nanodregg_sandbox::command` (CLIENT-26). One fd per connection, `full` at 64, `fds_max` 73, SIGTERM names every
  close (CLIENT-28/30).

**EACH ITEM vs HOSTING-17.**
| item | what it did | verdict |
|---|---|---|
| CLIENT-26 `nd --join` | TOFU → sponsor-signed invitation; key a chain-checked file; ONE spawner shared with nd-supervise; ws/invitation + ws/input 0600 | **NARROWS** |
| CLIENT-27 settlement | custody settles a rotation only on the member's own receipt, never the Host's byte; terminal `absent` deleted; `Envelope.check` at the Host NOT widened | **NARROWS** |
| CLIENT-27 `signIncoming` | while a rotation is ARMED, the precommitted next key may sign READ ENVELOPES (never a call; stdio custody refuses) so a landed rotation can confirm through a Host that answers `unknownKey` | **WIDENS, bounded** — the only new key use in the bundle; the alternative was a lockout with no way out. Ember to see it, not to fear it |
| CLIENT-28 one fd per connection | the fence's resource bound became real (was 410 fds / 204 threads after 200 connections) | **NARROWS** |
| CLIENT-29 nd-members | per-resident member socket from the World; one follower PER resident (a follower is one member's command machine); decider confined read=STORE; no env file, no operator list | **KEEPS** (one more nd-held member key per resident, inside the member tree) |
| CLIENT-30 SIGTERM | every close named; `signal-hook` + `signal-hook-registry` pinned, 2 new UNVERIFIED rows in gates/tcb.tsv | **KEEPS** custody; **WIDENS the TCB by two crates** (named) |
| CLIENT-31 sun_path bound | refuses a root the sockets would not fit; GRAIN_NAME_MAX/SOCK_PATH_MAX emitted | **KEEPS** |
| CLIENT-32 uncertain hint | follow's stderr carried VERBATIM into the attempt store (≤ 512 B; Lean prints only table names) | **KEEPS** |
| OPS-15 hosted follower join | hand-run `sudo -u nd-hosted host join …`; the chain rule is the operator's shell (operator = sponsor; "no custody gain" from a confined store-only join); carry rejoin stays TOFU by design (card 7a) | **KEEPS** |
| HOSTING-20 member socket | a SECOND resident-initiated socket (peer-checked, verb-listed, per resident) | **WIDENS by one surface** — already the 4th point of the ratified bundle |
| HOSTING-25 built as ruled | typed MEMBER root; `rootsOverlap`; isolation test: other resident's sockets ENOENT | **KEEPS** |
| HOSTING-26 ND_RESIDENTS deleted | residents from the World, not an env list | **KEEPS** |
| HOSTING-32 layout | members + follower state leave the hosted tree; stdio child can no longer write its follower's Store or `follow` file | **NARROWS** |

**The red flag that is not one, said plainly.** HOSTING-17 itself widened "who may connect to the broker" from one
uid to one group and narrowed key reach to nd alone; the bundle since has one bounded widening (`signIncoming`) and
one TCB widening (signal-hook). Nothing else widened. **The unexercised fact (BACKLOG §E):** hbox has ONE uid, so the
0660 group peer check (`peerRefused` for another uid) and the grain's `/home` hide have NEVER RUN with a real second
uid; both are proved and planted with a configured other uid. Residue: the member follower's policy still comes from
Rust/unit text, not a Lean plan (cv 01a14df6-0647; BACKLOG says "likely done by HOSTING-32 — CHECK").

**PRIOR ART.** Mini's `mini-keys` split + the consent provider; Sandstorm's per-grain uids (filed: cv 01a14aad-fc83,
needs a box).

**ROOT'S LEAN.** Ratify as built; name the two widenings in the ratification line; a two-uid box (or a SECOND UID on
hbox) is the first thing a box buys.

**THE ONE LINE.** "Custody bundle RATIFIED as built (CLIENT-26..32, OPS-15, HOSTING-25/26/32), noting `signIncoming`
(bounded) and the two signal-hook TCB rows; exercise peerRefused and the /home hide on a second uid when there is one."

---

## CARD 6 · ID-4 — bytes primitives need a cost model (cv 01a14805-3d32)

**QUESTION.** On what unit are `len`, `take`, `drop` charged so that one tick stays O(1) work — and do the two
byte primitives already landed obey it?

**TODAY (MEASURED).** `Prim = add sub mul div mod eq lt le beq cat deq lenLe` (Lang/Term.lean:16-24).
`lawTicks = 100000` (Lang/Law.lean:17); `treeTicksMax = 131072` (Kernel/Bounds.lean:83). LANG-L (DECISIONS.md):
"I am picking the TigerStyle reading because it gives every step O(1) cost, which makes the tick a real work unit;
that is also why the tick bound theorem means anything." LANG-34: THE BAR's tick row = machine ticks / required
steps (a ratio, pinned; THE BAR 1.000 exact after 16f3b9f). `lenLe` is O(1) (LANG-51, a size field).
**But `cat` copies `a.size + b.size ≤ Bounds.bytesMax` bytes for ONE tick (Lang/Eval.lean:114-115) and `beq` compares
up to that for one tick (:111).** With values ≤ `valueBytesMax` = 65,536 (Bounds.lean:29) one tick may be 64 KiB of
memcpy; one law run may do 100,000 × 64 KiB ≈ 6.5 GB of copying inside the writer's admission loop. LANG-L's O(1)
claim is already false for two landed primitives, not only for three unbuilt ones. The cv's trigger ("first package
with a variable-length collection in state") has been half-answered another way: collections are RELATIONS now
(LANG-44 rows), and bounded text goes through `lenLe`; no shipped package slices bytes.

**OPTIONS.**
- **α · per-32-byte-word ticks (the cv's own proposal).** `cost(cat a b) = 1 + ⌈(|a|+|b|)/32⌉`, `beq` the same over
  the shorter, `len = 1`, `take/drop n = 1 + ⌈n/32⌉`. The tick stays a work unit. Premise spread: `run` consumes
  `cost(step)` ticks, so `law_never_stuck`, `invoke_never_stuck`, `Need.requiredOf … N < ticks` (Need.lean:751,
  NeedComplete.lean:162) and LANG-2/18's fuel-independence restate over a cost function (statement change, no new
  premise); LANG-34's row re-pins for byte-heavy programs (counters and the Bell barely move); no kernel theorem;
  ticks are not on the wire, so no re-genesis — a `lang!` only in that a program that fit `lawTicks` may now not.
- **β · a second budget**: `bytesTouched ≤ B` per run beside ticks; tick theorems untouched; a new fault
  `tooManyBytes`. Two meters for one resource is a law-1 smell, and THE BAR's tick row would stop measuring work.
- **γ · status quo extended** (O(1) per prim; bound by valueBytesMax alone). Honest only if 6.5 GB per law run is
  acceptable on the request path (law 5 forbids O(store); this is O(value) × ticks). Refuse.
- **δ · no take/drop**; `len` only, charged 1. Slicing bytes inside a law is a parser inside a law (a smell); wait for
  a program that needs it under α's rule.

**PRIOR ART.** Mini Core4: unbounded `Nat`, "a fuel bound is not a memory bound" (LANG-L's own critique). Word-gas
(32-byte words) is the EVM precedent (ASSUMED, not read this session).

**ROOT'S LEAN.** α, applied NOW to `cat` and `beq` with a plant (a law that cats 64 KiB 100,000 times must be
refused by the budget, not run); `len` at 1 when a package asks; `take/drop` under α when δ's trigger fires. Say the
bound out loud in the decision: today one tick may be 65,536 bytes of work.

**THE ONE LINE.** "α: word ticks; retrofit `cat`/`beq` now with the plant; `len` on first need; `take/drop` wait."

---

## CARD 7 · PROTOCOL-42/43 RESIDUES

### 7a · cv 01a14de7-224a — an invitation to a CARRIED World (rejoin is still TOFU)
**WHAT REMAINS (READ protocol.md PROTOCOL-42 "STILL TOFU"; OPS-15 §6.7).** The carry row's `rejoin`, and any actor first
used after a carry, take the carried World as given: a carried World is made from a FILE (`host export` → `host import
--digest`), not from genesis inputs, so `Invite.accept` (which returns `genesis inputs`, `accept_ok`) cannot derive it.
RUNBOOK §5 records `from HEX` (old origin), `anchor H:C` and the export digest beside the backup. The deployed client
(CLIENT-26) is no longer TOFU; only the post-carry case is.
**THE DESIGN.** `Invite.unsigned` gains the `.inr` arm: the CarryInput (new origin, `from`, `anchor`, the EXPORT
DIGEST) signed by the sponsor; `accept` for `.inr` returns not a World but a checked `(origin, digest)`; the joiner
obtains the base bytes (a served base, PROTOCOL-14 A) and geneses its own Store by `import --digest` — the digest check
that already exists. `host join` for a carried World = `host import` of a served base under a sponsor-signed digest.
**PREMISE SPREAD.** None new. The joiner checks (sponsor key) ∧ (bytes = the signed digest); it does NOT check that
the exported World was the fold of the old one — that premise is the CARRY's own, accepted at OPS-1 ("history is never
carried, only state"). The TOFU on the HOST goes away; what stays is trust in the sponsor, as at genesis. It is the
same shape as card 1's `CheckpointTrusted` (a base received, its history not re-derived) — rule them together.
**TRIGGER.** A real carry on a deployed World with a joiner after it. THE BAR does not need it. Keep OPS-15's
mitigation until then.
**THE ONE LINE.** "7a: design = a sponsor-signed carry digest adopted as `import --digest`; no new premise; build
after THE BAR, together with card 1's named premise."

### 7b · cv 01a14de7-225e — the use count on a real Store
**WHAT REMAINS (READ PROTOCOL-43 critique; STAND-INS C7).** `Protocol.Use.shared` is counted in row `use` over the
rows' attempt-store `committed` list — scripted, so it always reads 4/5 (plant `oneMember` reads 0). The number that
matters is the same count over a REAL Store's committed calls with real residents. STAND-INS C7 (READ, not verified in
code): `use=` already exists in `host check` but not in BAR output (cv 01a14e19-a82f, PERF, "hours").
**THE DESIGN.** Nothing new to decide: `host check` walks every record already; print `USE shared-objects N of M` and
have bar.sh v2 carry it beside THE BAR's numbers. Premise spread: none (`mem_shared`, `shared_self`, `shared_nodup`
already; a reader, no theorem).
**THE ONE LINE.** "7b: no ruling; fold 225e into PERF's bar v2 (print `use=`), owner PERF/OPS."

---

## CARD 8 · RULES-AND-WANTS (Ember ruled WAIT 10-17)

**WHAT IT IS (READ DELVETALK-LEARNINGS §4.6).** delvetalk objects carry `law/rule/want` lines; a rule fires when a
condition becomes true with nobody posting ("need, feed and tend are what make things act on each other"). On the
obend night residents did place tide rules (yue hit `placedPerHand` at her fifth), but the third playtest's measures
were 0 rules and 0 grown verbs written by residents. In nano a rule would be a Turn some principal signs: the
delegated pre-signed grant shape (KERNEL-20), never a host loop. The reader said: defer until §4.7's use measure says
residents ask for it. Ember: WAIT for the use row (10-17 (9)).

**DOES ANYTHING SINCE CHANGE THE WAIT? No — it sharpens it.** The use row exists (PROTOCOL-43 BUILT, 10-18) but it is
scripted, so "wait for the use row" is satisfied by letter and not by meaning; the real condition is the real-Store
`use=` (card 7b, after THE BAR v2). Meanwhile the Bell (LANG-58, HOSTING-31; MEASURED landed 96179fb) met the reaction
need WITHOUT rules: a resident PROCESS polls `pending` (a cursor relation) and answers; exactly-once is a guard on one
relation (LANG-59). That is the evidence that a polling resident covers "when X then Y" for the first real resident,
and delvetalk's own zero-rules measure is the evidence that residents did not ask for more. Premises if built later:
a pre-signed delegated Turn needs a signer for a future state → a grant with a condition, i.e. a new grant kind in
KERNEL-20's chain walk (a premise on `grant_rooted`); not priced here.

**THE ONE LINE.** "WAIT stands; the condition is a real-Store `use=` showing resident-made things used by others AND
a resident asking for a reaction a polling resident cannot do."

---

## ALREADY RULED 10-17 (do not re-ask) — STALL-WATCH:676, resume index line 85

- burst5 TEAR DOWN — done 10-18 (≈ $40.81; left for Ember: the Latitude tag, hbox burst5-seed).
- minidregg FINISH-ONLY (clear the known reds, stop; main 334316df; 137 open tasks remain in its backlog).
- HOSTING-17 custody bundle RATIFIED (62b346d + §7 + the observe-only key + HOSTING-20). Card 5 is the extensions.
- nd-bwrap on hbox KEPT.
- AGPL-3.0 (landed c4d9229 + README 606a31e).
- blinding custody DEFERRED to PRIVACY-DESIGN-BRIEF.md — and on 10-18 04:25Z the scope call ruled (a) for v1; card 2
  is only the write-down.
- ledger credit SITS (no sweep, no decay, no reclaim).
- refusals RECORDED, DoS-bounded (landed: the refusals day 38d94e1, KERNEL-50 refusalsCounted, KERNEL-54 version
  pins) + a pruning/checkpointing story wanted — card 1 is that story's default.
- rules-and-wants WAIT (card 8 confirms).
- Also ruled since and not to re-ask: HOSTING-18 (A); KERNEL-49 (a) path compression; KERNEL-54 (C) version pins;
  KERNEL-55 (B) derived worldBytesMax; PROTOCOL-53 rowbar (a); CLIENT ceiling 2150; the 10-19 "no contraction" word.

## Cross-card notes
- Cards 1 and 7a share one premise (a base received, its history not re-derived). Name it once (`CheckpointTrusted`),
  plant it once, and both the checkpoint default and the carried-World invitation rest on it.
- Cards 2 and 4 are one commit: the scope paragraph and PROTOCOL-3's status say the same sentence.
- Card 6 is the only card where something LANDED is already outside its own law (LANG-L vs `cat`/`beq`); it is the one
  with a defect, not only a default.
- Nothing in these eight needs a box, a key or a friend; the three calls that do (the PIN, the KEY, a BOX, a FRIEND,
  a SECOND UID) are BACKLOG §E and are not re-argued here.
