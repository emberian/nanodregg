> record copy of redregg/work/NANO-VS-BREADSTUFFS-20261018.md, 2026-10-18; the lane logs stay in redregg

# nanodregg vs breadstuffs — scope, scale, lineage, and what to do with the relationship (2026-10-18)

> **CORRECTION (2026-10-21, Ember, recorded by ROOT-DOCS).** This brief's framing of breadstuffs is wrong and
> out of date: its §5 "what breadstuffs should be treated as" (the main line for PoA, a quarry, a museum) and every sentence calling Path of Angels a live product with users. Ember: "PoA actually isn't even a real or running thing, so the idea that breadstuffs is
> PoA mainline is hilarious and extremely wrong/out of date … breadstuffs is where our whole system we built
> lives and we've been splintering out into these side projects (mini, nano) for diversity and continued focused
> exploration while the whole breadstuffs system waits there to be either resumed or truly composted into the
> next version of robigalia." Read every PoA / main-line / quarry / museum sentence below against that.

Reader: Ember and ROOT. Written by a read-only scholar; nothing was built, run, or changed.
Ember's question, verbatim: *"how does nano compare to proper ~/dev/breadstuffs in scope or scale?"*

Tags on every claim: **[read]** = I read it at the pointer; **[measured]** = I ran the command shown (the
command list is in the appendix); **[inferred]** = my conclusion from what I read or measured.
Pointers: `B:` = `/Users/ember/dev/breadstuffs` at main `22fad151e`; `N:` = hbox
`/tank/dregg-build/nanodregg/main` (405 commits, tip `606a31e`); `M:` = minidregg at `2c27b08b` as read
through `redregg/work/NANO-VS-MINI-20261017.md` (not re-read here; that document is built on, not redone);
`mem:` = `~/.claude/projects/-Users-ember-dev-breadstuffs/memory/`; `W:` = `~/dev/redregg/work/`.

---

## 0. The answer in four sentences

1. **Breadstuffs is a five-month, 10,359-commit, ~2.1 M-line-Rust / 1.39 M-line-Lean research city with
   three load-bearing districts and a great deal of sediment**: a verified kernel-as-executor (`Dregg2/Exec`,
   302 `@[export]`s), a Lean-emitted STARK/FRI/circuit stack whose own memory says its soundness is
   "conjectured 130 / proven 51–73 bits, apex vacuous at BabyBear", and one live product (Path of Angels)
   on infra in a separate repo; nanodregg is **two days, 405 commits, 62 K Lean / 12 K Rust**, one kernel,
   six wire operations, 21 conformance rows and a GREEN standing verdict [measured; read].
2. **In scope nano is roughly a twentieth of breadstuffs' Lean and a hundredth-and-a-half of its Rust, and
   covers only breadstuffs' *kernel* district** — World/Turn/admit, a store, a client, a law language, grain
   hosting — with none of the circuits, carriers, shielded pool, lightclients, Pickles, federation, games,
   deos, or the fleet machinery [measured; read N:README, CHARTER].
3. **In discipline the order is reversed**: nano has what breadstuffs never managed in five months — a whole-tree
   standing verdict that is GREEN, zero `sorry` and zero `#guard` by gate, every byte decided in Lean, commit
   gates that refuse, a TCB table, waste ratios that only fall, and re-genesis three times a day without a
   decision memo — because its charter was written *from* breadstuffs' and Mini's measured failures
   [read N:CHARTER laws 1–12; `W:RETRO-20261008.md`; `mem:minted-fail-open-gate-class`].
4. **Lineage: nano is not a branch of breadstuffs and not its kernel-of-the-kernel; it is a fresh root grown
   from the *spec* of Mini, which was itself a fresh root grown beside breadstuffs** — so breadstuffs is
   now a quarry and a museum (designs, carriers, Pickles, PoA product) rather than the main line, and the one
   decision Ember owes is to *say so*, with the trigger spelled out in §5 [inferred, from §1–§4].

---

## 1. What breadstuffs is — read as strata

The repo's git history begins 2026-05-19 with a commit that *imports* a system ("pyana: 22 crates, ~70k LOC,
1000+ tests") [read: `git log --reverse` first commit]. So the lineage is older than the repo by an
unmeasured amount; what is measurable is **152 days, 10,359 commits**, with the commit curve
May 806 → Jun 2,603 → **Jul 5,441** → Aug 1,355 → Sep 140 → Oct 14 [measured]. The last commit on main is
2026-10-01 [measured]. The memory index's "30 dated logs 2025-05→2026-06" are a filename year-typo: the
oldest, `project-architecture-2025-05-23.md`, calls itself "the 2026-05-23 snapshot" [read]. **Breadstuffs is
five months of work, not eighteen; its density, not its age, is what makes it feel like a city** [inferred].

### Stratum 0 — pyana (May 2026): object-capability authorization with ZK proofs
Macaroon/biscuit tokens, a Datalog authorizer, "prove you're authorized without revealing your delegation
chain" [read: first two commit messages]. Renamed dregg 2026-05-28 [read: `mem:project-pyana-renamed-dregg`].
The through-line that survives every later layer was coined here and is still the HORIZONLOG's spine:
**"a turn = the exercise of an attenuable proof-carrying token over conserved state, leaving a receipt"**
[read: `B:HORIZONLOG.md:17203`; `mem:MEMORY.md` header]. What is sediment: the multi-backend circuit
portfolio ("every backend it names is deleted at HEAD") and the ~62 root design docs archived to `docs-old/`
[read: `mem:historical-index`, `mem:project-pyana-renamed-dregg`].

### Stratum 1 — dregg2 / `metatheory/` (from 2026-05-29): Lean IS the implementation
Two decisions made this layer: *"rebuild under, not layer upon"* (Lean-core-first) and, on 2026-06-08,
*"'Lean model + Rust differential' is NOT a verified Lean implementation"* → the node must **call** the Lean
[read: `mem:project-dregg-rebuild-research` via the historical index; `mem:project-lean-must-be-the-implementation`].
The third law followed on 2026-06-11: **zero Rust-authored constraints or AIRs, ever; circuits are emitted
from Lean** [read: `mem:project-lean-authored-air-law`]. The self-description at HEAD: "`execFullForestG`
behind `dregg_exec_full_forest_auth` … is the same definition the theorems are proved about. There is no
Rust executor to keep in sync" [read: `B:metatheory/README.md` fact 1]. Measured shape of the layer today:

| | value | note |
|---|---|---|
| Lean files / lines under `metatheory/` | 2,656 / 1,392,231 | [measured] |
| of which `Dregg2/Circuit/` | 714,474 | 438,030 are `Circuit/Emit/`; two SRS-constant files alone are 98.5 K [measured] |
| `Dregg2/Crypto/` · `Games/` · `Exec/` | 128 K · 114 K (PoA 86.7 K) · 72.7 K | [measured] |
| `theorem`/`lemma` lines | 43,342 | grep; includes emitted modules [measured] |
| `#assert_axioms` / `#assert_compiled` | 24,245 / 2,237 | the credibility mechanism [measured; read `B:docs/reference/lean-assurance.md`] |
| `#guard` lines in `Dregg2/` | **14,399** | against the repo's own GUARD-DISCIPLINE doctrine; a ratchet exists [measured; read `B:CLAUDE.md`] |
| `native_decide` in `Dregg2/` | 3,064 | [measured] |
| `@[export]` C-ABI entries | 302 | the FFI surface the node calls [measured] |
| `sorry` (`grep -nw`) | 629 hits | **unreliable** — AGENTS.md says the grep lies (docstrings); CLAIMS.md says zero open holes [measured; read `B:AGENTS.md`] |
| `turn/src/executor/` | 23 Rust files still present | whether wrappers or a twin I did not read [measured; inferred] |

Load-bearing from this stratum: the kernel-as-executor, the five-guarantee `AssuranceCase`, the `CLAIMS.md`
honesty ledger with its labels (PROVED-axiom-clean / rests-on-§8-primitive / honest-OPEN), and the emit
origin ("the circuit as a first-class Lean object with a proved spec↔satisfiability bridge")
[read: `B:metatheory/CLAIMS.md` §Honesty labels; `mem:project-dregg2-circuit-emit-origin`].
Sediment: the "verified system" campaign of 2026-07-09 — **retracted** ("real theorems about TOY MODELS …
λ=149 … overclaims") [read: `mem:project-verified-system`]; the statement audit of 07-27 ("the arithmetic was
checked against reality; the statements were not; chain-safety + 4 hash-folds VACUOUS") [read:
`mem:project-statement-audit-campaign`].

### Stratum 2 — the proof city (June–August 2026): STARK/FRI, carriers, shielded, lightclients, Pickles, games
This is where 8,000 of the 10,359 commits went [measured: Jun+Jul+Aug]. Per subsystem, state per the index
(alive / frozen / retracted / superseded), with the pointer:

- **STARK / FRI / circuit stack** — *alive but its soundness is not what the headlines said.* "THREE
  non-communicating islands; ε_C is not a leg; bound ≥1 at 2^31 queries; the pair to quote is **conjectured
  130 / proven 51–73 / ceiling 2^123.6**" [read: `mem:project-fri-soundness-reality`]. The apex
  (light-client unfoolability) is `#assert_axioms`-clean but "**vacuous at BabyBear via TWO floors** — hash
  weld vestigial, `CommitSurface`-injective the real terminal one" [read: `mem:project-circuit-soundness-apex`
  index line]. Mini's 10-01 decision quotes exactly this to refuse any proof system in admission
  [read: `mem:project-no-proof-system-in-mini-admission`].
- **Shielded pool / shielded apex** — *Lean side complete, never deployed*: "six wounds became theorems …
  but the pool has NEVER held value and L0's append is prover-written" [read: `mem:project-shielded-apex-campaign`].
- **Carriers (8) / universal fold** — *deployed at HEAD*: all 8 `*BindingFromFold.lean` axiom-clean with a
  Rust tooth each; "the live geometry is 178/239" [read: `mem:project-carrier-deployment-architecture`].
- **Lightclient-STARK / true peers** — *substantially delivered*: 4 chains STARK-ified as Lean-emitted
  AIRs carrying no-forgery; on-chain peer registry [read: `mem:project-lightclient-stark-true-peers`].
- **Pickles in Lean** — *alive, phase A only*: "first independent synthesis … 40/40; wrap VK applied on
  devnet. NOT a `Side_loaded.Proof`" [read: `mem:project-pickles-in-lean-epoch`, index line]. Two Mina SRS
  constant files are 98.5 K of the Lean line count [measured].
- **Twin-deletion** — *campaign closed, count refuted*: "11/11 Rust twins DELETED … THE 11/11 IS REFUTED:
  at least 24 more surviving twins, six diverged" [read: `mem:project-twin-deletion-campaign`]. The
  diagnostic that survives: "a `def` with no `@[export]` is the best predictor there IS a twin"
  [read: `mem:minted-census-from-the-lean-side`].
- **Automatafl** — *shipped as theorem*: clean play + conflict protocol are theorems at n=11; the Rust AIR
  deleted; one real STARK fold verifies the whole turn [read: `mem:project-automatafl-verified-game`].
- **dregg2's three projections** (authority spine / trust law / coinductive soundness, "realize Robigalia,
  layer it like l4v") — *still the stated shape*; "dregg2 bootable is a NON-goal"
  [read: `mem:project-dregg2-three-projections`].
- **The gates** — *local is stricter than GitHub*: of the last 60 `ci.yml` runs "37 CANCELLED, 21 failed,
  0 succeeded"; CI needs ~57× the commit interval; `scripts/local-gates.sh` is the bar [read:
  `mem:project-ci-meaningfulness-audit`; `ls B:scripts/local-gates.sh` measured]. And: "`main` NOT
  branch-protected — every gate reports, none blocks" [read: `mem:minted-fail-open-gate-class`].
- **Fleet / pipeline / census machinery** — *the organizational stratum*: "~10 immortal terminals driving
  ~420 subagents … none of the nine live sessions had ever compacted; they wall" [read:
  `mem:project-fleet-context-ceiling-pathology`]. 313 memory files; HORIZONLOG 21,257 lines, 413 entries
  [measured].

### Stratum 3 — Path of Angels (from 2026-08-03): the one live product
Sentyr's Khovokhi game platform; 84 Lean modules / 60.7 K lines by 08-05 with "0 `sorry`, 0 `#guard`, 1840
theorems"; infra in **`~/dev/dregg-infra`** (exists: `edge/ hbox/ poa/`) [read: `mem:project-path-of-angels-platform`;
measured `ls`]. Today PoA is 86.7 K Lean lines [measured]. The last commit on breadstuffs main is a PoA
galley re-emit on 2026-10-01 [measured]. State: *alive, one validator, with a documented deployed-vs-HEAD
gap* ("the running node predates every PoA module"; the cured class "fresh web on a stale node, zero turns,
`healthy: true`") [read: same memory].

### Stratum 4 — Mini (2026-08-07 → 2026-10-16): a second root beside the city
`~/dev/minidregg` first commit 2026-08-07; 3,844 commits locally, 158 behind main [measured; read
`W:NANO-VS-MINI` §0]. On 2026-09-19 Ember "selected Mini as the New World construction home, with Bread as
reference"; by 09-26 "Bread remains reference material for this cycle" [read: `B:HORIZONLOG.md` entries
SEPTEMBER 19, 26]. Mini's defining decisions: **no proof system in admission** (`witnessed` compiles to
FALSE; runs are checked by re-execution) and *Nock is evaluator #1 in a registry, not the center*
[read: `mem:project-no-proof-system-in-mini-admission`]. Its measured shape at 2c27b08b: 586 K Lean, 292 K
Rust, 167 host opcodes, a 776-module Host closure, 429 open tasks [read: `W:NANO-VS-MINI` §1;
`W:ARCHITECTURE-20261016.md` header]. The 10-08 RETRO's software signals: version counters as the merge
bottleneck, a third of commits regenerated artifacts, two layers beside the kernel, Θ(2ⁿ) encoders found
only when THE BAR's row finally ran, gates whose verdicts depend on who ran them
[read: `W:RETRO-20261008.md` §"Signals that the SOFTWARE needs the architectural rethink"].

### Stratum 5 — the rethink and nano (2026-10-08 → 2026-10-16 → today)
10-08: "we have some major problems with this software right now, and they aren't going to be solved by
sending out subagents" → drain, freeze, RETRO, rewrite the coordination protocols
[read: `mem:project-2026-10-08-drain-and-freeze-for-rethink`]. 10-16: after ARCHITECTURE / CYCLE-TIME /
RECOVERY showed "186 opcodes, ~120 Host verbs, 51 admission ctors, 70 versioned modules, 281 k Rust lines
deciding things, two state machines", Ember: "rip and tear … rebuild whatever shape … go hardcore. ONLY GOOD
CODE"; ROOT's reservation ("rewrite swarms re-accrete; delete toward the design instead") was overruled
[read: `mem:project-2026-10-16-nanodregg-rebuild`].

**What in breadstuffs is still load-bearing, by this reading** [inferred from the above]: the through-line
sentence; the *laws* (Lean is the implementation; circuits emitted from Lean; constructive knowledge); the
emit-origin architecture; the carriers; PoA as a running product; the honesty vocabulary (`CLAIMS.md` labels,
"a STARK proves the TRACE not the GENERATOR", "prove the floor false"). **What is sediment**: the backend
portfolio, the retracted verified-system claims, the 24+ twins, 14,399 `#guard`s, the `headver/` full-tree
copy (2.6 M Rust lines) and `target/` (0.85 M) sitting in the working tree, 1.7 GB of `.git`, 152 commits
whose subject mentions an epoch and 74 a flag day [measured].

---

## 2. What nano is

**Ambition.** "The same end-computing system as minidregg rebuilt from its spec, not ported from its code";
the spec = the journey rows, the deterministic simulation, THE BAR (two friends + hosted Hermes over ssh;
1000 records, write ≤5 s, cold reopen ≤60 s), and the theorem statements that survived review
[read: `N:CHARTER.md` preamble]. Twelve laws, each "a response to a measured minidregg failure" [read:
CHARTER meta-critique]: one of everything; Lean decides, Rust moves bytes; bytes end to end; TigerStyle
bounds + assertions, no `partial`; performance is designed (waste ratios only fall); named theorems never
`#guard`, one tree-wide axiom census; refusals by name; def/proof module split, Host closure ≤150; every
commit builds; decisions examined then re-examined (CRITIQUE + META-CRITIQUE); no twins of minidregg; size
is a ratchet [read: CHARTER laws 1–12].

**What it has** [read: `N:README.md` "What is true today", `N:SIZE.md`, `N:gates/*.tsv`; measured]:
- A kernel: World = one persistent binary Merkle trie of cells *and* nullifiers *and* (KERNEL-41) the
  journal, root committed into the chain every turn; one `World.admit`; receivers as one derivation per
  kind; members with pre-committed rotation; one grant kind rooted at genesis; value with wells, floors,
  credit, escrow; carry = re-genesis from a digest-checked export [read: `decisions/kernel.md` headings
  KERNEL-3..42].
- A codec layer with a canonicity theorem per site, cSHAKE256/KMAC256 in Lean, and **Ed25519 fully in Lean**:
  field, Pratt primality of p and L, curve, group law, ladder, `verify_iff` = RFC 8032, `sign_verifies`,
  "propext/choice/Quot.sound only, no native_decide" [read: `mem:…nanodregg-rebuild` 10-17 ~15:00Z;
  `decisions/codec.md` CODEC-11/18/23; `N:gates/tcb.tsv` row `Codec.Sha512` says SHA-512 itself is trusted by vectors].
- A host: framed log, sealed whole-World base off-loop, fixed MAC'd index (open reads O(1)), crash cuts at
  every byte, named open faults [read: README Layers; `gates/waste.tsv`].
- A protocol: **6 wire operations, 13 call kinds, 59 refusal names**, 21 conformance rows each with a plant
  [read: SIZE.md; `Protocol/Rows.lean` names, measured 21].
- Objective Bend (`Lang/`, 16.7 K lines, the largest layer): monomorphic CBV CEK, laws as terms, checker
  proved equal to the typing relation, reader/printer round trip [read: `W:NANO-VS-MINI` §3.4].
- Hosting (grain lifecycle generated from an edge list; TLS keybroker with canary), a Rust client that
  "decides nothing" (nd 90 lines, nd-supervise 154, library 1,864, generated 1,921), one confinement shape
  per platform [read: SIZE.md; README].
- Gates: ownership, size ratchet, axiom census, refine census, **TCB table** (`gates/tcb.tsv`: every
  trusted-unverified component with its lift condition — lean4 itself, gcc, rustls/ring, the dalek chain,
  bwrap, sandbox-exec), vector immutability, a runs table executed on every landing [read: `N:gates/`].
- **A GREEN standing verdict**: `STANDING 2f5a201d gates=ok build=ok census=ok runs=ok waste=ok(pinned 24)
  unmeasured=0 => GREEN`, first at 10-17 15:24Z, ~45 h after the charter; three times that day
  [read: hbox `nanodregg/logs`; `mem:…nanodregg-rebuild`].

**What it deliberately does not have** [read: `N:README` "What is not true yet"; `W:NANO-VS-MINI` §2;
`mem:project-no-proof-system-in-mini-admission`]: no proof system in admission (re-execution is the check;
the carrier slot is empty — inherited from Mini's 10-01 decision), no circuits, no STARK, no shielding
("per-cell hiding is not designed"; `W:PRIVACY-DESIGN-BRIEF` recommends ruling "the host sees everything" as
v1's threat model), no federation or agreement mesh (one writer per Store; followers re-derive), no
lightclients of foreign chains, no Pickles, no games, no deos, no fleet surface, no Solana pay rail, no
documents/rooms/chat, no deployment, THE BAR unjudged, phones designed but the client not built.

**Where it sits in the strata** [inferred]: nano is **a fresh root, not a branch and not a kernel-of-the-kernel.**
Its spec is Mini's rows, not breadstuffs' theorems; its laws cite Mini's failures and the RETRO, not
`Dregg2`; it imports nothing from either tree (Lean core only, GATES-1); its one law against twins is
phrased against minidregg [read: CHARTER law 11, GATES-1 via `W:NANO-VS-MINI` §6b]. What it *inherits* from
breadstuffs is doctrine, not code: Lean-is-the-implementation (law 2 is breadstuffs' 06-08 pivot restated
with teeth), named-theorems-not-`#guard` (breadstuffs' GUARD-DISCIPLINE, which breadstuffs itself has not
met — 14,399 `#guard`s remain), re-genesis-is-free (breadstuffs' CLAUDE.md doctrine, which breadstuffs
practised with 74 flag-day commits and a decision memo each time) [measured; read `B:CLAUDE.md`].

---

## 3. Scope and scale, side by side

| metric | breadstuffs | minidregg (the middle stratum) | nanodregg | what the number means |
|---|---|---|---|---|
| age in git | 152 days (2026-05-19 →) [measured] | 72 days (08-07 →) [measured] | **2 days** (10-16 18:30 →) [measured] | nano is 1.3 % of breadstuffs' calendar |
| commits | 10,359 [measured] | ~4,000 (3,844 local +158) [measured; read] | 405 (148 + 257) [measured] | per day: 68 · 55 · **203** |
| Lean lines | 1,392,231 in 2,656 files [measured] | 586,348 in 1,625 files [read M] | 62,224 in 289 files [measured; SIZE.md 62,081 / 288 modules] | 22× · 9.4× · 1 |
| Lean lines excluding emitted/generated circuit modules | ≈ 954 K (minus `Circuit/Emit/` 438 K) [measured] | — | 62 K | the proved-and-read corpus is still ~15× nano |
| Rust lines (first-party) | ≈ 2,128,000 (5.65 M raw minus `headver/` 2.61 M, `target/` 0.85 M, `vendor/` 0.06 M) [measured] | 291,827 [read M] | **12,431** [measured; SIZE.md] | 171× · 23× · 1 — the number law 2 was written against |
| crates / modules | ~207 crate dirs with a `Cargo.toml` [measured] | ~25 crates, 776-module Host closure [read M] | 1 workspace (client, sandbox, attach, launcher, devtools); Host closure **71** (ceiling 150) [read SIZE.md] | nano's whole closure is smaller than one breadstuffs subsystem |
| theorems | 43,342 `theorem/lemma` lines [measured] | (Core4 proofs opt-in, not in default build) [read M] | 2,618 by grep; 2,828 per SIZE.md [measured; read] | 15× — but see the `#guard` row |
| `#guard` | **14,399** [measured] | — | **0**, refused by gate [measured; read CHARTER law 6] | breadstuffs' doctrine, nano's practice |
| `sorry` | grep says 629, CLAIMS says 0 open holes; the grep is known to lie [measured; read AGENTS.md] | — | 0, gated [measured] | nano's count is a gate verdict, not a grep |
| axiom hygiene | 24,245 per-theorem `#assert_axioms` [measured] | AxiomCensus with 23 open "census defect" tasks [read M] | one tree-wide census, 1 `native_decide` allow row [read `gates/axioms-allow.tsv`] | "checks every declaration rather than the ones someone remembered" |
| native / C in the TCB | Rust runtime everywhere; `@[export]` 302 [measured] | Rust verifier executable for signatures [read M] | 9 externs, 159 C lines, TCB table of ~50 rows each with a lift condition [read SIZE.md; tcb.tsv] | nano can *list* what it trusts |
| wire surface | hundreds of verbs across node/sdk/deos (not counted) | 167 opcodes [read M] | 6 operations, 13 call kinds, 11–17 verbs [read SIZE.md] | the "one of everything" law, measured |
| acceptance | `scripts/local-gates.sh`; GitHub CI 0/60 green [read mem] | 28 runner rows + ~85 journey steps, judged by exit code [read M] | 21 rows with plants, over sockets, PENDING never PASS [read] | a row that cannot go red is not a row |
| standing verdict over the whole tree | none that I can find; "every gate reports, none blocks" [read `mem:minted-fail-open-gate-class`] | static-gate green mistaken for landed; journeys 1/102 → 24/50 nonpass while main was pushed [read RETRO #3] | **GREEN ×3 on 10-17** [read logs] | the single largest qualitative difference |
| docs | 712 md / 213,821 lines in `docs/`; HORIZONLOG 21,257 lines; 313 memory files [measured] | ~1,100-line ARCHITECTURE reading needed to orient [read W] | README 117 lines; CHARTER 156; `decisions/` 10,477 lines / ~266 decisions each with critique + meta-critique [measured] | nano's record is per-decision, not per-day |
| agents of work | ~10 immortal terminals, ~420 subagents (07-25 census) [read mem] | 125 lanes / 5.6 B tokens in one 2-day window [read RETRO] | 6 opus owners + 27 sonnet scouts + 6 opus assemblies; 22 successions on 10-17; 388 Opus-5.5 + 17 Fable co-author lines [measured; read] | nano spends a comparable swarm on a 20× smaller target |
| flag days | 74 commits say "flag day", 152 "epoch", 5 "re-genesis" [measured] | 66 of 378 commits mention a re-genesis [read RETRO] | every Store re-genesised 3–4× on 10-17; 3 subjects say so [read synthesis; measured] | same doctrine; in nano it costs nothing because nothing is deployed and no counter is global |
| what is deployed | PoA live beta, one validator (`~/dev/dregg-infra`) [read mem] | was deployed on a public node from the 10-01 candidate [read M] | nothing [read README] | breadstuffs is the only one with a user |

**What breadstuffs can do that nano cannot** [read, pointers in §1]: prove a STARK and verify one in a
browser tab (the trustless web portal); emit a circuit from a proved Lean module and byte-pin it; carry a
foreign chain's validity in a Lean-emitted AIR (4 lightclients, true peers); hold a shielded design whose
wounds are theorems (though it never held value); synthesize Pickles step/wrap in Lean (40/40 differential);
run a verified board game end to end; serve a live product with a validator, a galley and a federation
design; speak hybrid ed25519+ML-DSA identity (58 Lean modules mention ML-DSA [measured]); run deos, a
cockpit, a Hermes bridge, Solana/Stripe rails. Breadstuffs *knows* things nano has not learned yet: that a
width bounds the image not the attack, that an apex can be true with an empty premise, that behavioural
evidence cannot see a proof hole, that a falsifier can stop falsifying [read: the `minted-*` memories].

**What nano can do that breadstuffs never managed** [read: `N:README`, SIZE.md, gates; RETRO]: a GREEN
standing verdict over the whole tree, reproduced on demand; zero `#guard` and zero `sorry` as gate facts;
every accept/refuse/digest decided by a Lean definition with a named theorem, the Rust client reduced to a
generated table; commit gates that *refuse* (ownership, size, def/proof split, TCB, vectors, runs); waste
ratios pinned per operation that may only fall; a TCB table that names every unverified thing and its lift
condition; an Ed25519 verifier proved to RFC 8032 rather than carried as an EUF-CMA `Prop`; a decision
record where every choice carries its own critique and meta-critique; re-genesis as a routine commit line.

**Why the second list exists at all** [read: `W:RETRO-20261008.md` §0 and the software signals;
`mem:…drain-and-freeze`; `mem:…nanodregg-rebuild`]: the 10-08 RETRO measured that 26 aged lanes used 62 % of
5.6 B tokens; that a static-gate green was taken as landed while journeys deteriorated at every tip; that
installed copies decayed; that version counters caused 4 of 5 ejections; that a third of commits were
regenerated artifacts; that gate verdicts depended on who ran them. Every nano law is one of those findings
inverted: the size ratchet (against accretion), the one-branch CAS commit with gates run from main's own
copy (against installed-copy decay and branch-sitting), content-addressed tags instead of version counters
(against the v4→v12 merge collisions), rows that are PENDING-never-PASS over real sockets (against the
static-gate-as-landed error), decisions with meta-critique (against "an estimate mistaken for a constraint",
which is also breadstuffs' CLAUDE.md's 07-30 lesson). **Breadstuffs could not have the second list because
its laws were written as doctrine *after* the code existed; nano's were written as gates *before*** [inferred].

---

## 4. Lineage and debt

### 4a. What nano re-derived that breadstuffs (or Mini) already had — and whether each was right

| thing | breadstuffs had | Mini had | nano built | verdict [inferred unless marked] |
|---|---|---|---|---|
| Ed25519 | `Dregg2/Crypto/Ed25519Reduction.lean`: an EUF-CMA **`Prop` carrier** plus the reduction "protocol-break ⇒ EUF-CMA-break"; **no executable verifier** in Lean [read: file header] | a Rust helper executable (`credential-signature-verifier`, also ML-DSA, sshsig) [read M] | pure-Lean RFC 8032 verifier + signer with proved field/curve/group law, Pratt primality, `verify_iff`, no `native_decide` [read CODEC-11/18/23; mem] | **Right, and new.** Nothing in either tree was a verifier that decides admission in Lean. The debt is the reverse: nano has no ML-DSA/hybrid (CLIENT-11 "NOT IMPLEMENTED"); breadstuffs has 58 ML-DSA modules it could lend as *spec* [measured; read M]. |
| Merkle / authenticated map | `Dregg2/Crypto/Merkle.lean`: a **circuit gadget bridge** over abstract Poseidon2 (`merkle_bridge : Satisfies ↔ MerkleMembers`) [read]; `Circuit/IndexedMerkleTree`, `MapMerkleRoot` [measured ls] | an authenticated trie landed late (Store chain, "Trie B2 approved and never started") [read RETRO] | a persistent binary Merkle trie as *the* World map, cells + nullifiers + journal, root in the chain, "the phone's read" proved premise-free [read KERNEL-23/30/41] | **Right.** Breadstuffs' Merkle is a circuit object for a prover; nano's is the state. Different artifact, same name. |
| Codec family | `Exec/CodecRoundtrip.lean`: parse∘encode over a text-ish wire grammar with fuel, "PROVED vs DEFERRED" receipt [read]; PoA `CanonicalCodec` [measured ls] | hand-written frame codecs with global version counters (v4→v12) [read RETRO] | one `StreamCodec` family over `ByteArray`, canonicity as "consumed bytes ARE the encoding", content-addressed tags, refine census [read CODEC-1/2/5/16/28] | **Right.** The breadstuffs codec is a left-inverse theorem; nano's is canonicity + tags, which is what kills version counters. |
| Keccak / cSHAKE / KMAC | breadstuffs Lean hashes are Poseidon2/Blake3/SHA-256 for circuits [read OVERVIEW; ls] | KMAC256 log tags over SQLite [read M] | Keccak-f[1600] + sponge in Lean, checked by FIPS vectors; listed as **trusted-unverified** in `tcb.tsv` [read] | Right to own it; honest to list it. A proof against FIPS 202 is a shared debt neither tree has paid [inferred]. |
| Custody / key split | Cipherclerk; hybrid identity; `secrets/` crate [read mem; ls] | `mini-keys` [read M] | custody records, observer record, keybroker with canary, second system user `nd-hosted` [read HOSTING-17] | Right: nano's custody is cut around "no key byte reaches a process that parses untrusted bytes", a rule Mini stated and breadstuffs did not [read HOSTING-0]. |
| Kernel: cells / turns / admit | `Dregg2/Exec` with four substances, caps as witness-production, `execFullForestG` [read OVERVIEW; README] | `Kernel/World.lean` 2,814 lines + ~57 receivers [read M] | `World.lean` 659 + `Turn.lean` 101 + one `receive` [read M §2] | **Right as a restatement; the loss is explicit.** Nano kept Mini's "no proof in admission"; it dropped breadstuffs' receipt-as-STARK entirely. The through-line sentence still holds minus "proof-carrying" [inferred]. |
| Law language | the DSL / effect VM / Argus IR, emitted to circuits [read OVERVIEW] | Core4 Objective Bend with call-by-need, reflection, activities, quantities [read M §3.4] | monomorphic CBV Objective Bend, laws as terms, no activities/reflection/sharing [read LANG-0..6] | **Unsettled.** NANO-VS-MINI's own verdict: "neither is a strict improvement … LANG-1: 'the kept set is Core4 minus the parts whose proofs scared me'"; DELVETALK names the authoring surface and keyed relations as the missing pieces [read W §3.4; `W:DELVETALK-LEARNINGS` §7]. |
| Gates / census | `#assert_axioms` ×24 K, `local-gates.sh`, GUARD-DISCIPLINE ratchet [measured; read] | AxiomCensus + census-defect tasks [read M] | one census, size ratchet, TCB table, commit judge [read] | Right: breadstuffs invented the vocabulary; nano made it refuse. |

Net [inferred]: **every re-derivation was a different artifact wearing a shared name**, so none was waste by
the greenfield rule ("prefer deleting the old thing to keeping both"); the cost paid was ~2 days of swarm.
The one genuinely open re-derivation is the language.

### 4b. What breadstuffs holds that nano will need when it grows — and the cleanest extraction shape

| asset | where | state | extraction shape [inferred] |
|---|---|---|---|
| **Circuit emit origin** (circuit as a first-class Lean object; `StepInv ↔ satisfied (encode …)`; descriptor IR; fingerprint-bound decoder) | `mem:project-dregg2-circuit-emit-origin`; `B:docs/CIRCUITS-FROM-PROOFS.md`; `Dregg2/Circuit/Argus` 21 K lines [measured] | alive; the architecture held from 05-29 | **spec**, not library. If nano ever fills the empty carrier slot (Mini 10-01: "someone else's carrier behind a stated bound"), the emit *pattern* is the thing to restate; the FRI stack beneath it is below the bar and should not be lifted. |
| **Carriers** (8 deployed `*BindingFromFold.lean`, the THIRD EDGE law) | `mem:project-carrier-deployment-architecture`; `B:docs/WELD-STATE.md` | deployed at HEAD | spec. A carrier is exactly the shape of nano's "trusted-unverified with a lift condition" row made executable. |
| **Pickles synthesis** | `metatheory/Emit*Mina*`, `fixtures/pickles-*` (16 harness dirs) [measured ls] | phase A, 40/40, not a `Side_loaded.Proof` | **library, standalone.** It is Mina-facing, not dregg-facing; it should live in its own repo whatever happens to breadstuffs. |
| **Shielded designs** | `mem:project-shielded-apex-campaign`; `Circuit/Shielded*` [measured ls] | proof complete, never held value | spec, read alongside `W:PRIVACY-DESIGN-BRIEF` (which already recommends commit-reveal / custody over a proof system for nano v1). |
| **PoA / galley product** | `Dregg2/Games/PathOfAngels/` 86.7 K lines; `~/dev/dregg-infra` | **live**, with users, one validator | **the main line for itself.** PoA runs on breadstuffs' node; nothing in nano can host it today (no rooms, no documents, no federation). It stays where it is until nano can run one real app (NANO-VS-MINI's trigger). |
| **Lightclients / true peers**, Solana/Cosmos/Eth bridges | `bridge/`, `cosmos-*`, `eth-lightclient`, `solana-*` crates [measured ls]; `mem:project-lightclient-stark-true-peers` | delivered | nothing for now; spec if nano ever wants a pay rail (Mini's JPAY is also not in nano). |
| **Hybrid identity ed25519+ML-DSA** | `Dregg2/Crypto/MlDsa*`, 58 modules [measured] | shipped; its silent-consumer class is documented | spec for CLIENT-11 when the v0 "Ed25519 only" ruling is revisited. |
| **The honesty instruments** | `CLAIMS.md` labels; `minted-*` memories; GUARD-DISCIPLINE; `check-guard-discipline.py` | alive as doctrine | already extracted — nano's laws 6/7 and the TCB table are these, with teeth. |
| **The agent-coordination record** | HORIZONLOG, 313 memories, RETRO, CYCLE-TIME | the most expensive asset in the tree | keep as museum; its lessons are in `W:` and in nano's working rules. |

### 4c. What in breadstuffs is dead and should be said so [inferred from the index; each pointer is the memory that says it]
- The verified-system campaign's deployed-system claims (λ=149, the extractions, CircuitSound as stated) —
  **retracted** [`mem:project-verified-system`].
- The FRI headline numbers (~112.6 bits, "61 bits") — superseded by the three-islands reading; the only
  honest pair is conjectured 130 / proven 51–73 [`mem:project-fri-soundness-reality`].
- The 11/11 twin-deletion count — refuted; ≥24 twins survive [`mem:project-twin-deletion-campaign`].
- The circuit backend portfolio, the Rust AIRs, `docs-old/`, `old-docs/`, `site-old-scavenge/`,
  `ts-sdk.archived/` [measured ls]; `headver/` (a full copy of the tree, 2.6 M Rust lines) and `target/`
  in the working tree [measured].
- The "DreggNet" review unification and `~/dev/DreggNet` scoping — superseded [`mem:MEMORY.md` index].
- GitHub CI as a bar — 0/60 green; local is the bar [`mem:project-ci-meaningfulness-audit`].
- 14,399 `#guard`s against the tree's own GUARD-DISCIPLINE — not dead code, but a doctrine the tree never
  enforced on itself [measured; read `B:CLAUDE.md`].
- The git `replace` graft on `orb` (a 2026-07-15 "fresh cut") — history that has already been rewritten once
  [measured `git replace -l`].

---

## 5. The architect's view

**The attractor.** The whole thing — pyana, dregg2, the proof city, Mini, nano — is trying to become one
sentence made executable: *a turn is the exercise of an attenuable proof-carrying token over owned state,
leaving a receipt*, with the receipt checkable by someone who holds one root and re-runs nothing
[read `B:HORIZONLOG.md:17203`; `B:docs/OVERVIEW.md` first line]. Breadstuffs attacked that sentence from the
"proof-carrying" end and built a city of circuits around a kernel whose soundness story was never closed;
Mini and nano attack it from the "owned state, leaving a receipt" end, with re-execution as the receipt's
check and the proof slot empty on purpose [read `mem:project-no-proof-system-in-mini-admission`].

**Is nano the right root?** Yes, for the kernel, by the only test that matters here: it is the first tree in
this lineage whose standing verdict is GREEN and whose gates refuse, and its laws are the inverted list of
breadstuffs' and Mini's measured failures rather than aspirations [read §3]. It is *not* yet the right root
for the product (no app has run, THE BAR is unjudged, the language question is open) and it is not a root
for proofs at all; those judgements are NANO-VS-MINI's and I find nothing in breadstuffs that overturns them
[inferred].

**What breadstuffs should be treated as from here.** Three things at once, by district: **the main line for
PoA** (the only thing with users; it stays on breadstuffs' node until nano can run one real application);
**a quarry of specs** for the carrier pattern, the emit origin, hybrid identity, and the shielded/privacy
reasoning — restated into nano by theorem, never copied (nano's law 11 generalized); and **a museum** for the
rest, including the proof city, whose honest state is "conjectured 130 / proven 51–73, apex vacuous at
BabyBear" and whose next owner should be a standalone Pickles repo, not nano [inferred from §1, §4b].

**The one decision, with its trigger.** Declare, in writing, that **breadstuffs is no longer the main line
for the kernel and will receive only PoA-serving and spec-clarifying commits** — the same freeze-to-spec that
NANO-VS-MINI recommends for Mini, applied one stratum down — and name the day the PoA product moves: **when
nano runs one real application end to end under THE BAR, judged on a quiet box with a remote friend over
ssh and a hosted Hermes** (NANO-VS-MINI's flip trigger), PoA is re-expressed as nano packages and
re-genesised onto a nano node, and breadstuffs becomes archive. Until that trigger fires, no lane is
briefed to "port X from breadstuffs"; a lane may be briefed to "restate the *spec* of X as a decision with
both critiques." The thing to avoid is the one the record shows twice (Bread → Mini, Mini → nano): the
older tree quietly keeping its own lanes because nobody said it had stopped being the main line
[read `B:HORIZONLOG.md` SEPTEMBER 19/26: "Bread remains reference material", while `B:` still took 140
commits in September and 14 in October; measured].

---

## Appendix — measurement commands (all read-only; run 2026-10-18)

```
# breadstuffs
git -C ~/dev/breadstuffs log --oneline | wc -l                                   # 10359
git -C ~/dev/breadstuffs log --reverse --format='%ad %h %s' --date=short | head -1   # 2026-05-19 pyana import
git -C ~/dev/breadstuffs log -1 --format='%ad %h' --date=short                   # 2026-10-01 22fad151e
git -C ~/dev/breadstuffs log --format='%ad' --date=format:'%Y-%m' | sort | uniq -c
git -C ~/dev/breadstuffs log --format=%s | grep -ciE 'flag.?day'                 # 74 ; 'epoch' 152 ; 're-?genes' 5
ls ~/dev/breadstuffs/*/Cargo.toml | wc -l                                        # 208 (one is headver/)
find . -name '*.rs' -not -path './target/*' -not -path './vendor/*' | xargs cat | wc -l   # 5,648,939 raw
# per top dir: headver 2,611,677 · target 849,396 · vendor 59,804 → first-party ≈ 2,128,000
find metatheory -name '*.lean' -not -path '*/.lake/*' | xargs cat | wc -l        # 1,392,231 in 2,656 files
# Dregg2 by subdir: Circuit 714,474 (Emit 438,030) · Crypto 128,302 · Games 113,696 · Exec 72,696
grep -rhwE '^\s*(theorem|lemma)' metatheory --include='*.lean' | wc -l           # 43,342
grep -rhw '#assert_axioms' metatheory --include='*.lean' | wc -l                 # 24,245
grep -rhE '^#guard' metatheory/Dregg2 --include='*.lean' | wc -l                 # 14,399
grep -rhoE '@\[export [a-z_0-9]+\]' metatheory/Dregg2 | wc -l                     # 302
find docs -name '*.md' | wc -l ; ... | xargs cat | wc -l                         # 712 / 213,821
wc -l HORIZONLOG.md ; grep -c '^## ' HORIZONLOG.md                               # 21,257 / 413
ls ~/.claude/projects/-Users-ember-dev-breadstuffs/memory | wc -l                # 313
git -C ~/dev/minidregg log --oneline | wc -l ; ... --reverse --format=%ad | head -1   # 3844 / 2026-08-07

# nanodregg (hbox, read-only)
ssh hbox 'cd /tank/dregg-build/nanodregg/main && git log --oneline | wc -l'      # 405
ssh hbox '... git log --format=%ad --date=short | sort | uniq -c'                # 148 on 10-16, 257 on 10-17
ssh hbox '... find . -name "*.lean" -not -path "*/.lake/*" -not -path "./.git/*" | xargs cat | wc -l'   # 62,224 / 289 files
ssh hbox '... find . -name "*.rs" -not -path "*/target/*" -not -path "./.git/*" | xargs cat | wc -l'    # 12,431
ssh hbox '... grep -hwE "^\s*(theorem|lemma)" ... | wc -l'                       # 2,618 (SIZE.md: 2,828)
ssh hbox '... cat SIZE.md'                                                        # closure 71/150, sorry 0, partial 0, ops 6, kinds 13
ssh hbox '... cat decisions/*.md | wc -l'                                         # 10,477 ; ~266 "## " decisions
ssh hbox '... grep -c "name := " Protocol/Rows.lean'                              # 21
ssh hbox 'grep -h "=> GREEN" /tank/dregg-build/nanodregg/logs/*standing*'        # STANDING 2f5a201d … => GREEN
# NOTE: a naive find under main/ also sweeps .git/nanodregg-gate-*/tree worktree copies (699 K Lean lines,
# 29 K theorems); the numbers above exclude ./.git.
```
