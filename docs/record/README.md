# docs/record — the briefs that carried a decision

Dated, read-only copies of the decision-bearing briefs written in `~/dev/redregg/work/` (Ember approved the
migration 2026-10-21; nothing is redacted). Each file's first line names its source and its date (the date in the
brief's name, else its file's last write). They are a record, not a specification: a brief's recommendation binds nothing
until a `decisions/` entry or `CHARTER.md` says so, and where a decision and a brief disagree, the decision wins.
Never edit a record copy; a correction is a new decision entry (the 10-21 CORRECTION headers on the three briefs
that called breadstuffs a PoA main line were written into the sources before the copy). The lane logs
(`<LAYER>-LOG.md`), the STALL-WATCH and the measurement harnesses stay in redregg.

| file | source in redregg/work | dated | title |
|---|---|---|---|
| [ARCHITECTURE-20261016.md](ARCHITECTURE-20261016.md) | `ARCHITECTURE-20261016.md` | 2026-10-16 | ARCHITECTURE — Mini's layers, interfaces, data model and TODO, read from the code |
| [ASSEMBLY-hosting.md](ASSEMBLY-hosting.md) | `nanodregg-scout/ASSEMBLY-hosting.md` | 2026-10-16 | ASSEMBLY — hosting (Opus evaluator, 2026-10-16/17) |
| [ASSEMBLY-lang-docs.md](ASSEMBLY-lang-docs.md) | `nanodregg-scout/ASSEMBLY-lang-docs.md` | 2026-10-16 | ASSEMBLY-lang-docs — the Opus evaluation of scouts G1, G2, D1, D2, D3 (area: lang-docs), 2026-10-16/17 |
| [ASSEMBLY-ledger.md](ASSEMBLY-ledger.md) | `nanodregg-scout/ASSEMBLY-ledger.md` | 2026-10-16 | ASSEMBLY — ledger (Opus evaluator, 2026-10-16, nanodregg main d1f483e) |
| [ASSEMBLY-ops.md](ASSEMBLY-ops.md) | `nanodregg-scout/ASSEMBLY-ops.md` | 2026-10-16 | ASSEMBLY-ops — the Opus evaluation of scouts O1–O5 (area: ops), 2026-10-16 |
| [ASSEMBLY-perf.md](ASSEMBLY-perf.md) | `nanodregg-scout/ASSEMBLY-perf.md` | 2026-10-16 | ASSEMBLY-perf — the Opus evaluation of scouts P1–P3 (area: perf), 2026-10-16 |
| [ASSEMBLY-transport-consent.md](ASSEMBLY-transport-consent.md) | `nanodregg-scout/ASSEMBLY-transport-consent.md` | 2026-10-16 | ASSEMBLY — transport-consent (Opus evaluator, 2026-10-16) |
| [CYCLE-TIME-20261016.md](CYCLE-TIME-20261016.md) | `CYCLE-TIME-20261016.md` | 2026-10-16 | CYCLE-TIME 2026-10-16: why one Mini iteration takes hours, and what to cut |
| [DELETE-CLOSURE-20261016.md](DELETE-CLOSURE-20261016.md) | `DELETE-CLOSURE-20261016.md` | 2026-10-16 | DELETE-CLOSURE — the module graph of Mini main 2c27b08b (short form) |
| [DELETE-CODEC-20261016.md](DELETE-CODEC-20261016.md) | `DELETE-CODEC-20261016.md` | 2026-10-16 | DELETE-CODEC — codec/wire layer deletion dossier (SHORT; cut off by ROOT's re-tasking to BUILD-CODEC) |
| [DELETE-HOST-20261016.md](DELETE-HOST-20261016.md) | `DELETE-HOST-20261016.md` | 2026-10-16 | DELETE-HOST — Host layer deletion dossier (SHORT; cut off by re-tasking to BUILD-HOST) |
| [DELETE-KERNEL-20261016.md](DELETE-KERNEL-20261016.md) | `DELETE-KERNEL-20261016.md` | 2026-10-16 | DELETE-KERNEL — 2026-10-16 (DISCOVER-KERNEL, truncated: ROOT reassigned me to BUILD-KERNEL in ~/dev/nanodregg) |
| [DELETE-PROTOCOL-20261016.md](DELETE-PROTOCOL-20261016.md) | `DELETE-PROTOCOL-20261016.md` | 2026-10-16 | DELETE-PROTOCOL — the protocol surface, measured by what the spec reaches |
| [DELETE-RUST-20261016.md](DELETE-RUST-20261016.md) | `DELETE-RUST-20261016.md` | 2026-10-16 | DELETE-RUST — minidregg's native/ layer: reach, decisions, twins, keep set (DISCOVER-RUST, 2026-10-16) |
| [RECOVERY-20261016.md](RECOVERY-20261016.md) | `RECOVERY-20261016.md` | 2026-10-16 | RECOVERY 2026-10-16 — what happened 10-01 → 10-16, what exists, what to recover |
| [DELVETALK-LEARNINGS.md](DELVETALK-LEARNINGS.md) | `DELVETALK-LEARNINGS.md` | 2026-10-17 | What delvetalk2's Objective Bend learned that nanodregg has not taken in |
| [NANO-VS-MINI-20261017.md](NANO-VS-MINI-20261017.md) | `NANO-VS-MINI-20261017.md` | 2026-10-17 | nanodregg vs minidregg — scope, semantics, and which way to go (2026-10-17) |
| [PRIVACY-DESIGN-BRIEF.md](PRIVACY-DESIGN-BRIEF.md) | `PRIVACY-DESIGN-BRIEF.md` | 2026-10-17 | PRIVACY-DESIGN-BRIEF — per-cell blinding custody (D8) for nanodregg, read against the project's history |
| [GATES-19-DESIGN.md](GATES-19-DESIGN.md) | `GATES-19-DESIGN.md` | 2026-10-18 | GATES-19 design: a FIFO landing queue, an incremental re-judge after a re-base, and no stale verdict |
| [MINI-CONCEPTS-IN-NANO-20261018.md](MINI-CONCEPTS-IN-NANO-20261018.md) | `MINI-CONCEPTS-IN-NANO-20261018.md` | 2026-10-18 | Mini's coordination concepts in nanodregg: intents, co-receipts, joint turns, hyperedges, guarded holes (2026-10-18) |
| [NANO-VS-BREADSTUFFS-20261018.md](NANO-VS-BREADSTUFFS-20261018.md) | `NANO-VS-BREADSTUFFS-20261018.md` | 2026-10-18 | nanodregg vs breadstuffs — scope, scale, lineage, and what to do with the relationship (2026-10-18) |
| [GATES-20-DESIGN.md](GATES-20-DESIGN.md) | `GATES-20-DESIGN.md` | 2026-10-19 | GATES-20 design: traced read-sets select the runs and key the reuse |
| [GATES-21-PROPOSED.md](GATES-21-PROPOSED.md) | `GATES-21-PROPOSED.md` | 2026-10-19 | GATES-21 (PROPOSED, not to be built yet): a merge-train for tied landers |
| [PROOF-TECHNIQUE-20261019.md](PROOF-TECHNIQUE-20261019.md) | `PROOF-TECHNIQUE-20261019.md` | 2026-10-19 | PROOF TECHNIQUE — what nanodregg's theorem families are, what calculus they are groping toward, and one worked instance (2026-10-19) |
| [STAND-INS-20261019.md](STAND-INS-20261019.md) | `STAND-INS-20261019.md` | 2026-10-19 | nanodregg stand-ins: what stands where a real thing should (2026-10-19) |
| [BACKLOG-20261021.md](BACKLOG-20261021.md) | `BACKLOG-20261021.md` | 2026-10-21 | BACKLOG — nanodregg, 2026-10-21 ~17:00Z (ROOT's catalog before the context wall) |
| [COMPARE-20261021.md](COMPARE-20261021.md) | `COMPARE-20261021.md` | 2026-10-21 | nanodregg's four open calls against breadstuffs, delvetalk2 and minidregg (SCHOLAR-COMPARE, 2026-10-21) |
| [DECISIONS-20261021.md](DECISIONS-20261021.md) | `DECISIONS-20261021.md` | 2026-10-21 | DECISIONS — decision cards for Ember's open calls (SCHOLAR-DECISIONS, 2026-10-21) |
| [DREDGE-20261021.md](DREDGE-20261021.md) | `DREDGE-20261021.md` | 2026-10-21 | DREDGE — what the two pruned ROOT sessions queued, promised, asked, found or ruled and never put somewhere durable (SCHOLAR-DREDGE, 2026-10-21) |
