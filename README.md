# nanodregg

nanodregg is a small shared-state system with a verified kernel. A group of members holds one
*World*: a finite map of typed cells. The World advances only by *Turns*, and a Turn is admitted
only by one function, `World.admit`, whose properties are theorems. A resident host process keeps
the World and a log of Turns on disk; a client signs requests; a follower re-derives every Turn
from its signed request and refuses the log by name if the host lied. The language members use to
write laws over their cells, Objective Bend, is part of the kernel's definition, not a layer on top.

It is a rebuild of an earlier system, minidregg, from that system's specification rather than its
code. The specification is the set of conformance rows in `Protocol/Rows.lean`, the deterministic
simulations, one workload called THE BAR, and the theorem statements that survived review. Nothing
here has users yet; every incompatible change is a re-genesis, and the repository says so in each
such commit.

## What is true today

Measured on 2026-10-18, from the standing verdict and the row runner on the build host:

- 22 conformance rows pass against the real host process over sockets, including key
  rotation, a cold follower catching up from two windows behind, log paging, audit, a thin
  member adopting a pinned checkpoint, and recorded refusals. Each row has a planted fault that
  turns it red by name. No row is pending.
- The kernel simulation runs 64 seeds under the deployed parameters (32-byte digests, cSHAKE256,
  the real codecs, RFC 8032 Ed25519): 4,395 turns admitted, 50,502 refused by their expected names,
  no failing seed, and the planted refusal kinds met. Disabling the pin check, the credit,
  the chain walk or the signature check turns most seeds red.
- The host simulations run the real loop over an in-memory disk and over a real file with
  `F_FULLFSYNC`, with crash cuts at every byte of an unsynced batch, thirty-one in-process fuel
  restarts, a second-writer attempt, a foreign segment, and a forged base.
- The client round trip runs the Rust client, its supervisor and two confined host processes end
  to end: create, write, read, a refused expectation, rotate, write under the rotated key, read.
  Under 0.5 s. Under bwrap on Linux and sandbox-exec on macOS.

What is not true yet: no deployment exists; THE BAR has not been judged (it is judged only on a
quiet machine, and no wall-clock number is taken before the end of development); the authenticated
cell root (the structure that lets a phone verify one cell) is designed and its trie is proved, but
the World does not use it yet; per-cell hiding is ruled out for v1 (the operator is a trusted vat and
sees every byte; decisions/protocol.md PROTOCOL-3), with member sealing held behind a named trigger.

## Laws

`CHARTER.md` holds the twelve laws every commit obeys and the critique of each. The ones that
decide the shape of the code:

1. One of everything. One World, one Turn, one admission path, one store format, one codec family,
   one digest type, one dispatch table, one sandbox shape. A second shape of an existing thing is a
   defect. Old shapes refuse to load; state is carried only by re-genesis from a checked export.
2. Lean decides, Rust moves bytes. Every accept, refuse, select, order or digest is a Lean
   definition with a named theorem. The Rust client's only protocol knowledge is a table generated
   from Lean.
3. Bytes end to end. `ByteArray` everywhere; one-pass canonical decoders with a proof that a
   decoder accepts exactly the encoding of the value it returns.
4. A static bound on everything; an assertion for every premise the types do not carry; no
   `partial def` in deployed code; O(touched) work per request, never O(store). The host's top loop
   is total, bounded by a lifetime constant with a named exit.
7. Refusals by name. Every refusal is a constructor with an injective name on the wire; a parse
   failure is never rendered as a verdict; "uncertain" is a real outcome.

Theorems are named; `#guard` is refused by the gates; one tree-wide axiom census replaces
per-theorem assertions; no `sorry` lands. A theorem that could be vacuous ships with a *tooth*: a
mutation, as a named theorem or a planted fault, that it refutes.

## Layers

| directory | owns | the theorem that holds it |
|---|---|---|
| `Kernel/` | World, Turn, `World.admit`, `World.fold`, the receivers that turn a signed request into a Turn, members and keys, grants, value, the simulation | admission is deterministic; a stale request is refused by name; storage and value are conserved as equalities; every live grant is rooted at genesis; the follower's fold reaches the host's World or exhibits a hash collision |
| `Codec/` | the one stream-codec family, digests, tags, SHA-3 and cSHAKE, Ed25519, the World and Call codecs, the generator for the client's table | `decode b = ok v ↔ b = bytes v` for every codec; equal tags mean equal shapes or a hash collision |
| `Host/` | the resident loop, the framed log, the sealed whole-World base, open and recovery, serve and follow, the exit table | a written segment reads back exactly; a torn tail is recovered and never invents a record; the loop's step equals the kernel's `submit`; no accepted frame is lost across a restart |
| `Protocol/` | the operation table (six wire operations on two sockets), the command language (eleven verbs), the read envelope, the attempt-store decision, the conformance rows and their runner | every operation is reached by a row; the only call a follower hands the client to submit is one its own World derived and admitted |
| `Lang/` | Objective Bend: terms, types, the checker, the machine, the reference semantics, packages, the standard laws | a term has one type; the machine computes exactly the reference relation; a checked program never gets stuck at any budget |
| `client/`, `sandbox/` | the Rust client (`nd`), its supervisor, custody of keys, the one confinement shape | the client decides nothing; a confined child cannot read the seed |
| `Hosting/`, `Ops/`, `gates/` | grain lifecycle and the provider broker; units, runbook, store plants; the gates and the commit judge | a grain's lifecycle is one edge list and its laws are generated from it; a restart is blocked on exactly the fatal exit codes; a commit that touches another layer's file, raises a size count without a reason, or exports a definition from a proof module is refused |

Each layer keeps its decisions, with a critique and a meta-critique of each, in `decisions/`.

## Building and running

Lean v4.30.0 (pinned in `lean-toolchain`), no packages beyond the core library; Rust stable for
`client/` and `sandbox/`.

```
lake build                      # every library; warnings are errors
lake exe kernel-sim --seeds 64  # the kernel simulation, deployed parameters
lake exe host-sim 1             # the host loop over an in-memory disk, one seed
lake exe host-file-sim 1        # the same over a real file
lake exe lang-journey           # a law installed and invoked through the real receivers
lake exe rows                   # every conformance row, with its plant
scripts/standing.sh             # the one-line verdict for the checkout
```

The standing verdict is `GREEN` only when every stage is a verdict and none is red. At the time of
writing it is `GREEN` (recorded at 2d76795; all 22 rows pass at 38d94e1).

## Working in the repository

Main is the only branch. Every layer edits in its own git worktree and lands with
`scripts/commit -m MSG PATH...`, which builds the candidate from the current main plus exactly the
named paths, runs the gates and the census from main's own copy of the scripts, and lands by
compare-and-swap. A plain `git commit` is refused by the hook. The gates refuse: a path outside the
committer's layer without a declared reason, a size count that rises without a reason, a definition
module importing a proof module, a proof module exporting a definition, `sorry`, `#guard`,
`partial`, a stale generated file, a dropped build target, and two paths that differ only in case.

`SIZE.md` is generated and holds the counts; `gates/ceilings.tsv` holds the ceilings, which only
fall unless a commit says why.

## Provenance

The charter was written on 2026-10-16. The layers were built by parallel agents, each attacking
its own row of the charter before building it; twenty-seven short prototypes were made across the
missing surfaces and six assemblies chose what to keep. The day's record, including every ruling
and every mistake, is in the project log outside this repository.

License: AGPL-3.0 (see LICENSE).
