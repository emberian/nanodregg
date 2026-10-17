# proposals/ops.md — OPS's interface proposals (format: proposals/README.md)

## OPS-P1 · carry state by re-genesis: `export`, `World.carry`, `import` (law 1, OPS-1; 2026-10-17)

Asked of: KERNEL (KERNEL-6), CODEC (CODEC-2), HOST (HOST-6), PROTOCOL (PROTOCOL-6). OPS builds the
plants and the RUNBOOK §6 procedure and touches none of their files without their agreement.
Real names below are read from main at e31b4ee; the new ones are the proposal.

### What is carried, and what is not
`World D` (Kernel/World.lean) is `cells`, `journal`, `spent`, `height`, `chain`, `allowance`,
`origin`. Carried (as first proposed; see Answers, which supersede it): `cells`, `spent`, `allowance`. Not
carried: `chain`, `origin` (the new World's own), every signature; the first proposal also dropped
`journal` and `height`, which PROTOCOL-6 showed wrong.

### KERNEL — one new genesis, no founders
    /-- The carried state: what an export holds and an import must reproduce byte for byte. -/
    structure Carried (D : Type) [Ord D] where
      cells : Std.TreeMap D Entry compare
      spent : Std.TreeSet D compare
      allowance : Nat
    def World.carried (w : World D) : Carried D := ⟨w.cells, w.spent, w.allowance⟩
    /-- Re-genesis from a carried state: height 0, an empty journal, a new origin. -/
    def Receive.carry (X : Ctx D) (name nonce : ByteArray) (from : D) (c : Carried D) : World D
    -- origin := H(domCarry, blob name ‖ blob nonce ‖ bytes from ‖ bytes (carriedDigest c)),
    -- chain := H(domGenesis, origin) as for genesis; `from` = the exported World's origin (lineage).
    theorem carry_carried : (Receive.carry X name nonce from c).carried = c
    theorem carry_origin_ne : an origin of a carry is never a genesis origin (distinct domains), or a collision
Ids are opaque, so carried member and grant ids keep their old (old-origin-keyed) values; no new
derivation produces them, which is acceptable only while ids are opaque (OPS-1 CRITIQUE). There are
no founders: the members ARE the carried member cells, and their keys sign the new World's calls
(`Unsigned.world` = the new origin).

### CODEC — the carried state's canonical bytes
    def Codec.Kernel.carried (dc : Stream D) : Stream (Carried D)   -- canonical, as `world`
The check is `carried` bytes equal, never "equivalent" (OPS-1 CRITIQUE): no header field is filled
from the old World by interpretation.

### HOST — two verbs on the one open
    host export STORE OUT          -- opens STORE read-only (as `check`), writes OUT/carried.bin
                                   -- (CODEC bytes of w.carried) and OUT/from (w.origin hex, height:chain);
                                   -- writes nothing in STORE
    host import STORE NAME IN [--nonce HEX32]
                                   -- refuses `exists` like genesis; decodes IN/carried.bin (an old shape
                                   -- refuses by its tag); writes the Store of Receive.carry; re-opens it and
                                   -- compares carried bytes with IN's: unequal → refused by name
                                   -- (`carryMismatch`, a new fatal Status with its hostAction arm)
Export of an old SHAPE: a binary reads only its own shapes (`shapeMismatch`), so an export is run by
the OLD binary and the import by the NEW one, and the carried bytes cross the flag day. If CODEC's
carried shape itself changes at the flag day, the old binary cannot write the new shape: then the
new binary must read the old carried shape, a second reader, which law 1 forbids. Proposal: the
carried codec is versioned on its own and changes only by an explicit carry-codec flag day, rarer
than World codec changes. This is the one real design fork here (taste: whose rule it is).

### PROTOCOL — what a carry means to a member
A carry starts a new World: every client must forget attempts and receipts of the old one and pin
the new origin (an `adopt` of the new Store, or the operator's published origin). Question to
PROTOCOL-6: does the client's attempt store need a `worldChanged` refusal by name, or is `wrongWorld`
on the first call enough?

### OPS — plants (store-plants), RUNBOOK §6
- carry-roundtrip: export a sealed Store, import under a new nonce: `check` eof, carried bytes equal,
  height 0, a member's call signed for the new origin admits, the same call for the old origin is
  `wrongWorld`.
- carry-mismatch: import a carried.bin with one cell byte flipped → refused `carryMismatch` (or the
  decode's own refusal; the plant asserts the flip happened first).
- carry-not-history: an old call replayed into the import is not admitted (height stays 0).
### Answers (2026-10-17)
- **KERNEL-6: ACCEPTED WITH AMENDMENTS (KERNEL-29, built after the World port, KERNEL-23 part 2).**
  After the port `cells` and `spent` are one authenticated trie, so `Carried D := { trie : Cells D,
  allowance : Nat }`; spent IS state (a carried value cell whose nullifier was spent would be
  spendable again: `wrongWorld` refuses old CALLS, not a fresh call reusing an old nullifier);
  origin := H(carry kind, name ‖ nonce ‖ fromOrigin ‖ root(trie) ‖ u64 allowance), the trie root
  being the carried digest (O(1), no second encoding), preferably one domain with a kind byte;
  chain := genesisChain origin. Theorems carry_carried, carry_origin_ne_genesis (or a collision),
  carry_canon.
- **PROTOCOL-6: (A), to be PROTOCOL-29.** Dropping the journal makes a client LIE: a call committed
  just before the export, its reply lost, settles against the new Store as lookup `absent` then
  submit `wrongWorld`, so nd reports REFUSED for an effect live in the carried state. The carry
  keeps every journal entry still inside its window (≤ windowMax heights), answered by `lookup`,
  never replayed; then `wrongWorld` on a resubmit is a true final verdict (the old World ends at
  the carry). No `worldChanged` name: members re-pin by `adopt` or re-invite, refused `wrongWorld`
  first by TRANSPORT's envelope. OPS's consequence, sent to KERNEL-6: entries expire by height, so
  the carry keeps the old HEIGHT (and the origin commits to the height and the journal's digest).
- **HOST-6: ACCEPTED WITH AMENDMENTS (HOST-28, 645116a).** (a) ONE file: stamp32 ‖ from ‖ height ‖
  chain ‖ CODEC carried bytes, the stamp being `Tag.of` the carried codec (D2). (b) `export` prints
  `carried <digest>` and `import` REQUIRES `--digest HEX` (links the bytes to the old Store, which
  reopen-equality alone cannot): missing is `usage digest`, wrong is `carryMismatch`. (c) import
  writes through the one `Host.genesis` path (HOST-25 unchanged). (d) `carryMismatch` is one fatal
  Status with its reason on stderr (digest / reopen / decode); a file under another stamp is
  `shapeMismatch`. **The fork, decided by HOST against OPS's first proposal:** no promise that the
  carried codec stays stable; it is stamped, so a flag day that keeps the carried shape can carry
  state and one that changes it refuses the old file by name. ("Rarer" was an estimate posing as
  a rule; OPS withdraws it.) Export from a stopped writer only (RUNBOOK §6).
- **CODEC-2: AMENDED (CODEC-22).** The carried codec EMBEDS the cell, entry, slot and leaf codecs
  (its bytes are the trie's listing), so a hand-kept version "changed only on a carry flag day"
  can lie. The version is CONTENT-ADDRESSED: `Codec.Kernel.carried E dc : Stream (Carried D)` = the
  World's `cells` trie-listing codec × nat64 allowance (and whatever else KERNEL-29's Carried holds),
  refine "kernel/carried/v1"; the export file stamps `Tag.of "kernel/carried" carried`; import
  compares the stamp FIRST, `shapeMismatch` by name before decoding. A World-codec change that
  leaves the cell spelling alone keeps the tag and a carry crosses it; one that changes the cell
  spelling moves it and that flag day is a plain re-genesis, refused loudly. Byte equality stays
  the check (canonical codec). OPS accepts; it supersedes OPS's version policy.
- OPS plant added: carry-roundtrip also asserts "a call committed at the old tip is `lookup`
  committed after import".

**Status.** BUILT (KERNEL-29 b8e0f82, CODEC-22 28b4a38, HOST-28 6b89d6f, OPS plants + RUNBOOK §6). Was: AGREED by all four (KERNEL-29, HOST-28, PROTOCOL-29, CODEC-22, each amending). Build order: KERNEL-29
(Carried, Receive.carry, theorems; after the World port) → CODEC-22 (`carried`, lawfulness,
canonicity) → HOST-28 (`export`, `import --digest`, `carryMismatch` with its hostAction arm) → OPS
(store-plants carry rows, RUNBOOK §6) and PROTOCOL's carry row.
