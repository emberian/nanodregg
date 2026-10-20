> record copy of redregg/work/nanodregg-scout/ASSEMBLY-lang-docs.md, 2026-10-16; the lane logs stay in redregg

# ASSEMBLY-lang-docs — the Opus evaluation of scouts G1, G2, D1, D2, D3 (area: lang-docs), 2026-10-16/17

Evaluator: Opus, one pass. I read CHARTER.md and decisions/{lang,kernel,protocol}.md at main (not the
primary checkout's working tree; see §0), LANG-0..7 in the frozen DECISIONS.md, LANG-LOG.md and
KERNEL-LOG.md, every scout's SCOUT.md and code, and the real code at main. Main moved four times while
I worked: 43c4d58 → 42bf1ce → d1f483e → ccec081. I extracted d1f483e with `git archive` to a scratch
copy and read the code there. Between d1f483e and ccec081 nothing changed in `Kernel/Receive/`,
`Kernel/{Turn,World}.lean` or `Lang/{Program,Package,Term}.lean` (`git diff --stat` is empty), so every
receiver and LANG citation below holds at ccec081. I did not modify nanodregg or any scout directory.
I added one file beside this one: `probe-lang-occasion.lean`, the probe of §1.

Each claim carries a tag:
- **[read]** I read it in code or docs at the cited place (main d1f483e unless a commit is named).
- **[ran]** I ran it myself this session; the output is quoted.
- **[scout-ran]** the scout reports running it, and I did not re-run it.
- **[assumed]** my inference; nothing I ran checks it.

---

## 0. Facts the scouts did not have, which change the assembly

### 0.1 Four of the five scouts measured a tree about 87 commits old [ran]

The primary checkout `~/dev/nanodregg` is "nobody's editing surface" under the CHARTER's worktree rule.
Its working tree and its `.lake` are frozen at about 19:25 on 10-16:
- `.lake/build/lib/lean/Lang/Term.olean` has mtime `Oct 16 19:25`.
- The working tree's `Kernel/Receive/Call.lean` is the blob that `82e71e4` replaced.
- `git rev-list --count 760115e..HEAD` = 87.

G1, G2, D2 and D3 all ran `lake env lean` from that checkout, or parsed it, so they built against its
oleans. D1 used `git archive f11caa2` plus wt/protocol's binaries at 43c4d58, which is fresher but
still stale. What this falsifies, each item checked at main:

| scout claim | at main | tag |
|---|---|---|
| G1: "Req needs `height`; no law can see time" | `Req` carries `notBefore`/`validUntil` (Call.lean:161-167, KERNEL-10, 82e71e4). `reqTy` has them (Lang/Package.lean:27-28). | [read] |
| G1: "no denotation of a law; a meaning theorem needs one" | LANG-18 landed `Lang/Proofs/BigStep.lean` with `run_bigStep` (Agree.lean:282) and `bigStep_run` (Complete.lean:205). A law's meaning is now stateable. | [read] |
| G1: package bytes 499–2756 B | LANG-17 changed the wire. The same quorum package is 2331 B at main, versus G1's 2008. | [ran] |
| G2: one-leg-per-cell, `legOf`, `duplicateLeg` | KERNEL-11 deleted legs. A Turn is `touches : List (Touch D)` with `Act = keep / write ops / retire` (Kernel/Turn.lean:26-48), and `sealTurn` takes ONE `effect : Option (D × Act)` (Call.lean:287). Cross.lean does not elaborate at main: `Unknown identifier legOf`, `Turn.legs` absent, `Req.mk has 4 explicit field`. | [ran] |
| D3: "`Lang/Read` does not exist" | `Lang/Read.lean` exists (f587ab3, s-expressions with names). `Protocol.Command.Verb.packageArg` (Verb.lean:176) reads `install TEXT` through it. | [read] |
| D3/D2: "Refusal/Reject need a `name`; `Sim.nameOf` parses repr" | `Refusal.name` exists (Call.lean:129) with `name_injective` (Kernel/Proofs/Receive.lean:15). So does `Reject.name` (World.lean:68, Proofs/Admit.lean:15). | [read] |
| D1/D3: "no `host` executable" | `lean_exe «host»` exists (lakefile.lean:77, 943cab7). `Host/Deployed.lean` imports `Codec.Deployed` and `Lang.Program`. | [read] |
| D2: "waste.tsv has 0 rows" | It has 6 rows (submit ×2, open, admit, fold, seal). | [read] |
| D2: "7 of 11 plants are prose" | Plants are typed: `plant := .caught .openLog 8 .ok` (Rows.lean:206). | [read] |
| D3 finding 1: "`well` expects `noGrant`, which will fail" | The `well` row now expects `lawDenied` (Rows.lean:302). | [read] |
| D3 finding 4: `stateKey` docstring wrong | Fixed: "a state slot below `stateBase`, or an edit key past `Bounds.slotKeyLimit`" (Call.lean:99). | [read] |

The same stale checkout is also a live hazard. Its default index stages deletions of files that are in
HEAD: `git status` shows `D  Codec/Deployed.lean`, `D  Codec/Ed25519.lean` and others. A plain
`git commit` from `~/dev/nanodregg` would revert main. The commit hook refuses plain commits (CHARTER
working rules) [read], so this is contained. But any scout or lane told to "build against
~/dev/nanodregg" gets a mirror of a dead tree. **Every future brief names a worktree refreshed to main,
or `git archive main`, and never the primary checkout.** The sibling ASSEMBLY-ops.md found the same
thing for its area.

### 0.2 The judge does not know which act it is judging: the birth hole and a new relaw hole [read + ran]

`Program.judge` gets `old new : Slots` and a `Req` (Call.lean:176-177). It never learns whether it is
judging a birth, a write, a law replacement or an invoke. Three receivers call it with `old = new`:
- `create`: `X.program.judge look pkg laws state state (reqOf u u.member)` (Derive.lean:159). This is G1's birth hole.
- `law`: `X.program.judge look none laws (stateOf cell) (stateOf cell) (reqOf u principal)` (Derive.lean:191). **This hole is new; no scout saw it.**
- `write` and `invoke` pass the real old and new (Derive.lean:178, :210).

A transition law has to admit `old = new` or it refuses every no-op. Because of that, it admits a
seeded birth, and it admits its own removal. §1 runs both holes at main.

### 0.3 `invoke` has no authority check, by design; a LANG doc says otherwise [read]

`invoke` computes `principal ← principalOf X look u obj (.invoke method) via` (Derive.lean:204).
`principalOf … none = .ok u.member` (Derive.lean:82-84), so without `via` any member invokes any
method, and only laws gate. KERNEL-6 says so explicitly ("`invoke` acts on programmed objects only,
principal = signer or root issuer"); write and law instead require `ownerAuthority`. So D3's finding 1
describes the design, not a missing check. However, `Lang/Journey.lean:16` says of L5: "B, holding A's
grant to invoke method 0 (so the kernel's authority check passes with principal A)". No such check
exists; B would be admitted to the method without the grant, and only `ownerOnly` stops it. That
docstring is false, and it belongs in the docs backlog (§3, ID-6).

---

## 1. What I ran at main

### 1.1 The probe

The file is `/Users/ember/dev/redregg/work/nanodregg-scout/probe-lang-occasion.lean`. It restates G1's
combinators and quorum at main's 4-field `reqTy`, adds `windowed` (a rate limit taken from the signed
window), and drives the real `Receive.submit` with `Lang.program`, using `Lang.Journey`'s `go` and Sim
toy parameters.

I ran it from `~/dev/nanodregg-wt/protocol`. Its oleans are at 943cab7, and the Lang and Kernel
sources there are clean and identical to main's receivers. The command was
`lake env lean --run …/probe-lang-occasion.lean` (about 2 s). Output [ran]:

```
ok   H1a install quorum (2331 bytes at HEAD's wire): admitted
ok   H1b A creates quorum object seeded approvals=7 (all three): admitted
ok   H1c A commits 77 alone: admitted, total = (some 77)
ok   H2a install law-only quorum package: admitted
ok   H2b A creates data object {approvals 0, total 5} under the quorum law: admitted
ok   H2c CONTROL A writes total 77 alone: refused lawDenied ... "quorum: no quorum"
ok   H2d A removes the quorum law (judged old = new): admitted
ok   H2e A writes total 77 alone after removing the law: admitted
ok   H3a install windowed(W=50, limit 2): admitted
ok   H3b create {count 0, epoch 0, total 0} window [0,49] at height 8: admitted
ok   H3c write #1 in epoch 0: admitted
ok   H3c write #2 in epoch 0: admitted
ok   H3c write #3 in epoch 0: refused lawDenied ... "windowed: rate limit 2"
ok   H3d cheat: a window spanning epochs [0,1000]: refused lawDenied ... "windowed: window spans epochs"
ok   H3e cheat: claim future epoch 5 by signing its window: rejected outsideWindow
ok   H3f next epoch 1 (height 49), count reset to 1: admitted
probe: AS EXPECTED
```

What it shows:
- **H1:** the birth hole holds at main.
- **H2:** a quorum law on a data object stops a lone write (H2c) but cannot stop its owner from removing it (H2d). After that the lone write goes through (H2e).
- **H3:** a real per-window rate limit can be written today without a clock holder:
  - the law requires `validUntil / W = notBefore / W`, so the Turn lands in epoch `notBefore / W`, because `World.admit` enforces the window (H3e);
  - and it requires `new.epoch = notBefore / W`.

  This makes G1's ask for `Req.height` unnecessary, and its `rateLimit` (with a trusted clock) wrong.
  KERNEL-10's reason for giving the window instead of the admitting height (the height is not in the
  pinned view) is correct, and the window is enough.

To run the probe at ccec081: commit 9e60d7f changed `Lang.Journey`'s helpers (`ctxWith prog` takes no
registry; the `Run` state has no `reg`; `Sim.u64le` becomes `Sim.dc.bytes`). That is a four-line port.
The receivers it exercises are unchanged [read].

### 1.2 The scouts' own artifacts against current code [ran]

- **D3 `Explain.lean`** fails, and the failures are its purpose:
  - `Missing cases: @Refusal.eventMismatch @Refusal.undecodableEvent (Refusal.enrollSpent _) (Refusal.unrooted _)`
  - `Unknown constant Nanodregg.Kernel.Reject.duplicateLeg`
  - `Missing cases: (Codec.Refusal.tooDeep _ _)`

  A total, wildcard-free glossary turned drift into named compile errors within hours.
- **D1 `Boundaries.lean`** shows 2 of its 21 ascriptions drifted: `Host.openWith` gives a type mismatch at :65, and `Protocol.Rows.Writer.HostState` is unknown at :81. The second is in wt/protocol's uncommitted edits, so treat it as indicative. The ascription gate works.
- **D2 `matrix.py`**, run on a copy in my scratchpad against the main snapshot, crashes: `ValueError: substring not found` at `inductive AuditFault`, because `AuditFault` is gone. A Python projection rots with the tree; D2 predicted this ("not this script as a gate").
- **D1 `layers.py`** on the main snapshot: both lib cycles persist. `Codec -> Kernel 3` / `Kernel -> Codec 2`, and `Host -> Protocol 6` / `Protocol -> Host 6`.
- **G2 `Cross.lean`** does not elaborate (see §0.1). **G1** at the stale tree (its own `run-final.log` and `e2e.log`): GREEN as reported [ran at the stale tree, which proves only that the scout's claims were true of its tree].

---

## 2. Per scout: keep, discard, rework

### G1 — a standard library of laws [verdict: assemble the shape, rework three laws]

**KEEP**
- **The combinator set:** `sortRow guard guards allOf andT anyOf notT lawOf pkgOf methodOf keep` (G1/Laws.lean:10-31, :85-101). Restate it at main's `reqTy`, as the probe already does; it compiled and ran there [ran]. A law is a closed `lawTy S` term. Composition is a list of laws over one state type (G1's `vault`), so no new language construct is needed.
- **`bounded` and `allowlist` as written** (Laws.lean:41-47).
- **The quorum skeleton:** the bitmask, `approvalFor`, members baked into the term (Laws.lean:50-67).
- **The mutation generator `mutants`** (G1/Tests.lean:11-24): every well-typed one-site mutation of a law term. Keep it as tooling. It reports how sharp a law's case table is; it is evidence, not proof.
- **E11/E12 and my H2c-H2e as standing rows:** they must flip to refused when ID-1 lands.

**REWORK**
- **`ownerOnly`** checks `agent` (Laws.lean:37). With grants, `principal` is the delegated authority (`Req` docstring, Call.lean:158-160). An `ownerOnly` on `agent` refuses every delegate, and Journey L5 relies on exactly that. The stdlib needs two named laws: `ownerActs` (principal = owner, so delegation works) and `ownerSigns` (agent = owner, so only the owner's key may act). The name must say which.
- **`quorum`:** bind approvals to a proposal. The state becomes `{approvals, proposal, total}`. `approve` keeps `proposal`; `commit` requires `new.total = old.proposal`; a change of `proposal` resets approvals. Add the birth clause (ID-1). Without both, approvals for 9 authorize 77 (G1's own critique) and the creator seeds a full quorum (H1).
- **`judgeLaw`** (Laws.lean:119-128): do not keep it as a second harness. Factor the inner `run … extract verdictTy` out of `Lang.Program.judgeOne` (Lang/Program.lean:189-207) into one `runLaw`, and have both the receiver and the tests call it (law 1).

**DISCARD**
- **`rateLimit`** (Laws.lean:70-82). It is a per-epoch budget ticked by a trusted clock holder (G1's own words), not a rate limit. `windowed` replaces it [ran, H3].
- **G1 interface 1 (`Req.height`).** Answered by KERNEL-10, which explains why the admitting height is not given; H3 shows the window suffices.
- **G1 interface 3 (bytes `len`/`slice`) for the first lane.** Under ID-2 (parameters live in the generated term, not in state), nothing needs a variable-length member set. A `slice` that copies up to 64 KiB in one tick breaks LANG-L's "one tick = O(1) work"; the prim's cost model is the real design work (ID-4).
- **The package byte counts and survivor triage numbers.** They come from the old wire and the stale tree.

### G2 — cross-object calls (LANG-13) [verdict: keep the design, discard the code, build when LEDGER consumes it]

**KEEP (the design)**
- Effects returned as DATA by `run`.
- A depth-first visit that runs each object once, on its pre-Turn state, so nothing reads an intermediate state.
- Re-entry as a named refusal (`reentry`).
- The bounds trio: `callDepthMax = 4`, `callsMax = 8`, a consensus `treeTicksMax`.
- Object-as-grantee.
- The `visit_distinct` proof idea (`foldlM_inv` + the `any`-check). At main it restates as "the derived touches name distinct cells", so `duplicateTouch` is unreachable.
- The ten scenarios, as rows once the code exists.
- The confused-deputy and no-cross-object-law critiques, which carry over unchanged.

**DISCARD (the code)**
- Cross.lean does not elaborate at main [ran].
- `ProgramFx` beside `Program` is a twin (G2 said so).
- The local `Fault` is not `Refusal` constructors (law 7).

**REWORK: restate over touches**
`sealTurn` takes `effects : List (D × Act)`, one per visited object, each on a pinned cell. The
signatures are in ID-9.

**The fork G2 left open (client-composed `Body.invokeAll`): I rule against it [assumed]**
A one-signer batch of independent invokes is atomic. But no object's law can see the others, and
since invoke is open (§0.3), one signer's batch carries no authority a single invoke lacks. A bounty's
`approve` law cannot check that the batch also moved the funds, and the funds' law cannot check that
the bounty approved. Atomicity without mutual visibility is a client convenience, not a semantic. With
effects-as-data, `approve` itself emits the transfer, so the package code guarantees approve ⇒
transfer. That is exactly what the bounty and pay rows need from LEDGER.

**When to build it**
Build it with LEDGER's first receiver that a method must trigger (ROOT's ruling, PROTOCOL-15:
pay/well/bounty need LEDGER receivers). A method-result `effects` field that nothing consumes would be
a no-op shape (CLAUDE.md). See risk R7 for the meta-critique of this ordering.

### D1 — ARCHITECTURE.md from the code [verdict: assemble the checkers, regenerate the prose]

**KEEP**
- **The type-ascription technique:** `example : <claimed type> := @Real.name` (D1/Boundaries.lean). It catches drift [ran: 2 of 21 within hours] and is not a `#guard`: it asserts a type, not an evaluated instance.
- **`layers.py`** [ran at main].
- **The "does anything run this hop" column.**
- **The THEOREM / INSTANCE / PLANT / PREMISE matrix,** as the template for law 6's vacuity read.
- **The disagreement backlog,** re-verified at main:
  - (1) Partly done: 051a8cc says "the rows drive HOST's own log arm and pager". `Protocol/Rows/Writer.lean` shrank by 119 lines, but `logAnswer`/`machine` were still present at d1f483e (:64, :80) [read at d1f483e; not re-read at ccec081].
  - (2) Done.
  - (3) Holds: `Op.receiver : Op → String` (Table.lean:74).
  - (4) Holds: `nullifiers := []` (Call.lean:293). The pay row is blocked on LEDGER by name.
  - (5) Holds: no `Ed25519.sign` (Codec/Ed25519.lean:205 is `verify`).
  - (6) Holds: both cycles [ran].
  - (7) Not re-checked.

**DISCARD**
- **`path:line` pinning in `cites.py`.** Every insertion above a cited line breaks it, and main moved four times while I wrote. Cite by declaration NAME; let a renderer derive file:line.
- **Every count in the prose** (D1's own rule).
- **The 1.6 MB `head/` snapshot.**

### D2 — the spec matrix [verdict: keep the questions, discard the instrument]

**KEEP**
- **The question it asks:** rows × refusal names × theorems × plants × waste.
- **"A refusal name a row expects must resolve to a constructor, by a theorem."** At main `Expect.refused (name : String)` is still untyped (Rows.lean:27), and `"crossWorldVolume"` (Rows.lean:329, a blocked row) names no constructor [read].
- **"Row.kinds should be `Body` tags".** It is still `List String` (Rows.lean:130) [read].

**DISCARD**
- **`matrix.py`:** it crashes at main [ran], and its theorem coverage is lexical.
- **Its counts and findings 1, 5 and 8:** stale (§0.1).
- **"A row per uncovered constructor":** D2 rejected this itself (the minidregg 186-opcode failure).

### D3 — the resident tutorial [verdict: assemble the technique, rewrite the text]

**KEEP**
- **The total, wildcard-free glossary** (D3/Explain.lean). It catches drift by constructor name [ran]. It moves to `Docs/` and takes each name from the owner's `name` (ID-6).
- **The Tour technique** (D3/Tour.lean): every tutorial step is an executed call whose outcome name is asserted.
- **Finding 2, as teaching material:** identical package bytes answer `idTaken`, which means "use the existing id".
- **The `Refusal.program` text leak, which holds at main:**
  - `decodeText e := s!"decode {repr e}"` (Lang/Program.lean:49) puts Lean `repr` on the wire.
  - `CheckError.text` (Package.lean:54) sends prose ("body does not check at its interface") where law 7 wants a name.
  - `Lang.Read`'s errors are `Except String` (Read.lean:31) with no position.

**DISCARD**
- **TUTORIAL.md's command text:** it describes the surface as it was at 19:25.
- **Findings 1, 3 and 4:** 1 is by design (§0.3); 3 is answered by the rotate row expecting and passing `unknownKey` (D1 run.out at 43c4d58) [scout-ran]; 4 is fixed.
- **Restated name strings in the glossary:** they are a second list. Use `r.name`.

---

## 3. Interface decisions

Each entry gives the signature at main, the layer that owns it, both critiques, and what re-emits.

### ID-1 — `Req.occasion`: the judge is told what it judges (KERNEL owns `Req`; LANG owns `reqTy`)

```lean
-- Kernel/Receive/Call.lean (beside Req, :161)
inductive Occasion
  | birth            -- create: old = new = the seed
  | write            -- write on a data object
  | relaw            -- law on a data object: the laws in force judge their own replacement
  | invoke (method : Nat)
  deriving DecidableEq, Repr
structure Req (D : Type) where
  agent : D; principal : D; notBefore : Nat; validUntil : Nat
  occasion : Occasion
def reqOf (u : Unsigned D) (principal : D) (o : Occasion) : Req D   -- :244, every caller passes its occasion

-- Lang/Package.lean:27
def occasionTy : Ty := .sum [("birth", .record []), ("invoke", .nat), ("relaw", .record []), ("write", .record [])]
def reqTy : Ty := .record [("agent", .bytes), ("notBefore", .nat), ("occasion", occasionTy),
                           ("principal", .bytes), ("validUntil", .nat)]
-- Lang/Program.lean:172 reqData gains the occasion's `.inj`
```

**Decision.**
- Every judge call passes its occasion: Derive.lean:159 passes `birth`, :178 `write`, :191 `relaw`, :204/210 `invoke method`.
- The stdlib's `lawOf` takes a REQUIRED birth clause and a REQUIRED relaw clause. It has no default arm.
- E11/E12/H1 and H2d must flip to refused (rows in lang-journey).

**Alternatives.**
- (a) A package `init` constructor (`fn A (fn reqTy S)`): `create` runs it, so a programmed object's seed is computed, never supplied. That is the OO answer.
- (b) `Req.birth : Bool` (G1's suggestion).
- (c) Judge birth against an absent old (`old : Option S`).

**Why this one.**
- One mechanism closes all three `old = new` call sites. (a) closes only programmed-object birth: data objects (`create none laws state`) and relaw stay open.
- (b) misses relaw.
- (c) changes `lawTy` and still misses relaw.

**Critique.**
- It fails open by omission. A hand-written law that ignores `occasion` keeps both holes, and install cannot tell. Only the stdlib's `lawOf` makes the birth clause unavoidable. This is the "gating defaults to silence" class, moved from the kernel to authors.
- `relaw` does not show the law the NEW law list. A law can refuse its replacement, or permit it under a state condition (a quorum), but it cannot say "only by a superset of me".
- Every law term gets bigger by one `case`.
- (a)'s property is real and lost: a package's methods may rely on invariants their laws do not state, and only a constructor establishes those.

**Meta-critique.** I picked the option with fewest mechanisms (law 1), which is also the one I can
probe today. The constructor is what a Hermes author would expect, and I have not asked one.

**Flag day.** `reqTy` changes, so `lawTy` and `methodTy` change, so every package's interface, bytes
and id (`romIdOf`) change. Every installed package refuses to load (`malformedCell` at the package
slot). Re-genesis. `Lang/Journey.lean`'s `ownedText` must re-emit (its `reqTy` is spelled out at :60-88).

### ID-2 — The law stdlib is generated core terms with meaning theorems (LANG owns `Lang/Std.lean`, `Lang/Proofs/Std.lean`)

```lean
-- Lang/Std.lean (def module)
def lawOf (S : Ty) (birth relaw change : Term) : Term   -- case on req.occasion; no default arm
def guard (c : Term) (why : String) (rest : Term) : Term
def allOf : List (Term × String) → Term
def anyOf : List Term → Term
def ownerActs (S : Ty) (ownerField : Label) : Term       -- principal = owner
def ownerSigns (S : Ty) (ownerField : Label) : Term      -- agent = owner
def bounded (S : Ty) (f : Label) (max : Nat) : Term
def allowlist (S : Ty) (ids : List ByteArray) : Term
def quorum (S : Ty) (members : List ByteArray) (k : Nat) (guarded : Label) : Term  -- proposal-bound
def windowed (S : Ty) (W limit : Nat) (guarded : Label) : Term
def pkgOf (S : Ty) (laws : List (Label × Term)) (methods : List (Label × Ty × Term)) : Package
-- Lang/Program.lean: the one law runner, factored out of judgeOne (:189-207)
def runLaw (lib : List Term) (t : Term) (o n r : Data) : Except Fault (Except String Unit)
-- Lang/Proofs/Std.lean (proof module), over Lang/Proofs/BigStep.lean's BigStep
theorem bigStep_guard … ; theorem bigStep_allOf … ; theorem bigStep_anyOf …
theorem quorum_change_needs_k : BigStep [] (env o n r) (apply3 (quorum S ms k g)) (.ok okV) →
  n.get g ≠ o.get g → k ≤ popcount (o.get "approvals") ∧ n.get g = o.get "proposal"
theorem quorum_birth_empty : … occasion = birth → admitted → n.get "approvals" = 0
theorem windowed_lands_in_epoch : admitted → n.get "epoch" = r.notBefore / W ∧ r.validUntil / W = r.notBefore / W
```

**Decision.**
- Laws are Lean generators that emit closed core terms. A package is composed at author time (one state type, a list of laws), and its id commits to the expanded term.
- Each combinator has a BigStep meaning lemma. Each stdlib law has a spec theorem proved compositionally from those lemmas, never by `decide` through the evaluator. A 166-node term under `decide` is the reduction-bomb shape.
- `lang-journey` gains rows L8+: H1 refused, H2d refused, H3 as is, and quorum with proposal binding. G1's E4-E10 are restated.

**Alternatives.**
- (a) Parameters in STATE: one installed `std/quorum` package reused by every object, with members and k as state fields. This needs bytes `len`/`slice` and parameter-freeze clauses.
- (b) Laws as `.obend` text files a resident copies.
- (c) Keep G1's combinators outside `Lang/` as test helpers.

**Why this one.**
- (a) does not compose. LANG-11 lays state out positionally, so two separately installed law packages on one data object read slot `stateBase + i` at their own state types. Quorum's slot 16 is `approvals`; windowed's slot 16 is `count`. They cannot be stacked on one object [read: LANG-11, Lang/Program.lean:142-166]. Author-time composition into one package has no such conflict.
- (b) has no parameters (the core is monomorphic, LANG-1).
- (c) leaves residents with nothing to use and the theorems with nothing to be about.

**Critique.**
- Every object type is its own install (2–3 KB of ROM charged to the World's storage, KERNEL-15).
- Changing a member set is a new package plus a new object, with state carried by a "migrate" commit. A real multisig rotates members, and this design makes that a migration.
- A resident can reach the generators only through Lean, or through a `Lang.Read` macro (`(std quorum …)`) that does not exist yet. That makes Read an elaborator, which LANG-0 kept out of admission. It stays out of admission (Read runs client-side), but it grows.
- The meaning theorems may be expensive. Symbolic records under `BigStep` have not been tried here.

**Meta-critique.**
- I chose per-instance generation partly because it lets me drop the bytes-prim question (ID-4) from the first lane. That is the "phase ordering that avoids a hard part" smell. The test is whether (a) is right on its own merits; it is not, by the positional-composition argument, which I derived and did not run [assumed].

### ID-3 — Authority is an explicit clause of every generated package (LANG; KERNEL-6 unchanged)

**Decision.**
- `pkgOf` requires one authority law (`ownerActs` | `ownerSigns` | `allowlist` | `anyone`).
- `anyone` is a named law that admits everything, so a public object says so.
- KERNEL keeps open invoke (KERNEL-6). The bounty "hunter" and "rival" rows need strangers to reach the method.

**Alternatives.** Make `invoke` default-closed (owner or grant), like `write`. Then a public object needs a World-wide grant, which does not exist.

**Critique.**
- This is an authoring convention, not an install-time check. A hand-written package with no authority law is world-writable through its methods, and nothing says so.
- The ids are public (the log), so open invoke is ambient authority, not capability.

**Meta-critique.** I am preserving a KERNEL decision I did not make, because flipping it breaks rows that do not run yet. Name it, and ask KERNEL whether `Right.invoke` should be required.

### ID-4 — Bytes primitives need a cost model before they exist (LANG; not in the first lane)

`Prim` is binary over one operand type (`Prim.right := Prim.left`, Term.lean:27). `len`
(bytes → nat) and `take`/`drop` (nat × bytes → bytes) need heterogeneous operand types, and a copy
charged per 32-byte word (LANG-L: each tick is O(1) work). They are deferred to the first package that
needs a variable-length collection in state. Under ID-2 no stdlib law does.

**Critique.**
- A list-of-links wiki page (LANG-1's own example) is that package, and it is plausibly soon.

**Meta-critique.**
- "No one needs it yet" is how a missing primitive becomes permanent. File it (`cv task`), with the cost model as the task.

### ID-5 — Names on the wire, not prose and not `repr` (LANG and CODEC)

```lean
-- Codec/Refusal.lean (CODEC): the pattern Kernel already follows
def Codec.Refusal.name : Codec.Refusal → String          + theorem name_injective
-- Lang/Package.lean (LANG)
def CheckError.name : CheckError → String                + theorem name_injective   -- text stays for humans
-- Lang/Program.lean:49 (LANG)
def decodeText (e : Codec.Refusal) : String := s!"decode {e.name}"
-- Lang/Read.lean:31 (LANG): a typed refusal with a position
inductive ReadRefusal | unbalanced (at : Nat) | badAtom (at : Nat) (s : String) | … ; def ReadRefusal.name
```

**Why.** Law 7. A `repr` on the wire is the "refusal renders as the expected verdict" class waiting to happen.

**Critique.**
- `Refusal.program (reason : String)` stays a string, because KERNEL cannot import LANG's types. The reason's FIRST token is a name with `name_injective`, and the rest is free text. That is a convention inside a string, and no type checks it.

**Meta-critique.**
- I am fixing what D3 tripped over, not auditing every `String` refusal.

### ID-6 — Docs are checked artifacts in a `Docs/` lib, per-layer files, in the per-commit build (new DOCS owner; every layer owns its own file)

```
Docs/Boundaries/<Layer>.lean   example : <type> := @Real.name   (one file per layer; OWNERS: Docs/Boundaries/Kernel.lean KERNEL, …)
Docs/Glossary/<Layer>.lean     def <Type>.explain : <Type> → (meaning next : String), TOTAL, no wildcard;
                               the name is always r.name (never restated)
Docs/Tour.lean + lean_exe «docs-tour»   each step an executed call; its outcome NAME is the row's expectation
docs/ARCHITECTURE.md           prose; cites declaration NAMES only (no path:line, no counts); every fenced
                               signature must be an ascription line in Docs/Boundaries (gate checks)
```

**Decision.**
- `Docs` is a `@[default_target] lean_lib`, so a signature change that breaks its layer's ascription, or a new constructor without an explanation, fails THAT commit. The committer updates its own layer's `Docs/` file in the same commit ("say what you broke").
- A gate (`gates/docs.py`) fails when an `ARCHITECTURE.md` fence has no matching ascription, so deleting an ascription to go green turns the doc red.
- The Journey L5 docstring (§0.3) is the first correction.

**Alternatives.**
- (a) A standing-stage docs gate, not per commit. It reports but never blocks: the fail-open gate class (memory: every gate reports, none blocks).
- (b) Put the explanations on the owners' def modules beside `name`. That adds English prose to the deployed closure and the deployed line count (KERNEL-22).
- (c) Generate ARCHITECTURE.md entirely.

**Why this one.**
- It blocks like code does.
- The prose leaves the deployed closure.
- (c) loses the explanation, which is the part only a reader can write.

**Critique.**
- Every interface change now also touches a `Docs/` file: more friction and more hot files (scripts/commit's compare-and-swap retries absorb that).
- A KERNEL change to a type that LANG's ascription mentions breaks LANG's Docs file, so this is cross-layer again. It is the same ripple as any downstream consumer, and law 9 already makes the committer fix it.
- Glossary prose can be WRONG while complete. Only `Tour` checks a meaning against a run.

**Meta-critique.**
- I watched four scouts build on a dead tree and am reacting by making docs block commits. The test is whether a blocking docs gate would have caught the Journey L5 lie. It would not have (that is prose, not a signature); only `Tour` would.

### ID-7 — Row expectations resolve to constructors, by theorem (PROTOCOL; KERNEL supplies the lists)

```lean
-- Kernel (beside Refusal.name / Reject.name)
def Refusal.names : List String ;  theorem Refusal.name_mem (r : Refusal D) : r.name ∈ Refusal.names := by cases r <;> decide
                                   theorem Refusal.names_realized : ∀ n ∈ Refusal.names, ∃ r : Refusal Unit, r.name = n
-- Protocol/Proofs/Rows.lean
theorem rows_refusals_resolve : ∀ r ∈ rows, ∀ l ∈ r.lines, ∀ n, l.expect = .refused n → n ∈ allNames := by decide
-- Protocol/Rows.lean:130   kinds : List Kernel.Receive.Body.Tag   (not List String)
```

**Why.** It kills unresolvable names (`crossWorldVolume`) at build time without D2's lexical
matcher, and the `names` list cannot drift, because it is proved complete both ways.

**Critique.**
- The list is a second enumeration, guarded by two theorems instead of by construction.
- A typed `Expect.refused (t : AnyTag)` is cleaner but couples Rows to every owner's tag type.

**Meta-critique.**
- The cheap form was the one I could specify without designing a tag type for six layers.

### ID-8 — `Op.receiver` names something a checker resolves (PROTOCOL)

`Protocol/Table.lean:74 def receiver : Op → String` becomes `Op → Lean.Name`. A `Docs/Boundaries/Protocol.lean`
`run_cmd` throws on any name absent from the environment. At f11caa2 three names
(`World.lookup`, `Receive.view`, `Log.framesFrom`) named nothing (D1 [scout-ran]). I did not re-check
them at ccec081, where 051a8cc touched the table.

**Critique.**
- `run_cmd` is a meta check, not a theorem. An environment fact cannot be a Prop, so law 6's "named theorem" does not apply. Record it as a gate, not a proof.

### ID-9 — Cross-object calls, shape decided now, built with LEDGER's first effect (KERNEL + LANG, LANG-19)

```lean
-- Kernel/Receive/Call.lean:179
run : Pinned D → (pkg : D) → (state : Slots) → (method : Nat) → (args : ByteArray) → Req D →
  (budget : Nat) → Except (Refusal D) (Slots × List (Effect D))
structure Effect (D) where target : D; method : Nat; args : ByteArray; budget : Nat; via : D
-- :287
def sealTurn (X) (c) (creates : List Cell) (effects : List (D × Act)) : Except (Refusal D) (Turn D)
-- Refusal gains: reentry (obj : D) | callDepth | callFanout | callBudget ; Bounds: callDepthMax 4, callsMax 8, treeTicksMax
-- Derive.lean:250   grant: readKind look grantee kindMember  ∨  kindObject
-- Lang: methodTy S A := fn S (fn A (fn reqTy (rec {calls : <effect list>, state : S})))
theorem visit_distinct : visit … = .ok acc → (acc.ran.map (·.obj)).Nodup   -- ⇒ no duplicateTouch
```

**Decision.** Write LANG-19 now; build when LEDGER lands its first receiver that a method triggers.

**Critique.** G2's critique, carried over:
- the confused deputy (callee laws see the calling object, not the signer, so `Req` may need `origin`);
- no answer flows back;
- no law spans the objects changed together;
- the client pins the whole tree.

**Meta-critique.** See R7.

---

## 4. Charter rows

| layer | owner | owns | must never | first deliverable |
|---|---|---|---|---|
| LANG (amended row) | BUILD-LANG (LANG-3, successor of LANG-2) | adds `Lang/Std.lean`, `Lang/Proofs/Std.lean`, `runLaw` in `Lang/Program.lean`, LANG's half of ID-1 (`occasionTy` in `reqTy`), ID-5's LANG names | ship a stdlib law without its spec theorem; ship `lawOf` with a default occasion arm; keep a second law runner beside `judgeOne`; prove a law's meaning by `decide` through the evaluator | ID-1 landed with KERNEL (H1, H2 flip to refused in lang-journey); `quorum`/`windowed`/`ownerActs`/`ownerSigns`/`bounded`/`allowlist` in `Lang/Std.lean` with `quorum_change_needs_k`, `quorum_birth_empty`, `windowed_lands_in_epoch` |
| KERNEL (deliverable) | BUILD-KERNEL | `Occasion`, `Req.occasion`, `reqOf … o`, every receiver passing its occasion; `Refusal.names`/`Reject.names` with both theorems (ID-7) | judge any act with `old = new` without saying which act | the ID-1 kernel half in the same commit train as LANG's (flag day: re-genesis) |
| DOCS (new) | BUILD-DOCS | `Docs/` lib (Boundaries and Glossary per layer, OWNERS rows mapping each file to its layer), `Docs/Tour.lean` + `docs-tour` exe (a row), `docs/ARCHITECTURE.md`, `gates/docs.py` | write a count or a `path:line` in prose; restate a constructor name; be a non-blocking gate; enter the deployed closure; describe a command that no executable runs | `Docs/Boundaries/*.lean` seeded from D1's 21 ascriptions re-stated at main; `Docs/Glossary/*.lean` from D3's Explain using `r.name`; `gates/docs.py`; the Journey L5 docstring corrected (through LANG) |
| CODEC (deliverable) | BUILD-CODEC | `Codec.Refusal.name` + `name_injective` | render `repr` on the wire | that one function and its theorem |
| PROTOCOL (deliverable) | BUILD-PROTOCOL | ID-7 `rows_refusals_resolve`, `Row.kinds : List Body.Tag`, ID-8 `receiver : Op → Lean.Name` | keep a refusal name no constructor carries | `rows_refusals_resolve` by `decide` |
| LEDGER (ROOT's new layer, PROTOCOL-15; not defined here) | — | — | — | its design must answer ID-9: does a method trigger a ledger transfer through an `Effect`? |

---

## 5. Risks (what gets worse)

- **R1 Flag day.** ID-1 changes `reqTy`, so every package id changes and every installed package and
  object refuses to load. Re-genesis is free. But kernel-sim, host-sim and lang-journey fixtures re-emit,
  and any falsifier that mutates a fixture must re-assert its mutation happened (minted: a falsifier
  that stopped falsifying).
- **R2 Fail-open by omission** (ID-1, ID-3). Only `lawOf` forces the birth, relaw and authority
  clauses; hand-written core terms keep the holes. A reviewer reading a package must check them.
- **R3 Meaning-theorem cost** (ID-2). Symbolic `BigStep` over record environments is untried here. A
  lane that stalls on it must not fall back to case tables relabelled as verification. The fallback is
  smaller combinator lemmas.
- **R4 Docs friction** (ID-6). A blocking docs lib adds a file to every interface change. Lanes will
  be tempted to delete the ascription to go green; `gates/docs.py` must make that red. The glossary can
  be complete and wrong.
- **R5 Per-instance stdlib** (ID-2). Storage per object type; membership change = migration.
- **R6 Stale-tree assembly.** Everything the scouts cite by line is at the 19:25 tree. A builder who
  lifts a scout file verbatim inherits `Req.mk` with 2 fields, `encodePackage : ByteArray`, `legOf`,
  `Turn.legs` and `ctxWith prog reg`. The probe file is the only lifted code that ran at main (at
  943cab7's identical receivers), and even it needs a four-line port for ccec081's Journey helpers.
- **R7 Deferral smell on ID-9.** "Build it with LEDGER's first effect" is a phase ordering. If LEDGER
  instead decides that value moves only by client-signed ledger calls, then ID-9 is never built and
  LANG-13 stays open forever. The guard: LANG-19 is written NOW, with a decided shape, and LEDGER's
  design must answer it by name.
- **R8 Lib cycles persist** (Codec<->Kernel, Host<->Protocol) [ran]. Not this area's to fix, but
  `Docs/` must import only def modules so that it adds no third cycle.
- **R9 Tracked `__pycache__`.** `gates/__pycache__/*.pyc` are tracked and dirty in wt/lang [read];
  every lane that runs a gate dirties them. That is GATES' to fix; I mention it because it makes
  `git status` noisy enough to hide a real stray edit.

---

## 6. FIRST BUILDER BRIEF — LANG-3 (law stdlib and occasion), model: opus

> If a LANG lane is live, send this to it with SendMessage. Do not spawn fresh. LANG-2's continuation
> is `~/dev/redregg/work/LANG-LOG.md`; read it whole first.

Repo `~/dev/nanodregg`, main only.
- **Edit only in `~/dev/nanodregg-wt/lang`.** Refresh it with `git checkout -q --detach main` first; it is at 48041e0 and idle since 22:07. NEVER read, build or run from `~/dev/nanodregg` itself: its tree and `.lake` are 87 commits stale, and its index stages deletions.
- **Commit only with `scripts/commit -F MSG PATHS…`** (it builds, runs census, and lands by CAS onto main). Use a `lang:` subject and a `SIZE:` line for every count that rises. Use `--cross-layer REASON` only for the KERNEL half of item 1, and only if KERNEL agrees.
- **Decisions** go in `decisions/lang.md` as LANG-19+ (the decision, alternatives, why, CRITIQUE, META-CRITIQUE). Every theorem statement gets a second-agent vacuity read before it lands (law 6). No `#guard`, no `sorry`.

**Ground truth (real signatures at main ccec081; quote these, do not reconstruct them):**
- `Kernel/Receive/Call.lean`:
  - :161 `structure Req (D) where agent principal : D; notBefore validUntil : Nat`
  - :172-180 `structure Program` with `judge : Pinned D → Option D → List D → Slots → Slots → Req D → Except (Refusal D) Unit` and `run : … → Except (Refusal D) Slots`
  - :244 `def reqOf (u : Unsigned D) (principal : D) : Req D`
  - :129 `Refusal.name`
- `Kernel/Receive/Derive.lean`: the four judge sites are :159 (create, `state state`), :178 (write), :191 (law, `stateOf cell` twice) and :210 (invoke). `principalOf` is at :82.
- `Lang/Package.lean`: :27-28 `reqTy := .record [agent, notBefore, principal, validUntil]`, :34 `lawTy`, :37 `methodTy`, :185 `encodePackage : Package → Option ByteArray`.
- `Lang/Program.lean`: :49 `decodeText` (the repr leak), :168 `reqOk`, :172 `reqData`, :189-207 `judgeOne`, :209 `judge`.
- `Lang/Proofs/BigStep.lean`: :32 `BigStep lib env t (r : Except Fault Val)`, with `run_bigStep` at Agree.lean:282 and `bigStep_run` at Complete.lean:205.
- **KERNEL is editing `Lang/Journey.lean` cross-layer** (wt/kernel has it dirty, making Journey generic over Sim parameters). Pull main before every edit to Journey, and tell KERNEL when you touch it.

**Open, in order:**

1. **ID-1 `Req.occasion` (with KERNEL).**
   - Send KERNEL the exact `Occasion`, `Req`, `reqOf` signatures from ASSEMBLY-lang-docs §3 ID-1, plus the probe output (§1) as evidence. KERNEL owns `Req` and the four call sites.
   - LANG's half: `occasionTy`, `reqTy`, `reqData`, `reqOk`, and re-emitting `Journey.ownedText`.
   - Rows in lang-journey that must go from admitted to refused: G1's E11/E12, and the probe's H1b/H1c and H2d/H2e. The plant is a program whose judge ignores `occasion`; those rows must flip back to admitted under it.
   - Commit message: what shape changed (`reqTy`, so every package id), what re-genesises, what now refuses to load.

2. **`runLaw`.** Factor the inner `run … extract verdictTy` of `judgeOne` into `Lang.Program.runLaw` (definitions only). It is the one law runner the receiver and every test call. Do not lift G1's `judgeLaw`.

3. **`Lang/Std.lean`.**
   - Lift the combinators from `~/dev/redregg/work/nanodregg-scout/probe-lang-occasion.lean` (they are G1/Laws.lean restated at main's `reqTy`). Port its Journey calls for ccec081: `ctxWith prog`, no `reg`, `Sim.dc.bytes`.
   - Make `lawOf S birth relaw change` case on `req.occasion` with no default arm.
   - Laws: `ownerActs` (principal), `ownerSigns` (agent), `bounded`, `allowlist`, `quorum` (state `{approvals, proposal, total}`; approvals bound to the proposal; birth requires `approvals = 0`; relaw requires a quorum), `windowed` (copy the probe's: `validUntil / W = notBefore / W`, `new.epoch = notBefore / W`), and `anyone`.
   - `pkgOf` requires one authority law (ID-3).
   - Put the generators in a def module and the theorems in `Lang/Proofs/Std.lean`.

4. **`Lang/Proofs/Std.lean`.**
   - Meaning lemmas for `guard`, `allOf`, `anyOf` and `lawOf` over `BigStep`, then `quorum_change_needs_k`, `quorum_birth_empty` and `windowed_lands_in_epoch`, stated over all `Data` inputs at the law's state type.
   - Prove compositionally. Do not `decide` through `run` on a 150+ node term (the reduction-bomb shape).
   - A vacuity reviewer reads each statement: no hypothesis may be unsatisfiable, and the conclusion must mention the guarded field.

5. **Rows.** Add lang-journey L8+: the H1/H2 refusals, the H3 sequence (including the `outsideWindow` cheat), and quorum's proposal binding (approve for 9, commit 77: refused). Each row has a plant with its line.

6. **ID-5, LANG's part.**
   - `CheckError.name` + `name_injective`.
   - `decodeText` uses `Codec.Refusal.name` once CODEC lands it (ask CODEC; until then leave the repr and name the dependency).
   - A typed `ReadRefusal` with a position for `Lang.Read`.

7. **Tooling (after 1-6).** `mutants` from `~/dev/nanodregg-scout/G1/Tests.lean:11-24`, restated as a tooling module (a path component that `tree.Module.is_tooling` counts as tooling) behind a `law-mutants` exe. It prints the kill ratio and survivors per stdlib law. It is evidence, never a gate verdict on meaning.

8. **LANG-19 decision entry (write now, build later).** Cross-object calls take G2's effects-as-data shape, restated over touches (ASSEMBLY §3 ID-9). `Body.invokeAll` is rejected, with the reason. The build trigger is LEDGER's first receiver a method triggers. File a `cv task` so the trigger is tracked.

**Lift / ignore:**
- LIFT: `~/dev/redregg/work/nanodregg-scout/probe-lang-occasion.lean` (whole); G1/Laws.lean's combinator and quorum shapes; G1/Tests.lean:11-24 (`mutants`) and its case tables as test data; G2/Cross.lean's `visit`/`visit_distinct`/`foldlM_inv` as the PROOF SHAPE for item 8.
- IGNORE: G1 `rateLimit`, `judgeLaw`, `Pkgs.lean`'s byte counts and `E2E.lean`'s 2-field `Req`; G2's `ProgramFx`, `Fault`, `Demo` and `legOf`; any scout's line numbers.

**Box safety:**
- Mac only, no hbox.
- Build the narrowest closure: `lake build Lang.Std Lang.Proofs.Std`, then `lake exe lang-journey`. No unfiltered suites. Foreground-wait builds.
- Verdicts come from artifacts (the exe's exit code and its last line), never from a wrapper's exit status (`tee | tail` exits 0).
- Never `git stash`; never `git add -A`; never stage into the default index.
- Disk pressure is Ember's: stop, report a ranked `du`, delete nothing that is not yours.

## Stopping processes: PID file or nothing (incident 2026-10-10)

A subagent ran `pkill -f "cat" -u ember` to clear its own stuck `cat`. `-f` matches the whole
command line, every app lives under `/Appli**cat**ions`, and 44 of my apps and agents got SIGTERM.
- **Never kill by pattern.** No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`.
- **A process you started is stopped by the PID in its PID file**, and only that. Every detached job
  writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead.
- If you must look first, `pgrep -fl` and read the list; it is never the argument to a kill.
- Every subagent brief you write quotes this block verbatim.

**Report to ROOT** on events only: item 1 agreed with KERNEL, the first green row, a theorem that will
not state without weakening, and the handoff (append to LANG-LOG.md before 350K tokens).

---

## 7. Second brief, sketch — DOCS-1 (after LANG-3's item 1 lands, so the glossary starts on the new `Req`)

> This is ID-6's charter row, as a brief. Use the same worktree discipline, in `~/dev/nanodregg-wt/docs`
> via `scripts/worktree docs`, with an OWNERS row `Docs/ DOCS` plus per-layer rows. Quote the PID-file
> block verbatim.

1. **`lean_lib Docs` (default target)** and `Docs/Boundaries/<Layer>.lean`, seeded from D1's 21 ascriptions (`~/dev/nanodregg-scout/D1/Boundaries.lean`) restated at main. Fix the two that drifted [ran]. Each layer owns its file through OWNERS.
2. **`Docs/Glossary/<Layer>.lean`** from D3's `Explain.lean` (`~/dev/nanodregg-scout/D3/Explain.lean`). Every entry's name is `r.name`; the match is total with no wildcard. It must compile against main, where it currently fails on 4 Refusal, 1 Reject and 1 Codec constructor [ran].
3. **`Docs/Tour.lean` + `docs-tour` exe**, from D3's Tour, driving the `host` exe's member commands where they exist (`host genesis/serve/follow` at main). Each step's outcome name is the expectation; register it as a row.
4. **`docs/ARCHITECTURE.md`** from D1's ARCHITECTURE.md with every count and every `path:line` removed. It cites names, and every fenced signature has its ascription. `gates/docs.py` checks the fences. Replace D1's `cites.py` with name existence.
5. **Correct `Lang/Journey.lean:16`** (L5's "the kernel's authority check"), as a message to LANG.

LIFT: D1 Boundaries.lean, layers.py, the theorem/instance/plant/premise matrix (ARCHITECTURE.md §6),
and the "does anything run this hop" column. D3 Explain.lean and Tour.lean. D2's three questions as
ID-7 asks to PROTOCOL.
IGNORE: D1 `head/` and `cites.py` line pinning; D2 matrix.py; D3 TUTORIAL.md text; every scout count.

---

## 8. What I did not do

- I did not port G1's E2E or G2's Cross to main. The probe covers the claims they rest on.
- I did not prove any theorem.
- I did not read LEDGER's design: it does not exist yet.
- I did not re-check D1's `Op.receiver` names at ccec081.
- I did not run cargo, host-file-sim, or any test suite.
- I wrote no `cv task`. ID-4 and LANG-19's build trigger need one; filing them is the builder's item 8, or ROOT's.
