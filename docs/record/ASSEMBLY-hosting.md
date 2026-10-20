> record copy of redregg/work/nanodregg-scout/ASSEMBLY-hosting.md, 2026-10-16; the lane logs stay in redregg

# ASSEMBLY — hosting (Opus evaluator, 2026-10-16/17)

Area: everything that runs ON the operator's box for someone else: hosted grains (SPK apps), the hosted
Hermes resident, the provider-key broker, and friends reaching the Store over ssh. Scouts H1–H5 under
`/Users/ember/dev/nanodregg-scout/`.

Marks: **[read]** I read it in the file named; **[ran]** I ran it this session and saw the output;
**[assumed]** neither (stated so it can be checked). Every decision carries CRITIQUE and META (law 10).

## 0. The headline finding: every scout built against a stale checkout

**[read]** `~/dev/nanodregg` (the primary checkout) is not main. Its index stages deletions of
`Codec/Deployed.lean`, `Codec/Hash.lean`, `Codec/Kernel.lean`, … and its working tree lacks
`Lang/Read.lean`, `Protocol/Command/*`, `Protocol/Envelope.lean`, `Host/Open.lean`. CHARTER (main) says
it "is nobody's editing surface"; layers work in `~/dev/nanodregg-wt/<layer>` and land by CAS. All five
scouts compiled with `cd /Users/ember/dev/nanodregg && lake env lean …`, so they built against a
mirror of the tree as of about 20:00. I read main at **43c4d58** (22:54) via `git archive main` into my
scratchpad, and compiled the scout Lean files against current oleans
(`~/dev/nanodregg-wt/host/.lake/build/lib/lean`, tree at 24d0f79) **[ran]**:

| file | result vs main | why |
|---|---|---|
| H1 `Grain.lean` | compiles | no nanodregg import |
| H1 `GrainPkg.lean` | **4 errors** | `Wire.encodeData`/`encodePackage` now return `Option ByteArray` |
| H2 `Broker.lean`, `BrokerProofs.lean` | compile | only `Codec.Stream` |
| H4 `H4Read.lean`, `H4Theorem.lean` | compile | `checkInstall_importFree` still holds on main |
| H4 `H4Resident.lean` | **6 errors** | same Option change |
| H5 `Repl.lean` | **8 errors** | same, plus `Wire.depthMax`/hand wire gone (LANG-17, d96b08a) |

Scout claims about what does not exist were false at main when the scouts wrote them **[read]**:

| scout claim | main |
|---|---|
| H3: "neither CLIENT-12 nor `idleMsMax` exists" | `decisions/client.md` CLIENT-12 chose option B (H3's design). `Protocol/Table.lean` has `Bounds.idleMsMax := 300000` (PROTOCOL-12), not H3's 30000. **But** `Emit/Rust.lean` `bounds` does not emit it, so `generated.rs` has no `IDLE_MS_MAX`, and H3's emit ask stands. |
| H4: "no Lang/Read; `Protocol.Command` absent; no install verb" | `Lang/Read.lean` (213 lines, LANG f587ab3). `Protocol/Command/Verb.lean` has `install TEXT` read by `Lang.Read.readPackage`. The `hermes` row runs `install` in loopback. |
| H5: "only `Kernel.Sim.env` (toy FNV) exists" | `Codec/Deployed.lean` (CODEC-15) is the deployed Env/Ctx. H5's printed `bytes[597]` are the deleted pre-`Codec.Tree` wire. |
| H2: "Ember ruled KEY-CUSTODY option A" | **No record**: `DECISIONS.md:340` still says "OPEN, for Ember"; the CLIENT, PROTOCOL and DELETE-RUST logs say open. The scout's brief said so; nothing in the tree does. This is **[assumed]** until ROOT confirms. |
| H1: "`World` has no id" | True at main (`Kernel/World.lean:89`; `genesis` at :145 hashes `name` into `chain`). `Receive.worldId` (Call.lean:251) is one constant for every Store (`hash domWorld ""`), so it is not a store identity. |

What survived: the **Rust** ground truth. `sandbox/src/lib.rs`, `client/src/mux.rs` and
`client/src/frame.rs` are byte-identical between the stale checkout and main **[ran: diff]**, so
H1's launcher, H2's crate and H3's attach were built against the real Rust.

Consequence for the builder: start from main, in a worktree. Lift scout **ideas and theorems**; do not
lift Lean files as files.

## 1. Per-scout verdicts

### H1 — grain lifecycle as Lean policy
**Re-verified.** **[ran]** `Grain.lean` compiles clean on main oleans (1.5 s). **[ran]** I rebuilt the launcher
probe in my scratchpad with H1's `grain-launch` binary and a hand-written plan. Result: `vol-write OK`,
`neighbour-write`, `neighbour-read` and `pkg-write` each `Operation not permitted`. The tampered plan is
refused `confine: exposed: …/worlds/bb reaches hidden …/worlds/bb`. **[ran]** A Rust std binary
(grain-launch itself, copied into pkg/) aborts under the floor with `failed to allocate a guard page:
Invalid argument (os error 22)`, so H1's critique 5 is confirmed.
**[read]** The grain row on main (`Protocol/Rows.lean:319-331`) is **blind**. Its drive is
install(0) / `grain start`(1) / `grain mount b`(2), and its plant is `.caught .skipJudge 2 .ok`. Skipping
the law judge cannot make line 2 pass, because `crossWorldVolume` is not a law verdict. It also declares
`kinds := ["install","invoke"]` with no invoke line, which PROTOCOL-15's kinds check will reject the day
the row is unblocked.

KEEP
- `edges` as the single lifecycle source. Keep `step`, `step_table`, `edges_deterministic` and
  `no_double_start`, and the rule that the law is generated from the edge list with `legalPairs_iff_step`
  and `methodTable_iff_step` proved (Grain.lean). Restate them in `Hosting/Lifecycle.lean`.
- The born-only-initial rule (`create` judges old = new = seed, so the law admits `initial→initial` and no
  other self-pair) and its plant: under skip-judge, the born-running create is admitted (GrainPkg G3/PLANT).
- `plan` as a total Lean function whose `Plan` mirrors `sandbox::Policy` field for field. Keep
  `plan_startable` and `plan_paths` (everything allowed lies under the grain's world root, every hidden
  path is another world's root).
- The glue discipline of `launch/main.rs`: a Lean refusal ends the run, `Exposed` is an independent second
  barrier, and an unconfined control keeps the denials non-vacuous.
- "The World holds DESIRED phase only; observed process state is never World state."

DISCARD
- One method `fire : nat` with an event code. KERNEL's `Right.invoke (method : Nat)` grants per method
  (Call.lean:30). One method per event lets an owner grant an operator `invoke:start` but not `stop`,
  with no law code. H1 critique 8 ("hosting needs operator may start, only owner may stop … untested")
  is answered by the kernel that already exists. `fire` makes that unrepresentable.
- `ownerLaw` comparing `req.agent` to the owner. `invoke` derives `principal` through the grant chain
  (`Derive.lean:204`), so the law must compare **`principal`**. Checking `agent` refuses every grantee,
  which is G6, the behaviour H1 called a silent policy choice.
- `resolve` and its refusals `crossGrainVolume`, `notAVolumePath`, `volumeComponent` and `volumeTooDeep`,
  with `resolve_sound`. In the assembled design no one ever sends a volume request: the volume is a
  function of (store, grain). A refusal function with no caller is the no-op law 1 / CLAUDE.md forbids. If
  a row ever needs named sub-volumes, it comes back with that row.
- The argv/TSV process boundary and `lean --run` per call (2.8 s). Law 2: the boundary is stdio frames to
  a compiled Lean exe.
- `Own.world` as a caller-supplied string. The controller is per Store, so its world label is a
  deployment constant, not an argument (HOSTING-4).
- The Interface-1 ask for `World.id` in KERNEL. It is not needed (HOSTING-5). The real cross-world issue
  is a different one (HOSTING-10).

NEEDS REWORK
- `GrainPkg.lean` itself. Port it onto main's `Option` encoders and onto LANG text (`Lang.Read`), so the
  package is a `world/` text file rather than Lean constructors. Use one method per event, and the
  principal-owner law.

### H2 — provider-key broker
**[ran]** `Broker.lean` and `BrokerProofs.lean` compile on main oleans. **[read]** `EInv` is not vacuous: a
satisfiable disjunction (`frozen ∨ within bounds`), and the scout's plant (delete the `overSpend` check)
breaks `inv_decide`. `run-output.txt` shows every named refusal **[read; I did not re-run the HTTP demo]**.

KEEP
- `decide`/`settle`/`abort` with reserve-the-worst-case-then-settle, overrun ⇒ `frozen` by name, `EInv`
  and `inv_decide`/`inv_settle`/`inv_abort`/`inv_roll`, `frozen_never_granted`, `unallowed_model_refused`.
  These are the in-lease meter (HOSTING-7).
- Identity by per-resident socket, with Rust prepending the resident digest and a sum-tag prefix read off
  the codec's own encoding (`generated.rs` `ASK_PREFIX`/`SETTLE_PREFIX`/`ABORT_PREFIX`), so a resident
  cannot forge a settle, an abort or another resident.
- One generated refusal table with distinctness theorems. `keyEchoed` withholding the body. The 0600
  key-file refusal.

DISCARD
- The meter as broker-process memory (restart refunds the window). Replaced by a World lease (HOSTING-7).
- `nat32`/`nat64` as `refine` over `Nat` (not Lawful past 2^64, by H2's own note). Use CODEC's bounded
  carriers (CODEC-12).
- `Host.Log.le32`/`ofLe32` reuse. Those were deleted on main (HOST-5 twin; HOST-2 dbf6f04).
- The hand-written Rust `parse_verdict`. Emit it from the Lean codec, as `Emit/Rust.lean` does for
  layouts.
- Building the key-holding half before ROOT/Ember confirms KEY-CUSTODY (pause list item 1). Option C
  needs this broker too ("the broker must still hold a real key at the moment of the call", DECISIONS.md
  KEY-CUSTODY C), so A and C share it and only B deletes it. The Lean core is safe to build. The key file
  is not, until ruled.

NEEDS REWORK
- `Policy` keyed by `Digest`. On main a resident is a **member** (`hermes` row), so the key should be the
  member id `D`, and the policy should be the lease object's state, not a broker list.

### H3 — nd-attach over ssh
**[read]** `t1.out` passes everything; `t2.out` gives the latency and cap numbers. **[read]** HEAD `mux.rs`
`forward` returns on client EOF and tells the child nothing (fn `forward`). `serve` is at ~line 63, not
:46 as cited, but has the same signature. **[assumed]** I did not re-run the private sshd.
**[read]** The "256 served against 64" number is from H3's *python fake host*, which has no cap. Under the
real `nd-supervise` the 65th connection is refused. The real defect is **fairness**, not overrun: one
friend key can take all 64 slots and starve the local Hermes and the other friends.

KEEP
- The wire: mux.rs's child frame (`u32 conn ‖ op|status ‖ payload`) is the ssh link format. Add a close
  tag each way, as Table rows. One mux serves both the supervisor and the member-side link, and
  `nd-link.rs` is deleted.
- The per-connection and per-channel idle watchdog, in `nd-supervise`'s mux (one place reaps), driven by
  an emitted `IDLE_MS_MAX` (300000, the value on main).
- `restrict,command="nd-attach SOCK"` and the t1 probes (key→socket routing, `SSH_ORIGINAL_COMMAND`
  ignored, `-L` refused). The t2 cap probe becomes a plant: k channels from one key must not hold more
  than `connsPerKeyMax` (HOSTING-8).
- "No Rust on this path branches on key or op; the World grant is the only authority."

DISCARD
- `--idle-ms N` on the authorized_keys line (an operator constant: law 2).
- The 30 s default (main already ruled 300000).
- Scout constants `CLOSE_OP=0`/`CLOSED=255` as Rust literals. They become `Protocol.Link` rows (values
  kept).

NEEDS REWORK
- nd-link's lifecycle (it exits and removes `host.sock` when the channel idles). Respawn ssh on demand
  inside `nd-supervise -- /usr/bin/ssh -T box` (CLIENT-12's own shape). The supervisor already
  restarts its child on close, and that is the one restart path.

This is CLIENT's work (CLIENT-12 is CLIENT's decision), not the new layer's. Route H3 to CLIENT.

### H4 — the resident authoring loop
**[ran]** `H4Read.lean` and `H4Theorem.lean` compile on main. **[read]** `checkInstall_importFree` is a real,
modest statement: for import-free bytes the receiver's `checkInstall` *is* `checkWith []`. It is not
vacuous; the premise `decodePackage b = .ok p` is satisfiable. **[read]** main's `Lang/Read.lean` refuses with
`Except String` (`abbrev P α := Except String α`), so the one reader on main breaks law 7. H4's 21
named `ReadError` constructors with offsets are the fix.

KEEP
- The named reader refusals with byte offsets (H4Read's `ReadError`), as an **edit to main's
  `Lang/Read.lean`**, not a second reader. LANG owns it.
- `checkInstall_importFree`, lifted into `Lang/Proofs/` by LANG.
- The **three-process split**. (1) A model-driving process: no seed, no sockets but its own pipe and
  the broker. (2) The resident's `nd` (custody). (3) The Lean Host and follow. This is CLIENT-8's
  invariant ("no process that parses untrusted bytes reads the seed") applied to model output. It refines
  CLIENT-7 ("Hermes runs nd inside one bwrap shape") into two confined processes.
- The probe form (`(probes (create …) (invoke A set 50 admitted (state …)))`) as the resident's own
  tests, run at the **Program** level (HOSTING-9).

DISCARD
- `blame` (a second traversal of `infer`). Both H4 and H5 wrote one. The fix is LANG's `inferE`.
- Silent row sorting **in the resident surface** stays LANG's call. H4's meta-critique (authors cannot
  predict bytes) is real, but main's Read already sorts, so it is a LANG decision to re-argue, not a
  hosting one.
- The dry run on a toy-parameter in-memory World (`Lang.Journey.go`). Main's follow already runs
  `World.admit` on the member's real World in `plan` (`plan_admits`, PROTOCOL-11). Program-level probes
  cover the law, so the toy World adds nothing.
- The outbox file as the resident's egress. Replaced by argv frames to its own nd (HOSTING-6). An outbox
  of package bytes only covers `install`, and the resident must also `invoke`/`write`/`grant`.

### H5 — the REPL
**[ran]** `Repl.lean` does not compile on main (8 errors). **[read]** H5's `session.out` is real for the stale tree.

KEEP
- `(eval TICKS t)` / `(cost t)` printing `value : type [used of budget]` or `fault after N ticks`. It is
  the author's budget feedback. `Outcome.used` exists.
- The ask for `inferE` with a constructor per failure and a path. H4 and H5 found it independently.

DISCARD
- The reader and elaborator (`Repl.lean` 1-205): a **third** reader beside main's `Lang.Read` and H4's.
- The print-then-read round-trip theorem. LANG-LOG item 7 already argued it is not needed: the bytes are
  what is checked. I agree, because the reader is trusted for nothing.
- The toy FNV id. Main's deployed Env exists, so an `ob` exe prints the real `romIdOf` under
  `Codec.Deployed`, or no id.

Route H4 and H5 to **LANG** as the reference prototypes of LANG-LOG's own open item 5 ("a `check` CLI
over Read + checkWith with named diagnostics").

## 2. The assembled system (one paragraph)

A **grain** is any process the operator hosts for a member: an SPK app, or a resident (Hermes). Its
lifecycle is an ordinary World object: a LANG package with one method per event (`start`, `stop`,
`remove`), generated from one edge list, with a law that admits only edges and a law that the principal
is the owner. The World holds desired phase only. A per-Store **controller** (a compiled Lean exe) opens
the Store read-only through `Host.openWith`, the follower's own open (HOST-16 key, never truncates). It
tails batches, and for each grain cell whose desired phase is `running` with no live child it emits
`launch(plan)`, where `plan` is a total Lean function of (store label, grain id, kind, entry). For a
grain whose desired phase is not `running` and whose child is live, it emits `kill`. The Rust parent
(`grain-launch`, hosting crate) spawns each plan through `sandbox::command` and reports exits back on
the Lean child's stdin. Observed state lives only in the controller's memory and in the OS process
table, never in the World. A **resident** grain's plan is two confined children. One is the model
driver: it sees its package, its volume and two sockets (its own `nd --stdio`, the broker). The other
is the resident's `nd` custody (Option 1 key record, CLIENT-13). The driver's only effect on the World
is argv frames that its nd runs through its own follow. The **broker** meters provider calls inside a
**lease**, an `invoke` on a per-resident budget object that the World admits once per window.
`EInv` bounds spend within the lease, and the object's law bounds leases per window, so a restart
forfeits and never refunds. **Friends** reach `host.sock` through CLIENT-12 B: one mux with a close tag
and an idle reaper, per-key slot bounds, and the World grant as the only authority.

## 3. Interface decisions (each: signature, owner, CRITIQUE, META)

### HOSTING-1 · A new layer HOSTING, not more of CLIENT
**Decision.** `Hosting/` (Lean: lifecycle, plan, controller decisions, broker decisions, resident profile)
and `hosting/` (Rust crate: `grain-launch`, `keybroker`). CLIENT keeps `client/` and `sandbox/` and
CLIENT-12 (nd-attach, mux close tag, idle reaper).
**Why.** The charter puts "SPK broker, grain runtime" in CLIENT's row, but CLIENT is custody and
transport under a 2,000-line ceiling (1,703 used, SIZE.md). A process that parses provider HTTP and
model output is a different trust domain from custody (CLIENT-7's own critique: "may deserve its own
small component"). The Lean half is not KERNEL (no receiver, no Body) and not LANG (it consumes LANG text).
**CRITIQUE.** An eighth layer adds an owner, OWNERS rows, a decisions file and coordination. The
grain row could be finished by CLIENT with ~300 Rust lines and a Lean file in `Protocol/`. A layer whose
first deliverable is a 200-line Lean file may be overhead (PROTOCOL-0's own critique of itself).
**META.** I am the evaluator writing the brief for the builder this decision creates; a clean row is
what makes my brief easy. Counter-check: the provider broker alone is a second custody (keys), which
the charter's custody rule says must not share a process or crate with the seed holder.

### HOSTING-2 · One hosted-process shape: `Grain` with kind `app | resident`
```lean
-- Hosting/Grain.lean (HOSTING)
inductive Kind | app | resident
structure Grain (D : Type) where
  id : D            -- the lifecycle object's cell id
  kind : Kind
  entry : ByteArray -- the package-relative program name; a clean component or refused
```
**Why.** Law 1: one launcher, one plan function, one lifecycle. minidregg's grain-runtime ran Hermes as
a grain. Two shapes (an "SPK broker" and a "resident runner") would be the P3 twin CLIENT-9 deleted.
**CRITIQUE.** A resident holds a member seed and an app does not. Putting both under one `plan` means
one function decides custody-bearing and custody-free launches, and a bug in the shared branch exposes
the seed. Separate types would make that unrepresentable.
**META.** The unification is elegant, and that is the bias. The test: `plan_paths` must also prove that
an `app` plan never names any workspace path (a theorem over the kind).

### HOSTING-3 · The lifecycle is a LANG text package with one method per event
```lean
-- Hosting/Lifecycle.lean (HOSTING; restated from H1 Grain.lean, then generated text)
inductive Phase | installed | running | stopped        -- `absent` = no cell; birth is `create`
inductive Event | start | stop | remove
def edges : List (Phase × Event × Phase)
def step : Phase → Event → Except Refusal Phase
def methods : List Label := Event.all.map Event.label  -- ["start","stop","remove"], index = Right.invoke n
def lifecycleText : String   -- (package (imports) (state (rec (phase nat))) … ) generated from `edges`
theorem step_table : … = edges
theorem method_iff_step : ∀ p e, Lang.run (lifecycle) (stateOf p) (index e) … = phase-of (step p e)
theorem born_initial_only : judge … old new = ok → old = new → old.phase = installed
```
The laws are `phase` (old→new ∈ edges ∪ {installed→installed}) and `owner` (`req.principal = owner`,
the owner read from KERNEL slot 1). `remove` = `installed|stopped → retired`: does KERNEL retire a
programmed object by method? **[assumed]**: not today. Until KERNEL says, `remove` is an edge to a
`removed` phase that the controller treats as absent.
**Owner.** HOSTING writes the generator and the theorems. The text is checked by LANG's `checkWith`, and
the file lives in `world/grain/Lifecycle` (the row already names that path).
**CRITIQUE.** `method_iff_step` over a generated Core4 term is a theorem about LANG's evaluator on a
specific term. If it is only provable by `native_decide` it needs an allow row (law 6), and H1's 16/16
differential was exactly the confession that it was not proved. A remove that does not retire the cell
leaves dead grain cells in the World forever (KERNEL-17: nothing is pruned).
**META.** One method per event is what I chose once I saw `Right.invoke n`. I am fitting the design to
the kernel I found, which is right only if the kernel's per-method grain is the right authority unit for
hosting. Per-(method, args) would need LANG-13 or args in grants.

### HOSTING-4 · The controller is a read-only follower in Lean; the launcher is Rust over stdio frames
```lean
-- Hosting/Controller.lean (HOSTING)
structure Live (D : Type) where grain : D ; since : Nat          -- the launcher's report, never World state
inductive Action (D : Type) | launch (g : D) (p : Plan) | kill (g : D) | refuse (g : D) (r : Refusal)
def reconcile (label : StoreLabel) (w : World D) (live : List (Live D)) : List (Action D)  -- ≤ grainsMax
theorem reconcile_launch_desired : .launch g p ∈ reconcile l w live →
    desired w g = some .running ∧ g ∉ live.map (·.grain) ∧ plan l (grainOf w g) = .ok p
theorem reconcile_kill_undesired : .kill g ∈ reconcile l w live → desired w g ≠ some .running
-- input: Host.openWith (HOST, existing; follower mode: never truncates) + a tail of new batch records
```
Rust `grain-launch`: reads `Action` frames (CODEC layout), runs `sandbox::command(policy, program,
args)`, writes `exited(g, status)` frames back. It holds the Store path and nothing else. Restart
backoff (`restartsPerWindowMax`, `crashLoop` refusal) is a Lean decision over `Live`.
**Why.** `read` is RESERVED (PROTOCOL-13), so H1's "broker calls a `read` kind" has no op. The operator
owns the Store files and the Store key (HOST-16: "serve and follow read it"). Opening the Store with
HOST's own open is one code path and needs no member key, no grant and no socket. Desired against
observed is H1's critique 1, answered: the World says what should run, the controller converges, and a
crash is a restart, not a World write.
**Asks.** HOST: a tail API over `Host.openWith`'s follower mode (`Tail.next : IO (List ByteArray)` of
new batch records, O(appended)) **[assumed name]**. CODEC: the `Action`/`exited` layouts.
**CRITIQUE.** The controller trusts the writer's derivations (it folds, it does not re-derive). That is
fine for the operator's own process, but it is a second replayer, against law 5's "the follower is the
only replayer". Crash-loop counters are state outside the World and die with the controller. A
controller restart relaunches everything that is desired, so a grain that must not double-start (one
holding a lock on its volume) needs a lifetime handle (law 4's lease amendment: an `flock` on the volume
held by the child).
**META.** "Observed is never World state" is the rule I like (HOST-8's meta says the same of the Host).
I have not measured whether members need to *see* "your grain is crash-looping". If they do, that is a
signed status Turn by the operator, i.e. observed state entering the World after all.

### HOSTING-5 · Volumes are a function of (store label, grain id); cross-world is structural, tested physically
```lean
-- Hosting/Plan.lean (HOSTING)
structure Plan where program : Path ; read write exec connect hidden : List Path   -- = sandbox::Policy
def plan (l : StoreLabel) (g : Grain D) : Except Refusal Plan
theorem plan_paths   : plan l g = .ok p → ∀ x ∈ p.read ++ p.write ++ p.exec, worldRoot l <+: x   -- H1, kept
theorem plan_app_no_workspace : g.kind = .app → plan l g = .ok p → ∀ x ∈ allowed p, ¬ workspaceRoot l <+: x
```
No `World.id` in KERNEL. The controller is per Store and its label is a deployment constant (a clean
component, refused otherwise), so no input can name another world. The m6grain property is tested
**physically**: the grain process tries to read and write `worlds/<other>` and must get EPERM (H1's demo
case 1, **[ran]** above). The plant is a plan that grants `worlds/` as read, which must turn the row red.
**Owner.** HOSTING; PROTOCOL rewrites the row (HOSTING-11).
**CRITIQUE.** `plan_paths` is about strings, not inodes (H1 critique 3): a symlink inside the volume
is caught only by deny-default. "No request surface" also means no shared volumes or grain-to-grain mounts
(Sandstorm's powerbox). The first row that wants them re-opens path requests.
**META.** Deleting `resolve` deletes the part H1 proved most about. I may be deleting proof mass to win
a SIZE count. The test is whether any row sends a volume path, and none does.

### HOSTING-6 · The resident: two confined processes; the driver's only egress is argv frames to its own nd
```rust
// sandbox/src/lib.rs (CLIENT) — the first network allowance, unix sockets only
pub struct Policy { pub read: Vec<PathBuf>, pub write: Vec<PathBuf>, pub exec: Vec<PathBuf>,
                    pub connect: Vec<PathBuf>, pub hidden: Vec<PathBuf> }
// macOS: (allow network-outbound (remote unix-socket (path-literal "<p>"))) per entry; nothing else.
// Linux: --bind-try <p> <p> per entry (an AF_UNIX path connects through a bind mount in a new netns).
```
```text
nd --stdio   (CLIENT): reads commandLayout frames (argv) on stdin, writes the `done` step's frame per
             command; each command runs exactly as `nd ARGV` would. Bounded by ARGV_BYTES_MAX and
             STEPS_PER_COMMAND_MAX; one command at a time.
```
Plan for `kind = resident`. Driver: `read` = pkg plus the resident runtime floor; `write` = vol;
`connect` = [nd.sock, broker.sock]; `hidden` = [the resident's ws, other worlds]. nd custody: `write` =
ws; `connect` = [host.sock, follow.sock]; `hidden` = [vol, other worlds]. The driver acts **as the
resident member** under its own grants. Consent for its own calls is its own follow (`plan_admits`). A
human's consent is needed only when the resident proposes something under the *human's* authority,
which is the human's nd signing it (H4's outbox case, now an ordinary `invoke` the human runs).
**Why.** H4's split is CLIENT-8 applied to model output. `nd --stdio` covers all eleven verbs, not just
install, and adds no Rust decision: argv goes to follow's one parser.
**CRITIQUE.** The model can make nd sign anything the resident's grants allow. That is by design, so the
grants must be narrow, and a sponsor who gives Hermes `mutate` on a shared object has given it to the
model. `connect` is the sandbox's first network allowance: a plant must prove an unlisted socket is
refused. The resident runtime floor is unmeasured. **[ran]** A Rust std binary aborts under today's
macOS floor, and Python (`/Library/Frameworks/Python.framework/...`) will need its framework prefix as
read+exec (CLIENT-9's own critique). Per the charter's law-2 amendment, that floor is a platform-fact
table with a no-over-allow plant and a recorded bisection, owned by the layer that touches the platform
(sandbox/, CLIENT).
**META.** "Hermes acts as itself, consent is its own follow" is the answer that needs the least new
machinery. I have not checked that Ember wants an unattended resident able to spend its grants without a
human in the loop. That is a product question.

### HOSTING-7 · Provider spend: a World lease per window, H2's meter inside the lease
```lean
-- world/hosting/Lease (HOSTING, LANG text): state (rec (window nat) (leased nat) (cap nat))
--   method lease : (rec (window nat) (amount nat)) → …   laws: window non-decreasing; same-window
--   leased + amount ≤ cap; principal = owner (the operator, who pays)
-- Hosting/Broker.lean (HOSTING; H2's decide/settle/abort, re-keyed by member id D)
def decide (b : Broker D) (lease : Lease) (now model maxTokens : Nat) (r : D) : Except Refusal (Broker D × Grant)
theorem spend_le_leases : Inv b → settledInWindow b r w ≤ leasedInWindow (World) r w     -- EInv + lease
```
The broker (a hosting process with an operator key that holds only `invoke:lease` grants: a bounded
operational key, recorded) submits one `lease` Turn per resident per window, at the first ask of the
window. Within the lease it runs H2's `decide`/`settle` in memory. A restart loses the lease's unspent
remainder (forfeit). It cannot re-lease past `cap` in the same window, because the World refuses it by
law.
**Why.** H2's process-memory meter lets a restart refund the window, and a Turn per call would put one
journal entry per model call into a journal that is never pruned (KERNEL-17). At ~1 call/s that is
86,400 entries a day. A lease is one entry per resident per window.
**Pause.** KEY-CUSTODY is open for Ember (pause list item 1). Build the Lean core and the lease package.
Do not build the provider-key file or the upstream forwarder until ROOT relays a ruling.
**CRITIQUE.** The World has no clock: `window` is the broker's claim, and the law can only check
monotonicity. A broker that advances windows early multiplies budget, and that broker is the operator's
own (the operator pays, so this is self-harm, but under BYOK it is the member's money and the operator
holds the key anyway). Spend is still only as true as the provider's usage report (H2 critique), and
`frozen` comes after the money is gone. The first call of each window waits on a submit.
**META.** The lease is the shape that makes both H2's theorem and "World is the ledger" true at once. That
is a two-birds design, and it should be measured: is a World Turn per window actually cheap on THE BAR
path, where the hosted Hermes shares the writer with two friends?

### HOSTING-8 · ssh: CLIENT-12 B as H3 built it, plus link rows, emitted idle, per-key slots
```lean
-- Protocol/Table.lean (PROTOCOL)
namespace Link
def closeOp : UInt8 := 0       -- toward the remote: this conn's client side closed
def closedStatus : UInt8 := 255 -- back: the remote side closed (EOF, idle, or refused for a bound)
end Link
theorem link_disjoint : Link.closeOp ∉ Op.all.map Op.code ∧ Link.closedStatus ∉ Status.all.map Status.code := by decide
namespace Bounds
def remoteKeysMax : Nat := 8
def connsPerKeyMax : Nat := 6
def localConnsReserve : Nat := 16
end Bounds
theorem remote_fits : Bounds.remoteKeysMax * Bounds.connsPerKeyMax + Bounds.localConnsReserve ≤ Bounds.connectionsMax := by decide
```
`Emit/Rust.lean` (CODEC) emits `IDLE_MS_MAX`, `CONNS_PER_KEY_MAX` and a `link` byte module. `mux.rs` (CLIENT)
sends `closeOp` on client EOF, routes `closedStatus`, and reaps idle connections. `nd-attach KEYLABEL SOCK`
(CLIENT, ~30 lines over the mux) holds at most `connsPerKeyMax` connections across all of that key's
channels, through flock'd slot files `attach/<label>.<i>`. Each lock is held for the connection's
lifetime: the lock IS the handle (law 4's amendment). The plant is H3's t2: four channels from one key
must hold ≤ `connsPerKeyMax`.
**CRITIQUE.** A key label on the authorized_keys line is an operator-written string that sshd trusts, so
a mislabelled line shares a friend's slots. The numbers 8/6/16 are chosen to make 64 add up, not derived
from a row (PROTOCOL-8's meta-critique, again). There are now two revocation planes, ssh key and World
grant. Admission must stay a strict superset of authority (H3), and a row should show a revoked grant
refused over a still-valid key (CLIENT-12 already asks for it).
**META.** I accepted H3's reuse of the mux wire because law 1 favours it. H3's meta-critique (a
purpose-built link with flow control might be better for 256 KiB frames) is untested in both directions.

### HOSTING-9 · Authoring is LANG's: `inferE`, named reader refusals, `ob`, Program-level probes
```lean
-- Lang/Check.lean (LANG)
inductive TypeFault | unbound (i : Nat) | notFunction (got : Ty) | argMismatch (want got : Ty)
  | notBool (got : Ty) | branchMismatch (a b : Ty) | primOperand (p : Prim) (got : Ty)
  | noField (l : Label) (have_ : List Label) | rowNotAscending | …     -- one per `infer` failure
structure TypeError where path : List Nat ; fault : TypeFault
def inferE (Δ Γ : List Ty) : Term → Except TypeError Ty
theorem infer_eq : infer Δ Γ t = (inferE Δ Γ t).toOption      -- infer kept as the projection
-- Lang/Package.lean: CheckError.illTyped (e : TypeError)
-- Lang/Read.lean: abbrev P α := Except ReadRefusal α  (was Except String); ReadRefusal.name, name_injective
-- Lang/Probe.lean: def probe (p : Package) (s : State) (m : Nat) (args : Data) (r : Req D) : Verdict-or-state
-- lean_exe «ob»: check / eval TICKS / cost / probe, printing deployed romIdOf (Codec.Deployed) or no id
```
**Why.** Every authoring tool H4/H5 built needed these, and each built a twin (`blame`) to get them.
Probes at the Program level need no signatures and no World: a probe is (state, method, args, Req) →
verdict, which is exactly what laws judge. Authority checks are the kernel's and are covered by follow's
real `plan` at submit time.
**CRITIQUE.** `inferE` changes the checker's core definition, and every `Proofs/Check` theorem is
restated over it (LANG's cost, not hosting's). Program-level probes miss everything that depends on
KERNEL (grants, pins, charge), so a green probe still means "the law says what I said", which is H4's
self-grading exam. Named reader refusals with offsets are a UX for an LLM author. Law 7 justifies them,
but a resident could also just retry.
**META.** Two scouts asked for `inferE`, which makes it look settled; both were LLMs writing for an LLM
author, the same bias H4 named.

### HOSTING-10 · A signed call does not bind its World (ask of KERNEL)
**[read]** `Unsigned` (Call.lean:65) has no world field. `checkSignature` verifies over `unsignedBytes`
alone (Derive.lean:17). Member ids descend from `founderId X name i = hash(domFounder, name ‖ i)`
(Follow.lean:30). So two Stores genesised with the same `name` and the same founder keys accept each
other's calls. One operator hosting many Stores for one person is exactly that setup.
**Decision (hosting side, now).** The controller and the hosting genesis script refuse a genesis name
that is not 32 fresh OS-random bytes ‖ label (`nameNotFresh`).
**Ask of KERNEL.** Either a `world : D` field in `Unsigned` (the genesis chain), checked in `receive`, or
a theorem that distinct names give disjoint member-id spaces, plus the operator rule above.
**CRITIQUE.** Adding a field changes every signed call and every row fixture (a re-genesis, which is
free). The operator rule alone is a convention, which CLAUDE.md calls a defect when a check would do.
**META.** I found this by reading for hosting, so I may overweight a multi-Store operator that no row has
yet.

### HOSTING-11 · The grain row, rewritten (with PROTOCOL)
Drive: `install world/grain/Lifecycle` → `create @grain` (binds the object; phase installed) →
`invoke @grain start` ok → `invoke @grain start` **lawDenied** → owner `grant @grain @operator invoke:0`
→ operator `invoke @grain start --via @g`… (after a stop) ok → operator `invoke @grain stop --via @g`
**noGrant** (the grant was invoke:0 only). Then the controller converges, and the grain probe gets
EPERM on `worlds/b`. Plants: `.caught .skipJudge <second start> .ok` (laws matter), and the launcher
handed a plan with `worlds/` read must turn the probe red. `kinds := ["install","create","grant","invoke"]`.
**CRITIQUE.** The physical half (controller, probe) is not a loopback row; it needs a `.exe` driver the
way `lang-journey` is. A row that mixes member commands and a process probe is two rows' worth of
mechanism. **META.** I am rewriting another layer's row because it is blind; PROTOCOL may prefer to split it.

## 4. Charter rows

| layer | owner | owns | must never | first deliverable |
|---|---|---|---|---|
| HOSTING | BUILD-HOSTING (Opus) | `Hosting/` (Lean: Lifecycle generator + theorems, Plan, Controller decisions, Broker decisions + lease, resident profile), `hosting/` (Rust crate: `grain-launch`, later `keybroker`), `world/grain/`, `world/hosting/` package texts, `decisions/hosting.md` | hold a member seed in any process that parses model output or provider bytes; keep grain phase, pid or volume lists as truth outside the World; add a Body constructor or a receiver (KERNEL's); add a reader or checker (LANG's); hold a provider key before Ember rules KEY-CUSTODY; run anything unconfined ("no fallback", CLIENT-9) | `Hosting/Lifecycle.lean` + `Hosting/Proofs/Lifecycle.lean` (edges, step, generated text checked by `Lang.Package.checkWith`, `method_iff_step`, born-only-initial, skip-judge plant), `Hosting/Plan.lean` + proofs (`plan_paths`, `plan_app_no_workspace`), and a `hosting-sim` exe whose plant is red by name |
| CLIENT (amended) | BUILD-CLIENT | + `Policy.connect`; + `nd --stdio`; + CLIENT-12 B (`nd-attach`, mux close tag, idle reaper, per-key slots); + the resident runtime floor table | grow an "SPK broker" or "grain runtime" (moved to HOSTING) | mux close + idle with H3's t1/t2 as plants |
| LANG (asks) | BUILD-LANG | `inferE`, `ReadRefusal`, `Lang/Probe.lean`, `ob` exe | a second reader | `inferE` with `infer_eq` |

New deliverables in existing layers: PROTOCOL `Link` rows + `remote_fits` + the grain row rewrite; CODEC
emits `IDLE_MS_MAX`, `CONNS_PER_KEY_MAX`, `link`, `Action`/`exited` layouts; HOST a follower tail API;
KERNEL answers HOSTING-10 and whether a method may retire its object. GATES adds OWNERS rows
`Hosting/ HOSTING`, `hosting/ HOSTING`, `world/ HOSTING` (assumed: `world/` is unowned today), and
`decisions/hosting.md HOSTING`.

## 5. Risks (what gets worse)

1. **A new trust surface on the box.** `grain-launch`, `nd-attach` and (later) `keybroker` are new Rust
   that runs as the operator, reachable by friends (attach) or by model output (broker). Rust lines rise
   by ~300–500.
2. **The first network allowance in the sandbox** (`connect`). A profile bug that allows all
   `network-outbound` is silent unless the plant runs on every platform. The Linux branch has never run.
3. **The resident floor will be wide.** Python/Node need framework prefixes, and **[ran]** Rust std
   aborts today. Each widening is a platform-fact row with a plant, or it is a hole.
4. **An unattended member with grants.** A hosted Hermes can make its nd sign anything within its
   grants. A sponsor's careless `mutate` grant goes to the model.
5. **Second replayer.** The controller folds the log beside `host follow` (law 5 tension).
6. **Journal growth.** Leases add one never-pruned journal entry per resident per window (1,440/day at 60 s).
7. **Cross-Store replay** (HOSTING-10) until KERNEL answers. Today it is mitigated only by a naming rule.
8. **Keys.** The broker's operational key and the controller's lack of one are both custody choices,
   recorded but not ruled. Provider keys remain Ember's.
9. **Stale-mirror risk repeats.** Any lane that builds in `~/dev/nanodregg` reproduces section 0.

## 6. FIRST BUILDER BRIEF — BUILD-HOSTING (Opus)

```
You are BUILD-HOSTING, a new nanodregg layer (ROOT must add the charter row and gates/OWNERS rows
`Hosting/ HOSTING`, `hosting/ HOSTING`, `world/ HOSTING`, `decisions/hosting.md HOSTING` before your
first commit — ask ROOT by SendMessage if they are absent; do not edit OWNERS yourself).

GROUND TRUTH FIRST. ~/dev/nanodregg (the primary checkout) is STALE and nobody's editing surface: every
hosting scout built against it and three of their Lean files no longer compile on main. Work ONLY in
`~/dev/nanodregg-wt/hosting` (`cd ~/dev/nanodregg && scripts/worktree hosting`). Commit ONLY with
`scripts/commit -F MSG PATH...` from there; subject prefix `hosting:`; a SIZE rise needs a
`SIZE: <exact metric>: <why>` line; write MSG with a QUOTED heredoc (<<'EOF'). Never the shared index,
never git add -A, never git stash. Read before writing: CHARTER.md (main), decisions/{kernel,lang,
protocol,client,host}.md, and these real signatures (main 43c4d58):
  Kernel/Receive/Call.lean:24  inductive Right | observe | mutate | invoke (method : Nat) | enroll (count : Nat)
  Kernel/Receive/Call.lean:37  inductive Body … | create (pkg : Option D) (laws : List D) (state : Slots)
                               | invoke (obj : D) (method : Nat) (args : ByteArray) (budget : Nat) (via : Option D)
  Kernel/Receive/Call.lean:161 structure Req (D) where agent principal : D ; notBefore validUntil : Nat
  Kernel/Receive/Derive.lean:198 def invoke … principalOf X look u obj (.invoke method) via …
  Lang/Read.lean:152           def readPackage (text : String) : P Package     -- P = Except String today
  Lang/Package.lean:185,192    encodePackage : Package → Option ByteArray ; decodePackage : ByteArray → Except Refusal Package
  Protocol/Rows.lean:150-162   reqTy, verdictTy, lawPackage (the LANG text shape a law takes)
  Protocol/Rows.lean:319-331   the grain row (BLIND: its plant targets a non-law line; see ASSEMBLY §1)
  Host/Open.lean:110           def openWith … (the follower's and the writer's one open)
  sandbox/src/lib.rs:27        pub struct Policy { read, write, exec, hidden : Vec<PathBuf> }
  sandbox/src/lib.rs:171       pub fn command(policy, program, args) -> Result<Command, ConfineError>
Re-read each at your worktree's HEAD before using it; main moves every few minutes.

BUILD, in order:
1. Hosting/Lifecycle.lean (+ Hosting/Proofs/Lifecycle.lean, + lakefile `lean_lib Hosting` in the SAME
   commit). Restate from /Users/ember/dev/nanodregg-scout/H1/Grain.lean lines 17-75 and 145-170
   (Phase, Event, edges, step, step_table, edges_deterministic, no_double_start, legalPairs_iff_step),
   BUT: Phase without `absent` (birth is `create`); Event = start | stop | remove, ONE METHOD PER EVENT
   (index = Right.invoke n, so an owner can grant an operator `invoke:<start>` alone); the owner law
   compares `req.principal` (NOT agent) to the owner. Generate the package as LANG TEXT
   (`lifecycleText : String`, the shape of Protocol/Rows.lean `lawPackage`), read it with
   `Lang.Read.readPackage` and check it with `Package.checkWith []`; prove the born-only-initial rule
   and the method/step agreement as named theorems (decide/rfl; if only native_decide reaches, add the
   gates/axioms-allow.tsv row and say why). No #guard. Plant (in hosting-sim): skip-judge admits a
   create seeded `running` — must go red by name.
2. Hosting/Plan.lean (+ Proofs): `plan (label : StoreLabel) (g : Grain D) : Except Refusal Plan`,
   `Plan` = sandbox::Policy field for field PLUS `connect`; theorems plan_paths (from H1 Grain.lean lines 122-143 and
   228-261, restated), plan_startable, plan_app_no_workspace. NO `resolve` (nothing sends a volume
   path; ASSEMBLY HOSTING-5). Paths are ByteArray components, each clean or refused by name.
3. Hosting/Controller.lean: `reconcile label w live : List (Action D)` with reconcile_launch_desired /
   reconcile_kill_undesired; restart backoff as a named Bound and a `crashLoop` refusal. Input from
   HOST's follower open; ASK HOST (SendMessage) for a tail API over Host.openWith's follower mode —
   do not write your own segment reader.
4. hosting/ crate, bin `grain-launch` (std only; depends on ../sandbox by path): reads Action frames
   from the Lean controller's stdout, spawns via sandbox::command, reports exits on its stdin. It
   decides nothing; a Lean refusal ends the action; Exposed is the second barrier; keep H1's
   unconfined CONTROL run (/Users/ember/dev/nanodregg-scout/H1/launch/entry.c + demo.sh case 1/3)
   as the plant that proves the EPERMs are not vacuous. Layouts from CODEC (ask; no hand codec).
5. Hand PROTOCOL the grain-row rewrite (ASSEMBLY HOSTING-11); hand CLIENT `Policy.connect`,
   `nd --stdio`, and the resident runtime floor (H1 critique 5 is real: a Rust std binary aborts under
   today's floor, measured).
Then (only after 1-4 are green): the resident plan (HOSTING-6), and the Broker Lean core
(/Users/ember/dev/nanodregg-scout/H2/lean/Broker.lean decide/settle/abort + BrokerProofs.lean EInv,
re-keyed by member id D, with the World LEASE of HOSTING-7). DO NOT build the provider-key file or the
upstream forwarder: KEY-CUSTODY is OPEN for Ember (no ruling exists in the tree, whatever H2 says).

LIFT (ideas/theorems, restated on main): H1 Grain.lean (edges/step/plan theorems), H1 GrainPkg.lean
(the generator idea and the skip-judge plant only), H1 launch/main.rs (the glue discipline), H2
Broker.lean + BrokerProofs.lean (later), H2 generated.rs ASK_PREFIX idea.
IGNORE: H1 GrainPlan.lean (argv/TSV seam), H1 `resolve`/`fire`/`ownerLaw`, H2 nat32/nat64 and le32 use,
H2 parse_verdict, H3 entirely (CLIENT's: CLIENT-12), H4 and H5 entirely (LANG's: LANG-LOG item 5) —
send their paths to those owners, do not port them.

Tests are theorems, plants and rows. No unfiltered test suites: build only your import closure
(`lake build Hosting`, `cargo check -p hosting`), run `lake exe hosting-sim` and the one plant.
Every theorem statement gets a second-agent vacuity read before it lands (law 6); ask ROOT for the
reader. Decisions go in decisions/hosting.md with decision · alternatives · why · CRITIQUE ·
META-CRITIQUE · status. Report to ROOT on events only (first commit, first green plant, a decision
another layer must answer, handoff). Write ~/dev/redregg/work/HOSTING-LOG.md as your continuation
before 350K tokens.

Box safety (quoted verbatim from Ember's rules): Stopping processes: PID file or nothing (incident
2026-10-10). A subagent ran `pkill -f "cat" -u ember` to clear its own stuck `cat`. `-f` matches the
whole command line, every app lives under `/Appli**cat**ions`, and 44 of my apps and agents got SIGTERM.
- Never kill by pattern. No `pkill -f <anything>`, no `pkill -x <bare word>`, no `killall`, no `kill -u`.
- A process you started is stopped by the PID in its PID file, and only that. Every detached job
  writes one (`nohup ... & echo $! > job.pid`). No PID file, no kill: tell me instead.
- If you must look first, `pgrep -fl` and read the list; it is never the argument to a kill.
- Every subagent brief you write quotes this block verbatim.
Disk: the Mac data volume is ~98% full (187 GiB free on 10-16). Keep .lake small, no fixture over 1 MB;
if writes fail, STOP and report — delete nothing that is not yours. hbox is Ember's: do not use it.
Every loop sleeps and has a deadline; foreground-wait builds (a backgrounded wait strands you).
```
