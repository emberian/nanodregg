> record copy of redregg/work/DELETE-PROTOCOL-20261016.md, 2026-10-16; the lane logs stay in redregg

# DELETE-PROTOCOL — the protocol surface, measured by what the spec reaches

DISCOVER-PROTOCOL (scholar → BUILD-PROTOCOL), 2026-10-16, for Ember's deletion program. Tree: detached worktree
of main **2c27b08b** (`git log -1`), read-only; nothing built, nothing run against a Store. The only programs run
were pure Python parsers over the tree: `scripts/host-operations.py check` (prints
`{"active": 184, "public": 113, "operatorOnly": 69, "hostOnly": [24, 25], "reserved": 2, "clientConstants": 20}`)
and my own scanners (kept in the scratchpad `proto/`, named below so the numbers are re-derivable).

**Tags.** READ = read at the cited path:line. DERIVED = computed by a scanner over the tree (method stated).
ASSUMED = my inference; each says what would settle it.

**Method (DERIVED).**
1. *Spec = the landing rows.* `scripts/pipeline/journey-rows:15` `JOURNEY_ROWS=(journey objective rooms activity seats
   bounty call send domain upgrade hostupgrade objectrecord welcomecontinuity sshe2e m3 m4 hermes m6grain m7 m8 fleetsign
   jpay exchange chargedfailure births jserve perf)`. Row `journey` runs only `J0..J8 JROT JROTL` + `JRLANE JGATE JAUDIT`
   (`journey-rows:22-27`); the other ~75 steps of `journey.sh:192 STEPS=(…)` are **not** run by any landing row (they
   are "DRIVER-only" below). Each row's driver and its transitive script closure (files it names, `hook NAME`,
   Python sibling imports) was computed (`proto/closure.py` → 80 files), excluding build scripts.
2. *Driver → verbs.* Every closure file was scanned for `mini VERB`, `--action ACT`, `HOST CONFIG VERB`, and
   `hostraw.py call|repeat|debt|proxy … OP` (`proto/usage.py`). The other 151 scripts under native/ scripts/ deploy/
   examples/ were scanned the same way → the DRIVER-only column.
3. *Verb → opcode.* Rust: every function with a `u8` operation parameter, every call site whose argument is a literal
   or a `const …: u8` (`proto/rustops.py`, 538 literal sites, test modules separated), grouped by sending file; a `mini`
   verb reaches the ops of the modules its `run` arm dispatches to (`native/resource-client/src/main.rs:3194-4500`).
   Kernel-client verbs reach ops 0–11/130/150 through `process` → `socket_process` (`main.rs:1230-1345`, READ: the
   verb→op table describe 0, prepare 1, submit 2, lookup 3, challenge 4, query 5, profile 6, author 7, inspect 8,
   signatures 9, observe-assemble 10, assemble 11, dry-run 130, law-sat 150).
4. *Host side.* Each op's dispatch arm (`proto/arms.py`: `dispatchSession` `Host/Main.lean:2047`, the `fnDispatch`
   match in `run`'s stdio arm, `serveFrame` `:2613`).
5. Manual corrections where the scanner is blind (enum-valued ops, constants behind `mod host_operations`): 30/31/91
   `current_birth.rs:45-49,167`; 193/194 `member_app.rs:10-11,264,304`; 153 `receipt_continuity/carry.rs:1504`;
   34/164 `spk-host/src/dispatch_native.rs:24,1028,1072`; 130/150 `main.rs:1337-1340`.

**Known blind spots (ASSUMED, each with its settler).**
- `mini shell` and `mini workspace` lines inside heredocs/pipes are not parsed into workspace actions: the rooms, m4,
  m7, jserve rows drive the shell, so workspace-action reach is a *lower bound*. Settle: one run of those rows with a
  log line per dispatched workspace action (the natural place: `shell.rs` where a line becomes `ws(&[("action", …)])`,
  e.g. `shell.rs:1946`), or one opcode trace: the Host's `serveFrame` (`Host/Main.lean:2613`) logging `operation` per
  frame to the operator log under a `MINI_TRACE_OPS=1` switch, collected over one standing run.
- Rows `m6grain` (known-red, `required-rows`) drives spk-host; I attributed spk-host's production senders (ops 22, 26,
  34, 36-39, 46, 48, 49, 66-71, 76, 78, 79, 152, 154, 164) to it. ASSUMED: m6grain is red at main, so nothing proves
  those ops ran green. Settle: the same opcode trace on hbox's m6grain run.
- SIM: `Host/WorldSim.lean` and `Kernel/TurnGen.lean` do **not exist on main** (READ `ls`); on `gh/lane/turn-log`
  the sim drives `Turn.ofIntent`/`World.admit` over intent classes (content birth, field write/free, send; READ its
  header), never the opcode wire. So **SIM = none for every opcode**; it covers the *meaning* of op 2 submit only.
- Python drivers call `mini` through helper wrappers (`w.mini`, `mini(…)`); the regexes cover those shapes; a wrapper
  of a new shape would be missed (would under-count reach, never over-count).
- Shared helper scripts (newparticipant-acceptance.sh, genesis.sh) put their verbs into every row that uses them; the
  closure therefore *over*-counts which rows reach the setup verbs (workspace init, clock init, keygen). That only
  affects the ROWS list, never the KEEP/DELETE verdict.

## 6. THE NUMBERS NOW (seed for the size ratchet; first because everything below refers to it)

| surface | now (main 2c27b08b) | reached by a landing row | BAR only | DRIVER-only | client sends, no row/driver | nothing | source |
|---|---|---|---|---|---|---|---|
| Host opcodes (allocated) | **186** (184 active, 2 reserved) | 86 (incl. 21 spk via known-red m6grain, ASSUMED) | 0 (BAR ⊂ rows) | 26 | 31 | **43** | `protocol/host-operations.json` |
| Host opcodes THE BAR touches | 21 | — | — | — | — | — | 0-11, 170-173, 210-214 (`scripts/perf/workload.py:15-17,115,136,185,305` + `activity_world.py`) |
| `fnDispatch` arm lines | 1,294 | 468 | — | 204 | 261 | 361 | `proto/arms.py` |
| Host CLI verbs (`run`) | **116** distinct (124 arms) | 23 | — | 13 | 50 (string hit in Rust only) | **30** | `Host/Main.lean:6288-9143` (2,856 lines) |
| `Host/Main.lean` | **9,163 lines** | | | | | | `wc -l` |
| `mini` verbs | **127** (125 in `run` + `bend-session-sign`, `fleet-sign` pre-routed `main.rs:4507,4513`) | 40 | — | 29 | — | **56** | `main.rs:3194-4500` |
| `mini workspace` actions | **90** | ≥12 (lower bound, shell blind spot) | — | 23 | — | ≤55 | `workspace.rs:6165+` |
| `native/resource-client/src/main.rs` | 5,208 lines | | | | | | `wc -l` |
| consent frames | **12** (220-222, 224, 226-233) | 9 (220, 221, 222, 224, 226, 227, 228, 229, 233) | — | 3 (230-232 thin, `MINI_THIN_CONSENT=1` only; THIN step) | — | 0 | `Host/ClientConsentCore.lean:507-571`, `client_consent.rs:247-262` |
| socket envelope copies (Rust) | 3 | | | | | | §6.10 R14 of ARCHITECTURE |
| SPK broker verbs | 14 | only m6grain (known-red) — ASSUMED | | | | | `native/spk-host/src/broker.rs:291-363` |
| spk-host verbs | 22 + 11 `grain` subverbs | only m6grain — ASSUMED | | | | | `spk-host/src/main.rs:36-197` |
| op families | 25 owners | | | | | | registry |

Ratchet proposal: these eleven numbers in one TSV checked by the gate; a landing may only lower a number unless the
same commit adds a landing row that reaches the new thing.

## 1. THE REACH TABLE

### 1.1 Host opcodes (all 186)

Columns: ROWS = landing rows whose closure reaches the op (DERIVED); BAR = `births`/`perf`; SIM = none for every op
(see blind spots); CLIENT = first production Rust sender (file:line; DERIVED); DRIVER-only = scripts not in any
landing row; class = the strongest reach. `Host/Main.lean:N` = the op's dispatch arm.

| op | symbol | family | receiver (dispatch arm) | ROWS (landing) | BAR | SIM | CLIENT prod sender | DRIVER-only (not a landing row) | class |
|---|---|---|---|---|---|---|---|---|---|
| 0 | DESCRIBE | kernel-client | dispatchSession `Host/Main.lean:2054` | activity,bounty,call,chargedfailure,domain,… (25 rows) | births,perf | - | - | deploy/hermes-dispatch/receiving.py, native/discord-entrance/tests/native-world.py (+113) | **ROW** |
| 1 | AUTHORIZED_PREPARE | kernel-client | dispatchSession `Host/Main.lean:2058` | activity,bounty,call,chargedfailure,domain,… (25 rows) | births,perf | - | native/mini-sdk/src/flow.rs:69 | deploy/hermes-dispatch/receiving.py, native/discord-entrance/tests/native-world.py (+112) | **ROW** |
| 2 | SUBMIT | kernel-client | fnDispatch `Host/Main.lean:6662` | activity,bounty,call,chargedfailure,domain,… (25 rows) | births,perf | - | native/resource-client/src/agent_reserve.rs:598 | deploy/hermes-dispatch/receiving.py, native/discord-entrance/tests/native-world.py (+112) | **ROW** |
| 3 | LOOKUP | kernel-client | fnDispatch `Host/Main.lean:6662` | activity,bounty,call,chargedfailure,domain,… (25 rows) | births,perf | - | native/resource-client/src/historical_call_receipt.rs:35 | deploy/hermes-dispatch/receiving.py, native/discord-entrance/tests/native-world.py (+113) | **ROW** |
| 4 | OBSERVATION_CHALLENGE | kernel-client | dispatchSession `Host/Main.lean:2066` | activity,bounty,call,chargedfailure,domain,… (25 rows) | births,perf | - | native/resource-client/src/participant_enrollment.rs:544; native/mini-sdk/src/flow.rs:64 | deploy/hermes-dispatch/receiving.py, native/discord-entrance/tests/native-world.py (+112) | **ROW** |
| 5 | AUTHORIZED_QUERY | kernel-client | dispatchSession `Host/Main.lean:2072` | activity,bounty,call,chargedfailure,domain,… (25 rows) | births,perf | - | native/resource-client/src/participant_enrollment.rs:588 | deploy/hermes-dispatch/receiving.py, native/discord-entrance/tests/native-world.py (+112) | **ROW** |
| 6 | PROFILE | kernel-client | dispatchSession `Host/Main.lean:2081` | activity,bounty,call,chargedfailure,domain,… (25 rows) | births,perf | - | native/resource-client/src/key_adoption.rs:404 | deploy/hermes-dispatch/receiving.py, native/discord-entrance/tests/native-world.py (+117) | **ROW** |
| 7 | AUTHOR | kernel-client | dispatchSession `Host/Main.lean:2084` | activity,bounty,call,chargedfailure,domain,… (25 rows) | births,perf | - | native/resource-client/src/activity.rs:84; native/mini-sdk/src/host.rs:18 | deploy/hermes-dispatch/receiving.py, native/discord-entrance/tests/native-world.py (+118) | **ROW** |
| 8 | INSPECT | kernel-client | dispatchSession `Host/Main.lean:2085` | activity,bounty,call,chargedfailure,domain,… (25 rows) | births,perf | - | native/resource-client/src/world_prototype.rs:91; native/mini-sdk/src/host.rs:22 | deploy/hermes-dispatch/receiving.py, native/discord-entrance/tests/native-world.py (+122) | **ROW** |
| 9 | SIGNATURES | kernel-client | dispatchSession `Host/Main.lean:2084` | activity,bounty,call,chargedfailure,domain,… (25 rows) | births,perf | - | native/mini-sdk/src/host.rs:27 | deploy/hermes-dispatch/receiving.py, native/discord-entrance/tests/native-world.py (+112) | **ROW** |
| 10 | OBSERVATION_ASSEMBLE | kernel-client | dispatchSession `Host/Main.lean:2084` | activity,bounty,call,chargedfailure,domain,… (25 rows) | births,perf | - | native/resource-client/src/participant_enrollment.rs:579; native/mini-sdk/src/host.rs:31 | deploy/hermes-dispatch/receiving.py, native/discord-entrance/tests/native-world.py (+112) | **ROW** |
| 11 | CALL_ASSEMBLE | kernel-client | dispatchSession `Host/Main.lean:2084` | activity,bounty,call,chargedfailure,domain,… (25 rows) | births,perf | - | native/mini-sdk/src/host.rs:35 | deploy/hermes-dispatch/receiving.py, native/discord-entrance/tests/native-world.py (+112) | **ROW** |
| 12 | FN_POLL | fn-services | fnDispatch `Host/Main.lean:6685` | - | - | - | - | - | **NONE** |
| 13 | FN_ACK | fn-services | fnDispatch `Host/Main.lean:6685` | - | - | - | - | - | **NONE** |
| 14 | FN_REPLY_POLL | fn-services | fnDispatch `Host/Main.lean:6693` | - | - | - | - | - | **NONE** |
| 15 | FN_REPLY_ACK | fn-services | fnDispatch `Host/Main.lean:6693` | - | - | - | - | - | **NONE** |
| 16 | FN_ORIGIN_OUTBOX | fn-services | fnDispatch `Host/Main.lean:6708` | - | - | - | native/resource-client/src/main.rs:2939 | - | **CLIENT** |
| 17 | PROVIDER_CONTINUITY | inference | fnDispatch `Host/Main.lean:6713` | - | - | - | native/resource-client/src/provider_continuity.rs:404 | - | **CLIENT** |
| 18 | FN_ORIGIN_OUTBOX_EXPORT | fn-services | fnDispatch `Host/Main.lean:6720` | - | - | - | native/resource-client/src/publisher.rs:154 | - | **CLIENT** |
| 19 | PROVIDER_USAGE_QUOTE | inference | fnDispatch `Host/Main.lean:6739` | - | - | - | native/resource-client/src/meter.rs:172 | - | **CLIENT** |
| 20 | SELECTED_RELEASE_SUBMIT | selected-release | dispatchSession `Host/Main.lean:2119` | exchange | - | - | native/resource-client/src/selected_release.rs:242 | selected-release-acceptance.sh | **ROW** |
| 21 | SELECTED_RELEASE_LOOKUP | selected-release | dispatchSession `Host/Main.lean:2122` | exchange | - | - | native/resource-client/src/selected_release.rs:251 | selected-release-acceptance.sh | **ROW** |
| 22 | APPLICATION_LIFECYCLE_BEGIN_SUBMIT | spk-lifecycle | dispatchSession `Host/Main.lean:2125` | m6grain(spk-host) | - | - | native/spk-host/src/lifecycle_v3_stop_begin_native.rs:218 | - | **ROW** |
| 23 | APPLICATION_LIFECYCLE_BEGIN_LOOKUP | spk-lifecycle | dispatchSession `Host/Main.lean:2128` | - | - | - | - | - | **NONE** |
| 24 | SELECTED_SOURCE_PUBLISH_SUBMIT | selected-release | dispatchSession `Host/Main.lean:2134` | - | - | - | selected_publisher.rs -> Host CLI selected-source-publication-submit (one-shot, no socket route) | - | **CLIENT** |
| 25 | SELECTED_SOURCE_PUBLISH_LOOKUP | selected-release | dispatchSession `Host/Main.lean:2137` | - | - | - | selected_publisher.rs -> Host CLI selected-source-publication-lookup | - | **CLIENT** |
| 26 | APPLICATION_LIFECYCLE_CLAIM_SUBMIT | spk-lifecycle | serveFrame `Host/Main.lean:-` | m6grain(spk-host) | - | - | native/spk-host/src/lifecycle_v3_claim_native.rs:450 | - | **ROW** |
| 27 | APPLICATION_LIFECYCLE_CLAIM_LOOKUP | spk-lifecycle | dispatchSession `Host/Main.lean:2131` | - | - | - | - | - | **NONE** |
| 28 | APPLICATION_SHARE_ISSUE_SUBMIT | spk | fnDispatch `Host/Main.lean:6751` | - | - | - | native/resource-client/src/share_issue.rs:383 | scripts/application-share-issue/native-acceptance.sh | **DRV** |
| 29 | APPLICATION_SHARE_ISSUE_LOOKUP | spk | fnDispatch `Host/Main.lean:6755` | - | - | - | native/resource-client/src/share_issue.rs:431 | scripts/application-share-issue/native-acceptance.sh | **DRV** |
| 30 | APPLICATION_CURRENT_BIRTH | spk | fnDispatch `Host/Main.lean:7313` | m6grain | - | - | native/resource-client/src/current_birth.rs:167 | - | **ROW** |
| 31 | APPLICATION_SESSION_CURRENT_BIRTH | spk | fnDispatch `Host/Main.lean:7317` | - | - | - | native/resource-client/src/current_birth.rs:167 | - | **CLIENT** |
| 32 | APPLICATION_SHARE_ISSUE_PLAN | spk | fnDispatch `Host/Main.lean:7450` | - | - | - | native/resource-client/src/share_issue.rs:508 | scripts/application-share-issue/native-acceptance.sh | **DRV** |
| 33 | APPLICATION_SHARE_ISSUE_ASSEMBLE | spk | fnDispatch `Host/Main.lean:7459` | - | - | - | native/resource-client/src/share_issue.rs:571 | scripts/application-share-issue/native-acceptance.sh | **DRV** |
| 34 | APPLICATION_DISPATCH_SUBMIT | spk | serveFrame `Host/Main.lean:-` | m6grain? | - | - | native/spk-host/src/dispatch_native.rs:1028 | - | **ROW** |
| 35 | APPLICATION_DISPATCH_LOOKUP | spk | fnDispatch `Host/Main.lean:7667` | - | - | - | - | - | **NONE** |
| 36 | APPLICATION_DISPATCH_PLAN | spk | fnDispatch `Host/Main.lean:7672` | m6grain(spk-host) | - | - | native/spk-host/src/dispatch_native.rs:891 | - | **ROW** |
| 37 | APPLICATION_DISPATCH_ASSEMBLE | spk | dispatchSession `Host/Main.lean:2148` | m6grain(spk-host) | - | - | native/spk-host/src/dispatch_native.rs:923 | - | **ROW** |
| 38 | APPLICATION_LIFECYCLE_COMPLETION_SUBMIT | spk | dispatchSession `Host/Main.lean:2155` | m6grain(spk-host) | - | - | native/spk-host/src/lifecycle_v3_completion_native.rs:424 | - | **ROW** |
| 39 | APPLICATION_LIFECYCLE_COMPLETION_LOOKUP | spk | dispatchSession `Host/Main.lean:2158` | m6grain(spk-host) | - | - | native/spk-host/src/lifecycle_v3_completion_native.rs:470 | - | **ROW** |
| 40 | FN_NAMESPACE_SUBMIT | fn-services | fnDispatch `Host/Main.lean:7488` | - | - | - | native/resource-client/src/fn_namespace.rs:455 | - | **CLIENT** |
| 41 | FN_NAMESPACE_LOOKUP | fn-services | dispatchSession `Host/Main.lean:2161` | - | - | - | native/resource-client/src/fn_namespace.rs:329 | - | **CLIENT** |
| 42 | FN_NAMESPACE_PLAN | fn-services | fnDispatch `Host/Main.lean:7504` | - | - | - | native/resource-client/src/fn_namespace.rs:146 | - | **CLIENT** |
| 43 | FN_NAMESPACE_ASSEMBLE | fn-services | fnDispatch `Host/Main.lean:7519` | - | - | - | native/resource-client/src/fn_namespace.rs:418 | - | **CLIENT** |
| 44 | APPLICATION_LIFECYCLE_COMPLETION_PLAN | spk-lifecycle | fnDispatch `Host/Main.lean:7538` | - | - | - | - | - | **NONE** |
| 45 | APPLICATION_LIFECYCLE_COMPLETION_ASSEMBLE | spk-lifecycle | fnDispatch `Host/Main.lean:7552` | - | - | - | - | - | **NONE** |
| 46 | AGENT_PAID_DISPATCH_SUBMIT | hermes | serveFrame `Host/Main.lean:-` | m6grain(spk-host) | - | - | native/spk-host/src/agent_api_native.rs:819 | - | **ROW** |
| 47 | AGENT_PAID_DISPATCH_LOOKUP | hermes | dispatchSession `Host/Main.lean:2141` | - | - | - | - | - | **NONE** |
| 48 | AGENT_PAID_DISPATCH_PLAN | hermes | fnDispatch `Host/Main.lean:7767` | m6grain(spk-host) | - | - | native/spk-host/src/agent_api_native.rs:746; native/resource-client/src/agent_payer.rs:125 | - | **ROW** |
| 49 | AGENT_PAID_DISPATCH_ASSEMBLE | hermes | fnDispatch `Host/Main.lean:7767` | m6grain(spk-host) | - | - | native/spk-host/src/agent_api_native.rs:789 | - | **ROW** |
| 50 | APPLICATION_LIFECYCLE_BEGIN_PLAN | spk-lifecycle | fnDispatch `Host/Main.lean:7563` | - | - | - | - | - | **NONE** |
| 51 | APPLICATION_LIFECYCLE_BEGIN_ASSEMBLE | spk-lifecycle | fnDispatch `Host/Main.lean:7577` | - | - | - | - | - | **NONE** |
| 52 | APPLICATION_LIFECYCLE_CLAIM_PLAN | spk-lifecycle | fnDispatch `Host/Main.lean:7588` | - | - | - | - | - | **NONE** |
| 53 | APPLICATION_LIFECYCLE_CLAIM_ASSEMBLE | spk-lifecycle | fnDispatch `Host/Main.lean:7602` | - | - | - | - | - | **NONE** |
| 54 | GRAIN_SHARE_ISSUE_SUBMIT | spk | fnDispatch `Host/Main.lean:6759` | m6grain | - | - | native/resource-client/src/grain_share_issue.rs:534 | scripts/application-share-issue/native-grain-acceptance.sh, scripts/application-share-issue/resume-prepared-native-grain.sh (+6) | **ROW** |
| 55 | GRAIN_SHARE_ISSUE_LOOKUP | spk | fnDispatch `Host/Main.lean:6763` | m6grain | - | - | native/resource-client/src/grain_share_issue.rs:579 | scripts/application-share-issue/native-grain-acceptance.sh, scripts/application-share-issue/resume-prepared-native-grain.sh (+6) | **ROW** |
| 56 | GRAIN_SHARE_ISSUE_PLAN | spk | fnDispatch `Host/Main.lean:7469` | m6grain | - | - | native/resource-client/src/grain_share_issue.rs:357 | scripts/application-share-issue/native-grain-acceptance.sh, scripts/application-share-issue/resume-prepared-native-grain.sh (+6) | **ROW** |
| 57 | GRAIN_SHARE_ISSUE_ASSEMBLE | spk | fnDispatch `Host/Main.lean:7478` | m6grain | - | - | native/resource-client/src/grain_share_issue.rs:503 | scripts/application-share-issue/native-grain-acceptance.sh, scripts/application-share-issue/resume-prepared-native-grain.sh (+6) | **ROW** |
| 58 | AGENT_RESERVE_PLAN | hermes | fnDispatch `Host/Main.lean:7767` | - | - | - | native/resource-client/src/agent_reserve.rs:263 | - | **CLIENT** |
| 59 | AGENT_RESERVE_ASSEMBLE | hermes | fnDispatch `Host/Main.lean:7767` | - | - | - | native/resource-client/src/agent_reserve.rs:536 | - | **CLIENT** |
| 60 | FN_SELECTED_COVERAGE_SUBMIT | fn-services | fnDispatch `Host/Main.lean:7267` | - | - | - | - | - | **NONE** |
| 61 | FN_SELECTED_COVERAGE_LOOKUP | fn-services | fnDispatch `Host/Main.lean:7271` | - | - | - | - | - | **NONE** |
| 62 | FN_EMPTY_PROGRESS_SUBMIT | fn-services | fnDispatch `Host/Main.lean:7275` | - | - | - | - | - | **NONE** |
| 63 | FN_EMPTY_PROGRESS_LOOKUP | fn-services | fnDispatch `Host/Main.lean:7279` | - | - | - | - | - | **NONE** |
| 64 | FN_FRONTIER_PLAN | fn-services | fnDispatch `Host/Main.lean:7283` | - | - | - | native/resource-client/src/fn_frontier.rs:248 | - | **CLIENT** |
| 65 | FN_FRONTIER_ASSEMBLE | fn-services | fnDispatch `Host/Main.lean:7295` | - | - | - | native/resource-client/src/fn_frontier.rs:546 | - | **CLIENT** |
| 66 | APPLICATION_LAUNCH_BEGIN_PLAN | spk-lifecycle | fnDispatch `Host/Main.lean:7613` | m6grain(spk-host) | - | - | native/spk-host/src/lifecycle_v3_stop_begin_native.rs:171 | - | **ROW** |
| 67 | APPLICATION_LAUNCH_BEGIN_ASSEMBLE | spk-lifecycle | fnDispatch `Host/Main.lean:7613` | m6grain(spk-host) | - | - | native/spk-host/src/lifecycle_v3_stop_begin_native.rs:200 | - | **ROW** |
| 68 | APPLICATION_LAUNCH_CLAIM_PLAN | spk-lifecycle | fnDispatch `Host/Main.lean:7613` | m6grain(spk-host) | - | - | native/spk-host/src/lifecycle_v3_claim_native.rs:242 | - | **ROW** |
| 69 | APPLICATION_LAUNCH_CLAIM_ASSEMBLE | spk-lifecycle | fnDispatch `Host/Main.lean:7613` | m6grain(spk-host) | - | - | native/spk-host/src/lifecycle_v3_claim_native.rs:281 | - | **ROW** |
| 70 | APPLICATION_LAUNCH_COMPLETION_PLAN | spk-lifecycle | fnDispatch `Host/Main.lean:7613` | m6grain(spk-host) | - | - | native/spk-host/src/lifecycle_v3_completion_native.rs:237 | - | **ROW** |
| 71 | APPLICATION_LAUNCH_COMPLETION_ASSEMBLE | spk-lifecycle | fnDispatch `Host/Main.lean:7613` | m6grain(spk-host) | - | - | native/spk-host/src/lifecycle_v3_completion_native.rs:277 | - | **ROW** |
| 72 | AGENT_LIFETIME_GRANT_SUBMIT | hermes | fnDispatch `Host/Main.lean:6767` | - | - | - | native/resource-client/src/agent_lifetime_grant.rs:393 | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| 73 | AGENT_LIFETIME_GRANT_LOOKUP | hermes | fnDispatch `Host/Main.lean:6771` | - | - | - | native/resource-client/src/agent_lifetime_grant.rs:456 | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| 74 | AGENT_LIFETIME_GRANT_PLAN | hermes | fnDispatch `Host/Main.lean:7645` | - | - | - | native/resource-client/src/agent_lifetime_grant.rs:181 | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| 75 | AGENT_LIFETIME_GRANT_ASSEMBLE | hermes | fnDispatch `Host/Main.lean:7654` | - | - | - | native/resource-client/src/agent_lifetime_grant.rs:307 | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| 76 | AGENT_LIFETIME_DISPATCH_SUBMIT | hermes | serveFrame `Host/Main.lean:-` | m6grain(spk-host) | - | - | native/spk-host/src/agent_api_lifetime_dispatch_native_v3.rs:167; native/resource-client/src/agent_reserve/lifetime_v3/paid.rs:623 | - | **ROW** |
| 77 | AGENT_LIFETIME_DISPATCH_LOOKUP | hermes | dispatchSession `Host/Main.lean:2144` | - | - | - | native/resource-client/src/agent_reserve/lifetime_v3/paid.rs:685 | - | **CLIENT** |
| 78 | AGENT_LIFETIME_DISPATCH_PLAN | hermes | fnDispatch `Host/Main.lean:7773` | m6grain(spk-host) | - | - | native/spk-host/src/agent_api_lifetime_paid_native_v3.rs:147; native/resource-client/src/agent_reserve/lifetime_v3/paid.rs:206 | - | **ROW** |
| 79 | AGENT_LIFETIME_DISPATCH_ASSEMBLE | hermes | fnDispatch `Host/Main.lean:7773` | m6grain(spk-host) | - | - | native/spk-host/src/agent_api_lifetime_paid_native_v3.rs:183; native/resource-client/src/agent_reserve/lifetime_v3/paid.rs:511 | - | **ROW** |
| 80 | AGENT_LIFETIME_RESERVE_PLAN | hermes | fnDispatch `Host/Main.lean:7773` | - | - | - | native/resource-client/src/agent_lifetime_grant.rs:181 | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| 81 | AGENT_LIFETIME_RESERVE_ASSEMBLE | hermes | fnDispatch `Host/Main.lean:7773` | - | - | - | native/resource-client/src/agent_lifetime_grant.rs:307 | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| 82 | APPLICATION_SESSION_ENROLLMENT_PLAN | spk | fnDispatch `Host/Main.lean:7685` | m6grain | - | - | native/resource-client/src/session_enrollment.rs:158 | - | **ROW** |
| 83 | APPLICATION_SESSION_ENROLLMENT_ASSEMBLE | spk | fnDispatch `Host/Main.lean:7698` | m6grain | - | - | native/resource-client/src/session_enrollment.rs:285 | - | **ROW** |
| 84 | APPLICATION_SESSION_ENROLLMENT_SUBMIT | spk | fnDispatch `Host/Main.lean:6775` | m6grain | - | - | native/resource-client/src/session_enrollment.rs:419 | - | **ROW** |
| 85 | APPLICATION_SESSION_ENROLLMENT_LOOKUP | spk | fnDispatch `Host/Main.lean:6780` | m6grain | - | - | native/resource-client/src/session_enrollment.rs:462 | - | **ROW** |
| 86 | PARTICIPANT_KEY_ENROLLMENT_PLAN | identity | fnDispatch `Host/Main.lean:7715` | exchange,hermes,journey,jserve,m3,… (8 rows) | - | - | native/resource-client/src/participant_enrollment.rs:917 | journey.d/j12c-kernel.sh, journey.d/j12e.sh (+4) | **ROW** |
| 87 | PARTICIPANT_KEY_ENROLLMENT_ASSEMBLE | identity | fnDispatch `Host/Main.lean:7727` | exchange,hermes,journey,jserve,m3,… (8 rows) | - | - | native/resource-client/src/participant_enrollment.rs:1568 | journey.d/j12c-kernel.sh, journey.d/j12e.sh (+4) | **ROW** |
| 88 | PARTICIPANT_KEY_ENROLLMENT_SUBMIT | identity | fnDispatch `Host/Main.lean:6785` | exchange,hermes,journey,jserve,m3,… (8 rows) | - | - | native/resource-client/src/participant_enrollment.rs:1719 | journey.d/j12c-kernel.sh, journey.d/j12e.sh (+4) | **ROW** |
| 89 | PARTICIPANT_KEY_ENROLLMENT_LOOKUP | identity | fnDispatch `Host/Main.lean:6790` | exchange,hermes,journey,jserve,m3,… (8 rows) | - | - | native/resource-client/src/participant_enrollment.rs:1449 | journey.d/j12c-kernel.sh, journey.d/j12e.sh (+4) | **ROW** |
| 91 | CURRENT_RESOURCE_BIRTH | world | fnDispatch `Host/Main.lean:7436` | - | - | - | native/resource-client/src/current_birth.rs:167 | - | **CLIENT** |
| 92 | PARTICIPANT_PROVISIONING_PLAN | identity | fnDispatch `Host/Main.lean:7745` | - | - | - | native/resource-client/src/agent_lifetime_grant.rs:181 | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| 93 | PARTICIPANT_PROVISIONING_ASSEMBLE | identity | fnDispatch `Host/Main.lean:7757` | - | - | - | native/resource-client/src/agent_lifetime_grant.rs:307 | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| 94 | PARTICIPANT_PROVISIONING_SUBMIT | identity | fnDispatch `Host/Main.lean:6795` | - | - | - | native/resource-client/src/agent_lifetime_grant.rs:393 | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| 95 | PARTICIPANT_PROVISIONING_LOOKUP | identity | fnDispatch `Host/Main.lean:6800` | - | - | - | native/resource-client/src/agent_lifetime_grant.rs:456 | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| 96 | FLEET_TURN_PLAN | fleet | fnDispatch `Host/Main.lean:6805` | m8 | - | - | native/resource-client/src/fleet.rs:525 | fleet-contention.sh, journey.d/j17.sh | **ROW** |
| 97 | FLEET_TURN_ASSEMBLE | fleet | fnDispatch `Host/Main.lean:6817` | m8 | - | - | native/resource-client/src/fleet.rs:552 | fleet-contention.sh, journey.d/j17.sh | **ROW** |
| 98 | FLEET_TURN_SUBMIT | fleet | fnDispatch `Host/Main.lean:6825` | m8 | - | - | native/resource-client/src/fleet.rs:567 | fleet-contention.sh, journey.d/j17.sh | **ROW** |
| 99 | FLEET_TURN_LOOKUP | fleet | fnDispatch `Host/Main.lean:6830` | m8 | - | - | native/resource-client/src/fleet.rs:289 | fleet-contention.sh, journey.d/j17.sh | **ROW** |
| 100 | FLEET_TOPIC_POLL | fleet | fnDispatch `Host/Main.lean:6834` | m8 | - | - | native/resource-client/src/fleet.rs:845 | fleet-contention.sh, journey.d/j17.sh | **ROW** |
| 101 | FLEET_HEAD | fleet | fnDispatch `Host/Main.lean:6847` | m8 | - | - | native/resource-client/src/fleet.rs:762 | fleet-contention.sh, journey.d/j17.sh | **ROW** |
| 102 | FLEET_RECEIPT | fleet | fnDispatch `Host/Main.lean:6866` | m8 | - | - | native/resource-client/src/fleet.rs:744 | fleet-contention.sh, journey.d/j17.sh | **ROW** |
| 103 | PAY_COMMAND_PLAN | payments | fnDispatch `Host/Main.lean:6904` | - | - | - | - | - | **NONE** |
| 104 | PAY_COMMAND_ASSEMBLE | payments | fnDispatch `Host/Main.lean:6911` | - | - | - | - | - | **NONE** |
| 105 | PAY_COMMAND_SUBMIT | payments | fnDispatch `Host/Main.lean:6919` | - | - | - | - | - | **NONE** |
| 106 | PAY_COMMAND_LOOKUP | payments | fnDispatch `Host/Main.lean:6927` | - | - | - | - | - | **NONE** |
| 107 | PAY_VIEW | payments | fnDispatch `Host/Main.lean:7036` | journey,jpay,jserve,m7,rooms | - | - | native/resource-client/src/job.rs:335 | native/inference-scheduler/native-two-member.py, journey.d/jjob-money.sh (+7) | **ROW** |
| 108 | PAY_OBSERVATION_PLAN | payments | fnDispatch `Host/Main.lean:7084` | - | - | - | - | - | **NONE** |
| 109 | PAY_OBSERVATION_ASSEMBLE | payments | fnDispatch `Host/Main.lean:7092` | - | - | - | - | - | **NONE** |
| 110 | PAY_OBSERVATION_SUBMIT | payments | fnDispatch `Host/Main.lean:7100` | - | - | - | - | - | **NONE** |
| 111 | PAY_OBSERVATION_LOOKUP | payments | fnDispatch `Host/Main.lean:7104` | - | - | - | - | - | **NONE** |
| 112 | PAY_ENROLLMENT_VIEW | payments | fnDispatch `Host/Main.lean:7108` | journey,jpay,jserve,m7,rooms | - | - | native/resource-client/src/main.rs:3136 | native/inference-scheduler/native-two-member.py, journey.d/jjob-money.sh (+7) | **ROW** |
| 113 | PAY_REFILL_PLAN | payments | fnDispatch `Host/Main.lean:7214` | - | - | - | native/resource-client/src/pay_refill.rs:113 | - | **CLIENT** |
| 114 | PAY_REFILL_ASSEMBLE | payments | fnDispatch `Host/Main.lean:7222` | - | - | - | native/resource-client/src/pay_refill.rs:125 | - | **CLIENT** |
| 115 | PAY_REFILL_SUBMIT | payments | fnDispatch `Host/Main.lean:7230` | - | - | - | native/resource-client/src/pay_refill.rs:127 | - | **CLIENT** |
| 116 | PAY_REFILL_LOOKUP | payments | fnDispatch `Host/Main.lean:7238` | - | - | - | native/resource-client/src/pay_refill.rs:140 | - | **CLIENT** |
| 117 | PAY_SELF_ENROLLMENT_PLAN | payments | fnDispatch `Host/Main.lean:7163` | - | - | - | - | - | **NONE** |
| 118 | PAY_SELF_ENROLLMENT_ASSEMBLE | payments | fnDispatch `Host/Main.lean:7171` | - | - | - | - | - | **NONE** |
| 119 | PAY_SELF_ENROLLMENT_SUBMIT | payments | fnDispatch `Host/Main.lean:7179` | - | - | - | - | - | **NONE** |
| 120 | PAY_SELF_ENROLLMENT_LOOKUP | payments | fnDispatch `Host/Main.lean:7183` | - | - | - | - | - | **NONE** |
| 121 | PAY_ENROLLMENT_QUOTE | payments | fnDispatch `Host/Main.lean:7115` | - | - | - | native/resource-client/src/join_solana_v2.rs:439 | - | **CLIENT** |
| 123 | REALM_WELL_PLAN | world | fnDispatch `Host/Main.lean:7040` | bounty,seats | - | - | native/resource-client/src/well.rs:138 | journey.d/j10c.sh, journey.d/jwell.sh | **ROW** |
| 124 | REALM_WELL_ASSEMBLE | world | fnDispatch `Host/Main.lean:7045` | bounty,seats | - | - | native/resource-client/src/well.rs:159 | journey.d/j10c.sh, journey.d/jwell.sh | **ROW** |
| 125 | REALM_WELL_SUBMIT | world | fnDispatch `Host/Main.lean:7051` | bounty,seats | - | - | native/resource-client/src/well.rs:168 | journey.d/j10c.sh, journey.d/jwell.sh | **ROW** |
| 126 | CLOCK_TICK_PLAN | clock | fnDispatch `Host/Main.lean:7061` | activity,bounty,call,chargedfailure,domain,… (23 rows) | - | - | native/resource-client/src/clock.rs:283 | deploy/hermes-dispatch/receiving.py, journey-timers/ticker.sh (+4) | **ROW** |
| 127 | CLOCK_TICK_ASSEMBLE | clock | fnDispatch `Host/Main.lean:7068` | activity,bounty,call,chargedfailure,domain,… (23 rows) | - | - | native/resource-client/src/clock.rs:292 | deploy/hermes-dispatch/receiving.py, journey-timers/ticker.sh (+4) | **ROW** |
| 128 | CLOCK_TICK_SUBMIT | clock | fnDispatch `Host/Main.lean:7076` | activity,bounty,call,chargedfailure,domain,… (23 rows) | - | - | native/resource-client/src/clock.rs:205 | deploy/hermes-dispatch/receiving.py, journey-timers/ticker.sh (+4) | **ROW** |
| 129 | CLOCK_VIEW | clock | fnDispatch `Host/Main.lean:7080` | activity,bounty,call,chargedfailure,domain,… (25 rows) | - | - | native/resource-client/src/job.rs:156 | deploy/hermes-dispatch/receiving.py, native/inference-scheduler/native-two-member.py (+10) | **ROW** |
| 130 | AFFORDANCE_DRY_RUN | world | dispatchSession `Host/Main.lean:2106` | - | - | - | native/resource-client/src/main.rs:1337 | journey.d/j12a.sh (J12A, mini shell can) | **DRV** |
| 131 | NOCK_PROGRAM_CHECK | nock | fnDispatch `Host/Main.lean:7321` | - | - | - | - | - | **NONE** |
| 132 | NOCK_PROGRAM_SHOW | nock | fnDispatch `Host/Main.lean:7333` | - | - | - | native/resource-client/src/world_prototype.rs:76 | journey.d/jjob-money.sh, journey.d/jjob.sh (+3) | **DRV** |
| 133 | NOCK_SAMPLE | nock | fnDispatch `Host/Main.lean:7344` | - | - | - | - | - | **NONE** |
| 134 | NOCK_DRY_RUN | nock | fnDispatch `Host/Main.lean:7355` | - | - | - | native/resource-client/src/world_prototype.rs:83 | journey.d/jjob-money.sh, journey.d/jjob.sh (+3) | **DRV** |
| 135 | NOCK_APP_POKE_DRY_RUN | nock | fnDispatch `Host/Main.lean:7371` | - | - | - | - | - | **NONE** |
| 136 | NOCK_APP_PEEK | nock | fnDispatch `Host/Main.lean:7393` | - | - | - | - | - | **NONE** |
| 137 | NOCK_APP_STATE | nock | fnDispatch `Host/Main.lean:7393` | - | - | - | - | - | **NONE** |
| 140 | KEY_ROTATION_PLAN | identity | fnDispatch `Host/Main.lean:6993` | journey,rooms | - | - | native/resource-client/src/key_rotation.rs:685 | deploy/hermes-dispatch/receiving.py, native/grain-runtime/journeys/byok-native.py (+1) | **ROW** |
| 141 | KEY_ROTATION_ASSEMBLE | identity | fnDispatch `Host/Main.lean:7003` | journey,rooms | - | - | native/resource-client/src/key_rotation.rs:716 | deploy/hermes-dispatch/receiving.py, native/grain-runtime/journeys/byok-native.py (+1) | **ROW** |
| 142 | KEY_ROTATION_SUBMIT | identity | fnDispatch `Host/Main.lean:7011` | journey,rooms | - | - | native/resource-client/src/key_rotation.rs:746 | deploy/hermes-dispatch/receiving.py, native/grain-runtime/journeys/byok-native.py (+1) | **ROW** |
| 143 | KEY_ROTATION_LOOKUP | identity | fnDispatch `Host/Main.lean:7017` | journey,rooms | - | - | native/resource-client/src/key_rotation.rs:752 | deploy/hermes-dispatch/receiving.py, native/grain-runtime/journeys/byok-native.py (+1) | **ROW** |
| 144 | KEY_ROTATION_STATUS | identity | fnDispatch `Host/Main.lean:7023` | journey,jpay,rooms | - | - | native/resource-client/src/keys.rs:96 | deploy/hermes-dispatch/receiving.py, native/grain-runtime/journeys/byok-native.py (+5) | **ROW** |
| 150 | LAW_SAT | laws | dispatchSession `Host/Main.lean:2115` | - | - | - | native/resource-client/src/main.rs:1340 | journey.d/jlawsat.sh (JLS, can --any) | **DRV** |
| 151 | RECEIPT_CONTINUITY | receipt-continuity | fnDispatch `Host/Main.lean:6725` | - | - | - | native/resource-client/src/receipt_continuity.rs:609 | - | **CLIENT** |
| 152 | APPLICATION_STREAM_RENEW | spk | serveFrame `Host/Main.lean:-` | m6grain(spk-host) | - | - | native/spk-host/src/dispatch_native.rs:698 | - | **ROW** |
| 153 | CARRY_RECEIPT_LOOKUP | checked-carry | fnDispatch `Host/Main.lean:6731` | - | - | - | native/resource-client/src/receipt_continuity/carry.rs:1504 | - | **CLIENT** |
| 154 | APPLICATION_ROUTE_INSPECT | spk | serveFrame `Host/Main.lean:-` | m6grain(spk-host) | - | - | native/spk-host/src/dispatch_native.rs:1277 | - | **ROW** |
| 160 | JOB_MONEY_PLAN | job-money | fnDispatch `Host/Main.lean:7187` | - | - | - | native/resource-client/src/job.rs:342 | journey.d/jjob-money.sh, journey.d/jjob.sh (+3) | **DRV** |
| 161 | JOB_MONEY_ASSEMBLE | job-money | fnDispatch `Host/Main.lean:7195` | - | - | - | native/resource-client/src/job.rs:359 | journey.d/jjob-money.sh, journey.d/jjob.sh (+3) | **DRV** |
| 162 | JOB_MONEY_SUBMIT | job-money | fnDispatch `Host/Main.lean:7203` | - | - | - | native/resource-client/src/job.rs:397 | journey.d/jjob-money.sh, journey.d/jjob.sh (+3) | **DRV** |
| 163 | JOB_MONEY_LOOKUP | job-money | fnDispatch `Host/Main.lean:7210` | - | - | - | native/resource-client/src/job.rs:492 | journey.d/jjob-money.sh, journey.d/jjob.sh (+3) | **DRV** |
| 164 | APPLICATION_ROUTE_BOUND_DISPATCH | spk | serveFrame `Host/Main.lean:-` | m6grain? | - | - | native/spk-host/src/dispatch_native.rs:24,1028 | - | **ROW** |
| 170 | CERTIFY_PLAN | history | fnDispatch `Host/Main.lean:7242` | hostupgrade,journey,jserve,m7,rooms | births,perf | - | native/resource-client/src/checkpoint.rs:140 | journey-timers/ticker.sh, journey.d/jtail.sh (+1) | **ROW** |
| 171 | CERTIFY_ASSEMBLE | history | fnDispatch `Host/Main.lean:7249` | hostupgrade,journey,jserve,m7,rooms | births,perf | - | native/resource-client/src/checkpoint.rs:149 | journey-timers/ticker.sh, journey.d/jtail.sh (+1) | **ROW** |
| 172 | CERTIFY_SUBMIT | history | fnDispatch `Host/Main.lean:7257` | hostupgrade,journey,jserve,m7,rooms | births,perf | - | native/resource-client/src/checkpoint.rs:150 | journey-timers/ticker.sh, journey.d/jtail.sh (+1) | **ROW** |
| 173 | CERTIFY_VIEW | history | fnDispatch `Host/Main.lean:7261` | hostupgrade,journey,jserve,m7,rooms | births,perf | - | native/resource-client/src/checkpoint.rs:113 | journey-timers/ticker.sh, journey.d/jtail.sh (+1) | **ROW** |
| 180 | FLEET_INCOMING_LEDGER | fleet | fnDispatch `Host/Main.lean:6853` | m8 | - | - | native/resource-client/src/fleet.rs:989 | fleet-contention.sh, journey.d/j17.sh | **ROW** |
| 181 | PAY_CLAIM_VIEW | payments | fnDispatch `Host/Main.lean:7125` | journey,jpay,jserve,m7,rooms | - | - | native/resource-client/src/pay.rs:1461 | native/inference-scheduler/native-two-member.py, journey.d/jjob-money.sh (+7) | **ROW** |
| 182 | PAY_CLAIM_QUOTE | payments | fnDispatch `Host/Main.lean:7125` | - | - | - | native/resource-client/src/pay_claim.rs:221 | - | **CLIENT** |
| 183 | PAY_CLAIM_PLAN | payments | fnDispatch `Host/Main.lean:7139` | - | - | - | native/resource-client/src/pay_claim.rs:625 | - | **CLIENT** |
| 184 | PAY_CLAIM_ASSEMBLE | payments | fnDispatch `Host/Main.lean:7146` | - | - | - | native/resource-client/src/pay_claim.rs:658 | - | **CLIENT** |
| 185 | PAY_CLAIM_SUBMIT | payments | fnDispatch `Host/Main.lean:7152` | - | - | - | native/resource-client/src/pay_claim.rs:679 | - | **CLIENT** |
| 186 | PAY_CLAIM_LOOKUP | payments | fnDispatch `Host/Main.lean:7158` | - | - | - | native/resource-client/src/pay_claim.rs:580 | - | **CLIENT** |
| 187 | NEXT_KEY_ADOPTION_PLAN | identity | fnDispatch `Host/Main.lean:6963` | - | - | - | native/resource-client/src/key_adoption.rs:197 | deploy/hermes-dispatch/receiving.py | **DRV** |
| 188 | NEXT_KEY_ADOPTION_ASSEMBLE | identity | fnDispatch `Host/Main.lean:6968` | - | - | - | native/resource-client/src/key_adoption.rs:239 | deploy/hermes-dispatch/receiving.py | **DRV** |
| 189 | NEXT_KEY_ADOPTION_SUBMIT | identity | fnDispatch `Host/Main.lean:6976` | - | - | - | native/resource-client/src/key_adoption.rs:298 | deploy/hermes-dispatch/receiving.py | **DRV** |
| 190 | NEXT_KEY_ADOPTION_LOOKUP | identity | fnDispatch `Host/Main.lean:6976` | - | - | - | native/resource-client/src/key_adoption.rs:305 | deploy/hermes-dispatch/receiving.py | **DRV** |
| 191 | CARRY_PAY_CLAIM_LOOKUP | checked-carry/payments | None `Host/Main.lean:-` | - | - | - | - | - | **NONE** |
| 192 | LAW_DIAGNOSTIC | law-diagnostics | None `Host/Main.lean:-` | - | - | - | - | - | **NONE** |
| 193 | APPLICATION_DISPATCH_READY | application-dispatch/member-workspace | fnDispatch `Host/Main.lean:6931` | - | - | - | native/resource-client/src/member_app.rs:304 | - | **CLIENT** |
| 194 | APPLICATION_DISPATCH_AUTHENTICATED_PLAN | application-dispatch/member-workspace | fnDispatch `Host/Main.lean:6941` | - | - | - | native/resource-client/src/member_app.rs:264 | - | **CLIENT** |
| 201 | RESERVE_RESOURCE_BIRTH_PLAN | resource-reserve-birth | fnDispatch `Host/Main.lean:7420` | - | - | - | - | - | **NONE** |
| 202 | RESERVE_RESOURCE_BIRTH_ASSEMBLE | resource-reserve-birth | fnDispatch `Host/Main.lean:7429` | - | - | - | - | - | **NONE** |
| 206 | APPLICATION_FAILED_START_RECOVERY_PREPARE | spk-recovery | fnDispatch `Host/Main.lean:7616` | - | - | - | - | - | **NONE** |
| 207 | APPLICATION_FAILED_START_RECOVERY_ASSEMBLE | spk-recovery | fnDispatch `Host/Main.lean:7629` | - | - | - | - | - | **NONE** |
| 208 | APPLICATION_FAILED_START_RECOVERY_SUBMIT | spk-recovery | fnDispatch `Host/Main.lean:7638` | - | - | - | - | - | **NONE** |
| 209 | APPLICATION_FAILED_START_RECOVERY_LOOKUP | spk-recovery | fnDispatch `Host/Main.lean:7641` | - | - | - | - | - | **NONE** |
| 210 | ACTIVITY_PLAN | activity-native | fnDispatch `Host/Main.lean:7265` | activity,bounty,call,chargedfailure,domain,… (9 rows) | births,perf | - | native/resource-client/src/activity.rs:135 | - | **ROW** |
| 211 | ACTIVITY_ASSEMBLE | activity-native | fnDispatch `Host/Main.lean:7265` | activity,bounty,call,chargedfailure,domain,… (9 rows) | births,perf | - | native/resource-client/src/activity.rs:239 | - | **ROW** |
| 212 | ACTIVITY_SUBMIT | activity-native | fnDispatch `Host/Main.lean:7265` | activity,bounty,call,chargedfailure,domain,… (9 rows) | births,perf | - | native/resource-client/src/activity.rs:254 | - | **ROW** |
| 213 | ACTIVITY_LOOKUP | activity-native | fnDispatch `Host/Main.lean:7265` | activity,bounty,call,chargedfailure,domain,… (9 rows) | births,perf | - | native/resource-client/src/activity.rs:307 | - | **ROW** |
| 214 | ACTIVITY_VIEW | activity-native | fnDispatch `Host/Main.lean:7265` | activity,bounty,call,chargedfailure,domain,… (9 rows) | births,perf | - | native/resource-client/src/activity.rs:100 | - | **ROW** |
| 215 | SEAT_PLAN | seats-native | fnDispatch `Host/Main.lean:7265` | bounty,seats | - | - | native/resource-client/src/seat.rs:125 | - | **ROW** |
| 216 | SEAT_ASSEMBLE | seats-native | fnDispatch `Host/Main.lean:7265` | bounty,seats | - | - | native/resource-client/src/seat.rs:133 | - | **ROW** |
| 217 | SEAT_SUBMIT | seats-native | fnDispatch `Host/Main.lean:7265` | bounty,seats | - | - | native/resource-client/src/seat.rs:142 | - | **ROW** |
| 218 | SEAT_LOOKUP | seats-native | fnDispatch `Host/Main.lean:7265` | bounty,seats | - | - | native/resource-client/src/seat.rs:196 | - | **ROW** |
| 219 | SEAT_VIEW | seats-native | fnDispatch `Host/Main.lean:7265` | bounty,seats | - | - | native/resource-client/src/seat.rs:103 | - | **ROW** |

### 1.2 Consent frames (12)

| frame | meaning (READ `Host/ClientConsentCore.lean`) | client sender (READ) | reach | class |
|---|---|---|---|---|
| 220 | intent consent | `client_consent.rs:249` (`if thin_mode(){230}else{220}`) | every signed op of every row | ROW |
| 221 | observation consent | `client_consent.rs:255` | every signed read/write | ROW |
| 222 | plan consent (`checkIntentPlan`) | `client_consent.rs:259` | every kernel-client write | ROW |
| 224 | specialized consent for operator-authored plans | `client_consent.rs:1101` (`operator_plan`, ops listed `:1093-1095`) | m6grain, journey (enroll), JROT | ROW |
| 226 | possession consent (no Store) | `client_consent.rs:1112` | enrollment (journey J1, welcomecontinuity) | ROW |
| 227 | objective headers | `client_consent.rs:1116`, `bend_session.rs:3` | activity/seats/bounty/call/send/… | ROW |
| 228 · 229 · 233 | anchor offer / return / per-connection recheck | `client_consent.rs:149,223,368,519,540` | resident provider is the default (`MINI_CONSENT_RESIDENT=0` disables) → every row | ROW |
| 230 · 231 · 232 | thin intent / observation / plan | `client_consent.rs:249,255,262` under `thin_mode()` | only `journey.d/jthin-consent.sh` (step THIN, not a landing row) | **DRV — twin of 220-222** |

### 1.3 Host CLI verbs (116)

ROWS = a landing-row driver calls `HOST CONFIG VERB` directly; RUST = a string hit in Rust (mostly `mini`'s
`local_process` one-shot fallback, `main.rs:1245`, which HP-DESIGN §2 deletes); NONE = no caller found.

| Host CLI verb | arm | ROWS (direct) | DRIVER-only | Rust caller (string hit) | class |
|---|---|---|---|---|---|
| `author` | Host/Main.lean:6312 | activity,births,bounty,call | journey.d/jpay-e2.sh, journey.d/jpay-e3.sh | native/spk-host/src/launch_descriptor_native.rs:135, native/spk-host/src/lifecycle_v3_claim_native.rs:228 | **ROW** |
| `objective-quote` | Host/Main.lean:6319 | objective | - | native/resource-client/src/objective_invoke.rs:33 | **ROW** |
| `objective-publication` | Host/Main.lean:6328 | activity,births,bounty,call | - | - | **ROW** |
| `carry-plan` | Host/Main.lean:6352 | - | carry-stage-journey.py | - | **DRV** |
| `carry-receive` | Host/Main.lean:6358 | - | carry-stage-journey.py | - | **DRV** |
| `carry-edge-verify` | Host/Main.lean:6365 | - | - | native/resource-client/src/receipt_continuity/carry.rs:287 | **RUST** |
| `continuity-point` | Host/Main.lean:6370 | - | carry-source-journey.sh, continuity-journey.sh | native/resource-client/src/receipt_continuity.rs:510 | **DRV** |
| `continuity-verify` | Host/Main.lean:6375 | - | continuity-journey.sh, fresh-onboarding-journey.sh | native/resource-client/src/receipt_continuity.rs:579 | **DRV** |
| `profile` | Host/Main.lean:6381 | activity,births,bounty,call | native/grain-runtime/acceptance.sh, acceptance.sh | native/spk-host/src/grain.rs:1428, native/spk-host/src/dispatch_native.rs:431 | **ROW** |
| `pay-claim-status` | Host/Main.lean:6386 | - | - | - | **NONE** |
| `pay-claim-audit` | Host/Main.lean:6395 | - | - | native/resource-client/src/pay.rs:1951 | **RUST** |
| `pay-enrol-v2-context` | Host/Main.lean:6404 | - | - | native/resource-client/src/join_solana_v2.rs:268 | **RUST** |
| `inspect` | Host/Main.lean:6418 | journey,m6grain | inspect-journey.sh, journey.d/j15.sh | native/spk-host/src/launch_descriptor_native.rs:188, native/spk-host/src/lifecycle_v3_claim_native.rs:247 | **ROW** |
| `inspect-agent-lifetime-paid-ingress` | Host/Main.lean:6573 | - | - | native/grain-runtime/src/main.rs:6231 | **RUST** |
| `inspect-accepted-agent-lifetime-grant` | Host/Main.lean:6583 | - | scripts/spk-platform/prepare-lifetime-host-services.sh, scripts/spk-platform/prepare-lifetime-route.sh | - | **DRV** |
| `inspect-stop-claim` | Host/Main.lean:6593 | - | - | native/spk-host/src/lifecycle_v3_stop_service.rs:372, native/spk-host/src/lifecycle_v3_stop_native.rs:526 | **RUST** |
| `derive` | Host/Main.lean:6602 | - | - | native/mini-sdk/tests/golden.rs:25, native/mini-sdk/tests/golden.rs:25 | **RUST** |
| `signatures` | Host/Main.lean:6606 | journey | - | native/spk-host/src/lifecycle_v3_claim_native.rs:271, native/spk-host/src/lifecycle_v3_stop_begin_native.rs:190 | **ROW** |
| `genesis` | Host/Main.lean:6610 | all (via mini bootstrap, main.rs:1450) | - | native/resource-client/src/workspace.rs:4572, native/resource-client/src/workspace.rs:4612 | **ROW** |
| `describe` | Host/Main.lean:6628 | m6grain | scripts/application-current-birth/native-acceptance.sh, scripts/application-share-issue/native-acceptance.sh | native/resource-client/src/shell.rs:70, native/resource-client/src/shell.rs:623 | **ROW** |
| `fn-archive` | Host/Main.lean:6632 | - | scripts/fn-archive-acceptance.py | - | **DRV** |
| `codec` | Host/Main.lean:6647 | all (session) | - | native/resource-client/src/member.rs:227, native/resource-client/src/member.rs:408 | **ROW** |
| `stdio` | Host/Main.lean:6650 | all (session) | scripts/overnight-tests/exact-helper-pinning-session.sh | native/resource-client/src/client_consent.rs:141, native/resource-client/src/transport.rs:1449 | **ROW** |
| `bootstrap` | Host/Main.lean:7797 | all (via mini bootstrap, main.rs:1450) | - | native/resource-client/src/main.rs:1465, native/resource-client/src/main.rs:3806 | **ROW** |
| `store-bench` | Host/Main.lean:7800 | - | - | - | **NONE** |
| `well-ledger` | Host/Main.lean:7803 | - | journey.d/jwell.sh | native/resource-client/src/well.rs:193 | **DRV** |
| `pay-ledger` | Host/Main.lean:7807 | - | - | native/resource-client/src/main.rs:1473, native/resource-client/src/pay.rs:2146 | **RUST** |
| `pay-enrol-ids` | Host/Main.lean:7811 | - | - | native/resource-client/src/join_solana_v2.rs:548, native/resource-client/src/join_solana.rs:957 | **RUST** |
| `pay-enrol-probe` | Host/Main.lean:7816 | - | - | - | **NONE** |
| `pay-job` | Host/Main.lean:7837 | - | - | - | **NONE** |
| `job-money-explain` | Host/Main.lean:7842 | - | journey.d/jjob.sh | - | **DRV** |
| `pay-purse` | Host/Main.lean:7848 | - | - | - | **NONE** |
| `object-roster-inspect` | Host/Main.lean:7853 | - | - | native/resource-client/src/protected_object/object_epoch_cli.rs:205 | **RUST** |
| `object-audience-roster` | Host/Main.lean:7857 | - | - | native/resource-client/src/protected_document_members.rs:352, native/resource-client/src/protected_document.rs:245 | **RUST** |
| `object-audience` | Host/Main.lean:7869 | - | - | native/resource-client/src/protected_document.rs:236, native/resource-client/src/protected_document.rs:406 | **RUST** |
| `audit` | Host/Main.lean:7881 | journey | affordances-journey.sh, carry-source-journey.sh | native/spk-host/src/hostd.rs:582, native/spk-host/src/grain_export.rs:492 | **ROW** |
| `store-audit` | Host/Main.lean:7887 | exchange,journey | - | native/resource-client/src/main.rs:1194, native/resource-client/src/main.rs:4565 | **ROW** |
| `checkpoint-differential` | Host/Main.lean:7905 | - | - | - | **NONE** |
| `presence-index` | Host/Main.lean:7914 | - | journey.d/j10-index.sh | - | **DRV** |
| `reserve-birth-plan` | Host/Main.lean:7919 | - | - | - | **NONE** |
| `reserve-birth-assemble` | Host/Main.lean:7928 | - | - | - | **NONE** |
| `plan-ungated` | Host/Main.lean:7935 | journey | - | - | **ROW** |
| `prepare` | Host/Main.lean:7961 | objective | scripts/workroom/member-acceptance.sh | native/resource-client/src/shell.rs:1156, native/resource-client/src/shell.rs:1160 | **ROW** |
| `enroll-key-plan` | Host/Main.lean:7965 | - | - | - | **NONE** |
| `enroll-key-assemble` | Host/Main.lean:7976 | welcomecontinuity | - | - | **ROW** |
| `enroll-key-submit` | Host/Main.lean:7991 | - | - | - | **NONE** |
| `enroll-key-lookup` | Host/Main.lean:7997 | - | - | - | **NONE** |
| `application-share-issue-plan` | Host/Main.lean:8003 | - | scripts/application-share-issue/native-acceptance.sh | native/resource-client/src/share_issue.rs:518 | **DRV** |
| `application-share-issue-assemble` | Host/Main.lean:8013 | - | - | - | **NONE** |
| `application-grain-share-issue-plan` | Host/Main.lean:8025 | - | scripts/application-share-issue/native-grain-acceptance.sh | - | **DRV** |
| `application-grain-share-issue-assemble` | Host/Main.lean:8035 | - | - | - | **NONE** |
| `challenge-batch` | Host/Main.lean:8047 | - | - | native/resource-client/src/main.rs:2328 | **RUST** |
| `query-batch` | Host/Main.lean:8052 | - | - | native/resource-client/src/main.rs:1368, native/resource-client/src/main.rs:2362 | **RUST** |
| `challenge` | Host/Main.lean:8057 | - | - | native/resource-client/src/hermes_handoff.rs:1282, native/resource-client/src/hermes_handoff.rs:1290 | **RUST** |
| `observe-assemble` | Host/Main.lean:8062 | - | - | native/resource-client/src/client_consent.rs:344, native/resource-client/src/client_consent.rs:1044 | **RUST** |
| `query` | Host/Main.lean:8071 | - | application-acceptance.sh, scripts/workroom/hosted-negative.sh | native/spk-host/src/agent_api_wire.rs:374, native/spk-host/src/export_receipt.rs:112 | **DRV** |
| `pin-plan-height` | Host/Main.lean:8074 | - | - | native/resource-client/src/provider_continuity.rs:417 | **RUST** |
| `assemble` | Host/Main.lean:8080 | journey | scripts/gitweb-content-export/finalize.sh | native/resource-client/src/client_consent.rs:344, native/resource-client/src/client_consent.rs:344 | **ROW** |
| `submit` | Host/Main.lean:8089 | - | - | native/resource-client/src/session_enrollment.rs:431, native/resource-client/src/activity.rs:279 | **RUST** |
| `law-sat` | Host/Main.lean:8092 | - | - | native/resource-client/src/main.rs:1519 | **RUST** |
| `dry-run` | Host/Main.lean:8096 | - | - | native/resource-client/src/inspect_views.rs:265, native/resource-client/src/main.rs:2072 | **RUST** |
| `lookup` | Host/Main.lean:8108 | - | scripts/spk-platform/prepare-install-config.sh | native/resource-client/src/activity.rs:304, native/resource-client/src/shell.rs:85 | **DRV** |
| `selected-release-submit` | Host/Main.lean:8111 | - | - | native/resource-client/src/selected_release.rs:235, native/resource-client/src/main.rs:4410 | **RUST** |
| `selected-release-lookup` | Host/Main.lean:8119 | - | - | native/resource-client/src/main.rs:4457 | **RUST** |
| `application-lifecycle-begin-submit` | Host/Main.lean:8127 | - | - | - | **NONE** |
| `application-lifecycle-begin-lookup` | Host/Main.lean:8135 | - | - | - | **NONE** |
| `application-lifecycle-claim-lookup` | Host/Main.lean:8143 | - | - | - | **NONE** |
| `application-lifecycle-completion-submit` | Host/Main.lean:8151 | - | - | - | **NONE** |
| `application-lifecycle-completion-lookup` | Host/Main.lean:8159 | - | - | - | **NONE** |
| `diagnose-completion` | Host/Main.lean:8167 | - | - | - | **NONE** |
| `selected-source-publication-submit` | Host/Main.lean:8187 | - | - | native/resource-client/src/selected_publisher.rs:206, native/resource-client/src/selected_publisher.rs:536 | **RUST** |
| `selected-source-publication-lookup` | Host/Main.lean:8195 | - | - | native/resource-client/src/selected_publisher.rs:256, native/resource-client/src/selected_publisher.rs:306 | **RUST** |
| `application-share-issue-submit` | Host/Main.lean:8203 | - | - | - | **NONE** |
| `application-share-issue-lookup` | Host/Main.lean:8211 | - | - | - | **NONE** |
| `application-grain-share-issue-submit` | Host/Main.lean:8219 | - | - | - | **NONE** |
| `application-grain-share-issue-lookup` | Host/Main.lean:8227 | - | - | - | **NONE** |
| `selected-release-source-plan` | Host/Main.lean:8235 | - | - | native/resource-client/src/selected_publisher.rs:42 | **RUST** |
| `selected-release-source-assemble` | Host/Main.lean:8247 | - | - | native/resource-client/src/selected_publisher.rs:59 | **RUST** |
| `selected-release-source-check` | Host/Main.lean:8254 | - | - | native/resource-client/src/selected_exchange.rs:364, native/resource-client/src/selected_publisher.rs:440 | **RUST** |
| `selected-release-check-preimage` | Host/Main.lean:8259 | - | - | native/resource-client/src/main.rs:1046 | **RUST** |
| `selected-release-prepare` | Host/Main.lean:8265 | exchange | selected-release-acceptance.sh | native/resource-client/src/selected_exchange.rs:308 | **ROW** |
| `selected-release-assemble` | Host/Main.lean:8275 | exchange | selected-release-acceptance.sh | native/resource-client/src/selected_exchange.rs:339 | **ROW** |
| `selected-release-ingress` | Host/Main.lean:8284 | exchange | selected-release-acceptance.sh | - | **ROW** |
| `selected-release-fn-poll` | Host/Main.lean:8293 | - | - | native/resource-client/src/selected_exchange.rs:416 | **RUST** |
| `selected-release-fn-legacy-poll` | Host/Main.lean:8301 | exchange | - | native/resource-client/src/selected_exchange.rs:519 | **ROW** |
| `selected-release-fn-ack` | Host/Main.lean:8309 | - | - | native/resource-client/src/selected_exchange.rs:635 | **RUST** |
| `fn-empty-page-ack` | Host/Main.lean:8317 | - | - | - | **NONE** |
| `fn-frontier-request` | Host/Main.lean:8325 | - | - | native/resource-client/src/fn_frontier.rs:243 | **RUST** |
| `fn-frontier-export` | Host/Main.lean:8334 | - | - | native/resource-client/src/fn_frontier.rs:273 | **RUST** |
| `fn-frontier-plan` | Host/Main.lean:8344 | - | - | native/resource-client/src/main.rs:4260 | **RUST** |
| `fn-frontier-assemble` | Host/Main.lean:8364 | - | - | - | **NONE** |
| `fn-selected-poll-submit` | Host/Main.lean:8385 | - | - | - | **NONE** |
| `fn-selected-poll-lookup` | Host/Main.lean:8393 | - | - | - | **NONE** |
| `fn-empty-poll-submit` | Host/Main.lean:8401 | - | - | - | **NONE** |
| `fn-empty-poll-lookup` | Host/Main.lean:8409 | - | - | - | **NONE** |
| `export-evidence` | Host/Main.lean:8417 | - | - | native/resource-client/src/main.rs:4468, native/resource-client/src/main.rs:4480 | **RUST** |
| `verify-evidence` | Host/Main.lean:8422 | - | - | native/resource-client/src/main.rs:4483, native/resource-client/src/main.rs:4495 | **RUST** |
| `grain-origin-prepare` | Host/Main.lean:8427 | - | - | - | **NONE** |
| `portable-verify-fn` | Host/Main.lean:8459 | - | - | native/resource-client/src/main.rs:2544 | **RUST** |
| `consumer-verify-poll-files` | Host/Main.lean:8484 | - | - | native/resource-client/src/main.rs:2545 | **RUST** |
| `portable-consumer-decide` | Host/Main.lean:8515 | - | - | native/resource-client/src/main.rs:2546 | **RUST** |
| `poll-consumer-decide` | Host/Main.lean:8585 | - | - | native/resource-client/src/main.rs:2547 | **RUST** |
| `consumer-poll-decide` | Host/Main.lean:8590 | - | - | native/resource-client/src/main.rs:2548 | **RUST** |
| `reply-consumer-poll-decide` | Host/Main.lean:8615 | - | - | native/resource-client/src/main.rs:2552 | **RUST** |
| `reply-consumer-export-result` | Host/Main.lean:8622 | - | - | native/resource-client/src/main.rs:2553 | **RUST** |
| `reply-consumer-ack-poll` | Host/Main.lean:8640 | - | - | native/resource-client/src/main.rs:2554 | **RUST** |
| `consumer-export-inbox` | Host/Main.lean:8708 | - | - | native/resource-client/src/main.rs:2549 | **RUST** |
| `consumer-export-poll` | Host/Main.lean:8722 | - | - | native/resource-client/src/main.rs:2550 | **RUST** |
| `consumer-ack-poll` | Host/Main.lean:8742 | - | - | native/resource-client/src/main.rs:2551 | **RUST** |
| `consumer-export-reply` | Host/Main.lean:8812 | - | - | native/resource-client/src/main.rs:2555, native/resource-client/src/main.rs:4642 | **RUST** |
| `consumer-stage-reply-plan` | Host/Main.lean:8824 | - | - | native/resource-client/src/main.rs:2556 | **RUST** |
| `consumer-stage-reply-sign` | Host/Main.lean:8916 | - | - | native/resource-client/src/main.rs:2557 | **RUST** |
| `consumer-decide-test` | Host/Main.lean:9121 | - | - | native/resource-client/src/main.rs:2558 | **RUST** |
| `store-epoch` | Host/Main.lean:6290 | hostupgrade | - | - | **ROW** |
| `objective-constants` | Host/Main.lean:6295 | activity,births,bounty,call | - | - | **ROW** |
| `objective-front` | Host/Main.lean:6300 | - | - | native/resource-client/src/workspace/studio_preview.rs:72 | **RUST** |

### 1.4 `mini` verbs (127)

| mini verb | dispatch | ops it sends (DERIVED, module scan) | ROWS | DRIVER-only | class |
|---|---|---|---|---|---|
| `join` | main.rs:3197 | 4,5,8,10,86,87,88,89,112,121,181,182 | welcomecontinuity | journey.d/jpay-e4.sh, journey.d/jpay-v2.sh | **ROW** |
| `socket-proxy` | main.rs:3203 | - | - | - | **NONE** |
| `workspace` | main.rs:3209 | 0-11 via process() | activity,births,bounty,call,… (27) | affordances-journey.sh, carry-source-journey.sh (+68) | **ROW** |
| `member` | main.rs:3210 | - | - | - | **NONE** |
| `web` | main.rs:3212 | - | journey,jserve,m7,rooms | doc-search-journey.py, doc-search-protected-check.py (+2) | **ROW** |
| `operation-proof` | main.rs:3214 | - | - | - | **NONE** |
| `enroll` | main.rs:3216 | 4,5,8,10,86,87,88,89 | exchange,hermes,journey,jserve,… (8) | journey.d/j12c-kernel.sh, journey.d/j12e.sh (+2) | **ROW** |
| `clock` | main.rs:3217 | 7,8,126,127,128,129 | activity,births,bounty,call,… (25) | deploy/hermes-dispatch/receiving.py, journey-timers/ticker.sh (+4) | **ROW** |
| `checkpoint` | main.rs:3218 | 7,8,170,171,172,173 | births,hostupgrade,journey,jserve,… (7) | journey-timers/ticker.sh, journey.d/jtail.sh (+1) | **ROW** |
| `job` | main.rs:3220 | 7,8,107,129,132,134,160,161,162,163 | - | journey.d/jjob-money.sh, journey.d/jjob.sh (+3) | **DRV** |
| `activity` | main.rs:3221 | 7,8,210,211,212,213,214 | activity,births,bounty,call,… (11) | - | **ROW** |
| `seat` | main.rs:3222 | 7,8,215,216,217,218,219 | bounty,seats | - | **ROW** |
| `shell` | main.rs:3224 | - | journey,jserve,m7,rooms | deploy/hermes-dispatch/receiving.py, journey.d/jnames.sh (+10) | **ROW** |
| `key` | main.rs:3228 | 144 | jpay | journey.d/jhide.sh, native/grain-runtime/journeys/byok-native.py (+2) | **ROW** |
| `fleet` | main.rs:3237 | 96,97,98,99,100,101,102,180 | m8 | fleet-contention.sh, journey.d/j17.sh | **ROW** |
| `relay` | main.rs:3239 | - | - | journey.d/jchan-client.sh, journey.d/jchan-relay.sh | **DRV** |
| `relay-emit` | main.rs:3241 | - | - | journey.d/jchan-relay.sh | **DRV** |
| `relay-witness` | main.rs:3243 | - | - | journey.d/jchan-client.sh, journey.d/jchan-relay.sh | **DRV** |
| `relay-key` | main.rs:3245 | - | - | journey.d/jchan-client.sh, journey.d/jchan-relay.sh | **DRV** |
| `channel` | main.rs:3247 | - | - | journey.d/jchan-client.sh | **DRV** |
| `traffic` | main.rs:3249 | - | - | - | **NONE** |
| `mix` | main.rs:3251 | - | - | cohort-native-tcp.py | **DRV** |
| `mix-live` | main.rs:3253 | - | - | cohort-native-tcp.py, scripts/cohort-native-tcp.py (+1) | **DRV** |
| `adopt-next-key` | main.rs:3255 | 6,8,144,187,188,189,190 | - | deploy/hermes-dispatch/receiving.py | **DRV** |
| `rotate-key` | main.rs:3257 | 7,8,140,141,142,143,144 | journey | deploy/hermes-dispatch/receiving.py, journey.d/jpay-v2.sh (+1) | **ROW** |
| `key-status` | main.rs:3259 | 7,8,140,141,142,143,144 | journey,rooms | - | **ROW** |
| `credit` | main.rs:3261 | - | - | journey.d/j14.sh, journey.d/j17.sh (+1) | **DRV** |
| `hermes-handoff` | main.rs:3262 | 144 | - | deploy/hermes-dispatch/receiving.py, testing/journeys/shared-resident-useful-work.py | **DRV** |
| `story-law` | main.rs:3264 | - | - | scripts/gen-storylaw.py | **DRV** |
| `well` | main.rs:3265 | 123,124,125 | bounty,seats | journey.d/j10c.sh, journey.d/jwell.sh | **ROW** |
| `pay` | main.rs:3266 | 107,112,129,181 | journey,jpay,jserve,m7,rooms | journey.d/jjob-money.sh, journey.d/jjob.sh (+7) | **ROW** |
| `pay-claim` | main.rs:3268 | 182,183,184,185,186 | - | - | **NONE** |
| `enrollment-bootstrap` | main.rs:3270 | - | - | journey.d/jpay-bootstrap-budget.py, journey.d/jpay-e4.sh | **DRV** |
| `enrollment-view` | main.rs:3271 | - | - | journey.d/jpay-bootstrap-budget.py, journey.d/jpay-e4.sh (+1) | **DRV** |
| `selected-exchange` | main.rs:3279 | - | exchange | - | **ROW** |
| `serve` | main.rs:3290 | - | activity,births,bounty,call,… (27) | affordances-journey.sh, application-acceptance.sh (+54) | **ROW** |
| `consent-resident` | main.rs:3305 | 222,228,229,232,233 | - | - | **NONE** |
| `serve-operator` | main.rs:3312 | - | m6grain | journey.d/jpay-bootstrap-budget.py, journey.d/jpay-e4.sh (+2) | **ROW** |
| `serve-public-proxy` | main.rs:3325 | - | m6grain | journey.d/jpay-bootstrap-budget.py, journey.d/jpay-e4.sh (+2) | **ROW** |
| `drain-operator` | main.rs:3337 | - | - | - | **NONE** |
| `operator-status` | main.rs:3337 | - | - | testing/journeys/shared-resident-useful-work.py | **DRV** |
| `host-command` | main.rs:3348 | - | - | - | **NONE** |
| `consumer-poll` | main.rs:3356 | - | - | - | **NONE** |
| `reply-consumer-poll` | main.rs:3356 | - | - | - | **NONE** |
| `consumer-ack` | main.rs:3376 | - | - | - | **NONE** |
| `reply-consumer-ack` | main.rs:3376 | - | - | - | **NONE** |
| `origin-outbox-prepare` | main.rs:3401 | - | - | - | **NONE** |
| `origin-outbox-export` | main.rs:3416 | - | - | - | **NONE** |
| `origin-publish` | main.rs:3434 | 18 | - | - | **NONE** |
| `provider-continuity` | main.rs:3460 | 17 | - | - | **NONE** |
| `continuity` | main.rs:3475 | - | - | - | **NONE** |
| `meter` | main.rs:3491 | 19 | - | - | **NONE** |
| `consumer-drain-once` | main.rs:3511 | - | - | - | **NONE** |
| `reply-consumer-drain-once` | main.rs:3511 | - | - | - | **NONE** |
| `consumer-resume-ack` | main.rs:3545 | - | - | - | **NONE** |
| `reply-consumer-resume-ack` | main.rs:3545 | - | - | - | **NONE** |
| `consumer-host-upgrade` | main.rs:3568 | - | - | - | **NONE** |
| `consumer-worker` | main.rs:3602 | - | - | - | **NONE** |
| `reply-consumer-worker` | main.rs:3602 | - | - | - | **NONE** |
| `store` | main.rs:3624 | - | activity,births,bounty,call,… (27) | - | **ROW** |
| `audit` | main.rs:3625 | 0-11 via process() | rooms | fleet-sign-growth.sh, journey.d/j10c.sh (+10) | **ROW** |
| `describe` | main.rs:3637 | - | - | scripts/overnight-tests/exact-helper-pinning-session.sh, scripts/overnight-tests/exact-readback-session.sh | **DRV** |
| `profile` | main.rs:3637 | 0-11 via process() | jpay | journey.d/jpay-e4.sh, journey.d/jpay-v2.sh | **ROW** |
| `enc-public` | main.rs:3649 | 0-11 via process() | - | - | **NONE** |
| `enc-key-id` | main.rs:3660 | 0-11 via process() | - | - | **NONE** |
| `escrow-recover` | main.rs:3672 | 0-11 via process() | - | - | **NONE** |
| `keygen` | main.rs:3695 | - | activity,births,bounty,call,… (27) | acceptance.sh, application-acceptance.sh (+26) | **ROW** |
| `verify-view` | main.rs:3728 | - | - | journey.d/jhide.sh | **DRV** |
| `bootstrap` | main.rs:3806 | - | activity,births,bounty,call,… (25) | acceptance.sh, application-acceptance.sh (+14) | **ROW** |
| `author` | main.rs:3817 | - | jserve,m6grain | authority-acceptance.sh, journey-stranger.py (+5) | **ROW** |
| `inspect` | main.rs:3826 | - | - | - | **NONE** |
| `current-application-intent` | main.rs:3840 | - | m6grain | scripts/application-current-birth/native-acceptance.sh, scripts/spk-platform/same-store-app.py | **ROW** |
| `current-resource-intent` | main.rs:3840 | - | - | - | **NONE** |
| `current-session-intent` | main.rs:3840 | - | - | scripts/spk-platform/ws-continuity-fixture.py | **DRV** |
| `agent-reserve-plan` | main.rs:3868 | 2,3,58,59,74,75,76,77,78,79,80,81,92,93 | - | - | **NONE** |
| `agent-reserve-seal` | main.rs:3886 | 2,3,58,59,74,75,76,77,78,79,80,81,92,93 | - | - | **NONE** |
| `agent-reserve-submit` | main.rs:3893 | 2,3,58,59,74,75,76,77,78,79,80,81,92,93 | - | - | **NONE** |
| `agent-reserve-lookup` | main.rs:3899 | 2,3,58,59,74,75,76,77,78,79,80,81,92,93 | - | - | **NONE** |
| `agent-lifetime-reserve-plan` | main.rs:3905 | 2,3,58,59,74,75,76,77,78,79,80,81,92,93 | - | - | **NONE** |
| `agent-lifetime-reserve-seal` | main.rs:3923 | 2,3,58,59,74,75,76,77,78,79,80,81,92,93 | - | - | **NONE** |
| `agent-lifetime-reserve-submit` | main.rs:3930 | 2,3,58,59,74,75,76,77,78,79,80,81,92,93 | - | - | **NONE** |
| `agent-lifetime-reserve-lookup` | main.rs:3936 | 2,3,58,59,74,75,76,77,78,79,80,81,92,93 | - | - | **NONE** |
| `agent-lifetime-paid-plan` | main.rs:3942 | 2,3,58,59,74,75,76,77,78,79,80,81,92,93 | - | - | **NONE** |
| `agent-lifetime-paid-payer-sign` | main.rs:3950 | 2,3,58,59,74,75,76,77,78,79,80,81,92,93 | - | - | **NONE** |
| `agent-lifetime-paid-seal` | main.rs:3957 | 2,3,58,59,74,75,76,77,78,79,80,81,92,93 | - | - | **NONE** |
| `agent-lifetime-paid-submit` | main.rs:3964 | 2,3,58,59,74,75,76,77,78,79,80,81,92,93 | - | - | **NONE** |
| `agent-lifetime-paid-lookup` | main.rs:3970 | 2,3,58,59,74,75,76,77,78,79,80,81,92,93 | - | - | **NONE** |
| `agent-lifetime-grant-plan` | main.rs:3976 | 72,73,74,75,80,81,92,93,94,95 | - | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| `agent-lifetime-grant-seal` | main.rs:3986 | 72,73,74,75,80,81,92,93,94,95 | - | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| `agent-lifetime-grant-submit` | main.rs:3993 | 72,73,74,75,80,81,92,93,94,95 | - | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| `agent-lifetime-grant-lookup` | main.rs:3999 | 72,73,74,75,80,81,92,93,94,95 | - | scripts/spk-platform/issue-agent-lifetime-grant.sh | **DRV** |
| `session-reenroll` | main.rs:4005 | - | - | - | **NONE** |
| `session-enrollment-plan` | main.rs:4022 | 82,83,84,85 | m6grain | - | **ROW** |
| `session-enrollment-seal` | main.rs:4032 | 82,83,84,85 | m6grain | - | **ROW** |
| `session-enrollment-submit` | main.rs:4039 | 82,83,84,85 | m6grain | - | **ROW** |
| `session-enrollment-lookup` | main.rs:4045 | 82,83,84,85 | m6grain | - | **ROW** |
| `agent-payer-sign` | main.rs:4051 | 48 | - | - | **NONE** |
| `share-issue-prepare` | main.rs:4073 | 28,29,32,33 | - | scripts/application-share-issue/native-acceptance.sh | **DRV** |
| `share-issue-submit` | main.rs:4086 | 28,29,32,33 | - | scripts/application-share-issue/native-acceptance.sh | **DRV** |
| `share-issue-lookup` | main.rs:4092 | 28,29,32,33 | - | scripts/application-share-issue/native-acceptance.sh | **DRV** |
| `share-issue-receipt-lookup` | main.rs:4098 | - | - | - | **NONE** |
| `grain-share-issue-plan` | main.rs:4130 | 54,55,56,57 | m6grain | scripts/spk-platform/issue-agent-ticket.sh, scripts/spk-platform/issue-human-ticket.sh (+1) | **ROW** |
| `grain-share-issue-prepare` | main.rs:4142 | 54,55,56,57 | m6grain | scripts/application-share-issue/native-grain-acceptance.sh, scripts/spk-platform/issue-agent-ticket.sh (+2) | **ROW** |
| `grain-share-issue-submit` | main.rs:4155 | 54,55,56,57 | m6grain | scripts/application-share-issue/native-grain-acceptance.sh, scripts/application-share-issue/resume-prepared-native-grain.sh (+2) | **ROW** |
| `grain-share-issue-lookup` | main.rs:4161 | 54,55,56,57 | m6grain | scripts/application-share-issue/native-grain-acceptance.sh, scripts/application-share-issue/resume-prepared-native-grain.sh (+5) | **ROW** |
| `grain-share-issue-receipt-lookup` | main.rs:4167 | - | - | native/grain-runtime/agent-two-participant-preflight.sh | **DRV** |
| `historical-call-receipt-lookup` | main.rs:4199 | 3 | - | - | **NONE** |
| `fn-namespace-plan` | main.rs:4231 | 40,41,42,43 | - | - | **NONE** |
| `fn-namespace-register` | main.rs:4240 | 40,41,42,43 | - | - | **NONE** |
| `fn-namespace-lookup` | main.rs:4251 | 40,41,42,43 | - | - | **NONE** |
| `fn-frontier-plan` | main.rs:4260 | 64,65 | - | - | **NONE** |
| `fn-frontier-advance` | main.rs:4280 | 64,65 | - | - | **NONE** |
| `fn-frontier-lookup` | main.rs:4291 | 64,65 | - | - | **NONE** |
| `submit` | main.rs:4299 | - | hermes,jpay,m6grain,objective | acceptance.sh, application-acceptance.sh (+25) | **ROW** |
| `query` | main.rs:4327 | 0-11 via process() | births,exchange,jpay,m6grain,… (6) | acceptance.sh, application-acceptance.sh (+31) | **ROW** |
| `objective-invoke` | main.rs:4372 | - | objective | - | **ROW** |
| `retry` | main.rs:4389 | - | journey,jserve,m6grain,m7,rooms | acceptance.sh, application-acceptance.sh (+13) | **ROW** |
| `selected-release-submit` | main.rs:4410 | 20,21 | exchange | selected-release-acceptance.sh | **ROW** |
| `selected-release-sign` | main.rs:4422 | - | exchange | selected-release-acceptance.sh | **ROW** |
| `selected-source-sign` | main.rs:4432 | - | - | selected-source-publisher-acceptance.sh | **DRV** |
| `selected-source-publish` | main.rs:4446 | - | - | selected-source-publisher-acceptance.sh | **DRV** |
| `selected-release-lookup` | main.rs:4457 | 20,21 | - | selected-release-acceptance.sh | **DRV** |
| `selected-release-retry` | main.rs:4463 | 20,21 | - | - | **NONE** |
| `export-evidence` | main.rs:4468 | 0-11 via process() | - | - | **NONE** |
| `verify-evidence` | main.rs:4483 | 0-11 via process() | - | - | **NONE** |

`mini workspace` actions reached by a landing row (DERIVED, lower bound): create, describe, import, inspect, propose,
provision, provision-lookup, publish-delegation, read, room-key, submit, tail. Not seen in any driver text (but possibly
reached through `mini shell` lines — blind spot): can, context-review, continuity-carry{,-authority,-verifier},
doc-{accept,context,device,epoch-export,epoch-import,links,membership-recover,protect,protect-current,protect-recover,
pull,push,range,revoke,search,search-follow,share}, forget, found, instance-{call,create,show}, invite, invite-check,
kick, kind-{construct,create,show}, law-{check,export-show,show}, list, market-{bid,bids,reveal,settle}, move, open,
pin-member, program-create, register, remove, rewrap, room-kick, rotate, shared-name, splice, sync, transition, who.

### 1.5 Follower / export, SPK broker, spk-host, grain

- `turn-log-follower export|follow` (`Host/TurnLogFollower.lean:1-14`): **no landing row, no gate** (READ: only
  `scripts/kern/turn-log-follower.sh`). DRV.
- SPK broker (14: identify, init-store, place, set-cgroup, ingest, mount-volume, unmount, adopt-runtime,
  runtime-status, install-unit, start, stop, export-volume, backup) and spk-host verbs: reached only through m6grain's
  `scripts/spk-platform/two-world-journey.sh` (known-red at main, `required-rows` `known-red m6grain`). The broker's
  verbs are a serde `tag = "verb"` enum (`broker.rs:291-363`), so a text scan cannot see which are sent. ASSUMED
  reached: init-store, place, ingest, start, stop, unmount, backup, runtime-status (driver text mentions them);
  `identify`, `set-cgroup`, `mount-volume`, `export-volume` have **no mention in any driver** (DERIVED). Settle: the
  broker's per-request log line in m6grain's `broker-*.log` (kept by `journey-rows` `product_keep … broker-*.log`).
- grain-runtime calls `mini submit`/`retry --mode lookup` and the Host's `inspect outcome`,
  `inspect-agent-lifetime-paid-ingress` (ARCHITECTURE §3.6); reached by row `hermes`.

## 2. KEEP and DELETE

**KEEP (exercised by a landing row): 86 opcodes, 9 consent frames, 23 Host CLI verbs, 40 `mini` verbs, ≥12 workspace
actions.** Of the 86 ops, 21 are spk/spk-lifecycle ops whose only row is known-red m6grain (ASSUMED reach).

**DELETE outright (no row, no driver, no production sender): 43 opcodes** — 12-15 (fn poll/ack session ops; the fn
consumer path uses Host CLI verbs, not these), 23, 27, 35, 47 (lifecycle/dispatch/agent *lookups* nobody sends),
44, 45, 50-53 (lifecycle plan/assemble session twins of the operator 66-71 route), 60-63 (fn selected-coverage /
empty-progress), 103-106 (pay command), 108-111 (pay observation), 117-120 (pay self-enrollment), 131, 133, 135-137
(nock check/sample/app-poke/peek/state), 191, 192 (reserved), 201, 202 (reserve resource birth), 206-209 (failed-start
recovery). **30 Host CLI verbs** (table 1.3 class NONE, incl. store-bench, checkpoint-differential, pay-purse,
pay-job, pay-enrol-probe, pay-claim-status, reserve-birth-*, enroll-key-plan/submit/lookup, every
application-*-submit/lookup one-shot, fn-*-poll-* one-shots, grain-origin-prepare, diagnose-completion).
**56 `mini` verbs** with no driver.

**DELETE after one decision (reached only by DRIVER-only scripts or by a client path no row runs): 26 + 31 ops.**
- DRV-only 26: 28, 29, 32, 33 (share issue), 72-75, 80, 81 (agent lifetime grant/reserve), 92-95 (participant
  provisioning; m3's driver uses enroll, not these), 130, 150 (dry-run, law-sat: J12A/JLS only), 132, 134 (nock show,
  dry run: world_prototype, JN*), 160-163 (job money: JJOBM), 187-190 (next-key adoption).
  Decision: either a landing row that runs them, or delete. Each names a product (jobs, affordances `can`, key
  adoption) — the call is Ember's (CHARTER: what the end system does), not mine.
- CLIENT-only 31: 16-19 (fn origin outbox, provider continuity/usage), 24, 25 (host-only selected source publication),
  31, 91 (session/resource current birth), 40-43, 64, 65 (fn namespace, fn frontier), 58, 59, 77 (agent reserve),
  113-116 (pay refill), 121, 182-186 (pay enrollment quote, pay claim — JPAY rows do not reach them: `jpay-v2.sh` is
  not in `row_jpay`'s 1-4,6), 151, 153 (receipt continuity, carry lookup), 193, 194 (member dispatch). A client that
  sends an op no row runs is unverified code on both sides.
- Consent 230-232 (thin): a twin of 220-222 behind an env switch.

## 3. TWINS

| id | shape A | shape B | where (READ) | verdict |
|---|---|---|---|---|
| P1 | one-shot CLI verb per session op: `prepare submit lookup challenge challenge-batch query query-batch author inspect signatures observe-assemble assemble describe profile dry-run law-sat` + `selected-release-submit/lookup`, `selected-source-publication-*`, `application-lifecycle-*-submit/lookup`, `application-(grain-)share-issue-*`, `enroll-key-*`, `fn-*-poll-submit/lookup`, `reserve-birth-*` (≈45 verbs) | the session ops 0-11, 130, 150, 20-29, 38-39, 54-57, 60-63, 86-89, 201-202 | `Host/Main.lean:6312-9139` vs `:1997-2170`; caller `mini` `local_process` `main.rs:1245` | delete the CLI twins with `local_process` (HP-DESIGN §2 already says a workspace without a socket is an error) |
| P2 | per-family plan/assemble/submit/lookup opcodes (≈38 families × 4) | ops 1/11/2/3, whose `SignedCall` is already a sum `birth | invoke | install | delegate | revoke | renounce` (`Compiler/NativeHostCodec.lean:154`) | registry | one plan/assemble/submit/lookup; the family is the payload's kind |
| P3 | ops 44,45,50-53 (lifecycle plan/assemble, session route) | ops 66-71 (launch begin/claim/completion plan/assemble, operator route, v4 retry first) | `launchLifecycleOperatorOp` `Host/Main.lean:6137` | 44/45/50-53 unreached: delete |
| P4 | 34 dispatch submit | 164 route-bound dispatch submit (same receiver, extra route check) | `serveFrame` `:2624-2636`; `dispatch_native.rs:571-572,1028` | one submit with the route as a field |
| P5 | thin consent 230-232 | full consent 220-222 | `client_consent.rs:249-262` | keep one |
| P6 | consent 224 specialized, 226 possession, 227 objective headers | 222 plan consent (they are all "re-derive the plan of kind K") | `client_consent.rs:1093-1129` | one plan-consent frame keyed by kind |
| P7 | anchor frames 228/229/233 | session open | `ClientConsentCore.lean:524-550` | part of the provider's open/resume |
| P8 | `challenge-batch`/`query-batch` socket verbs | `challenge`/`query` on the same ops 4/5 | `main.rs:1325-1328` | batch is a payload shape, not a verb |
| P9 | 3 copies of the v2 socket envelope | | `transport.rs:1110-1120`, `spk-host dispatch_native.rs:531-541`, `mini-keys server/native.rs:55-59` | one SDK function |
| P10 | `object-audience`, `object-roster-inspect`, `object-audience-roster` (socket verbs on op 8) | `inspect KIND` | `main.rs:1331-1336` | inspect kinds |
| P11 | pay views 107, 112, 121, 181, 182, clock view 129, key status 144, certify view 173, activity view 214, seat view 219, fleet head/receipt/poll/ledger 100-102/180, current births 30/31/91, stream renew 152, route inspect 154, dispatch ready 193 | op 5 authorized query | registry | one query op; the view is a kind |
| P12 | stale Rust socket-filter arms 130-133 "C14 TAIL-BOUND" | 170-173 | `transport.rs:487,591-595` | delete (the comment admits it) |
| P13 | mini `key-service*` verbs that only refuse ("gone") | — | ARCHITECTURE §4.5 | delete |

## 4. THE COLLAPSED DESIGN

**One dispatch, one table, ≤ 12 operations.** Every surviving family already has the shape plan → custody signs →
assemble → submit → lookup (ARCHITECTURE §4.1 last paragraph); the opcode encodes *which family* only because each
family grew its own codec. Collapse the family into the payload's kind:

| new op | absorbs | count absorbed |
|---|---|---|
| `describe` | 0, 6 | 2 |
| `challenge` | 4 | 1 |
| `query KIND` | 5 and every view (P11) | ~20 |
| `plan KIND` | 1 and every `*_PLAN` (32, 36, 42, 48, 56, 66, 68, 70, 74, 78, 80, 82, 86, 92, 96, 113, 123, 126, 140, 160, 170, 183, 187, 210, 215) | ~26 |
| `assemble` (pure) | 10, 11 and every `*_ASSEMBLE` | ~26 |
| `submit` | 2 and every `*_SUBMIT` incl. streamed 34/164, 46, 76 | ~28 |
| `lookup` | 3 and every `*_LOOKUP` | ~25 |
| `codec KIND` (pure) | 7, 8, 9 | 3 |
| `dry-run` | 130 | 1 (if kept) |
| `law-sat` | 150 | 1 (if kept) |

That is **10 operations** for every family that has a landing row today (activity, seats, clock, certify, fleet,
identity enrollment + key rotation, selected release, realm well, pay view, spk share/lifecycle/dispatch/session
enrollment, hermes agent dispatch/lifetime). The receivers do not merge: each `submit` decodes one `SignedCall` and
routes to exactly one receiver by its constructor; the theorem the table must carry is "every (op, kind) names exactly
one receiver" — today it is a Python regex gate (`scripts/host-operations.py`), not a theorem.

**CLI verbs become thin clients of session ops.** Survivors of `run`: `stdio` (the session), `genesis`, `bootstrap`,
`audit`/`store-audit` (re-admission), `store-epoch`, and the authoring verbs the rows call (`objective-constants`,
`objective-publication`, `objective-quote`, `author objective-policy`, `objective-front`) — ≈ 10 verbs, against
116. Everything else is `mini` over the socket. `codec` (the storeless loop) goes when the resident answers `codec`.

**Consent: 12 frames → 2.** `consent{intent|observation|plan KIND}` (220/221/222/224/226/227 merged: they are all
"re-derive what custody signs from the provider's own prefix", differing only by kind) + the provider's open/resume
(228/229/233). Thin 230-232 deleted (or *made* the one mode: a genuine design fork for CONSENT).

**Theorems and gates whose statements mention deleted ops (the reads the cut must do).**
- `scripts/host-operations.py` (gate `host-operations`, in `local-gates.sh` and `merge-gate-checks.sh`): parses
  `dispatchSession`, `fnDispatch`, `serveFrame` and `transport.rs` `allowed_operation`/`allowed_operator_operation`;
  every deleted op must leave the registry, the three Lean matches and both Rust filters in one commit or it goes red.
- `client_consent.rs:1093-1095` `plan_operation` list (31 ops) — consent's notion of "operator plan"; deleted ops
  must leave it.
- `Kernel/NativeHostReplay.lean:976` `NativeAdmission` (51 constructors) — `audit`/`verifyLoaded` re-admits every
  ingress kind; a deleted submit family's constructor and its replay theorem go with it (H1 of ARCHITECTURE §6.10).
- Receiver modules of the 43 NONE ops (DERIVED `proto/recvmods.py`; theorem counts by `^theorem`):
  `PayCellDomain` (11 theorems; shared with the kept 107/112 — read before cutting), `NativeHostReserveBirth` (1),
  `NativeReserveBirthAuthoring` (0), `ApplicationFailedStartRecoveryAuthoring`/`…Endpoint` (0),
  `ApplicationLifecycle{Begin,Claim,Completion}Operator` (0), `NockProgramCell` (0), `NockDoor` (10), `Run` (36),
  `Evaluator` (25) — the last three are shared with kept Nock/job paths (JN*, JJOB): **they stay**; only the 131/133/
  135-137 arms go.
- `Kernel/ApplicationFailedCreateRetryEvidence.lean`, `ApplicationLifecycle*RetryV4*` (≈30 files) — reached by 66-71's
  v4 retry route first; m6grain is the only row; keep until m6grain is green or the retry is redesigned as a new birth
  (ARCHITECTURE H2).

## 5. ORDER OF CUTS (smallest-safest first)

| # | cut | rows that must stay green | opcodes | Host CLI verbs | mini verbs | Host/Main lines (est., DERIVED from arm spans) |
|---|---|---|---|---|---|---|
| 0 | registry-only: reserved 191, 192; stale transport arms 130-133 (P12) | host-operations gate | 186 → 184 | 116 | 127 | 9,163 |
| 1 | the 41 active NONE ops (§2) — arms, receivers' authoring wrappers, filters, registry | all rows (none reaches them) | 184 → 143 | 116 | 127 | −361 arm lines → ~8,800 |
| 2 | the 30 NONE Host CLI verbs | all rows | 143 | 116 → 86 | 127 | ~−700 → ~8,100 |
| 3 | the 56 NONE `mini` verbs + `key-service*` | all rows | 143 | 86 | 127 → 71 | 0 (Rust: main.rs and modules) |
| 4 | delete `local_process` (HP-4) and the one-shot CLI twins (P1) | journey, rooms, m3, m4, welcomecontinuity (they serve a socket already) | 143 | 86 → ~10 | 71 | ~−1,500 → ~6,600 |
| 5 | consent: thin 230-232 gone; 224/226/227 into 222 by kind; anchors into open | journey, activity, m6grain, welcomecontinuity | — | — | — | consent core ~−40% (ASSUMED) |
| 6 | Ember's decision on the 26 DRV-only + 31 CLIENT-only ops: give each a landing row or delete | the new rows | 143 → 86 (if all deleted) | — | — | ~−465 arm lines |
| 7 | collapse families into kinds (§4) | every row | 86 → 10 | ~10 | 71 → ~40 | `fnDispatch` disappears; one `dispatch` |

## 7. WHAT THE CUT CANNOT SEE

The reach of rows is DERIVED from driver text. The one experiment that would turn every ASSUMED above into READ is
an opcode trace over one standing run on hbox: one line per frame in `serveFrame` (`Host/Main.lean:2613`), one per
consent frame in `ClientConsentCore.serve` (`:507`), one per broker verb in `broker.rs`. Its union over the row set
*is* the KEEP list; the registry minus it is the DELETE list.
