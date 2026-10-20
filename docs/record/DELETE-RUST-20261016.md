> record copy of redregg/work/DELETE-RUST-20261016.md, 2026-10-16; the lane logs stay in redregg

# DELETE-RUST — minidregg's native/ layer: reach, decisions, twins, keep set (DISCOVER-RUST, 2026-10-16)

Short by ROOT's order (the scholar became BUILD-CLIENT in `~/dev/nanodregg`). Tree: minidregg main
**2c27b08b**, read-only, nothing built. Tags: READ (seen at file:line), DERIVED (computed by script over
the tree), ASSUMED. Four read-only sub-scholars did the sweeps; their numbers are DERIVED unless marked.
Static analysis only: a "dead" verdict means no required row, deployed unit or grain-runtime call site
was found by grep/call-graph; it is conservative (the call graph over-approximates by method name).

**The spec used.** Required rows (`scripts/pipeline/required-rows`) → drivers (`scripts/pipeline/journey-rows`)
→ a 66-file driver closure (`scratchpad/driver-closure.txt`). ⚑ The `journey` row runs only steps
J0–J8, JROT, JROTL, JRLANE, JGATE, JAUDIT of journey.sh (`journey-rows:22-27`); rooms J0–J5+JPRIV1; m7
J0+M7. So KH (hiding), JMKT (market), JCHAT, K12*, J14/J15/J17, JNOCK*, JJOB* are in **no required row**.
Plus deployed units (`deploy/**`: `mini serve`, `checkpoint certify`, `clock tick`, `socket-proxy`,
`shell`, `pay watch-config|observe`, `hermes-handoff dispatch`, grain-runtime serve, spk broker).

## 1. Numbers NOW (seed for a size ratchet)

| metric | value |
|---|---|
| Rust lines in native/ | 281 k (resource-client 113,757 · grain-runtime 55,896 · spk-host 54,498 · private-backend 26,139 · mini-sdk 5,782 · rest < 5 k each) + prover/ 7.9 k |
| `#[cfg(test)]` inline lines | 64,778 in 332 modules (+5,496 in 10 cfg(test) files, +6,559 in tests/) — 25 % of resource-client src |
| `mini` verbs reached by rows/units | 57 of 130 dispatch arms (T2) · workspace actions 16 of 68 · shell commands 18 of 55 |
| resource-client production lines unreached | 26,217 (T1: rows+units) · 23,887 (T2: +grain-runtime calls) · 15,304 (T3: +every shell command a friend can type) |
| decisions Rust makes that Lean does not | 25 in client/sdk/keys/pay (§3) + 8 in small crates + spk-host/grain-runtime (§3c) |
| decimal/nat parsers | 78 named fns; 32 do their own digit work (spk-host 25, grain-runtime 4, …); 186 raw digit-token sites in ~115 files; 3 hand big-number types; StreamCodec.nat (base-255) copied 5× |
| socket-envelope builders | 5 production (`transport.rs:935`, `:1117`, `spk-host dispatch_native.rs:531`, `mini-keys server/native.rs:54`, `mini-sdk operator.rs:364`) + 5 test |
| MDCOPRC1 coprocess loops | 2 (verifier `main.rs:172`, sqlite-store `main.rs:326`) |
| outcome-frame decoders in Rust | 8 spk-host files hard-code `DREGG/NATIVE-HOST/OUTCOME/v5` |
| Lean/Rust dual labels | 82 in 58 Rust files; 384 labels exist ONLY in Rust (resource-client 251, private-backend 95) |
| hand-copied frame bound `12_102_760` | 22 files (spk-host 13); `host-operations.rs` has ONE consumer (`member_app.rs:8`, itself dead) |
| `#[allow(dead_code)]` / `#![allow(dead_code)]` / `_unchecked` | 15 / 36 (35 spk-host files) / 3 |
| crates with no builder and no runtime caller | private-backend, prover/, joint-agreement-crypto, bend-ir2-proof (+entropy: path dep missing), hyperdocument-link-store, portable-archive ≈ 37 k lines |

## 2. KEEP set (what the end system needs from Rust) and DELETE list

**KEEP — transport, custody, workspace, sandbox plumbing.** In nanodregg these are rebuilt, not ported
(charter law 11): client frames + sockets (~570 lines of `transport.rs` client side are the reference),
consent-socket client (~210 of `client_consent.rs`), seed custody and signer, the socket supervisor
(today inside `mini serve`, `transport.rs:1184-1995`, ~1,200 operator lines in the client binary), the
store helper's 8 `durable-*` verbs (sqlite-store; nanodregg's HOST-4 replaces it with a flat log in C),
the signature verifier's `verify`/`verify-sshsig` (231 lines), the SPK sandbox floor (`sandbox.rs:41-50`
FIXED_ARGS), the user-mode broker's physical verbs, the volume helper, pay-watcher's RPC I/O.

**DELETE (by lines, with evidence):**

| # | target | lines | evidence |
|---|---|---|---|
| 1 | private-backend + `pinned_execution.rs` | ~26.8 k | no invoker; Lean side only via `ResearchWip.lean:86-87`; 4 test rows |
| 2 | resource-client unreached production code | 26.2 k (T1) | 29 fully dead files (13,990) + 9 near-dead (12,670): traffic/mix cluster 6.1 k (`cohort_tcp`, `pq_mailbox`, `scheduled_transport`, `async_dispatch`, `crypto_transit`), member/app 2.9 k, relay/channel 2.4 k, drain/consumer 2.4 k, enrollment_bootstrap 1.6 k, key_adoption 1.4 k, session_reenroll 1.2 k, job 1.1 k, fn_namespace 0.7 k, market 0.6 k … |
| 3 | `#[cfg(test)]` twins and inline tests | 64.8 k | tests in Rust of Lean-owned shapes are confessions (sdk golden/lean-codec rows, codec round-trips) |
| 4 | prover/ | 7.9 k + 25 k testdata | nothing compiles it |
| 5 | spk-host/grain-runtime versioned lifecycle and agent families | see §3c | v3/v4 twins of Lean V2/V3/V4 receivers (H1/H2) |
| 6 | operator code inside `mini` | ~2.9 k | `serve`/public_proxy/proxy/operator_drain/serve_queue are a supervisor, not a client |
| 7 | mini-sdk twins | ~2 k | contracts/consent/explain/wasm/flow/confirm/profile: no consumer outside the crate; mini-sdk-ts unbuilt |
| 8 | small dead crates | ~2.6 k | bend-* (874), hyperdocument-link-store (713), joint-agreement-crypto (709), portable-archive (338) |
| 9 | Discord mirror + broker discord ops | ~0.8 k | not in ROLES |

## 3. Every Rust decision → where it goes

Each decision belongs in Lean (owner named) or dies with its feature (no required row).

**(a) resource-client / mini-sdk / pay / keys** (sub-scholar census, READ unless marked)

| id | Rust | decides | Lean owner | row → verdict |
|---|---|---|---|---|
| D1 | `hiding.rs:445-535` (`main.rs:2235`) | recompute salted leaves/root of a view, refuse on mismatch | `Compiler/StoreCodec.lean:665,722` | `--view resource` (JPAY6) → Lean op (codec-child op 12 was planned) |
| D2 | `hiding.rs:248-262` (`workspace.rs:4646`) | KMAC blinding key + cell blinding at every birth | `StoreCodec.lean:644,665` | journey births → Lean |
| D3 | `hiding.rs:274-306` | blinding ratchet, owner salts | `StoreCodec.lean:883-892` | KH only → dies |
| D4 | `market.rs:45,271,476` | HashEq commitment; uniform-price CLEARING ALLOCATION | `Pred/HashEqDigest.lean:221`; `Kernel/SealedMarket.lean:115` bounds but computes no clearing | JMKT only → dies (if revived: clearing must be Lean) |
| D5 | `mini-keys server/member.rs:34-96` | Ed25519 auth over Rust-only domain `mini/member-provider-action/v1\0`; provider/grant choice | none | JPAY6 → KEY-CUSTODY (open, nanodregg DECISIONS) |
| D6 | `client_consent.rs:278-288`; `:70` | thin-consent stream encoder (StreamCodec.nat twin); replan verdict from refusal TEXT prefix `"stale observation:"` | `Tower256ConcreteBackend.lean:227`; `Kernel/NativeThinConsent.lean:263` | THIN not required → dies; `:70` is a parse-as-verdict on every row |
| D7 | `workspace.rs:108-121,3290-3320` | delegation pre-check (verbs ⊆ parent, observe, maxCost ≤ parent) | the Host's delegation receiver (attenuation rule not located: ASSUMED) | J3 → Lean only |
| D8 | `pay_memo_v2.rs:87-660` | memo-v2 codec, Uint256, quote validation, SSHSIG | `Kernel/PayEnrolMemoV2.lean:205,237` | none → dies |
| D9 | `join_solana.rs:11-230` | memo-v1 codec, possession frame, SSHSIG parse | `Kernel/PayEnrolMemo.lean:220,371` | none → dies |
| D10 | `key_rotation.rs:156-160` | next-possession frame (Host re-derives: admitted twin) | `Kernel/ParticipantKeyEnrollment.lean:67` | JROT → Lean |
| D11 | `replan.rs:37-101` | retry budget 5 and which refusals are retryable | `Kernel/NativeClientConsent.lean:101` (never called) | send/fleetsign/JGATE → Lean |
| D12-13 | `receipt_continuity/carry*.rs` | verifier selection; carried-lookup binding | `Host/CarryInspection.lean`, `RetainedSegmentInspection.lean` | welcomecontinuity → Lean |
| D14 | `private.rs`, `roomkey.rs` | room-key protocol, 39 Rust-only domains | partial: `Kernel/PrivateRoomKeys.lean`, `Compiler/RoomKeyReleaseCodec.lean` | rooms (JPRIV1) → Lean |
| D15 | `pq_mailbox.rs:434`, `cohort_tcp.rs:545-756` | manifests, roster admission | none | none → dies |
| D16 | `story.rs:146,357` | Rust GENERATES A LAW from a table | none | J15 → dies |
| D18 | `job.rs:579,771` | precondition refusals mirroring the job law | `Kernel/Job.lean:554` | JJOB → dies |
| D20 | `can.rs` | representative command per verb | — | J12A → dies |
| D21 | `shared_names.rs:440-474` | name → target binding | not located | shell → Lean |
| D22 | `mini-sdk/contracts.rs:12-175` | intent codec, canonical_json (differential test = confession) | `Kernel/Contracts/Intents.lean:212-223,484,488` | Rust tests only → dies |
| D23 | `pay-watcher/watch.rs:162-200`, `model.rs:62` | N-endpoint agreement (minEndpoints 2), finality, skips, memo classification | `Kernel/PayChainTip.lean:4-6` delegates finality to the observer | JPAY1/4 → the agreement rule to Lean; RPC I/O stays |
| D24 | `inference-scheduler core.rs:376-460` | job ordering, backend eligibility | none | hermes → physical capacity (ASSUMED keep) |
| D25 | private-backend (VABA, ACS, DZK, SH2T) | an MPC/consensus stack | research codecs only | none → dies |
| S1 | sqlite-store `anchor.rs:1-60`, `lib.rs:822-856` | MINIANC2: refuse a Store behind/conflicting; SHA-256 domains | Lean trusts it (`Compiler/DurableHistory.lean:18,323`) | every row → a refusal decision guarding a trust floor: Lean (nanodregg HOST-4a: chained MAC) |
| S2 | verifier `main.rs:45-48` | comment claims Lean's `CredentialSignatureIO.combineHalves` decides hybrid conjunction | ⚑ **that function does not exist**; `verify-mldsa` has no caller | ⚑ the ML-DSA half of hybrid signatures is verified nowhere on the Lean path |
| S3 | discord-entrance `signature.rs`, `roster.rs` | Discord signature + timestamp window, user→session roster | none | none → dies with the entrance (product call) |

**(c) spk-host / grain-runtime** — see §3c.

## 4. The one-process-two-sockets client: what survives

Built in nanodregg as `client/` (BUILD-CLIENT, commits e948710, 37baeae; DECISIONS CLIENT-1..8):
frames with bounds, seed custody (O_NOFOLLOW, 0600, euid, zeroized), frozen attempts (uncertain →
lookup only, absent → same bytes ≤ sendsMax), the socket mux for `host serve`/`host follow`. 686 lines
against minidregg's 113,757. What dies relative to HP-4's list: `local_process` (`main.rs:1245`),
`store_run` (`:1205`), the codec child (~72 lines), consent spawns + `consent-resident` self-spawn
(`client_consent.rs:134-153,406`), the host-image hash path (~160 lines; 97 call sites use it as a
generic file digest), every Host-CLI spawn in reached code (14 sites: `pay.rs:1951,2144,2179`,
`join_solana*.rs`, `well.rs:191`, …), the ssh relay/`socket-proxy` (OpenSSH StreamLocal forwarding,
CLIENT-4), and the whole command language (argv goes to `host follow`, which drives `nd` by steps;
CLIENT-2 / HOST-9).

## 5. Order of cuts (minidregg, if it is cut rather than replaced)

1. Crates with no builder (private-backend, prover, bend-*, link-store, joint-agreement, portable-archive):
   −37 k, no row moves. 2. resource-client T1-dead files: −14 k fully dead, no row moves (rows: all
   required pass unchanged by construction). 3. inline `#[cfg(test)]` twins of Lean codecs: −10–20 k,
   rows unchanged, Rust test rows deleted. 4. spk-host v3/v4 lifecycle twins after OB "retry is a new
   birth" (rows m6grain, hermes, JPAY6). 5. Move D1/D2/D6/D7/D10/D11/D14 into Lean ops (rows journey,
   rooms, JROT, JGATE, send, fleetsign), then delete their Rust. Nanodregg is the replacement path; ROOT
   chose it, so this order is informational.

## 3c. spk-host / grain-runtime (sub-scholar, DERIVED unless marked)

**Headline.** The agent→SPK application API is ~16.3 k lines that no row or unit ever gives work:
`grain.rs:1116` writes the resident config with a hard-coded `"agents":[]`, and no spec controller
config sets `dispatchTask` / `allowedApplicationApiRoutes` (`hermes-journey.sh:194-206`,
`jpay6.sh:565-583`). Statically linked, behaviourally dead.

**Verbs the spec runs.** m6grain: `spk-host grain {unit-name, init-store, install, route, start,
prepare-resident, stop, status}`, `resident-validate`, unit `resident-bootstrap`, `mini-spk-broker serve`,
volume helper {create, mount, unmount, freeze, volumes-status}. hermes/JPAY6: `grain-runtime serve`,
`connect`, `mcp-stdio`; launch-gate. m7/hostupgrade touch nothing here. Never run by spec: ~25 spk-host
verbs (qualify*, inspect-installed, checkpoint-*, human-custodian-init, export, backup, …), ~15
grain-runtime verbs (config-migrate, concierge, hermes-room, provider-provision, quiescence*, …), and
the binaries `mini-inference-scheduler`, `spk-hostd`, `spk-browser-proxy`.

| crate | reached | dead-by-spec | test | not shipped |
|---|---|---|---|---|
| spk-host 54,498 | ~38.8 k (27–28 k non-test) | ~11.5 k + 0.9 k shipped-unrun | 13,071 | 2,377 (5 bins) |
| grain-runtime 55,580 | ~41.3 k (~31 k non-test) | ~12.6 k | 11,799 + 2,206 | — |

35 spk-host files carry a file-wide `#![allow(dead_code)]` (24,629 lines) with stale "not linked yet"
comments (`resident_service.rs:5`, `lifecycle_v3_native.rs:4`); grain-runtime is one 13,832-line
`impl Runtime` (`main.rs:3345`). Features `fixture-os`/`integration-qualification` are never passed by
`build.sh:188` / `lane-build.sh:78`.

**Decisions Rust makes here.**

| Rust | decides | Lean owner / verdict |
|---|---|---|
| `lifecycle_v4_retry_native.rs:275-315` | v3 vs v4 START lane from local files before any Mini call | `Kernel/ApplicationFailedCreateRetryEvidence.lean:59,150-157` → dies (OB: retry = new birth) |
| same :80-256 | hand StreamCodec nat/bytes; `recovery_index = acceptedCount−1`; selector frame | `Tower256ConcreteBackend.lean:227,520`; `…RetryEvidence.lean:38` → dies |
| `hostd.rs:574-605` | STOP post-audit digest under Rust-only tag `DREGG/SPK-STOP-POST-AUDIT/v1` + serde_json + SHA-256 | Lean receives it opaque (`Kernel/ApplicationLifecycleCompletionReport.lean:56`) → Lean must author it |
| `descriptor_native.rs:177`, `resident_launch.rs:176`, `claim_descriptor.rs:45` | recompute `DREGG/SPK-IMAGE/v1` and refuse on mismatch (3 copies) | `Kernel/ApplicationSpkPackageIdentity.lean:96` → Lean |
| `lifecycle_v3_claim_native.rs:51` `later_decimal` | orders acceptedCount values | Lean receivers (ASSUMED) |
| `grain.rs:47-60` | signing-slot orders copied from Lean | Lean plan inspection (ASSUMED owner) |
| grain-runtime `main.rs:1629,1702-1728,1777` | provider charge ceiling, hold amount, charge ≤ reserve | twins of `Kernel/ProviderMetering.lean:156,189`, `Host/ProviderUsage.lean:294` → Lean |
| `main.rs:354-384`; `credentials.rs:358,392` | tariff selection; payer row; per-call/per-day limits | no Lean owner → KEY-CUSTODY (nanodregg, open) |
| `provider_choice.rs:22-35` | Rust-only signed `mini/provider-choice/v1` | none; unused verb → dies |
| `volume_custody.rs:132-175` | witness parse; quota range 64 MiB–16 GiB | physical KEEP; the range is policy → Lean |

**Duplicates here.** 46 decimal helpers in 35 files (20 `fn decimal`, 7 `canonical_decimal`), 41 hex
helpers, 52 `fn invalid`; the `u32LE(plan.len) ‖ plan ‖ sigs` pair built 10×; ~11 Host reply-frame
decoders; `NATIVE-HOST/OUTCOME/v5` defined in 11 files; 83 opcode literals for 25 ops in 17 files
while `native/host-operations.rs` is imported by none of them.

**Top deletions.** (1) the agent→SPK application API, ~16.3 k (spk-host `agent_api_*` 7,557 +
grain-runtime application_api_tools/dispatch_custody/gitweb_worker 4,138 + ~4,638 `impl Runtime`
methods, with V2/V3 twins). (2) failed-create retry v4 + grain_export, ~3.1 k. (3) binaries no row or
unit runs, ~3.6 k. (4) grain-runtime unused-verb clusters (concierge, hermes_room, room_resident,
provider_provision, resident_outcomes, legacy_custody_audit), ~3.4 k. (5) config_migration 2,033
(reached at `serve` startup: a migration in a greenfield repo; delete by design). Gate for any cut:
m6grain, hermes, JPAY6 unchanged, and `cargo check` clean after removing the 35 file-wide allows.

**In nanodregg** (CLIENT-7, ruled): none of this is ported. The sandbox is `sandbox/` (one shape,
4f71cae); a hosted resident is a member running `nd`; provider keys are KEY-CUSTODY, open for Ember.
