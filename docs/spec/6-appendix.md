# 6 Appendix

## 6.1 Soundness statements

This section lists the theorems the tree proves about the language, grouped by what they establish.
Each is cited by file and name.
`Census/Axioms.lean`, run in the convergence report, lists every declaration's axioms; theorems that rely on the compiler through `native_decide` have a row in [`gates/axioms-allow.tsv`](../../gates/axioms-allow.tsv).

### Typing

| statement | theorem |
|---|---|
| The checker returns `τ` exactly when the typing relation derives `τ`. | `Lang/Proofs/Check.lean` `inferE_iff_live`, `check_iff_live` |
| A term has at most one type. | `Lang/Proofs/Check.lean` `hasType_unique_live` |
| Every derived type is well formed, given well-formed contexts. | `Lang/Proofs/Canon.lean` `hasType_wf`, `infer_wf` |
| A filling typed at its hole's context preserves the type of the term it fills. | `Lang/Proofs/Fill.lean` `fillHoles_typed` |

### Running

| statement | theorem |
|---|---|
| A checked program never ends `stuck`; a value it ends with has its type. | `Lang/Proofs/Sound.lean` `checked_never_stuck`, `run_sound` |
| Two final runs of one state, at any budgets, have the same outcome. | `Lang/Proofs/Run.lean` `run_agree` |
| The machine's values and non-resource faults are the reference semantics' meanings. | `Lang/Proofs/Agree.lean` `run_bigStep`, `run_fault_bigStep` |
| Every meaning is reached by the machine at a large enough budget and stack bound. | `Lang/Proofs/Complete.lean` `bigStep_run`, `bigStep_run_fault` |
| A term has at most one meaning. | `Lang/Proofs/BigStep.lean` `bigStep_deterministic` |
| `extend` of a fixed point keeps the old self. | `Lang/Proofs/BigStep.lean` `bigStep_extend_keeps_old_self` |
| A run walks at most 32 primitive operand bytes per tick. | `Lang/Proofs/Cost.lean` `walked_le` |
| A law of a loaded package never ends `stuck`. | `Lang/Proofs/Invoke.lean` `law_never_stuck`; `Lang/Proofs/LawRun.lean` `runLaw_never_stuck` |

### Encoding

| statement | theorem |
|---|---|
| The tree codec is canonical. | `Codec/Proofs/Tree.lean` `tree_lawful` |
| A package has exactly one byte string. | `Lang/Proofs/Wire.lean` `decodePackage_eq_ok_iff`, `packageCodec_lawfulOn` |
| Bytes at another version are refused. | `Lang/Proofs/Wire.lean` `decodePackage_wrong_version`, `unversioned_package_refused` |
| Data at a type has exactly one byte string. | `Lang/Proofs/Data.lean` `decodeData_eq_ok_iff`, `dataStream_lawful` |

### Installing and running packages

| statement | theorem |
|---|---|
| A package install admits also loads, by the same admission. | `Lang/Proofs/LiveHoles.lean` `install_loads` |
| Every call a method returns is of a kind an object may make. | `Lang/Proofs/Call.lean` `callsOf_callable` |
| A run's calls move at most the method's grade. | `Lang/Proofs/Effect.lean` `runMeasured_moves_le` |
| A run that writes held rows moves their value in and out. | `Lang/Proofs/Holds.lean` `checkLegs_backed` |
| A template generator's run installs exactly the bytes of the Lean generator's package at the receipt's argument. | `Lang/Proofs/StdGen.lean` `generate_template_sound`, `generate_bounded_sound`, `make_bounded_sound` |

### Holes

| statement | theorem |
|---|---|
| A selection is the candidate the pinned row names, with every support holding. | `Lang/Proofs/LiveHoles.lean` `selectHole_origin` |
| A selected candidate's cell supports are live; its contract supports hold of the cell. | `selectHole_cell_support`, `selectHole_contract_support` |
| A position is strengthened away exactly when its hypothesis fails, and then it is unused. | `selectHole_hypotheses` |
| The factored filling is typed and re-embeds to the committed candidate. | `selectHole_factor` |
| A candidate whose supports and used hypotheses hold, and whose guard passes, is selected. | `selectHole_live_selects` |
| A candidate citing a dead cell is not selected. | `revoked_support_refused` |
| A blocked hole faults with its refusal's name on its first transition. | `blocked_step` |
| A prepared body is closed, typed at the interface, in bounds, and its digests come from committed text. | `instantiateHoles_typed`, `instantiateHoles_sources` |

### Claims

| statement | theorem |
|---|---|
| A guarded `ok` happened under the invariant's test or in the `relaw` arm. | `Lang/Proofs/Claim.lean` `guardedBy_sound` |
| A law in certifying shape that admits a non-`relaw` step leaves a state keeping the invariant; so does every step of a chain. | `keeps_step`, `chain_keeps` |
| A package the install check admits bears every claim it carries. | `install_claims` |
| Every state of an object under such a law keeps the invariant, once the first does. | `Kernel/Proofs/Logic/Claims.lean` `object_history_keeps` |

### The World the language runs in

| statement | theorem |
|---|---|
| Two members with the same pins derive the same Turn. | `Kernel/Proofs/Receive.lean` `receive_congr` |
| A read-only cell never changes along a fold. | `Kernel/Proofs/Frame.lean` `fold_rom` |
| A stale pin stays stale on every extension. | `Kernel/Proofs/Versions.lean` `stale_behind_forever` |
| An object's package never changes, and every history of an object under a `NoRef` law is a chain that law's meaning admits. | `Spec/Proofs/Deployed.lean` `top_integrity_law` (claim `Integrity.law`) |

The other top claims are listed in the [README](../../README.md#what-the-world-guarantees) and in [`Spec/README.md`](../../Spec/README.md).

### Not proved

* That the Lean compiler, the C runtime and the operating system preserve these statements.
* That every contextual run along a history used a justified candidate, and every hole refusal names a failed justification: in flight (§1.6).
* That a refusal's coordinates are every failed assumption of the invocation: they are the failures of the first failing step (§4.10.2).
* That an alternative candidate is selected after a support dies: repair is a new selection someone makes (§4.10.5).

## 6.2 Implementation limits

### The language

| bound | value | Lean |
|---|---|---|
| natural literal and value | `< 2^64` | `Lang/Bounds.lean` `natLimit` |
| byte string | ≤ 65536 bytes | `Bounds.bytesMax` |
| digest | ≤ 32 bytes | `Bounds.digestBytesMax` |
| bytes walked per tick | 32 | `Bounds.wordBytes` |
| machine stack | 4096 frames | `Bounds.stackMax` |
| refusal reason | ≤ 256 bytes, printable UTF-8 | `Bounds.reasonMax`, `Bounds.reasonOk` |
| package doc | ≤ 256 bytes, printable UTF-8, no `"` | `Bounds.docMax`, `Bounds.docOk` |
| candidates per hole | ≤ 64 | `Bounds.holeCandidatesMax` |
| holes per package | ≤ 16 | `Bounds.holeSignatureMax` |
| guard budget per hole | 256 ticks | `Bounds.holeGuardFuel` |
| law and guard budget | 100000 ticks each | `Lang/Law.lean` `lawTicks` |
| imports per package | ≤ 16 | `Lang/Package.lean` `importsMax` |
| methods per package | ≤ 64 | `methodsMax` |
| laws per package | ≤ 16 | `lawsMax` |
| claims per package | ≤ 16 | `claimsMax` |
| relations per package | ≤ 8 | `relsMax` |
| key fields per relation | 1 to 8 | `keyFieldsMax` |
| point reads per relation | ≤ 8 | `pointsMax` |
| rows per range read | ≤ 8 | `rangeRowsMax` |
| edit slots per method | ≤ 8 | `editsMax` |
| rights per granted call | ≤ 4 | `rightsMax` |
| closure depth | ≤ 8 | `Lang/Program.lean` `closureDepthMax` |

### The wire and the text

| bound | value | Lean |
|---|---|---|
| package wire version | 10 | `Bounds.packageWireVersion` |
| tree depth | ≤ 1024 | `Lang/Wire.lean` `depthMax` |
| payload and children per node | ≤ 65536 | `Wire.nodeMax` |
| entries per row, terms per substitution | ≤ 256 | `Wire.rowMax` |
| label | 1 to 64 bytes | `Wire.labelBytesMax` |
| text nesting | ≤ 1026 | `Lang/Read.lean` `depthMax` |
| elements per text list | ≤ 258 | `Read.listMax` |

### The kernel, as the language meets it

| bound | value | Lean |
|---|---|---|
| calls per run | ≤ 8 | `Kernel/Bounds.lean` `callsMax` |
| call nesting below the signed call | ≤ 4 | `callDepthMax` |
| ticks per call tree | ≤ 131072 | `treeTicksMax` |
| ticks per member per window | ≤ 2097152 | `ticksPerWindow` |
| slot value | ≤ 65536 bytes | `valueBytesMax` |
| key bytes | ≤ 128 | `keyBytesMax` |
| rows per relation | ≤ 4096 | `rowsPerRelationMax` |
| row pins per call | ≤ 32 | `rowsMax` |
| range reads per call | ≤ 4 | `rangesMax` |

## 6.3 Index of rules

| rule | chapter | Lean |
|---|---|---|
| T-Var, T-Lam, T-App, T-Fix | §3.3 | `HasType.var`, `.lam`, `.app`, `.fix` |
| T-Nat, T-Bool, T-Bytes, T-Digest, T-Prim | §3.3 | `HasType.nat`, `.bool`, `.bytes`, `.digest`, `.prim` |
| T-Record, T-Get, T-Extend, F-Nil, F-Cons | §3.3 | `HasType.record`, `.get`, `.extend`; `FieldsTy` |
| T-Inj, T-Case, A-One, A-Cons | §3.3 | `HasType.inj`, `.case`; `ArmsTy` |
| T-Ite, T-Refuse, T-Ref, T-Hole, S-Nil, S-Cons | §3.3 | `HasType.ite`, `.refuse`, `.ref`, `.hole`; `SubstTy` |
| H-Rom | §3.6 | `HoleROM.check` |
| P-Shape, P-Closed, P-Contextual | §3.7 | `Package.checkShape`, `Package.checkWith`, `Package.checkContextual` |
| G-Ite, G-Case, G-Inj, G-Refuse | §3.9 | `Term.guardedBy`, `Term.guardedArms` |
| E-Var … E-Hole | §4.2.1 | `step`, case `eval` |
| R-Halt … R-IteF | §4.2.2 | `step`, case `ret` |
| Sup-Row, Sup-Cell, Sup-Law, Sup-Package | §4.10.1 | `supportLive` |
| Res-Sel, Res-Block | §4.10.3 | `resolveHole` |

## 6.4 Index of refusals

### Decoding

`truncated`, `trailing`, `pastBound`, `badTag`, `wrongFrame`, `rejected`, `tooDeep` (`Codec/Refusal.lean`); the package's refinement names `lang/package-version/10` and `lang/package/10` (§5.7); `varint/overlong`, `bool`, `lang/data: no value`, `lang/data: type`.

### Reading text

`tooDeep`, `tooLong`, `unexpectedEnd`, `stray`, `unterminatedString`, `unclosed`, `trailing`, `notAType`, `badEntry`, `unbound`, `badRef`, `badDigest`, `badRefuse`, `emptyApplication`, `badBinder`, `reservedBinder`, `badImport`, `badLabel`, `notPackage`, `badDoc`, `notOfType` (`Lang/Read.lean` `ReadRefusal`).

### Typing

`unbound`, `noPackage`, `noHole`, `holeSubstitution`, `badType`, `notFunction`, `argument`, `notSelfMap`, `natRange`, `bytesRange`, `digestRange`, `badReason`, `operands`, `notCanonical`, `notRecord`, `noField`, `notSum`, `noArm`, `payload`, `arms`, `armType`, `condition`, `branches`, `declared` (§3.4).

### Install

`tooManyImports`, `tooManyMethods`, `tooManyLaws`, `tooManyClaims`, `stateNotData`, `ifaceNotRecord`, `illTyped`, `contextualSignature`, `importType`, `tooManyRels`, `relKey`, `badRel`, `noMethod`, `badMethod`, `liveNotCellKeyed`, `peerNotNamed`, `receiptRead`, `badEffect`, `effectExceeded`, `noLaw`, `badLaw`, `claimNotLaw`, `claimNotInvariant`, `claimShape`, `claimUnproved` (`Lang/Package.lean` `CheckError`); `notDigest`.

### Holes

| wire name | raised by |
|---|---|
| `holeType`, `holeContext`, `holeCandidates`, `holeGuardType`, `holeCandidateType` | §3.6 |
| `holeSignatureBound`, `holeDuplicate`, `holeBodyType` | §3.7.4 |
| `holeUnpinnedRow` | §4.10.2 steps 1, 7 and 8 |
| `holeSelectionAbsent`, `holeSelectionType`, `holeSelectionIndex` | §4.10.2 steps 1 to 3 |
| `holeUnpinned` | §4.10.2 steps 4, 7 and 8 |
| `holeDerivationMoved`, `holeSupportDead` | §4.10.2 steps 5 and 6 |
| `holeSupportMoved` | §4.10.2 step 7 |
| `holeGuardBlocked`, `holeGuardFault` | §4.10.2 step 8 |
| `holeWorkBound`, `holeSizeBound`, `holeProvenance`, `holeInstanceType` | §4.10.3, §3.7.4 |
| `holeUnresolved` | §4.2.1 E-Hole, §4.5.2 |

Lean: `Lang/LiveHoles.lean` `HoleRefusal`, `HoleRefusal.wire`.

### Running

The faults of §4.4.2 and the texts of §4.11.

### The kernel

The kernel's refusals, `program` and `lawDenied` among them, are listed in [`kernel.md`](../reference/kernel.md).
