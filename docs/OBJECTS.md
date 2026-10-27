# Objects and programs

A package is an immutable ROM cell identified by its canonical contents. Its [interface](../Lang/Package.lean) includes imports, state and interface types, a term, method and law labels, relations, documentation and contextual holes. Installation checks it and its pinned import closure. An object holds a package reference and state; a data object can instead have separate law packages.

Methods produce state, bounded row edits and typed call slots. Calls can exercise the kernel's callable bodies, including nested invocation and installation. The kernel checks the resulting tree as one transition: a refused leg does not leave earlier legs committed.

Laws see old state, proposed state and request. The occasion distinguishes birth, adoption, write, relaw and invocation with its payload. A law may refuse with its own bounded reason. Relations are bounded places under an object, not whole-table values; point and range reads are authenticated and pinned.

| Construction | Meaning | Executable evidence |
|---|---|---|
| Laws by act | Package and extra laws judge the occasion, including birth and law replacement. | [Lang journey](../Lang/Journey.lean), L8–L11 and erase-occasion plant. |
| Holes and justifications | ROM declares typed candidates and contexts. Each invocation resolves selections against authenticated rows/cells, support versions, blockers and guards; preparation is charged. | [LiveHoles](../Lang/LiveHoles.lean), [contextual receive](../Lang/Journey/ContextualReceive.lean), [hole checks](../Lang/Journey/HoleChecks.lean). |
| Activities | Generated methods capture a plan, keep pending/log rows and resume with a typed answer. Patience is in World heights; retirement handles overdue work. | [StdActivity](../Lang/StdActivity.lean), [activity surface](../Lang/Journey/Activity.lean), Bell cases in [Lang journey](../Lang/Journey.lean). |
| Offers | Each party posts terms and role. Fusion judges a named deal, consumes selected offers and records matching captures through nested calls. | [Offer journey](../Lang/Journey/Offer.lean), LF cases. |
| Offer escrow | Posting funds the offering object's value leg. Fusion pays both legs and consumes the offers atomically. | [OfferEscrow journey](../Lang/Journey/OfferEscrow.lean), LE cases. |
| Generators | A method emits package bytes through install. The receiver applies the same package check as member installation. Templates can depend on arguments or the invoker. | [Gen journey](../Lang/Journey/Gen.lean), GN cases; [StdGen](../Lang/StdGen.lean). |
| Claims | Term.guardedBy checks a restricted certifying law shape, with a soundness theorem. This checker is separate from package wire/install admission. | [Claim](../Lang/Claim.lean), [claim journey](../Lang/Journey/Claims.lean), LK cases. |
| Effects | Call-slot types constrain kinds and slot count; nested arguments are typed and encoded for the callee. This concrete boundary is not a general package-level grading system. | [Package.callTy](../Lang/Package.lean), [Call](../Lang/Call.lean), offer/generator journeys. |
| Foreign receipts | A receipt justifies an action relative to a trusted head object. It establishes admission at a height, not arbitrary outside content. | [Head journey](../Lang/Journey/Head.lean), HD/RC/TL cases; [Foreign.check](../Protocol/Foreign.lean). |

Cases are nested under lang-journey or rows, rather than separate [runs.tsv](../gates/runs.tsv) entries. The table names executable checks and controls.

[Contextual](../Lang/Contextual/Protocol.lean) retains a research model and instances. Deployed package preparation uses [Program](../Lang/Program.lean) and LiveHoles; a research-instance theorem is not automatically a runtime guarantee.
