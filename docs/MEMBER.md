# Being a member

nd uses ND_WORKSPACE for custody and attempts, and the follower and writer sockets. ND_FOLLOW_SOCK and ND_HOST_SOCK override socket paths. Personal custody uses a separate ND_HOLDING directory for the next secret. Local custody flags are parsed in [nd.rs](../client/src/bin/nd.rs); the shared language is parsed in [Verb](../Protocol/Command/Verb.lean).

These are command forms: uppercase words stand for the member's values. Digests and signed bytes use canonical hex; numbers are decimal. Lang reads package, state and argument text. Describe is spelled read OBJ ?.

| Action and syntax | What is checked |
|---|---|
| Join: nd --join KEY_FILE INVITATION STORE /ABS/HOST | The invitation verifies under the sponsor key obtained through a trusted channel. The joined origin comes from its inputs. Join creates the member's Store and retains the invitation; a sponsor enrolls the join token and supplies a World observe grant. |
| Write: nd write OBJ KEY VALUE [--via GRANT] | After catch-up, follow derives the call against its own World, including pins, authority, laws, bounds and charge. Only an admissible plan is offered for signature. |
| Read: nd read OBJ [KEY=VALUE...] | Follow re-derives history before reading its own state; each supplied expectation must hold. |
| Describe: nd read OBJ ? | Follow loads the package and prints its description, state type, methods, laws and relations. Method indices come from this description. |
| Invoke: nd invoke OBJ METHOD ARGS [--range REL K [PREFIX]] [--pin REL KEY]... [--via GRANT] | Arguments are read at the method's type. Follow plans against authenticated reads and checks the derived turn before requesting its signature. |
| Sync: nd sync | Each event is re-derived; reached steps and chain must match the page. Only read envelopes are signed. |
| Receipt: nd receipt CALL | Follow catches up and builds trie evidence and settlement against its own head. Output includes receipt, head and settlement. |
| Cancel: nd cancel CALL | Follow checks the member's own signed call can be cancelled, requests a cancel signature and sends it. A second catch-up must show the recorded cancellation before success. |

Writes and invokes first sign envelopes for bounded log pages. The eventual call signs its World, member, window, pins and body. A resumed plan is re-derived; changed signed bytes are planMoved. The sponsor key during adoption remains a trust premise described in [TRUST](TRUST.md).

The form nd read OBJ REL K [PREFIX] reads a bounded relation range. The form nd sync --to STEPS:CHAIN compares a position while catching up; --attest signs follow's head, --check ATTEST checks another member's attestation, and --post OBJ posts follow's own head. A follower already beyond the requested comparison answers ahead.

The language also has init, enroll, install, create, law, grant, revoke, rotate, adopt, issue, account, transfer, credit and invite. [Verb.usage](../Protocol/Command/Verb.lean) gives their forms. The --init, --init-hosted, --init-observer, --seal-observer and --keys flags are local custody operations. The --input HEX helper retains founder input; bare invite and adopt KEY_FILE use retained input/invitation files.

A refusal names the failed condition. Stale means a signed pin no longer matches; lawDenied carries the law's reason; noGrant and grantRight concern authority. Parsing and pre-signing refusals create no signed call. An already-sent call needs settlement: uncertain, declined, open and hostContradicted do not mean absent forever. Behind preserves catch-up progress; pageIo identifies a writer page-read failure.

An unsettled attempt stores exact argv, continuation and signed call. Repeating its argv resumes it. The writer reply is a hint; only the follower's receipt settles it. Repeating an already-settled command can create a new call: argv is not a durable caller-intent identifier. Transfer's --once HEX is a separate once-key mechanism.

The [protocol rows](../Protocol/Rows.lean) exercise join, use, describe, receipt, settlement, cancellation and fork comparison through the command machine.
