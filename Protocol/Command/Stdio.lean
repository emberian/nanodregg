/-
# Protocol.Command.Stdio — the command surface a hosted resident reaches through `nd --stdio` (PROTOCOL-40)

`nd --stdio` (HOSTING-20) serves a resident over its own socket. One request is one `nd` command
(`commandLayout`, the member's argv), and one reply is the command's end (`commandReplyLayout`, the
`done` step's fields: a `CommandExit` code, stdout and stderr). The resident runs only the verbs of
`stdioVerbs`. nd checks the request's first word against them before follow sees it, so a flag, an
empty argv and an excluded verb are all refused `notOnSurface` by one name. Excluded:
- `init`: it mints a join token signed twice, and a resident's keys are the operator's;
- `rotate`: rotation is the operator's, and custody in stdio mode refuses `precommit`,
  `signNext` and `signIncoming` as `noRotation`, a second fence;
- `adopt`: it replaces follow's World with a downloaded base.
- `invite`: an invitation is a person's word for the World (PROTOCOL-42); a resident vouches for no one.
Theorems: `Protocol.Proofs.Stdio`.
-/
import Protocol.Command.Verb
import Protocol.Table

namespace Nanodregg.Protocol.Command

/-- Whether a resident may run a verb through `nd --stdio`. A total match with no wildcard: a new
verb does not compile until its author decides its arm, so the surface never widens by default. -/
def Verb.onStdio : Verb → Bool
  | .init | .rotate | .adopt | .invite => false
  | .enroll | .install | .create | .write | .law | .invoke | .grant | .revoke | .read | .sync
  | .issue | .account | .transfer | .credit | .receipt | .cancel => true

/-- The verbs a resident may run through `nd --stdio`. -/
def stdioVerbs : List Verb := Verb.all.filter Verb.onStdio

/-- Their words, as nd compares a request's first argument. -/
def stdioWords : List String := stdioVerbs.map Verb.word

end Nanodregg.Protocol.Command

namespace Nanodregg.Protocol

/-- Why `nd --stdio` refuses a request before follow sees it, by name (law 7). Each is answered as
a reply with `CommandExit.refused` and `refused NAME` on stderr. -/
inductive StdioRefusal
  /-- the request's first word is not one of `Command.stdioWords` (an excluded verb, a flag, an
  empty argv) -/
  | notOnSurface
  /-- the request is not a `commandLayout` payload -/
  | undecodable
  deriving DecidableEq, Repr

namespace StdioRefusal

def all : List StdioRefusal := [notOnSurface, undecodable]

def code : StdioRefusal → UInt8
  | notOnSurface => 0 | undecodable => 1

def name : StdioRefusal → String
  | notOnSurface => "notOnSurface" | undecodable => "undecodable"

end StdioRefusal

/-- `nd --stdio`'s reply payload: the command's end, exactly the `done` step's fields (one source). -/
def commandReplyLayout : Codec.Layout := Step.layout .done

end Nanodregg.Protocol
