/-
# Protocol.Command.Verb — the verbs of the one command language, and its one parser

`nd VERB ARG…` is parsed here and nowhere else: not in Rust (law 2), not in the rows (a row's argv
goes through this same `parse`). Every verb is a constructor of `Verb` (the SIZE ratchet counts
them, ceiling 20), and every way an argv can be wrong is a constructor of `ParseRefusal`.

Arguments: a digest (a cell, a member, a grant, a package) is lowercase hex of its canonical
bytes; a number is decimal; a value is taken as its UTF-8 bytes; a package is its TEXT form, read
by LANG's one reader (`Lang.Read.readPackage`) and installed as its canonical bytes; a join token
(what `init` prints) is lowercase hex. A member names objects by id: petnames are not part of the
language (a member's own index of names is a later row, not a guess now).
-/
import Kernel.Receive.Call
import Protocol.Table
import Protocol.Command.Text
import Lang.Read
import Protocol.Thin
import Protocol.Invite

namespace Nanodregg.Protocol.Command

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- Every verb. -/
inductive Verb
  /-- `init SPONSOR`: a join token for SPONSOR to enroll into follow's World (key, next-key digest,
  the World's origin, the key's join consent over them: PROTOCOL-79) -/
  | init
  /-- `enroll TOKEN`: sponsor a new member -/
  | enroll
  /-- `install TEXT`: install the package TEXT reads to (LANG's text form) -/
  | install
  /-- `create LAW…`: birth a data object owned by the signer, judged by the laws;
  `create --pkg PKG STATE LAW…`: birth an object programmed by package PKG, its seed STATE read
  (at the package's state type, by LANG's reader, on follow's World) -/
  | create
  /-- `write OBJ KEY VALUE [--via GRANT]`: set one state slot -/
  | write
  /-- `law OBJ LAW… [--via GRANT]`: replace a data object's laws -/
  | law
  /-- `invoke OBJ METHOD ARGS [--range REL K [PREFIX]] [--pin REL KEY]... [--via GRANT]`: run a
  method; ARGS is read at the method's argument type (LANG's reader, on follow's World); a method
  that reads a relation by range is handed the range `--range` names, signed at follow's listing;
  each `--pin REL KEY` pins the row of relation REL at KEY (LANG text at the relation's key type) at
  follow's World, so a method's POINT read of it is handed that row and, on a `(live)` read, its key's
  cell liveness (CLIENT-35); `--pin OBJ/REL KEY` pins a row of another object OBJ's relation REL, a
  peer the method reads (CLIENT-50) -/
  | invoke
  /-- `grant TARGET MEMBER RIGHTS [--via PARENT]`: TARGET is an object, a value account
  (`well:ASSET` | `of:OWNER:ASSET`: a `transfer:N` grant over it lends at most N of its balance, a
  `credit:N` grant over a well at most N of its floor, KERNEL-60), or `world` (the World,
  KERNEL-20: `observe` on it is following the log, `enroll:N` is sponsoring N members); MEMBER is a
  member or `anyone` (a grant whose grantee is the World: every enrolled member, including members
  enrolled later, KERNEL-26: a public object); RIGHTS is
  `observe`, `mutate`, `invoke:N`, `enroll:N`, `transfer:N`, `credit:N`, comma-separated; PARENT is the
  grant attenuated -/
  | grant
  /-- `retire CELL`: retire a grant the signer issued, or an object or an empty account it owns
  (KERNEL-70) -/
  | retire
  /-- `read OBJ [KEY=VALUE…]`: print the object's state slots; each `KEY=VALUE` must hold.
  `read OBJ ?`: print the object's self-description, its methods with their indices and argument
  types, its laws and its relations (`Command.Describe`, PROTOCOL-44).
  `read OBJ REL K [PREFIX]`: print the rows of relation REL of the object's package whose key
  starts with PREFIX (LANG text of the key's first fields; none: every row), at most K, one per
  line in key-byte order (PROTOCOL-51) -/
  | read
  /-- `rotate`: move the member to custody's precommitted NEXT key, precommitting the one after -/
  | rotate
  /-- `adopt INVITE KEY`: start follow from the writer's base the invitation INVITE pins, accepted only
  if INVITE is signed by KEY, the sponsor key the member trusts out of band (`Invite.accept`), and the
  base's World bytes hash to the pin (thin consent, PROTOCOL-14; PROTOCOL-42) -/
  | adopt
  /-- `sync`: catch up to the writer's tip and print the height and chain reached (a follower driven
  by a timer, HOSTING-17 §7; it signs envelopes only). `sync --to STEPS:CHAIN`: catch up THROUGH
  another member's stated position and compare (PROTOCOL-74): `shared STEPS` when follow's own fold
  holds that chain at that step count, `refused forkedWorld` when it holds another (the page refused),
  `refused ahead` when follow was already past it, `unreached STEPS` when the writer's tip is below it.
  `sync --attest`: catch up, then sign follow's own head (`Protocol.Head`) and print `attest HEX`.
  `sync --check ATTEST`: `--to` at the attested position, with the attestation's signature, World
  and signer checked by name (`badAttestation`, `otherWorld`, `badHeadSignature`, `notMember`,
  `staleKey`); prints `shared STEPS MEMBER`. `sync --post OBJ`: catch up, then post follow's own
  World's head (chain, height, roots, steps) to the member's head object OBJ (`Std.head`, PROTOCOL-75:
  `invoke OBJ post`, planned at the tip; every follow that absorbs it compares) -/
  | sync
  /-- `issue CAP`: bear a new denomination; its WELL is a value account owned by the signer whose
  id is the denomination, with floor `-CAP` (LEDGER-2) -/
  | issue
  /-- `account ASSET [--owner OWNER]`: open the empty account of denomination ASSET owned by OWNER
  (default: the signer), at its keyed id (LEDGER-7) -/
  | account
  /-- `transfer SRC DST AMOUNT [--via GRANT] [--once HEX]`: move AMOUNT from SRC to DST; an
  account is `well:ASSET` or `of:OWNER:ASSET`; `--once` spends a once-only key of SRC -/
  | transfer
  /-- `credit WELL ACCT AMOUNT [--via GRANT]`: extend a credit line of AMOUNT out of WELL's floor to
  ACCT, with the issuer's authority (LEDGER-4) -/
  | credit
  /-- `invite INPUT`: catch up, then sign an invitation to this World: INPUT (the World's origin
  inputs, which must make the member's own World), the pin of the member's World as it stands, and
  the member's id and key (PROTOCOL-42); prints `invite HEX` -/
  | invite
  /-- `receipt CALL`: catch up, then print a RECEIPT for the signed call's transaction id against
  follow's World (its roots and the trie paths that show it committed, refused or absent,
  `Protocol.Receipt`, PROTOCOL-45), the head it was built at, and the member's settlement of the
  call (`Protocol.Settle.ofReceipt`, PROTOCOL-46): `receipt HEX`, `head STEPS HEIGHT ROOTS`,
  `settle VERDICT`. The attempt store's `confirm` and `probe` (`Protocol.Attempt`).
  `receipt --health [MEMBER]`: catch up, then print a HEALTH RECEIPT for MEMBER (default: the signer)
  against follow's World (`Protocol.Health`, DESIGN-OBS §1.5): the member's ticks this window (the
  meter, KERNEL-68), its recorded refusals and the World's, each with its window-trie path: `health HEX`,
  `head STEPS HEIGHT ROOTS CHAIN`, then `ticks N of BUDGET in window W`, `refusals …`, `total …`. Read
  from the member's own fold: nothing is asked of the writer and nothing is signed -/
  | receipt
  /-- `cancel CALL`: catch up, then sign a cancel of the member's own signed call CALL (the member's
  signature over `domCancel ‖ txId`, `Ctx.cancelMessage`) and send it to the writer as the `cancel`
  op (KERNEL-60's record C1): the writer records the call `refused cancelled`, final, inside the
  call's window, so a loose call (sent, outcome unknown, window still live) can be closed by its
  member without waiting out the window. Prints `cancelled HEX`, the call's transaction id -/
  | cancel
  deriving DecidableEq, Repr

namespace Verb

def all : List Verb :=
  [init, enroll, install, create, write, law, invoke, grant, retire, read, rotate, adopt, sync, issue, account,
   transfer, credit, invite, receipt, cancel]

def word : Verb → String
  | init => "init" | enroll => "enroll" | install => "install"
  | create => "create" | write => "write" | law => "law" | invoke => "invoke"
  | grant => "grant" | retire => "retire" | read => "read" | rotate => "rotate" | adopt => "adopt"
  | sync => "sync" | issue => "issue" | account => "account" | transfer => "transfer" | credit => "credit"
  | invite => "invite" | receipt => "receipt" | cancel => "cancel"

def ofWord? (s : String) : Option Verb := all.find? (·.word == s)

end Verb

/-- A join token: what a newcomer hands its sponsor: its key, its next key's digest, the World it
consents to join, and its consent (`Receive.joinMessage`, PROTOCOL-79). -/
structure Join (D : Type) where
  key : ByteArray
  next : D
  origin : D
  join : ByteArray
  deriving DecidableEq

/-- What a grant is over: the World, an object (or any cell) by id, or a value account by its
name (`well:ASSET` | `of:OWNER:ASSET`, resolved to its id when the call is planned). -/
inductive GrantTarget (D : Type)
  | world
  | cell (id : D)
  | account (r : AcctRef D)

/-- What an `invoke` names for its plan to sign, as TEXT read on follow's World when the call is
planned: `range` is `--range REL K [PREFIX]`, the relation, at most K rows and the prefix TEXT of
the one range the method reads (`read OBJ REL K [PREFIX]`'s arguments, in its order); `points` are
the `--pin REL KEY`s, each a relation and the TEXT of one key of it (CLIENT-35). -/
structure InvokeReads where
  range : Option (String × Nat × Option String) := none
  points : List (String × String) := []
  deriving DecidableEq, Repr

/-- What `sync` relates follow's fold to (PROTOCOL-74): the writer's tip alone; another member's
stated position (its step count and chain bytes, as a page states them); follow's own head, to
attest; or another member's attestation, its bytes decoded by the machine (`Protocol.Head`). -/
inductive SyncMode
  | tip
  | to (steps : Nat) (chain : ByteArray)
  | attest
  | check (attestation : ByteArray)
  deriving DecidableEq, Repr

/-- What a `receipt` is about: a signed call (its bytes, `Ctx.callBytes`, decoded by the machine),
or a member's health (DESIGN-OBS §1.5; `none` is the signer). -/
inductive ReceiptOf (D : Type)
  | call (bytes : ByteArray)
  | health (member : Option D)

/-- A parsed command. -/
inductive Cmd (D : Type)
  | init (sponsor : D)
  | enroll (join : Join D)
  | install (pkg : ByteArray)
  /-- `pkg` = the package and the seed state's TEXT -/
  | create (pkg : Option (D × String)) (laws : List D)
  | write (obj : D) (key : Nat) (value : ByteArray) (via : Option D)
  | law (obj : D) (laws : List D) (via : Option D)
  /-- `args` is TEXT, read at the method's argument type when the call is planned; `reads` are the
  reads the plan signs beside the ones the derivation asks for (`InvokeReads`) -/
  | invoke (obj : D) (method : Nat) (args : String) (reads : InvokeReads) (via : Option D)
  /-- `grantee = none` is `anyone` (the World as grantee, KERNEL-26) -/
  | grant (target : GrantTarget D) (grantee : Option D) (rights : List Right) (via : Option D)
  | retire (cell : D)
  | read (obj : D) (expect : List (Nat × ByteArray))
  /-- `read OBJ ?` -/
  | describe (obj : D)
  /-- `read OBJ REL K [PREFIX]`: `pre` is TEXT, read at the relation's prefix type when the read is
  answered (on follow's World, where the package is) -/
  | rangeRead (obj : D) (rel : String) (most : Nat) (pre : Option String)
  | rotate
  /-- the invitation's bytes and the sponsor key the member trusts -/
  | adopt (invite key : ByteArray)
  | sync (mode : SyncMode)
  /-- `sync --post OBJ` (PROTOCOL-75): `invoke OBJ post` with follow's OWN World's head
  (`Protocol.Head.headText`), planned at the tip -/
  | post (obj : D)
  | issue (cap : Nat)
  /-- `owner = none` is the signer -/
  | account (asset : D) (owner : Option D)
  | transfer (src dst : AcctRef D) (amount : Nat) (via : Option D) (once : Option ByteArray)
  | credit (well : D) (acct : AcctRef D) (amount : Nat) (via : Option D)
  /-- the World's signed-start inputs (`Invite.startInput` bytes) -/
  | invite (input : ByteArray)
  /-- the signed call's bytes (`Ctx.callBytes`), decoded by the machine -/
  | receipt (q : ReceiptOf D)
  /-- the signed call's bytes (`Ctx.callBytes`) of the call to cancel, decoded by the machine -/
  | cancel (call : ByteArray)

/-- Every way an argv is refused. -/
inductive ParseRefusal
  /-- the argv's encoding, `4 + Σ (4 + len)`, is past `Bounds.argvBytesMax` -/
  | argvPastBound (size : Nat)
  | notUtf8 (index : Nat)
  | noVerb
  | unknownVerb (word : String)
  /-- the verb got the wrong arguments; `usage` is its grammar -/
  | usage (verb : String) (usage : String)
  | badDigest (arg : String)
  | badNumber (arg : String)
  | badRight (arg : String)
  | badToken (arg : String)
  | badExpect (arg : String)
  /-- `install`'s text does not read as a package in bounds; LANG's reason -/
  | badPackage (why : String)
  /-- an account is neither `well:ASSET` nor `of:OWNER:ASSET` -/
  | badAccount (arg : String)
  /-- a `--once` key is not hex, or is empty -/
  | badOnce (arg : String)
  deriving DecidableEq, Repr

/-- The refusal's name on the wire (law 7): the constructor, without its arguments. Distinct
constructors have distinct names (`ParseRefusal.name_injective`). -/
def ParseRefusal.name : ParseRefusal → String
  | .argvPastBound _ => "argvPastBound" | .notUtf8 _ => "notUtf8" | .noVerb => "noVerb"
  | .unknownVerb _ => "unknownVerb" | .usage _ _ => "usage" | .badDigest _ => "badDigest"
  | .badNumber _ => "badNumber" | .badRight _ => "badRight" | .badToken _ => "badToken"
  | .badExpect _ => "badExpect" | .badPackage _ => "badPackage" | .badAccount _ => "badAccount"
  | .badOnce _ => "badOnce"

/-- The constructor's index, the thing a name must determine. -/
def ParseRefusal.tag : ParseRefusal → Nat
  | .argvPastBound _ => 0 | .notUtf8 _ => 1 | .noVerb => 2 | .unknownVerb _ => 3 | .usage _ _ => 4
  | .badDigest _ => 5 | .badNumber _ => 6 | .badRight _ => 7 | .badToken _ => 8 | .badExpect _ => 9
  | .badPackage _ => 10 | .badAccount _ => 11 | .badOnce _ => 12

def usage : Verb → String
  | .init => "init SPONSOR" | .enroll => "enroll TOKEN"
  | .install => "install TEXT" | .create => "create [--pkg PKG STATE] LAW..."
  | .write => "write OBJ KEY VALUE [--via GRANT]" | .law => "law OBJ LAW... [--via GRANT]"
  | .invoke => "invoke OBJ METHOD ARGS [--range REL K [PREFIX]] [--pin [OBJ/]REL KEY]... [--via GRANT]"
  | .grant => "grant TARGET|ACCOUNT|world MEMBER|anyone RIGHTS [--via PARENT]"
  | .retire => "retire CELL" | .read => "read OBJ [KEY=VALUE...] | read OBJ ? | read OBJ REL K [PREFIX]" | .rotate => "rotate"
  | .adopt => "adopt INVITE KEY" | .sync => "sync [--to STEPS:CHAIN | --attest | --check ATTEST | --post OBJ]"
  | .issue => "issue CAP"
  | .account => "account ASSET [--owner OWNER]"
  | .transfer => "transfer SRC DST AMOUNT [--via GRANT] [--once HEX]"
  | .credit => "credit WELL ACCT AMOUNT [--via GRANT]"
  | .invite => "invite INPUT"
  | .receipt => "receipt CALL | receipt --health [MEMBER]"
  | .cancel => "cancel CALL"

def argvSize (argv : List ByteArray) : Nat := 4 + (argv.map (4 + ·.size)).sum

variable {D : Type}

/-- The join token's bytes: `key ‖ next ‖ origin ‖ join`, each `u32le len ‖ bytes`. -/
def Join.bytes (dbytes : D → ByteArray) (j : Join D) : ByteArray :=
  let f (b : ByteArray) := Codec.Stream.u32.bytes b.size.toUInt32 ++ b
  f j.key ++ f (dbytes j.next) ++ f (dbytes j.origin) ++ f j.join

def Join.ofBytes (digestOf : ByteArray → Option D) (b : ByteArray) : Option (Join D) :=
  let field (i : Nat) : Option (ByteArray × Nat) :=
    match Codec.Stream.u32.get b i with
    | .ok (n, j) => if j + n.toNat ≤ b.size then some (b.extract j (j + n.toNat), j + n.toNat) else none
    | .error _ => none
  do
    let (key, i) ← field 0
    let (nb, i) ← field i
    let (ob, i) ← field i
    let (join, i) ← field i
    if i = b.size then some { key, next := ← digestOf nb, origin := ← digestOf ob, join } else none

section
variable (digestOf : ByteArray → Option D)

def digestArg (s : String) : Except ParseRefusal D :=
  match Text.ofHex s >>= digestOf with
  | some d => .ok d
  | none => .error (.badDigest s)

def numArg (s : String) : Except ParseRefusal Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .error (.badNumber s)

def rightArg (s : String) : Except ParseRefusal Right :=
  if s = "observe" then .ok .observe
  else if s = "mutate" then .ok .mutate
  else match (s.dropPrefix? "invoke:").bind (·.toString.toNat?) with
    | some m => .ok (.invoke m)
    | none => match (s.dropPrefix? "enroll:").bind (·.toString.toNat?) with
      | some n => .ok (.enroll n)
      | none => match (s.dropPrefix? "transfer:").bind (·.toString.toNat?) with
        | some n => .ok (.transfer n)
        | none => match (s.dropPrefix? "credit:").bind (·.toString.toNat?) with
          | some n => .ok (.credit n)
          | none => .error (.badRight s)

def expectArg (s : String) : Except ParseRefusal (Nat × ByteArray) :=
  match s.splitOn "=" with
  | [k, v] => match k.toNat? with
    | some n => .ok (n, v.toUTF8)
    | none => .error (.badExpect s)
  | _ => .error (.badExpect s)

/-- A package's text, read by LANG's reader, as its canonical bytes. -/
def packageArg (t : String) : Except ParseRefusal ByteArray :=
  match Lang.Read.readPackage t with
  | .error e => .error (.badPackage e.text)
  | .ok p => match Lang.Wire.encodePackage p with
    | some b => .ok b
    | none => .error (.badPackage "past the package bounds")

/-- A trailing `--via GRANT`, or none. -/
def viaArg (v : Verb) : List String → Except ParseRefusal (Option D)
  | [] => .ok none
  | ["--via", g] => (digestArg digestOf g).map some
  | _ => .error (.usage v.word (usage v))

/-- An account reference: `well:ASSET` (the well, whose id is its denomination) or
`of:OWNER:ASSET` (OWNER's account of ASSET, resolved by the receiver to `accountId`). -/
def acctArg (s : String) : Except ParseRefusal (AcctRef D) :=
  match s.splitOn ":" with
  | ["well", a] => match Text.ofHex a >>= digestOf with
    | some a => .ok (.well a)
    | none => .error (.badAccount s)
  | ["of", o, a] => match Text.ofHex o >>= digestOf, Text.ofHex a >>= digestOf with
    | some o, some a => .ok (.of o a)
    | _, _ => .error (.badAccount s)
  | _ => .error (.badAccount s)

/-- Trailing `--FLAG VALUE` pairs, each flag at most once and only from `allowed`, in any order. -/
def flagsArg (v : Verb) (allowed : List String) : List String → Except ParseRefusal (List (String × String))
  | [] => .ok []
  | f :: x :: rest =>
      if allowed.contains f then do
        let fs ← flagsArg v allowed rest
        if fs.any (·.1 = f) then throw (.usage v.word (usage v)) else pure ((f, x) :: fs)
      else .error (.usage v.word (usage v))
  | [_] => .error (.usage v.word (usage v))

/-- The value of `--via` among parsed flags, as a grant. -/
def viaFlag (fs : List (String × String)) : Except ParseRefusal (Option D) :=
  match fs.lookup "--via" with
  | some g => (digestArg digestOf g).map some
  | none => .ok none

/-- `invoke`'s `--pin REL KEY`s, in order. -/
def pinsArg (v : Verb) : List String → Except ParseRefusal (List (String × String))
  | [] => .ok []
  | "--pin" :: r :: k :: rest => do pure ((r, k) :: (← pinsArg v rest))
  | _ => .error (.usage v.word (usage v))

/-- `invoke`'s `[--range REL K [PREFIX]] [--pin REL KEY]...`, what is left of its tail once `--via`
is split off. A PREFIX is the word after K unless that word is `--pin` (no LANG text is). -/
def readsArg (v : Verb) : List String → Except ParseRefusal InvokeReads
  | "--range" :: r :: k :: rest => do
      let n ← numArg k
      match rest with
      | [] => pure { range := some (r, n, none) }
      | "--pin" :: _ => pure { range := some (r, n, none), points := ← pinsArg v rest }
      | p :: rest' => pure { range := some (r, n, some p), points := ← pinsArg v rest' }
  | rest => do pure { points := ← pinsArg v rest }

/-- Split a trailing `--via GRANT` off a variable-length tail. -/
def splitVia (args : List String) : List String × List String :=
  match args.reverse with
  | g :: "--via" :: rest => (rest.reverse, ["--via", g])
  | _ => (args, [])

def parseVerb (v : Verb) (args : List String) : Except ParseRefusal (Cmd D) :=
  let bad : Except ParseRefusal (Cmd D) := .error (.usage v.word (usage v))
  match v, args with
  | .init, [s] => .init <$> digestArg digestOf s
  | .enroll, [t] =>
      match Text.ofHex t >>= Join.ofBytes digestOf with
      | some j => .ok (.enroll j)
      | none => .error (.badToken t)
  | .install, [t] => (.install ·) <$> packageArg t
  | .create, "--pkg" :: p :: st :: ls => do
      pure (.create (some (← digestArg digestOf p, st)) (← mapEx (digestArg digestOf) ls))
  | .create, ls => .create none <$> mapEx (digestArg digestOf) ls
  | .write, o :: k :: val :: via => do
      pure (.write (← digestArg digestOf o) (← numArg k) val.toUTF8 (← viaArg digestOf .write via))
  | .law, o :: rest =>
      let (ls, via) := splitVia rest
      do pure (.law (← digestArg digestOf o) (← mapEx (digestArg digestOf) ls) (← viaArg digestOf .law via))
  | .invoke, o :: m :: a :: rest =>
      let (rg, via) := splitVia rest
      do pure (.invoke (← digestArg digestOf o) (← numArg m) a (← readsArg .invoke rg)
        (← viaArg digestOf .invoke via))
  | .grant, t :: m :: rs :: via => do
      let target ← if t = "world" then pure GrantTarget.world
        else if t.startsWith "well:" || t.startsWith "of:" then GrantTarget.account <$> acctArg digestOf t
        else GrantTarget.cell <$> digestArg digestOf t
      let grantee ← if m = "anyone" then pure none else some <$> digestArg digestOf m
      pure (.grant target grantee (← mapEx rightArg (rs.splitOn ","))
        (← viaArg digestOf .grant via))
  | .retire, [x] => .retire <$> digestArg digestOf x
  | .read, [o, "?"] => .describe <$> digestArg digestOf o
  -- a first argument with `=` is an expectation; one without is a relation's label
  | .read, o :: r :: k :: p =>
      if r.contains '=' then do pure (.read (← digestArg digestOf o) (← mapEx expectArg (r :: k :: p)))
      else match p with
        | [] => do pure (.rangeRead (← digestArg digestOf o) r (← numArg k) none)
        | [t] => do pure (.rangeRead (← digestArg digestOf o) r (← numArg k) (some t))
        | _ => bad
  | .read, o :: es => do pure (.read (← digestArg digestOf o) (← mapEx expectArg es))
  | .rotate, [] => .ok .rotate
  | .sync, [] => .ok (.sync .tip)
  | .sync, ["--attest"] => .ok (.sync .attest)
  | .sync, ["--post", o] => do pure (.post (← digestArg digestOf o))
  -- `STEPS:CHAIN`: a step count and the chain's hex, as `sync` prints them
  | .sync, ["--to", a] =>
      match a.splitOn ":" with
      | [s, c] =>
          match s.toNat?, Text.ofHex c with
          | some n, some cb => .ok (.sync (.to n cb))
          | none, _ => .error (.badNumber s)
          | _, none => .error (.badToken c)
      | _ => .error (.badToken a)
  | .sync, ["--check", h] =>
      match Text.ofHex h with
      | some b => .ok (.sync (.check b))
      | none => .error (.badToken h)
  | .adopt, [i, k] =>
      match Text.ofHex i, Text.ofHex k with
      | some inv, some key => .ok (.adopt inv key)
      | none, _ => .error (.badToken i)
      | _, none => .error (.badToken k)
  | .receipt, ["--health"] => .ok (.receipt (.health none))
  | .receipt, ["--health", m] => do pure (.receipt (.health (some (← digestArg digestOf m))))
  | .receipt, [c] =>
      match Text.ofHex c with
      | some call => .ok (.receipt (.call call))
      | none => .error (.badToken c)
  | .cancel, [c] =>
      match Text.ofHex c with
      | some call => .ok (.cancel call)
      | none => .error (.badToken c)
  | .invite, [i] =>
      match Text.ofHex i with
      | some input => .ok (.invite input)
      | none => .error (.badToken i)
  | .issue, [c] => .issue <$> numArg c
  | .account, a :: fl => do
      let fs ← flagsArg .account ["--owner"] fl
      let owner ← match fs.lookup "--owner" with
        | some o => some <$> digestArg digestOf o
        | none => pure none
      pure (.account (← digestArg digestOf a) owner)
  | .transfer, s :: d :: n :: fl => do
      let fs ← flagsArg .transfer ["--via", "--once"] fl
      let once ← match fs.lookup "--once" with
        | some k => match Text.ofHex k with
          | some b => if b.isEmpty then throw (.badOnce k) else pure (some b)
          | none => throw (.badOnce k)
        | none => pure none
      pure (.transfer (← acctArg digestOf s) (← acctArg digestOf d) (← numArg n) (← viaFlag digestOf fs) once)
  | .credit, w :: a :: n :: fl => do
      let fs ← flagsArg .credit ["--via"] fl
      pure (.credit (← digestArg digestOf w) (← acctArg digestOf a) (← numArg n) (← viaFlag digestOf fs))
  | _, _ => bad

/-- THE parser: argv bytes to a command, or a refusal by name. -/
def parse (argv : List ByteArray) : Except ParseRefusal (Cmd D) := do
  if argvSize argv > Bounds.argvBytesMax then throw (.argvPastBound (argvSize argv))
  let words ← mapEx (fun (b, i) => match String.fromUTF8? b with
    | some s => .ok s
    | none => .error (.notUtf8 i)) argv.zipIdx
  match words with
  | [] => throw .noVerb
  | w :: args => match Verb.ofWord? w with
    | none => throw (.unknownVerb w)
    | some v => parseVerb digestOf v args

end
end Nanodregg.Protocol.Command
