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

namespace Nanodregg.Protocol.Command

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- Every verb. -/
inductive Verb
  /-- `init SPONSOR`: a join token for SPONSOR to enroll (key, next-key digest, possession) -/
  | init
  /-- `enroll TOKEN`: sponsor a new member -/
  | enroll
  /-- `follow MEMBER`: let MEMBER follow the World, under the signer's follow grant -/
  | follow
  /-- `install TEXT`: install the package TEXT reads to (LANG's text form) -/
  | install
  /-- `create LAW…`: birth a data object owned by the signer, judged by the laws -/
  | create
  /-- `write OBJ KEY VALUE [--via GRANT]`: set one state slot -/
  | write
  /-- `law OBJ LAW… [--via GRANT]`: replace a data object's laws -/
  | law
  /-- `invoke OBJ METHOD ARGS [--via GRANT]`: run a method -/
  | invoke
  /-- `grant TARGET MEMBER RIGHTS`: RIGHTS is `observe`, `mutate`, `invoke:N`, comma-separated -/
  | grant
  /-- `revoke GRANT` -/
  | revoke
  /-- `read OBJ [KEY=VALUE…]`: print the object's state slots; each `KEY=VALUE` must hold -/
  | read
  deriving DecidableEq, Repr

namespace Verb

def all : List Verb := [init, enroll, follow, install, create, write, law, invoke, grant, revoke, read]

def word : Verb → String
  | init => "init" | enroll => "enroll" | follow => "follow" | install => "install"
  | create => "create" | write => "write" | law => "law" | invoke => "invoke"
  | grant => "grant" | revoke => "revoke" | read => "read"

def ofWord? (s : String) : Option Verb := all.find? (·.word == s)

end Verb

/-- A join token: what a newcomer hands its sponsor. -/
structure Join (D : Type) where
  key : ByteArray
  next : D
  possession : ByteArray
  deriving DecidableEq

/-- A parsed command. -/
inductive Cmd (D : Type)
  | init (sponsor : D)
  | enroll (join : Join D)
  | follow (grantee : D)
  | install (pkg : ByteArray)
  | create (laws : List D)
  | write (obj : D) (key : Nat) (value : ByteArray) (via : Option D)
  | law (obj : D) (laws : List D) (via : Option D)
  | invoke (obj : D) (method : Nat) (args : ByteArray) (via : Option D)
  | grant (target grantee : D) (rights : List Right)
  | revoke (grant : D)
  | read (obj : D) (expect : List (Nat × ByteArray))

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
  deriving DecidableEq, Repr

/-- The refusal's name on the wire (law 7): the constructor, without its arguments. Distinct
constructors have distinct names (`ParseRefusal.name_injective`). -/
def ParseRefusal.name : ParseRefusal → String
  | .argvPastBound _ => "argvPastBound" | .notUtf8 _ => "notUtf8" | .noVerb => "noVerb"
  | .unknownVerb _ => "unknownVerb" | .usage _ _ => "usage" | .badDigest _ => "badDigest"
  | .badNumber _ => "badNumber" | .badRight _ => "badRight" | .badToken _ => "badToken"
  | .badExpect _ => "badExpect" | .badPackage _ => "badPackage"

/-- The constructor's index, the thing a name must determine. -/
def ParseRefusal.tag : ParseRefusal → Nat
  | .argvPastBound _ => 0 | .notUtf8 _ => 1 | .noVerb => 2 | .unknownVerb _ => 3 | .usage _ _ => 4
  | .badDigest _ => 5 | .badNumber _ => 6 | .badRight _ => 7 | .badToken _ => 8 | .badExpect _ => 9
  | .badPackage _ => 10

def usage : Verb → String
  | .init => "init SPONSOR" | .enroll => "enroll TOKEN" | .follow => "follow MEMBER"
  | .install => "install TEXT" | .create => "create LAW..."
  | .write => "write OBJ KEY VALUE [--via GRANT]" | .law => "law OBJ LAW... [--via GRANT]"
  | .invoke => "invoke OBJ METHOD ARGS [--via GRANT]" | .grant => "grant TARGET MEMBER RIGHTS"
  | .revoke => "revoke GRANT" | .read => "read OBJ [KEY=VALUE...]"

def argvSize (argv : List ByteArray) : Nat := 4 + (argv.map (4 + ·.size)).sum

variable {D : Type}

/-- The join token's bytes: `key ‖ next ‖ possession`, each `u32le len ‖ bytes`. -/
def Join.bytes (dbytes : D → ByteArray) (j : Join D) : ByteArray :=
  let f (b : ByteArray) := Codec.Stream.u32.bytes b.size.toUInt32 ++ b
  f j.key ++ f (dbytes j.next) ++ f j.possession

def Join.ofBytes (digestOf : ByteArray → Option D) (b : ByteArray) : Option (Join D) :=
  let field (i : Nat) : Option (ByteArray × Nat) :=
    match Codec.Stream.u32.get b i with
    | .ok (n, j) => if j + n.toNat ≤ b.size then some (b.extract j (j + n.toNat), j + n.toNat) else none
    | .error _ => none
  do
    let (key, i) ← field 0
    let (nb, i) ← field i
    let (possession, i) ← field i
    if i = b.size then some { key, next := ← digestOf nb, possession } else none

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
  | .error e => .error (.badPackage e)
  | .ok p => match Lang.Wire.encodePackage p with
    | some b => .ok b
    | none => .error (.badPackage "past the package bounds")

/-- A trailing `--via GRANT`, or none. -/
def viaArg (v : Verb) : List String → Except ParseRefusal (Option D)
  | [] => .ok none
  | ["--via", g] => (digestArg digestOf g).map some
  | _ => .error (.usage v.word (usage v))

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
  | .follow, [m] => .follow <$> digestArg digestOf m
  | .install, [t] => (.install ·) <$> packageArg t
  | .create, ls => .create <$> mapEx (digestArg digestOf) ls
  | .write, o :: k :: val :: via => do
      pure (.write (← digestArg digestOf o) (← numArg k) val.toUTF8 (← viaArg digestOf .write via))
  | .law, o :: rest =>
      let (ls, via) := splitVia rest
      do pure (.law (← digestArg digestOf o) (← mapEx (digestArg digestOf) ls) (← viaArg digestOf .law via))
  | .invoke, o :: m :: a :: via => do
      pure (.invoke (← digestArg digestOf o) (← numArg m) a.toUTF8 (← viaArg digestOf .invoke via))
  | .grant, [t, m, rs] => do
      pure (.grant (← digestArg digestOf t) (← digestArg digestOf m)
        (← mapEx rightArg (rs.splitOn ",")))
  | .revoke, [g] => .revoke <$> digestArg digestOf g
  | .read, o :: es => do pure (.read (← digestArg digestOf o) (← mapEx expectArg es))
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
