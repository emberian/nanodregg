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

namespace Nanodregg.Protocol.Command

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- Every verb. -/
inductive Verb
  /-- `init SPONSOR`: a join token for SPONSOR to enroll (key, next-key digest, possession) -/
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
  /-- `invoke OBJ METHOD ARGS [--via GRANT]`: run a method; ARGS is read at the method's argument
  type (LANG's reader, on follow's World) -/
  | invoke
  /-- `grant TARGET MEMBER RIGHTS [--via PARENT]`: TARGET is an object or `world` (the World,
  KERNEL-20: `observe` on it is following the log, `enroll:N` is sponsoring N members); MEMBER is a
  member or `anyone` (a grant whose grantee is the World: every enrolled member, including members
  enrolled later, KERNEL-26: a public object); RIGHTS is
  `observe`, `mutate`, `invoke:N`, `enroll:N`, comma-separated; PARENT is the grant attenuated -/
  | grant
  /-- `revoke GRANT` -/
  | revoke
  /-- `read OBJ [KEY=VALUE…]`: print the object's state slots; each `KEY=VALUE` must hold -/
  | read
  /-- `rotate`: move the member to custody's precommitted NEXT key, precommitting the one after -/
  | rotate
  /-- `adopt HEIGHT DIGEST`: start follow from the writer's base at HEIGHT, accepted only if its
  World bytes hash to DIGEST, a pin the member trusts out of band (thin consent, PROTOCOL-14) -/
  | adopt
  deriving DecidableEq, Repr

namespace Verb

def all : List Verb :=
  [init, enroll, install, create, write, law, invoke, grant, revoke, read, rotate, adopt]

def word : Verb → String
  | init => "init" | enroll => "enroll" | install => "install"
  | create => "create" | write => "write" | law => "law" | invoke => "invoke"
  | grant => "grant" | revoke => "revoke" | read => "read" | rotate => "rotate" | adopt => "adopt"

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
  | install (pkg : ByteArray)
  /-- `pkg` = the package and the seed state's TEXT -/
  | create (pkg : Option (D × String)) (laws : List D)
  | write (obj : D) (key : Nat) (value : ByteArray) (via : Option D)
  | law (obj : D) (laws : List D) (via : Option D)
  /-- `args` is TEXT, read at the method's argument type when the call is planned -/
  | invoke (obj : D) (method : Nat) (args : String) (via : Option D)
  /-- `target = none` is the World; `grantee = none` is `anyone` (the World as grantee, KERNEL-26) -/
  | grant (target : Option D) (grantee : Option D) (rights : List Right) (via : Option D)
  | revoke (grant : D)
  | read (obj : D) (expect : List (Nat × ByteArray))
  | rotate
  | adopt (pin : Thin.Pin)

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
  | .init => "init SPONSOR" | .enroll => "enroll TOKEN"
  | .install => "install TEXT" | .create => "create [--pkg PKG STATE] LAW..."
  | .write => "write OBJ KEY VALUE [--via GRANT]" | .law => "law OBJ LAW... [--via GRANT]"
  | .invoke => "invoke OBJ METHOD ARGS [--via GRANT]" | .grant => "grant TARGET MEMBER|anyone RIGHTS [--via PARENT]"
  | .revoke => "revoke GRANT" | .read => "read OBJ [KEY=VALUE...]" | .rotate => "rotate"
  | .adopt => "adopt HEIGHT DIGEST"

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
    | none => match (s.dropPrefix? "enroll:").bind (·.toString.toNat?) with
      | some n => .ok (.enroll n)
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
  | .invoke, o :: m :: a :: via => do
      pure (.invoke (← digestArg digestOf o) (← numArg m) a (← viaArg digestOf .invoke via))
  | .grant, t :: m :: rs :: via => do
      let target ← if t = "world" then pure none else some <$> digestArg digestOf t
      let grantee ← if m = "anyone" then pure none else some <$> digestArg digestOf m
      pure (.grant target grantee (← mapEx rightArg (rs.splitOn ","))
        (← viaArg digestOf .grant via))
  | .revoke, [g] => .revoke <$> digestArg digestOf g
  | .read, o :: es => do pure (.read (← digestArg digestOf o) (← mapEx expectArg es))
  | .rotate, [] => .ok .rotate
  | .adopt, [h, d] => do
      let height ← numArg h
      match Text.ofHex d with
      | some digest => pure (.adopt ⟨height, digest⟩)
      | none => throw (.badDigest d)
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
