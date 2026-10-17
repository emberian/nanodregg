import Protocol.Table
import Codec.Layout

/-!
# Emit.Rust — the Rust copy of the protocol table

`client/src/generated.rs` is this function's output and nothing else (law 2: Rust consumes
Lean-generated tables, never hand-copied constants). Every op, status and step code is read off
`Nanodregg.Protocol`'s `all` lists, so a constructor added to the table appears in Rust on the
next regeneration; a bound that does not fit the Rust type refuses to emit.
-/

namespace Nanodregg.Emit.Rust

open Nanodregg.Protocol

/-- The constructor's own name as a Rust constant: `Op.submit` ↦ `SUBMIT`, `Step.signNext` ↦ `SIGN_NEXT`. -/
def constName {α : Type} [Repr α] (a : α) : String :=
  let name := ((toString (repr a)).splitOn ".").getLast!
  String.ofList (name.toList.flatMap fun c => if c.isUpper then ['_', c] else [c.toUpper])

/-- The constructor's own name as a Rust type name: `Step.signNext` ↦ `SignNext`. -/
def ctorName {α : Type} [Repr α] (a : α) : String :=
  match ((toString (repr a)).splitOn ".").getLast!.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => ""

/-- One `pub const NAME: u8 = n;` line per value. -/
def byteConsts {α : Type} [Repr α] (values : List α) (code : α → UInt8) : List String :=
  values.map fun v => s!"    pub const {constName v}: u8 = {code v};"

/-- A `pub mod` of byte constants. -/
def byteModule {α : Type} [Repr α] (name : String) (values : List α) (code : α → UInt8) : String :=
  String.intercalate "\n" ([s!"pub mod {name} \{"] ++ byteConsts values code ++ ["}"])

/-- The bounds the client enforces, with their Rust names. -/
def bounds : List (String × Nat) :=
  [("FRAME_BYTES_MAX", Bounds.frameBytesMax),
   ("ARGV_BYTES_MAX", Bounds.argvBytesMax),
   ("STEPS_PER_COMMAND_MAX", Bounds.stepsPerCommandMax),
   ("SENDS_MAX", Bounds.sendsMax),
   ("CONNECTIONS_MAX", Bounds.connectionsMax),
   ("PEER_CONNECTIONS_MAX", Bounds.peerConnectionsMax),
   ("IDLE_MS_MAX", Bounds.idleMsMax),
   ("FRAME_MS_MAX", Bounds.frameMsMax),
   ("REPLY_MS_MAX", Bounds.replyMsMax),
   ("REPLY_WRITE_MS_MAX", Bounds.replyWriteMsMax)]

/-- A `pub const NAME: u32 = n;` line, or the name of a bound that does not fit `u32`. -/
def u32Const (entry : String × Nat) : Except String String :=
  if entry.2 < 2 ^ 32 then .ok s!"pub const {entry.1}: u32 = {entry.2};"
  else .error s!"bound {entry.1} = {entry.2} does not fit u32"

/-! ## Layout readers and writers

Each `Codec.Layout` in the table becomes a Rust struct (or, for the tagged steps, an enum) with a
`decode` and an `encode` that follow `Codec.Layout.codec` byte for byte: the same field order, the
same `u32le` lengths, the same bound, and the same refusal at the same offset. -/

open Nanodregg.Codec

/-- `Op.submit` ↦ `Submit`. -/
def camel (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => s

def rustType : Field → String
  | .byte _ => "u8"
  | .u64 _ => "u64"
  | .bytes _ => "Vec<u8>"
  | .list _ => "Vec<Vec<u8>>"
  | .oneOf n _ => camel n

def readField (max : Nat) : Field → String
  | .byte n => s!"let {n} = c.byte()?;"
  | .u64 n => s!"let {n} = c.u64()?;"
  | .bytes n => s!"let {n} = c.bytes({max})?;"
  | .list n => s!"let {n} = c.list({max})?;"
  | .oneOf n _ => s!"let {n} = c.one_of({camel n}::from_code)?;"

def writeField (max : Nat) : Field → String
  | .byte n => s!"out.push(*{n});"
  | .u64 n => s!"out.extend_from_slice(&{n}.to_le_bytes());"
  | .bytes n => s!"put_bytes(&mut out, {n}, {max})?;"
  | .list n => s!"put_list(&mut out, {n}, {max})?;"
  | .oneOf n _ => s!"out.push({n}.code());"

def fieldNames (l : Layout) : String := String.intercalate ", " (l.map Field.name)

/-- `Name { a, b }`, or one field per line when the fields are wider than rustfmt's
`struct_lit_width` (18), so the emitted file is already `cargo fmt` clean. -/
def structLit (indent name : String) (l : Layout) : String :=
  if (fieldNames l).length ≤ 18 then s!"{name} \{ {fieldNames l} }"
  else String.intercalate "\n" ([s!"{name} \{"] ++ l.map (fun f => s!"{indent}    {f.name},") ++ [s!"{indent}}"])

def fieldDecls (indent vis : String) (l : Layout) : List String :=
  l.map fun f => s!"{indent}{vis}{f.name}: {rustType f},"

/-- A Rust enum for a `oneOf` field: its cases, their codes, and the inverse. -/
def oneOfEnum (name : String) (cases : List (String × UInt8)) : String :=
  let ty := camel name
  String.intercalate "\n" <|
    ["    #[derive(Debug, Clone, Copy, PartialEq, Eq)]", s!"    pub enum {ty} \{"] ++
    cases.map (fun c => s!"        {camel c.1},") ++
    ["    }", "", s!"    impl {ty} \{", "        pub fn code(self) -> u8 {", "            match self {"] ++
    cases.map (fun c => s!"                {ty}::{camel c.1} => {c.2},") ++
    ["            }", "        }", "", "        pub fn from_code(b: u8) -> Option<Self> {", "            match b {"] ++
    cases.map (fun c => s!"                {c.2} => Some({ty}::{camel c.1}),") ++
    ["                _ => None,", "            }", "        }", "    }"]

/-- The cursor's `oneOf` reader, emitted only when some layout has a `oneOf` field. -/
def oneOfReader : String := String.intercalate "\n" [
  "    impl Cursor<'_> {",
  "        fn one_of<T>(&mut self, from_code: fn(u8) -> Option<T>) -> Result<T, Refusal> {",
  "            let at = self.i;",
  "            let tag = self.byte()?;",
  "            from_code(tag).ok_or(Refusal::BadTag { offset: at, tag })",
  "        }",
  "    }"]

/-- The cursor's `u64` reader, emitted only when some layout has a `u64` field. -/
def u64Reader : String := String.intercalate "\n" [
  "    impl Cursor<'_> {",
  "        fn u64(&mut self) -> Result<u64, Refusal> {",
  "            let eight = self.b.get(self.i..self.i + 8).ok_or(Refusal::Truncated {",
  "                offset: self.i,",
  "                need: 8,",
  "            })?;",
  "            self.i += 8;",
  "            let mut v = [0u8; 8];",
  "            v.copy_from_slice(eight);",
  "            Ok(u64::from_le_bytes(v))",
  "        }",
  "    }"]

/-- Every `oneOf` field of the given layouts, once per name. -/
def oneOfs (ls : List Layout) : List (String × List (String × UInt8)) :=
  ls.flatten.foldl (fun acc f => match f with
    | .oneOf n cs => if acc.any (·.1 == n) then acc else acc ++ [(n, cs)]
    | _ => acc) []

/-- A struct for one untagged layout. -/
def structFor (name : String) (max : Nat) (l : Layout) (total : Option Nat := none) : String :=
  let totalRead := match total with
    | some t => [s!"            if c.i > {t} \{", s!"                return Err(Refusal::PastBound \{",
        "                    offset: 0,", s!"                    limit: {t},", "                    got: c.i,",
        "                });", "            }"]
    | none => []
  let totalWrite := match total with
    | some t => [s!"            if out.len() > {t} \{", s!"                return Err(Refusal::PastBound \{",
        "                    offset: 0,", s!"                    limit: {t},", "                    got: out.len(),",
        "                });", "            }"]
    | none => []
  String.intercalate "\n" <|
    [s!"    #[derive(Debug, Clone, PartialEq, Eq)]", s!"    pub struct {name} \{"] ++ fieldDecls "        " "pub " l ++
    ["    }", "", s!"    impl {name} \{",
     "        pub fn decode(b: &[u8]) -> Result<Self, Refusal> {",
     "            let mut c = Cursor { b, i: 0 };"] ++
    l.map (fun f => "            " ++ readField max f) ++ totalRead ++
    ["            c.end()?;", s!"            Ok({structLit "            " name l})", "        }", "",
     "        pub fn encode(&self) -> Result<Vec<u8>, Refusal> {",
     "            let mut out = Vec::new();",
     s!"            let {structLit "            " name l} = self;"] ++
    l.map (fun f => "            " ++ writeField max f) ++ totalWrite ++
    ["            Ok(out)", "        }", "    }"]

/-- An enum for the tagged step frame. -/
def stepEnum (max : Nat) : String :=
  let variants := Step.all.map fun st =>
    let l := st.layout
    String.intercalate "\n" ([s!"        {ctorName st} \{"] ++ fieldDecls "            " "" l ++
      ["        },"])
  let readArms := Step.all.map fun st =>
    let l := st.layout
    String.intercalate "\n" ([s!"                {st.code} => \{"] ++
      l.map (fun f => "                    " ++ readField max f) ++
      [s!"                    {structLit "                    " ("Step::" ++ ctorName st) l}", "                }"])
  let writeArms := Step.all.map fun st =>
    let l := st.layout
    String.intercalate "\n" ([s!"                {structLit "                " ("Step::" ++ ctorName st) l} => \{",
      s!"                    out.push({st.code});"] ++
      l.map (fun f => "                    " ++ writeField max f) ++ ["                }"])
  String.intercalate "\n" <|
    ["    #[derive(Debug, Clone, PartialEq, Eq)]", "    pub enum Step {"] ++ variants ++ ["    }", "",
     "    impl Step {",
     "        pub fn decode(b: &[u8]) -> Result<Self, Refusal> {",
     "            let mut c = Cursor { b, i: 0 };",
     "            let at = c.i;",
     "            let step = match c.byte()? {"] ++ readArms ++
    ["                tag => return Err(Refusal::BadTag { offset: at, tag }),",
     "            };", "            c.end()?;", "            Ok(step)", "        }", "",
     "        pub fn encode(&self) -> Result<Vec<u8>, Refusal> {",
     "            let mut out = Vec::new();", "            match self {"] ++ writeArms ++
    ["            }", "            Ok(out)", "        }", "    }"]

/-- The cursor and writers every layout shares: `Codec.Stream`'s u8, u32le, bytesOf and array. -/
def layoutPrelude : String := String.intercalate "\n" [
  "    /// Why a payload was refused: `Codec.Refusal`, with the same offsets.",
  "    #[derive(Debug, Clone, PartialEq, Eq)]",
  "    pub enum Refusal {",
  "        Truncated {",
  "            offset: usize,",
  "            need: usize,",
  "        },",
  "        Trailing {",
  "            offset: usize,",
  "        },",
  "        PastBound {",
  "            offset: usize,",
  "            limit: usize,",
  "            got: usize,",
  "        },",
  "        BadTag {",
  "            offset: usize,",
  "            tag: u8,",
  "        },",
  "    }",
  "",
  "    struct Cursor<'a> {",
  "        b: &'a [u8],",
  "        i: usize,",
  "    }",
  "",
  "    impl Cursor<'_> {",
  "        fn byte(&mut self) -> Result<u8, Refusal> {",
  "            let v = *self.b.get(self.i).ok_or(Refusal::Truncated {",
  "                offset: self.i,",
  "                need: 1,",
  "            })?;",
  "            self.i += 1;",
  "            Ok(v)",
  "        }",
  "        fn u32(&mut self) -> Result<usize, Refusal> {",
  "            let four = self.b.get(self.i..self.i + 4).ok_or(Refusal::Truncated {",
  "                offset: self.i,",
  "                need: 4,",
  "            })?;",
  "            self.i += 4;",
  "            Ok(u32::from_le_bytes([four[0], four[1], four[2], four[3]]) as usize)",
  "        }",
  "        fn bytes(&mut self, max: usize) -> Result<Vec<u8>, Refusal> {",
  "            let at = self.i;",
  "            let n = self.u32()?;",
  "            if n > max {",
  "                return Err(Refusal::PastBound {",
  "                    offset: at,",
  "                    limit: max,",
  "                    got: n,",
  "                });",
  "            }",
  "            let v = self.b.get(self.i..self.i + n).ok_or(Refusal::Truncated {",
  "                offset: self.i,",
  "                need: n,",
  "            })?;",
  "            self.i += n;",
  "            Ok(v.to_vec())",
  "        }",
  "        fn list(&mut self, max: usize) -> Result<Vec<Vec<u8>>, Refusal> {",
  "            let at = self.i;",
  "            let n = self.u32()?;",
  "            if n > max {",
  "                return Err(Refusal::PastBound {",
  "                    offset: at,",
  "                    limit: max,",
  "                    got: n,",
  "                });",
  "            }",
  "            (0..n).map(|_| self.bytes(max)).collect()",
  "        }",
  "        fn end(&self) -> Result<(), Refusal> {",
  "            if self.i == self.b.len() {",
  "                Ok(())",
  "            } else {",
  "                Err(Refusal::Trailing { offset: self.i })",
  "            }",
  "        }",
  "    }",
  "",
  "    fn put_bytes(out: &mut Vec<u8>, v: &[u8], max: usize) -> Result<(), Refusal> {",
  "        if v.len() > max {",
  "            return Err(Refusal::PastBound {",
  "                offset: out.len(),",
  "                limit: max,",
  "                got: v.len(),",
  "            });",
  "        }",
  "        out.extend_from_slice(&(v.len() as u32).to_le_bytes());",
  "        out.extend_from_slice(v);",
  "        Ok(())",
  "    }",
  "",
  "    fn put_list(out: &mut Vec<u8>, v: &[Vec<u8>], max: usize) -> Result<(), Refusal> {",
  "        if v.len() > max {",
  "            return Err(Refusal::PastBound {",
  "                offset: out.len(),",
  "                limit: max,",
  "                got: v.len(),",
  "            });",
  "        }",
  "        out.extend_from_slice(&(v.len() as u32).to_le_bytes());",
  "        v.iter().try_for_each(|x| put_bytes(out, x, max))",
  "    }"]

/-- The follow socket's payloads. -/
def layoutModule : String := String.intercalate "\n\n" ([
  "/// The follow socket's payloads (Protocol.Table layouts; Lean codec: Protocol.Frames).\npub mod layout {",
  layoutPrelude] ++
  (let es := oneOfs (commandLayout :: resumeLayout :: Step.all.map Step.layout)
   let ls := commandLayout :: resumeLayout :: signResultLayout :: precommitResultLayout :: Step.all.map Step.layout
   let hasU64 := ls.flatten.any fun f => match f with | .u64 _ => true | _ => false
   (if es.isEmpty then [] else [oneOfReader]) ++ (if hasU64 then [u64Reader] else []) ++
     es.map fun p => oneOfEnum p.1 p.2) ++ [
  structFor "Command" Bounds.argvBytesMax commandLayout (some Bounds.argvBytesMax),
  structFor "Resume" Bounds.frameBytesMax resumeLayout,
  structFor "SignResult" Bounds.frameBytesMax signResultLayout,
  structFor "PrecommitResult" Bounds.frameBytesMax precommitResultLayout,
  stepEnum Bounds.frameBytesMax ++ "\n}"])

/-- `CloseReason` as a Rust enum whose `name()` is the Lean constructor's wire name. -/
def closeReasonEnum : String :=
  String.intercalate "\n" (
    ["/// Why a connection was closed (Protocol.CloseReason); the `closed` frame's payload is `name()`.",
     "#[derive(Debug, Clone, Copy, PartialEq, Eq)]", "pub enum CloseReason {"] ++
    CloseReason.all.map (fun r => s!"    {ctorName r},") ++
    ["}", "", "impl CloseReason {", "    pub fn name(self) -> &'static str {", "        match self {"] ++
    CloseReason.all.map (fun r => s!"            CloseReason::{ctorName r} => \"{r.name}\",") ++
    ["        }", "    }", "}"])

def header : String :=
  "// GENERATED by emit-rust from Protocol/Table.lean — do not edit\n" ++
  "// Regenerate: lake exe emit-rust client/src/generated.rs\n" ++
  "// Check:      lake exe emit-rust --check client/src/generated.rs"

/-- The whole file. -/
def file : Except String String := do
  let consts ← bounds.mapM u32Const
  let opsOn (s : Socket) := Op.all.filter (·.socket == s)
  pure <| String.intercalate "\n\n"
    [header,
     String.intercalate "\n" consts,
     byteModule "host_op" (opsOn .host) Op.code,
     byteModule "follow_op" (opsOn .follow) Op.code,
     byteModule "status" Status.all Status.code,
     closeReasonEnum,
     byteModule "step" Step.all Step.code,
     layoutModule] ++ "\n"

/-- `emit-rust PATH` writes the file; `emit-rust --check PATH` exits 1 if PATH differs. -/
def run (args : List String) : IO UInt32 := do
  match file with
  | .error e => IO.eprintln s!"emit-rust: {e}"; return 2
  | .ok text =>
    match args with
    | [path] => IO.FS.writeFile path text; return 0
    | ["--check", path] =>
      let current ← IO.FS.readFile path
      if current == text then return 0
      IO.eprintln s!"emit-rust: {path} differs from the table; regenerate it"
      return 1
    | _ => IO.eprintln "usage: emit-rust [--check] PATH"; return 2

end Nanodregg.Emit.Rust
