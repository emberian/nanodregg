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

/-- The constructor's own name, upper case: `Op.submit` ↦ `SUBMIT`. -/
def constName {α : Type} [Repr α] (a : α) : String :=
  let full := toString (repr a)
  (full.splitOn ".").getLast!.toUpper

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
   ("CONNECTIONS_MAX", Bounds.connectionsMax)]

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
  | .bytes _ => "Vec<u8>"
  | .list _ => "Vec<Vec<u8>>"

def readField (max : Nat) : Field → String
  | .byte n => s!"let {n} = c.byte()?;"
  | .bytes n => s!"let {n} = c.bytes({max})?;"
  | .list n => s!"let {n} = c.list({max})?;"

def writeField (max : Nat) : Field → String
  | .byte n => s!"out.push(*{n});"
  | .bytes n => s!"put_bytes(&mut out, {n}, {max})?;"
  | .list n => s!"put_list(&mut out, {n}, {max})?;"

def fieldNames (l : Layout) : String := String.intercalate ", " (l.map Field.name)

/-- `Name { a, b }`, or one field per line when the fields are wider than rustfmt's
`struct_lit_width` (18), so the emitted file is already `cargo fmt` clean. -/
def structLit (indent name : String) (l : Layout) : String :=
  if (fieldNames l).length ≤ 18 then s!"{name} \{ {fieldNames l} }"
  else String.intercalate "\n" ([s!"{name} \{"] ++ l.map (fun f => s!"{indent}    {f.name},") ++ [s!"{indent}}"])

def fieldDecls (indent vis : String) (l : Layout) : List String :=
  l.map fun f => s!"{indent}{vis}{f.name}: {rustType f},"

/-- A struct for one untagged layout. -/
def structFor (name : String) (max : Nat) (l : Layout) : String :=
  String.intercalate "\n" <|
    [s!"    #[derive(Debug, Clone, PartialEq, Eq)]", s!"    pub struct {name} \{"] ++ fieldDecls "        " "pub " l ++
    ["    }", "", s!"    impl {name} \{",
     "        pub fn decode(b: &[u8]) -> Result<Self, Refusal> {",
     "            let mut c = Cursor { b, i: 0 };"] ++
    l.map (fun f => "            " ++ readField max f) ++
    ["            c.end()?;", s!"            Ok({structLit "            " name l})", "        }", "",
     "        pub fn encode(&self) -> Result<Vec<u8>, Refusal> {",
     "            let mut out = Vec::new();",
     s!"            let {structLit "            " name l} = self;"] ++
    l.map (fun f => "            " ++ writeField max f) ++
    ["            Ok(out)", "        }", "    }"]

/-- An enum for the tagged step frame. -/
def stepEnum (max : Nat) : String :=
  let variants := Step.all.map fun st =>
    let l := st.layout
    String.intercalate "\n" ([s!"        {camel (constName st |>.toLower)} \{"] ++ fieldDecls "            " "" l ++
      ["        },"])
  let readArms := Step.all.map fun st =>
    let l := st.layout
    String.intercalate "\n" ([s!"                {st.code} => \{"] ++
      l.map (fun f => "                    " ++ readField max f) ++
      [s!"                    {structLit "                    " ("Step::" ++ camel (constName st |>.toLower)) l}", "                }"])
  let writeArms := Step.all.map fun st =>
    let l := st.layout
    String.intercalate "\n" ([s!"                {structLit "                " ("Step::" ++ camel (constName st |>.toLower)) l} => \{",
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
def layoutModule : String := String.intercalate "\n\n" [
  "/// The follow socket's payloads (Protocol.Table layouts; Lean codec: Protocol.Frames).\npub mod layout {",
  layoutPrelude,
  structFor "Command" Bounds.argvBytesMax commandLayout,
  structFor "Resume" Bounds.frameBytesMax resumeLayout,
  stepEnum Bounds.frameBytesMax ++ "\n}"]

def header : String :=
  "// @generated from Nanodregg.Protocol (Protocol/Table.lean) by Emit/Rust.lean. DO NOT EDIT.\n" ++
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
