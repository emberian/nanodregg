import Protocol.Table
import Protocol.Attempt
import Protocol.Exit
import Protocol.Envelope
import Protocol.Command.Stdio
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

/-- Greedy packing of `items` into lines of at most `width` characters, each `indent ++ a, b, …,`:
rustfmt's layout for an array of short literals. -/
def packLines (indent : String) (width : Nat) (items : List String) : List String :=
  let close (cur : List String) := indent ++ ", ".intercalate cur.reverse ++ ","
  let (lines, cur) := items.foldl (fun (acc : List String × List String) it =>
    let (lines, cur) := acc
    if cur.isEmpty then (lines, [it])
    else if (close (it :: cur)).length ≤ width then (lines, it :: cur)
    else (close cur :: lines, [it])) ([], [])
  (if cur.isEmpty then lines else close cur :: lines).reverse

/-- One `pub const NAME: u8 = n;` line per value. -/
def byteConsts {α : Type} [Repr α] (values : List α) (code : α → UInt8) : List String :=
  values.map fun v => s!"    pub const {constName v}: u8 = {code v};"

/-- `pub const ALL: &[u8]`, every value's code in `values` order, laid out as rustfmt lays it out
inside a module: a table's membership list, so a reader can tell a code the table names from one it
does not (HOSTING-23; CODEC-7: one mechanism, so no table exists without its list). -/
def byteAll {α : Type} (values : List α) (code : α → UInt8) : List String :=
  let items := values.map fun v => toString (code v)
  let head := "    pub const ALL: &[u8] = &["
  let one := head ++ ", ".intercalate items ++ "];"
  -- rustfmt keeps an array on one line only within its `array_width` (60) and the line width
  if ("[" ++ ", ".intercalate items ++ "]").length ≤ 60 && one.length ≤ 100 then [one]
  else [head] ++ packLines "        " 100 items ++ ["    ];"]

/-- A `pub mod` of byte constants, and their membership list `ALL`. -/
def byteModule {α : Type} [Repr α] (name : String) (values : List α) (code : α → UInt8) : String :=
  String.intercalate "\n" ([s!"pub mod {name} \{"] ++ byteConsts values code ++ byteAll values code ++ ["}"])

/-- A `pub const NAME: &[&str]` holding `ws`, laid out as rustfmt lays it out. -/
def rustStrsConst (name : String) (ws : List String) : String :=
  let head := s!"pub const {name}: &[&str] = &["
  let items := ws.map fun w => "\"" ++ w ++ "\""
  let one := head ++ ", ".intercalate items ++ "];"
  if one.length ≤ 100 then one
  else String.intercalate "\n" ([head] ++ packLines "    " 100 items ++ ["];"])

/-- `StdioRefusal` as a Rust enum: its code and its Lean name. -/
def stdioRefusalEnum : String :=
  String.intercalate "\n" (
    ["/// Why `nd --stdio` refuses a request before follow sees it (Protocol.StdioRefusal).",
     "#[derive(Debug, Clone, Copy, PartialEq, Eq)]", "pub enum StdioRefusal {"] ++
    StdioRefusal.all.map (fun r => s!"    {ctorName r},") ++
    ["}", "", "impl StdioRefusal {", "    pub fn code(self) -> u8 {", "        match self {"] ++
    StdioRefusal.all.map (fun r => s!"            StdioRefusal::{ctorName r} => {r.code},") ++
    ["        }", "    }", "", "    pub fn name(self) -> &'static str {", "        match self {"] ++
    StdioRefusal.all.map (fun r => s!"            StdioRefusal::{ctorName r} => \"{r.name}\",") ++
    ["        }", "    }", "}"])

/-- A `pub const NAME: &[u8]` holding `b` as a byte list, laid out as rustfmt lays it out. -/
def rustByteConst (name : String) (b : ByteArray) : String :=
  let head := s!"pub const {name}: &[u8] = &["
  let one := head ++ ", ".intercalate (b.toList.map toString) ++ "];"
  if one.length ≤ 100 then one
  else String.intercalate "\n" ([head] ++ packLines "    " 100 (b.toList.map toString) ++ ["];"])

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

/-- The Rust type of a `oneOf` field: by default the enum the layout module emits for it
(`camel name`); a layout whose cases are a Lean enum emitted elsewhere names that enum instead. -/
abbrev OneOfType := String → String

/-- A Lean field name as a Rust identifier: `atMs` ↦ `at_ms` (rustc's `non_snake_case`). -/
def snake (s : String) : String :=
  String.ofList (s.toList.flatMap fun c => if c.isUpper then ['_', c.toLower] else [c])

def rustType (ty : OneOfType := camel) : Field → String
  | .byte _ => "u8"
  | .u64 _ => "u64"
  | .bytes _ => "Vec<u8>"
  | .list _ => "Vec<Vec<u8>>"
  | .oneOf n _ => ty n
  | .u32 _ => "u32"
  | .path _ => "Vec<u8>"
  | .paths _ => "Vec<Vec<u8>>"

def readField (max : Nat) (f : Field) (ty : OneOfType := camel) : String :=
  match f with
  | .byte n => s!"let {snake n} = c.byte()?;"
  | .u64 n => s!"let {snake n} = c.u64()?;"
  | .bytes n => s!"let {snake n} = c.bytes({max})?;"
  | .list n => s!"let {snake n} = c.list({max})?;"
  | .oneOf n _ => s!"let {snake n} = c.one_of({ty n}::from_code)?;"
  | .u32 n => s!"let {snake n} = c.u32()? as u32;"
  | .path n => s!"let {snake n} = c.path({max})?;"
  | .paths n => s!"let {snake n} = c.paths({max})?;"

def writeField (max : Nat) : Field → String
  | .byte n => s!"out.push(*{snake n});"
  | .u64 n => s!"out.extend_from_slice(&{snake n}.to_le_bytes());"
  | .bytes n => s!"put_bytes(&mut out, {snake n}, {max})?;"
  | .list n => s!"put_list(&mut out, {snake n}, {max})?;"
  | .oneOf n _ => s!"out.push({snake n}.code());"
  | .u32 n => s!"out.extend_from_slice(&{snake n}.to_le_bytes());"
  | .path n => s!"put_path(&mut out, {snake n}, {max})?;"
  | .paths n => s!"put_paths(&mut out, {snake n}, {max})?;"

def fieldNames (l : Layout) : String := String.intercalate ", " (l.map fun f => snake f.name)

/-- `Name { a, b }`, or one field per line when the fields are wider than rustfmt's
`struct_lit_width` (18), so the emitted file is already `cargo fmt` clean. -/
def structLit (indent name : String) (l : Layout) : String :=
  if (fieldNames l).length ≤ 18 then s!"{name} \{ {fieldNames l} }"
  else String.intercalate "\n" ([s!"{name} \{"] ++ l.map (fun f => s!"{indent}    {snake f.name},") ++ [s!"{indent}}"])

def fieldDecls (indent vis : String) (l : Layout) (ty : OneOfType := camel) : List String :=
  l.map fun f => s!"{indent}{vis}{snake f.name}: {rustType ty f},"

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
    ["                _ => None,", "            }", "        }", "",
     "        /// The Lean name of the case.", "        pub fn name(self) -> &'static str {", "            match self {"] ++
    cases.map (fun c => s!"                {ty}::{camel c.1} => \"{c.1}\",") ++
    ["            }", "        }", "    }"]

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
def structFor (name : String) (max : Nat) (l : Layout) (total : Option Nat := none) (ty : OneOfType := camel) : String :=
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
    [s!"    #[derive(Debug, Clone, PartialEq, Eq)]", s!"    pub struct {name} \{"] ++ fieldDecls "        " "pub " l ty ++
    ["    }", "", s!"    impl {name} \{",
     "        pub fn decode(b: &[u8]) -> Result<Self, Refusal> {",
     "            let mut c = Cursor { b, i: 0 };"] ++
    l.map (fun f => "            " ++ readField max f ty) ++ totalRead ++
    ["            c.end()?;", s!"            Ok({structLit "            " name l})", "        }", "",
     "        pub fn encode(&self) -> Result<Vec<u8>, Refusal> {",
     "            let mut out = Vec::new();",
     s!"            let {structLit "            " name l} = self;"] ++
    l.map (fun f => "            " ++ writeField max f) ++ totalWrite ++
    ["            Ok(out)", "        }", "    }"]

/-- A Rust enum for a tagged frame (`Codec.Tagged`): one variant per case, the tag byte, then the case's
fields; an unknown tag is `BadTag` at its offset. `name` is the enum, `cases` (variant, code, layout). -/
def taggedEnum (name : String) (max : Nat) (cases : List (String × UInt8 × Layout)) : String :=
  let var := String.ofList (name.toList.map Char.toLower)
  -- rustfmt's layout: when every struct variant's `{ fields }` body fits `struct_variant_width` (35),
  -- each is one line; if any does not, all are vertical
  let body (l : Layout) := "{ " ++ String.intercalate ", " (l.map fun f => s!"{snake f.name}: {rustType camel f}") ++ " }"
  let short := cases.all fun (_, _, l) => !l.isEmpty && (body l).length ≤ 35
  let variants := cases.map fun (v, _, l) =>
    if short then s!"        {camel v} {body l},"
    else String.intercalate "\n" ([s!"        {camel v} \{"] ++ fieldDecls "            " "" l ++ ["        },"])
  let readArms := cases.map fun (v, code, l) =>
    String.intercalate "\n" ([s!"                {code} => \{"] ++
      l.map (fun f => "                    " ++ readField max f) ++
      [s!"                    {structLit "                    " (name ++ "::" ++ camel v) l}", "                }"])
  let writeArms := cases.map fun (v, code, l) =>
    String.intercalate "\n" ([s!"                {structLit "                " (name ++ "::" ++ camel v) l} => \{",
      s!"                    out.push({code});"] ++
      l.map (fun f => "                    " ++ writeField max f) ++ ["                }"])
  String.intercalate "\n" <|
    ["    #[derive(Debug, Clone, PartialEq, Eq)]", s!"    pub enum {name} \{"] ++ variants ++ ["    }", "",
     s!"    impl {name} \{",
     "        pub fn decode(b: &[u8]) -> Result<Self, Refusal> {",
     "            let mut c = Cursor { b, i: 0 };",
     "            let at = c.i;",
     s!"            let {var} = match c.byte()? \{"] ++ readArms ++
    ["                tag => return Err(Refusal::BadTag { offset: at, tag }),",
     "            };", "            c.end()?;", s!"            Ok({var})", "        }", "",
     "        pub fn encode(&self) -> Result<Vec<u8>, Refusal> {",
     "            let mut out = Vec::new();", "            match self {"] ++ writeArms ++
    ["            }", "            Ok(out)", "        }", "    }"]

/-- The tagged step frame. -/
def stepEnum (max : Nat) : String :=
  taggedEnum "Step" max (Step.all.map fun st => (ctorName st, st.code, st.layout))

/-- The cursor and writers every layout shares: `Codec.Stream`'s u8, u32le, bytesOf and array. -/
def layoutPrelude (rejected : Bool := false) (lists : Bool := true) : String := String.intercalate "\n" ([
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
  "        },"] ++
  (if rejected then ["        Rejected {", "            offset: usize,", "            name: &'static str,", "        },"]
   else []) ++ [
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
  "        }"] ++ (if lists then [
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
  "        }"] else []) ++ [
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
  "    }"] ++ (if lists then [
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
  "    }"] else []))

/-- A Rust byte-string literal of `w`: printable ASCII as itself, `"` and `\\` escaped, any other byte `\\xNN`. -/
def rustBytes (w : ByteArray) : String :=
  let hex (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  "b\"" ++ String.ofList (w.toList.flatMap fun b =>
    let n := b.toNat
    if n == 34 || n == 92 then ['\\', Char.ofNat n]
    else if 32 ≤ n && n < 127 then [Char.ofNat n]
    else ['\\', 'x', hex (n / 16), hex (n % 16)]) ++ "\""

/-- The paths `PATH_VECTORS` carries: every clause of `Path.clean` and of the split (empty path, leading,
trailing and doubled separators, `.`/`..` alone and inside, the length edge, NUL, a backslash). -/
def pathVectors : List ByteArray :=
  (["", "a", "a/b", "/a", "a/", "a//b", ".", "..", "a/./b", "a/../b", "...", ".a", "a.", "a\\b",
    String.ofList (List.replicate Path.componentMax 'x'),
    String.ofList (List.replicate (Path.componentMax + 1) 'x'),
    String.ofList (List.replicate Path.componentMax 'x') ++ "/b"]).map String.toUTF8 ++
  -- NUL inside a component, as bytes: the compiled emitter misprints a `\x00` string literal followed
  -- by a hex digit (Lean's C string escape runs on), so the vector is built from its bytes
  [ByteArray.mk #[97, 0, 98]]

/-- One row: the path and the verdict of Lean's path decoder on its components
(`(Path.split v).all Path.clean`; `Codec.Proofs.Path.fits_split` is the decoder's whole condition). -/
def pathVectorRow (v : ByteArray) : String :=
  let one := s!"({rustBytes v}, {(Path.split v).all Path.clean})"
  -- rustfmt's layout: a tuple wider than `fn_call_width` (60) is one element per line
  if one.length ≤ 60 then s!"        {one},"
  else s!"        (\n            {rustBytes v},\n            {(Path.split v).all Path.clean},\n        ),"

/-- The cursor's and writer's path fields (`Codec.Path`), emitted only when some layout has one: the
same rule as `Path.clean` printed from its constants, the same refusal name at the same offset. -/
def pathSupport : String :=
  let lit := rustBytes
  String.intercalate "\n" ([
  s!"    const SEP: u8 = {Path.sep};",
  s!"    const NUL: u8 = {Path.nul};",
  s!"    const COMPONENT_MAX: usize = {Path.componentMax};",
  s!"    const RESERVED: [&[u8]; 2] = [{lit Path.dot}, {lit Path.dotdot}];",
  "",
  "    /// Codec.Path: the empty path, or components separated by SEP, each clean.",
  "    pub fn path_clean(v: &[u8]) -> bool {",
  "        v.is_empty()",
  "            || v.split(|b| *b == SEP).all(|c| {",
  "                !c.is_empty()",
  "                    && c.len() <= COMPONENT_MAX",
  "                    && !RESERVED.contains(&c)",
  "                    && !c.iter().any(|b| *b == SEP || *b == NUL)",
  "            })",
  "    }",
  "",
  "    impl Cursor<'_> {",
  "        fn path(&mut self, max: usize) -> Result<Vec<u8>, Refusal> {",
  "            let at = self.i;",
  "            let v = self.bytes(max)?;",
  "            if path_clean(&v) {",
  "                Ok(v)",
  "            } else {",
  "                Err(Refusal::Rejected {",
  "                    offset: at,",
  "                    name: \"path/badComponent\",",
  "                })",
  "            }",
  "        }",
  "        fn paths(&mut self, max: usize) -> Result<Vec<Vec<u8>>, Refusal> {",
  "            let at = self.i;",
  "            let n = self.u32()?;",
  "            if n > max {",
  "                return Err(Refusal::PastBound {",
  "                    offset: at,",
  "                    limit: max,",
  "                    got: n,",
  "                });",
  "            }",
  "            (0..n).map(|_| self.path(max)).collect()",
  "        }",
  "    }",
  "",
  "    fn put_path(out: &mut Vec<u8>, v: &[u8], max: usize) -> Result<(), Refusal> {",
  "        if !path_clean(v) {",
  "            return Err(Refusal::Rejected {",
  "                offset: out.len(),",
  "                name: \"path/badComponent\",",
  "            });",
  "        }",
  "        put_bytes(out, v, max)",
  "    }",
  "",
  "    fn put_paths(out: &mut Vec<u8>, v: &[Vec<u8>], max: usize) -> Result<(), Refusal> {",
  "        if v.len() > max {",
  "            return Err(Refusal::PastBound {",
  "                offset: out.len(),",
  "                limit: max,",
  "                got: v.len(),",
  "            });",
  "        }",
  "        out.extend_from_slice(&(v.len() as u32).to_le_bytes());",
  "        v.iter().try_for_each(|x| put_path(out, x, max))",
  "    }",
  "",
  "    /// Paths with the verdict Lean's decoder gives them (`Path.split`, then `Path.clean` on each",
  "    /// component), evaluated by the emitter; `tests/path_vectors.rs` checks `path_clean` against them.",
  "    pub const PATH_VECTORS: &[(&[u8], bool)] = &["] ++ pathVectors.map pathVectorRow ++ ["    ];"])

/-- The pipe framing for a tagged file (`u32le len ‖ payload`, `1 ≤ len ≤ FRAME_MAX`), with the end of
the stream at a boundary (`End`) told apart from one inside a frame (`Torn`); emitted only by
`taggedFile`, whose bounds must name `FRAME_MAX`. -/
def frameIo : String := String.intercalate "\n" [
  "/// Why a frame could not be read or written (the pipe framing: `u32le len ‖ payload`,",
  "/// `1 <= len <= FRAME_MAX`).",
  "#[derive(Debug)]",
  "pub enum FrameError {",
  "    /// The stream ended at a frame boundary.",
  "    End,",
  "    /// The stream ended inside a frame.",
  "    Torn,",
  "    /// A frame of length 0.",
  "    Empty,",
  "    /// A frame longer than `FRAME_MAX`.",
  "    TooLong {",
  "        len: usize,",
  "    },",
  "    Io(std::io::Error),",
  "}",
  "",
  "/// Fill `buf` from `r`; the number of bytes read before the end of the stream.",
  "fn read_full(r: &mut impl std::io::Read, buf: &mut [u8]) -> Result<usize, FrameError> {",
  "    let mut n = 0;",
  "    while n < buf.len() {",
  "        match r.read(&mut buf[n..]) {",
  "            Ok(0) => return Ok(n),",
  "            Ok(k) => n += k,",
  "            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}",
  "            Err(e) => return Err(FrameError::Io(e)),",
  "        }",
  "    }",
  "    Ok(n)",
  "}",
  "",
  "/// Read one frame's payload.",
  "pub fn read_frame(r: &mut impl std::io::Read) -> Result<Vec<u8>, FrameError> {",
  "    let mut len = [0u8; 4];",
  "    match read_full(r, &mut len)? {",
  "        0 => return Err(FrameError::End),",
  "        4 => {}",
  "        _ => return Err(FrameError::Torn),",
  "    }",
  "    let len = u32::from_le_bytes(len) as usize;",
  "    if len == 0 {",
  "        return Err(FrameError::Empty);",
  "    }",
  "    if len > FRAME_MAX as usize {",
  "        return Err(FrameError::TooLong { len });",
  "    }",
  "    let mut payload = vec![0u8; len];",
  "    if read_full(r, &mut payload)? != len {",
  "        return Err(FrameError::Torn);",
  "    }",
  "    Ok(payload)",
  "}",
  "",
  "/// Write one frame.",
  "pub fn write_frame(w: &mut impl std::io::Write, payload: &[u8]) -> Result<(), FrameError> {",
  "    if payload.is_empty() {",
  "        return Err(FrameError::Empty);",
  "    }",
  "    if payload.len() > FRAME_MAX as usize {",
  "        return Err(FrameError::TooLong { len: payload.len() });",
  "    }",
  "    w.write_all(&(payload.len() as u32).to_le_bytes())",
  "        .and_then(|()| w.write_all(payload))",
  "        .map_err(FrameError::Io)",
  "}"
  ]

/-- A generated file for two tagged frame families (one per direction), their bounds, and the
shared cursor: HOSTING's controller ↔ launcher boundary. `title` names the Lean source. -/
def taggedFile (title : String) (bounds : List (String × Nat)) (max : Nat)
    (families : List (String × Tagged)) : Except String String := do
  let consts ← bounds.mapM u32Const
  let ls := families.flatMap fun (_, cs) => cs.map (·.2.2)
  let has (p : Field → Bool) := ls.flatten.any p
  let hasPath := has fun | .path _ | .paths _ => true | _ => false
  let hasU64 := has fun | .u64 _ => true | _ => false
  let hasList := has fun | .list _ => true | _ => false
  let es := oneOfs ls
  -- every oneOf name names one case list, and no emitted type: a second list under one name would be
  -- dropped by `oneOfs`, and a clash with a type would not compile
  let all := ls.flatten.filterMap fun | .oneOf n cs => some (n, cs) | _ => none
  for (n, cs) in all do
    if all.any (fun (m, ds) => m == n && ds != cs) then
      throw s!"oneOf field {n} names two different case lists; rename one"
    if (["Refusal", "Cursor"] ++ families.map (·.1)).contains (camel n) then
      throw s!"oneOf field {n} becomes the Rust type {camel n}, which the file already defines; rename it"
  unless bounds.any (·.1 == "FRAME_MAX") do throw "a tagged file needs a FRAME_MAX bound for its framing"
  pure <| String.intercalate "\n\n" ([
    s!"// GENERATED by emit-rust from {title} — do not edit",
    String.intercalate "\n" consts,
    frameIo,
    "/// The frames (Lean codec: Codec.Tagged over the same layouts).\npub mod wire {",
    layoutPrelude hasPath hasList] ++
    (if es.isEmpty then [] else [oneOfReader]) ++ (if hasU64 then [u64Reader] else []) ++
    (if hasPath then [pathSupport] else []) ++
    es.map (fun p => oneOfEnum p.1 p.2) ++
    (match (families.map fun (n, cs) => taggedEnum n max cs).reverse with
     | [] => ["}"]
     | e :: rest => rest.reverse ++ [e ++ "\n}"])) ++ "\n"

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
  structFor "CustodyRefused" Bounds.frameBytesMax custodyRefusalLayout (ty := fun _ => "super::CustodyRefusal"),
  structFor "CommandReply" Bounds.frameBytesMax commandReplyLayout,
  stepEnum Bounds.frameBytesMax ++ "\n}"])

/-- `CustodyRefusal` as a Rust enum: the code on the wire (`layout::CustodyRefused`'s one byte), the
inverse, and the Lean name the follow renders. Its cases are `CustodyRefusal.all`, the same list
`custodyRefusalLayout`'s cases are read from, so the enum and the layout cannot disagree. -/
def custodyRefusalEnum : String :=
  String.intercalate "\n" (
    ["/// Why custody refused a step (Protocol.CustodyRefusal).",
     "#[derive(Debug, Clone, Copy, PartialEq, Eq)]", "pub enum CustodyRefusal {"] ++
    CustodyRefusal.all.map (fun r => s!"    {ctorName r},") ++
    ["}", "", "impl CustodyRefusal {", "    pub fn code(self) -> u8 {", "        match self {"] ++
    CustodyRefusal.all.map (fun r => s!"            CustodyRefusal::{ctorName r} => {r.code},") ++
    ["        }", "    }", "", "    pub fn from_code(b: u8) -> Option<Self> {", "        match b {"] ++
    CustodyRefusal.all.map (fun r => s!"            {r.code} => Some(CustodyRefusal::{ctorName r}),") ++
    ["            _ => None,", "        }", "    }", "", "    pub fn name(self) -> &'static str {", "        match self {"] ++
    CustodyRefusal.all.map (fun r => s!"            CustodyRefusal::{ctorName r} => \"{r.name}\",") ++
    ["        }", "    }", "}"])

/-! ## The attempt store's decision (Protocol.Attempt)

`attempt::next` is `Attempt.table` printed as one Rust `match`, one arm per row: the client consults
it and keeps no second copy of the rule. The 22 rows are every input (`Attempt.inputs`), so the
`match` is exhaustive and `cargo check` refuses it if a row were missing. -/

open Attempt in
def attemptRow (row : (Bool × Option (Request × Seen)) × Action) : String :=
  let last := match row.1.2 with
    | none => "None"
    | some (r, s) => s!"Some((Request::{ctorName r}, Seen::{ctorName s}))"
  s!"            ({row.1.1}, {last}) => Action::{ctorName row.2},"

open Attempt in
def attemptModule : String :=
  let enum (name : String) (cases : List String) : List String :=
    ["    #[derive(Debug, Clone, Copy, PartialEq, Eq)]", s!"    pub enum {name} \{"] ++
      cases.map (fun c => s!"        {c},") ++ ["    }"]
  let actions : List Action := [.submit, .lookup, .committed, .refused, .absent, .badReply, .uncertain]
  String.intercalate "\n" (
    ["/// What the attempt store does next with a frozen call (Protocol.Attempt.next, as its table).",
     "pub mod attempt {"] ++
    enum "Request" (Request.all.map ctorName) ++ [""] ++
    enum "Seen" (Seen.all.map ctorName) ++ [""] ++
    enum "Action" (actions.map ctorName) ++
    ["", "    impl Action {", "        pub fn name(self) -> &'static str {", "            match self {"] ++
    actions.map (fun a => s!"                Action::{ctorName a} => \"{a.name}\",") ++
    ["            }", "        }", "    }", "",
     "    /// `sends_left` is `sends < SENDS_MAX`; `last` is the last request and what its reply said.",
     "    pub fn next(sends_left: bool, last: Option<(Request, Seen)>) -> Action {",
     "        match (sends_left, last) {"] ++
    table.map attemptRow ++
    ["        }", "    }", "}"])

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
     s!"/// The child wire's hang-up byte (Protocol.hangupCode): connection ended, payload = its CloseReason name.\npub const HANGUP: u8 = {hangupCode};",
     custodyRefusalEnum,
     byteModule "step" Step.all Step.code,
     byteModule "supervisor_exit" SupervisorExit.all (fun s => s.code.toUInt8),
     byteModule "command_exit" CommandExit.all (fun c => c.code.toUInt8),
     "/// The read envelope's signing domain (Protocol.domEnvelope): an observer custody signs only\n" ++
       "/// messages that begin with it (HOSTING-17 §7, CLIENT-22).\n" ++
       rustByteConst "ENVELOPE_DOMAIN" domEnvelope,
     "/// The verbs a hosted resident may run through `nd --stdio` (Protocol.Command.stdioVerbs).\n" ++
       rustStrsConst "STDIO_VERBS" Command.stdioWords,
     stdioRefusalEnum,
     layoutModule,
     attemptModule] ++ "\n"

/-- `EXE PATH` writes the file; `EXE --check PATH` exits 1 if PATH differs. -/
def runWith (exe : String) (file : Except String String) (args : List String) : IO UInt32 := do
  match file with
  | .error e => IO.eprintln s!"{exe}: {e}"; return 2
  | .ok text =>
    match args with
    | [path] => IO.FS.writeFile path text; return 0
    | ["--check", path] =>
      let current ← IO.FS.readFile path
      if current == text then return 0
      IO.eprintln s!"{exe}: {path} differs from the table; regenerate it"
      return 1
    | _ => IO.eprintln s!"usage: {exe} [--check] PATH"; return 2

/-- `emit-rust PATH` writes client/src/generated.rs; `--check` compares. -/
def run (args : List String) : IO UInt32 := runWith "emit-rust" file args

end Nanodregg.Emit.Rust
