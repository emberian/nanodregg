import Protocol.Table

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
     byteModule "step" Step.all Step.code] ++ "\n"

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
