import Lang.Resident

open Nanodregg.Lang.Resident in
/-- `ob FORM` or `ob -f FILE`: one form, one answer line; exit 0 ok, 1 refused, 2 usage. -/
def main (args : List String) : IO UInt32 := do
  let text : Option (Option String) ← match args with
    | ["-f", path] => do
      let m ← System.FilePath.metadata path
      if m.byteSize.toNat > inputMax then pure (some none) else pure (some (some (← IO.FS.readFile path)))
    | [form] => pure (some (some form))
    | _ => pure none
  match text with
  | none =>
    IO.eprintln "usage: ob FORM | ob -f FILE   (one form: check bytes type eval law)"
    return 2
  | some none =>
    IO.println s!"refused tooLarge (over {inputMax} bytes)"
    return 1
  | some (some t) =>
    let a := run t
    IO.println a.line
    return if a.refused then 1 else 0
