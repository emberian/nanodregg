/-
# nanodregg — the one build (owner: BUILD-GATES; every layer adds its own `lean_lib`).

The file is a table, not a program: gates/tree.py reads it with a strict grammar and refuses any
top-level form it does not know (closure C0). The forms are
  * `package nanodregg where leanOptions := …` — warnings are errors, no auto-bound implicits;
  * `@[default_target] lean_lib X where globs := #[.submodules `X]` — one per layer directory,
    every file in X/ built, no umbrella module, no orphan (C1);
  * `@[default_target] lean_exe «name» where root := `M` — M holds only `main` (C7);
  * `extern_lib «ndhost»` — every Host/c/*.c, cc -Wall -Wextra -Werror, into libndhost.a. The only
    C in the tree; built from source, never a prebuilt object (ROOT ruling 2026-10-16).
No packages: Lean core and Std only (decisions/gates.md GATES-1). A bare `lake build` builds
every target, so it can never succeed by building nothing.
-/
import Lake
open Lake DSL System

package nanodregg where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`warningAsError, true⟩]

-- The axiom census command (Census.Axioms): build tooling, the only place `import Lean` is
-- allowed; nothing outside Census may import it (gates/closure.py C2, C5).
@[default_target] lean_lib Census where
  globs := #[.submodules `Census]

@[default_target] lean_lib Kernel where
  globs := #[.submodules `Kernel]

@[default_target] lean_lib Protocol where
  globs := #[.submodules `Protocol]

@[default_target] lean_lib Host where
  globs := #[.submodules `Host]

@[default_target] lean_lib Lang where
  globs := #[.submodules `Lang]

@[default_target] lean_lib Codec where
  globs := #[.submodules `Codec]

-- The Rust copy of the protocol table (client/src/generated.rs). Imports Protocol; nothing imports it.
@[default_target] lean_lib Emit where
  globs := #[.submodules `Emit]

@[default_target] lean_exe «emit-rust» where
  root := `Emit.Main

-- KERNEL's seeded simulation: `kernel-sim SEED…` (or `--seeds N`), ends `ALL PASS` (standing.sh).
@[default_target] lean_exe «kernel-sim» where
  root := `Kernel.Sim.Main

-- LANG's first law end to end: install → create → invoke through KERNEL's receivers.
@[default_target] lean_exe «lang-journey» where
  root := `Lang.Journey.Main

-- Host/c/*.c: the Store's physical IO (Host.File's externs). Sorted, so the archive is reproducible.
extern_lib «ndhost» pkg := do
  let dir := pkg.dir / "Host" / "c"
  let srcs := (← dir.readDir).filter (·.path.extension == some "c") |>.map (·.path)
    |>.qsort (·.toString < ·.toString)
  let leanInc := (← getLeanIncludeDir).toString
  let objs ← srcs.mapM fun src => do
    let o := pkg.buildDir / "c" / ((src.withExtension "o").fileName.getD "x.o")
    buildO o (← inputTextFile src) #["-I", leanInc] #["-fPIC", "-O2", "-Wall", "-Wextra", "-Werror"]
      "cc" getLeanTrace
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "ndhost") objs

-- The Host's loop end to end over the in-memory disk, with the crash plants (standing: seeds 1 2 3).
@[default_target] lean_exe «host-sim» where
  root := `Host.Sim.Main
