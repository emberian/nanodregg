# proposals/lang.md — what LANG takes from KERNEL and CODEC, and what it gives (BUILD-LANG)

Real signatures. Committed modules are cited by path; everything here builds on main.

## From KERNEL (committed at a6101cb, consumed as is — decisions/lang.md LANG-9, LANG-11, LANG-12)

`Kernel/Receive/Call.lean`:

```lean
abbrev Pinned (D : Type) := D → Except (Refusal D) (Option Cell)
structure Req (D : Type) where agent : D; principal : D
structure Program (D : Type) where
  checkInstall : Pinned D → ByteArray → Except (Refusal D) Unit
  judge : Pinned D → (pkg : Option D) → (laws : List D) → (old new : Slots) → Req D →
    Except (Refusal D) Unit
  run : Pinned D → (pkg : D) → (state : Slots) → (method : Nat) → (args : ByteArray) → Req D →
    (budget : Nat) → Except (Refusal D) Slots
-- refusals LANG produces: lawDenied (law : D) (reason : String), program (reason : String),
-- and, through readKind, unpinned / missingCell / wrongKind / malformedCell
```

Package id = `romIdOf` of `{kind := kindPackage, discipline := .rom, slots := [(0, bytes)]}`;
object state at `stateBase + i`.

**Asks of KERNEL (open):**
1. `Kernel/Sim.lean` declares a root-level `def main`, so no module that imports `Kernel.Sim` can be
   an exe root (`Lang.Journey` needs the Sim's toy `Ctx`). Move it to `Kernel/Sim/Main.lean`
   (main-only, as gate C7 wants for every exe).
2. `judge` has no budget: LANG runs each law under the consensus constant `Lang.lawTicks` (100,000).
   If laws should be paid for by the invoker, `judge` needs the remaining budget from `run`.
3. `Req` has no height: no law can say "not before height h". Adding `height : Nat` costs one field.

## Given to KERNEL (`Lang/Program.lean`, built)

```lean
def Nanodregg.Lang.program {D : Type} [DecidableEq D]
    (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D) : Kernel.Receive.Program D
```

The deployed `Ctx` sets `program := Lang.program env.bytes digestOf`. Every read is through the
`Pinned` view, so a call must pin the object, its package, every package of the closure and every
extra law package. The first law end to end is `Lang/Journey.lean` (rows L1–L7 + a skip-judge plant,
GREEN on the Sim's toy parameters).

## From CODEC (asked)

`Codec.Stream`/`Shape` has no recursive combinator, so `Lang/Wire.lean` is a recursive codec beside
the family (decisions/lang.md LANG-14 — a defect by law 1 until this lands). Proposed:

```lean
-- Shape gains a recursion point and a variable:
| mu (name : String) (body : Shape) | recVar (name : String)
-- and a depth-bounded fixpoint combinator, with the canonicity theorem proved once:
def Stream.fix (name : String) (depthMax : Nat) (f : Stream α → Stream α) : Stream α
```

With it, `Ty`, `Term`, `Data` (type-directed: a `Stream Data` per `Ty`) and `Package` become
`Stream`s with derived tags, and `Lang/Wire.lean` keeps only the instances. Until then LANG owns the
round-trip/canonicity theorems for `Lang/Wire.lean` (not yet written: `cv task`).
