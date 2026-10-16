/-
# Kernel.Check — the fail-closed combinators `World.admit` is written in

Structural recursion only, so every lemma about them is a short induction (Kernel.Proofs.Check).
-/
import Std.Data.TreeSet

namespace Nanodregg.Kernel

/-- Pass when `b`, refuse with `e` otherwise. -/
def req {ε : Type} (b : Bool) (e : ε) : Except ε Unit :=
  if b then .ok () else .error e

/-- Run a check on every element, stopping at the first refusal. -/
def forEx {α ε : Type} (f : α → Except ε Unit) : List α → Except ε Unit
  | [] => .ok ()
  | a :: rest =>
      match f a with
      | .ok () => forEx f rest
      | .error e => .error e

/-- Map a fallible function, stopping at the first refusal. -/
def mapEx {α β ε : Type} (f : α → Except ε β) : List α → Except ε (List β)
  | [] => .ok []
  | a :: rest =>
      match f a with
      | .ok b =>
          match mapEx f rest with
          | .ok bs => .ok (b :: bs)
          | .error e => .error e
      | .error e => .error e

/-- The first element that occurs earlier in the list, found in O(n log n). -/
def firstDup {α : Type} [Ord α] (l : List α) : Option α :=
  go Std.TreeSet.empty l
where
  go (seen : Std.TreeSet α compare) : List α → Option α
    | [] => none
    | a :: rest => if seen.contains a then some a else go (seen.insert a) rest

end Nanodregg.Kernel
