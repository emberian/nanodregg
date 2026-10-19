/-
# Hosting.Resident.Volume — the volume's contract, as a model (HOSTING-37)

What `keep` and `forget` trust of the filesystem, written down: one directory of names over inodes.
It is the CONTRACT, not a proof of the kernel's: the theorems of `Proofs.ResidentVolume` hold for
every filesystem that meets it, over exactly the steps `keepOps` and `forgetOps` perform.

- `create` makes a fresh inode under the name, empty; `write` sets the open inode's contents;
  both leave it unsynced. `sync` (`fsync`) marks the open inode's contents durable.
- `rename a b`, `removeIfExists`: change the live entries. Each value an entry takes is remembered
  (`hist`) until the next `syncDir` (`fsync` on the directory), which makes the live entries the
  only ones a crash can come back with.
- A crash is a RELATION (`Proofs.ResidentVolume.Crash`), not a function: each entry comes back as ANY value it held
  since the last directory sync, independently of the others (a rename's two halves too); a synced
  inode comes back with its contents; an unsynced one with ANY contents, or unreadable. Nothing
  else is assumed: no ordering between a file's data and its entry, no atomicity of rename across
  a crash beyond "the entry is one of its values".
Nothing here performs anything: the deployed exe never imports it.
-/
import Hosting.Resident.Run

namespace Nanodregg.Hosting.Resident

/-- One directory and its inodes. -/
structure Vol where
  live : System.FilePath → Option Nat
  /-- every value the entry has held since the last directory sync, the current one last -/
  hist : System.FilePath → List (Option Nat)
  data : Nat → Option String
  synced : Nat → Bool
  next : Nat
  cur : Option Nat

def upd {α β : Type} [DecidableEq α] (f : α → β) (k : α) (v : β) : α → β :=
  fun x => if x = k then v else f x

/-- Set one live entry, remembering the value. -/
def Vol.set (v : Vol) (p : System.FilePath) (x : Option Nat) : Vol :=
  { v with live := upd v.live p x, hist := upd v.hist p (v.hist p ++ [x]) }

/-- What one step does, under the contract. -/
def Vol.apply (v : Vol) : FsOp → Vol
  | .removeIfExists p => v.set p none
  | .create p =>
    let v1 := v.set p (some v.next)
    { v1 with data := upd v.data v.next (some ""), synced := upd v.synced v.next false,
              next := v.next + 1, cur := some v.next }
  | .write s => match v.cur with
    | some i => { v with data := upd v.data i (some s), synced := upd v.synced i false }
    | none => v
  | .sync => match v.cur with
    | some i => { v with synced := upd v.synced i true }
    | none => v
  | .rename a b => (v.set b (v.live a)).set a none
  | .syncDir _ => { v with hist := fun p => [v.live p] }

def Vol.applyAll (v : Vol) (ops : List FsOp) : Vol := ops.foldl Vol.apply v

/-- What `run` finds at a name: absent (`none`), or present with its contents (`none` inside:
unreadable). Exactly the three cases `seedOf` reads. -/
def Vol.read (v : Vol) (p : System.FilePath) : Option (Option String) := (v.live p).map v.data

/-- The empty volume. -/
def Vol.empty : Vol :=
  { live := fun _ => none, hist := fun _ => [none], data := fun _ => none, synced := fun _ => true,
    next := 0, cur := none }

/-- The crash outcome that keeps the live state (every entry and every contents as they are),
with `live`'s and `data`'s values replaced where a tooth needs another outcome. -/
def Vol.settle (v : Vol) (live : System.FilePath → Option Nat) (data : Nat → Option String) : Vol :=
  { v with live, hist := fun p => [live p], data, synced := fun _ => true, cur := none }

end Nanodregg.Hosting.Resident
