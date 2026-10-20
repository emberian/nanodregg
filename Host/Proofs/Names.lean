/-
# Host.Proofs.Names — every Host refusal's wire name determines its constructor (law 7)

The ROOT ruling on law 7: each refusal type has a total `name` and `name_injective` (equal names,
equal constructors), so a name on the wire is never ambiguous within its type. For `StoreFault`, whose
`base`/`seal` cases carry the inner refusal's name, equal names also force equal inner constructors.
-/
import Host.Follow
import Host.Store
import Host.Page
import Std.Data.String.ToNat

namespace Nanodregg.Host

theorem FrameRefusal.name_injective (a b : FrameRefusal) (h : a.name = b.name) : a.ctorIdx = b.ctorIdx := by
  cases a <;> cases b <;> simp_all [FrameRefusal.name] <;> rfl

theorem Follow.Refusal.name_injective (a b : Follow.Refusal) (h : a.name = b.name) :
    a.ctorIdx = b.ctorIdx := by
  cases a <;> cases b <;> simp_all [Follow.Refusal.name] <;> rfl

theorem Exit.name_injective (a b : Exit) (h : a.name = b.name) : a.ctorIdx = b.ctorIdx := by
  cases a <;> cases b <;> simp_all [Exit.name] <;> rfl

theorem SealFault.name_injective (a b : SealFault) (h : a.name = b.name) : a.ctorIdx = b.ctorIdx := by
  cases a <;> cases b <;> simp_all [SealFault.name] <;> rfl

theorem BaseFault.name_injective (a b : BaseFault) (h : a.name = b.name) : a.ctorIdx = b.ctorIdx := by
  cases a <;> cases b <;> simp_all [BaseFault.name] <;> rfl

theorem Record.Fault.name_injective {F : Type} (a b : Record.Fault F) (h : a.name = b.name) :
    a.ctorIdx = b.ctorIdx := by
  cases a <;> cases b <;> simp_all [Record.Fault.name] <;> rfl

theorem Page.Fault.name_injective (a b : Page.Fault) (h : a.name = b.name) : a.ctorIdx = b.ctorIdx := by
  cases a <;> cases b <;> simp_all [Page.Fault.name] <;> rfl

theorem StoreFault.name_injective {F : Type} (a b : StoreFault F) (h : a.name = b.name) :
    a.ctorIdx = b.ctorIdx := by
  rcases a with _ | _ | _ | _ | _ | (_ | _ | _ | _ | _ | _) | (_ | _) | (_ | _ | _ | _ | _) | _ <;>
  rcases b with _ | _ | _ | _ | _ | (_ | _ | _ | _ | _ | _) | (_ | _) | (_ | _ | _ | _ | _) | _ <;>
  simp_all [StoreFault.name, BaseFault.name, SealFault.name] <;> rfl

private theorem toList_head_append (p x : String) (c : Char) (hp : p.toList.head? = some c) :
    (p ++ x).toList.head? = some c := by
  rw [String.toList_append]
  cases hl : p.toList with
  | nil => rw [hl] at hp; cases hp
  | cons d l => rw [hl] at hp; simpa using hp

/-- The first character of a part's name: its family (`k`, `s`, `i`, `b`). -/
private theorem StorePart.name_head (p : StorePart) :
    p.name.toList.head? = some (match p with | .key => 'k' | .segment _ => 's' | .index _ => 'i' | .base => 'b') := by
  cases p with
  | key => decide
  | base => decide
  | segment o =>
    show ("seg." ++ toString o ++ ".log").toList.head? = some 's'
    rw [String.append_assoc]; exact toList_head_append _ _ _ (by decide)
  | index k =>
    show ("index." ++ toString k ++ ".log").toList.head? = some 'i'
    rw [String.append_assoc]; exact toList_head_append _ _ _ (by decide)

/-- **A part's name determines the part** (law 7, HOST-64): the family by its first character, and
a segment's start or an index file's first entry by the decimal between the family's prefix and
`.log` (`Nat.repr_injective`). So `missing seg.<o>.log` names one file. -/
theorem StorePart.name_injective (a b : StorePart) (h : a.name = b.name) : a = b := by
  have hd := congrArg (fun s => s.toList.head?) h
  simp only [StorePart.name_head] at hd
  cases a <;> cases b <;> simp at hd
  · rfl
  · rename_i o o'
    have h' : "seg." ++ toString o ++ ".log" = "seg." ++ toString o' ++ ".log" := h
    rw [String.append_left_inj, String.append_right_inj, Nat.toString_eq_repr, Nat.toString_eq_repr] at h'
    rw [Nat.repr_injective h']
  · rename_i k k'
    have h' : "index." ++ toString k ++ ".log" = "index." ++ toString k' ++ ".log" := h
    rw [String.append_left_inj, String.append_right_inj, Nat.toString_eq_repr, Nat.toString_eq_repr] at h'
    rw [Nat.repr_injective h']
  · rfl

/-- Every part `missing` can name is a family of the Store layout. -/
theorem StorePart.mem_layout (p : StorePart) : p.pattern ∈ Store.layout.map (·.name) := by
  cases p <;> simp only [StorePart.pattern] <;> decide

/-- **The families are the layout**: every Store file but the transient ones is a family, so a
check over `StorePart.families` checks every kind of file an open reads. -/
theorem StorePart.covers_layout : ∀ f ∈ Store.layout, f.kind ≠ .transient →
    f.name ∈ StorePart.families.map (·.pattern) := by
  decide

/-- A `missing` refusal's stderr text names its file: two refusals that print the same text are
missing the same file, a segment file by its start (HOST-35, HOST-64; the status, `missing`, is one
name for all of them). -/
theorem StoreFault.text_missing_injective {F : Type} (a b : StorePart)
    (h : (StoreFault.missing a : StoreFault F).text = (StoreFault.missing b : StoreFault F).text) : a = b := by
  simp only [StoreFault.text, String.append_right_inj] at h
  exact StorePart.name_injective a b h

/-- **A `pageIo` refusal is never mistaken for another** (HOST-48, law 7): the name a page whose IO
failed is refused by is none of the names a page reply otherwise carries: a page fault's (the
pager's `named f.name`), an envelope refusal's, or a frame refusal's. -/
theorem pageIoName_fresh :
    (∀ f : Page.Fault, f.name ≠ Protocol.pageIoName) ∧
      (∀ r : Protocol.ReadRefusal, r.name ≠ Protocol.pageIoName) ∧
      (∀ r : FrameRefusal, r.name ≠ Protocol.pageIoName) := by
  refine ⟨fun f => ?_, fun r => ?_, fun r => ?_⟩
  · cases f <;> simp [Page.Fault.name, Protocol.pageIoName]
  · cases r <;> simp [Protocol.ReadRefusal.name, Protocol.pageIoName]
  · cases r <;> simp [FrameRefusal.name, Protocol.pageIoName]

end Nanodregg.Host
