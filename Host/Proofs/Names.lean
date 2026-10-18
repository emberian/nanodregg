/-
# Host.Proofs.Names — every Host refusal's wire name determines its constructor (law 7)

The ROOT ruling on law 7: each refusal type has a total `name` and `name_injective` (equal names,
equal constructors), so a name on the wire is never ambiguous within its type. For `StoreFault`, whose
`base`/`seal` cases carry the inner refusal's name, equal names also force equal inner constructors.
-/
import Host.Follow
import Host.Store
import Host.Page

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

theorem StorePart.name_injective (a b : StorePart) (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [StorePart.name] at h)

theorem StorePart.mem_all (p : StorePart) : p ∈ StorePart.all := by
  cases p <;> decide

/-- Every part `missing` can name is a file of the Store layout. -/
theorem StorePart.mem_layout (p : StorePart) : p.name ∈ Store.layout.map (·.name) := by
  cases p <;> decide

/-- **The parts are the layout**: every Store file but the transient `base.tmp` is a part, so a
check over `StorePart.all` (what `openWriter` makes) checks every file an open reads. -/
theorem StorePart.covers_layout : ∀ f ∈ Store.layout, f.kind ≠ .transient → f.name ∈ StorePart.all.map (·.name) := by
  decide

/-- A `missing` refusal's stderr text names its file: two refusals that print the same text are
missing the same file (HOST-35; the status, `missing`, is one name for all four). -/
theorem StoreFault.text_missing_injective {F : Type} (a b : StorePart)
    (h : (StoreFault.missing a : StoreFault F).text = (StoreFault.missing b : StoreFault F).text) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [StoreFault.text, StorePart.name] at h)

/-- **A `pageIo` refusal is never mistaken for another** (HOST-48, law 7): the name a page whose IO
failed is refused by is none of the names a page reply otherwise carries: a page fault's (the
pager's `named f.name`), an envelope refusal's, or a frame refusal's. -/
theorem pageIoName_fresh :
    (∀ f : Page.Fault, f.name ≠ pageIoName) ∧ (∀ r : Protocol.ReadRefusal, r.name ≠ pageIoName) ∧
      (∀ r : FrameRefusal, r.name ≠ pageIoName) := by
  refine ⟨fun f => ?_, fun r => ?_, fun r => ?_⟩
  · cases f <;> simp [Page.Fault.name, pageIoName]
  · cases r <;> simp [Protocol.ReadRefusal.name, pageIoName]
  · cases r <;> simp [FrameRefusal.name, pageIoName]

end Nanodregg.Host
