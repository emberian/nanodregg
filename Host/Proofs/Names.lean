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
  rcases a with _ | _ | _ | _ | (_ | _ | _ | _ | _ | _) | (_ | _) | (_ | _ | _) | _ <;>
  rcases b with _ | _ | _ | _ | (_ | _ | _ | _ | _ | _) | (_ | _) | (_ | _ | _) | _ <;>
  simp_all [StoreFault.name, BaseFault.name, SealFault.name] <;> rfl

end Nanodregg.Host
