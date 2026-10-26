/-
# Kernel.Proofs.Generated — what an object's call installs is checked as a member's is (KERNEL-75)

An `install` may now sit in a method's calls (`Body.callable`, LANG-86: a GENERATOR is a package whose
method returns `install BYTES`). The tree derives it as the calling object (`effect_as_signed`) through
the one receiver a signed `install` goes through, which takes no authority from its actor and runs
`X.program.checkInstall` on the bytes before it bears the ROM cell. So every package cell a nested
call's Draft creates holds bytes the install check accepted at the signer's pinned view: the kernel
checks what a generator emits exactly as it checks what a member installs (`tree_package_checked`).
Its floor is the kernel whose nested install skips the check; `Lang.Journey.Gen` GN4 is the deployed
run that reaches it (a generator of bytes that are not a package is refused by name, nothing born).
-/
import Kernel.Proofs.Ledger

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- Every package cell the Draft bears holds bytes `checkInstall` accepted at `look`. -/
def PackagesChecked (X : Ctx D) (look : Pinned D) (d : Draft D) : Prop :=
  ∀ p ∈ d.creates, p.2.kind = kindPackage →
    ∃ bytes, p.2 = { kind := kindPackage, discipline := .rom, slots := [(0, bytes)] } ∧
      X.program.checkInstall look bytes = .ok ()

omit [Ord D] in
/-- **An object installs only what the install check accepted.** Every package cell in the Draft of a
call an object makes (any depth of the tree) holds bytes `X.program.checkInstall` accepted at the
signer's pinned view: `install` is the only callable receiver that bears a package cell, and it checks
first. -/
theorem tree_package_checked {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} :
    ∀ n wk a b r, tree X look rv c n wk a b = .ok r → PackagesChecked X look r.1 := by
  refine tree_all ?_ ?_ ?_
  · intro a b ha hb p hp hk
    rcases List.mem_append.mp hp with hp | hp
    · exact ha p hp hk
    · exact hb p hp hk
  · intro _ _ _ _ p hp; simp at hp
  · intro sub wk actor b r hc hi h
    cases b with
    | invoke => simp [Body.isInvoke] at hi
    | install pkg =>
        have hd := stepped_draft h
        simp only [install, bind, Except.bind] at hd
        split at hd
        · cases hd
        · rename_i u hu
          simp only [pure, Except.pure, Except.ok.injEq] at hd
          rw [← hd]
          intro p hp _
          have := mem_bornAt_cell hp
          simp only [List.mem_singleton] at this
          exact ⟨pkg, this, by cases u; exact hu⟩
    | account asset owner =>
        have hd := stepped_draft h
        simp only [account, pure, Except.pure, Except.ok.injEq] at hd
        rw [← hd]
        intro p hp hk
        simp only [List.mem_singleton] at hp
        rw [hp] at hk
        simp [accountCell, kindAccount, kindPackage] at hk
    | grant target grantee rights parent =>
        have hd := stepped_draft h
        simp only [grant, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, ⟨⟩, _, _, _, hr⟩ := hd
        rw [← hr]
        intro p hp hk
        have := mem_bornAt_cell hp
        simp only [List.mem_singleton] at this
        rw [this] at hk
        simp [kindGrant, kindPackage] at hk
    | transfer src dst amount via once =>
        have hd := stepped_draft h
        obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, -, hr⟩ := transfer_ok hd
        rw [hr]; simp [PackagesChecked]
    | credit well acct amount via =>
        have hd := stepped_draft h
        obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, hr⟩ := credit_ok hd
        rw [hr]; simp [PackagesChecked]
    | _ => simp [Body.callable] at hc

end Nanodregg.Kernel.Receive
