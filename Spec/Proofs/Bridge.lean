/-
# Spec.Proofs.Bridge — a System whose kernel is the deployed kernel folds and decides as it does

A `System` whose `admit`/`refuse` are `World.admit`/`World.refuse` folds exactly as `World.fold`;
one whose `receive`/`recordedBy` are also the kernel's decides exactly as `Receive.Honest`. So
every theorem stated over `World.fold … ∧ Honest …` is a theorem about `Audited` for `deployed`
and for every trivial system that swaps a field other than these four.
-/
import Spec.Proofs.Claims

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

theorem fold_eq_world (S : System D) (ha : S.admit = World.admit S.X.env)
    (hr : S.refuse = World.refuse S.X.env) :
    ∀ (w : World D) (l : List (Step D)), S.fold w l = World.fold S.X.env w l
  | _, [] => rfl
  | w, s :: rest => by
    have hs : S.step w s = World.step S.X.env w s := by
      cases s <;> simp [System.step, World.step, ha, hr]
    rw [System.fold, World.fold, hs]
    cases World.step S.X.env w s with
    | error r => rfl
    | ok w' =>
      simp only
      rw [fold_eq_world S ha hr w' rest]
      cases World.fold S.X.env w' rest <;> rfl

theorem decided_iff_honest (S : System D) (hrc : S.receive = receive S.X)
    (hrb : S.recordedBy = recordedBy S.X) (ha : S.admit = World.admit S.X.env)
    (hr : S.refuse = World.refuse S.X.env) :
    ∀ (w : World D) (l : List (Step D)), Decided S w l ↔ Honest S.X w l
  | _, [] => by simp [Decided, Honest]
  | w, .turn t :: rest => by
    simp only [Decided, Honest, hrc, ha]
    exact exists_congr fun c => and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun w' => imp_congr Iff.rfl (decided_iff_honest S hrc hrb ha hr w' rest)))
  | w, .refusal r :: rest => by
    simp only [Decided, Honest, hrb, hr]
    exact exists_congr fun c => exists_congr fun v => exists_congr fun w₁ => and_congr Iff.rfl
      (and_congr Iff.rfl
        (forall_congr' fun w' => imp_congr Iff.rfl (decided_iff_honest S hrc hrb ha hr w' rest)))

/-- **Audited is the kernel's audit**, for a system whose four kernel fields are the kernel's. -/
theorem audited_iff (S : System D) (hrc : S.receive = receive S.X)
    (hrb : S.recordedBy = recordedBy S.X) (ha : S.admit = World.admit S.X.env)
    (hr : S.refuse = World.refuse S.X.env) {w w' : World D} {l : List (Step D)} :
    Audited S w l w' ↔ World.fold S.X.env w l = .ok w' ∧ Honest S.X w l := by
  rw [Audited, fold_eq_world S ha hr, decided_iff_honest S hrc hrb ha hr]

theorem audited_deployed {d : ByteArray → ByteArray} {w w' : World Codec.Digest}
    {l : List (Step Codec.Digest)} :
    Audited (deployed d) w l w' ↔
      World.fold Host.Deployed.X.env w l = .ok w' ∧ Honest Host.Deployed.X w l :=
  audited_iff (deployed d) rfl rfl rfl rfl

end Nanodregg.Spec
