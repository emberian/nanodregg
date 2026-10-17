/-
# Host.Proofs.Serve — the loop decides a submit exactly as `Kernel.Receive.submit` does

`step_submit`: one submit frame carrying call `c`, stepped by the writer's machine from any batch
accumulator, leaves the World `Receive.submit` returns (or the World unchanged when it refuses),
and stages exactly the Turn `Receive.submit` derives (or nothing). The loop adds no decision of its
own between the signed call and the log.

`step_journaled`: a call already in the journal answers `ok` with its ORIGINAL receipt (height and
turn digest from the journal) and leaves the World and the staged Turns as they were — whatever
`receive` would now say about it (a retried rotation must not be re-judged, KERNEL-7).
-/
import Host.Serve

namespace Nanodregg.Host

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

theorem step_submit (X : Ctx D) (w : World D) (out : Out (Turn D)) (q : Request Frame) (c : Call D)
    (hop : Protocol.Op.ofCode? q.body.op = some .submit) (hc : X.decodeCall q.body.payload = some c) :
    ((machine X).step (w, out) q).1 =
        (match submit X w c with | .ok (_, w') => w' | .error _ => w) ∧
      ((machine X).step (w, out) q).2.staged =
        (match submit X w c with | .ok (t, _) => out.staged.push t | .error _ => out.staged) := by
  simp only [Machine.step, machine, handle, hop, hc, submit]
  cases hj : w.journal[txIdOf X c]? with
  | some p => simp
  | none =>
    simp only
    cases hr : receive X w c with
    | error r => simp
    | ok t =>
      simp only
      cases ha : World.admit X.env w t with
      | error r => simp
      | ok w' => simp

theorem step_journaled (X : Ctx D) (w : World D) (out : Out (Turn D)) (q : Request Frame) (c : Call D)
    (h : Nat) (d : D)
    (hop : Protocol.Op.ofCode? q.body.op = some .submit) (hc : X.decodeCall q.body.payload = some c)
    (hj : w.journal[txIdOf X c]? = some (h, d)) :
    (machine X).step (w, out) q =
      (w, { out with replies := out.replies.push ⟨q.conn, Protocol.Status.ok.code, receipt X h d⟩ }) := by
  simp only [Machine.step, machine, handle, hop, hc, hj]

end Nanodregg.Host
