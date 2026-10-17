/-
# Lang.Proofs.StdTeeth — every stdlib law, run by the one runner, admits and refuses

The spec theorems (`Lang.Proofs.Std`) say what an ADMITTED law implies; these instances show the
premise is satisfiable (each law admits a legitimate act) and that each clause bites (the act
with one thing wrong is refused, with that clause's reason). They run `runLaw`, the function the
receiver runs, by kernel evaluation of small closed instances: evidence that the generated terms
check out on these inputs, not a proof of their meaning.
-/
import Lang.Std
import Lang.Law

namespace Nanodregg.Lang.Std.Teeth

open Nanodregg.Lang Nanodregg.Lang.Std

private def admits : Except Fault (Except ByteArray Unit) → Bool
  | .ok (.ok ()) => true
  | _ => false

private def refusedWith (why : String) : Except Fault (Except ByteArray Unit) → Bool
  | .ok (.error b) => b == why.toUTF8
  | _ => false

private def b (s : String) : ByteArray := s.toUTF8

/-- A request from `agent` acting with `principal`'s authority, in window `[lo, hi]`, on `occ`. -/
private def req (agent principal : String) (occ : Data) (lo hi : Nat := 0) : Data :=
  .record [("agent", .bytes (b agent)), ("notBefore", .nat lo), ("occasion", occ),
    ("principal", .bytes (b principal)), ("validUntil", .nat hi)]

private def write : Data := .inj "write" (.record [])
private def birth : Data := .inj "birth" (.record [])
private def relaw (laws : String) : Data := .inj "relaw" (.bytes (b laws))
private def adopt (laws : String) : Data := .inj "adopt" (.bytes (b laws))

/-! ## quorum: 2 of {a, b, c} over `total` -/

private def QS : Ty := .record [("approvals", .nat), ("proposal", proposalTy .nat), ("total", .nat)]
/-- The law the CHECKED generator emits (a refusal would make every admitting tooth below fail). -/
private def q : Term := match quorum QS .nat [b "a", b "b", b "c"] 2 "total" with
  | .ok t => t
  | .error _ => .nat 0
private def qs (approvals : Nat) (p : Data) (total : Nat) : Data :=
  .record [("approvals", .nat approvals), ("proposal", p), ("total", .nat total)]
private def set (v : Nat) : Data := .inj "set" (.nat v)

theorem quorum_commits : admits (runLaw [] q (qs 3 (set 9) 5) (qs 0 (set 9) 9) (req "a" "a" write)) = true := by
  decide +kernel
theorem quorum_commit_only_the_proposal :
    refusedWith "not the proposal" (runLaw [] q (qs 3 (set 9) 5) (qs 0 (set 9) 77) (req "a" "a" write)) = true := by
  decide +kernel
theorem quorum_commit_needs_two :
    refusedWith "no quorum" (runLaw [] q (qs 1 (set 9) 5) (qs 0 (set 9) 9) (req "a" "a" write)) = true := by
  decide +kernel
theorem quorum_commit_resets :
    refusedWith "approvals not reset" (runLaw [] q (qs 3 (set 9) 5) (qs 3 (set 9) 9) (req "a" "a" write)) = true := by
  decide +kernel
theorem quorum_approves : admits (runLaw [] q (qs 1 (set 9) 5) (qs 3 (set 9) 5) (req "b" "b" write)) = true := by
  decide +kernel
theorem quorum_approval_is_own_bit :
    refusedWith "not an approval" (runLaw [] q (qs 1 (set 9) 5) (qs 5 (set 9) 5) (req "b" "b" write)) = true := by
  decide +kernel
theorem quorum_approves_once :
    refusedWith "not an approval" (runLaw [] q (qs 1 (set 9) 5) (qs 2 (set 9) 5) (req "a" "a" write)) = true := by
  decide +kernel
theorem quorum_members_only :
    refusedWith "not a member" (runLaw [] q (qs 1 (set 9) 5) (qs 3 (set 9) 5) (req "d" "d" write)) = true := by
  decide +kernel
theorem quorum_proposes : admits (runLaw [] q (qs 3 (set 9) 5) (qs 0 (set 77) 5) (req "c" "c" write)) = true := by
  decide +kernel
theorem quorum_propose_resets :
    refusedWith "approvals not reset" (runLaw [] q (qs 3 (set 9) 5) (qs 3 (set 77) 5) (req "c" "c" write)) = true := by
  decide +kernel
theorem quorum_birth_unapproved :
    refusedWith "approvals at birth" (runLaw [] q (qs 7 (set 77) 5) (qs 7 (set 77) 5) (req "a" "a" birth)) = true := by
  decide +kernel
theorem quorum_birth : admits (runLaw [] q (qs 0 (set 77) 5) (qs 0 (set 77) 5) (req "a" "a" birth)) = true := by
  decide +kernel
theorem quorum_relaws : admits (runLaw [] q (qs 3 (.inj "laws" (.bytes (b "L"))) 5)
    (qs 3 (.inj "laws" (.bytes (b "L"))) 5) (req "a" "a" (relaw "L"))) = true := by
  decide +kernel
theorem quorum_relaw_only_the_proposal :
    refusedWith "not the proposal" (runLaw [] q (qs 3 (.inj "laws" (.bytes (b "L"))) 5)
      (qs 3 (.inj "laws" (.bytes (b "L"))) 5) (req "a" "a" (relaw "M"))) = true := by
  decide +kernel
theorem quorum_relaw_not_by_set_approvals :
    refusedWith "not the proposal" (runLaw [] q (qs 3 (set 9) 5) (qs 3 (set 9) 5) (req "a" "a" (relaw "L"))) = true := by
  decide +kernel

/-- Adopting the quorum is a fresh start: a state with no approvals is admitted, and approvals the
previous laws let the owner write (all three bits, a proposal of exactly the incoming laws) are
refused: they were not judged by the quorum. -/
theorem quorum_adopts : admits (runLaw [] q (qs 0 (set 9) 5) (qs 0 (set 9) 5) (req "a" "a" (adopt "L"))) = true := by
  decide +kernel
theorem quorum_adopt_forged_approvals :
    refusedWith "approvals at birth" (runLaw [] q (qs 7 (.inj "laws" (.bytes (b "L"))) 5)
      (qs 7 (.inj "laws" (.bytes (b "L"))) 5) (req "a" "a" (adopt "L"))) = true := by
  decide +kernel

private def accepted : Except StdRefusal Term → Bool
  | .ok _ => true
  | .error _ => false

theorem quorum_accepts : accepted (quorum QS .nat [b "a", b "b", b "c"] 2 "total") = true := by decide +kernel

private def refusedBy (e : StdRefusal) : Except StdRefusal Term → Bool
  | .error e' => e' == e
  | .ok _ => false

/-- The checked generator refuses a member listed twice (two votes), a zero threshold, and agrees
with `q` on good parameters. -/
theorem quorum_refuses_duplicates :
    refusedBy .duplicateMember (quorum QS .nat [b "a", b "a", b "b"] 2 "total") = true := by decide +kernel
theorem quorum_refuses_zero :
    refusedBy .badThreshold (quorum QS .nat [b "a", b "b"] 0 "total") = true := by decide +kernel

/-! ## windowed: W = 50, at most 2 changes of `total` per epoch -/

private def WS : Ty := .record [("count", .nat), ("epoch", .nat), ("total", .nat)]
private def wd : Term := match windowed WS .nat 50 2 "total" with
  | .ok t => t
  | .error _ => .nat 0
private def ws (count epoch total : Nat) : Data :=
  .record [("count", .nat count), ("epoch", .nat epoch), ("total", .nat total)]

theorem windowed_bumps : admits (runLaw [] wd (ws 1 0 1) (ws 2 0 2) (req "a" "a" write 10 49)) = true := by
  decide +kernel
theorem windowed_limits :
    refusedWith "rate limit 2" (runLaw [] wd (ws 2 0 2) (ws 3 0 3) (req "a" "a" write 10 49)) = true := by
  decide +kernel
theorem windowed_one_epoch :
    refusedWith "window spans epochs" (runLaw [] wd (ws 2 0 2) (ws 3 0 3) (req "a" "a" write 0 1000)) = true := by
  decide +kernel
theorem windowed_epoch_is_the_window :
    refusedWith "epoch is not the call's window" (runLaw [] wd (ws 2 0 2) (ws 1 5 3) (req "a" "a" write 10 49)) = true := by
  decide +kernel
theorem windowed_restarts : admits (runLaw [] wd (ws 2 0 2) (ws 1 1 3) (req "a" "a" write 50 99)) = true := by
  decide +kernel
theorem windowed_refuses_zero_width :
    refusedBy .zeroWidth (windowed WS .nat 0 2 "total") = true := by decide +kernel
theorem windowed_limit_zero :
    refusedWith "rate limit 0" (runLaw [] (windowedLaw WS .nat 50 0 "total") (ws 0 0 1) (ws 1 1 2)
      (req "a" "a" write 50 99)) = true := by
  decide +kernel
theorem windowed_birth : admits (runLaw [] wd (ws 0 0 0) (ws 0 0 0) (req "a" "a" birth 10 49)) = true := by
  decide +kernel
/-- Adopted over a state, the window is the call's epoch and the count starts at 0: a stale epoch
(which would wedge every later change) or a spent count is refused. -/
theorem windowed_adopts : admits (runLaw [] wd (ws 0 1 7) (ws 0 1 7) (req "a" "a" (adopt "L") 50 99)) = true := by
  decide +kernel
theorem windowed_adopt_stale_epoch :
    refusedWith "epoch is not the call's window" (runLaw [] wd (ws 0 9 7) (ws 0 9 7) (req "a" "a" (adopt "L") 50 99)) = true := by
  decide +kernel
theorem windowed_adopt_spent_count :
    refusedWith "count at birth" (runLaw [] wd (ws 2 1 7) (ws 2 1 7) (req "a" "a" (adopt "L") 50 99)) = true := by
  decide +kernel
theorem windowed_counts_changes :
    refusedWith "count not bumped" (runLaw [] wd (ws 1 0 1) (ws 1 0 2) (req "a" "a" write 10 49)) = true := by
  decide +kernel

/-! ## bounded, the authority laws -/

private def OS : Ty := .record [("owner", .bytes), ("total", .nat)]
private def os (owner : String) (total : Nat) : Data := .record [("owner", .bytes (b owner)), ("total", .nat total)]

theorem bounded_admits : admits (runLaw [] (bounded OS "total" 100) (os "a" 0) (os "a" 100) (req "a" "a" write)) = true := by
  decide +kernel
theorem bounded_refuses :
    refusedWith "total over 100" (runLaw [] (bounded OS "total" 100) (os "a" 0) (os "a" 101) (req "a" "a" write)) = true := by
  decide +kernel
theorem bounded_adopt :
    refusedWith "total over 100" (runLaw [] (bounded OS "total" 100) (os "a" 500) (os "a" 500) (req "a" "a" (adopt "L"))) = true := by
  decide +kernel
theorem bounded_adopts :
    admits (runLaw [] (bounded OS "total" 100) (os "a" 5) (os "a" 5) (req "a" "a" (adopt "L"))) = true := by
  decide +kernel
theorem allowlist_adopt_refuses :
    refusedWith "not on the allowlist" (runLaw [] (allowlist OS [b "a", b "b"]) (os "a" 0) (os "a" 0) (req "c" "c" (adopt "L"))) = true := by
  decide +kernel
theorem allowlist_adopts :
    admits (runLaw [] (allowlist OS [b "a", b "b"]) (os "a" 0) (os "a" 0) (req "b" "b" (adopt "L"))) = true := by
  decide +kernel
theorem ownerSigns_adopts :
    admits (runLaw [] (ownerSigns OS) (os "a" 0) (os "a" 0) (req "a" "a" (adopt "L"))) = true := by
  decide +kernel
theorem ownerSigns_adopt_delegate :
    refusedWith "not signed by the owner" (runLaw [] (ownerSigns OS) (os "a" 0) (os "a" 0) (req "d" "a" (adopt "L"))) = true := by
  decide +kernel
theorem bounded_birth :
    refusedWith "total over 100" (runLaw [] (bounded OS "total" 100) (os "a" 500) (os "a" 500) (req "a" "a" birth)) = true := by
  decide +kernel

/-- A delegate `d` acting with owner `a`'s authority is refused; the owner's own key is admitted. -/
theorem ownerSigns_delegate :
    refusedWith "not signed by the owner" (runLaw [] (ownerSigns OS) (os "a" 0) (os "a" 7) (req "d" "a" write)) = true := by
  decide +kernel
theorem ownerSigns_owner :
    admits (runLaw [] (ownerSigns OS) (os "a" 0) (os "a" 7) (req "a" "a" write)) = true := by
  decide +kernel
theorem allowlist_admits :
    admits (runLaw [] (allowlist OS [b "a", b "b"]) (os "a" 0) (os "a" 7) (req "b" "b" write)) = true := by
  decide +kernel
theorem allowlist_refuses :
    refusedWith "not on the allowlist" (runLaw [] (allowlist OS [b "a", b "b"]) (os "a" 0) (os "a" 7) (req "c" "c" write)) = true := by
  decide +kernel
/-! ## machine: installed →start→ running →stop→ stopped, by methods 1 and 2 -/

private def phases : List Label := ["installed", "running", "stopped"]
private def edges : List (Label × Nat × Label) := [("installed", 1, "running"), ("running", 2, "stopped")]
private def MS : Ty := .record [("phase", stateTy phases)]
private def mc : Term :=
  match machine MS "phase" phases "installed" ["remove", "start", "stop"]
      [("installed", "start", "running"), ("running", "stop", "stopped")] with
  | .ok t => t
  | .error _ => .nat 0
private def ph (s : Label) : Data := .record [("phase", .inj s (.record []))]
private def invoke (m : Nat) : Data := .inj "invoke" (.nat m)

theorem machine_starts : admits (runLaw [] mc (ph "installed") (ph "installed") (req "a" "a" birth)) = true := by
  decide +kernel
theorem machine_starts_initial :
    refusedWith "phase does not start at installed" (runLaw [] mc (ph "running") (ph "running") (req "a" "a" birth)) = true := by
  decide +kernel
theorem machine_steps : admits (runLaw [] mc (ph "installed") (ph "running") (req "a" "a" (invoke 1))) = true := by
  decide +kernel
theorem machine_step_needs_its_method :
    refusedWith "no edge" (runLaw [] mc (ph "installed") (ph "running") (req "a" "a" (invoke 2))) = true := by
  decide +kernel
theorem machine_no_skip :
    refusedWith "no edge" (runLaw [] mc (ph "installed") (ph "stopped") (req "a" "a" (invoke 1))) = true := by
  decide +kernel
theorem machine_adopts : admits (runLaw [] mc (ph "installed") (ph "installed") (req "a" "a" (adopt "L"))) = true := by
  decide +kernel
theorem machine_adopt_initial :
    refusedWith "phase does not start at installed" (runLaw [] mc (ph "running") (ph "running") (req "a" "a" (adopt "L"))) = true := by
  decide +kernel
theorem machine_no_write :
    refusedWith "a machine changes only by its methods" (runLaw [] mc (ph "installed") (ph "running") (req "a" "a" write)) = true := by
  decide +kernel

end Nanodregg.Lang.Std.Teeth
