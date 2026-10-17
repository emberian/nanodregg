/-
# Ops.Proofs.Units — a rendered unit is confined, and restarts exactly the restart classes of
both exit tables (the child's `Host.Status`, nd-supervise's own `SupervisorExit`)
-/
import Ops.Units
import Host.Proofs.Exit
import Protocol.Proofs.Exit
import Hosting.Proofs.BrokerExit
import Hosting.Proofs.LaunchExit

namespace Nanodregg.Ops.Units

open Nanodregg.Host
open Nanodregg.Protocol (SupervisorExit)
open Nanodregg.Hosting (DeciderExit KeybrokerExit ControllerExit LaunchExit)

/-- What a rendered unit is: the node, its nd-supervise command line and `preventCodes`. -/
theorem ofNode_ok (n : Node) (u : Service) (h : Service.ofNode n = .ok u) :
    u = { node := n, exec := n.exec, prevent := preventCodes } := by
  unfold Service.ofNode at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl

/-- A unit exists only for a node that hides something. -/
theorem ofNode_hidden (n : Node) (u : Service) (h : Service.ofNode n = .ok u) : n.hide ≠ [] := by
  intro he
  simp [Service.ofNode, he] at h

/-- A rendered unit's command line starts with nd-supervise: the host is never run unconfined. -/
theorem ofNode_supervised (n : Node) (u : Service) (h : Service.ofNode n = .ok u) :
    u.exec.head? = some (.lit (supervisor n)) := by
  obtain rfl := ofNode_ok n u h; simp [Node.exec]

/-- A rendered unit lets the child execute exactly its own program: `--exec HOST` precedes every
`--hide`, and HOST is the program after `--` (CLIENT's `ProgramOutside` refuses a program outside
every read and exec entry, so a unit without it exits 64 at every start). -/
theorem ofNode_exec_program (n : Node) (u : Service) (h : Service.ofNode n = .ok u) :
    u.exec.take 6 = [.lit (supervisor n), .lit n.sock, .lit "--write", .lit n.store,
      .lit "--exec", .lit (hostExe n)] ∧ .lit (hostExe n) ∈ u.exec.drop 6 := by
  obtain rfl := ofNode_ok n u h
  exact ⟨by simp [Node.exec], by simp [Node.exec]⟩

/-- Every rendered unit prevents exactly `preventCodes`. -/
theorem ofNode_prevent_eq (n : Node) (u : Service) (h : Service.ofNode n = .ok u) :
    u.prevent = preventCodes := by
  obtain rfl := ofNode_ok n u h; rfl

/-- A Host status is in the prevent list iff HOST's table calls it fatal: the supervisor's half
adds no Host code (`code_disjoint_host`). -/
theorem mem_preventCodes_host (s : Status) : s.code ∈ preventCodes ↔ s.cls = .fatal := by
  unfold preventCodes
  rw [List.mem_append, Status.mem_codesOf_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exfalso
      simp only [SupervisorExit.codesOf, List.mem_map] at h
      obtain ⟨e, _, he⟩ := h
      exact SupervisorExit.code_disjoint_host e s he
  · exact Or.inl

/-- A supervisor exit is in the prevent list iff CLIENT's table calls it fatal. -/
theorem mem_preventCodes_supervisor (e : SupervisorExit) : e.code ∈ preventCodes ↔ e.cls = .fatal := by
  cases e <;> decide

/-- The prevented codes are exactly the fatal class of the Host's table: a Host status is
prevented from restarting iff it is fatal. -/
theorem ofNode_prevent (n : Node) (u : Service) (h : Service.ofNode n = .ok u) (s : Status) :
    s.code ∈ u.prevent ↔ s.cls = .fatal := by
  rw [ofNode_prevent_eq n u h]; exact mem_preventCodes_host s

/-- ... and of the supervisor's: nd-supervise's own exit is prevented iff it is fatal. -/
theorem ofNode_prevent_supervisor (n : Node) (u : Service) (h : Service.ofNode n = .ok u)
    (e : SupervisorExit) : e.code ∈ u.prevent ↔ e.cls = .fatal := by
  rw [ofNode_prevent_eq n u h]; exact mem_preventCodes_supervisor e

/-- No restart-class or done status is prevented: `uncertain`, a seal's IO and eof are never
mistaken for fatal. -/
theorem ofNode_restart_not_prevented (n : Node) (u : Service) (h : Service.ofNode n = .ok u)
    (s : Status) (hs : s.cls ≠ .fatal) : s.code ∉ u.prevent := by
  rw [ofNode_prevent n u h s]; exact hs

/-- The tooth of the supervisor half: a child killed by a signal (66) is restarted, a launch
refusal (64) is not. Removing the supervisor's codes from `preventCodes` falsifies the second. -/
theorem preventCodes_supervisor_split :
    SupervisorExit.childSignaled.code ∉ preventCodes ∧
    SupervisorExit.refusedAtLaunch.code ∈ preventCodes := by decide

/-- The planted node: nothing hidden → refused by name, never rendered. -/
theorem plant_nothing_hidden : Service.ofNode { writer with hide := [] } = .error .nothingHidden := by
  simp [Service.ofNode]

/-- The keybroker unit stops on a decider end iff HOSTING's table calls it fatal. -/
theorem mem_brokerPrevent_decider (e : DeciderExit) : e.code ∈ brokerPreventCodes ↔ e.cls = .fatal := by
  cases e <;> decide

/-- ... and on keybroker's own end iff fatal. -/
theorem mem_brokerPrevent_keybroker (e : KeybrokerExit) : e.code ∈ brokerPreventCodes ↔ e.cls = .fatal := by
  cases e <;> decide

/-- A Rust panic (101) is in no table and is restarted; a clean decider end (0) is never prevented. -/
theorem brokerPrevent_panic_and_done : 101 ∉ brokerPreventCodes ∧ 0 ∉ brokerPreventCodes := by decide

/-- The tooth: a custody refusal of the key file's chain (86) is prevented, a signalled decider
(102) and a decider behind the tail (77) are restarted. False if either table's half is dropped. -/
theorem brokerPrevent_split :
    KeybrokerExit.keyFileDir.code ∈ brokerPreventCodes ∧ DeciderExit.store.code ∈ brokerPreventCodes ∧
    KeybrokerExit.deciderSignaled.code ∉ brokerPreventCodes ∧ DeciderExit.behind.code ∉ brokerPreventCodes := by
  decide

/-- A unit with a runtime directory is a system unit (systemd makes `/run/NAME` only for one),
and its socket is in that directory by construction (`Node.sock`). -/
theorem ofNode_runtime_system (n : Node) (u : Service) (h : Service.ofNode n = .ok u) (r : String)
    (hr : n.runtime = some r) : n.user.isSome ∧ n.sock = "/run/" ++ r ++ "/" ++ n.socket := by
  refine ⟨?_, by simp [Node.sock, hr]⟩
  unfold Service.ofNode at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hu
      cases hus : n.user <;> simp_all

/-- The planted node: the writer's runtime directory on a user unit is refused by name. -/
theorem plant_runtime_on_user_unit :
    Service.ofNode { writer with user := none } = .error .runtimeOnUserUnit := by
  simp [Service.ofNode, writer]

/-- The broker check's first refusal: a hosted group equal to the key holder. -/
theorem Broker.check_of_hosted_eq (b : Broker) (he : b.hosted = b.user) :
    b.check = .error .hostedIsKeyHolder := by
  simp only [Broker.check, he, beq_self_eq_true, if_true]
  rfl

/-- A broker that renders never serves its key holder's own group: no tmpfiles line or sysusers
file is emitted for `hosted = user` (HOSTING-17: a grain under the key holder's uid reads the
provider keys). -/
theorem Broker.check_hosted_ne_user (b : Broker) (h : b.check = .ok ()) : b.hosted ≠ b.user := by
  intro he
  rw [Broker.check_of_hosted_eq b he] at h
  cases h

theorem Broker.tmpfiles_hosted_ne_user (b : Broker) (t : String) (h : b.tmpfiles = .ok t) :
    b.hosted ≠ b.user := by
  intro he
  simp only [Broker.tmpfiles, Broker.check_of_hosted_eq b he, bind, Except.bind] at h
  cases h

theorem Broker.sysusers_hosted_ne_user (b : Broker) (t : String) (h : b.sysusers = .ok t) :
    b.hosted ≠ b.user := by
  intro he
  simp only [Broker.sysusers, Broker.check_of_hosted_eq b he, bind, Except.bind] at h
  cases h

/-- The planted broker: the hosted group set to the key holder is refused by name. -/
theorem plant_hosted_is_key_holder :
    ({ keybroker with hosted := keybroker.user } : Broker).check = .error .hostedIsKeyHolder :=
  Broker.check_of_hosted_eq _ rfl

/-- A node that shares its socket with a group renders `--group ${ND_GID}` before `--`, inside
nd-supervise's own options (CLIENT-21: after `--` it would be the child's argument); one that does
not, renders nothing between `--exec HOST` and its `--hide`s (its socket stays 0600). -/
theorem ofNode_group (n : Node) (u : Service) (h : Service.ofNode n = .ok u) :
    (n.group = true → u.exec.take 8 = [.lit (supervisor n), .lit n.sock, .lit "--write", .lit n.store,
      .lit "--exec", .lit (hostExe n), .lit "--group", .var envGid]) ∧
    (n.group = false → u.exec.drop 6 = n.hide.flatMap (fun h => [.lit "--hide", .lit h]) ++ [.lit "--", .lit (hostExe n)] ++ n.args) := by
  obtain rfl := ofNode_ok n u h
  constructor
  · intro hg; simp [Node.exec, hg]
  · intro hg; simp [Node.exec, hg]

/-- The grain-launch unit stops on a controller end iff HOSTING's table calls it fatal. -/
theorem mem_launchPrevent_controller (e : ControllerExit) :
    e.code ∈ launchPreventCodes ↔ e.cls = .fatal := by
  cases e <;> decide

/-- ... and on grain-launch's own end iff fatal. -/
theorem mem_launchPrevent_launch (e : LaunchExit) : e.code ∈ launchPreventCodes ↔ e.cls = .fatal := by
  cases e <;> decide

/-- A Rust panic (101) and a clean controller end (0) are never prevented. -/
theorem launchPrevent_panic_and_done : 101 ∉ launchPreventCodes ∧ 0 ∉ launchPreventCodes := by decide

/-- The tooth: a Store refusal of the controller (109) and a defect action (120) stop the unit; a
signalled controller (126) and a failed report pipe (123) restart. False if either half is dropped
or a class flips. -/
theorem launchPrevent_split :
    ControllerExit.store.code ∈ launchPreventCodes ∧ LaunchExit.badAction.code ∈ launchPreventCodes ∧
    LaunchExit.controllerSignaled.code ∉ launchPreventCodes ∧ LaunchExit.reportPipe.code ∉ launchPreventCodes := by
  decide

/-- A launcher renders only if its controller reads the Store its follower writes, as the
follower's own user (HOSTING-17: the controller never reads the writer's files). -/
theorem Launcher.check_follower (l : Launcher) (h : l.check = .ok ()) :
    l.store = l.follower.store ∧ l.follower.user = some l.user := by
  cases hp : l.paired
  · have : l.check = .error (.badPath l.store) := by
      simp only [Launcher.check, hp]; rfl
    rw [this] at h; cases h
  · simpa [Launcher.paired, Bool.and_eq_true, beq_iff_eq] using hp

end Nanodregg.Ops.Units
