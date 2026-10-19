/-
# Hosting.Proofs.Plan — a plan stays inside its grain's directory and never touches what is hidden

`plan_paths`: every path a plan allows lies under `worlds/<l>/grains/<id>`. `plan_not_exposed`: no
allowed path is a prefix of a hidden one or lies inside one (the launcher's `Exposed` check is the
same property on canonical OS paths, a second barrier). `plan_sockets_own`: a grain may connect only
to its own broker socket and its own member socket, each under its own root, and only a resident to
any (HOSTING-17, HOSTING-25).
-/
import Hosting.Plan

namespace Nanodregg.Hosting.Proofs

open Nanodregg.Hosting
open Nanodregg.Codec.Path (clean)

theorem labelOk_clean {l : ByteArray} (h : labelOk l = true) : clean l = true := by
  simp only [labelOk, Bool.and_eq_true] at h; exact h.1

private theorem labelFrom_spec (c : ByteArray) : ∀ (n i : Nat), labelFrom c i n = true →
    ∀ j, i ≤ j → j < i + n → (h : j < c.size) → labelByte c[j] = true
  | 0, _, _, j, h1, h2, _ => by omega
  | n + 1, i, hf, j, h1, h2, hj => by
      simp only [labelFrom, Bool.and_eq_true] at hf
      by_cases hji : j = i
      · subst hji
        have := hf.1; rw [dif_pos hj] at this
        exact this
      · exact labelFrom_spec c n (i + 1) hf.2 j (by omega) (by omega) hj

/-- An accepted label holds only lowercase ASCII letters, digits and `-`. -/
theorem labelOk_bytes {l : ByteArray} (h : labelOk l = true) : ∀ x ∈ l.data.toList, labelByte x = true := by
  simp only [labelOk, Bool.and_eq_true] at h
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have hj' : j < l.size := by rw [Array.length_toList] at hj; exact hj
  have := labelFrom_spec l l.size 0 h.2 j (by omega) (by omega) hj'
  simp only [Array.getElem_toList]
  simpa only [ByteArray.getElem_eq_getElem_data] using this

/-- A label byte is neither an ASCII uppercase letter nor a non-ASCII byte: so ASCII case folding
and Unicode normalisation are the identity on an accepted label, and two accepted labels that a
case-insensitive file system identifies are equal. -/
theorem labelByte_folds_to_itself (x : UInt8) (h : labelByte x = true) :
    ¬ (65 ≤ x.toNat ∧ x.toNat ≤ 90) ∧ x.toNat < 128 := by
  have all : ∀ n : Fin 256, labelByte (UInt8.ofNat n) = true →
      ¬ (65 ≤ n.val ∧ n.val ≤ 90) ∧ n.val < 128 := by decide +kernel
  have := all ⟨x.toNat, x.toNat_lt⟩ (by simpa using h)
  simpa using this

/-- Two accepted labels that a case-insensitive file system identifies (equal after ASCII case
folding; no accepted byte is non-ASCII, so Unicode folding and normalisation do not apply) are
equal: they name two directories. -/
theorem labels_fold_injective {a b : ByteArray} (ha : labelOk a = true) (hb : labelOk b = true)
    (h : a.data.toList.map foldByte = b.data.toList.map foldByte) : a = b := by
  have fix : ∀ l : ByteArray, labelOk l = true → l.data.toList.map foldByte = l.data.toList := by
    intro l hl
    conv => rhs; rw [← List.map_id l.data.toList]
    apply List.map_congr_left
    intro x hx
    have := (labelByte_folds_to_itself x (labelOk_bytes hl x hx)).1
    unfold foldByte
    have : ¬ (65 ≤ x && x ≤ 90) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      intro ⟨h1, h2⟩; exact this ⟨UInt8.le_iff_toNat_le.mp h1, UInt8.le_iff_toNat_le.mp h2⟩
    simp [this]
  rw [fix a ha, fix b hb] at h
  cases a; cases b; simp_all [Array.toList_inj]

/-- Tooth: the fold is a real fold (`W` and `w` are one name to it), so `labels_fold_injective`
is not true of an identity. -/
theorem foldByte_folds : foldByte 87 = foldByte 119 := by decide

/-- Teeth: the label refusal is not vacuous, and a real label passes. -/
theorem labelOk_refuses_upper : labelOk (lit "W1") = false := by decide
theorem labelOk_refuses_nonascii : labelOk ⟨#[0xc3, 0xa9]⟩ = false := by decide
theorem labelOk_accepts : labelOk (lit "w1") = true ∧ labelOk (lit "alice-2") = true := by decide

/-- Each path of a plan in its ROLE: the program is `pkg/<entry>`, only `pkg` is read, only `vol` is
written, nothing else is executable, and the Store is hidden. (The other
theorems speak of `allowed`, the union; this one says which list each path is in, so a plan that
wrote `pkg` and read `vol` is refused here.) -/
theorem plan_roles {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    labelOk l = true ∧ labelOk g.idHex = true ∧ clean g.entry = true ∧
      p = { program := pkgDir l g ++ [g.entry], read := [pkgDir l g], write := [volDir l g],
            exec := [], broker := brokerOf g, member := memberOf g,
            hidden := [storeDir l] } := by
  unfold plan at h
  by_cases hl : labelOk l = true <;> by_cases hi : labelOk g.idHex = true <;>
    by_cases he : clean g.entry = true <;>
    simp_all [bind, Except.bind, pure, Except.pure]

/-- **The layout's hidden directories are exactly a plan's `hidden`** (HOSTING-24, CODEC-7's
condition): `layoutHidden`, which grain-launch checks at start, is the list every plan hides, so a
change of the plan's hidden list cannot leave the start check behind. -/
theorem plan_hidden_layout {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    p.hidden = layoutHidden.map fun n => worldRoot l ++ [n] := by
  obtain ⟨-, -, -, rfl⟩ := plan_roles h
  rfl

/-- **A grain connects only to its own sockets, each under its own root** (HOSTING-17, HOSTING-25):
an app's plan names no socket; a resident's names exactly `<its id>/broker.sock` under the broker
root and exactly `<its id>/nd.sock` under the member root. Identity is the socket, so no plan names
another grain's socket of either kind (`plan_sockets_disjoint`). -/
theorem plan_sockets_own {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    p.broker = (match g.kind with | .app => [] | .resident => [[g.idHex, brokerSock]]) ∧
      p.member = (match g.kind with | .app => [] | .resident => [[g.idHex, memberSock]]) := by
  obtain ⟨-, -, -, rfl⟩ := plan_roles h
  cases hk : g.kind <;> simp [brokerOf, memberOf, socketOf, hk]

/-- Every socket entry of a plan, of either root, starts with the grain's own directory name: the
law grain-launch checks of every launch frame (`foreignPath`), stated of Lean's plans; of the
controller's frames, `reconcile_launch_named`. -/
theorem plan_sockets_named {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    ∀ x ∈ p.broker ++ p.member, x.head? = some g.idHex := by
  obtain ⟨hb, hm⟩ := plan_sockets_own h
  intro x hx
  rw [hb, hm] at hx
  cases hk : g.kind <;> simp [hk] at hx
  rcases hx with rfl | rfl <;> rfl

/-- Two different grains' plans name no common socket, under either root. -/
theorem plan_sockets_disjoint {l l' : ByteArray} {g g' : Grain} {p p' : Plan} (h : plan l g = .ok p)
    (h' : plan l' g' = .ok p') (hne : g.idHex ≠ g'.idHex) :
    (∀ x ∈ p.broker, x ∉ p'.broker) ∧ (∀ x ∈ p.member, x ∉ p'.member) := by
  have n1 := plan_sockets_named h
  have n2 := plan_sockets_named h'
  refine ⟨fun x hx hx' => ?_, fun x hx hx' => ?_⟩
  · have := n1 x (List.mem_append_left _ hx); have := n2 x (List.mem_append_left _ hx'); simp_all
  · have := n1 x (List.mem_append_right _ hx); have := n2 x (List.mem_append_right _ hx'); simp_all

/-- A plan names at most two sockets in all (`sandbox::CONNECT_MAX` = 2, HOSTING-17 §5): a
resident's broker socket and its member socket, the two the model driver reaches. -/
theorem plan_sockets_max {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    p.broker.length + p.member.length ≤ 2 := by
  obtain ⟨hb, hm⟩ := plan_sockets_own h
  rw [hb, hm]; cases g.kind <;> simp

private theorem socks_clean : clean brokerSock = true ∧ clean memberSock = true := by decide

/-- Every component of a socket entry is clean: one directory below its root, one name in it (so
the launcher's join stays inside that root). -/
theorem plan_sockets_clean {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    ∀ x ∈ p.broker ++ p.member, x.length = 2 ∧ ∀ c ∈ x, clean c = true := by
  have hi := labelOk_clean (plan_roles h).2.1
  obtain ⟨hb, hm⟩ := plan_sockets_own h
  rw [hb, hm]
  intro x hx
  cases hk : g.kind <;> simp [hk] at hx
  rcases hx with rfl | rfl <;> simp [hi, socks_clean.1, socks_clean.2]

theorem plan_paths {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    ∀ x ∈ p.allowed, grainDir l g <+: x := by
  obtain ⟨-, -, -, rfl⟩ := plan_roles h
  intro x hx
  simp only [Plan.allowed, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨[lit "pkg", g.entry], by simp [pkgDir]⟩
  · exact ⟨[lit "pkg"], by simp [pkgDir]⟩
  · exact ⟨[lit "vol"], by simp [volDir]⟩

/-- `grains` is not `store`, so the grain directory and the hidden Store part at the third
component. -/
private theorem grains_ne : lit "grains" ≠ lit "store" := by
  decide

/-- Two paths that agree on `c` and then differ are not prefixes of one another. -/
private theorem parted {c s t : Path} {u v : ByteArray} (huv : u ≠ v) :
    ¬ (c ++ u :: s) <+: (c ++ v :: t) := by
  intro ⟨r, hr⟩
  have := congrArg (fun z => z[c.length]?) hr
  simp only [List.append_assoc, List.cons_append, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at this
  exact huv this

theorem plan_not_exposed {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    ∀ hd ∈ p.hidden, ∀ x ∈ p.allowed, ¬ hd <+: x ∧ ¬ x <+: hd := by
  intro hd hh x hx
  obtain ⟨y, rfl⟩ := plan_paths h x hx
  obtain ⟨-, -, -, rfl⟩ := plan_roles h
  have hx' : grainDir l g ++ y = worldRoot l ++ lit "grains" :: (g.idHex :: y) := by
    simp [grainDir]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rw [hx']
  subst hh
  exact ⟨parted (Ne.symm grains_ne), parted grains_ne⟩

/-- No grain may reach its Store's files. -/
theorem plan_no_store {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    ∀ x ∈ p.allowed, ¬ storeDir l <+: x := by
  have hh : storeDir l ∈ p.hidden := by
    obtain ⟨-, -, -, rfl⟩ := plan_roles h
    simp
  intro x hx
  exact (plan_not_exposed h _ hh x hx).1

/-! ## The deployed roots (HOSTING-32) -/

private theorem hosted_ne_members : lit "nd-hosted" ≠ lit "nd-members" := by decide
private theorem members_ne_follow : lit "members" ≠ lit "follow" := by decide

/-- **The hosted root, World `l`'s member workspaces and World `l'`'s follower state are three
disjoint trees** (cv 01a1507c-7245): none is a prefix of another, for every pair of labels. So the
stdio child, whose only write is its workspace under `membersRoot l`, writes no follower Store
(`stateRoot`), and nd-hosted's tree holds neither. -/
theorem roots_disjoint (l l' : ByteArray) :
    (¬ hostedRoot <+: membersRoot l ∧ ¬ membersRoot l <+: hostedRoot) ∧
      (¬ hostedRoot <+: stateRoot l' ∧ ¬ stateRoot l' <+: hostedRoot) ∧
      (¬ membersRoot l <+: stateRoot l' ∧ ¬ stateRoot l' <+: membersRoot l) := by
  have e1 : hostedRoot = [lit "srv"] ++ lit "nd-hosted" :: [] := rfl
  have e2 : membersRoot l = [lit "srv"] ++ lit "nd-members" :: [l, lit "members"] := rfl
  have e3 : stateRoot l' = [lit "srv"] ++ lit "nd-members" :: [l', lit "follow"] := rfl
  have same : ∀ {a b : Path}, a <+: b → a.length = b.length → a = b := fun h e => h.eq_of_length e
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [e1, e2]; exact parted hosted_ne_members
  · rw [e1, e2]; exact parted (Ne.symm hosted_ne_members)
  · rw [e1, e3]; exact parted hosted_ne_members
  · rw [e1, e3]; exact parted (Ne.symm hosted_ne_members)
  · have := same h rfl
    simp only [membersRoot, stateRoot, membersHome, List.cons_append, List.nil_append,
      List.cons.injEq, true_and] at this
    exact members_ne_follow this.2.1
  · have := same h rfl
    simp only [membersRoot, stateRoot, membersHome, List.cons_append, List.nil_append,
      List.cons.injEq, true_and] at this
    exact members_ne_follow this.2.1.symm

/-- **No path under the hosted root reaches a member workspace or a follower Store, or contains
one**: every path a plan names is joined onto `hostedRoot` (grain-launch's join), so no grain's
plan, of any World, reaches either. -/
theorem hosted_outside_members (l : ByteArray) (x : Path) :
    ¬ membersRoot l <+: hostedRoot ++ x ∧ ¬ stateRoot l <+: hostedRoot ++ x ∧
      ¬ hostedRoot ++ x <+: membersRoot l ∧ ¬ hostedRoot ++ x <+: stateRoot l := by
  have e1 : hostedRoot ++ x = [lit "srv"] ++ lit "nd-hosted" :: x := rfl
  have e2 : membersRoot l = [lit "srv"] ++ lit "nd-members" :: [l, lit "members"] := rfl
  have e3 : stateRoot l = [lit "srv"] ++ lit "nd-members" :: [l, lit "follow"] := rfl
  rw [e1, e2, e3]
  exact ⟨parted (Ne.symm hosted_ne_members), parted (Ne.symm hosted_ne_members),
    parted hosted_ne_members, parted hosted_ne_members⟩

theorem bytes_size (p : Path) : (Path.bytes p).size = p.textBytes := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    have h1 : (lit "/").size = 1 := by decide
    simp only [Path.bytes, ByteArray.size_append, h1, ih, Path.textBytes, List.map_cons, List.sum_cons]
    omega

/-- **Every socket a resident's processes connect to fits `sun_path`** (HOST-52: `pathTooLong` at
108), for every grain directory name the launcher accepts (`grain_name_ok`: at most `componentMax` = 64 bytes, emitted as
`GRAIN_NAME_MAX`, beside `sockPathMax` as `SOCK_PATH_MAX`) and
every label: no socket root holds a label, so no label can push one past the bound. The longest is
the follower's, 98 bytes at 64. -/
theorem sockets_fit (n : ByteArray) (hn : n.size ≤ Codec.Path.componentMax) :
    (brokerRoot ++ [n, brokerSock]).textBytes ≤ sockPathMax ∧
      (memberRoot ++ [n, memberSock]).textBytes ≤ sockPathMax ∧
      (followSockRoot ++ [n, followSock]).textBytes ≤ sockPathMax := by
  have h1 : (lit "run").size = 3 := by decide
  have h2 : (lit "nd-broker").size = 9 := by decide
  have h3 : (lit "nd-member").size = 9 := by decide
  have h4 : (lit "nd-member-follow").size = 16 := by decide
  have h5 : brokerSock.size = 11 := by decide
  have h6 : memberSock.size = 7 := by decide
  have h7 : followSock.size = 11 := by decide
  simp only [brokerRoot, memberRoot, followSockRoot, Path.textBytes, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h1, h2, h3, h4, h5,
    h6, h7, sockPathMax, Codec.Path.componentMax] at hn ⊢
  omega

/-- A label is at most `componentMax` (64) bytes: one clean component. Every path rendered from
a label (`membersRoot`, `stateRoot`, the units' `%i`) is bounded with it; no socket path holds one
(`sockets_fit`). -/
theorem labelOk_size {l : ByteArray} (h : labelOk l = true) : l.size ≤ Codec.Path.componentMax := by
  have := labelOk_clean h
  simp only [clean, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1.1.2

/-- Tooth for `sockets_fit`: the bound is not slack. A 74-byte name puts the follower's socket at 108
bytes, one past `sun_path`. -/
theorem follow_sock_past_bound : (followSockRoot ++ [⟨Array.replicate 74 97⟩, followSock]).textBytes = 108 := by
  decide

private theorem lits_clean :
    clean (lit "worlds") = true ∧ clean (lit "grains") = true ∧ clean (lit "pkg") = true ∧
      clean (lit "vol") = true ∧ clean (lit "store") = true := by
  decide

/-- Every component of every path a plan names is clean: so the list-prefix facts above are facts
about directories (no `..`, no `/`, no empty component), up to symlinks, which the sandbox's
deny-default and the launcher's program check answer. -/
theorem plan_components_clean {l : ByteArray} {g : Grain} {p : Plan} (h : plan l g = .ok p) :
    ∀ x ∈ p.allowed ++ p.hidden, ∀ c ∈ x, clean c = true := by
  obtain ⟨hl, hi, he, rfl⟩ := plan_roles h
  have hl := labelOk_clean hl
  have hi := labelOk_clean hi
  obtain ⟨h1, h2, h3, h4, h5⟩ := lits_clean
  intro x hx c hc
  simp only [Plan.allowed, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp only [pkgDir, volDir, grainDir, storeDir, worldRoot,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- Each refusal is exactly its unclean input (checked in order: label, id, entry). -/
theorem plan_refuses_label (l : ByteArray) (g : Grain) (h : labelOk l = false) :
    plan l g = .error .labelUnclean := by
  simp [plan, h, bind, Except.bind]

theorem plan_refuses_id (l : ByteArray) (g : Grain) (hl : labelOk l = true) (h : labelOk g.idHex = false) :
    plan l g = .error .idUnclean := by
  simp [plan, hl, h, bind, Except.bind, pure, Except.pure]

theorem plan_refuses_entry (l : ByteArray) (g : Grain) (hl : labelOk l = true) (hi : labelOk g.idHex = true)
    (h : clean g.entry = false) : plan l g = .error .entryUnclean := by
  simp [plan, hl, hi, h, bind, Except.bind, pure, Except.pure]

/-- Tooth for `Proofs.Wire.decode_encodeAction` on a launch: a real plan (a 64-byte directory
name, the label `w1`, the entry `app`) encodes into one frame. -/
theorem planned_launch_encodes :
    (match plan (lit "w1") { idHex := ⟨Array.replicate 64 97⟩, kind := .app, entry := lit "app" } with
     | .ok p => (Wire.encodeAction { grain := ⟨Array.replicate 64 97⟩, verdict := .launch p }).isSome
     | .error _ => false) = true := by
  decide +kernel

/-- Tooth: a resident's plan (a 64-byte directory name) encodes, and its socket entries are its own
broker socket and its own member socket, each in its own field, and nothing else. -/
theorem planned_resident_encodes :
    (match plan (lit "w1") { idHex := ⟨Array.replicate 64 97⟩, kind := .resident, entry := lit "app" } with
     | .ok p => (Wire.encodeAction { grain := ⟨Array.replicate 64 97⟩, verdict := .launch p }).isSome &&
         p.broker == [[⟨Array.replicate 64 97⟩, lit "broker.sock"]] &&
         p.member == [[⟨Array.replicate 64 97⟩, lit "nd.sock"]]
     | .error _ => false) = true := by
  decide +kernel

/-- Plans of two different Stores, or of two different grains, allow disjoint trees: no path one
allows is a prefix of a path the other allows (with `labels_fold_injective`, also on a
case-insensitive file system). -/
theorem plan_disjoint {l l' : ByteArray} {g g' : Grain} {p p' : Plan} (h : plan l g = .ok p)
    (h' : plan l' g' = .ok p') (hne : l ≠ l' ∨ g.idHex ≠ g'.idHex) :
    ∀ x ∈ p.allowed, ∀ y ∈ p'.allowed, ¬ x <+: y := by
  intro x hx y hy hxy
  obtain ⟨u, rfl⟩ := plan_paths h x hx
  obtain ⟨v, rfl⟩ := plan_paths h' y hy
  have e1 : grainDir l g ++ u = [lit "worlds"] ++ l :: (lit "grains" :: g.idHex :: u) := by simp [grainDir, worldRoot]
  have e2 : grainDir l' g' ++ v = [lit "worlds"] ++ l' :: (lit "grains" :: g'.idHex :: v) := by simp [grainDir, worldRoot]
  rw [e1, e2] at hxy
  rcases hne with hl | hi
  · exact parted hl hxy
  · by_cases hll : l = l'
    · subst hll
      have e3 : [lit "worlds"] ++ l :: (lit "grains" :: g.idHex :: u) = [lit "worlds", l, lit "grains"] ++ g.idHex :: u := by simp
      have e4 : [lit "worlds"] ++ l :: (lit "grains" :: g'.idHex :: v) = [lit "worlds", l, lit "grains"] ++ g'.idHex :: v := by simp
      rw [e3, e4] at hxy
      exact parted hi hxy
    · exact parted hll hxy

end Nanodregg.Hosting.Proofs
