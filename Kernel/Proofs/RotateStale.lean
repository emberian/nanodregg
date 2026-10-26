/-
# Kernel.Proofs.RotateStale — a rotate ends every outstanding call of its member (KERNEL-60)

breadstuffs' `SelfNonceBump` recovered for nothing: a member's `rotate` writes its member cell, so
the cell's version moves, and (KERNEL-54) a pin names the version. Every call that pinned the member
cell before the rotate carries a pin the World never holds again, so no World the fold reaches
from the rotate admits a Turn derived from it: the call is ended, whoever holds its signature. This
is the security property of a rotation after a key compromise: the stolen key's in-flight calls
are dead at the rotate, as a theorem of the fold, not only because the key is no longer current
(`unknownKey`, KERNEL-47 amendment 7), which a call signed with the NEXT key would pass.

The hash escape is a collision between the two pin inputs compared (`CollidesAmong` over an explicit
two-element list, KERNEL-56); `rotate_stales_outstanding_sep` is the binding form.
-/
import Kernel.Proofs.Versions
import Kernel.Proofs.Ledger

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel
open Nanodregg.Codec.Kernel (Cell.Fits)

variable {D : Type} [Ord D] [DecidableEq D]

/-- An admitted Turn's touches each saw the pin of the entry it was judged on. -/
theorem admit_seen {E : Env D} {w w' : World D} {t : Turn D} {x : Touch D}
    (h : World.admit E w t = .ok w') (hx : x ∈ t.touches) : pinOf E (w.entry E x.cell) = x.seen := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  obtain ⟨raw, hm, -⟩ := hk.touches
  obtain ⟨r, hr⟩ := mapEx_each hm x hx
  unfold touchCheck at hr
  simp only [except_bind_ok] at hr
  obtain ⟨⟨⟩, hs, -⟩ := hr
  simpa using req_ok.mp hs

/-- A derived rotation writes its member's cell: the Turn carries a write touch on it. -/
theorem rotate_writes_member {X : Ctx D} {w : World D} {c : Call D} {t : Turn D} {key : ByteArray} {next : D}
    (hb : c.unsigned.body = .rotate key next) (hr : receive X w c = .ok t) :
    ∃ x ∈ t.touches, x.cell = c.unsigned.member ∧ ∃ ops, x.act = .write ops := by
  obtain ⟨_, d, _k, hdd, hsl⟩ := receiveWith_sealed (receive_ok_with hr).2
  replace hdd := derive_of_withTicks hdd
  rw [derive_eq, hb] at hdd
  simp only [dispatch, stepped_map] at hdd
  unfold rotate at hdd
  simp only [except_bind_ok] at hdd
  obtain ⟨m, -, ⟨⟩, -, committed, -, ⟨⟩, -, hd⟩ := hdd
  simp only [pure, Except.pure, Except.ok.injEq] at hd
  subst hd
  obtain ⟨_, _, htouch, _, _, _, _, _, _, hpin⟩ := sealTurn_ok hsl
  obtain ⟨p, hp, hpk⟩ := hpin _ (List.mem_singleton_self _)
  refine ⟨{ cell := p.1, seen := p.2, act := actFor _ p.1 }, by rw [htouch]; exact List.mem_map_of_mem hp, hpk,
    [Op.set slotKey key, Op.set slotNext (X.env.bytes next)], ?_⟩
  simp [actFor, hpk]

section
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

/-- **A rotate ends every outstanding call of its member** (KERNEL-60; breadstuffs' `SelfNonceBump`,
as a theorem of the fold). From a World whose cells fit (`fold_cellsFit`: every reached World's), let
a call `c` of member `m` pin `m`'s member cell as it was at `w₀`. If the fold from `w₀` then admits a
rotation of `m`, no World the fold reaches from the rotation admits any Turn derived from `c`, or
the hash collides on the two pin inputs compared (the member entry's at `w₀` and at the World of the
attempt, which differ: the rotation moved the version). -/
theorem rotate_stales_outstanding {X : Ctx D} {w₀ w₁ w₂ w w' : World D} {l₁ l₂ : List (Step D)}
    {cr c : Call D} {tr t : Turn D} {key : ByteArray} {next : D}
    (hf : w₀.CellsFit Cell.Fits X.env) (h₁ : World.fold X.env w₀ l₁ = .ok w₁)
    (hb : cr.unsigned.body = .rotate key next) (hr : receive X w₁ cr = .ok tr)
    (ha : World.admit X.env w₁ tr = .ok w₂) (h₂ : World.fold X.env w₂ l₂ = .ok w)
    (hm : c.unsigned.member = cr.unsigned.member)
    (hpin : (c.unsigned.member, pinOf X.env (w₀.entry X.env c.unsigned.member)) ∈ c.unsigned.pins)
    (hrc : receive X w c = .ok t) (hac : World.admit X.env w t = .ok w') :
    CollidesAmong X.env.hash
      [pinPre X.env (w₀.entry X.env c.unsigned.member), pinPre X.env (w.entry X.env c.unsigned.member)] := by
  obtain ⟨x, hx, hxc, ops, hxa⟩ := rotate_writes_member hb hr
  obtain ⟨cell, v, post, hc1, -, hc2⟩ := admit_written_entry ha hx hxa
  rw [hxc, ← hm] at hc1 hc2
  have hadv12 : EAdv (w₁.entry X.env c.unsigned.member) (w₂.entry X.env c.unsigned.member) := by
    rw [hc1, hc2]; simp only [EAdv]; omega
  have hb2 : EAdv (w₁.entry X.env c.unsigned.member) (w.entry X.env c.unsigned.member) := by
    rcases fold_entryStep c.unsigned.member h₂ with h | h
    · rw [← h]; exact hadv12
    · exact eAdv_trans hadv12 h
  have hadv : EAdv (w₀.entry X.env c.unsigned.member) (w.entry X.env c.unsigned.member) := by
    rcases fold_entryStep c.unsigned.member h₁ with h | h
    · rw [h]; exact hb2
    · exact eAdv_trans h hb2
  have h12 : World.fold X.env w₁ [.turn tr] = .ok w₂ := by
    simp [World.fold, World.step, ha]
  have hfw : w.CellsFit Cell.Fits X.env := fold_cellsFit (fold_cellsFit (fold_cellsFit hf h₁) h12) h₂
  have hpre := pinPre_adv_ne (E := X.env) (cellsFit_verFit hf c.unsigned.member) (cellsFit_verFit hfw c.unsigned.member) hadv
  obtain ⟨_, d, _k, -, hsl⟩ := receiveWith_sealed (receive_ok_with hrc).2
  obtain ⟨_, _, htouch, -⟩ := sealTurn_ok hsl
  have hx' := List.mem_map_of_mem (f := fun p : D × D =>
    ({ cell := p.1, seen := p.2, act := actFor d.effects p.1 } : Touch D)) hpin
  have hseen := admit_seen hac (by rw [htouch]; exact hx')
  simp only at hseen
  exact ⟨_, List.mem_cons_self, _, List.mem_cons_of_mem _ List.mem_cons_self, fun h => hpre h.symm,
    (pinOf_eq_pre X.env _).symm.trans (hseen.symm.trans (pinOf_eq_pre X.env _))⟩

/-- **TOOTH** (`rotate_stales_outstanding`, the binding form): where the hash separates the two pin
inputs, a call that pinned its member before a rotation of that member is never admitted after
it. -/
theorem rotate_stales_outstanding_sep {X : Ctx D} {w₀ w₁ w₂ w : World D} {l₁ l₂ : List (Step D)}
    {cr c : Call D} {tr : Turn D} {key : ByteArray} {next : D}
    (hf : w₀.CellsFit Cell.Fits X.env) (h₁ : World.fold X.env w₀ l₁ = .ok w₁)
    (hb : cr.unsigned.body = .rotate key next) (hr : receive X w₁ cr = .ok tr)
    (ha : World.admit X.env w₁ tr = .ok w₂) (h₂ : World.fold X.env w₂ l₂ = .ok w)
    (hm : c.unsigned.member = cr.unsigned.member)
    (hpin : (c.unsigned.member, pinOf X.env (w₀.entry X.env c.unsigned.member)) ∈ c.unsigned.pins)
    (hs : Separates X.env.hash
      [pinPre X.env (w₀.entry X.env c.unsigned.member), pinPre X.env (w.entry X.env c.unsigned.member)]) :
    ∀ t w', receive X w c = .ok t → World.admit X.env w t = .ok w' → False :=
  fun _ _ hrc hac => hs.not_collides (rotate_stales_outstanding hf h₁ hb hr ha h₂ hm hpin hrc hac)

end

end Nanodregg.Kernel.Receive
