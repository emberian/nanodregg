/-
# Lang.Proofs.LiveInvoke — the live invoke never sticks

`method_live_run_sound`, `invoke_live_never_stuck`: consumed by `Lang.Proofs.Provenance`.
-/
import Lang.Proofs.LiveHoles
import Lang.Proofs.Invoke

namespace Nanodregg.Lang

/-! ## From `Lang.Proofs.Contextual.LiveInvoke` -/
section

open Nanodregg.Kernel Nanodregg.Kernel.Receive

theorem method_live_run_sound {D : Type} {rv : RowView D} {self : D} {digestOf : ByteArray → Option D} {look : Pinned D}
    {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat} {p : Package} {ℓ : Label} {mty : Ty}
    {sg : Sig} {sv av reqv wv : Val} {ticks : Nat}
    (hload : loadLive digestOf rv self look fuel idb ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p)
    (hm : Row.find? ℓ (recordRow p.iface) = some mty) (hA : methodSig p.state p.rels mty = some sg)
    (hs : ValTy (Loaded.ifaces L) sv p.state) (ha : ValTy (Loaded.ifaces L) av sg.arg)
    (hr : ValTy (Loaded.ifaces L) reqv reqTy)
    (hw : ValTy (Loaded.ifaces L) wv (rowsTy p.rels sg.reads (methodPeer p.rels mty))) :
    RunOK (Loaded.ifaces L) (resultTy p.state sg.calls (editTy p.rels) sg.edits)
      (run L.lib Bounds.stackMax ticks 0 (State.init (apply4 g ℓ) [reqv, av, sv, wv])) := by
  obtain ⟨hlib, _⟩ := loadLive_libTy hload
  obtain ⟨row, hrow, hfind⟩ := recordRow_find hm
  have hmt := (methodSig_spec hA).1
  generalize methodPeer p.rels mty = ps at hw hmt
  subst hmt
  have href : HasType (Loaded.ifaces L) [reqTy, sg.arg, p.state, rowsTy p.rels sg.reads ps] (.ref g)
      (.record row) :=
    .ref (by rw [← hrow]; simp [Loaded.ifaces, hp])
  have ht : HasType (Loaded.ifaces L) [reqTy, sg.arg, p.state, rowsTy p.rels sg.reads ps] (apply4 g ℓ)
      (resultTy p.state sg.calls (editTy p.rels) sg.edits) :=
    .app (.app (.app (.app (.get href hfind) (.var rfl)) (.var rfl)) (.var rfl)) (.var rfl)
  exact run_sound hlib _ _ _ (.eval (.cons hr (.cons ha (.cons hs (.cons hw .nil)))) ht .nil)

theorem invoke_live_never_stuck {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat} {p : Package}
    {rv : RowView D} {ℓ : Label} {mty : Ty} {sg : Sig} {state : Slots} {args : ByteArray}
    {sd ad wd : Data} {r : Req D} {ticks : Nat}
    (hload : loadLive digestOf rv r.self look fuel idb ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p)
    (hm : Row.find? ℓ (recordRow p.iface) = some mty) (hA : methodSig p.state p.rels mty = some sg)
    (hstate : readState digestOf (recordRow p.state) state = .ok sd)
    (hargs : Wire.decodeData sg.arg args = .ok ad)
    {pkg : D} (hrows : methodReads bytesOf digestOf look pkg p.rels rv r.self ad sg.reads (p.peerReads ℓ) = .ok wd)
    (hr : reqOk bytesOf r = true) :
    RunOK L.ifaces (resultTy p.state sg.calls (editTy p.rels) sg.edits)
      (run L.lib Bounds.stackMax ticks 0
        (State.init (apply4 g ℓ) [(reqData bytesOf r).toVal, ad.toVal, sd.toVal, wd.toVal])) := by
  have hs := readState_conforms hstate
  rw [← checkShape_state ((loadLive_checked hload g p hp).1)] at hs
  rw [Package.peerReads_of hm] at hrows
  exact method_live_run_sound hload hp hm hA (toVal_typed hs) (toVal_typed (decodeData_conforms hargs))
    (toVal_typed (reqOk_conforms hr)) (toVal_typed (methodReads_conforms hrows))

end

end Nanodregg.Lang
