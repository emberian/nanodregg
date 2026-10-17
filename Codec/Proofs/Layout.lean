import Codec.Layout
import Codec.Proofs.Stream
import Codec.Proofs.Path

/-! # Every layout's codec is lawful (hence canonical: `Stream.decode_eq_ok_iff`). -/

namespace Nanodregg.Codec

theorem pathCodec_lawful (max : Nat) (fits : max < 2 ^ 32) : Stream.Lawful (Field.pathCodec max fits) := by
  unfold Field.pathCodec
  refine Stream.refine_lawful (Stream.bytesOf_lawful max fits) _ (fun p => ?_) (fun x y h => ?_)
  · have hc : ∀ c ∈ p.val, Path.clean c = true := by
      have := p.property; simp only [Path.fits, Bool.and_eq_true, List.all_eq_true] at this; exact this.1
    have hs : Path.split (Path.join p.val) = p.val := Path.split_join hc
    simp only [hs, p.property, dif_pos]
  · split at h
    · cases h; exact Subtype.ext (Path.join_split x.val)
    · cases h

/-- The path codec's tooth: `a//b` (an empty component) is refused by name at the field's offset,
and `a/b` reads back as two components. -/
theorem pathCodec_refuses_empty_component :
    (match (Field.pathCodec 64 (by decide)).decode ⟨#[4, 0, 0, 0, 97, 47, 47, 98]⟩ with
     | .error (.rejected 0 "path/badComponent") => true
     | _ => false) = true := by decide

theorem pathCodec_reads_components :
    (match (Field.pathCodec 64 (by decide)).decode ⟨#[3, 0, 0, 0, 97, 47, 98]⟩ with
     | .ok p => p.val == [⟨#[97]⟩, ⟨#[98]⟩]
     | _ => false) = true := by decide

theorem Field.codec_lawful (max : Nat) (fits : max < 2 ^ 32) :
    (f : Field) → Stream.Lawful (f.codec max fits)
  | .byte _ => Stream.u8_lawful
  | .u64 _ => Stream.u64_lawful
  | .bytes _ => Stream.bytesOf_lawful max fits
  | .list _ => Stream.array_lawful (Stream.bytesOf_lawful max fits) max fits
  | .oneOf _ cases => Stream.oneOf_lawful (cases.map Prod.snd).toArray
  | .u32 _ => Stream.u32_lawful
  | .path _ => pathCodec_lawful max fits
  | .paths _ => Stream.array_lawful (pathCodec_lawful max fits) max fits

theorem Layout.codec_lawful (max : Nat) (fits : max < 2 ^ 32) :
    (l : Layout) → Stream.Lawful (Layout.codec max fits l)
  | [] => Stream.unit_lawful
  | f :: fs => Stream.product_lawful (f.codec_lawful max fits) (Layout.codec_lawful max fits fs)

private theorem nodup_getElem_inj {α : Type} : ∀ {l : List α}, l.Nodup → ∀ {i j : Nat} (hi : i < l.length)
    (hj : j < l.length), l[i] = l[j] → i = j
  | [], _, _, _, hi, _, _ => by simp at hi
  | a :: as, h, i, j, hi, hj, he => by
      rw [List.nodup_cons] at h
      cases i with
      | zero => cases j with
        | zero => rfl
        | succ j => simp at he; exact absurd (he ▸ List.getElem_mem _) h.1
      | succ i => cases j with
        | zero => simp at he; exact absurd (he.symm ▸ List.getElem_mem _) h.1
        | succ j =>
            simp at he
            exact congrArg (· + 1) (nodup_getElem_inj h.2 (by simpa using hi) (by simpa using hj) he)

theorem Tagged.ofCode?_code {cases : Tagged} (h : (cases.map (·.2.1)).Nodup) (s : Fin cases.length) :
    Tagged.ofCode? cases (Tagged.code cases s) = some s := by
  unfold Tagged.ofCode?
  rcases hf : (List.finRange cases.length).find? (fun s' => Tagged.code cases s' == Tagged.code cases s) with _ | s'
  · rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf s (List.mem_finRange s))
  · have hs' := List.find?_some hf
    simp only [beq_iff_eq, Tagged.code, List.get_eq_getElem] at hs'
    have := nodup_getElem_inj h (i := s'.val) (j := s.val) (by simp) (by simp) (by simpa using hs')
    exact congrArg some (Fin.ext this)

theorem Tagged.code_ofCode? {cases : Tagged} {t : UInt8} {s : Fin cases.length}
    (h : Tagged.ofCode? cases t = some s) : Tagged.code cases s = t := by
  have := List.find?_some h; simpa using this

/-- A tagged frame with distinct codes is lawful (hence canonical). -/
theorem Tagged.codec_lawful (max : Nat) (fits : max < 2 ^ 32) (cases : Tagged)
    (h : (cases.map (·.2.1)).Nodup) : Stream.Lawful (Tagged.codec max fits cases) :=
  Stream.tagged_lawful _ (fun _ => Layout.codec_lawful max fits _) (Tagged.ofCode?_code h)
    (fun _ _ hs => Tagged.code_ofCode? hs)

/-- The tooth: two cases with one code are not told apart — the first wins, so the premise is needed. -/
theorem Tagged.ofCode?_needs_nodup :
    Tagged.ofCode? [("a", 1, []), ("b", 1, [])] (Tagged.code [("a", 1, []), ("b", 1, [])] ⟨1, by decide⟩) ≠
      some ⟨1, by decide⟩ := by decide

end Nanodregg.Codec
