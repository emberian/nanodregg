/-
# Protocol.Proofs.FrameFit — a page and the continuation that asked for it fit ONE frame (PROTOCOL-70)

The transport bounds a frame's body as a whole (`bodyFits`: `Host.Wire.bodyMax`, `client/src/frame.rs`);
a layout bounds each field on its own. A `resume` after a `log` carries the continuation AND the
Host's page, so the deployed page budget is the frame less the largest page-phase continuation and
every byte of framing (`Bounds.pageBytesMax`). Here:

* `resume_size`, `State.bytes_size`, `Signed.bytes_size`, `page_size`: what each frame costs, read off
  the one codec (`Stream.Lawful.size_eq`), never restated; `command_size`: a command payload's size
  is `argvSize`, the number `parse` refuses by, and `commandFrame_argv_within`: every argv a decoded
  command frame carries is within that bound;
* `resume_frame_fits`: for every phase-2 continuation of an argv `parse` admits (`parse_past_bound`:
  within `argvBytesMax`), custody's answer at the deployed widths, and every page the Host builds at
  `Host.Page.budget` (`Host.Page.build_within`), the resume frame fits;
* `perField_budget_overflows`: the tooth, in the constants: at the old budget (`frameBytesMax - 1024`)
  the same sum is past the frame. The rows' `fullPage` plant is the same tooth, run.
-/
import Protocol.Proofs.Incoming
import Protocol.Proofs.Command
import Host.Proofs.Page

namespace Nanodregg.Protocol.FrameFit

open Nanodregg.Codec Nanodregg.Protocol.Command

theorem foldl_add_eq {α : Type} (f : α → Nat) : ∀ (l : List α) (n : Nat),
    l.foldl (fun n x => n + f x) n = n + (l.map f).sum
  | [], n => by simp
  | x :: l, n => by simp only [List.foldl_cons, foldl_add_eq f l, List.map_cons, List.sum_cons]; omega

/-- A list field's wire size: its `u32` count, then each item behind its `u32` length. -/
theorem list_size {max : Nat} (fits : max < 2 ^ 32) (v : Bounded max (Bytes max)) :
    (Stream.array max (Stream.bytesOf max fits) fits).size v = 4 + ((Text.unlist v).map (4 + ·.size)).sum := by
  simp only [Stream.array, Stream.bytesOf, Text.unlist, ← Array.foldl_toList, List.map_map]
  rw [foldl_add_eq (fun x : Bytes max => 4 + x.val.size)]
  rfl

/-- **A command payload's size is `argvSize`** (PROTOCOL-68's number, read off the one codec): the
size `commandFrame`'s `within` bounds, for the argv the payload carries, is `argvSize` of that argv.
So `parse`'s `argvPastBound` and the frame's bound compare the same number, and a change to
`commandLayout` that changes the payload's size breaks this statement. -/
theorem command_size {argv : List ByteArray} {v : Bounded Bounds.argvBytesMax (Bytes Bounds.argvBytesMax)}
    (h : Text.fitList Bounds.argvBytesMax argv = some v) :
    (Layout.codec Bounds.argvBytesMax (by decide) commandLayout).size (v, ()) = argvSize argv := by
  simp only [commandLayout, Layout.codec, Field.codec, Stream.product, Stream.unit]
  rw [list_size, unlist_fitList h]
  simp only [argvSize]
  omega

/-- **Every argv a command frame carries is within `parse`'s bound**: the frame admits a payload only
at most `argvBytesMax` bytes (`Stream.within`), which is `argvSize` of its argv (`command_size`), so
`parse` never refuses a decoded payload `argvPastBound`. -/
theorem commandFrame_argv_within
    (x : { v : Layout.Ty Bounds.argvBytesMax commandLayout //
      (Layout.codec Bounds.argvBytesMax (by decide) commandLayout).size v ≤ Bounds.argvBytesMax }) :
    argvSize (Text.unlist x.1.1) ≤ Bounds.argvBytesMax := by
  obtain ⟨⟨a, ⟨⟩⟩, h⟩ := x
  simp only [commandLayout, Layout.codec, Field.codec, Stream.product, Stream.unit] at h
  rw [list_size] at h
  simp only [argvSize]
  omega

theorem u64_size (n : Nat) : (Text.u64 n).size = 8 := by
  rw [Text.u64, ← Stream.u64_lawful.size_eq]; rfl

/-- **A resume frame's payload**: the two fields behind their lengths. -/
theorem resume_size (kf rf : Bytes Bounds.frameBytesMax) :
    (resumeFrame.bytes (kf, rf, ())).size = 4 + kf.val.size + (4 + rf.val.size) := by
  rw [← resumeFrame_lawful.size_eq]
  simp [resumeFrame, resumeLayout, Layout.codec, Field.codec, Stream.product, Stream.bytesOf, Stream.unit]

/-- **A continuation's size**: the argv as `argvSize` counts it, the phase byte, the acc. -/
theorem State.bytes_size {s : State} {k : ByteArray} (h : s.bytes = some k) :
    k.size = argvSize s.argv + 1 + (4 + (s.acc.map (4 + ·.size)).sum) := by
  unfold State.bytes at h
  cases ha : Text.fitList Bounds.frameBytesMax s.argv with
  | none => simp [ha, bind, Option.bind] at h
  | some a =>
    cases hc : Text.fitList Bounds.frameBytesMax s.acc with
    | none => simp [ha, hc, bind, Option.bind] at h
    | some c =>
      simp only [ha, hc, bind, Option.bind, pure, Option.some.injEq] at h
      subst h
      rw [← stateFrame_lawful.size_eq]
      simp only [stateFrame, stateLayout, Layout.codec, Field.codec, Stream.product, Stream.unit, Stream.u8]
      rw [list_size, list_size, unlist_fitList ha, unlist_fitList hc]
      simp only [argvSize]
      omega

/-- **Custody's answer's size**: three fields behind their lengths. -/
theorem Signed.bytes_size {s : Signed} {b : ByteArray} (h : s.bytes = some b) :
    b.size = (4 + s.key.size) + (4 + s.next.size) + (4 + s.signature.size) := by
  unfold Signed.bytes at h
  cases h1 : Text.fit Bounds.frameBytesMax s.key <;> cases h2 : Text.fit Bounds.frameBytesMax s.next <;>
    cases h3 : Text.fit Bounds.frameBytesMax s.signature <;> simp [h1, h2, h3, bind, Option.bind] at h
  subst h
  rw [← signResultFrame_lawful.size_eq]
  simp [signResultFrame, signResultLayout, Layout.codec, Field.codec, Stream.product, Stream.bytesOf, Stream.unit,
    fit_val h1, fit_val h2, fit_val h3]
  omega

/-- **A log page's size** (`Host.Page.bytes`): its events' wire bytes, the list's count, four `u64`
positions, the chain and the base digest, each behind its length. -/
theorem page_size {a : Host.Page.Acc} {ts th bs : Nat} {bd p : ByteArray}
    (h : Host.Page.bytes a ts th bs bd = .ok p) :
    p.size = 4 + a.eventBytes + 4 * (4 + 8) + (4 + a.chain.size) + (4 + bd.size) := by
  unfold Host.Page.bytes at h
  dsimp only at h
  split at h
  · rename_i l n c t th' bs' bd' hl hn hc ht hth hbs hbd
    simp only [Except.ok.injEq] at h
    subst h
    rw [← logReplyFrame_lawful.size_eq]
    simp only [logReplyFrame, logReplyLayout, Layout.codec, Field.codec, Stream.product, Stream.unit]
    rw [list_size, unlist_fitList hl]
    simp only [Stream.bytesOf, fit_val hn, fit_val hc, fit_val ht, fit_val hth, fit_val hbs, fit_val hbd, u64_size,
      Host.Page.Acc.eventBytes]
    omega
  · cases h

/-- The constants: the frame is exactly its framing, the largest page-phase continuation and the
page budget (no subtraction in `pageBytesMax` truncates). -/
theorem frame_split : Bounds.resumeFramingBytes + Bounds.logReplyFramingBytes +
    Bounds.pageContinuationBytesMax + Bounds.pageBytesMax = Bounds.frameBytesMax := by decide

/-- **A full page and its continuation fit one frame** (PROTOCOL-70, readers A3). For a phase-2
continuation (the one a `log` step hands out: `start`, custody's `signed` answer, `pages`, `upTo`,
`tried`) of an argv within `argvBytesMax` (every argv `parse` admits, `parse_past_bound`), with the
four positions as `u64`s and custody's key, next key and signature at most the deployed widths, and
for every page `Host.Page.bytes` writes from an `Acc` holding at most `Host.Page.budget` event bytes
(every page `Host.Page.build` returns at that budget, `Host.Page.build_within`) with a chain and base
digest of the deployed digest width: the continuation and the Host's reply (`ok ‖ page`) each fit a
field, and the `resume` frame carrying both fits the transport's bound AS A WHOLE. At the old budget
it does not (`perField_budget_overflows`, and the rows' `fullPage` plant). -/
theorem resume_frame_fits {argv : List ByteArray} {startB pagesB upToB triedB signedB k page bd : ByteArray}
    {s : Signed} {a : Host.Page.Acc} {ts th bs : Nat}
    (hargv : argvSize argv ≤ Bounds.argvBytesMax)
    (hu : startB.size = 8 ∧ pagesB.size = 8 ∧ upToB.size = 8 ∧ triedB.size = 8)
    (hs : s.bytes = some signedB)
    (hw : s.key.size ≤ Bounds.custodyKeyBytes ∧ s.next.size ≤ Bounds.custodyKeyBytes ∧
      s.signature.size ≤ Bounds.custodySignatureBytes)
    (hk : State.bytes ⟨argv, 2, [startB, signedB, pagesB, upToB, triedB]⟩ = some k)
    (ha : a.eventBytes ≤ Host.Page.budget)
    (hc : a.chain.size ≤ Host.digestBytes) (hd : bd.size ≤ Host.digestBytes)
    (hp : Host.Page.bytes a ts th bs bd = .ok page) :
    ∃ kf rf, Text.fit Bounds.frameBytesMax k = some kf ∧
      Text.fit Bounds.frameBytesMax (⟨#[Status.ok.code]⟩ ++ page) = some rf ∧
      bodyFits (resumeFrame.bytes (kf, rf, ())) = true := by
  have hks := State.bytes_size hk
  have hss := Signed.bytes_size hs
  have hps := page_size hp
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hks
  obtain ⟨h1, h2, h3, h4⟩ := hu
  obtain ⟨w1, w2, w3⟩ := hw
  have nb : Host.Page.budget = 129717 := by decide
  have na : Bounds.argvBytesMax = 132096 := by decide
  have nf : Bounds.frameBytesMax = 262144 := rfl
  have nk : Bounds.custodyKeyBytes = 32 := rfl
  have ns : Bounds.custodySignatureBytes = 64 := rfl
  have nd : Host.digestBytes = 32 := rfl
  have hr : (⟨#[Status.ok.code]⟩ ++ page : ByteArray).size = 1 + page.size := by
    simp [ByteArray.size_append]
  have hkb : k.size ≤ Bounds.frameBytesMax := by omega
  have hrb : (⟨#[Status.ok.code]⟩ ++ page : ByteArray).size ≤ Bounds.frameBytesMax := by omega
  refine ⟨⟨k, hkb⟩, ⟨_, hrb⟩, by simp only [Text.fit, dif_pos hkb], by simp only [Text.fit, dif_pos hrb], ?_⟩
  have hres := resume_size ⟨k, hkb⟩ ⟨_, hrb⟩
  simp only at hres
  simp only [bodyFits, decide_eq_true_eq]
  omega

/-- **The tooth, in the constants**: at the per-field budget (`frameBytesMax - 1024`, before
PROTOCOL-70) the largest page-phase continuation and a full page are past the frame. -/
theorem perField_budget_overflows : Bounds.frameBytesMax < Bounds.resumeFramingBytes +
    Bounds.logReplyFramingBytes + Bounds.pageContinuationBytesMax + (Bounds.frameBytesMax - 1024) := by
  decide

/-- The budget still serves the largest event the kernel admits (HOST's `budget_fits_event`, here
with its margin): a page of one such event has room to spare. -/
theorem budget_serves_event : Bounds.pageEventBytesMax + 4 ≤ Host.Page.budget := Host.Page.budget_fits_event

end Nanodregg.Protocol.FrameFit
