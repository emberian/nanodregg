/- The generated methods pass the supplied response to the author's continuation. -/
import Lang.Proofs.StdActivity

namespace Nanodregg.Lang.Std


/-- Once the start precondition succeeds, selecting the generated method's
result state evaluates the author's start function at the original inputs. -/
theorem activity_start_state
    (S : Ty) (rels : List (Label × RelDecl)) (cursor log : Label)
    (cd ld : RelDecl) (plans : List ActivityPlan) (p : ActivityPlan)
    (lib : List Term) (env : Env) (req arg state rows result : Val)
    (hpre : BigStep lib (req :: arg :: state :: rows :: req :: arg :: state :: rows :: env)
      (activityApply p.precondition [.var 2, .var 1, .var 0]) (.ok (.bool true)))
    (hstart : BigStep lib (req :: arg :: state :: rows :: req :: arg :: state :: rows :: env)
      (activityApply p.start [.var 2, .var 1, .var 0]) (.ok result)) :
    BigStep lib (req :: arg :: state :: rows :: env)
      (.get (activityApply (activityStartMethod S rels cursor log cd ld plans p)
        [.var 3, .var 2, .var 1, .var 0]) "state") (.ok result) := by
  apply BigStep.get
  · unfold activityApply activityStartMethod activityMethod
    simp only [List.foldl]
    apply BigStep.app
      (BigStep.app (BigStep.app (BigStep.app .lam (.var rfl) .lam) (.var rfl) .lam) (.var rfl) .lam)
      (.var rfl)
    exact .iteT hpre .record
  · exact .field rfl hstart

private def resumeArg (agent : ByteArray) (nb : Nat) (response : Data) : Data :=
  .record [("agent", .digest agent), ("notBefore", .nat nb), ("response", response)]

private def resumeOld (name : Label) (captured answered : Data) : Data :=
  .record [("answered", answered), ("captured", .inj name captured)]

private def resumePoint (agent : ByteArray) (nb : Nat) (old : Data) : Data :=
  .record [("key", .record [("agent", .digest agent), ("notBefore", .nat nb)]),
    ("val", .inj "some" old)]

private def resumeRows (log : Label) (point : Data) : Data :=
  .record [(log, .record [("p0", .inj "some" point)])]

private def resumeEnv (log name : Label) (agent : ByteArray) (nb : Nat)
    (captured answered response : Data) (req state : Val) (env : Env) : Env :=
  let arg := (resumeArg agent nb response).toVal
  let rows := (resumeRows log (resumePoint agent nb (resumeOld name captured answered))).toVal
  req :: arg :: state :: rows :: req :: arg :: state :: rows :: env

private theorem find_plan {names : List (Label × Unit)} {l : Label}
    (hf : Row.find? l names = some ()) (f : Label → Term) :
    Row.find? l (names.map fun p => (p.1, f p.1)) = some (f l) := by
  induction names with
  | nil => simp [Row.find?] at hf
  | cons p ps ih =>
    rcases p with ⟨k, _⟩
    simp only [Row.find?, List.map_cons] at hf ⊢
    split at hf
    · rename_i h; subst h; simp
    · rename_i h; simp only [h, ↓reduceIte]; exact ih hf

/-- The generated method's successful path reaches the author's continuation
with the captured payload and this call's response. The resumer and keyed-read
checks are actual evaluations, not assumed package admission. Row guards still
judge the emitted edits separately, including replay and immutable capture. -/
theorem activity_resume_state
    (S : Ty) (rels : List (Label × RelDecl)) (cursor log : Label)
    (cd ld : RelDecl) (resumer : Term) (plans : List ActivityPlan) (p : ActivityPlan)
    (lib : List Term) (env : Env) (agent : ByteArray) (nb : Nat)
    (captured answered response : Data) (req state result : Val)
    (hp : Row.find? p.name (Row.sort (plans.map fun q => (q.name, ()))) = some ())
    (hres : BigStep lib (resumeEnv log p.name agent nb captured answered response req state env)
      (activityApply resumer [.var 2, .var 0]) (.ok (.bool true)))
    (hkey : BigStep lib
      ((resumeOld p.name captured answered).toVal ::
        (resumePoint agent nb (resumeOld p.name captured answered)).toVal ::
        resumeEnv log p.name agent nb captured answered response req state env)
      (eqData (keyTy ld) (.get (.var 1) "key")
        (activityKeyTerm (.get (.var 3) "agent") (.get (.var 3) "notBefore")))
      (.ok (.bool true)))
    (hresume : BigStep lib
      (captured.toVal :: (resumeOld p.name captured answered).toVal ::
        (resumePoint agent nb (resumeOld p.name captured answered)).toVal ::
        resumeEnv log p.name agent nb captured answered response req state env)
      (activityApply p.resume [.var 5, .var 0, .get (.var 4) "response", .var 3]) (.ok result)) :
    BigStep lib
      (req :: (resumeArg agent nb response).toVal :: state ::
        (resumeRows log (resumePoint agent nb (resumeOld p.name captured answered))).toVal :: env)
      (.get (activityApply (activityResumeMethod S rels cursor log cd ld resumer plans p)
        [.var 3, .var 2, .var 1, .var 0]) "state") (.ok result) := by
  let old := resumeOld p.name captured answered
  let point := resumePoint agent nb old
  let e := resumeEnv log p.name agent nb captured answered response req state env
  apply BigStep.get
  · unfold activityApply activityResumeMethod activityMethod
    simp only [List.foldl]
    apply BigStep.app
      (BigStep.app (BigStep.app (BigStep.app .lam (.var rfl) .lam) (.var rfl) .lam) (.var rfl) .lam)
      (.var rfl)
    apply BigStep.iteT hres
    refine BigStep.case (ℓ := "some") (w := point.toVal) ?_ rfl ?_
    · exact .get (.get (.var rfl) (.field (t := .var 0) (env := [(Data.record [("p0", .inj "some" point)]).toVal])
          (by simp [Data.rowToVal, Row.find?, point, old]) (.var rfl)))
        (.field rfl (.var rfl))
    refine BigStep.case (ℓ := "some") (w := old.toVal) ?_ rfl ?_
    · exact .get (.var rfl) (.field rfl (.var rfl))
    apply BigStep.iteT hkey
    apply BigStep.case (ℓ := p.name) (w := captured.toVal)
      (body := activityResumeResult rels cursor log cd ld plans p)
    · exact .get (.var rfl) (.field rfl (.var rfl))
    · simpa only [↓reduceIte] using find_plan hp (fun l =>
        if l = p.name then activityResumeResult rels cursor log cd ld plans p
        else .refuse (resultTy S [] (editTy rels) 2) "wrongPlan".toUTF8)
    · exact .record
  · exact .field rfl hresume

end Nanodregg.Lang.Std
