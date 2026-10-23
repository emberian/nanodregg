/-
# Lang.Proofs.StdOffer — what the generated offer judge, its take and its matcher decide (PROT-6)

Every theorem here is about a term `Lang.StdOffer` generates, by its `BigStep` meaning, or about
`Lang.program`'s `run` of the generated package:

* `offerJoint_meaning` / `offerJoint_total` (term grain): the joint judge `offerJoint` says
  `sameRole`, `ok` (exactly `JointOk`: different roles, θ inside BOTH boxes) or `notCompliant`.
* `take_iff_compliant` (method-term grain, as the receiver applies it): with both offer slots
  present, the take returns iff `JointOk` of the two pinned offers and the θ it decoded. The
  matcher's code is not a premise. Its refusals by name: `take_offerUnpinned`, `take_noOffer`,
  `take_peerRowUnpinned`, `take_noPeerOffer`, `take_sameRole`, `take_notCompliant`.
* `take_run_sound` (the deployed run): a returned take decoded `{pair, theta}`, read both pinned
  offers, found them `JointOk`, makes no calls, and its row acts are exactly its own offer's retract
  and its own session insert.
* `fuse_calls` (the deployed run): a returned fuse makes exactly the two `take` invokes, carrying the
  SAME `deal` bytes, and edits nothing. The one θ is the matcher's property, not the takes'.
* `fuse_refused_disjoint`: buyer `[5,10]` and seller `[11,12]` over `["price"]` have no common θ, and
  the take term refuses that pair `notCompliant` at every θ.

The run-grain converse of `take_run_sound` is not here: the tree has no completeness lemma for the
machine at the deployed `Bounds.stackMax` (`bigStep_run` gives an existential stack bound) nor for
extraction (`forces_le` is the other direction).
-/
import Lang.StdOffer
import Lang.Proofs.StdActivityMonitor
import Lang.Proofs.Extract
import Lang.Proofs.Invoke

namespace Nanodregg.Lang.Std

open Nanodregg.Lang

/-- θ is inside box `terms` at every label of `fs`. -/
def InBox (fs : List Label) (terms th : Data) : Prop :=
  ∀ f ∈ fs, ∃ lo hi t, terms.field f = some (.record [("hi", .nat hi), ("lo", .nat lo)]) ∧
    th.field f = some (.nat t) ∧ lo ≤ t ∧ t ≤ hi

/-- What `offerJoint` decides: two different chooser roles, θ inside both boxes. -/
def JointOk (fs : List Label) (o q th : Data) : Prop :=
  o.field "role" ≠ q.field "role" ∧
  (∃ ot, o.field "terms" = some ot ∧ InBox fs ot th) ∧ (∃ qt, q.field "terms" = some qt ∧ InBox fs qt th)

/-! ## Data in the environment, forward -/

private theorem find_rowToVal_of {ℓ : Label} : ∀ {fs : List (Label × Data)} {x : Data},
    Row.find? ℓ fs = some x → Row.find? ℓ (Data.rowToVal fs) = some (.var 0, [x.toVal])
  | [], _, h => by simp [Row.find?] at h
  | (k, d) :: fs, x, h => by
    by_cases hk : ℓ = k
    · subst hk; simp only [Row.find?, if_true, Option.some.injEq] at h; subst h
      simp [Data.rowToVal, Row.find?]
    · simp only [Row.find?, hk, if_false] at h
      simp only [Data.rowToVal, Row.find?, hk, if_false]
      exact find_rowToVal_of h

private theorem get_data {lib : List Term} {env : Env} {t : Term} {d x : Data} {ℓ : Label}
    (ht : BigStep lib env t (.ok d.toVal)) (hf : d.field ℓ = some x) :
    BigStep lib env (.get t ℓ) (.ok x.toVal) := by
  cases d with
  | record fs => exact .get ht (.field (find_rowToVal_of hf) (.var rfl))
  | _ => simp [Data.field] at hf

private theorem andT_eval {lib : List Term} {env : Env} {a b : Term} {x y : Bool}
    (ha : BigStep lib env a (.ok (.bool x))) (hb : BigStep lib env b (.ok (.bool y))) :
    BigStep lib env (andT a b) (.ok (.bool (x && y))) := by
  cases x
  · exact .iteF ha .bool
  · exact .iteT ha hb

/-! ## The labels and the conforming shapes -/

private theorem sort_labels (theta : List Label) {α : Type} (a : α) :
    Row.sort (theta.map (·, a)) = (offerLabels theta).map (·, a) := by
  unfold offerLabels
  rw [List.map_map]
  have h := Row.sort_map (fun p : Label × Unit => (p.1, a)) (fun _ => rfl) (theta.map (·, ()))
  rw [List.map_map] at h
  exact h.symm

private theorem find_labels_const {α : Type} {a : α} {f : Label} :
    ∀ {fs : List Label}, f ∈ fs → Row.find? f (fs.map (·, a)) = some a
  | [], h => by cases h
  | g :: fs, h => by
    by_cases hg : f = g
    · simp [Row.find?, hg]
    · simp only [List.map_cons, Row.find?, hg, if_false]
      exact find_labels_const ((List.mem_cons.mp h).resolve_left hg)

private theorem conform_find {ds : List (Label × Data)} {r : List (Label × Ty)}
    (hd : RowConforms ds r) {l : Label} {T : Ty} (hf : Row.find? l r = some T) :
    ∃ d, Row.find? l ds = some d ∧ Conforms d T := by
  induction r generalizing ds with
  | nil => simp [Row.find?] at hf
  | cons p r ih =>
    rcases p with ⟨k, A⟩
    cases hd with
    | cons h hr =>
      rename_i d ds
      by_cases hk : l = k
      · subst hk; simp only [Row.find?, if_true, Option.some.injEq] at hf ⊢; subst hf; exact ⟨d, rfl, h⟩
      · simp only [Row.find?, hk, if_false] at hf ⊢; exact ih hr hf

/-- A conforming θ holds a natural at every label. -/
private theorem theta_shape {theta : List Label} {th : Data} (h : Conforms th (offerThetaTy theta))
    {f : Label} (hf : f ∈ offerLabels theta) : ∃ t, th.field f = some (.nat t) := by
  unfold offerThetaTy at h
  rw [sort_labels] at h
  cases h with
  | record hr =>
    obtain ⟨d, hd, hc⟩ := conform_find hr (find_labels_const hf)
    cases hc with
    | nat _ => exact ⟨_, hd⟩

/-- A conforming box holds an interval of naturals at every label. -/
private theorem terms_shape {theta : List Label} {ot : Data} (h : Conforms ot (offerTermsTy theta))
    {f : Label} (hf : f ∈ offerLabels theta) :
    ∃ lo hi, ot.field f = some (.record [("hi", .nat hi), ("lo", .nat lo)]) := by
  unfold offerTermsTy at h
  rw [sort_labels] at h
  cases h with
  | record hr =>
    obtain ⟨d, hd, hc⟩ := conform_find hr (find_labels_const hf)
    unfold offerBoxTy at hc
    cases hc with
    | record hr' =>
      cases hr' with
      | cons h1 hr' => cases hr' with
        | cons h2 hr' =>
          cases hr'; cases h1; cases h2
          exact ⟨_, _, hd⟩

/-! ## `offerInBox`, by induction over the labels -/

private theorem inBox_eval {lib : List Term} {env : Env} {terms thT : Term} {ot th : Data}
    (hterms : BigStep lib env terms (.ok ot.toVal)) (hth : BigStep lib env thT (.ok th.toVal)) :
    ∀ fs : List Label, (∀ f ∈ fs, (∃ lo hi, ot.field f = some (.record [("hi", .nat hi), ("lo", .nat lo)])) ∧
      ∃ t, th.field f = some (.nat t)) →
    ∃ b, BigStep lib env (offerInBox fs terms thT) (.ok (.bool b)) ∧ (b = true ↔ InBox fs ot th)
  | [], _ => ⟨true, .bool, by simp [InBox]⟩
  | f :: fs, hs => by
    obtain ⟨⟨lo, hi, hb⟩, t, ht⟩ := hs f (by simp)
    obtain ⟨c, hc, hci⟩ := inBox_eval hterms hth fs (fun g hg => hs g (by simp [hg]))
    have hbox := get_data hterms hb
    have hlo : BigStep lib env (.get (.get terms f) "lo") (.ok (Data.nat lo).toVal) :=
      get_data (d := .record [("hi", .nat hi), ("lo", .nat lo)]) (ℓ := "lo") (x := .nat lo) hbox rfl
    have hhi : BigStep lib env (.get (.get terms f) "hi") (.ok (Data.nat hi).toVal) :=
      get_data (d := .record [("hi", .nat hi), ("lo", .nat lo)]) (ℓ := "hi") (x := .nat hi) hbox rfl
    have htf : BigStep lib env (.get thT f) (.ok (Data.nat t).toVal) := get_data hth ht
    have h1 : BigStep lib env (.prim .le (.get (.get terms f) "lo") (.get thT f))
        (.ok (.bool (decide (lo ≤ t)))) :=
      BigStep.prim (x := .nat lo) (y := .nat t) hlo htf (by simp [primEval])
    have h2 : BigStep lib env (.prim .le (.get thT f) (.get (.get terms f) "hi"))
        (.ok (.bool (decide (t ≤ hi)))) :=
      BigStep.prim (x := .nat t) (y := .nat hi) htf hhi (by simp [primEval])
    refine ⟨(decide (lo ≤ t) && decide (t ≤ hi)) && c, andT_eval (andT_eval h1 h2) hc, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, hci]
    constructor
    · rintro ⟨⟨hl1, hl2⟩, hl3⟩ g hg
      rcases List.mem_cons.mp hg with hgf | hg
      · subst hgf; exact ⟨lo, hi, t, hb, ht, hl1, hl2⟩
      · exact hl3 g hg
    · intro h
      obtain ⟨lo', hi', t', hb', ht', h1, h2⟩ := h f (by simp)
      rw [hb] at hb'; rw [ht] at ht'
      have e1 : hi = hi' ∧ lo = lo' := by simpa using hb'
      have e2 : t = t' := by simpa using ht'
      obtain ⟨rfl, rfl⟩ := e1; subst e2
      exact ⟨⟨h1, h2⟩, fun g hg => h g (by simp [hg])⟩

/-! ## The joint judge -/

/-- An offer value, conforming, is a role and a box. -/
private theorem offer_shape {theta roles : List Label} {o : Data} (h : Conforms o (offerValTy theta roles)) :
    ∃ ro ot, o = .record [("role", ro), ("terms", ot)] ∧ Conforms ro (offerRoleTy roles) ∧
      Conforms ot (offerTermsTy theta) := by
  cases h with
  | record hr =>
    cases hr with
    | cons h1 hr => cases hr with
      | cons h2 hr => cases hr; exact ⟨_, _, rfl, h1, h2⟩

/-- The judge's evaluation, over any environment in which its three operands mean `o`, `q`, `θ`. -/
private theorem joint_eval {theta roles : List Label} {lib : List Term} {E : Env} {a b c : Term}
    {o q th : Data} (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (offerValTy theta roles)) (hq : Conforms q (offerValTy theta roles))
    (hth : Conforms th (offerThetaTy theta))
    (ha : BigStep lib E a (.ok o.toVal)) (hb : BigStep lib E b (.ok q.toVal))
    (hc : BigStep lib E c (.ok th.toVal)) :
    ∃ v, BigStep lib E (activityApply (offerJoint theta roles) [a, b, c]) (.ok v) ∧
      ((o.field "role" = q.field "role" ∧ v = .inj "refused" (.bytes "sameRole".toUTF8)) ∨
       (JointOk (offerLabels theta) o q th ∧ v = .inj "ok" (.record [])) ∨
       (o.field "role" ≠ q.field "role" ∧ ¬ JointOk (offerLabels theta) o q th ∧
         v = .inj "refused" (.bytes "notCompliant".toUTF8))) := by
  obtain ⟨ro, ot, rfl, hro, hot⟩ := offer_shape ho
  obtain ⟨rq, qt, rfl, hrq, hqt⟩ := offer_shape hq
  let O := Data.record [("role", ro), ("terms", ot)]
  let Q := Data.record [("role", rq), ("terms", qt)]
  let Eb := th.toVal :: Q.toVal :: O.toVal :: E
  suffices hbody : ∃ v, BigStep lib Eb
      (.ite (eqData (offerRoleTy roles) (.get (.var 2) "role") (.get (.var 1) "role"))
        (refusedT "sameRole")
        (.ite (andT (offerInBox (offerLabels theta) (.get (.var 2) "terms") (.var 0))
            (offerInBox (offerLabels theta) (.get (.var 1) "terms") (.var 0)))
          okT (refusedT "notCompliant"))) (.ok v) ∧
      ((O.field "role" = Q.field "role" ∧ v = .inj "refused" (.bytes "sameRole".toUTF8)) ∨
       (JointOk (offerLabels theta) O Q th ∧ v = .inj "ok" (.record [])) ∨
       (O.field "role" ≠ Q.field "role" ∧ ¬ JointOk (offerLabels theta) O Q th ∧
         v = .inj "refused" (.bytes "notCompliant".toUTF8))) by
    obtain ⟨v, hv, hd⟩ := hbody
    exact ⟨v, by
      unfold activityApply offerJoint
      simp only [List.foldl]
      exact .app (.app (.app .lam ha .lam) hb .lam) hc hv, hd⟩
  have hO : BigStep lib Eb (.var 2) (.ok O.toVal) := .var rfl
  have hQ : BigStep lib Eb (.var 1) (.ok Q.toVal) := .var rfl
  have hT : BigStep lib Eb (.var 0) (.ok th.toVal) := .var rfl
  have hxo := get_data (ℓ := "role") (x := ro) hO rfl
  have hxq := get_data (ℓ := "role") (x := rq) hQ rfl
  obtain ⟨same, hs, hsi⟩ := eqDataBody_meaning (lib := lib) (env := Eb) (offerRoleTy roles) hR hro hrq
  have heq : BigStep lib Eb (eqData (offerRoleTy roles) (.get (.var 2) "role") (.get (.var 1) "role"))
      (.ok (.bool same)) := .app (.app .lam hxo .lam) hxq hs
  have hfO : O.field "role" = Q.field "role" ↔ ro = rq := by
    simp [O, Q, Data.field, Row.find?]
  cases same with
  | true =>
    refine ⟨_, .iteT heq (.inj .bytes), .inl ⟨hfO.mpr (hsi.mp rfl), rfl⟩⟩
  | false =>
    have hne : O.field "role" ≠ Q.field "role" := fun h => by simpa using hsi.mpr (hfO.mp h)
    have hshape : ∀ (ut : Data), Conforms ut (offerTermsTy theta) →
        ∀ f ∈ offerLabels theta, (∃ lo hi, ut.field f = some (.record [("hi", .nat hi), ("lo", .nat lo)])) ∧
          ∃ t, th.field f = some (.nat t) := fun ut hu f hf => ⟨terms_shape hu hf, theta_shape hth hf⟩
    obtain ⟨b1, hb1, hb1i⟩ := inBox_eval (get_data (ℓ := "terms") (x := ot) hO rfl) hT (offerLabels theta) (hshape ot hot)
    obtain ⟨b2, hb2, hb2i⟩ := inBox_eval (get_data (ℓ := "terms") (x := qt) hQ rfl) hT (offerLabels theta) (hshape qt hqt)
    have hand := andT_eval hb1 hb2
    have hj : JointOk (offerLabels theta) O Q th ↔ (b1 && b2) = true := by
      simp only [JointOk, Bool.and_eq_true, hb1i, hb2i]
      have hne' : ro ≠ rq := fun h => hne (hfO.mpr h)
      simp [O, Q, Data.field, Row.find?, hne']
    cases hbb : (b1 && b2) with
    | true =>
      rw [hbb] at hand
      exact ⟨_, .iteF heq (.iteT hand (.inj .record)), .inr (.inl ⟨hj.mpr hbb, rfl⟩)⟩
    | false =>
      rw [hbb] at hand
      exact ⟨_, .iteF heq (.iteF hand (.inj .bytes)),
        .inr (.inr ⟨hne, fun h => by simpa [hbb] using hj.mp h, rfl⟩)⟩

/-- **The joint judge's meaning** (term grain, the generated `offerJoint`): applied to two conforming
offers `o` (own) and `q` (peer) and a conforming θ, it returns `refused "sameRole"` exactly when the
two chooser roles are equal, `ok` exactly when `JointOk` (different roles, θ inside BOTH boxes),
and otherwise `refused "notCompliant"`. Mutations that falsify it: dropping the PEER's
`offerInBox` (different roles, own box `[5,10]`, peer box `[8,12]`, θ = 6: inside the own box,
outside the peer's, the mutant says `ok` where `JointOk` is false; not the both-boxes-fail row F2),
and swapping the two refusal names. -/
theorem offerJoint_meaning {theta roles : List Label} {lib : List Term} {env : Env} {o q th : Data}
    {v : Val} (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (offerValTy theta roles)) (hq : Conforms q (offerValTy theta roles))
    (hth : Conforms th (offerThetaTy theta))
    (h : BigStep lib (th.toVal :: q.toVal :: o.toVal :: env)
      (activityApply (offerJoint theta roles) [.var 2, .var 1, .var 0]) (.ok v)) :
    (o.field "role" = q.field "role" ∧ v = .inj "refused" (.bytes "sameRole".toUTF8)) ∨
    (JointOk (offerLabels theta) o q th ∧ v = .inj "ok" (.record [])) ∨
    (o.field "role" ≠ q.field "role" ∧ ¬ JointOk (offerLabels theta) o q th ∧
      v = .inj "refused" (.bytes "notCompliant".toUTF8)) := by
  obtain ⟨w, hw, hd⟩ := joint_eval hR ho hq hth (BigStep.var (i := 2) rfl) (BigStep.var (i := 1) rfl) (BigStep.var (i := 0) rfl)
    (lib := lib) (E := th.toVal :: q.toVal :: o.toVal :: env)
  have he := bigStep_deterministic h hw
  cases he
  exact hd

/-- The joint judge is total on conforming operands. -/
theorem offerJoint_total {theta roles : List Label} {lib : List Term} {env : Env} {o q th : Data}
    (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (offerValTy theta roles)) (hq : Conforms q (offerValTy theta roles))
    (hth : Conforms th (offerThetaTy theta)) :
    ∃ v, BigStep lib (th.toVal :: q.toVal :: o.toVal :: env)
      (activityApply (offerJoint theta roles) [.var 2, .var 1, .var 0]) (.ok v) := by
  obtain ⟨w, hw, -⟩ := joint_eval hR ho hq hth (BigStep.var (i := 2) rfl) (BigStep.var (i := 1) rfl) (BigStep.var (i := 0) rfl)
    (lib := lib) (E := th.toVal :: q.toVal :: o.toVal :: env)
  exact ⟨w, hw⟩

/-! ## The take, at the method term's grain -/

/-- `take`'s rows argument: its own offer slot and its peer's. -/
private def takeRows (own peer : Data) : Data :=
  .record [("offer", .record [("p0", own)]), ("peer", .record [("offer", .record [("p0", peer)])])]

/-- A pinned point: its key and its row's value, if any. -/
private def pointD (k : Data) (v : Option Data) : Data := .record [("key", k), ("val", optD v)]

/-- The take's argument. -/
private def takeArg (pair th : Data) : Data := .record [("pair", pair), ("theta", th)]

/-- The env the take body runs in (var 0 req, var 1 arg, var 2 state, var 3 rows). -/
private abbrev bodyEnv (req state : Val) (arg rows : Data) (E : Env) : Env :=
  req :: arg.toVal :: state :: rows.toVal :: E

/-- The verdict's `ok` arm's env: payload, peer value, peer point, own value, own point, then the body env. -/
private abbrev okEnv (req state : Val) (pair th k o kq q : Data) (E : Env) : Env :=
  .record [] :: q.toVal :: (pointD kq (some q)).toVal :: o.toVal :: (pointD k (some o)).toVal ::
    bodyEnv req state (takeArg pair th) (takeRows (.inj "some" (pointD k (some o))) (.inj "some" (pointD kq (some q)))) E

/-- The take's success term, as `offerTakeBody` writes it. -/
private abbrev doneT (theta : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl) : Term :=
  activityResult rels (.var 7) [
    activityEdit rels "offer" od "retract" (.get (.var 4) "key"),
    activityEdit rels "session" sd "insert"
      (activityKeyTerm (.get (.var 5) "agent") (.get (.var 5) "notBefore"))
      (.record [("answered", noCallT (activityResponses [offerSettlePlan theta])),
        ("captured", .inj (activityCaptured [offerSettlePlan theta]) "settle"
          (.record [("pair", .get (.var 6) "pair"), ("theta", .get (.var 6) "theta")]))])]

private theorem rows_own {lib : List Term} {req state : Val} {arg own peer : Data} {E : Env} :
    BigStep lib (bodyEnv req state arg (takeRows own peer) E) (.get (.get (.var 3) "offer") "p0")
      (.ok own.toVal) :=
  get_data (ℓ := "p0") (x := own) (get_data (ℓ := "offer") (x := .record [("p0", own)])
    (BigStep.var (i := 3) rfl) rfl) rfl

private theorem body_offerUnpinned {theta roles : List Label} {rels : List (Label × RelDecl)}
    {od sd : RelDecl} {lib : List Term} {req state : Val} {arg peer : Data} {E : Env} :
    BigStep lib (bodyEnv req state arg (takeRows (optD none) peer) E) (offerTakeBody theta roles rels od sd)
      (.error (.refused "offerUnpinned".toUTF8)) := by
  unfold offerTakeBody; dsimp only
  exact .case rows_own rfl .refuse

private theorem body_noOffer {theta roles : List Label} {rels : List (Label × RelDecl)}
    {od sd : RelDecl} {lib : List Term} {req state : Val} {arg peer k : Data} {E : Env} :
    BigStep lib (bodyEnv req state arg (takeRows (.inj "some" (pointD k none)) peer) E)
      (offerTakeBody theta roles rels od sd) (.error (.refused "noOffer".toUTF8)) := by
  unfold offerTakeBody; dsimp only
  refine .case rows_own rfl ?_
  exact .case (get_data (ℓ := "val") (x := optD none) (BigStep.var (i := 0) rfl) rfl) rfl .refuse

/-- The peer slot, inside the own offer's two arms. -/
private theorem rows_peer {lib : List Term} {req state : Val} {arg k o peer : Data} {E : Env} :
    BigStep lib (o.toVal :: (pointD k (some o)).toVal ::
        bodyEnv req state arg (takeRows (.inj "some" (pointD k (some o))) peer) E)
      (.get (.get (.get (.var 5) "peer") "offer") "p0") (.ok peer.toVal) :=
  get_data (ℓ := "p0") (x := peer) (get_data (ℓ := "offer") (x := .record [("p0", peer)])
    (get_data (ℓ := "peer") (x := .record [("offer", .record [("p0", peer)])]) (BigStep.var (i := 5) rfl) rfl)
    rfl) rfl

private theorem body_peerRowUnpinned {theta roles : List Label} {rels : List (Label × RelDecl)}
    {od sd : RelDecl} {lib : List Term} {req state : Val} {arg k o : Data} {E : Env} :
    BigStep lib (bodyEnv req state arg (takeRows (.inj "some" (pointD k (some o))) (optD none)) E)
      (offerTakeBody theta roles rels od sd) (.error (.refused "peerRowUnpinned".toUTF8)) := by
  unfold offerTakeBody; dsimp only
  refine .case rows_own rfl ?_
  refine .case (get_data (ℓ := "val") (x := optD (some o)) (BigStep.var (i := 0) rfl) rfl) rfl ?_
  exact .case rows_peer rfl .refuse

private theorem body_noPeerOffer {theta roles : List Label} {rels : List (Label × RelDecl)}
    {od sd : RelDecl} {lib : List Term} {req state : Val} {arg k o kq : Data} {E : Env} :
    BigStep lib (bodyEnv req state arg (takeRows (.inj "some" (pointD k (some o))) (.inj "some" (pointD kq none))) E)
      (offerTakeBody theta roles rels od sd) (.error (.refused "noPeerOffer".toUTF8)) := by
  unfold offerTakeBody; dsimp only
  refine .case rows_own rfl ?_
  refine .case (get_data (ℓ := "val") (x := optD (some o)) (BigStep.var (i := 0) rfl) rfl) rfl ?_
  refine .case rows_peer rfl ?_
  exact .case (get_data (ℓ := "val") (x := optD none) (BigStep.var (i := 0) rfl) rfl) rfl .refuse

/-- The judge's env inside the take: peer value, peer point, own value, own point, then the body env. -/
private abbrev judgeEnv (req state : Val) (pair th k o kq q : Data) (E : Env) : Env :=
  q.toVal :: (pointD kq (some q)).toVal :: o.toVal :: (pointD k (some o)).toVal ::
    bodyEnv req state (takeArg pair th) (takeRows (.inj "some" (pointD k (some o))) (.inj "some" (pointD kq (some q)))) E

private abbrev bothRows (k o kq q : Data) : Data :=
  takeRows (.inj "some" (pointD k (some o))) (.inj "some" (pointD kq (some q)))

private theorem body_ok {theta roles : List Label} {rels : List (Label × RelDecl)}
    {od sd : RelDecl} {lib : List Term} {req state : Val} {pair th k o kq q : Data} {E : Env}
    {r : Except Fault Val}
    (hj : BigStep lib (judgeEnv req state pair th k o kq q E)
      (activityApply (offerJoint theta roles) [.var 2, .var 0, .get (.var 5) "theta"]) (.ok (.inj "ok" (.record []))))
    (hd : BigStep lib (okEnv req state pair th k o kq q E) (doneT theta rels od sd) r) :
    BigStep lib (bodyEnv req state (takeArg pair th) (bothRows k o kq q) E)
      (offerTakeBody theta roles rels od sd) r := by
  unfold offerTakeBody; dsimp only
  refine .case rows_own rfl ?_
  refine .case (get_data (ℓ := "val") (x := optD (some o)) (BigStep.var (i := 0) rfl) rfl) rfl ?_
  refine .case rows_peer rfl ?_
  refine .case (get_data (ℓ := "val") (x := optD (some q)) (BigStep.var (i := 0) rfl) rfl) rfl ?_
  exact .case hj rfl hd

private theorem body_refused {theta roles : List Label} {rels : List (Label × RelDecl)}
    {od sd : RelDecl} {lib : List Term} {req state : Val} {pair th k o kq q : Data} {E : Env}
    {why : String} (hw : why = "sameRole" ∨ why = "notCompliant")
    (hj : BigStep lib (judgeEnv req state pair th k o kq q E)
      (activityApply (offerJoint theta roles) [.var 2, .var 0, .get (.var 5) "theta"])
      (.ok (.inj "refused" (.bytes why.toUTF8)))) :
    BigStep lib (bodyEnv req state (takeArg pair th) (bothRows k o kq q) E)
      (offerTakeBody theta roles rels od sd) (.error (.refused why.toUTF8)) := by
  unfold offerTakeBody; dsimp only
  refine .case rows_own rfl ?_
  refine .case (get_data (ℓ := "val") (x := optD (some o)) (BigStep.var (i := 0) rfl) rfl) rfl ?_
  refine .case rows_peer rfl ?_
  refine .case (get_data (ℓ := "val") (x := optD (some q)) (BigStep.var (i := 0) rfl) rfl) rfl ?_
  refine .case hj rfl ?_
  rcases hw with rfl | rfl
  · have hb := BigStep.prim (lib := lib) (p := .beq) (x := .bytes "sameRole".toUTF8) (y := .bytes "sameRole".toUTF8)
      (a := .var 0) (b := .bytes "sameRole".toUTF8)
      (env := Val.bytes "sameRole".toUTF8 :: judgeEnv req state pair th k o kq q E) (.var rfl) .bytes
      (by simp [primEval])
    have he : primEval .beq (.bytes "sameRole".toUTF8) (.bytes "sameRole".toUTF8) = .ok (.bool true) := by
      simp [primEval]
    rw [he] at hb
    exact .iteT hb .refuse
  · have hb := BigStep.prim (lib := lib) (p := .beq) (x := .bytes "notCompliant".toUTF8) (y := .bytes "sameRole".toUTF8)
      (a := .var 0) (b := .bytes "sameRole".toUTF8)
      (env := Val.bytes "notCompliant".toUTF8 :: judgeEnv req state pair th k o kq q E) (.var rfl) .bytes
      (by simp [primEval])
    have he : primEval .beq (.bytes "notCompliant".toUTF8) (.bytes "sameRole".toUTF8) = .ok (.bool false) := by
      simp [primEval]; decide
    rw [he] at hb
    exact .iteF hb .refuse

/-- The judge inside the take sees the own value, the peer's, and the decoded θ. -/
private theorem judge_in_take {theta roles : List Label} {lib : List Term} {req state : Val}
    {pair th k o kq q : Data} {E : Env} (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (offerValTy theta roles)) (hq : Conforms q (offerValTy theta roles))
    (hth : Conforms th (offerThetaTy theta)) :
    ∃ v, BigStep lib (judgeEnv req state pair th k o kq q E)
      (activityApply (offerJoint theta roles) [.var 2, .var 0, .get (.var 5) "theta"]) (.ok v) ∧
      ((o.field "role" = q.field "role" ∧ v = .inj "refused" (.bytes "sameRole".toUTF8)) ∨
       (JointOk (offerLabels theta) o q th ∧ v = .inj "ok" (.record [])) ∨
       (o.field "role" ≠ q.field "role" ∧ ¬ JointOk (offerLabels theta) o q th ∧
         v = .inj "refused" (.bytes "notCompliant".toUTF8))) :=
  joint_eval hR ho hq hth (BigStep.var (i := 2) rfl) (BigStep.var (i := 0) rfl)
    (get_data (ℓ := "theta") (x := th) (BigStep.var (i := 5) rfl) rfl)

/-- The method term, applied as the receiver applies it, runs its body over `[req, arg, state, rows]`. -/
private theorem method_app {S A R : Ty} {body : Term} {lib : List Term} {req state : Val} {arg rows : Data}
    {env : Env} {r : Except Fault Val}
    (h : BigStep lib (bodyEnv req state arg rows (req :: arg.toVal :: state :: rows.toVal :: env)) body r) :
    BigStep lib (req :: arg.toVal :: state :: rows.toVal :: env)
      (activityApply (activityMethod S A R body) [.var 3, .var 2, .var 1, .var 0]) r := by
  unfold activityApply activityMethod
  simp only [List.foldl]
  exact .app (.app (.app (.app .lam (.var rfl) .lam) (.var rfl) .lam) (.var rfl) .lam) (.var rfl) h

/-- **Each party's honesty** (method-term grain, the generated `take` as the receiver applies it,
over the env `[req, arg, state, rows]` it builds): with both offer slots pinned and present (own
point `k`/`o`, peer point `kq`/`q`) and the argument `{pair, theta := th}`, the take returns iff
`JointOk`: it judges the pair itself, whoever called it. The matcher's code is not a premise.
Mutation P2 (`take` without the judge: the `ok` arm taken unconditionally) makes it false at F2
(buyer `[5,10]`, seller `[11,12]`, θ = 11: the mutant returns, `JointOk` is false). -/
theorem take_iff_compliant {theta roles : List Label} {rels : List (Label × RelDecl)} {od sd : RelDecl}
    {lib : List Term} {env : Env} {req state : Val} {pair th k o kq q : Data}
    (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (offerValTy theta roles)) (hq : Conforms q (offerValTy theta roles))
    (hth : Conforms th (offerThetaTy theta)) :
    (∃ v, BigStep lib (req :: (Data.record [("pair", pair), ("theta", th)]).toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
          env)
      (activityApply (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels)
        (offerTakeBody theta roles rels od sd)) [.var 3, .var 2, .var 1, .var 0]) (.ok v)) ↔
    JointOk (offerLabels theta) o q th := by
  obtain ⟨v, hv, hd⟩ := judge_in_take (lib := lib) (req := req) (state := state) (pair := pair) (k := k)
    (kq := kq) (E := req :: (takeArg pair th).toVal :: state :: (bothRows k o kq q).toVal :: env) hR ho hq hth
  constructor
  · rintro ⟨w, hw⟩
    rcases hd with ⟨-, rfl⟩ | ⟨hok, -⟩ | ⟨-, -, rfl⟩
    · have := bigStep_deterministic hw (method_app (body_refused (rels := rels) (od := od) (sd := sd) (.inl rfl) hv))
      cases this
    · exact hok
    · have := bigStep_deterministic hw (method_app (body_refused (rels := rels) (od := od) (sd := sd) (.inr rfl) hv))
      cases this
  · intro hok
    rcases hd with ⟨hr, -⟩ | ⟨-, rfl⟩ | ⟨-, hn, -⟩
    · exact absurd hr hok.1
    · exact ⟨_, method_app (body_ok (rels := rels) (od := od) (sd := sd) hv .record)⟩
    · exact absurd hok hn

/-! ### The take's refusals, by name (method-term grain) -/

/-- Own offer slot unpinned: `offerUnpinned`. -/
theorem take_offerUnpinned {theta roles : List Label} {rels : List (Label × RelDecl)} {od sd : RelDecl}
    {lib : List Term} {env : Env} {req state : Val} {arg peer : Data} :
    BigStep lib (req :: arg.toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "none" (.record []))]),
          ("peer", .record [("offer", .record [("p0", peer)])])]).toVal :: env)
      (activityApply (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels)
        (offerTakeBody theta roles rels od sd)) [.var 3, .var 2, .var 1, .var 0])
      (.error (.refused "offerUnpinned".toUTF8)) :=
  method_app (rows := takeRows (optD none) peer) body_offerUnpinned

/-- Own offer slot pinned absent: `noOffer`. -/
theorem take_noOffer {theta roles : List Label} {rels : List (Label × RelDecl)} {od sd : RelDecl}
    {lib : List Term} {env : Env} {req state : Val} {arg k peer : Data} :
    BigStep lib (req :: arg.toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "none" (.record []))]))]),
          ("peer", .record [("offer", .record [("p0", peer)])])]).toVal :: env)
      (activityApply (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels)
        (offerTakeBody theta roles rels od sd)) [.var 3, .var 2, .var 1, .var 0])
      (.error (.refused "noOffer".toUTF8)) :=
  method_app (rows := takeRows (.inj "some" (pointD k none)) peer) body_noOffer

/-- Peer offer slot unpinned: `peerRowUnpinned`. -/
theorem take_peerRowUnpinned {theta roles : List Label} {rels : List (Label × RelDecl)} {od sd : RelDecl}
    {lib : List Term} {env : Env} {req state : Val} {arg k o : Data} :
    BigStep lib (req :: arg.toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "none" (.record []))])])]).toVal :: env)
      (activityApply (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels)
        (offerTakeBody theta roles rels od sd)) [.var 3, .var 2, .var 1, .var 0])
      (.error (.refused "peerRowUnpinned".toUTF8)) :=
  method_app (rows := takeRows (.inj "some" (pointD k (some o))) (optD none)) body_peerRowUnpinned

/-- Peer offer slot pinned absent: `noPeerOffer`. -/
theorem take_noPeerOffer {theta roles : List Label} {rels : List (Label × RelDecl)} {od sd : RelDecl}
    {lib : List Term} {env : Env} {req state : Val} {arg k o kq : Data} :
    BigStep lib (req :: arg.toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "none" (.record []))]))])])]).toVal :: env)
      (activityApply (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels)
        (offerTakeBody theta roles rels od sd)) [.var 3, .var 2, .var 1, .var 0])
      (.error (.refused "noPeerOffer".toUTF8)) :=
  method_app (rows := takeRows (.inj "some" (pointD k (some o))) (.inj "some" (pointD kq none))) body_noPeerOffer

/-- Both offers present, equal chooser roles: `sameRole`. Mutation: the two refusal names swapped. -/
theorem take_sameRole {theta roles : List Label} {rels : List (Label × RelDecl)} {od sd : RelDecl}
    {lib : List Term} {env : Env} {req state : Val} {pair th k o kq q : Data}
    (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (offerValTy theta roles)) (hq : Conforms q (offerValTy theta roles))
    (hth : Conforms th (offerThetaTy theta)) (hr : o.field "role" = q.field "role") :
    BigStep lib (req :: (Data.record [("pair", pair), ("theta", th)]).toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
          env)
      (activityApply (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels)
        (offerTakeBody theta roles rels od sd)) [.var 3, .var 2, .var 1, .var 0])
      (.error (.refused "sameRole".toUTF8)) := by
  obtain ⟨v, hv, hd⟩ := judge_in_take (lib := lib) (req := req) (state := state) (pair := pair) (k := k)
    (kq := kq) (E := req :: (takeArg pair th).toVal :: state :: (bothRows k o kq q).toVal :: env) hR ho hq hth
  rcases hd with ⟨-, rfl⟩ | ⟨hok, -⟩ | ⟨hn, -, -⟩
  · exact method_app (body_refused (.inl rfl) hv)
  · exact absurd hr hok.1
  · exact absurd hr hn

/-- Both offers present, different roles, θ outside a box: `notCompliant`. -/
theorem take_notCompliant {theta roles : List Label} {rels : List (Label × RelDecl)} {od sd : RelDecl}
    {lib : List Term} {env : Env} {req state : Val} {pair th k o kq q : Data}
    (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (offerValTy theta roles)) (hq : Conforms q (offerValTy theta roles))
    (hth : Conforms th (offerThetaTy theta)) (hr : o.field "role" ≠ q.field "role")
    (hn : ¬ JointOk (offerLabels theta) o q th) :
    BigStep lib (req :: (Data.record [("pair", pair), ("theta", th)]).toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
          env)
      (activityApply (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels)
        (offerTakeBody theta roles rels od sd)) [.var 3, .var 2, .var 1, .var 0])
      (.error (.refused "notCompliant".toUTF8)) := by
  obtain ⟨v, hv, hd⟩ := judge_in_take (lib := lib) (req := req) (state := state) (pair := pair) (k := k)
    (kq := kq) (E := req :: (takeArg pair th).toVal :: state :: (bothRows k o kq q).toVal :: env) hR ho hq hth
  rcases hd with ⟨he, -⟩ | ⟨hok, -⟩ | ⟨-, -, rfl⟩
  · exact absurd he hr
  · exact absurd hok hn
  · exact method_app (body_refused (.inr rfl) hv)

/-! ## The package: closed facts about the generator's method table -/

private theorem slot_p1 : slotLabels "p" 1 = ["p0"] := by decide
private theorem slot_e2 : slotLabels "e" 2 = ["e0", "e1"] := by decide
private theorem slot_c2 : slotLabels "c" 2 = ["c0", "c1"] := by decide

private theorem take_rowsOf (theta roles : List Label) (ol sl : Nat) :
    rowsOf (offerRels theta roles ol sl) (offerTakeRows (offerRels theta roles ol sl)) =
      some (offerRead, offerRead) := by
  simp [rowsOf, offerTakeRows, rowsTy, readsTy, offerRead, offerRels, Row.find?, relReadTy, readsOf,
    relReadOf, relReadShape, peerLabel, slot_p1, Row.sort, Row.insert, pointsMax, rangeRowsMax]

/-- The take resolves to its declared signature: argument `{pair, theta}`, no calls, the one offer
point read under itself and under its peer, two edits. -/
private theorem take_resolve {D : Type} {theta roles : List Label} {ol sl b : Nat} {x : Label × Sig}
    (h : resolveMethod (D := D) (offerPackageOf theta roles ol sl b) offerTakeIx = .ok x) :
    x = ("take", ⟨offerTakeArg theta, [], offerRead, 2⟩) := by
  have hc : callSlotsOf [] = some [] := by simp [callSlotsOf, slotLabels]
  have he : editSlotsOf (offerRels theta roles ol sl)
      [("e0", optTy (editTy (offerRels theta roles ol sl))), ("e1", optTy (editTy (offerRels theta roles ol sl)))] =
      some 2 := by simp [editSlotsOf, editsMax, slot_e2]
  have hn : pairNamed (offerTakeArg theta) offerRead = true := by
    simp [pairNamed, offerTakeArg, Row.find?, offerRead]
  simp [resolveMethod, offerPackageOf, offerTakeIx, offerMethods, recordRow, Row.find?, methodSig, methodTy,
    resultTy, callsTy, slot_e2, hc, he, take_rowsOf, hn] at h
  split at h
  · rename_i sg hsg
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    split at hsg
    · cases hsg; rfl
    · cases hsg
  · simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem take_peerReads (theta roles : List Label) (ol sl b : Nat) :
    (offerPackageOf theta roles ol sl b).peerReads "take" = offerRead := by
  simp [Package.peerReads, offerPackageOf, recordRow, Row.find?, methodPeer, methodTy, take_rowsOf]

/-! ## Relocation: the take and fuse terms name no closure package -/

private theorem noRef_offerInBox : ∀ (fs : List Label) {terms th : Term}, NoRef terms → NoRef th →
    NoRef (offerInBox fs terms th)
  | [], _, _, _, _ => trivial
  | _ :: fs, _, _, ht, hth => ⟨⟨⟨ht, hth⟩, ⟨hth, ht⟩, trivial⟩, noRef_offerInBox fs ht hth, trivial⟩

private theorem noRef_offerJoint (theta roles : List Label) : NoRef (offerJoint theta roles) := by
  simp [offerJoint, eqData, NoRef, NoRefRow, refusedT, okT, andT, noRef_eqDataBody, noRef_offerInBox]

private theorem noRef_take (theta roles : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl) :
    NoRef (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels) (offerTakeBody theta roles rels od sd)) := by
  simp [activityMethod, offerTakeBody, NoRef, NoRefRow, activityResult, activityEdit, resultT, activityKeyTerm,
    noCallT, someCallT, slot_e2, activityApply, noRef_offerJoint]

/-! ## The deployed run of `take` -/

private theorem find_suspend_of {ℓ : Label} {env : Env} : ∀ {fs : List (Label × Term)} {t : Term},
    Row.find? ℓ fs = some t → Row.find? ℓ (suspend env fs) = some (t, env)
  | [], _, h => by simp [Row.find?] at h
  | (k, u) :: fs, t, h => by
    by_cases hk : ℓ = k
    · subst hk; simp only [Row.find?, if_true, Option.some.injEq] at h; subst h
      simp [suspend, Row.find?]
    · simp only [Row.find?, hk, if_false] at h
      have := find_suspend_of (env := env) h
      simpa [suspend, Row.find?, hk] using this

/-- The receiver's method application `apply4 g ℓ`, at a closure body whose field `ℓ` is a
generated method term, runs that method's body over `[req, arg, state, rows]`. -/
private theorem apply4_field {lib : List Term} {g : Nat} {f : Nat → Nat} {pb : Term}
    {fs : List (Label × Term)} {ℓ : Label} {S A R : Ty} {body : Term} {req state : Val} {arg rows : Data}
    {r : Except Fault Val}
    (hlib : lib[g]? = some (pb.relocate f)) (hb : pb = .record fs)
    (hf : Row.find? ℓ fs = some (activityMethod S A R body))
    (hn : NoRef (activityMethod S A R body))
    (h : BigStep lib (bodyEnv req state arg rows []) body r) :
    BigStep lib [req, arg.toVal, state, rows.toVal] (apply4 g ℓ) r := by
  subst hb
  have hrel : (Term.record fs).relocate f = .record (Term.relocateRow f fs) := by simp [Term.relocate]
  rw [hrel] at hlib
  have hf' : Row.find? ℓ (Term.relocateRow f fs) = some (activityMethod S A R body) := by
    rw [find_relocateRow, hf, Option.map_some, relocate_noRef f _ hn]
  have hget : BigStep lib [req, arg.toVal, state, rows.toVal] (.get (.ref g) ℓ)
      (.ok (.clo (.lam S (.lam A (.lam reqTy body))) [])) :=
    .get (.ref hlib .record) (.field (find_suspend_of hf') .lam)
  unfold apply4
  exact .app (.app (.app (.app hget (.var rfl) .lam) (.var rfl) .lam) (.var rfl) .lam) (.var rfl) h

/-- `runMeasured`'s do-block inverted, with the calls conjunct (`runMeasuredWith_ok` with `callsOf`). -/
private theorem runMeasured_inv {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {method : Nat} {args : ByteArray} {r : Kernel.Receive.Req D} {budget : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t n : Nat}
    (h : runMeasured bytesOf digestOf look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∃ S v used c e ds left es, runSetup bytesOf digestOf look rv pkg state method args r = .ok S ∧
      run S.lib Bounds.stackMax (budget - S.preparation) 0 (State.init S.term S.env) = .value v used ∧
      (Machine.mk S.lib).extract S.ty (budget - S.preparation - used) v =
        .ok (.record [("calls", c), ("edits", e), ("state", .record ds)], left) ∧
      callsOf digestOf c = .ok calls ∧ editsOf S.rels r.self e = .ok es ∧
      rows = es.map (fun x => (x.slot, x.act)) := by
  unfold runMeasured runMeasuredWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i S hS
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i v used hrun
  split at h
  all_goals first | (simp at h; done) | skip
  rename_i c e ds left hx
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, rfl, -, -⟩ := h
  exact ⟨S, v, used, c, e, ds, left, _, hS, hrun, hx, ‹callsOf _ _ = .ok _›, ‹editsOf _ _ _ = .ok _›, rfl⟩

/-! ### Conforming shapes of what the run decodes and reads -/

private theorem conforms_empty {d : Data} (h : Conforms d (.record [])) : d = .record [] := by
  cases h with | record hr => cases hr; rfl

private theorem conforms_opt {d : Data} {T : Ty} (h : Conforms d (optTy T)) :
    d = optD none ∨ ∃ z, d = optD (some z) ∧ Conforms z T := by
  cases h with
  | inj hf hc =>
    rename_i ℓ A z
    simp only [Row.find?] at hf
    split at hf
    · cases hf; subst_vars; exact .inl (by rw [conforms_empty hc]; rfl)
    · split at hf
      · cases hf; subst_vars; exact .inr ⟨z, rfl, hc⟩
      · cases hf

private theorem arg_cases {theta : List Label} {ad : Data} (h : Conforms ad (offerTakeArg theta)) :
    ∃ pair th, ad = takeArg pair th ∧ Conforms pair pairTy ∧ Conforms th (offerThetaTy theta) := by
  cases h with
  | record hr =>
    cases hr with
    | cons h1 hr => cases hr with
      | cons h2 hr => cases hr; exact ⟨_, _, rfl, h1, h2⟩

private theorem point_cases {d : RelDecl} {X : Data} (h : Conforms X (optTy (pointRecTy d false))) :
    X = optD none ∨ ∃ k, Conforms k (keyTy d) ∧
      (X = .inj "some" (pointD k none) ∨ ∃ o, Conforms o d.val ∧ X = .inj "some" (pointD k (some o))) := by
  rcases conforms_opt h with rfl | ⟨z, rfl, hz⟩
  · exact .inl rfl
  · simp only [pointRecTy, List.append_nil, Bool.false_eq_true, ↓reduceIte, List.singleton_append] at hz
    cases hz with
    | record hr =>
      cases hr with
      | cons h1 hr => cases hr with
        | cons h2 hr =>
          cases hr
          rcases conforms_opt h2 with rfl | ⟨o, rfl, ho⟩
          · exact .inr ⟨_, h1, .inl rfl⟩
          · exact .inr ⟨_, h1, .inr ⟨o, ho, rfl⟩⟩

private theorem take_rowsTy (theta roles : List Label) (ol sl : Nat) :
    offerTakeRows (offerRels theta roles ol sl) =
      .record [("offer", .record [("p0", optTy (pointRecTy (offerDecl theta roles ol) false))]),
        ("peer", .record [("offer", .record [("p0", optTy (pointRecTy (offerDecl theta roles ol) false))])])] := by
  simp [offerTakeRows, rowsTy, readsTy, offerRead, offerRels, Row.find?, relReadTy, slot_p1, peerLabel,
    Row.sort, Row.insert]

private theorem rec1_cases {d : Data} {l : Label} {T : Ty} (h : Conforms d (.record [(l, T)])) :
    ∃ x, d = .record [(l, x)] ∧ Conforms x T := by
  cases h with
  | record hr => cases hr with
    | cons h1 hr => cases hr; exact ⟨_, rfl, h1⟩

private theorem rows_cases {theta roles : List Label} {ol sl : Nat} {wd : Data}
    (h : Conforms wd (offerTakeRows (offerRels theta roles ol sl))) :
    ∃ X Y, wd = takeRows X Y ∧ Conforms X (optTy (pointRecTy (offerDecl theta roles ol) false)) ∧
      Conforms Y (optTy (pointRecTy (offerDecl theta roles ol) false)) := by
  rw [take_rowsTy] at h
  cases h with
  | record hr =>
    cases hr with
    | cons h1 hr => cases hr with
      | cons h2 hr =>
        cases hr
        obtain ⟨X, rfl, hx⟩ := rec1_cases h1
        obtain ⟨P, rfl, hp⟩ := rec1_cases h2
        obtain ⟨Y, rfl, hy⟩ := rec1_cases hp
        exact ⟨X, Y, rfl, hx, hy⟩

/-! ### What a conforming value means -/

mutual
private theorem means_toVal {lib : List Term} : ∀ {d : Data} {T : Ty}, Conforms d T → Means lib T d.toVal d
  | _, _, .nat _ => .nat
  | _, _, .bool => .bool
  | _, _, .bytes _ => .bytes
  | _, _, .digest _ => .digest
  | _, _, .record h => .record .record (rowMeans_toVal h)
  | _, _, .inj hf h => .inj hf (means_toVal h)

private theorem rowMeans_toVal {lib : List Term} : ∀ {ds : List (Label × Data)} {r : List (Label × Ty)},
    RowConforms ds r → RowMeans lib r (Data.rowToVal ds) ds
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (.var rfl) (means_toVal h) (rowMeans_toVal hs)
end


/-- The take's edits row, as `offerTakeBody` writes it. -/
private abbrev editsT (theta : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl) : Term :=
  .record ((slotLabels "e" 2).zip ([
    activityEdit rels "offer" od "retract" (.get (.var 4) "key"),
    activityEdit rels "session" sd "insert"
      (activityKeyTerm (.get (.var 5) "agent") (.get (.var 5) "notBefore"))
      (.record [("answered", noCallT (activityResponses [offerSettlePlan theta])),
        ("captured", .inj (activityCaptured [offerSettlePlan theta]) "settle"
          (.record [("pair", .get (.var 6) "pair"), ("theta", .get (.var 6) "theta")]))])].map
    fun t => someCallT (editTy rels) t))

/-- What the take's edits row means: the own retract at key `k`, the session insert keyed by the
request's agent and time, capturing `{pair, theta}` unanswered. -/
private theorem editsT_means {theta roles : List Label} {ol sl : Nat} {lib : List Term} {req state : Val}
    {pair th k o kq q : Data} {E : Env} {agent : ByteArray} {nb : Nat}
    (hag : BigStep lib (okEnv req state pair th k o kq q E) (.get (.var 5) "agent") (.ok (.digest agent)))
    (hnb : BigStep lib (okEnv req state pair th k o kq q E) (.get (.var 5) "notBefore") (.ok (.nat nb)))
    (hk : Conforms k (keyTy (offerDecl theta roles ol))) (hpair : Conforms pair pairTy)
    (hth : Conforms th (offerThetaTy theta)) {W : Val}
    (hW : BigStep lib (okEnv req state pair th k o kq q E)
      (editsT theta (offerRels theta roles ol sl) (offerDecl theta roles ol) (offerSessionDecl theta sl)) (.ok W)) :
    Means lib (.record ((slotLabels "e" 2).map fun l => (l, optTy (editTy (offerRels theta roles ol sl))))) W
      (.record [("e0", .inj "some" (.inj "offer" (.inj "retract" (.record [("key", k)])))),
        ("e1", .inj "some" (.inj "session" (.inj "insert" (.record [
          ("key", .record [("agent", .digest agent), ("notBefore", .nat nb)]),
          ("val", .record [("answered", .inj "none" (.record [])),
            ("captured", .inj "settle" (.record [("pair", pair), ("theta", th)]))])]))))]) := by
  cases hW
  simp only [slot_e2, activityEdit, List.map, List.zip, List.zipWith, suspend, ↓reduceIte]
  have hkt : keyTy (offerSessionDecl theta sl) = .record [("agent", .digest), ("notBefore", .nat)] := rfl
  refine .record .record (.cons (.inj (.inj (.inj .record))) ?_ (.cons (.inj (.inj (.inj .record))) ?_ .nil))
  · refine .inj rfl (.inj rfl (.inj (by simp [offerDecl, Row.find?]) (.record .record
      (.cons (get_data (ℓ := "key") (x := k) (BigStep.var (i := 4) rfl) rfl) (means_toVal hk) .nil))))
  · refine .inj rfl (.inj rfl (.inj (A := rowTy (offerSessionDecl theta sl)) (by simp [Row.find?]) (.record .record
      (.cons .record ?_ (.cons .record ?_ .nil)))))
    · rw [hkt]
      exact .record .record (.cons hag .digest (.cons hnb .nat .nil))
    · refine .record .record (.cons (.inj .record) (.inj rfl (.record .record .nil)) (.cons (.inj .record) ?_ .nil))
      exact .inj rfl (.record .record (.cons (get_data (ℓ := "pair") (x := pair) (BigStep.var (i := 6) rfl) rfl)
        (means_toVal hpair) (.cons (get_data (ℓ := "theta") (x := th) (BigStep.var (i := 6) rfl) rfl)
          (means_toVal hth) .nil)))

/-- What the take's two edits read as, under `self`: the own offer's retract at relation 0 and the
session insert at relation 1, each at its key's bytes. -/
private theorem take_editsOf {D : Type} {theta roles : List Label} {ol sl : Nat} {self : D}
    {k K V : Data} {es : List (Edit D)}
    (h : editsOf (offerRels theta roles ol sl) self
      (.record [("e0", .inj "some" (.inj "offer" (.inj "retract" (.record [("key", k)])))),
        ("e1", .inj "some" (.inj "session" (.inj "insert" (.record [("key", K), ("val", V)]))))]) = .ok es) :
    ∃ kb sb vb, keyBytes (offerDecl theta roles ol) k = some kb ∧ keyBytes (offerSessionDecl theta sl) K = some sb ∧
      Wire.encodeData (offerSessionDecl theta sl).val V = some vb ∧
      es.map (fun x => (x.slot, x.act)) =
        [(Kernel.RowSlot.row ⟨self, 0, kb⟩, Kernel.RowAct.retract), (Kernel.RowSlot.row ⟨self, 1, sb⟩, Kernel.RowAct.insert 0 vb)] := by
  have hr : (offerDecl theta roles ol).retract = true := rfl
  have i0 : List.findIdx? (fun x => decide (x.fst = "offer"))
      [("offer", offerDecl theta roles ol), ("session", offerSessionDecl theta sl)] = some 0 := rfl
  have i1 : List.findIdx? (fun x => decide (x.fst = "session"))
      [("offer", offerDecl theta roles ol), ("session", offerSessionDecl theta sl)] = some 1 := rfl
  have ha : amtOf (offerSessionDecl theta sl) V = 0 := rfl
  cases hk : keyBytes (offerDecl theta roles ol) k <;> cases hs : keyBytes (offerSessionDecl theta sl) K <;>
    cases hv : Wire.encodeData (offerSessionDecl theta sl).val V <;>
    simp [editsOf, editsOf.go, editOf, relIndex, i0, i1, offerRels, Row.find?, hk, hs, hv, hr, ha, bind,
      Except.bind, pure, Except.pure] at h
  subst h
  exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩

/-- **The deployed take is sound** (`Lang.program`'s `run`, the run the kernel records, at
`activity_program_safe`'s grain): a run of method `take` of an object of the generated package
that RETURNED decoded the argument `{pair, theta := th}`, built (by the declared peer read) the
rows `{offer: {p0: some {key k, val some o}}, peer: {offer: {p0: some {key kq, val some q}}}}`
from the caller's pins, found `JointOk` of the two pinned offers and θ, makes no calls, and its
row acts are exactly the retract of its own offer at `⟨self, 0, keyBytes k⟩` and the insert of its
own session row at `⟨self, 1, keyBytes {agent, notBefore}⟩` with the value bytes of
`{answered := none, captured := settle {pair, theta := th}}`. Mutations: P2 (the judge skipped:
the run returns at F2, buyer `[5,10]` / seller `[11,12]` / θ = 11, where `JointOk` is false), and the
retract keyed by the peer's point (`.var 2`) instead of its own (`.var 4`): the first act's slot is
then the peer key's bytes. P5 (the retract became an upsert) is refused earlier, by `offer_guard`'s
`final`, so on P5 the run does not return and this theorem is not its tooth. -/
theorem take_run_sound {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {theta roles : List Label} {ol sl budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hR : (offerRoleTy roles).wf = true)
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerPackageOf theta roles ol sl budget))
    (h : (Lang.program bytesOf digestOf).run look rv pkg state offerTakeIx args r budget' =
      .ok (s, calls, rows, used)) :
    ∃ pair th k o kq q kb sb vb,
      Wire.decodeData (offerTakeArg theta) args = .ok (.record [("pair", pair), ("theta", th)]) ∧
      methodReads bytesOf digestOf look pkg (offerRels theta roles ol sl) rv r.self
        (.record [("pair", pair), ("theta", th)]) offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]) ∧
      JointOk (offerLabels theta) o q th ∧ calls = [] ∧
      keyBytes (offerDecl theta roles ol) k = some kb ∧
      keyBytes (offerSessionDecl theta sl)
        (.record [("agent", .digest (bytesOf r.agent)), ("notBefore", .nat r.notBefore)]) = some sb ∧
      Wire.encodeData (offerSessionDecl theta sl).val
        (.record [("answered", .inj "none" (.record [])),
          ("captured", .inj "settle" (.record [("pair", pair), ("theta", th)]))]) = some vb ∧
      rows = [(.row ⟨r.self, 0, kb⟩, .retract), (.row ⟨r.self, 1, sb⟩, .insert 0 vb)] := by
  change (runMeasuredLive bytesOf digestOf look rv pkg state offerTakeIx args r budget').map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
  cases hm : runMeasured bytesOf digestOf look rv pkg state offerTakeIx args r budget' with
  | error e => rw [hm] at h; cases h
  | ok x =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := x
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S, v, used, c, e, ds, left, es, hS, hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, hpg, hres, -, had, -, hwd, rfl⟩ := runSetup_spec hS
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  have hsig := take_resolve hres
  cases hsig
  rw [take_peerReads] at hwd
  simp only at hrun hx hes
  obtain ⟨pair, th, rfl, hpair, hth⟩ := arg_cases (decodeData_conforms had)
  obtain ⟨X, Y, rfl, hX, hY⟩ := rows_cases (methodReads_conforms hwd)
  have hbig := run_bigStep hrun
  have fwd : ∀ {r' : Except Fault Val}, BigStep L.lib
      (bodyEnv (reqData bytesOf r).toVal sd.toVal (takeArg pair th) (takeRows X Y) [])
      (offerTakeBody theta roles (offerRels theta roles ol sl) (offerDecl theta roles ol) (offerSessionDecl theta sl)) r' →
      BigStep L.lib [(reqData bytesOf r).toVal, (takeArg pair th).toVal, sd.toVal, (takeRows X Y).toVal]
        (apply4 g "take") r' :=
    fun hb => apply4_field hlib rfl (by simp [Row.find?]) (noRef_take _ _ _ _ _) hb
  rcases point_cases hX with rfl | ⟨k, hk, rfl | ⟨o, ho, rfl⟩⟩
  · cases bigStep_deterministic hbig (fwd body_offerUnpinned)
  · cases bigStep_deterministic hbig (fwd body_noOffer)
  rcases point_cases hY with rfl | ⟨kq, hkq, rfl | ⟨q, hq, rfl⟩⟩
  · cases bigStep_deterministic hbig (fwd body_peerRowUnpinned)
  · cases bigStep_deterministic hbig (fwd body_noPeerOffer)
  obtain ⟨jv, hjv, hd⟩ := judge_in_take (lib := L.lib) (req := (reqData bytesOf r).toVal) (state := sd.toVal)
    (pair := pair) (k := k) (kq := kq) (E := []) hR ho hq hth
  rcases hd with ⟨-, rfl⟩ | ⟨hok, rfl⟩ | ⟨-, -, rfl⟩
  · cases bigStep_deterministic hbig (fwd (body_refused (.inl rfl) hjv))
  · have hdone : BigStep L.lib (okEnv (reqData bytesOf r).toVal sd.toVal pair th k o kq q [])
        (doneT theta (offerRels theta roles ol sl) (offerDecl theta roles ol) (offerSessionDecl theta sl)) _ := .record
    cases bigStep_deterministic hbig (fwd (body_ok hjv hdone))
    have hM := extract_means _ _ hx
    have hwE := BigStep.get (ℓ := "edits") hbig (.field (find_suspend_of
      (t := editsT theta (offerRels theta roles ol sl) (offerDecl theta roles ol) (offerSessionDecl theta sl)) rfl) .record)
    obtain ⟨A, hA, hmA⟩ := means_get hbig hM rfl hwE
    simp [Row.find?] at hA
    subst hA
    have hED := editsT_means (lib := L.lib) (state := sd.toVal) (o := o) (kq := kq) (q := q) (E := []) (sl := sl) (agent := bytesOf r.agent) (nb := r.notBefore)
      (get_data (ℓ := "agent") (d := reqData bytesOf r) (x := .digest (bytesOf r.agent)) (BigStep.var (i := 5) rfl) rfl)
      (get_data (ℓ := "notBefore") (d := reqData bytesOf r) (x := .nat r.notBefore) (BigStep.var (i := 5) rfl) rfl)
      hk hpair hth .record
    have he := means_deterministic hmA hED
    subst he
    have hwC := BigStep.get (ℓ := "calls") hbig (.field (find_suspend_of (t := .record []) rfl) .record)
    obtain ⟨A', hA', hmC⟩ := means_get hbig hM rfl hwC
    simp [Row.find?] at hA'
    subst hA'
    have hc0 : Means L.lib (callsTy []) (.record []) (.record []) := .record .record .nil
    have hce := means_deterministic hmC hc0
    subst hce
    simp [callsOf, callsOf.go] at hc
    subst hc
    obtain ⟨kb, sb, vb, hkb, hsb, hvb, hmap⟩ := take_editsOf hes
    exact ⟨pair, th, k, o, kq, q, kb, sb, vb, had, hwd, hok, rfl, hkb, hsb, hvb, hrows.trans hmap⟩
  · cases bigStep_deterministic hbig (fwd (body_refused (.inr rfl) hjv))

/-! ## The deployed run of `fuse`: two invokes of `take`, one `deal` -/

/-- A call's `via` field read as the kernel reads it: no grant, or a grant that is a digest of the World. -/
def ViaReads {D : Type} (digestOf : ByteArray → Option D) (v : Data) (g : Option D) : Prop :=
  (v = .inj "none" (.record []) ∧ g = none) ∨ ∃ b d, v = .inj "some" (.digest b) ∧ digestOf b = some d ∧ g = some d

private theorem viaReads_of {D : Type} {digestOf : ByteArray → Option D} {v : Data} {g : Option D}
    (hv : Conforms v (optTy .digest)) (h : optOf (digestAt digestOf "via") "via" v = .ok g) :
    ViaReads digestOf v g := by
  rcases conforms_opt hv with rfl | ⟨z, rfl, hz⟩
  · simp [optD, optOf] at h
    exact .inl ⟨rfl, h.symm⟩
  · cases hz with
    | @digest b _ =>
      cases hb : digestOf b with
      | none => simp [optD, optOf, digestAt, hb, Except.map] at h
      | some d =>
        simp [optD, optOf, digestAt, hb, Except.map] at h
        exact .inr ⟨b, d, rfl, hb, h.symm⟩

private theorem fuse_resolve {D : Type} {theta roles : List Label} {ol sl b : Nat} {x : Label × Sig}
    (h : resolveMethod (D := D) (offerPackageOf theta roles ol sl b) offerFuseIx = .ok x) :
    x = ("fuse", ⟨offerFuseArg, [offerCallTy, offerCallTy], [], 0⟩) := by
  have hc : callSlotsOf [("c0", optTy offerCallTy), ("c1", optTy offerCallTy)] = some [offerCallTy, offerCallTy] := by
    decide
  have hr : rowsOf (offerRels theta roles ol sl) (.record []) = some ([], []) := by
    simp [rowsOf, readsOf, readsTy, Row.find?]
  simp [resolveMethod, offerPackageOf, offerFuseIx, offerMethods, recordRow, Row.find?, methodSig, methodTy,
    resultTy, callsTy, slot_c2, hc, hr, pairNamed] at h
  split at h
  · rename_i sg hsg
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    split at hsg
    · cases hsg; rfl
    · cases hsg
  · simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem fuse_peerReads (theta roles : List Label) (ol sl b : Nat) :
    (offerPackageOf theta roles ol sl b).peerReads "fuse" = [] := by
  have hr : rowsOf (offerRels theta roles ol sl) (.record []) = some ([], []) := by
    simp [rowsOf, readsOf, readsTy, Row.find?]
  simp [Package.peerReads, offerPackageOf, recordRow, Row.find?, methodPeer, methodTy, hr]

private theorem noRef_fuse (budget : Nat) :
    NoRef (activityMethod offerStateTy offerFuseArg (.record []) (offerFuseBody budget)) := by
  simp [activityMethod, offerFuseBody, NoRef, NoRefRow, resultT, callsT, someCallT, offerTakeCall, slot_c2]

private def fuseArgD (deal : ByteArray) (vx vy : Data) (x y : ByteArray) : Data :=
  .record [("deal", .bytes deal), ("viaX", vx), ("viaY", vy), ("x", .digest x), ("y", .digest y)]

private theorem fuseArg_cases {ad : Data} (h : Conforms ad offerFuseArg) :
    ∃ deal vx vy x y, ad = fuseArgD deal vx vy x y ∧ Conforms vx (optTy .digest) ∧ Conforms vy (optTy .digest) := by
  cases h with
  | record hr =>
    cases hr with
    | cons h1 hr => cases hr with
      | cons h2 hr => cases hr with
        | cons h3 hr => cases hr with
          | cons h4 hr => cases hr with
            | cons h5 hr =>
              cases hr; cases h1; cases h4; cases h5
              exact ⟨_, _, _, _, _, rfl, h2, h3⟩

/-- The fuse's calls row, as `offerFuseBody` writes it. -/
private abbrev callsFuseT (budget : Nat) : Term :=
  callsT [someCallT offerCallTy (offerTakeCall budget (.get (.var 1) "x") (.get (.var 1) "viaX") (.get (.var 1) "deal")),
    someCallT offerCallTy (offerTakeCall budget (.get (.var 1) "y") (.get (.var 1) "viaY") (.get (.var 1) "deal"))]

private def invokeTy : Ty :=
  .record [("args", .bytes), ("budget", .nat), ("method", .nat), ("obj", .digest), ("via", optTy .digest)]

private theorem callsFuse_means {lib : List Term} {req state : Val} {rows : Data} {E : Env}
    {deal : ByteArray} {vx vy : Data} {x y : ByteArray} {budget : Nat}
    (hvx : Conforms vx (optTy .digest)) (hvy : Conforms vy (optTy .digest)) {W : Val}
    (hW : BigStep lib (bodyEnv req state (fuseArgD deal vx vy x y) rows E) (callsFuseT budget) (.ok W)) :
    Means lib (callsTy [offerCallTy, offerCallTy]) W
      (.record [("c0", .inj "some" (.inj "invoke" (.record [("args", .bytes deal), ("budget", .nat budget),
          ("method", .nat offerTakeIx), ("obj", .digest x), ("via", vx)]))),
        ("c1", .inj "some" (.inj "invoke" (.record [("args", .bytes deal), ("budget", .nat budget),
          ("method", .nat offerTakeIx), ("obj", .digest y), ("via", vy)])))]) := by
  cases hW
  simp only [callsTy, List.map, List.zip, suspend, offerTakeCall]
  have hf : Row.find? "invoke" (callArms.filter fun a => ["invoke"].contains a.1) = some invokeTy := by decide
  refine .record .record (.cons (.inj (.inj .record)) ?_ (.cons (.inj (.inj .record)) ?_ .nil))
  · exact .inj rfl (.inj hf (.record .record
      (.cons (get_data (ℓ := "deal") (x := .bytes deal) (BigStep.var (i := 1) rfl) rfl) .bytes
      (.cons .nat .nat (.cons .nat .nat
      (.cons (get_data (ℓ := "x") (x := .digest x) (BigStep.var (i := 1) rfl) rfl) .digest
      (.cons (get_data (ℓ := "viaX") (x := vx) (BigStep.var (i := 1) rfl) rfl) (means_toVal hvx) .nil)))))))
  · exact .inj rfl (.inj hf (.record .record
      (.cons (get_data (ℓ := "deal") (x := .bytes deal) (BigStep.var (i := 1) rfl) rfl) .bytes
      (.cons .nat .nat (.cons .nat .nat
      (.cons (get_data (ℓ := "y") (x := .digest y) (BigStep.var (i := 1) rfl) rfl) .digest
      (.cons (get_data (ℓ := "viaY") (x := vy) (BigStep.var (i := 1) rfl) rfl) (means_toVal hvy) .nil)))))))

/-- **The matcher forwards one deal to both takes** (`Lang.program`'s `run` of `fuse`): a run that
returned decoded `{deal, viaX, viaY, x, y}`, makes exactly two calls, `invoke x take deal budget`
and `invoke y take deal budget`, carrying the SAME `deal` bytes (each `via` read as the kernel reads
it), and edits no row. The matcher judges nothing: the honesty is each take's
(`take_iff_compliant`); the one θ is this theorem's. Mutations: P3 (the second call dropped: the
calls list has one element) and P4 (a second argument field `dealY` sent to `y`: the second call's
bytes are not `deal`). -/
theorem fuse_calls {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)
    {theta roles : List Label} {ol sl budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerPackageOf theta roles ol sl budget))
    (h : (Lang.program bytesOf digestOf).run look rv pkg state offerFuseIx args r budget' =
      .ok (s, calls, rows, used)) :
    ∃ deal x y vx vy x' y' vx' vy',
      Wire.decodeData offerFuseArg args =
        .ok (.record [("deal", .bytes deal), ("viaX", vx), ("viaY", vy), ("x", .digest x), ("y", .digest y)]) ∧
      digestOf x = some x' ∧ digestOf y = some y' ∧ ViaReads digestOf vx vx' ∧ ViaReads digestOf vy vy' ∧
      calls = [.invoke x' offerTakeIx deal budget vx', .invoke y' offerTakeIx deal budget vy'] ∧ rows = [] := by
  change (runMeasuredLive bytesOf digestOf look rv pkg state offerFuseIx args r budget').map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
  cases hm : runMeasured bytesOf digestOf look rv pkg state offerFuseIx args r budget' with
  | error e => rw [hm] at h; cases h
  | ok x =>
  rw [hm] at h
  obtain ⟨s', calls', rows', t', n'⟩ := x
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨S, v, used, c, e, ds, left, es, hS, hrun, hx, hc, hes, hrows⟩ := runMeasured_inv hm
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, hpg, hres, -, had, -, hwd, rfl⟩ := runSetup_spec hS
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hl
  rw [hpg'] at hpg
  cases hpg
  have hsig := fuse_resolve hres
  cases hsig
  simp only at hrun hx hes
  obtain ⟨deal, vx, vy, xb, yb, rfl, hvx, hvy⟩ := fuseArg_cases (decodeData_conforms had)
  have hbig := run_bigStep hrun
  have hval : BigStep L.lib (bodyEnv (reqData bytesOf r).toVal sd.toVal (fuseArgD deal vx vy xb yb) wd [])
      (offerFuseBody budget) _ := .record
  cases bigStep_deterministic hbig
    (apply4_field hlib rfl (by simp [Row.find?]) (noRef_fuse budget) hval)
  have hM := extract_means _ _ hx
  have hwC := BigStep.get (ℓ := "calls") hbig (.field (find_suspend_of (t := callsFuseT budget) rfl) .record)
  obtain ⟨A, hA, hmA⟩ := means_get hbig hM rfl hwC
  simp [Row.find?] at hA
  subst hA
  have hce := means_deterministic hmA (callsFuse_means (budget := budget) hvx hvy .record)
  subst hce
  have hwE := BigStep.get (ℓ := "edits") hbig (.field (find_suspend_of (t := .record []) rfl) .record)
  obtain ⟨A', hA', hmE⟩ := means_get hbig hM rfl hwE
  simp [Row.find?] at hA'
  subst hA'
  have hee := means_deterministic hmE (.record .record .nil)
  subst hee
  simp [editsOf, editsOf.go] at hes
  subst hes
  cases hdx : digestOf xb <;> cases hdy : digestOf yb <;>
    cases hox : optOf (digestAt digestOf "via") "via" vx <;> cases hoy : optOf (digestAt digestOf "via") "via" vy <;>
    simp [callsOf, callsOf.go, bodyOf, digestAt, natOf, bytesAt, hdx, hdy, hox, hoy, bind, Except.bind, pure,
      Except.pure, Except.map] at hc
  rename_i x' y' vx' vy'
  exact ⟨deal, xb, yb, vx, vy, x', y', vx', vy', had, hdx, hdy, viaReads_of hvx hox, viaReads_of hvy hoy,
    hc.symm, hrows⟩

/-! ## Two real rows with no common θ -/

private def buyerA : Data :=
  .record [("role", .inj "buyer" (.record [])), ("terms", .record [("price", .record [("hi", .nat 10), ("lo", .nat 5)])])]

private def sellerB : Data :=
  .record [("role", .inj "seller" (.record [])), ("terms", .record [("price", .record [("hi", .nat 12), ("lo", .nat 11)])])]

private theorem labels_price : offerLabels ["price"] = ["price"] := rfl

private theorem roles_wf : (offerRoleTy ["buyer", "seller"]).wf = true := by decide

private theorem buyerA_conforms : Conforms buyerA (offerValTy ["price"] ["buyer", "seller"]) :=
  .record (.cons (.inj (by decide) (.record .nil))
    (.cons (.record (.cons (.record (.cons (.nat (by decide)) (.cons (.nat (by decide)) .nil))) .nil)) .nil))

private theorem sellerB_conforms : Conforms sellerB (offerValTy ["price"] ["buyer", "seller"]) :=
  .record (.cons (.inj (by decide) (.record .nil))
    (.cons (.record (.cons (.record (.cons (.nat (by decide)) (.cons (.nat (by decide)) .nil))) .nil)) .nil))

/-- **No common θ for the buyer `[5,10]` and the seller `[11,12]`** (θ labels `["price"]`, roles
`["buyer","seller"]`): each box holds a θ of its own (7 and 11), no θ is inside both (so no θ is
`JointOk` for the pair), and the generated take term, at every conforming θ, refuses the pair
`notCompliant`. This is the arithmetic half of the deleted `separate_witnesses_over_substitutions`
(each side satisfiable, no common point), over the two real rows. Mutation: `offerJoint := okT`
(the take then returns at every θ), and a judge that refuses only the journey's θ = 11 and accepts
another (it returns at θ = 12). -/
theorem fuse_refused_disjoint :
    (∃ th, InBox (offerLabels ["price"]) (.record [("price", .record [("hi", .nat 10), ("lo", .nat 5)])]) th) ∧
    (∃ th, InBox (offerLabels ["price"]) (.record [("price", .record [("hi", .nat 12), ("lo", .nat 11)])]) th) ∧
    (∀ th, Conforms th (offerThetaTy ["price"]) →
      ¬ JointOk (offerLabels ["price"])
        (.record [("role", .inj "buyer" (.record [])),
          ("terms", .record [("price", .record [("hi", .nat 10), ("lo", .nat 5)])])])
        (.record [("role", .inj "seller" (.record [])),
          ("terms", .record [("price", .record [("hi", .nat 12), ("lo", .nat 11)])])]) th) ∧
    (∀ (th pair k kq : Data) (rels : List (Label × RelDecl)) (od sd : RelDecl) (lib : List Term) (env : Env)
        (req state : Val), Conforms th (offerThetaTy ["price"]) →
      BigStep lib (req :: (Data.record [("pair", pair), ("theta", th)]).toVal :: state ::
          (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some"
              (.record [("role", .inj "buyer" (.record [])),
                ("terms", .record [("price", .record [("hi", .nat 10), ("lo", .nat 5)])])]))]))]),
            ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some"
              (.record [("role", .inj "seller" (.record [])),
                ("terms", .record [("price", .record [("hi", .nat 12), ("lo", .nat 11)])])]))]))])])]).toVal ::
            env)
        (activityApply (activityMethod offerStateTy (offerTakeArg ["price"]) (offerTakeRows rels)
          (offerTakeBody ["price"] ["buyer", "seller"] rels od sd)) [.var 3, .var 2, .var 1, .var 0])
        (.error (.refused "notCompliant".toUTF8))) := by
  have hnot : ∀ th, ¬ JointOk (offerLabels ["price"]) buyerA sellerB th := by
    rintro th ⟨-, ⟨ot, hot, hA⟩, ⟨qt, hqt, hB⟩⟩
    simp [buyerA, sellerB, Data.field, Row.find?] at hot hqt
    subst hot; subst hqt
    rw [labels_price] at hA hB
    obtain ⟨lo, hi, t, h1, h2, h3, h4⟩ := hA "price" (by simp)
    obtain ⟨lo', hi', t', h1', h2', h3', h4'⟩ := hB "price" (by simp)
    rw [h2] at h2'
    have e1 : hi = 10 ∧ lo = 5 := by simpa [Data.field, Row.find?] using h1.symm
    have e2 : hi' = 12 ∧ lo' = 11 := by simpa [Data.field, Row.find?] using h1'.symm
    have e3 : t = t' := by simpa using h2'
    omega
  have hrole : buyerA.field "role" ≠ sellerB.field "role" := by
    simp [buyerA, sellerB, Data.field, Row.find?]
  refine ⟨⟨.record [("price", .nat 7)], ?_⟩, ⟨.record [("price", .nat 11)], ?_⟩, fun th _ => hnot th, ?_⟩
  · rw [labels_price]; intro f hf; simp only [List.mem_singleton] at hf; subst hf
    exact ⟨5, 10, 7, rfl, rfl, by decide, by decide⟩
  · rw [labels_price]; intro f hf; simp only [List.mem_singleton] at hf; subst hf
    exact ⟨11, 12, 11, rfl, rfl, by decide, by decide⟩
  · intro th pair k kq rels od sd lib env req state hth
    exact take_notCompliant (o := buyerA) (q := sellerB) roles_wf buyerA_conforms sellerB_conforms hth hrole (hnot th)

end Nanodregg.Lang.Std
