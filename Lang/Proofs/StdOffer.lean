/-
# Lang.Proofs.StdOffer — what the generated offer judge, its take and its matcher decide (PROT-6)

Every theorem here is about a term `Lang.StdOffer` generates, by its `BigStep` meaning, or about
`Lang.program`'s `run` of the generated package:

* `offerJoint_meaning` / `offerJoint_total` (term grain): the joint judge `offerJoint` says
  `sameRole`, `ok` (exactly `JointOk`: different roles, θ inside BOTH boxes) or `notCompliant`.
* `take_iff_compliant` (method-term grain, as the receiver applies it): with both offer slots
  present, the take returns iff its own pinned offer is the one the deal names for it (`NamedKey`)
  and `JointOk` of the two pinned offers and the θ it decoded. The matcher's code is not a premise.
  Its refusals by name: `take_offerUnpinned`, `take_noOffer`, `take_peerRowUnpinned`,
  `take_noPeerOffer`, `take_offerNotNamed`, `take_sameRole`, `take_notCompliant`.
* `take_run_sound` (the deployed run): a returned take decoded `{keys, pair, theta}`, read both
  pinned offers, its own the one the deal names for it, found them `JointOk`, makes no calls, and
  its row acts are exactly that named offer's retract and its own session insert.
* `fuse_refused_disjoint`: buyer `[5,10]` and seller `[11,12]` over `["price"]` have no common θ, and
  the take term refuses that pair `notCompliant` at every θ.

The fuse's run (`fuse_run_sound`) is in `Lang.Proofs.StdOfferFuse`, with what a signed fuse seals.
The run-grain steps (`get_data`, `apply4_method`, `runMeasured_inv`, `means_toVal`) are
`Lang.Proofs.MethodRun`'s.

The run-grain converse of `take_run_sound` is not here: the tree has no completeness lemma for the
machine at the deployed `Bounds.stackMax` (`bigStep_run` gives an existential stack bound) nor for
extraction (`forces_le` is the other direction).
-/
import Lang.StdOffer
import Lang.Proofs.StdActivityMonitor
import Lang.Proofs.Extract
import Lang.Proofs.Invoke
import Lang.Proofs.MethodRun

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

/-- The offer key the deal names for the object whose digest bytes are `self`, as `offerNamedT`
computes it: `keys.a` when `self` is `pair.a`, else `keys.b`. -/
def NamedKey (self : ByteArray) (keys pair k : Data) : Prop :=
  ∃ a b na nb, keys = .record [("a", .nat na), ("b", .nat nb)] ∧
    pair = .record [("a", .digest a), ("b", .digest b)] ∧ k = .record [("n", .nat (if self = a then na else nb))]

/-! ## Data in the environment, forward -/

theorem andT_eval {lib : List Term} {env : Env} {a b : Term} {x y : Bool}
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
theorem offer_shape {theta roles : List Label} {o : Data} (h : Conforms o (offerValTy theta roles)) :
    ∃ ro ot, o = .record [("role", ro), ("terms", ot)] ∧ Conforms ro (offerRoleTy roles) ∧
      Conforms ot (offerTermsTy theta) := by
  cases h with
  | record hr =>
    cases hr with
    | cons h1 hr => cases hr with
      | cons h2 hr => cases hr; exact ⟨_, _, rfl, h1, h2⟩

/-- The judge's evaluation, at any value type, over any environment in which its three operands
mean `o`, `q`, `θ`, where `o` and `q` carry a conforming `role` and `terms`. -/
theorem offerJoint_eval {theta roles : List Label} {V : Ty} {lib : List Term} {E : Env} {a b c : Term}
    {o q th ro ot rq qt : Data} (hR : (offerRoleTy roles).wf = true)
    (hor : o.field "role" = some ro) (hro : Conforms ro (offerRoleTy roles))
    (hot : o.field "terms" = some ot) (hotc : Conforms ot (offerTermsTy theta))
    (hqr : q.field "role" = some rq) (hrq : Conforms rq (offerRoleTy roles))
    (hqt : q.field "terms" = some qt) (hqtc : Conforms qt (offerTermsTy theta))
    (hth : Conforms th (offerThetaTy theta))
    (ha : BigStep lib E a (.ok o.toVal)) (hb : BigStep lib E b (.ok q.toVal))
    (hc : BigStep lib E c (.ok th.toVal)) :
    ∃ v, BigStep lib E (activityApply (offerJoint theta roles V) [a, b, c]) (.ok v) ∧
      ((o.field "role" = q.field "role" ∧ v = .inj "refused" (.bytes "sameRole".toUTF8)) ∨
       (JointOk (offerLabels theta) o q th ∧ v = .inj "ok" (.record [])) ∨
       (o.field "role" ≠ q.field "role" ∧ ¬ JointOk (offerLabels theta) o q th ∧
         v = .inj "refused" (.bytes "notCompliant".toUTF8))) := by
  let Eb := th.toVal :: q.toVal :: o.toVal :: E
  suffices hbody : ∃ v, BigStep lib Eb
      (.ite (eqData (offerRoleTy roles) (.get (.var 2) "role") (.get (.var 1) "role"))
        (refusedT "sameRole")
        (.ite (andT (offerInBox (offerLabels theta) (.get (.var 2) "terms") (.var 0))
            (offerInBox (offerLabels theta) (.get (.var 1) "terms") (.var 0)))
          okT (refusedT "notCompliant"))) (.ok v) ∧
      ((o.field "role" = q.field "role" ∧ v = .inj "refused" (.bytes "sameRole".toUTF8)) ∨
       (JointOk (offerLabels theta) o q th ∧ v = .inj "ok" (.record [])) ∨
       (o.field "role" ≠ q.field "role" ∧ ¬ JointOk (offerLabels theta) o q th ∧
         v = .inj "refused" (.bytes "notCompliant".toUTF8))) by
    obtain ⟨v, hv, hd⟩ := hbody
    exact ⟨v, by
      unfold activityApply offerJoint
      simp only [List.foldl]
      exact .app (.app (.app .lam ha .lam) hb .lam) hc hv, hd⟩
  have hO : BigStep lib Eb (.var 2) (.ok o.toVal) := .var rfl
  have hQ : BigStep lib Eb (.var 1) (.ok q.toVal) := .var rfl
  have hT : BigStep lib Eb (.var 0) (.ok th.toVal) := .var rfl
  have hxo := get_data hO hor
  have hxq := get_data hQ hqr
  obtain ⟨same, hs, hsi⟩ := eqDataBody_meaning (lib := lib) (env := Eb) (offerRoleTy roles) hR hro hrq
  have heq : BigStep lib Eb (eqData (offerRoleTy roles) (.get (.var 2) "role") (.get (.var 1) "role"))
      (.ok (.bool same)) := .app (.app .lam hxo .lam) hxq hs
  have hfO : o.field "role" = q.field "role" ↔ ro = rq := by
    rw [hor, hqr]; simp
  cases same with
  | true =>
    refine ⟨_, .iteT heq (.inj .bytes), .inl ⟨hfO.mpr (hsi.mp rfl), rfl⟩⟩
  | false =>
    have hne : o.field "role" ≠ q.field "role" := fun h => by simpa using hsi.mpr (hfO.mp h)
    have hshape : ∀ (ut : Data), Conforms ut (offerTermsTy theta) →
        ∀ f ∈ offerLabels theta, (∃ lo hi, ut.field f = some (.record [("hi", .nat hi), ("lo", .nat lo)])) ∧
          ∃ t, th.field f = some (.nat t) := fun ut hu f hf => ⟨terms_shape hu hf, theta_shape hth hf⟩
    obtain ⟨b1, hb1, hb1i⟩ := inBox_eval (get_data hO hot) hT (offerLabels theta) (hshape ot hotc)
    obtain ⟨b2, hb2, hb2i⟩ := inBox_eval (get_data hQ hqt) hT (offerLabels theta) (hshape qt hqtc)
    have hand := andT_eval hb1 hb2
    have hj : JointOk (offerLabels theta) o q th ↔ (b1 && b2) = true := by
      simp only [JointOk, Bool.and_eq_true, hb1i, hb2i, hot, hqt, Option.some.injEq, exists_eq_left']
      exact ⟨fun h => h.2, fun h => ⟨hne, h⟩⟩
    cases hbb : (b1 && b2) with
    | true =>
      rw [hbb] at hand
      exact ⟨_, .iteF heq (.iteT hand (.inj .record)), .inr (.inl ⟨hj.mpr hbb, rfl⟩)⟩
    | false =>
      rw [hbb] at hand
      exact ⟨_, .iteF heq (.iteF hand (.inj .bytes)),
        .inr (.inr ⟨hne, fun h => by simpa [hbb] using hj.mp h, rfl⟩)⟩

/-- `Std.offer`'s value: its role and box, as fields. -/
theorem offer_fields {theta roles : List Label} {o : Data} (h : Conforms o (offerValTy theta roles)) :
    (∃ ro, o.field "role" = some ro ∧ Conforms ro (offerRoleTy roles)) ∧
      (∃ ot, o.field "terms" = some ot ∧ Conforms ot (offerTermsTy theta)) := by
  obtain ⟨ro, ot, rfl, hro, hot⟩ := offer_shape h
  exact ⟨⟨ro, by simp [Data.field, Row.find?], hro⟩, ⟨ot, by simp [Data.field, Row.find?], hot⟩⟩

/-- `joint_eval` at `Std.offer`'s values. -/
private theorem joint_eval {theta roles : List Label} {lib : List Term} {E : Env} {a b c : Term}
    {o q th : Data} (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (offerValTy theta roles)) (hq : Conforms q (offerValTy theta roles))
    (hth : Conforms th (offerThetaTy theta))
    (ha : BigStep lib E a (.ok o.toVal)) (hb : BigStep lib E b (.ok q.toVal))
    (hc : BigStep lib E c (.ok th.toVal)) :
    ∃ v, BigStep lib E (activityApply (offerJoint theta roles (offerValTy theta roles)) [a, b, c]) (.ok v) ∧
      ((o.field "role" = q.field "role" ∧ v = .inj "refused" (.bytes "sameRole".toUTF8)) ∨
       (JointOk (offerLabels theta) o q th ∧ v = .inj "ok" (.record [])) ∨
       (o.field "role" ≠ q.field "role" ∧ ¬ JointOk (offerLabels theta) o q th ∧
         v = .inj "refused" (.bytes "notCompliant".toUTF8))) := by
  obtain ⟨⟨ro, hor, hro⟩, ⟨ot, hot, hotc⟩⟩ := offer_fields ho
  obtain ⟨⟨rq, hqr, hrq⟩, ⟨qt, hqt, hqtc⟩⟩ := offer_fields hq
  exact offerJoint_eval hR hor hro hot hotc hqr hrq hqt hqtc hth ha hb hc

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
      (activityApply (offerJoint theta roles (offerValTy theta roles)) [.var 2, .var 1, .var 0]) (.ok v)) :
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
      (activityApply (offerJoint theta roles (offerValTy theta roles)) [.var 2, .var 1, .var 0]) (.ok v) := by
  obtain ⟨w, hw, -⟩ := joint_eval hR ho hq hth (BigStep.var (i := 2) rfl) (BigStep.var (i := 1) rfl) (BigStep.var (i := 0) rfl)
    (lib := lib) (E := th.toVal :: q.toVal :: o.toVal :: env)
  exact ⟨w, hw⟩

/-! ## The take, at the method term's grain -/

/-- `take`'s rows argument: its own offer slot and its peer's. -/
private def takeRows (own peer : Data) : Data :=
  .record [("offer", .record [("p0", own)]), ("peer", .record [("offer", .record [("p0", peer)])])]

/-- A pinned point: its key and its row's value, if any. -/
private def pointD (k : Data) (v : Option Data) : Data := .record [("key", k), ("val", optD v)]

/-- The take's argument, `{keys, pair, theta}`, and whatever fields a method sharing the take's tree
adds after them (the fuse's `via`, LANG-77): the tree reads only the three. -/
private def takeArg (keys pair th : Data) (tail : List (Label × Data)) : Data :=
  .record ([("keys", keys), ("pair", pair), ("theta", th)] ++ tail)

/-- The env the take body runs in (var 0 req, var 1 arg, var 2 state, var 3 rows). -/
private abbrev bodyEnv (req state : Val) (arg rows : Data) (E : Env) : Env :=
  req :: arg.toVal :: state :: rows.toVal :: E

/-- The verdict's `ok` arm's env: payload, peer value, peer point, own value, own point, then the body env. -/
private abbrev okEnv (req state : Val) (keys pair th : Data) (tail : List (Label × Data)) (k o kq q : Data) (E : Env) : Env :=
  .record [] :: q.toVal :: (pointD kq (some q)).toVal :: o.toVal :: (pointD k (some o)).toVal ::
    bodyEnv req state (takeArg keys pair th tail) (takeRows (.inj "some" (pointD k (some o))) (.inj "some" (pointD kq (some q)))) E

private theorem rows_own {lib : List Term} {req state : Val} {arg own peer : Data} {E : Env} :
    BigStep lib (bodyEnv req state arg (takeRows own peer) E) (.get (.get (.var 3) "offer") "p0")
      (.ok own.toVal) :=
  get_data (ℓ := "p0") (x := own) (get_data (ℓ := "offer") (x := .record [("p0", own)])
    (BigStep.var (i := 3) rfl) rfl) rfl

/-- `offerUnwrap` over a `some`: the body runs with the payload bound, as under a `some` arm. -/
theorem offerUnwrap_some {lib : List Term} {env : Env} {T : Ty} {s body : Term} {why : String} {w : Val}
    {r : Except Fault Val} (hs : BigStep lib env s (.ok (.inj "some" w))) (hb : BigStep lib (w :: env) body r) :
    BigStep lib env (offerUnwrap T s why body) r :=
  .app .lam (.case hs rfl (.var rfl)) hb

/-- `offerUnwrap` over a `none`: refused `why`. -/
theorem offerUnwrap_none {lib : List Term} {env : Env} {T : Ty} {s body : Term} {why : String} {u : Val}
    (hs : BigStep lib env s (.ok (.inj "none" u))) :
    BigStep lib env (offerUnwrap T s why body) (.error (.refused why.toUTF8)) :=
  .appA .lam (.case hs rfl .refuse)

private theorem body_offerUnpinned {theta roles : List Label} {V : Ty} {fair : Option Term}
    {done : Term} {lib : List Term} {req state : Val} {arg peer : Data} {E : Env} :
    BigStep lib (bodyEnv req state arg (takeRows (optD none) peer) E) (offerTakeTree theta roles V fair done)
      (.error (.refused "offerUnpinned".toUTF8)) :=
  offerUnwrap_none rows_own

private theorem body_noOffer {theta roles : List Label} {V : Ty} {fair : Option Term}
    {done : Term} {lib : List Term} {req state : Val} {arg peer k : Data} {E : Env} :
    BigStep lib (bodyEnv req state arg (takeRows (.inj "some" (pointD k none)) peer) E)
      (offerTakeTree theta roles V fair done) (.error (.refused "noOffer".toUTF8)) :=
  offerUnwrap_some rows_own (offerUnwrap_none (get_data (ℓ := "val") (x := optD none) (BigStep.var (i := 0) rfl) rfl))

/-- The peer slot, inside the own offer's two binders. -/
private theorem rows_peer {lib : List Term} {req state : Val} {arg k o peer : Data} {E : Env} :
    BigStep lib (o.toVal :: (pointD k (some o)).toVal ::
        bodyEnv req state arg (takeRows (.inj "some" (pointD k (some o))) peer) E)
      (.get (.get (.get (.var 5) "peer") "offer") "p0") (.ok peer.toVal) :=
  get_data (ℓ := "p0") (x := peer) (get_data (ℓ := "offer") (x := .record [("p0", peer)])
    (get_data (ℓ := "peer") (x := .record [("offer", .record [("p0", peer)])]) (BigStep.var (i := 5) rfl) rfl)
    rfl) rfl

private theorem body_peerRowUnpinned {theta roles : List Label} {V : Ty} {fair : Option Term}
    {done : Term} {lib : List Term} {req state : Val} {arg k o : Data} {E : Env} :
    BigStep lib (bodyEnv req state arg (takeRows (.inj "some" (pointD k (some o))) (optD none)) E)
      (offerTakeTree theta roles V fair done) (.error (.refused "peerRowUnpinned".toUTF8)) :=
  offerUnwrap_some rows_own (offerUnwrap_some
    (get_data (ℓ := "val") (x := optD (some o)) (BigStep.var (i := 0) rfl) rfl) (offerUnwrap_none rows_peer))

private theorem body_noPeerOffer {theta roles : List Label} {V : Ty} {fair : Option Term}
    {done : Term} {lib : List Term} {req state : Val} {arg k o kq : Data} {E : Env} :
    BigStep lib (bodyEnv req state arg (takeRows (.inj "some" (pointD k (some o))) (.inj "some" (pointD kq none))) E)
      (offerTakeTree theta roles V fair done) (.error (.refused "noPeerOffer".toUTF8)) :=
  offerUnwrap_some rows_own (offerUnwrap_some
    (get_data (ℓ := "val") (x := optD (some o)) (BigStep.var (i := 0) rfl) rfl) (offerUnwrap_some rows_peer
      (offerUnwrap_none (get_data (ℓ := "val") (x := optD none) (BigStep.var (i := 0) rfl) rfl))))

/-- The judge's env inside the take: peer value, peer point, own value, own point, then the body env. -/
private abbrev judgeEnv (req state : Val) (keys pair th : Data) (tail : List (Label × Data)) (k o kq q : Data) (E : Env) : Env :=
  q.toVal :: (pointD kq (some q)).toVal :: o.toVal :: (pointD k (some o)).toVal ::
    bodyEnv req state (takeArg keys pair th tail) (takeRows (.inj "some" (pointD k (some o))) (.inj "some" (pointD kq (some q)))) E

private abbrev bothRows (k o kq q : Data) : Data :=
  takeRows (.inj "some" (pointD k (some o))) (.inj "some" (pointD kq (some q)))

/-- The four unwraps of a take over two present offers: whatever the gate-and-done term does under
the judge's env, the tree does. -/
private theorem tree_present {theta roles : List Label} {V : Ty} {fair : Option Term} {done : Term} {lib : List Term}
    {req state : Val} {keys pair th k o kq q : Data} {E : Env} {tail : List (Label × Data)} {r : Except Fault Val}
    (h : BigStep lib (judgeEnv req state keys pair th tail k o kq q E)
      (.app (.lam (.record []) done) (offerGate theta roles V fair)) r) :
    BigStep lib (bodyEnv req state (takeArg keys pair th tail) (bothRows k o kq q) E)
      (offerTakeTree theta roles V fair done) r :=
  offerUnwrap_some rows_own (offerUnwrap_some
    (get_data (ℓ := "val") (x := optD (some o)) (BigStep.var (i := 0) rfl) rfl) (offerUnwrap_some rows_peer
      (offerUnwrap_some (get_data (ℓ := "val") (x := optD (some q)) (BigStep.var (i := 0) rfl) rfl) h)))

private theorem body_ok {theta roles : List Label} {V : Ty} {fair : Option Term}
    {done : Term} {lib : List Term} {req state : Val} {keys pair th k o kq q : Data} {E : Env} {tail : List (Label × Data)}
    {r : Except Fault Val}
    (hn : BigStep lib (judgeEnv req state keys pair th tail k o kq q E) (offerNamedOkT (.var 3) (.var 4) (.var 5))
      (.ok (.bool true)))
    (hj : BigStep lib (judgeEnv req state keys pair th tail k o kq q E)
      (activityApply (offerJoint theta roles V) [.var 2, .var 0, .get (.var 5) "theta"])
      (.ok (.inj "ok" (.record []))))
    (hf : ∀ f, fair = some f → BigStep lib (okEnv req state keys pair th tail k o kq q E) f (.ok (.bool true)))
    (hd : BigStep lib (okEnv req state keys pair th tail k o kq q E) done r) :
    BigStep lib (bodyEnv req state (takeArg keys pair th tail) (bothRows k o kq q) E)
      (offerTakeTree theta roles V fair done) r := by
  cases fair with
  | none => exact tree_present (.app .lam (.iteT hn (.case hj rfl (.var rfl))) hd)
  | some f => exact tree_present (.app .lam (.iteT hn (.case hj rfl (.iteT (hf f rfl) (.var rfl)))) hd)

/-- Both offers present, named, `ok` by the judge, and the instance's own compliance false: `unfairLegs`. -/
private theorem body_unfair {theta roles : List Label} {V : Ty} {f : Term}
    {done : Term} {lib : List Term} {req state : Val} {keys pair th k o kq q : Data} {E : Env} {tail : List (Label × Data)}
    (hn : BigStep lib (judgeEnv req state keys pair th tail k o kq q E) (offerNamedOkT (.var 3) (.var 4) (.var 5))
      (.ok (.bool true)))
    (hj : BigStep lib (judgeEnv req state keys pair th tail k o kq q E)
      (activityApply (offerJoint theta roles V) [.var 2, .var 0, .get (.var 5) "theta"])
      (.ok (.inj "ok" (.record []))))
    (hf : BigStep lib (okEnv req state keys pair th tail k o kq q E) f (.ok (.bool false))) :
    BigStep lib (bodyEnv req state (takeArg keys pair th tail) (bothRows k o kq q) E)
      (offerTakeTree theta roles V (some f) done) (.error (.refused "unfairLegs".toUTF8)) :=
  tree_present (.appA .lam (.iteT hn (.case hj rfl (.iteF hf .refuse))))

/-- Both offers present, the own pinned key not the one the deal names: `offerNotNamed`. -/
private theorem body_notNamed {theta roles : List Label} {V : Ty} {fair : Option Term}
    {done : Term} {lib : List Term} {req state : Val} {keys pair th k o kq q : Data} {E : Env} {tail : List (Label × Data)}
    (hn : BigStep lib (judgeEnv req state keys pair th tail k o kq q E) (offerNamedOkT (.var 3) (.var 4) (.var 5))
      (.ok (.bool false))) :
    BigStep lib (bodyEnv req state (takeArg keys pair th tail) (bothRows k o kq q) E)
      (offerTakeTree theta roles V fair done) (.error (.refused "offerNotNamed".toUTF8)) :=
  tree_present (.appA .lam (.iteF hn .refuse))

private theorem body_refused {theta roles : List Label} {V : Ty} {fair : Option Term}
    {done : Term} {lib : List Term} {req state : Val} {keys pair th k o kq q : Data} {E : Env} {tail : List (Label × Data)}
    {why : String} (hw : why = "sameRole" ∨ why = "notCompliant")
    (hn : BigStep lib (judgeEnv req state keys pair th tail k o kq q E) (offerNamedOkT (.var 3) (.var 4) (.var 5))
      (.ok (.bool true)))
    (hj : BigStep lib (judgeEnv req state keys pair th tail k o kq q E)
      (activityApply (offerJoint theta roles V) [.var 2, .var 0, .get (.var 5) "theta"])
      (.ok (.inj "refused" (.bytes why.toUTF8)))) :
    BigStep lib (bodyEnv req state (takeArg keys pair th tail) (bothRows k o kq q) E)
      (offerTakeTree theta roles V fair done) (.error (.refused why.toUTF8)) := by
  refine tree_present (.appA .lam (.iteT hn (.case hj rfl ?_)))
  rcases hw with rfl | rfl
  · have hb := BigStep.prim (lib := lib) (p := .beq) (x := .bytes "sameRole".toUTF8) (y := .bytes "sameRole".toUTF8)
      (a := .var 0) (b := .bytes "sameRole".toUTF8)
      (env := Val.bytes "sameRole".toUTF8 :: judgeEnv req state keys pair th tail k o kq q E) (.var rfl) .bytes
      (by simp [primEval])
    have he : primEval .beq (.bytes "sameRole".toUTF8) (.bytes "sameRole".toUTF8) = .ok (.bool true) := by
      simp [primEval]
    rw [he] at hb
    exact .iteT hb .refuse
  · have hb := BigStep.prim (lib := lib) (p := .beq) (x := .bytes "notCompliant".toUTF8) (y := .bytes "sameRole".toUTF8)
      (a := .var 0) (b := .bytes "sameRole".toUTF8)
      (env := Val.bytes "notCompliant".toUTF8 :: judgeEnv req state keys pair th tail k o kq q E) (.var rfl) .bytes
      (by simp [primEval])
    have he : primEval .beq (.bytes "notCompliant".toUTF8) (.bytes "sameRole".toUTF8) = .ok (.bool false) := by
      simp [primEval]; decide
    rw [he] at hb
    exact .iteF hb .refuse

/-- The judge inside the take, typed at `V`, sees the own value, the peer's, and the decoded θ. -/
private theorem judge_in_tree {theta roles : List Label} {V : Ty} {lib : List Term} {req state : Val}
    {keys pair th k o kq q ro ot rq qt : Data} {E : Env} {tail : List (Label × Data)} (hR : (offerRoleTy roles).wf = true)
    (hor : o.field "role" = some ro) (hro : Conforms ro (offerRoleTy roles))
    (hot : o.field "terms" = some ot) (hotc : Conforms ot (offerTermsTy theta))
    (hqr : q.field "role" = some rq) (hrq : Conforms rq (offerRoleTy roles))
    (hqt : q.field "terms" = some qt) (hqtc : Conforms qt (offerTermsTy theta))
    (hth : Conforms th (offerThetaTy theta)) :
    ∃ v, BigStep lib (judgeEnv req state keys pair th tail k o kq q E)
      (activityApply (offerJoint theta roles V) [.var 2, .var 0, .get (.var 5) "theta"]) (.ok v) ∧
      ((o.field "role" = q.field "role" ∧ v = .inj "refused" (.bytes "sameRole".toUTF8)) ∨
       (JointOk (offerLabels theta) o q th ∧ v = .inj "ok" (.record [])) ∨
       (o.field "role" ≠ q.field "role" ∧ ¬ JointOk (offerLabels theta) o q th ∧
         v = .inj "refused" (.bytes "notCompliant".toUTF8))) :=
  offerJoint_eval hR hor hro hot hotc hqr hrq hqt hqtc hth (BigStep.var (i := 2) rfl) (BigStep.var (i := 0) rfl)
    (get_data (ℓ := "theta") (x := th) (BigStep.var (i := 5) rfl) rfl)

/-- The offer's own take: the judge at `Std.offer`'s values. -/
private theorem judge_in_take {theta roles : List Label} {lib : List Term} {req state : Val}
    {keys pair th k o kq q : Data} {E : Env} {tail : List (Label × Data)} (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (offerValTy theta roles)) (hq : Conforms q (offerValTy theta roles))
    (hth : Conforms th (offerThetaTy theta)) :
    ∃ v, BigStep lib (judgeEnv req state keys pair th tail k o kq q E)
      (activityApply (offerJoint theta roles (offerValTy theta roles)) [.var 2, .var 0, .get (.var 5) "theta"])
        (.ok v) ∧
      ((o.field "role" = q.field "role" ∧ v = .inj "refused" (.bytes "sameRole".toUTF8)) ∨
       (JointOk (offerLabels theta) o q th ∧ v = .inj "ok" (.record [])) ∨
       (o.field "role" ≠ q.field "role" ∧ ¬ JointOk (offerLabels theta) o q th ∧
         v = .inj "refused" (.bytes "notCompliant".toUTF8))) := by
  obtain ⟨⟨ro, hor, hro⟩, ⟨ot, hot, hotc⟩⟩ := offer_fields ho
  obtain ⟨⟨rq, hqr, hrq⟩, ⟨qt, hqt, hqtc⟩⟩ := offer_fields hq
  exact judge_in_tree hR hor hro hot hotc hqr hrq hqt hqtc hth

/-- The method term, applied as the receiver applies it, runs its body over `[req, arg, state, rows]`. -/
private theorem method_app {S A R : Ty} {body : Term} {lib : List Term} {req state : Val} {arg rows : Data}
    {env : Env} {r : Except Fault Val}
    (h : BigStep lib (bodyEnv req state arg rows (req :: arg.toVal :: state :: rows.toVal :: env)) body r) :
    BigStep lib (req :: arg.toVal :: state :: rows.toVal :: env)
      (activityApply (activityMethod S A R body) [.var 3, .var 2, .var 1, .var 0]) r := by
  unfold activityApply activityMethod
  simp only [List.foldl]
  exact .app (.app (.app (.app .lam (.var rfl) .lam) (.var rfl) .lam) (.var rfl) .lam) (.var rfl) h

/-! ### The named offer -/

theorem keys_shape {keys : Data} (h : Conforms keys offerKeysTy) :
    ∃ na nb, keys = .record [("a", .nat na), ("b", .nat nb)] := by
  unfold offerKeysTy at h
  cases h with
  | record hr => cases hr with
    | cons h1 hr => cases hr with
      | cons h2 hr => cases hr; cases h1; cases h2; exact ⟨_, _, rfl⟩

theorem pair_shape {pair : Data} (h : Conforms pair pairTy) :
    ∃ a b, pair = .record [("a", .digest a), ("b", .digest b)] := by
  unfold pairTy at h
  cases h with
  | record hr => cases hr with
    | cons h1 hr => cases hr with
      | cons h2 hr => cases hr; cases h1; cases h2; exact ⟨_, _, rfl⟩

theorem key_shape {k : Data} (h : Conforms k (.record [("n", .nat)])) : ∃ n, k = .record [("n", .nat n)] := by
  cases h with
  | record hr => cases hr with
    | cons h1 hr => cases hr; cases h1; exact ⟨_, rfl⟩

/-- `offerNamedOkT` over operands that mean the own point `{key k, …}`, a request whose `self` is
`sb`, and an argument `{keys, pair, …}`: a Boolean, true exactly when `k` is the key the deal names
for `sb`. -/
theorem offerNamedOk_eval {lib : List Term} {env : Env} {pt rq ag : Term} {keys pair k : Data}
    {sb : ByteArray}
    (hk : BigStep lib env (.get pt "key") (.ok k.toVal))
    (hs : BigStep lib env (.get rq "self") (.ok (.digest sb)))
    (hpa : BigStep lib env (.get ag "pair") (.ok pair.toVal))
    (hke : BigStep lib env (.get ag "keys") (.ok keys.toVal))
    (hkeys : Conforms keys offerKeysTy) (hpair : Conforms pair pairTy) (hkc : Conforms k (.record [("n", .nat)])) :
    ∃ b, BigStep lib env (offerNamedOkT pt rq ag) (.ok (.bool b)) ∧ (b = true ↔ NamedKey sb keys pair k) := by
  obtain ⟨na, nb, rfl⟩ := keys_shape hkeys
  obtain ⟨a, b, rfl⟩ := pair_shape hpair
  obtain ⟨n, rfl⟩ := key_shape hkc
  have hkey : BigStep lib env (.get (.get pt "key") "n") (.ok (Data.nat n).toVal) :=
    get_data (d := .record [("n", .nat n)]) (x := .nat n) hk rfl
  have hpa' : BigStep lib env (.get (.get ag "pair") "a") (.ok (Data.digest a).toVal) :=
    get_data (d := .record [("a", .digest a), ("b", .digest b)]) (x := .digest a) hpa rfl
  have hka : BigStep lib env (.get (.get ag "keys") "a") (.ok (Data.nat na).toVal) :=
    get_data (d := .record [("a", .nat na), ("b", .nat nb)]) (x := .nat na) hke rfl
  have hkb : BigStep lib env (.get (.get ag "keys") "b") (.ok (Data.nat nb).toVal) :=
    get_data (d := .record [("a", .nat na), ("b", .nat nb)]) (x := .nat nb) hke rfl
  have hdeq : BigStep lib env (.prim .deq (.get rq "self") (.get (.get ag "pair") "a"))
      (.ok (.bool (decide (sb = a)))) :=
    BigStep.prim (x := .digest sb) (y := .digest a) hs hpa' (by simp [primEval])
  have hnamed : BigStep lib env (offerNamedT rq ag) (.ok (.nat (if sb = a then na else nb))) := by
    unfold offerNamedT
    by_cases h : sb = a
    · rw [if_pos h]; exact .iteT (by simpa [h] using hdeq) hka
    · rw [if_neg h]; exact .iteF (by simpa [h] using hdeq) hkb
  refine ⟨decide (n = if sb = a then na else nb),
    BigStep.prim (x := .nat n) (y := .nat (if sb = a then na else nb)) hkey hnamed (by simp [primEval]), ?_⟩
  simp only [decide_eq_true_eq, NamedKey]
  constructor
  · intro h; exact ⟨a, b, na, nb, rfl, rfl, by rw [h]⟩
  · rintro ⟨a', b', na', nb', h1, h2, h3⟩
    simp only [Data.record.injEq, List.cons.injEq, Prod.mk.injEq, Data.nat.injEq, Data.digest.injEq, true_and,
      and_true] at h1 h2 h3
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    exact h3

/-- The named check inside the take, over a request `rq` whose `self` is `sb`. -/
private theorem named_in_take {lib : List Term} {state : Val} {rq keys pair th k o kq q : Data} {E : Env} {tail : List (Label × Data)}
    {sb : ByteArray} (hself : rq.field "self" = some (.digest sb))
    (hkeys : Conforms keys offerKeysTy) (hpair : Conforms pair pairTy) (hkc : Conforms k (.record [("n", .nat)])) :
    ∃ b, BigStep lib (judgeEnv rq.toVal state keys pair th tail k o kq q E) (offerNamedOkT (.var 3) (.var 4) (.var 5))
      (.ok (.bool b)) ∧ (b = true ↔ NamedKey sb keys pair k) :=
  offerNamedOk_eval (get_data (d := pointD k (some o)) (BigStep.var (i := 3) rfl) rfl)
    (get_data (x := .digest sb) (BigStep.var (i := 4) rfl) hself)
    (get_data (d := takeArg keys pair th tail) (BigStep.var (i := 5) rfl) rfl)
    (get_data (d := takeArg keys pair th tail) (BigStep.var (i := 5) rfl) rfl) hkeys hpair hkc

/-- **Each party's honesty** (method-term grain, the generated `take` as the receiver applies it,
over the env `[req, arg, state, rows]` it builds): with both offer slots pinned and present (own
point `k`/`o`, peer point `kq`/`q`), the argument `{keys, pair, theta := th}` and a request whose
`self` is `sb`, the take returns iff its own pinned offer is the one the deal NAMES for `sb`
(`NamedKey`) and `JointOk`: it checks the name and judges the pair itself, whoever called it. The
matcher's code is not a premise. Mutation P2 (`take` without the judge: the `ok` arm taken
unconditionally) makes it false at F2 (buyer `[5,10]`, seller `[11,12]`, θ = 11: the mutant
returns, `JointOk` is false); mutation PA (the name check skipped) at LF8 (the deal names Y's offer
1, the pin is Y's offer 0: the mutant returns, `NamedKey` is false). -/
theorem take_iff_compliant {theta roles : List Label} {rels : List (Label × RelDecl)} {od sd : RelDecl}
    {lib : List Term} {env : Env} {state : Val} {rq keys pair th k o kq q : Data} {sb : ByteArray}
    (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (offerValTy theta roles)) (hq : Conforms q (offerValTy theta roles))
    (hth : Conforms th (offerThetaTy theta)) (hself : rq.field "self" = some (.digest sb))
    (hkeys : Conforms keys offerKeysTy) (hpair : Conforms pair pairTy) (hk : Conforms k (.record [("n", .nat)])) :
    (∃ v, BigStep lib (rq.toVal :: (Data.record [("keys", keys), ("pair", pair), ("theta", th)]).toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
          env)
      (activityApply (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels)
        (offerTakeBody theta roles rels od sd)) [.var 3, .var 2, .var 1, .var 0]) (.ok v)) ↔
    NamedKey sb keys pair k ∧ JointOk (offerLabels theta) o q th := by
  obtain ⟨v, hv, hd⟩ := judge_in_take (lib := lib) (tail := []) (req := rq.toVal) (state := state) (keys := keys) (pair := pair)
    (k := k) (kq := kq) (E := rq.toVal :: (takeArg keys pair th []).toVal :: state :: (bothRows k o kq q).toVal :: env) hR ho hq hth
  obtain ⟨nb, hnb, hni⟩ := named_in_take (lib := lib) (tail := []) (state := state) (th := th) (o := o) (kq := kq) (q := q)
    (E := rq.toVal :: (takeArg keys pair th []).toVal :: state :: (bothRows k o kq q).toVal :: env) hself hkeys hpair hk
  cases nb with
  | false =>
    constructor
    · rintro ⟨w, hw⟩
      cases bigStep_deterministic hw (method_app (body_notNamed hnb))
    · rintro ⟨hnk, -⟩
      cases hni.mpr hnk
  | true =>
    constructor
    · rintro ⟨w, hw⟩
      rcases hd with ⟨-, rfl⟩ | ⟨hok, -⟩ | ⟨-, -, rfl⟩
      · cases bigStep_deterministic hw (method_app (body_refused (.inl rfl) hnb hv))
      · exact ⟨hni.mp rfl, hok⟩
      · cases bigStep_deterministic hw (method_app (body_refused (.inr rfl) hnb hv))
    · rintro ⟨-, hok⟩
      rcases hd with ⟨hr, -⟩ | ⟨-, rfl⟩ | ⟨-, hn, -⟩
      · exact absurd hr hok.1
      · exact ⟨_, method_app (body_ok hnb hv (fun (f : Term) (e : (none : Option Term) = some f) => nomatch e) .record)⟩
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

/-- Both offers present, the own pinned offer not the one the deal names for `self` (`¬ NamedKey`):
`offerNotNamed`, before the judge reads either value. Mutation PA (the check skipped): false at LF8. -/
theorem take_offerNotNamed {theta roles : List Label} {rels : List (Label × RelDecl)} {od sd : RelDecl}
    {lib : List Term} {env : Env} {state : Val} {rq keys pair th k o kq q : Data} {sb : ByteArray}
    (hself : rq.field "self" = some (.digest sb))
    (hkeys : Conforms keys offerKeysTy) (hpair : Conforms pair pairTy) (hk : Conforms k (.record [("n", .nat)]))
    (hn : ¬ NamedKey sb keys pair k) :
    BigStep lib (rq.toVal :: (Data.record [("keys", keys), ("pair", pair), ("theta", th)]).toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
          env)
      (activityApply (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels)
        (offerTakeBody theta roles rels od sd)) [.var 3, .var 2, .var 1, .var 0])
      (.error (.refused "offerNotNamed".toUTF8)) := by
  obtain ⟨nb, hnb, hni⟩ := named_in_take (lib := lib) (tail := []) (state := state) (th := th) (o := o) (kq := kq) (q := q)
    (E := rq.toVal :: (takeArg keys pair th []).toVal :: state :: (bothRows k o kq q).toVal :: env) hself hkeys hpair hk
  cases nb with
  | false => exact method_app (body_notNamed hnb)
  | true => exact absurd (hni.mp rfl) hn

/-- Both offers present and the own one named, equal chooser roles: `sameRole`. Mutation: the two
refusal names swapped. -/
theorem take_sameRole {theta roles : List Label} {rels : List (Label × RelDecl)} {od sd : RelDecl}
    {lib : List Term} {env : Env} {state : Val} {rq keys pair th k o kq q : Data} {sb : ByteArray}
    (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (offerValTy theta roles)) (hq : Conforms q (offerValTy theta roles))
    (hth : Conforms th (offerThetaTy theta)) (hself : rq.field "self" = some (.digest sb))
    (hkeys : Conforms keys offerKeysTy) (hpair : Conforms pair pairTy) (hk : Conforms k (.record [("n", .nat)]))
    (hnk : NamedKey sb keys pair k) (hr : o.field "role" = q.field "role") :
    BigStep lib (rq.toVal :: (Data.record [("keys", keys), ("pair", pair), ("theta", th)]).toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
          env)
      (activityApply (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels)
        (offerTakeBody theta roles rels od sd)) [.var 3, .var 2, .var 1, .var 0])
      (.error (.refused "sameRole".toUTF8)) := by
  obtain ⟨v, hv, hd⟩ := judge_in_take (lib := lib) (tail := []) (req := rq.toVal) (state := state) (keys := keys) (pair := pair)
    (k := k) (kq := kq) (E := rq.toVal :: (takeArg keys pair th []).toVal :: state :: (bothRows k o kq q).toVal :: env) hR ho hq hth
  obtain ⟨nb, hnb, hni⟩ := named_in_take (lib := lib) (tail := []) (state := state) (th := th) (o := o) (kq := kq) (q := q)
    (E := rq.toVal :: (takeArg keys pair th []).toVal :: state :: (bothRows k o kq q).toVal :: env) hself hkeys hpair hk
  cases nb with
  | false => cases hni.mpr hnk
  | true =>
    rcases hd with ⟨-, rfl⟩ | ⟨hok, -⟩ | ⟨hn, -, -⟩
    · exact method_app (body_refused (.inl rfl) hnb hv)
    · exact absurd hr hok.1
    · exact absurd hr hn

/-- Both offers present and the own one named, different roles, θ outside a box: `notCompliant`. -/
theorem take_notCompliant {theta roles : List Label} {rels : List (Label × RelDecl)} {od sd : RelDecl}
    {lib : List Term} {env : Env} {state : Val} {rq keys pair th k o kq q : Data} {sb : ByteArray}
    (hR : (offerRoleTy roles).wf = true)
    (ho : Conforms o (offerValTy theta roles)) (hq : Conforms q (offerValTy theta roles))
    (hth : Conforms th (offerThetaTy theta)) (hself : rq.field "self" = some (.digest sb))
    (hkeys : Conforms keys offerKeysTy) (hpair : Conforms pair pairTy) (hk : Conforms k (.record [("n", .nat)]))
    (hnk : NamedKey sb keys pair k) (hr : o.field "role" ≠ q.field "role")
    (hn : ¬ JointOk (offerLabels theta) o q th) :
    BigStep lib (rq.toVal :: (Data.record [("keys", keys), ("pair", pair), ("theta", th)]).toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
          env)
      (activityApply (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels)
        (offerTakeBody theta roles rels od sd)) [.var 3, .var 2, .var 1, .var 0])
      (.error (.refused "notCompliant".toUTF8)) := by
  obtain ⟨v, hv, hd⟩ := judge_in_take (lib := lib) (tail := []) (req := rq.toVal) (state := state) (keys := keys) (pair := pair)
    (k := k) (kq := kq) (E := rq.toVal :: (takeArg keys pair th []).toVal :: state :: (bothRows k o kq q).toVal :: env) hR ho hq hth
  obtain ⟨nb, hnb, hni⟩ := named_in_take (lib := lib) (tail := []) (state := state) (th := th) (o := o) (kq := kq) (q := q)
    (E := rq.toVal :: (takeArg keys pair th []).toVal :: state :: (bothRows k o kq q).toVal :: env) hself hkeys hpair hk
  cases nb with
  | false => cases hni.mpr hnk
  | true =>
    rcases hd with ⟨he, -⟩ | ⟨hok, -⟩ | ⟨-, -, rfl⟩
    · exact absurd he hr
    · exact absurd hok hn
    · exact method_app (body_refused (.inr rfl) hnb hv)

/-! ## The package: closed facts about the generator's method table -/

private theorem slot_p1 : slotLabels "p" 1 = ["p0"] := by decide
private theorem slot_e2 : slotLabels "e" 2 = ["e0", "e1"] := by decide

private theorem take_rowsOf (theta roles : List Label) (ol sl : Nat) :
    rowsOf (offerRels theta roles ol sl) (offerTakeRows (offerRels theta roles ol sl)) =
      some (offerRead, offerRead) := by
  simp [rowsOf, offerTakeRows, rowsTy, readsTy, offerRead, offerRels, Row.find?, relReadTy, readsOf,
    relReadOf, relReadShape, peerLabel, slot_p1, Row.sort, Row.insert, pointsMax, rangeRowsMax]

/-- The take resolves to its declared signature: argument `{pair, theta}`, no calls, the one offer
point read under itself and under its peer, two edits. -/
private theorem take_resolve {D : Type} {theta roles : List Label} {ol sl pt b : Nat} {x : Label × Sig}
    (h : resolveMethod (D := D) (offerPackageOf theta roles ol sl pt b) offerTakeIx = .ok x) :
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

private theorem take_peerReads (theta roles : List Label) (ol sl pt b : Nat) :
    (offerPackageOf theta roles ol sl pt b).peerReads "take" = offerRead := by
  simp [Package.peerReads, offerPackageOf, recordRow, Row.find?, methodPeer, methodTy, take_rowsOf]

/-! ## Relocation: the take and fuse terms name no closure package -/

private theorem noRef_offerInBox : ∀ (fs : List Label) {terms th : Term}, NoRef terms → NoRef th →
    NoRef (offerInBox fs terms th)
  | [], _, _, _, _ => trivial
  | _ :: fs, _, _, ht, hth => ⟨⟨⟨ht, hth⟩, ⟨hth, ht⟩, trivial⟩, noRef_offerInBox fs ht hth, trivial⟩

/-- The joint judge names no closure package. -/
theorem noRef_offerJoint (theta roles : List Label) (V : Ty) : NoRef (offerJoint theta roles V) := by
  simp [offerJoint, eqData, NoRef, NoRefRow, refusedT, okT, andT, noRef_eqDataBody, noRef_offerInBox]

private theorem noRef_take (theta roles : List Label) (rels : List (Label × RelDecl)) (od sd : RelDecl) :
    NoRef (activityMethod offerStateTy (offerTakeArg theta) (offerTakeRows rels) (offerTakeBody theta roles rels od sd)) := by
  simp [activityMethod, offerTakeBody, NoRef, NoRefRow, activityResult, activityResultCalls, activityEdit, resultT, activityKeyTerm,
    noCallT, someCallT, slot_e2, activityApply, noRef_offerJoint, offerNamedOkT, offerNamedT, offerTakeTree, offerUnwrap, offerGate,
    offerTakeDone, offerTakeEdits]

/-! ## The deployed run of `take` -/

/-- A conforming take argument is `{keys, pair, theta}` (`Std.offer`'s and the escrow's). -/
theorem offerTakeArg_cases {theta : List Label} {ad : Data} (h : Conforms ad (offerTakeArg theta)) :
    ∃ keys pair th, ad = .record [("keys", keys), ("pair", pair), ("theta", th)] ∧ Conforms keys offerKeysTy ∧
      Conforms pair pairTy ∧ Conforms th (offerThetaTy theta) := by
  cases h with
  | record hr =>
    cases hr with
    | cons h0 hr => cases hr with
      | cons h1 hr => cases hr with
        | cons h2 hr => cases hr; exact ⟨_, _, _, rfl, h0, h1, h2⟩

/-- A conforming point slot: unpinned, pinned absent, or pinned present. -/
theorem point_cases {d : RelDecl} {X : Data} (h : Conforms X (optTy (pointRecTy d false))) :
    X = .inj "none" (.record []) ∨ ∃ k, Conforms k (keyTy d) ∧
      (X = .inj "some" (.record [("key", k), ("val", .inj "none" (.record []))]) ∨
        ∃ o, Conforms o d.val ∧ X = .inj "some" (.record [("key", k), ("val", .inj "some" o)])) := by
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

private theorem take_rowsTy (od sd : RelDecl) :
    offerTakeRows [("offer", od), ("session", sd)] =
      .record [("offer", .record [("p0", optTy (pointRecTy od false))]),
        ("peer", .record [("offer", .record [("p0", optTy (pointRecTy od false))])])] := by
  simp [offerTakeRows, rowsTy, readsTy, offerRead, Row.find?, relReadTy, slot_p1, peerLabel,
    Row.sort, Row.insert]

/-- A record with one field. -/
theorem rec1_cases {d : Data} {l : Label} {T : Ty} (h : Conforms d (.record [(l, T)])) :
    ∃ x, d = .record [(l, x)] ∧ Conforms x T := by
  cases h with
  | record hr => cases hr with
    | cons h1 hr => cases hr; exact ⟨_, rfl, h1⟩

/-- A conforming take rows argument, over relations `offer` and `session`: its own point slot and
its peer's. -/
theorem offerTakeRows_cases {od sd : RelDecl} {wd : Data}
    (h : Conforms wd (offerTakeRows [("offer", od), ("session", sd)])) :
    ∃ X Y, wd = .record [("offer", .record [("p0", X)]), ("peer", .record [("offer", .record [("p0", Y)])])] ∧
      Conforms X (optTy (pointRecTy od false)) ∧ Conforms Y (optTy (pointRecTy od false)) := by
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

/-! ### The take's tree, inverted -/

/-- **A returned take passed every check of its tree** (`offerTakeTree`, the term both `Std.offer`'s
take and the escrow's run, as the receiver applies the method: `fwd` carries the body's result out to
the run). Its own slot and its peer's held offers `o` and `q` (pinned keys `k`, `kq`), `k` is the key
the deal names for `self` (`NamedKey`), the two are `JointOk` at θ (their `role` and `terms`), the
instance's own compliance `fair`, if it declares one, evaluated `true` in the `ok` arm's environment
(LANG-82: given `hfe`, that it evaluates to a Boolean there), and the result is the `ok` arm's record
`done`, its fields suspended in that environment. -/
theorem offerTakeTree_inv {theta roles : List Label} {V : Ty} {fair : Option Term}
    {done : Term} {fs : List (Label × Term)} {d : RelDecl} {lib : List Term} {E env0 : Env} {tail : List (Label × Data)} {t0 : Term}
    {state : Val} {rq keys pair th X Y : Data} {sb : ByteArray} {v : Val}
    (hval : ∀ {u : Data}, Conforms u d.val →
      (∃ ru, u.field "role" = some ru ∧ Conforms ru (offerRoleTy roles)) ∧
        (∃ tu, u.field "terms" = some tu ∧ Conforms tu (offerTermsTy theta)))
    (hR : (offerRoleTy roles).wf = true) (hkt : keyTy d = .record [("n", .nat)])
    (hth : Conforms th (offerThetaTy theta)) (hself : rq.field "self" = some (.digest sb))
    (hkeys : Conforms keys offerKeysTy) (hpair : Conforms pair pairTy)
    (hX : Conforms X (optTy (pointRecTy d false))) (hY : Conforms Y (optTy (pointRecTy d false)))
    (hd : done = .record fs)
    (hfe : ∀ f, fair = some f → ∀ k o kq q, Conforms o d.val → Conforms q d.val → ∃ b, BigStep lib
      (.record [] :: q.toVal :: (Data.record [("key", kq), ("val", .inj "some" q)]).toVal ::
        o.toVal :: (Data.record [("key", k), ("val", .inj "some" o)]).toVal :: rq.toVal ::
        (takeArg keys pair th tail).toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
          E) f (.ok (.bool b)))
    (fwd : ∀ {r : Except Fault Val}, BigStep lib (rq.toVal ::
        (takeArg keys pair th tail).toVal :: state ::
        (Data.record [("offer", .record [("p0", X)]), ("peer", .record [("offer", .record [("p0", Y)])])]).toVal :: E)
        (offerTakeTree theta roles V fair done) r → BigStep lib env0 t0 r)
    (h : BigStep lib env0 t0 (.ok v)) :
    ∃ k o kq q, X = .inj "some" (.record [("key", k), ("val", .inj "some" o)]) ∧
      Y = .inj "some" (.record [("key", kq), ("val", .inj "some" q)]) ∧
      Conforms k (keyTy d) ∧ Conforms o d.val ∧ Conforms q d.val ∧
      NamedKey sb keys pair k ∧ JointOk (offerLabels theta) o q th ∧
      (∀ f, fair = some f → BigStep lib (.record [] :: q.toVal :: (Data.record [("key", kq), ("val", .inj "some" q)]).toVal ::
        o.toVal :: (Data.record [("key", k), ("val", .inj "some" o)]).toVal :: rq.toVal ::
        (takeArg keys pair th tail).toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
          E) f (.ok (.bool true))) ∧
      v = .record (suspend (.record [] :: q.toVal :: (Data.record [("key", kq), ("val", .inj "some" q)]).toVal ::
        o.toVal :: (Data.record [("key", k), ("val", .inj "some" o)]).toVal :: rq.toVal ::
        (takeArg keys pair th tail).toVal :: state ::
        (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
          E) fs) := by
  rcases point_cases hX with rfl | ⟨k, hk, rfl | ⟨o, ho, rfl⟩⟩
  · cases bigStep_deterministic h (fwd body_offerUnpinned)
  · cases bigStep_deterministic h (fwd body_noOffer)
  rcases point_cases hY with rfl | ⟨kq, hkq, rfl | ⟨q, hq, rfl⟩⟩
  · cases bigStep_deterministic h (fwd body_peerRowUnpinned)
  · cases bigStep_deterministic h (fwd body_noPeerOffer)
  obtain ⟨nb, hnb, hni⟩ := named_in_take (lib := lib) (tail := tail) (state := state) (rq := rq) (th := th) (o := o) (kq := kq)
    (q := q) (E := E) hself hkeys hpair (hkt ▸ hk)
  cases nb with
  | false => cases bigStep_deterministic h (fwd (body_notNamed hnb))
  | true =>
  obtain ⟨⟨ro, hor, hro⟩, ⟨ot, hot, hotc⟩⟩ := hval ho
  obtain ⟨⟨rq', hqr, hrq⟩, ⟨qt, hqt, hqtc⟩⟩ := hval hq
  obtain ⟨jv, hjv, hjd⟩ := judge_in_tree (V := V) (lib := lib) (tail := tail) (req := rq.toVal) (state := state) (keys := keys)
    (pair := pair) (k := k) (kq := kq) (E := E) hR hor hro hot hotc hqr hrq hqt hqtc hth
  rcases hjd with ⟨-, rfl⟩ | ⟨hok, rfl⟩ | ⟨-, -, rfl⟩
  · cases bigStep_deterministic h (fwd (body_refused (.inl rfl) hnb hjv))
  · subst hd
    cases fair with
    | none =>
      cases bigStep_deterministic h (fwd (body_ok hnb hjv (fun (f : Term) (e : (none : Option Term) = some f) => nomatch e) .record))
      refine ⟨k, o, kq, q, rfl, rfl, hk, ho, hq, hni.mp rfl, hok, ?_, rfl⟩
      intro f e
      cases e
    | some f =>
      obtain ⟨b, hb⟩ := hfe f rfl k o kq q ho hq
      cases b with
      | false => cases bigStep_deterministic h (fwd (body_unfair hnb hjv hb))
      | true =>
        cases bigStep_deterministic h (fwd (body_ok hnb hjv (fun f' e => by cases e; exact hb) .record))
        refine ⟨k, o, kq, q, rfl, rfl, hk, ho, hq, hni.mp rfl, hok, ?_, rfl⟩
        intro f' e
        cases e
        exact hb
  · cases bigStep_deterministic h (fwd (body_refused (.inr rfl) hnb hjv))

/-! ### The take's two edits -/

/-- **What the take's edits row means** (`offerTakeEdits`, as `Std.offer`'s and the escrow's results
write it, over relations `offer` and `session`), in any environment whose own point (var 4), request
(var 5) and argument (var 6) mean key `k`, `{agent, notBefore}` and `{pair, theta}`: the retract of
the own offer at `k`, and the session insert keyed by the request's agent and time, capturing
`{pair, theta}` unanswered. -/
theorem offerTakeEdits_means {theta : List Label} {od : RelDecl} {sl : Nat} {lib : List Term} {env : Env}
    {k pair th : Data} {agent : ByteArray} {nb : Nat} (hret : od.retract = true)
    (hk : BigStep lib env (.get (.var 4) "key") (.ok k.toVal)) (hkc : Conforms k (keyTy od))
    (hag : BigStep lib env (.get (.var 5) "agent") (.ok (.digest agent)))
    (hnb : BigStep lib env (.get (.var 5) "notBefore") (.ok (.nat nb)))
    (hpa : BigStep lib env (.get (.var 6) "pair") (.ok pair.toVal)) (hpair : Conforms pair pairTy)
    (htv : BigStep lib env (.get (.var 6) "theta") (.ok th.toVal)) (hth : Conforms th (offerThetaTy theta))
    {W : Val}
    (hW : BigStep lib env (.record ((slotLabels "e"
        (offerTakeEdits theta [("offer", od), ("session", offerSessionDecl theta sl)] od (offerSessionDecl theta sl)).length).zip
        ((offerTakeEdits theta [("offer", od), ("session", offerSessionDecl theta sl)] od (offerSessionDecl theta sl)).map
          fun t => someCallT (editTy [("offer", od), ("session", offerSessionDecl theta sl)]) t))) (.ok W)) :
    Means lib (.record ((slotLabels "e" 2).map fun l => (l, optTy (editTy [("offer", od), ("session", offerSessionDecl theta sl)])))) W
      (.record [("e0", .inj "some" (.inj "offer" (.inj "retract" (.record [("key", k)])))),
        ("e1", .inj "some" (.inj "session" (.inj "insert" (.record [
          ("key", .record [("agent", .digest agent), ("notBefore", .nat nb)]),
          ("val", .record [("answered", .inj "none" (.record [])),
            ("captured", .inj "settle" (.record [("pair", pair), ("theta", th)]))])]))))]) := by
  cases hW
  simp only [offerTakeEdits, List.length, slot_e2, activityEdit, List.map, List.zip, suspend, ↓reduceIte]
  have hkt : keyTy (offerSessionDecl theta sl) = .record [("agent", .digest), ("notBefore", .nat)] := rfl
  refine .record .record (.cons (.inj (.inj (.inj .record))) ?_ (.cons (.inj (.inj (.inj .record))) ?_ .nil))
  · refine .inj rfl (.inj rfl (.inj (A := .record [("key", keyTy od)]) (by simp [hret, Row.find?])
      (.record .record (.cons hk (means_toVal hkc) .nil))))
  · refine .inj rfl (.inj rfl (.inj (A := rowTy (offerSessionDecl theta sl)) (by simp [Row.find?]) (.record .record
      (.cons .record ?_ (.cons .record ?_ .nil)))))
    · rw [hkt]
      exact .record .record (.cons hag .digest (.cons hnb .nat .nil))
    · refine .record .record (.cons (.inj .record) (.inj rfl (.record .record .nil)) (.cons (.inj .record) ?_ .nil))
      exact .inj rfl (.record .record (.cons hpa (means_toVal hpair) (.cons htv (means_toVal hth) .nil)))

/-- **What the take's two edits read as**, under `self`, over relations `offer` (index 0) and
`session` (index 1): the own offer's retract and the session insert, each at its key's bytes. -/
theorem offerTake_editsOf {D : Type} {theta : List Label} {od : RelDecl} {sl : Nat} {self : D}
    {k K V : Data} {es : List (Edit D)} (hret : od.retract = true)
    (h : editsOf [("offer", od), ("session", offerSessionDecl theta sl)] self
      (.record [("e0", .inj "some" (.inj "offer" (.inj "retract" (.record [("key", k)])))),
        ("e1", .inj "some" (.inj "session" (.inj "insert" (.record [("key", K), ("val", V)]))))]) = .ok es) :
    ∃ kb sb vb, keyBytes od k = some kb ∧ keyBytes (offerSessionDecl theta sl) K = some sb ∧
      Wire.encodeData (offerSessionDecl theta sl).val V = some vb ∧
      es.map (fun x => (x.slot, x.act)) =
        [(Kernel.RowSlot.row ⟨self, 0, kb⟩, Kernel.RowAct.retract), (Kernel.RowSlot.row ⟨self, 1, sb⟩, Kernel.RowAct.insert 0 vb)] := by
  have i0 : List.findIdx? (fun x => decide (x.fst = "offer"))
      [("offer", od), ("session", offerSessionDecl theta sl)] = some 0 := rfl
  have i1 : List.findIdx? (fun x => decide (x.fst = "session"))
      [("offer", od), ("session", offerSessionDecl theta sl)] = some 1 := rfl
  have ha : amtOf (offerSessionDecl theta sl) V = 0 := rfl
  cases hk : keyBytes od k <;> cases hs : keyBytes (offerSessionDecl theta sl) K <;>
    cases hv : Wire.encodeData (offerSessionDecl theta sl).val V <;>
    simp [editsOf, editsOf.go, editOf, relIndex, i0, i1, Row.find?, hk, hs, hv, hret, ha, bind,
      Except.bind, pure, Except.pure] at h
  subst h
  exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩

/-- **The deployed take is sound** (`Lang.program`'s `run`, the run the kernel records, at
`activity_program_safe`'s grain): a run of method `take` of an object of the generated package
that RETURNED decoded the argument `{keys, pair, theta := th}`, built (by the declared peer read)
the rows `{offer: {p0: some {key k, val some o}}, peer: {offer: {p0: some {key kq, val some q}}}}`
from the caller's pins, its own pinned key `k` is the one the deal NAMES for `self` (`NamedKey`),
found `JointOk` of the two pinned offers and θ, makes no calls, and its row acts are exactly the
retract of that named offer at `⟨self, 0, keyBytes k⟩` and the insert of its
own session row at `⟨self, 1, keyBytes {agent, notBefore}⟩` with the value bytes of
`{answered := none, captured := settle {pair, theta := th}}`. Mutations: P2 (the judge skipped:
the run returns at F2, buyer `[5,10]` / seller `[11,12]` / θ = 11, where `JointOk` is false), and the
retract keyed by the peer's point (`.var 2`) instead of its own (`.var 4`): the first act's slot is
then the peer key's bytes. P5 (the retract became an upsert) is refused earlier, by `offer_guard`'s
`final`, so on P5 the run does not return and this theorem is not its tooth. PA (the name check
skipped): the run returns at LF8 with `k` Y's offer 0 where the deal names offer 1. -/
theorem take_run_sound {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D) {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl pt budget : Nat}
    {look : Kernel.Receive.Pinned D} {rv : Kernel.Receive.RowView D} {pkg : D} {state : Kernel.Slots}
    {args : ByteArray} {r : Kernel.Receive.Req D} {budget' : Nat} {s : Kernel.Slots}
    {calls : List (Kernel.Receive.Body D)} {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {used : Nat}
    (hR : (offerRoleTy roles).wf = true)
    (hid : digestOf (bytesOf pkg) = some pkg)
    (hp : readPackage look pkg = .ok (offerPackageOf theta roles ol sl pt budget))
    (h : (Lang.program bytesOf digestOf rc).run look rv pkg state offerTakeIx args r budget' =
      .ok (s, calls, rows, used)) :
    ∃ keys pair th k o kq q kb sb vb,
      Wire.decodeData (offerTakeArg theta) args = .ok (.record [("keys", keys), ("pair", pair), ("theta", th)]) ∧
      methodReads bytesOf digestOf rc look pkg (offerRels theta roles ol sl) rv r.self
        (.record [("keys", keys), ("pair", pair), ("theta", th)]) offerRead offerRead =
        .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
          ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]) ∧
      NamedKey (bytesOf r.self) keys pair k ∧ JointOk (offerLabels theta) o q th ∧ calls = [] ∧
      keyBytes (offerDecl theta roles ol) k = some kb ∧
      keyBytes (offerSessionDecl theta sl)
        (.record [("agent", .digest (bytesOf r.agent)), ("notBefore", .nat r.notBefore)]) = some sb ∧
      Wire.encodeData (offerSessionDecl theta sl).val
        (.record [("answered", .inj "none" (.record [])),
          ("captured", .inj "settle" (.record [("pair", pair), ("theta", th)]))]) = some vb ∧
      rows = [(.row ⟨r.self, 0, kb⟩, .retract), (.row ⟨r.self, 1, sb⟩, .insert 0 vb)] := by
  change (runMeasuredLive bytesOf digestOf rc look rv pkg state offerTakeIx args r budget').map _ = _ at h
  rw [runMeasuredLive_leaf_closed hid hp rfl rfl] at h
  cases hm : runMeasured bytesOf digestOf rc look rv pkg state offerTakeIx args r budget' with
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
  obtain ⟨keys, pair, th, rfl, hkeys, hpair, hth⟩ := offerTakeArg_cases (decodeData_conforms had)
  obtain ⟨X, Y, rfl, hX, hY⟩ := offerTakeRows_cases (methodReads_conforms hwd)
  have hbig := run_bigStep hrun
  have hself : (reqData bytesOf r).field "self" = some (.digest (bytesOf r.self)) := by
    simp [reqData, Data.field, Row.find?]
  have fwd : ∀ {r' : Except Fault Val}, BigStep L.lib
      [(reqData bytesOf r).toVal, (Data.record [("keys", keys), ("pair", pair), ("theta", th)]).toVal, sd.toVal,
        (Data.record [("offer", .record [("p0", X)]), ("peer", .record [("offer", .record [("p0", Y)])])]).toVal]
      (offerTakeBody theta roles (offerRels theta roles ol sl) (offerDecl theta roles ol) (offerSessionDecl theta sl)) r' →
      BigStep L.lib [(reqData bytesOf r).toVal, (Data.record [("keys", keys), ("pair", pair), ("theta", th)]).toVal,
        sd.toVal, (Data.record [("offer", .record [("p0", X)]), ("peer", .record [("offer", .record [("p0", Y)])])]).toVal]
        (apply4 g "take") r' :=
    fun hb => apply4_method hlib rfl (by simp [Row.find?, activityMethod]) (noRef_take _ _ _ _ _) hb
  obtain ⟨k, o, kq, q, rfl, rfl, hk, -, -, hnk, hok, -, rfl⟩ :=
    offerTakeTree_inv offer_fields hR rfl hth hself hkeys hpair hX hY rfl (fun (f : Term) (e : (none : Option Term) = some f) => nomatch e) fwd hbig
  have hM := extract_means _ _ hx
  have hwE := BigStep.get (ℓ := "edits") hbig (.field (find_suspend_of (t := .record ((slotLabels "e"
    (offerTakeEdits theta (offerRels theta roles ol sl) (offerDecl theta roles ol) (offerSessionDecl theta sl)).length).zip
    ((offerTakeEdits theta (offerRels theta roles ol sl) (offerDecl theta roles ol) (offerSessionDecl theta sl)).map
      fun t => someCallT (editTy (offerRels theta roles ol sl)) t))) rfl) .record)
  obtain ⟨A, hA, hmA⟩ := means_get hbig hM rfl hwE
  simp [Row.find?] at hA
  subst hA
  have hED := offerTakeEdits_means (lib := L.lib) (od := offerDecl theta roles ol) (sl := sl)
    (env := .record [] :: q.toVal :: (Data.record [("key", kq), ("val", .inj "some" q)]).toVal ::
      o.toVal :: (Data.record [("key", k), ("val", .inj "some" o)]).toVal :: (reqData bytesOf r).toVal ::
      (Data.record [("keys", keys), ("pair", pair), ("theta", th)]).toVal :: sd.toVal ::
      (Data.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
        ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]).toVal ::
        []) rfl
    (get_data (d := .record [("key", k), ("val", .inj "some" o)]) (BigStep.var (i := 4) rfl) rfl) hk
    (get_data (ℓ := "agent") (d := reqData bytesOf r) (x := .digest (bytesOf r.agent)) (BigStep.var (i := 5) rfl) rfl)
    (get_data (ℓ := "notBefore") (d := reqData bytesOf r) (x := .nat r.notBefore) (BigStep.var (i := 5) rfl) rfl)
    (get_data (d := .record [("keys", keys), ("pair", pair), ("theta", th)]) (BigStep.var (i := 6) rfl) rfl) hpair
    (get_data (d := .record [("keys", keys), ("pair", pair), ("theta", th)]) (BigStep.var (i := 6) rfl) rfl) hth .record
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
  obtain ⟨kb, sb, vb, hkb, hsb, hvb, hmap⟩ := offerTake_editsOf (od := offerDecl theta roles ol) rfl hes
  exact ⟨keys, pair, th, k, o, kq, q, kb, sb, vb, had, hwd, hnk, hok, rfl, hkb, hsb, hvb, hrows.trans hmap⟩

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
`JointOk` for the pair), and the generated take term, at every conforming θ with its own offer the
one the deal names, refuses the pair `notCompliant`. This is the arithmetic half of the deleted `separate_witnesses_over_substitutions`
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
    (∀ (th keys pair k kq rq : Data) (sb : ByteArray) (rels : List (Label × RelDecl)) (od sd : RelDecl)
        (lib : List Term) (env : Env) (state : Val), Conforms th (offerThetaTy ["price"]) →
        rq.field "self" = some (.digest sb) → Conforms keys offerKeysTy → Conforms pair pairTy →
        Conforms k (.record [("n", .nat)]) → NamedKey sb keys pair k →
      BigStep lib (rq.toVal :: (Data.record [("keys", keys), ("pair", pair), ("theta", th)]).toVal :: state ::
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
  · intro th keys pair k kq rq sb rels od sd lib env state hth hself hkeys hpair hk hnk
    exact take_notCompliant (o := buyerA) (q := sellerB) roles_wf buyerA_conforms sellerB_conforms hth hself hkeys
      hpair hk hnk hrole (hnot th)

/-- **A deal's session row leaves exactly from its deadline** (LANG-80): the package's session guard
(`offerSessionGuard`, `activityWaiting` at patience `pt`) admits the retraction of a session row
(always unanswered: nothing in the package answers it) iff the call's signed `notBefore` `m` is at
least the row key's `notBefore` `n` plus `pt`, whoever retracts; before that it refuses `unanswered`.
`waiting_retract_iff` (LANG-76) at the offer's guard. -/
theorem offer_session_retract_iff (theta : List Label) (sd : RelDecl) (pt n m : Nat) (key captured req : Data)
    (lib : List Term) (env : Env) (state : Val)
    (hk : key.field "notBefore" = some (.nat n)) (hr : req.field "notBefore" = some (.nat m))
    (hlim : n + pt < Bounds.natLimit) :
    (∃ w, BigStep lib
      ((Data.record [("edit", .inj "retract" (.record [("key", key)])), ("old", .inj "some" (.record [
        ("answered", .inj "none" (.record [])), ("captured", captured)]))]).toVal :: req.toVal :: state :: env)
      (activityApply (offerSessionGuard theta sd pt) [.var 2, .var 1, .var 0]) (.ok (.inj "ok" w))) ↔
      n + pt ≤ m := by
  have h := waiting_retract_iff offerStateTy [offerSettlePlan theta] sd offerResumer {} (some pt) n m key captured
    req none lib env state hk hr (fun P hP => by cases hP; exact hlim)
  simpa [offerSessionGuard] using h

end Nanodregg.Lang.Std
