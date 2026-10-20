/- Translation validation versus internal transport, Ringer et al. (2021) p7;
Viola–Fan–Ringer (2025) pp1–2. -/
import Lang.Contextual.RepairObjects

namespace Nanodregg.Lang.Contextual.TransportKinds

/-- Distinct data constructors record how a claim is justified; Valid is a separate Prop
(Ringer p7; Viola pp1–2). Merely constructing a claim is not evidence of validity. -/
inductive Claim (D : CalculusData) (E : Type) where
  | rechecked (evidence : RepairObjects.TransportEvidence D E)
  | internal (source target : Candidate D)

/-- Rechecked claims can be emitted only after the existing transport operation succeeds
(Ringer et al. p7). -/
def recheck {D : CalculusData} {E : Type} (registry : RepairObjects.Registry D E)
    (certificate : Nat) (w : World E) (c : Candidate D) (cost : Nat) :
    Except RepairObjects.TransportRefusal (Claim D E) :=
  match RepairObjects.transport registry certificate w c cost with
  | .error e => .error e
  | .ok (.transported ev) => .ok (.rechecked ev)
  | .ok (.existing _) => .error .unknownCertificate

/-- Quotient by the declared observable, permitting multiple concrete representatives
(Viola et al. p2). -/
abbrev Observed (A V : Type) (observe : A → V) :=
  Quot (fun a b : A => observe a = observe b)

/-- The quotient's observation is well-defined (Viola et al. pp1–2). -/
def observation {A V : Type} (observe : A → V) : Observed A V observe → V :=
  Quot.lift observe (fun _ _ h => h)

/-- Lift an observation-preserving representation map to quotients. The required proof is
kernel checked, not a Boolean recheck (Viola et al. p2). -/
def liftMap {A B V : Type} (a : A → V) (b : B → V) (f : A → B)
    (h : ∀ x, b (f x) = a x) : Observed A V a → Observed B V b :=
  Quot.lift (fun x => Quot.mk _ (f x)) (by
    intro x y he
    apply Quot.sound
    exact (h x).trans (he.trans (h y).symm))


/-- Consume the actual offered candidate from either evidence form; admission still goes
through the existing propose/select operations (Ringer p7; Viola pp1–2). -/
def Claim.destination {D : CalculusData} {E : Type} : Claim D E → Candidate D
  | .rechecked ev => ev.image
  | .internal _ target => target

end Nanodregg.Lang.Contextual.TransportKinds
