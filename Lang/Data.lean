/-
# Lang.Data — first-order data: what crosses between a program and the World

State fields, method arguments and law verdicts are `Data` at a data type (`Ty.isData`). `toVal`
puts data into the machine (a record's fields become suspensions that are already values);
`extract` forces a value of a data type back out, running each suspended field under the SAME
budget the run had left, so extraction is metered like everything else and a lazy field that
diverges exhausts the budget instead of hanging.
-/
import Lang.Eval

namespace Nanodregg.Lang

inductive Data
  | nat (value : Nat)
  | bool (value : Bool)
  | bytes (value : ByteArray)
  | record (fields : List (Label × Data))
  | inj (label : Label) (payload : Data)
  deriving Inhabited

mutual
def Data.toVal : Data → Val
  | .nat n => .nat n
  | .bool b => .bool b
  | .bytes s => .bytes s
  | .record fs => .record (Data.rowToVal fs)
  | .inj ℓ d => .inj ℓ d.toVal

def Data.rowToVal : List (Label × Data) → List (Label × (Term × List Val))
  | [] => []
  | (ℓ, d) :: fs => (ℓ, (.var 0, [d.toVal])) :: Data.rowToVal fs
end

/-- What extraction needs from the machine: the closure's bodies. -/
structure Machine where
  lib : List Term

/-- Run one suspension to a value, spending from `fuel`; returns the value and the fuel left. -/
def Machine.force (m : Machine) (fuel : Nat) (t : Term) (env : Env) : Except Fault (Val × Nat) :=
  match run m.lib Bounds.stackMax fuel 0 (State.init t env) with
  | .value v used => .ok (v, fuel - used)
  | .fault f _ => .error f

/-- Unfold knots until a record value appears; each unfolding is a metered run. -/
def Machine.unknot (m : Machine) : (rounds fuel : Nat) → Val → Except Fault (List (Label × (Term × Env)) × Nat)
  | _, fuel, .record fs => .ok (fs, fuel)
  | 0, _, .knot _ _ => .error .ticks
  | r + 1, fuel, v@(.knot body env) =>
      match m.force fuel body (v :: env) with
      | .ok (v', fuel') => m.unknot r fuel' v'
      | .error e => .error e
  | _, _, _ => .error .stuck

mutual
/-- Force a value of data type `T` into `Data`, spending from `fuel`. -/
def Machine.extract (m : Machine) : Ty → Nat → Val → Except Fault (Data × Nat)
  | .nat, fuel, .nat n => .ok (.nat n, fuel)
  | .bool, fuel, .bool b => .ok (.bool b, fuel)
  | .bytes, fuel, .bytes s => .ok (.bytes s, fuel)
  | .record row, fuel, v =>
      match m.unknot fuel fuel v with
      | .ok (fs, fuel') =>
          match m.extractRow row fuel' fs with
          | .ok (ds, fuel'') => .ok (.record ds, fuel'')
          | .error e => .error e
      | .error e => .error e
  | .sum row, fuel, .inj ℓ w =>
      match m.extractArm row ℓ fuel w with
      | .ok (d, fuel') => .ok (.inj ℓ d, fuel')
      | .error e => .error e
  | _, _, _ => .error .stuck

/-- Force an injection's payload at the type its label has in the sum row. -/
def Machine.extractArm (m : Machine) :
    List (Label × Ty) → Label → Nat → Val → Except Fault (Data × Nat)
  | [], _, _, _ => .error .stuck
  | (k, A) :: row, ℓ, fuel, w => if ℓ = k then m.extract A fuel w else m.extractArm row ℓ fuel w

/-- Force each suspended field at its type, in row order. -/
def Machine.extractRow (m : Machine) :
    List (Label × Ty) → Nat → List (Label × (Term × Env)) → Except Fault (List (Label × Data) × Nat)
  | [], fuel, [] => .ok ([], fuel)
  | (ℓ, A) :: row, fuel, (ℓ', (t, env)) :: fs =>
      if ℓ = ℓ' then
        match m.force fuel t env with
        | .ok (v, fuel') =>
            match m.extract A fuel' v with
            | .ok (d, fuel'') =>
                match m.extractRow row fuel'' fs with
                | .ok (ds, f) => .ok ((ℓ, d) :: ds, f)
                | .error e => .error e
            | .error e => .error e
        | .error e => .error e
      else .error .stuck
  | _, _, _ => .error .stuck
end

/-- A field of record data (first match, as selection reads it). -/
def Data.field (d : Data) (ℓ : Label) : Option Data :=
  match d with
  | .record fs => Row.find? ℓ fs
  | _ => none

end Nanodregg.Lang
