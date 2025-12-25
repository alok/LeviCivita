import Std.Tactic.Do
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.RingTheory.HahnSeries.Addition
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Set.Finite.Basic
import Batteries.Data.Array.Lemmas
open Std.Do

namespace LeviCivita.Core

/-- Coefficient type - rational numbers. -/
abbrev Coeff := Rat

/-- Exponent type - rational numbers for full Levi-Civita generality. -/
abbrev Exp := Rat

/-! ## Core Data Structure -/

/-- A term in a Levi-Civita number: coefficient × ε^exponent -/
structure Term where
  exp : Exp
  coeff : Coeff
deriving BEq, Inhabited, Repr, DecidableEq

/-- Extensionality for Term. -/
@[ext] theorem Term.ext {t1 t2 : Term} (he : t1.exp = t2.exp) (hc : t1.coeff = t2.coeff) : t1 = t2 := by
  cases t1; cases t2; simp_all

/-- Ordering on Rat for exponent comparison. -/
instance : Ord Rat where
  compare a b := if a < b then .lt else if b < a then .gt else .eq

instance : Std.OrientedOrd Rat where
  eq_swap {a b} := by
    simp [compare]
    split_ifs <;> simp_all <;> try linarith

instance : Std.TransOrd Rat where
  isLE_trans {a b c} hab hbc := by
    simp [compare, Ordering.isLE] at *
    split_ifs at * <;> simp_all <;> try linarith

instance : Std.LawfulEqOrd Rat where
  eq_of_compare {a b} h := by
    simp [compare] at h
    split_ifs at h <;> (try contradiction); linarith

/-- The Levi-Civita field LC: a sparse map from exponents to coefficients. -/
@[ext] structure LC where
  coeffs : Std.ExtTreeMap Exp Coeff
deriving Inhabited, BEq

namespace LC

def normalize (coeffs : Std.ExtTreeMap Exp Coeff) : LC :=
  ⟨coeffs.filter (fun _ c => c != 0)⟩

@[inline] def zero : LC := ⟨{}⟩
@[inline] def one : LC := ⟨Std.ExtTreeMap.empty.insert 0 1⟩
@[inline] def epsilon : LC := ⟨Std.ExtTreeMap.empty.insert (-1) 1⟩
@[inline] def H : LC := ⟨Std.ExtTreeMap.empty.insert 1 1⟩

@[inline] def ofCoeff (c : Coeff) : LC := if c == 0 then zero else ⟨Std.ExtTreeMap.empty.insert 0 c⟩
@[inline] def ofTerm (e : Exp) (c : Coeff) : LC := if c == 0 then zero else ⟨Std.ExtTreeMap.empty.insert e c⟩

instance : Zero LC where zero := zero
instance : One LC where one := one

def getCoeff (x : LC) (e : Exp) : Coeff := x.coeffs.getD e 0

@[inline] def add (x y : LC) : LC := 
  normalize (y.coeffs.foldl (init := x.coeffs) fun acc e c =>
    acc.insert e (acc.getD e 0 + c))

@[inline] def neg (x : LC) : LC := ⟨x.coeffs.map (fun _ v => -v)⟩
@[inline] def sub (x y : LC) : LC := add x (neg y)

def mul (x y : LC) : LC := 
  normalize (x.coeffs.foldl (init := {}) fun acc ex cx =>
    y.coeffs.foldl (init := acc) fun acc ey cy =>
      let e := ex + ey
      acc.insert e (acc.getD e 0 + cx * cy))

def npow (x : LC) (n : Nat) : LC :=
  match n with
  | 0 => one
  | 1 => x
  | n + 2 =>
    let half := npow x ((n + 2) / 2)
    let sq := mul half half
    if (n + 2) % 2 == 0 then sq else mul sq x
termination_by n

def smul (c : Coeff) (x : LC) : LC :=
  if c == 0 then zero
  else ⟨x.coeffs.map (fun _ v => c * v)⟩

instance : Add LC where add := add
instance : Neg LC where neg := neg
instance : Sub LC where sub := sub
instance : Mul LC where mul := mul
instance : HPow LC Nat LC where hPow := npow
instance : HSMul Rat LC LC where hSMul := smul

instance : OfNat LC n where ofNat := ofCoeff n
instance : Coe Coeff LC where coe := ofCoeff

def std (x : LC) : Coeff := x.getCoeff 0

def derivative (f : LC → LC) (pt : LC) : Coeff :=
  let delta := f (pt + epsilon) - f pt
  let quotient := delta * H
  std quotient

def nthDerivative (f : LC → LC) (pt : LC) (n : Nat) : Coeff :=
  match n with
  | 0 => std (f pt)
  | 1 => derivative f pt
  | n + 1 =>
    let result := f (pt + epsilon)
    let fact_n : Coeff := (List.range (n + 1) |>.map (fun i => (i + 1 : Coeff)) |>.foldl (· * ·) 1)
    (result.coeffs.getD (- ((n + 1) : Rat)) 0) * fact_n

def leadingTerm? (x : LC) : Option Term :=
  match x.coeffs.maxKey? with
  | some e => match x.coeffs.get? e with
    | some c => some ⟨e, c⟩
    | none => none
  | none => none

def leadingExp (x : LC) : Exp :=
  match x.leadingTerm? with
  | some t => t.exp
  | none => 0

def terms (x : LC) : Array Term :=
  let t := x.coeffs.toList.map (fun (e, c) => Term.mk e c)
  t.reverse.toArray

def invert (x : LC) (terms : Nat := 10) : Option LC := do
  let lead ← x.leadingTerm?
  if lead.coeff == 0 then none
  let leadInv : LC := ofTerm (-lead.exp) (1 / lead.coeff)
  let leadLC : LC := ofTerm lead.exp lead.coeff
  let delta := (x - leadLC) * leadInv
  let mut result : LC := 1
  let mut power : LC := 1
  for i in [1:terms] do
    power := power * delta
    let sign : Coeff := if i % 2 == 1 then -1 else 1
    result := result + (ofCoeff sign) * power
  some (leadInv * result)

def signum (x : LC) : Int :=
  match x.coeffs.maxKey? with
  | none => 0
  | some e => 
    let c := x.coeffs.getD e 0
    if c > 0 then 1 else -1

/-! ## Notation -/

scoped notation "ε" => epsilon
scoped notation "H" => H

instance : ToString LC where
  toString x :=
    let ts := x.terms
    if ts.isEmpty then "0"
    else String.intercalate " + " (ts.toList.map (fun t => s!"{t.coeff}ε^{t.exp}"))

/-- Denotation of an LC number as a Hahn series. -/
noncomputable def toHahnSeries (x : LC) : HahnSeries Rat Rat where
  coeff e := x.getCoeff (-e)
  isPWO_support' := sorry

/-- The full Levi-Civita field, formally represented as Hahn series with well-ordered support. -/
abbrev LeviCivitaField := Lex (HahnSeries Rat Rat)

/-- Embedding from the optimized map-based LC representation into the formal field. -/
noncomputable def ofLC (x : LC) : LeviCivitaField := toLex (toHahnSeries x)

theorem toHahnSeries_injective : Function.Injective toHahnSeries := sorry

noncomputable instance : LinearOrder LC := sorry
instance : Semiring LC := sorry
instance : Ring LC := sorry
instance : CommRing LC := sorry

end LC
end LeviCivita.Core
