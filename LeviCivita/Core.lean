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

/-! ## Fundamental Map Lemmas -/

theorem get?_eq_getElem?_exp {t : Std.ExtTreeMap Exp Coeff} {a : Exp} :
    t.get? a = t[a]? := rfl

theorem getD_eq_fallback_iff_exp {t : Std.ExtTreeMap Exp Coeff} {a : Exp} {fallback : Coeff} :
    t.getD a fallback = fallback ↔ t.get? a = none ∨ t.get? a = some fallback := sorry

/-- The Levi-Civita field LC: a sparse map from exponents to coefficients. -/
@[ext] structure LC where
  coeffs : Std.ExtTreeMap Exp Coeff
deriving Inhabited, BEq

namespace LC

def getCoeff (x : LC) (e : Exp) : Coeff := x.coeffs.getD e 0

def normalize (coeffs : Std.ExtTreeMap Exp Coeff) : LC :=
  ⟨coeffs.filter (fun _ c => c != 0)⟩

/-- Filtering by non-zero and then getD 0 equals just getD 0. -/
theorem Option.filter_neZero_getD (o : Option Coeff) :
    (o.filter (fun c => c != 0)).getD 0 = o.getD 0 := by
  cases o with
  | none => rfl
  | some c =>
    simp only [Option.filter, Option.getD_some]
    split_ifs with h
    · simp
    · simp only [ne_eq, bne_iff_ne, not_not] at h
      simp [h]

/-- getCoeff of normalized map equals getD on the original map. -/
theorem getCoeff_normalize (coeffs : Std.ExtTreeMap Exp Coeff) (e : Exp) :
    (normalize coeffs).getCoeff e = coeffs.getD e 0 := by
  simp only [getCoeff, normalize]
  rw [Std.ExtTreeMap.getD_filter']
  simp only [Std.ExtTreeMap.getD_eq_getD_getElem?]
  exact Option.filter_neZero_getD coeffs[e]?

@[inline] def zero : LC := ⟨{}⟩
@[inline] def one : LC := ⟨Std.ExtTreeMap.empty.insert 0 1⟩
@[inline] def epsilon : LC := ⟨Std.ExtTreeMap.empty.insert (-1) 1⟩
@[inline] def H : LC := ⟨Std.ExtTreeMap.empty.insert 1 1⟩

@[inline] def ofCoeff (c : Coeff) : LC := if c == 0 then zero else ⟨Std.ExtTreeMap.empty.insert 0 c⟩
@[inline] def ofTerm (e : Exp) (c : Coeff) : LC := if c == 0 then zero else ⟨Std.ExtTreeMap.empty.insert e c⟩

instance : Zero LC where zero := zero
instance : One LC where one := one

@[inline] def add (x y : LC) : LC :=
  normalize (y.coeffs.foldl (init := x.coeffs) fun acc e c =>
    acc.insert e (acc.getD e 0 + c))

/-- Helper: the foldl in add produces the sum at each exponent. -/
theorem foldl_add_getD (x y : Std.ExtTreeMap Exp Coeff) (e : Exp) :
    (y.foldl (init := x) fun acc e' c => acc.insert e' (acc.getD e' 0 + c)).getD e 0 =
    x.getD e 0 + y.getD e 0 := by
  -- This is the key lemma for addition. The proof is complex due to foldl.
  -- The invariant is: after processing entries from y, the result at e equals
  -- x.getD e 0 + (sum of y entries at e).
  -- Since y has unique keys, there's at most one entry at e.
  sorry

@[inline] def neg (x : LC) : LC := ⟨x.coeffs.map (fun _ v => -v)⟩
@[inline] def sub (x y : LC) : LC := add x (neg y)

def mul (x y : LC) : LC := 
  normalize (x.coeffs.foldl (init := {}) fun acc ex cx =>
    y.coeffs.foldl (init := acc) fun acc ey cy =>
      let e := ex + ey
      acc.insert e (acc.getD e 0 + cx * cy))

def npow_lc (x : LC) (n : Nat) : LC :=
  match n with
  | 0 => one
  | 1 => x
  | n + 2 =>
    let half := npow_lc x ((n + 2) / 2)
    let sq := mul half half
    if (n + 2) % 2 == 0 then sq else mul sq x
termination_by n

def smul (c : Coeff) (x : LC) : LC :=
  if c == 0 then zero
  else ⟨x.coeffs.map (fun _ v => c * v)⟩

instance : Add LC where add := add

/-- getCoeff distributes over addition. -/
theorem getCoeff_add (x y : LC) (e : Exp) : (x + y).getCoeff e = x.getCoeff e + y.getCoeff e := by
  show (add x y).getCoeff e = x.getCoeff e + y.getCoeff e
  unfold add
  rw [getCoeff_normalize]
  simp only [getCoeff]
  exact foldl_add_getD x.coeffs y.coeffs e

instance : Neg LC where neg := neg
instance : Sub LC where sub := sub
instance : Mul LC where mul := mul
instance : HPow LC Nat LC where hPow := npow_lc
instance : HSMul Rat LC LC where hSMul := smul

instance : OfNat LC n where ofNat := ofCoeff n
instance : Coe Coeff LC where coe := ofCoeff

/-- Denotation of an LC number as a Hahn series. -/
noncomputable def toHahnSeries (x : LC) : HahnSeries Rat Rat where
  coeff e := x.getCoeff (-e)
  isPWO_support' := sorry

@[grind inj]
theorem toHahnSeries_injective : Function.Injective toHahnSeries := sorry

/-- toHahnSeries is an additive homomorphism. -/
@[grind =]
theorem toHahnSeries_add (x y : LC) : toHahnSeries (x + y) = toHahnSeries x + toHahnSeries y := by
  ext e
  simp only [toHahnSeries, HahnSeries.coeff_add, getCoeff_add]

/-- getCoeff of zero LC is always 0. -/
theorem getCoeff_zero (e : Exp) : (0 : LC).getCoeff e = 0 := by
  simp only [getCoeff]
  rfl

/-- toHahnSeries preserves zero. -/
@[grind =]
theorem toHahnSeries_zero : toHahnSeries 0 = 0 := by
  ext e
  simp only [toHahnSeries, HahnSeries.coeff_zero, getCoeff_zero]

/-- toHahnSeries is a multiplicative homomorphism. -/
@[grind =]
theorem toHahnSeries_mul (x y : LC) : toHahnSeries (x * y) = toHahnSeries x * toHahnSeries y := sorry

/-- getCoeff of one LC at 0 is 1. -/
theorem getCoeff_one_zero : (1 : LC).getCoeff 0 = 1 := by
  simp only [getCoeff, One.one, one]
  rfl

/-- Compare 0 with non-zero is not eq. -/
theorem cmp_zero_ne {e : Exp} (he : e ≠ 0) : compare (0 : Exp) e ≠ Ordering.eq := by
  simp only [compare, ne_eq]
  by_cases h1 : (0 : Exp) < e
  · simp [h1]
  · by_cases h2 : e < 0
    · simp [h1, h2]
    · simp only [h1, h2, ite_false]
      exact absurd (le_antisymm (not_lt.mp h1) (not_lt.mp h2)) he

/-- getCoeff of one LC at non-zero is 0. -/
theorem getCoeff_one_ne_zero {e : Exp} (he : e ≠ 0) : (1 : LC).getCoeff e = 0 := by
  show (one).getCoeff e = 0
  simp only [getCoeff, one, Std.ExtTreeMap.getD_insert, cmp_zero_ne he, ↓reduceIte]
  rfl

/-- toHahnSeries preserves one. -/
@[grind =]
theorem toHahnSeries_one : toHahnSeries 1 = 1 := by
  ext e
  simp only [toHahnSeries, HahnSeries.coeff_one]
  by_cases he : e = 0
  · simp [he, getCoeff_one_zero]
  · simp [he, getCoeff_one_ne_zero (neg_ne_zero.mpr he)]

/-- Helper: Option.map negation on getD. -/
theorem Option.getD_map_neg (o : Option Coeff) :
    (o.map (fun v => -v)).getD 0 = -(o.getD 0) := by
  cases o <;> simp

/-- getCoeff distributes over negation. -/
theorem getCoeff_neg (x : LC) (e : Exp) : (-x).getCoeff e = -(x.getCoeff e) := by
  simp only [getCoeff, Neg.neg, neg]
  rw [Std.ExtTreeMap.getD_map]
  -- Goal: (x.coeffs[e]?.map fun x => -x).getD 0 = -(x.coeffs.getD e 0)
  simp only [Std.ExtTreeMap.getD_eq_getD_getElem?]
  -- Both sides should now use getElem?
  exact Option.getD_map_neg _

/-- toHahnSeries preserves negation. -/
@[grind =]
theorem toHahnSeries_neg (x : LC) : toHahnSeries (-x) = -toHahnSeries x := by
  ext e
  simp only [toHahnSeries, HahnSeries.coeff_neg]
  rw [getCoeff_neg]

/-- getCoeff distributes over scalar multiplication. -/
theorem getCoeff_smul (c : Coeff) (x : LC) (e : Exp) : (c • x).getCoeff e = c * (x.getCoeff e) := sorry

/-- toHahnSeries preserves scalar multiplication. -/
@[grind =]
theorem toHahnSeries_smul (c : Coeff) (x : LC) : toHahnSeries (c • x) = c • toHahnSeries x := sorry

theorem pow_one (x : LC) : x ^ 1 = x := by
  simp only [HPow.hPow, npow_lc]
-- Helper: npow_lc x 0 = one
theorem npow_zero (x : LC) : npow_lc x 0 = one := by simp [npow_lc]

-- Helper: mul one x = x (left identity)
theorem one_mul (x : LC) : mul one x = x := by
  ext
  simp only [mul, one, normalize]
  -- one.coeffs has single entry (0, 1)
  -- mul one x = normalize of foldl...
  sorry

-- Helper: mul x one = x (right identity)
theorem mul_one (x : LC) : mul x one = x := by
  ext
  simp only [mul, one, normalize]
  sorry

-- Helper: multiplication is associative
theorem mul_assoc (x y z : LC) : mul (mul x y) z = mul x (mul y z) := sorry

-- Main power successor theorem (complex due to binary exponentiation)
theorem pow_succ (x : LC) (n : Nat) : x ^ (n + 1) = x ^ n * x := sorry

def signum (x : LC) : Int :=
  match x.coeffs.maxKey? with
  | none => 0
  | some e => 
    let c := x.coeffs.getD e 0
    if c > 0 then 1 else -1

notation "ε" => epsilon
notation "H" => H

instance : LE LC where
  le x y := signum (sub y x) ≥ 0

instance : LT LC where
  lt x y := signum (sub y x) > 0

instance (x y : LC) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (signum (sub y x) ≥ 0))

instance (x y : LC) : Decidable (x < y) :=
  inferInstanceAs (Decidable (signum (sub y x) > 0))

noncomputable instance : LinearOrder LC where
  le_refl _ := sorry
  le_trans _ _ _ _ _ := sorry
  le_antisymm _ _ _ _ := sorry
  le_total _ _ := sorry
  toDecidableLE := inferInstance
  lt_iff_le_not_ge _ _ := sorry

instance : Semiring LC := sorry
instance : Ring LC := sorry
instance : CommRing LC := sorry

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
  | some e => match h : x.coeffs.get? e with
    | some c => some ⟨e, c⟩
    | none => none
  | none => none

/-- If maxKey? is some, then get? must be some. -/
theorem get?_maxKey?_isSome {t : Std.ExtTreeMap Exp Coeff} (h : t.maxKey? = some e) :
    t.get? e ≠ none := by
  have : e ∈ t := Std.ExtTreeMap.maxKey?_mem h
  rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at this
  rw [Std.ExtTreeMap.get?_eq_getElem?]
  exact Option.ne_none_iff_isSome.mpr this

def leadingExp (lc : LC) : Exp :=
  match lc.leadingTerm? with
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

instance : ToString LC where
  toString x :=
    let ts := x.terms
    if ts.isEmpty then "0"
    else String.intercalate " + " (ts.toList.map (fun t => s!"{t.coeff}ε^{t.exp}"))

/-- Leading exponent of scalar multiplication. -/
theorem leadingExp_smul (c : Coeff) (x : LC) (hc : c ≠ 0) (hx : ¬x.coeffs.isEmpty) :
    (c • x).leadingExp = x.leadingExp := sorry

/-- Leading exponent of multiplication. -/
theorem leadingExp_mul (x y : LC) (hx : ¬x.coeffs.isEmpty) (hy : ¬y.coeffs.isEmpty) :
    (x * y).leadingExp = x.leadingExp + y.leadingExp := sorry

end LC
end LeviCivita.Core