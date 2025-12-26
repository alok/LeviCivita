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
    t.getD a fallback = fallback ↔ t.get? a = none ∨ t.get? a = some fallback := by
  rw [Std.ExtTreeMap.getD_eq_getD_getElem?, get?_eq_getElem?_exp]
  cases h : t[a]? with
  | none => simp [h]
  | some v => simp [h, eq_comm]

/-- map preserves maxKey? since it preserves membership. -/
theorem maxKey?_map_exp (t : Std.ExtTreeMap Exp Coeff) (f : Exp → Coeff → Coeff) :
    (t.map f).maxKey? = t.maxKey? := by
  cases ht : t.maxKey? with
  | none =>
    rw [Std.ExtTreeMap.maxKey?_eq_none_iff] at ht
    have hempty : (t.map f) = ∅ := by
      rw [Std.ExtTreeMap.isEmpty_iff]
      rw [Std.ExtTreeMap.isEmpty_iff] at ht
      simp only [Std.ExtTreeMap.size_map, ht]
    rw [Std.ExtTreeMap.maxKey?_eq_none_iff]
    exact hempty
  | some km =>
    have hmem : km ∈ t.map f := Std.ExtTreeMap.mem_map.mpr (Std.ExtTreeMap.maxKey?_mem ht)
    have hle : ∀ k, k ∈ t.map f → (compare k km).isLE = true := by
      intro k hk
      rw [Std.ExtTreeMap.mem_map] at hk
      exact Std.ExtTreeMap.maxKey?_le.mp (fun _ h' => by rw [ht] at h'; cases h'; simp [compare]) k hk
    symm
    exact Std.ExtTreeMap.maxKey?_eq_some_iff_mem_and_forall.mpr ⟨hmem, hle⟩

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

/-- compare a b = .eq ↔ compare b a = .eq since .eq.swap = .eq -/
theorem compare_eq_comm (a b : Exp) : compare a b = .eq ↔ compare b a = .eq := by
  constructor <;> intro h
  · have heq : a = b := Std.LawfulEqOrd.eq_of_compare h
    subst heq
    exact h
  · have heq : b = a := Std.LawfulEqOrd.eq_of_compare h
    subst heq
    exact h

/-- Helper for foldl_add_getD: induction on list of key-value pairs.
    Invariant: getD e 0 of result = x.getD e 0 + (value at e in list, or 0) -/
theorem foldl_add_getD_list (x : Std.ExtTreeMap Exp Coeff) (l : List (Exp × Coeff)) (e : Exp)
    (hnd : l.Pairwise (fun a b => ¬compare a.1 b.1 = .eq)) :
    (l.foldl (fun acc (p : Exp × Coeff) => acc.insert p.1 (acc.getD p.1 0 + p.2)) x).getD e 0 =
    x.getD e 0 + (l.find? (fun p => compare p.1 e == .eq)).elim 0 (·.2) := by
  induction l generalizing x with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hnd' : tl.Pairwise (fun a b => ¬compare a.1 b.1 = .eq) := List.Pairwise.of_cons hnd
    rw [ih _ hnd']
    simp only [List.find?_cons]
    by_cases heq : compare hd.1 e = .eq
    · -- hd.1 = e case
      have he : hd.1 = e := Std.LawfulEqOrd.eq_of_compare heq
      subst he
      simp only [heq, beq_self_eq_true, ↓reduceIte, Std.ExtTreeMap.getD_insert_self]
      -- e is not in tl (by pairwise with hd)
      have hnotin : tl.find? (fun p => compare p.1 hd.1 == .eq) = none := by
        apply List.find?_eq_none.mpr
        intro p hp
        have hrel := List.rel_of_pairwise_cons hnd hp
        -- hrel : ¬compare hd.1 p.1 = .eq, need ¬(compare p.1 hd.1 == .eq)
        simp only [bne_iff_ne, ne_eq, beq_iff_eq]
        intro heq
        have heq' : compare hd.1 p.1 = .eq := compare_eq_comm p.1 hd.1 |>.mp heq
        exact hrel heq'
      simp only [hnotin, Option.elim_some, Option.elim_none, add_zero]
    · -- hd.1 ≠ e case
      simp only [beq_eq_false_iff_ne.mpr heq, Bool.false_eq_true, ↓reduceIte,
        Std.ExtTreeMap.getD_insert, heq]

/-- Helper: the foldl in add produces the sum at each exponent. -/
theorem foldl_add_getD (x y : Std.ExtTreeMap Exp Coeff) (e : Exp) :
    (y.foldl (init := x) fun acc e' c => acc.insert e' (acc.getD e' 0 + c)).getD e 0 =
    x.getD e 0 + y.getD e 0 := by
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  have hpw := Std.ExtTreeMap.distinct_keys_toList (t := y)
  rw [foldl_add_getD_list x y.toList e hpw]
  -- Now relate find? on toList to getD
  simp only [Std.ExtTreeMap.getD_eq_getD_getElem?]
  congr 1
  -- Show: (toList.find? ...).elim 0 (·.2) = y[e]?.getD 0
  cases hy : y[e]? with
  | none =>
    simp only [Option.getD_none]
    have hfind : (y.toList.find? fun p => compare p.1 e == .eq) = none := by
      apply List.find?_eq_none.mpr
      intro p hp
      simp only [beq_iff_eq]
      intro heq
      have he : p.1 = e := Std.LawfulEqOrd.eq_of_compare heq
      subst he
      rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at hp
      simp [hp] at hy
    simp [hfind]
  | some v =>
    simp only [Option.getD_some]
    -- find? returns some (e, v) or some (e, v')
    have hmem : (e, v) ∈ y.toList := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hy
    -- Show find? finds some element with key e
    cases hfind : y.toList.find? (fun p => compare p.1 e == .eq) with
    | none =>
      -- Contradiction: e is in the list
      exfalso
      have := List.find?_eq_none.mp hfind (e, v) hmem
      simp at this
    | some p =>
      simp only [Option.elim_some]
      -- p.1 = e by predicate, and p.2 = v by uniqueness of keys
      have hpred := List.find?_some hfind
      have hpeq : compare p.1 e = .eq := beq_iff_eq.mp hpred
      have hpe : p.1 = e := Std.LawfulEqOrd.eq_of_compare hpeq
      -- p ∈ y.toList and has key e
      have hp_mem := List.mem_of_find?_eq_some hfind
      rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at hp_mem
      rw [hpe] at hp_mem
      rw [hy] at hp_mem
      injection hp_mem with hpv
      rw [← hpv]

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

/-- The support of getCoeff is finite (bounded by the finite map). -/
theorem support_getCoeff_finite (x : LC) : {e : Exp | x.getCoeff e ≠ 0}.Finite := by
  -- The support is a subset of keys in the finite ExtTreeMap
  have hfin : (x.coeffs.toList.map Prod.fst).toFinset.toSet.Finite :=
    Set.toFinite _
  apply Set.Finite.subset hfin
  intro e he
  simp only [Set.mem_setOf_eq, getCoeff] at he
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
  -- e is in support implies e is a key in the map
  have h : x.coeffs[e]? ≠ none := by
    intro hn
    simp [Std.ExtTreeMap.getD_eq_getD_getElem?, hn] at he
  cases hx : x.coeffs[e]? with
  | none => exact absurd hx h
  | some v =>
    have hmem : (e, v) ∈ x.coeffs.toList := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hx
    exact ⟨(e, v), hmem, rfl⟩

/-- Denotation of an LC number as a Hahn series. -/
noncomputable def toHahnSeries (x : LC) : HahnSeries Rat Rat where
  coeff e := x.getCoeff (-e)
  isPWO_support' := by
    apply Set.Finite.isPWO
    have hneg : {e | x.getCoeff (-e) ≠ 0} ⊆ (fun e => -e) '' {e | x.getCoeff e ≠ 0} := by
      intro e he
      simp only [Set.mem_setOf_eq] at he
      simp only [Set.mem_image, Set.mem_setOf_eq]
      exact ⟨-e, he, neg_neg e⟩
    exact Set.Finite.subset (Set.Finite.image _ (support_getCoeff_finite x)) hneg

/-- Two LC numbers with equal getCoeff at all exponents are equal.
    Note: This requires that LC numbers don't store zero coefficients. -/
theorem ext_getCoeff {x y : LC} (h : ∀ e, x.getCoeff e = y.getCoeff e) : x = y := by
  -- This proof requires that coeffs don't contain zero values
  -- (which should be ensured by normalize)
  ext e a
  constructor
  · intro hx
    have hcoeff : x.getCoeff e = a := by
      simp only [getCoeff, Std.ExtTreeMap.getD_eq_getD_getElem?, hx, Option.getD_some]
    rw [h e] at hcoeff
    simp only [getCoeff, Std.ExtTreeMap.getD_eq_getD_getElem?] at hcoeff
    cases hy : y.coeffs[e]? with
    | none =>
      -- a = 0 from hcoeff, but then x.coeffs shouldn't store 0
      simp [hy] at hcoeff
      -- This requires an invariant that coeffs don't store 0
      sorry
    | some b => simp [hy] at hcoeff; rw [hcoeff]
  · intro hy
    have hcoeff : y.getCoeff e = a := by
      simp only [getCoeff, Std.ExtTreeMap.getD_eq_getD_getElem?, hy, Option.getD_some]
    rw [← h e] at hcoeff
    simp only [getCoeff, Std.ExtTreeMap.getD_eq_getD_getElem?] at hcoeff
    cases hx : x.coeffs[e]? with
    | none =>
      simp [hx] at hcoeff
      sorry
    | some b => simp [hx] at hcoeff; rw [hcoeff]

@[grind inj]
theorem toHahnSeries_injective : Function.Injective toHahnSeries := by
  intro x y hxy
  apply ext_getCoeff
  intro e
  have h := congrArg (fun h => h.coeff (-e)) hxy
  simp only [toHahnSeries, neg_neg] at h
  exact h

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
theorem getCoeff_smul (c : Coeff) (x : LC) (e : Exp) : (c • x).getCoeff e = c * (x.getCoeff e) := by
  simp only [HSMul.hSMul, smul, getCoeff]
  by_cases hc : c = 0
  · simp only [hc, beq_self_eq_true, ↓reduceIte, zero, Std.ExtTreeMap.getD_empty, zero_mul]
  · have hc_beq : (c == 0) = false := by simp [hc]
    simp only [hc_beq, ite_false]
    simp only [Std.ExtTreeMap.getD_eq_getD_getElem?, Std.ExtTreeMap.getElem?_map]
    cases hx : x.coeffs[e]? with
    | none => simp [hx, mul_zero]
    | some v => simp [hx]

/-- toHahnSeries preserves scalar multiplication. -/
@[grind =]
theorem toHahnSeries_smul (c : Coeff) (x : LC) : toHahnSeries (c • x) = c • toHahnSeries x := by
  ext e
  simp only [toHahnSeries, HahnSeries.coeff_smul, getCoeff_smul, smul_eq_mul]

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

/-- getCoeff distributes over subtraction. -/
theorem getCoeff_sub (x y : LC) (e : Exp) : (x - y).getCoeff e = x.getCoeff e - y.getCoeff e := by
  show (sub x y).getCoeff e = x.getCoeff e - y.getCoeff e
  simp only [sub]
  rw [getCoeff_add, getCoeff_neg]
  ring

/-- x - x has all zero coefficients. -/
theorem getCoeff_sub_self (x : LC) (e : Exp) : (x - x).getCoeff e = 0 := by
  rw [getCoeff_sub]; ring

def signum (x : LC) : Int :=
  match x.coeffs.maxKey? with
  | none => 0
  | some e =>
    let c := x.coeffs.getD e 0
    if c > 0 then 1 else -1

/-- signum of zero is 0. -/
theorem signum_zero : signum (0 : LC) = 0 := rfl

/-- If all coefficients are zero, then the LC is zero. -/
theorem eq_zero_of_getCoeff_eq_zero (x : LC) (h : ∀ e, x.getCoeff e = 0) :
    x.coeffs.maxKey? = none := by
  by_contra hne
  push_neg at hne
  obtain ⟨km, hkm⟩ := Option.ne_none_iff_exists'.mp hne
  have hc := h km
  simp only [getCoeff, Std.ExtTreeMap.getD_eq_getD_getElem?] at hc
  have hmem : km ∈ x.coeffs := Std.ExtTreeMap.maxKey?_mem hkm
  rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at hmem
  cases hget : x.coeffs[km]? with
  | none => simp [hget] at hmem
  | some v =>
    simp [hget] at hc
    -- v = 0, but the map shouldn't store zeros (normalization invariant)
    -- This requires the invariant that coeffs don't contain zero values
    sorry

/-- signum of x - x is 0 or ≥ 0. -/
theorem signum_sub_self (x : LC) : signum (x - x) ≥ 0 := by
  show signum (sub x x) ≥ 0
  simp only [signum]
  have h : ∀ e, (sub x x).getCoeff e = 0 := getCoeff_sub_self x
  cases hmax : (sub x x).coeffs.maxKey? with
  | none => simp
  | some e =>
    -- If maxKey? = some e, then getCoeff e ≠ 0 (by map invariant)
    -- But h says getCoeff e = 0, contradiction
    -- This requires the normalization invariant
    have hc := h e
    simp only [getCoeff, Std.ExtTreeMap.getD_eq_getD_getElem?] at hc
    have hmem : e ∈ (sub x x).coeffs := Std.ExtTreeMap.maxKey?_mem hmax
    rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at hmem
    cases hget : (sub x x).coeffs[e]? with
    | none => simp [hget] at hmem
    | some v =>
      -- v should be non-zero by invariant, but hc says v = 0
      simp [hget] at hc
      simp [hget, Std.ExtTreeMap.getD_eq_getD_getElem?, hc]

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
  le_refl x := signum_sub_self x
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
    (c • x).leadingExp = x.leadingExp := by
  simp only [leadingExp, leadingTerm?]
  have hc_beq : (c == 0) = false := beq_eq_false_iff_ne.mpr hc
  simp only [HSMul.hSMul, smul, hc_beq, ite_false]
  rw [maxKey?_map_exp]
  cases hmax : x.coeffs.maxKey? with
  | none =>
    rw [Std.ExtTreeMap.maxKey?_eq_none_iff, Std.ExtTreeMap.isEmpty_iff] at hmax
    exact absurd hmax hx
  | some e =>
    simp only
    cases hget : x.coeffs.get? e with
    | none =>
      have h := get?_maxKey?_isSome hmax
      exact absurd hget h
    | some v =>
      simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_map, hget, Option.map_some']

/-- Leading exponent of multiplication. -/
theorem leadingExp_mul (x y : LC) (hx : ¬x.coeffs.isEmpty) (hy : ¬y.coeffs.isEmpty) :
    (x * y).leadingExp = x.leadingExp + y.leadingExp := sorry

end LC
end LeviCivita.Core