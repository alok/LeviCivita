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
    rw [Std.ExtTreeMap.maxKey?_eq_none_iff] at ht ⊢
    rw [ht]
    ext k
    constructor
    · intro h
      simp only [Std.ExtTreeMap.getElem?_map, Std.ExtTreeMap.getElem?_empty] at h
      cases h
    · intro h
      simp only [Std.ExtTreeMap.getElem?_empty] at h
      cases h
  | some km =>
    have hmem : km ∈ t.map f := Std.ExtTreeMap.mem_map.mpr (Std.ExtTreeMap.maxKey?_mem ht)
    have hle : ∀ k, k ∈ t.map f → (compare k km).isLE = true := by
      intro k hk
      rw [Std.ExtTreeMap.mem_map] at hk
      exact Std.ExtTreeMap.maxKey?_le.mp (fun _ h' => by rw [ht] at h'; cases h'; simp [compare]) k hk
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

/-- If e is in normalized coeffs, then the value there is non-zero.
    The filter function ensures only non-zero values are kept. -/
theorem normalize_mem_ne_zero (coeffs : Std.ExtTreeMap Exp Coeff) (e : Exp)
    (hmem : e ∈ (normalize coeffs).coeffs) : (normalize coeffs).coeffs.getD e 0 ≠ 0 := by
  unfold normalize at hmem ⊢
  rw [Std.ExtTreeMap.getD_filter']
  rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at hmem
  simp only [Std.ExtTreeMap.getElem?_filter] at hmem
  cases hget : coeffs[e]? with
  | none => simp [hget] at hmem
  | some v =>
    simp only [hget] at hmem
    simp only [Option.filter, bne_iff_ne, ne_eq]
    split_ifs with hv
    · -- hv : v = 0, filter produces guard false on 0 != 0
      simp only [hv] at hmem
      -- hmem : ((some 0).pfilter fun a _ => a != 0).isSome = true
      -- But 0 != 0 is false, so pfilter gives none, and none.isSome = false
      simp only [Option.pfilter, bne_self_eq_false, cond_false, Option.isSome_none] at hmem
      -- hmem : false = true is a contradiction
      exact absurd hmem Bool.false_ne_true
    · simp only [Option.getD_some]; exact hv

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

/-- add produces a normalized result: if e is in the coeffs, the value is non-zero. -/
theorem add_mem_ne_zero (x y : LC) (e : Exp) (hmem : e ∈ (add x y).coeffs) :
    (add x y).coeffs.getD e 0 ≠ 0 := by
  unfold add at hmem ⊢
  exact normalize_mem_ne_zero _ e hmem

/-- sub produces a normalized result: if e is in the coeffs, the value is non-zero. -/
theorem sub_mem_ne_zero (x y : LC) (e : Exp) (hmem : e ∈ (sub x y).coeffs) :
    (sub x y).coeffs.getD e 0 ≠ 0 := by
  unfold sub at hmem ⊢
  exact add_mem_ne_zero _ _ e hmem

/-- mul produces a normalized result: if e is in the coeffs, the value is non-zero. -/
theorem mul_mem_ne_zero (x y : LC) (e : Exp) (hmem : e ∈ (mul x y).coeffs) :
    (mul x y).coeffs.getD e 0 ≠ 0 := by
  unfold mul at hmem ⊢
  exact normalize_mem_ne_zero _ e hmem

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

/-- toHahnSeries preserves ofCoeff as single. -/
@[grind =]
theorem toHahnSeries_ofCoeff (c : Coeff) : toHahnSeries (ofCoeff c) = HahnSeries.single 0 c := by
  -- ofCoeff c creates LC with coefficient c at exponent 0
  -- HahnSeries.single 0 c is the HahnSeries with coefficient c at exponent 0
  sorry

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

-- Helper: foldl over singleton insert builds exactly y.coeffs when multiplied by 1
theorem foldl_singleton_mul_one (y : Std.ExtTreeMap Exp Coeff) (e : Exp) :
    (y.foldl (init := ({} : Std.ExtTreeMap Exp Coeff)) fun acc ey cy =>
      acc.insert (0 + ey) (acc.getD (0 + ey) 0 + 1 * cy)).getD e 0 =
    y.getD e 0 := by
  simp only [zero_add, one_mul]
  -- Use foldl_add_getD with x = {}
  have h := foldl_add_getD {} y e
  simp only [Std.ExtTreeMap.getD_empty, zero_add] at h
  exact h

-- Helper lemma: getCoeff of mul one x equals getCoeff of x
theorem getCoeff_mul_one_left (x : LC) (e : Exp) : (mul one x).getCoeff e = x.getCoeff e := by
  -- Proof structure: one.coeffs = {0 ↦ 1}, so foldl over one.coeffs with ex=0, cx=1
  -- produces x * 1 = x via foldl_singleton_mul_one
  -- Technical difficulty: Std.ExtTreeMap.empty vs ∅ notation causes elaboration issues
  sorry

-- Helper: inner foldl over singleton {0 ↦ 1} simplifies to single insert
theorem inner_foldl_one (acc : Std.ExtTreeMap Exp Coeff) (ex : Exp) (cx : Coeff) :
    ((({} : Std.ExtTreeMap Exp Coeff).insert 0 1).foldl (init := acc) fun acc' ey cy =>
      acc'.insert (ex + ey) (acc'.getD (ex + ey) 0 + cx * cy)) =
    acc.insert ex (acc.getD ex 0 + cx) := by
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  have hone : (({} : Std.ExtTreeMap Exp Coeff).insert 0 1).toList = [(0, 1)] := rfl
  simp only [hone, List.foldl_cons, List.foldl_nil, _root_.add_zero, mul_one]

-- Helper: after applying inner_foldl_one, the outer foldl copies x.coeffs
-- This is a complex lemma that requires careful tracking of insertion order
theorem foldl_copy_coeffs (y : Std.ExtTreeMap Exp Coeff) (e : Exp) :
    (y.foldl (init := ({} : Std.ExtTreeMap Exp Coeff))
      fun acc ex cx => acc.insert ex (acc.getD ex 0 + cx)).getD e 0 = y.getD e 0 := by
  -- The proof requires showing that inserting each entry from y accumulates correctly
  -- This is complex due to the ordered nature of ExtTreeMap
  sorry

-- Helper lemma: getCoeff of mul x one equals getCoeff of x
theorem getCoeff_mul_one_right (x : LC) (e : Exp) : (mul x one).getCoeff e = x.getCoeff e := by
  -- The inner foldl over {0 ↦ 1} adds (ex + 0, cx * 1) = (ex, cx)
  -- Using inner_foldl_one, the outer foldl becomes a copy operation
  unfold mul one
  rw [getCoeff_normalize]
  simp only [getCoeff]
  -- Use inner_foldl_one to simplify the nested structure
  -- The full proof requires showing the outer foldl correctly copies coefficients
  sorry

-- Helper: mul one x = x (left identity)
theorem one_mul (x : LC) : mul one x = x := by
  apply toHahnSeries_injective
  ext e
  simp only [toHahnSeries, getCoeff_mul_one_left]

-- Helper: mul x one = x (right identity)
theorem mul_one (x : LC) : mul x one = x := by
  apply toHahnSeries_injective
  ext e
  simp only [toHahnSeries, getCoeff_mul_one_right]

-- Helper: multiplication is associative
theorem mul_assoc (x y z : LC) : mul (mul x y) z = mul x (mul y z) := sorry

-- Main power successor theorem (complex due to binary exponentiation)
theorem pow_succ (x : LC) (n : Nat) : x ^ (n + 1) = x ^ n * x := sorry

/-! ## Algebraic Properties via toHahnSeries -/

theorem add_assoc (x y z : LC) : x + y + z = x + (y + z) := by
  apply toHahnSeries_injective
  simp only [toHahnSeries_add]
  ring

theorem add_comm (x y : LC) : x + y = y + x := by
  apply toHahnSeries_injective
  simp only [toHahnSeries_add]
  ring

theorem zero_add' (x : LC) : 0 + x = x := by
  apply toHahnSeries_injective
  simp only [toHahnSeries_add, toHahnSeries_zero, _root_.zero_add]

theorem add_zero' (x : LC) : x + 0 = x := by
  apply toHahnSeries_injective
  simp only [toHahnSeries_add, toHahnSeries_zero, _root_.add_zero]

theorem neg_add_cancel (x : LC) : -x + x = 0 := by
  apply toHahnSeries_injective
  simp only [toHahnSeries_add, toHahnSeries_neg, toHahnSeries_zero]
  ring

theorem add_neg_cancel (x : LC) : x + (-x) = 0 := by
  apply toHahnSeries_injective
  simp only [toHahnSeries_add, toHahnSeries_neg, toHahnSeries_zero]
  ring

theorem zero_mul (x : LC) : mul zero x = zero := by
  -- foldl over empty coeffs returns init
  rfl

theorem mul_zero (x : LC) : mul x zero = zero := by
  unfold mul zero
  -- For each entry in x, the inner foldl over {} returns acc unchanged (by rfl)
  -- So the outer foldl produces {} (the init)
  -- Since the inner foldl over empty always returns acc unchanged, the outer foldl
  -- just returns the init value {}
  have h_inner : ∀ (acc : Std.ExtTreeMap Exp Coeff) ex cx, (({} : Std.ExtTreeMap Exp Coeff).foldl
    (init := acc) fun acc' ey cy =>
      let e := ex + ey
      acc'.insert e (acc'.getD e 0 + cx * cy)) = acc := fun _ _ _ => rfl
  -- The outer foldl is:
  -- x.coeffs.foldl (init := {}) (fun acc ex cx => h_inner acc ex cx = acc) = {}
  -- Since each step returns acc unchanged, the fold returns init = {}
  simp only [normalize]
  -- Need to show the filtered foldl is {}
  have h_outer : x.coeffs.foldl (init := ({} : Std.ExtTreeMap Exp Coeff))
    (fun acc ex cx => (({} : Std.ExtTreeMap Exp Coeff).foldl
      (init := acc) fun acc' ey cy =>
        let e := ex + ey
        acc'.insert e (acc'.getD e 0 + cx * cy))) = {} := by
    rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
    induction x.coeffs.toList with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.foldl_cons]
      rw [h_inner]
      exact ih
  -- Since foldl produces {}, filtering {} also gives {}
  have h_filter : (({} : Std.ExtTreeMap Exp Coeff).filter (fun _ c => c != 0)) = {} := rfl
  congr 1
  rw [h_outer, h_filter]

/-- getCoeff distributes over subtraction. -/
theorem getCoeff_sub (x y : LC) (e : Exp) : (x - y).getCoeff e = x.getCoeff e - y.getCoeff e := by
  show (sub x y).getCoeff e = x.getCoeff e - y.getCoeff e
  unfold sub
  have hadd : (x + neg y).getCoeff e = x.getCoeff e + (neg y).getCoeff e := getCoeff_add x (neg y) e
  have hneg : (neg y).getCoeff e = -(y.getCoeff e) := getCoeff_neg y e
  have h : (add x (neg y)).getCoeff e = (x + neg y).getCoeff e := rfl
  rw [h, hadd, hneg]
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
theorem signum_zero : signum (0 : LC) = 0 := by
  show signum zero = 0
  unfold signum zero
  have h : ({} : Std.ExtTreeMap Exp Coeff).maxKey? = none := by
    rw [Std.ExtTreeMap.maxKey?_eq_none_iff]
  simp only [h]

/-- If all coefficients are zero, then the LC is zero.
    Note: This assumes x is constructed through normal operations (which produce normalized maps).
    The proof is sorry'd because the LC type doesn't enforce normalization. -/
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
    -- v = 0, but normalized maps don't store zeros
    -- This would need a stronger invariant on LC construction
    sorry

/-- signum of x - x is 0 or ≥ 0. -/
theorem signum_sub_self (x : LC) : signum (x - x) ≥ 0 := by
  show signum (sub x x) ≥ 0
  simp only [signum]
  have h : ∀ e, (sub x x).getCoeff e = 0 := getCoeff_sub_self x
  cases hmax : (sub x x).coeffs.maxKey? with
  | none => simp
  | some e =>
    -- If maxKey? = some e, then the map stores a value at e
    -- Since sub normalizes, this value should be non-zero
    -- But h says getCoeff e = 0, which is a contradiction
    have hc := h e
    simp only [getCoeff, Std.ExtTreeMap.getD_eq_getD_getElem?] at hc
    have hmem : e ∈ (sub x x).coeffs := Std.ExtTreeMap.maxKey?_mem hmax
    -- sub produces normalized result, so value at e is non-zero
    have hne := sub_mem_ne_zero x x e hmem
    simp only [Std.ExtTreeMap.getD_eq_getD_getElem?] at hne
    rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at hmem
    cases hget : (sub x x).coeffs[e]? with
    | none => simp [hget] at hmem
    | some v =>
      simp [hget] at hc hne
      -- hne : v ≠ 0, hc : v = 0 - contradiction
      exact absurd hc hne

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

-- Distributivity lemmas (need toHahnSeries_mul or direct proof)
theorem left_distrib (x y z : LC) : mul x (add y z) = add (mul x y) (mul x z) := sorry
theorem right_distrib (x y z : LC) : mul (add x y) z = add (mul x z) (mul y z) := sorry
theorem mul_comm (x y : LC) : mul x y = mul y x := sorry

-- Define natural number scalar multiplication using Rat smul
def nsmul_lc (n : ℕ) (x : LC) : LC := smul (n : Coeff) x

instance : Semiring LC where
  add := add
  add_assoc := add_assoc
  zero := zero
  zero_add := zero_add'
  add_zero := add_zero'
  nsmul := nsmul_lc
  nsmul_zero := fun x => by
    simp only [nsmul_lc, Nat.cast_zero, smul]
    rfl
  nsmul_succ := fun n x => by
    simp only [nsmul_lc, Nat.cast_succ]
    -- Need to show: smul (n + 1) x = smul n x + x
    apply toHahnSeries_injective
    have hs : (smul (n : Coeff) x : LC) = (n : Coeff) • x := rfl
    have hs' : (smul ((n : Coeff) + 1) x : LC) = ((n : Coeff) + 1) • x := rfl
    simp only [hs, hs', toHahnSeries_smul, toHahnSeries_add]
    -- Goal: (n + 1) • x.toHahnSeries = n • x.toHahnSeries + x.toHahnSeries
    rw [add_smul, one_smul]
  add_comm := add_comm
  mul := mul
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one := one
  one_mul := one_mul
  mul_one := mul_one
  natCast := fun n => ofCoeff n
  natCast_zero := by simp [ofCoeff, zero]; rfl
  natCast_succ := fun n => by
    -- Goal: ofCoeff (n+1) = ofCoeff n + 1
    -- This is: ofCoeff (n+1) = ofCoeff n + ofCoeff 1
    -- Follows from add distributing over ofCoeff
    sorry
  npow := fun n x => npow_lc x n
  npow_zero := fun x => by
    show npow_lc x 0 = one
    unfold npow_lc
    rfl
  npow_succ := fun n x => by
    -- Need: npow_lc x (n + 1) = mul (npow_lc x n) x
    sorry

-- Define integer scalar multiplication using Rat smul
def zsmul_lc (n : ℤ) (x : LC) : LC := smul (n : Coeff) x

instance : Ring LC where
  toSemiring := inferInstance
  neg := neg
  sub := sub
  sub_eq_add_neg := fun x y => rfl
  zsmul := zsmul_lc
  zsmul_zero' := fun x => by
    show zsmul_lc 0 x = zero
    simp only [zsmul_lc, Int.cast_zero, smul]
    -- (0 == 0) = true
    simp only [beq_self_eq_true, ↓reduceIte]
  zsmul_succ' := fun n x => by
    simp only [zsmul_lc, Int.ofNat_add_out]
    apply toHahnSeries_injective
    have hs : (smul ((n : ℤ) : Coeff) x : LC) = ((n : ℤ) : Coeff) • x := rfl
    have hs' : (smul ((n.succ : ℤ) : Coeff) x : LC) = ((n.succ : ℤ) : Coeff) • x := rfl
    simp only [hs, hs', toHahnSeries_smul, toHahnSeries_add]
    rw [show ((n.succ : ℤ) : Coeff) = (n : ℤ) + 1 by simp [Nat.succ_eq_add_one]]
    rw [add_smul, one_smul]
  zsmul_neg' := fun n x => by
    -- zsmul (Int.negSucc n) x = (zsmul n.succ x).neg
    -- i.e., smul (-(n+1)) x = -(smul (n+1) x)
    -- Follows from neg_smul
    sorry
  neg_add_cancel := fun x => by
    show neg x + x = zero
    apply toHahnSeries_injective
    -- Rewrite neg x = -x and zero = 0 for simp to work with standard lemmas
    have hneg : neg x = -x := rfl
    have hzero : (zero : LC) = 0 := rfl
    simp only [hneg, hzero, toHahnSeries_add, toHahnSeries_neg, toHahnSeries_zero]
    -- Goal: -x.toHahnSeries + x.toHahnSeries = 0
    exact _root_.neg_add_cancel _
  intCast := fun n => ofCoeff n
  intCast_ofNat := fun n => by
    show ofCoeff n = ofCoeff n
    rfl
  intCast_negSucc := fun n => by
    -- Goal: ofCoeff (Int.negSucc n) = (↑(n + 1)).neg
    -- This is: ofCoeff (-(n+1)) = -(ofCoeff (n+1))
    sorry

instance : CommRing LC where
  toRing := inferInstance
  mul_comm := fun x y => by
    show mul x y = mul y x
    exact mul_comm x y

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
  have hc_beq : (c == 0) = false := beq_eq_false_iff_ne.mpr hc
  unfold leadingExp leadingTerm?
  simp only [HSMul.hSMul, smul, hc_beq, Bool.false_eq_true, ↓reduceIte]
  rw [maxKey?_map_exp]
  cases hmax : x.coeffs.maxKey? with
  | none =>
    exfalso
    have h : x.coeffs.maxKey?.isNone = x.coeffs.isEmpty := Std.ExtTreeMap.isNone_maxKey?_eq_isEmpty
    simp only [hmax, Option.isNone_none] at h
    exact hx h.symm
  | some e =>
    have hget' : x.coeffs.get? e ≠ none := get?_maxKey?_isSome hmax
    simp only [Std.ExtTreeMap.get?_eq_getElem?] at hget'
    cases hget : x.coeffs[e]? with
    | none => exact absurd hget hget'
    | some v =>
      -- Both sides simplify to e since both maps have the same maxKey
      -- and the leadingTerm?.exp is just the maxKey
      -- Technical details: nested match simplification is complex, sorry for now
      sorry

/-- Leading exponent of multiplication. -/
theorem leadingExp_mul (x y : LC) (hx : ¬x.coeffs.isEmpty) (hy : ¬y.coeffs.isEmpty) :
    (x * y).leadingExp = x.leadingExp + y.leadingExp := sorry

end LC
end LeviCivita.Core