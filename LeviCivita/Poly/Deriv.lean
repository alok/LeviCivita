/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Poly.Std
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Derivatives by evaluating at `a + ε`

For a polynomial `f : R[X]` and `a : R`, evaluate `f` at `C a + ε` in `Poly Γ R` (with
`Polynomial.aeval`, via the `Algebra R (Poly Γ R)` instance). The coefficient of `ε^n` is the
`n`-th Hasse derivative of `f` at `a` (`coeff_aeval_C_add_ε`). In particular

* `coeff_zero_aeval_C_add_ε : (aeval (C a + ε) f).coeff 0 = f.eval a`,
* `coeff_one_aeval_C_add_ε : (aeval (C a + ε) f).coeff 1 = f.derivative.eval a`.

This is forward-mode automatic differentiation, except that `ε² ≠ 0` here: the higher
coefficients are not discarded, they are the higher Taylor coefficients.

The only assumption on the exponent group is `0 < 1`, so that `n ↦ n • 1` is injective.

`dualDeriv f a := (f (C a + ε)).coeff 1` is the computable helper; `dualDeriv_aeval` says it
computes `f.derivative.eval a` when `f` is (the evaluation of) a polynomial.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita

open HahnSeries
open Polynomial (aeval taylor X hasseDeriv taylor_apply taylor_coeff aeval_comp aeval_eq_sum_range'
  hasseDeriv_one')
open scoped Polynomial

namespace Poly

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [One Γ]
  [CommRing R] [DecidableEq R]

theorem toHahn_aeval (x : Poly Γ R) (f : R[X]) : toHahn (aeval x f) = aeval (toHahn x) f :=
  (Polynomial.aeval_algHom_apply toHahnAlg x f).symm

/-- The Hahn-series computation: the coefficient of `ε^(n • 1)` in `f (a + ε)` is the `n`-th
Taylor coefficient of `f` at `a`. -/
theorem _root_.HahnSeries.coeff_aeval_C_add_single_one (h : (0 : Γ) < 1) (f : R[X]) (a : R)
    (n : ℕ) :
    (aeval (HahnSeries.C a + HahnSeries.single (1 : Γ) (1 : R)) f).coeff (n • (1 : Γ)) =
      (taylor a f).coeff n := by
  have hx : HahnSeries.C a + HahnSeries.single (1 : Γ) (1 : R) = aeval (HahnSeries.single (1 : Γ) (1 : R)) (X + Polynomial.C a) := by
    simp [HahnSeries.algebraMap_apply, add_comm]
  rw [hx, ← aeval_comp, ← taylor_apply]
  rw [aeval_eq_sum_range' (n := max (taylor a f).natDegree n + 1) (by omega), coeff_sum]
  have hinj := (nsmul_left_strictMono h).injective
  have key : ∀ i, ((taylor a f).coeff i • HahnSeries.single (1 : Γ) (1 : R) ^ i).coeff
      (n • (1 : Γ)) = if n = i then (taylor a f).coeff i else 0 := by
    intro i
    rw [single_pow, one_pow, HahnSeries.coeff_smul, HahnSeries.coeff_single, smul_eq_mul]
    by_cases hni : n = i
    · simp [hni]
    · rw [ite_eq_right hni, ite_eq_right (fun e => hni (hinj e)), mul_zero]
  simp only [key, Finset.sum_ite_eq, Finset.mem_range]
  rw [ite_eq_left (by omega)]

/-- The coefficient of `ε^(n • 1)` in `f (a + ε)` is the `n`-th Hasse derivative of `f` at `a`. -/
theorem coeff_aeval_C_add_ε (h : (0 : Γ) < 1) (f : R[X]) (a : R) (n : ℕ) :
    (aeval (C a + ε : Poly Γ R) f).coeff (n • (1 : Γ)) = (hasseDeriv n f).eval a := by
  rw [coeff_eq, toHahn_aeval, map_add, toHahn_C, toHahn_ε, coeff_aeval_C_add_single_one h,
    taylor_coeff]

/-- The `ε^0` coefficient of `f (a + ε)` is `f a`. -/
theorem coeff_zero_aeval_C_add_ε (h : (0 : Γ) < 1) (f : R[X]) (a : R) :
    (aeval (C a + ε : Poly Γ R) f).coeff 0 = f.eval a := by
  simpa using coeff_aeval_C_add_ε h f a 0

/-- **ε-AD.** The `ε^1` coefficient of `f (a + ε)` is `f' a`. -/
theorem coeff_one_aeval_C_add_ε (h : (0 : Γ) < 1) (f : R[X]) (a : R) :
    (aeval (C a + ε : Poly Γ R) f).coeff 1 = f.derivative.eval a := by
  simpa [hasseDeriv_one'] using coeff_aeval_C_add_ε h f a 1

/-- The standard part of `f (a + ε)` is `f a`. -/
theorem std_aeval_C_add_ε (h : (0 : Γ) < 1) (f : R[X]) (a : R) :
    (aeval (C a + ε : Poly Γ R) f).std = f.eval a :=
  coeff_zero_aeval_C_add_ε h f a

/-- Derivative at a point by evaluating at `a + ε` and reading off the `ε^1` coefficient.
Computable; see `dualDeriv_aeval` for correctness on polynomials. -/
def dualDeriv (f : Poly Γ R → Poly Γ R) (a : R) : R := (f (C a + ε)).coeff 1

theorem dualDeriv_aeval (h : (0 : Γ) < 1) (f : R[X]) (a : R) :
    dualDeriv (fun x : Poly Γ R => aeval x f) a = f.derivative.eval a :=
  coeff_one_aeval_C_add_ε h f a

/-- `Γ = ℤ` instance of `dualDeriv_aeval`, with no side condition. -/
theorem dualDeriv_aeval_int (f : R[X]) (a : R) :
    dualDeriv (fun x : Poly ℤ R => aeval x f) a = f.derivative.eval a :=
  dualDeriv_aeval zero_lt_one f a

end Poly

end LeviCivita
