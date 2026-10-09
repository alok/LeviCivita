/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Util.AssertAxioms
import LeviCivita.Test
import LeviCivita.TestM2

/-!
# Axiom audit

Built as part of `lake build` (it is a root of the default library), so CI fails if any key
declaration depends on `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler` or any custom axiom.
-/

open LeviCivita LeviCivita.Poly LeviCivita.Test LeviCivita.TestM2

-- Denotation and injectivity
#assert_axioms toHahn toHahn_injective toHahnFun_injective eq_of_hahnL_eq
  toHahnFun_add toHahnFun_mul toHahnFun_neg toHahnFun_pow toHahn_smul toHahn_ε toHahn_H

-- Transported algebra
#assert_axioms instCommRing commRingAux

-- Sign and order
#assert_axioms sign_eq_one_iff sign_eq_neg_one_iff sign_eq_zero_iff lt_iff_sign le_iff_sign
  decidableLT decidableLE instLinearOrder linearOrderAux toLexHahn_strictMono
  instIsStrictOrderedRing

-- `decide` tests
#assert_axioms eps_lt_one_thousandth eps_pos eps_sq_lt_eps ten_pow_nine_lt_H eps_mul_H
  one_add_eps_mul_one_sub_eps H_sq_gt neg_eps_lt_zero eps_le_eps not_H_le_eps
  eps_lt_one_thousandth' eps_pos' eps_sq_lt_eps' ten_pow_nine_lt_H' eps_mul_H'
  one_add_eps_mul_one_sub_eps' int_eps_mul_H int_ten_pow_nine_lt_H int_eps_pos
  sqrt_eps_sq eps_lt_sqrt_eps eps_sq_pos toHahn_eps

/-! ### M2 -/

-- Algebra structure and bundled maps
#assert_axioms CHom instAlgebra smul_eq_C_mul toHahnAlg toHahnAlg_injective toLexHahnHom
  toLexHahnHom_strictMono toLexHahnHom_injective toLexHahnEmb toLexHahn_abs

-- Accessors
#assert_axioms coeff_eq leadExp_eq_orderTop leadCoeff_eq_leadingCoeff coeff_injective
  coeff_leadExp coeff_eq_zero_of_lt_leadExp lt_leadExp_of_coeff_eq_zero leadExp_eq_top_iff

-- Finite / infinitesimal / standard part
#assert_axioms IsInfinitesimal.add IsInfinitesimal.neg IsInfinitesimal.mul_left
  IsInfinitesimal.mul_right IsFinite.add IsFinite.mul IsFinite.neg isFinite_C
  IsFinite.isInfinitesimal_sub_C_std IsFinite.isInfinitesimal_iff_std_eq_zero std_mul
  finiteSubring stdPart stdPart_C isInfinitesimal_sub_C_stdPart mem_ker_stdPart
  infinitesimalIdeal mem_infinitesimalIdeal isInfinitesimal_ε
  lt_iff_exists_coeff leadCoeff_pos_iff leadExp_abs
  isFinite_iff_exists_abs_le isInfinitesimal_iff_forall_abs_lt

-- ε-AD
#assert_axioms toHahn_aeval HahnSeries.coeff_aeval_C_add_single_one coeff_aeval_C_add_ε
  coeff_zero_aeval_C_add_ε coeff_one_aeval_C_add_ε std_aeval_C_add_ε dualDeriv
  dualDeriv_aeval dualDeriv_aeval_int

-- M2 tests
#assert_axioms std_example coeff_example leadExp_example isInfinitesimal_eps
  not_isInfinitesimal_one not_isFinite_H isFinite_three_add_eps not_isInfinitesimal_three_add_eps
  isInfinitesimal_eps_sub_eps_sq int_isInfinitesimal_eps int_not_isFinite_H stdPart_three_add_eps
  stdPart_mul_example abs_eps_lt one_sub_eps_bounded ad_example_kernel ad_example_theorem
  aeval_eq_direct cube_expansion lexLinearOrder eps1_lt_eps2 eps1_pos eps1_mul_eps2_pos
  eps1_mul_eps2_lt_eps1 eps1_lt_eps2_pow eps2_lt_one_thousandth eps1_isInfinitesimal
  int_eps1_lt_eps2 int_eps1_mul_eps2_pos
