/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Util.AssertAxioms
import LeviCivita.Test
import LeviCivita.TestM2
import LeviCivita.TestM3
import LeviCivita.TestM4

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
  aeval_eq_direct cube_expansion eps1_lt_eps2 eps1_pos eps1_mul_eps2_pos
  eps1_mul_eps2_lt_eps1 eps1_lt_eps2_pow eps2_lt_one_thousandth eps1_isInfinitesimal
  int_eps1_lt_eps2 int_eps1_mul_eps2_pos eps1_eq_epsI int_eps1_lt_eps2_pow eps1_lt_eps2'

/-! ### M3 -/

section M3
open LeviCivita.Geometry LeviCivita.LazySign LeviCivita.TestM3

-- Predicates: determinant specs, antisymmetry, translation, naturality
#assert_axioms orient2d_eq_det orient3d_eq_det incircle_eq_det insphere_eq_det
  orient2d_swap₁₂ orient2d_swap₂₃ orient2d_swap₁₃ orient2d_rotate orient3d_swap₁₂
  orient3d_swap₂₃ orient3d_swap₃₄ incircle_swap₁₂ incircle_swap₃₄ insphere_swap₁₂
  insphere_swap₄₅ orient2d_add_const orient3d_add_const incircle_add_const insphere_add_const
  map_det3 map_det4 map_orient2d map_orient3d map_incircle map_insphere

-- SoS
#assert_axioms digit_sum_lt digit_extract sosSubst toHahn_sosSubst sosExpo_injOn
  sosSubst_ne_zero DegLe.mul DegLe.det3 DegBd.det3 DegBd.det4 sosIdx_injective sosPoint
  sosSubst_mvPoint orient2dSoS orient3dSoS incircleSoS insphereSoS
  orient2dSoS_ne_zero orient3dSoS_ne_zero incircleSoS_ne_zero insphereSoS_ne_zero
  sign_of_isFinite_of_std_ne_zero orient2dSoS_std orient2dSoS_sign orient3dSoS_std
  orient3dSoS_sign incircleSoS_std incircleSoS_sign insphereSoS_std insphereSoS_sign
  orient2dSoS_swap₁₂ orient2dSoS_sign_swap₁₂ Geometry.sign_neg orient2dSoS_sign_ne_zero
  orient3dSoS_sign_ne_zero signOf_int

-- Truncation and lazy sign
#assert_axioms incircleExpr eval_incircleExpr incircleLazy incircleLazy_sound
  Poly.truncLT Poly.mulTrunc Poly.toHahn_truncLT Poly.mulTrunc_eq
  Poly.truncLT_add Poly.truncLT_neg Poly.truncLT_sub Poly.mulTrunc_truncLT Poly.truncLT_mul
  Poly.leadCoeff_truncLT Poly.sign_truncLT Poly.truncLT_eq_self
  Expr.evalTrunc_eq lazySign lazySign_sound lazySign_complete lazySign_complete_of_ne_zero
  lazySignIter lazySignIter_sound lazySignIter_complete sqStep sqStep_ge orient2dExpr eval_orient2dExpr
  orient2dLazy orient2dLazy_sound orient2dLazy_complete

-- M3 tests
#assert_axioms orient2d_ccw incircle_inside orient2d_rat sos_collinear sos_collinear_swap
  sos_coincident sos_coincident_swap sos_generic sos_ne_zero sos_sign_ne_zero sos_generic'
  sos3_coplanar sos3_coplanar_swap sos_cocircular sos_incircle_ne_zero lazy_collinear
  lazy_agrees lazy_sound_example lazy_cocircular truncLT_example mulTrunc_example

end M3

/-! ### M4 -/

section M4
open LeviCivita.Approx LeviCivita.TestM4

-- Hahn-series lemmas: agreement below a precision, our `truncLT_mul`
#assert_axioms LeviCivita.HahnSeries.agree_iff_le_orderTop
  LeviCivita.HahnSeries.le_orderTop_add_of_coeff LeviCivita.HahnSeries.coeff_mul_eq_of_agree
  LeviCivita.HahnSeries.coeff_mul_eq_of_agree_sub LeviCivita.HahnSeries.truncLT_mul_of_orderTop
  LeviCivita.HahnSeries.orderTop_le_orderTop_truncLT

-- Truncation API
#assert_axioms Poly.truncTop Poly.truncLT_truncLT Poly.coeff_truncTop Poly.truncTop_truncTop
  Poly.mulTruncTop Poly.mulTruncTop_eq exact ofPoly withPrec represents_ofPoly
  Represents.withPrec Represents.mono represents_truncTop_iff

-- `Represents`
#assert_axioms represents_iff_le_orderTop represents_iff_truncLT represents_iff_truncLT_eq
  represents_top_iff represents_exact represents_exact_iff Represents.ord_le
  Represents.orderTop_eq Represents.leadingCoeff_eq Represents.ne_zero

-- Sound arithmetic
#assert_axioms Approx.add Approx.neg Approx.sub Approx.mul Represents.add Represents.neg
  Represents.sub represents_mul_val Represents.mul Represents.mul_exact

-- Certified sign
#assert_axioms sign? sign?_exact sign?_of_certified sign?_eq_none_iff decidePos?
  decidePos?_exact_ne Represents.leadingCoeff_eq_of_sign? sign?_sound decidePos?_accept
  decidePos?_reject

-- Inverse
#assert_axioms newtonInv invPrec invCore inv? orderTop_inv Represents.inv_of_residual
  Represents.invCore inv?_isSome Represents.inv? exists_inv?_represents

-- M4 tests
#assert_axioms inv_one_add_eps inv_mul_self_val inv_mul_self_represents inv_b_prec
  mul_prec_example mul_unknown_order sign_unresolved sign_resolved sign_exact_zero
  accept_example pos_of_approx inv_pos_example


end M4

/-! ### M5 -/

section M5

-- `LeviCivita/ForMathlib/Order/FinLex.lean` (imports only Mathlib; audited here)
#assert_axioms Fin.lexCmp Fin.lexCmp_eq_eq_iff Fin.lexCmp_eq_lt_iff Fin.lexCmp_swap
  FinLex.instFunLike FinLex.ext FinLex.equivFun FinLex.instPartialOrder FinLex.lt_iff_toLex_lt
  FinLex.le_iff_toLex_le FinLex.lt_iff_exists FinLex.le_iff_eq_or_lt FinLex.lexCmp_eq_lt_iff
  FinLex.lexCmp_eq_eq_iff FinLex.lexCmp_ne_gt_iff FinLex.decidableLE FinLex.decidableLT
  FinLex.decidableEq FinLex.instLinearOrder FinLex.compare_eq_lexCmp FinLex.toLex_strictMono
  FinLex.instAddCommGroup FinLex.instIsOrderedCancelAddMonoid FinLex.single FinLex.single_apply
  FinLex.single_lt_single FinLex.single_pos FinLex.toLexOrderAddIso FinLex.toLexOrderIso
  Pi.Lex.decidableLTFin Pi.Lex.linearOrderFin Pi.Lex.linearOrderFin_eq

-- `MultiEps`
#assert_axioms Poly.epsI Poly.epsI_pos Poly.epsI_lt_epsI Poly.isInfinitesimal_epsI

end M5
