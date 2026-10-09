/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Util.AssertAxioms
import LeviCivita.Test

/-!
# Axiom audit

Built as part of `lake build` (it is a root of the default library), so CI fails if any key
declaration depends on `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler` or any custom axiom.
-/

open LeviCivita LeviCivita.Poly LeviCivita.Test

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
