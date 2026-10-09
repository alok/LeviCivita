/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Poly

/-!
# Tests for M2: accessors, standard part, ε-AD, several infinitesimals

As in `LeviCivita.Test`: `#guard_msgs` `#eval`s for the compiled code and named `decide` theorems
for the kernel (no `native_decide`). `decide +kernel` is used over `ℚ` because core's `Rat`
arithmetic is `@[irreducible]` for the elaborator.
-/

namespace LeviCivita.TestM2

open LeviCivita.Poly
open Polynomial (aeval X)

abbrev P := LeviCivita.Poly ℤ ℚ

/-! ### Accessors (`#eval`) -/

/-- info: 3 -/
#guard_msgs in #eval ((3 : P) + ε - 2 * H).std

/-- info: -2 -/
#guard_msgs in #eval ((3 : P) + ε - 2 * H).coeff (-1)

/-- info: some (-1) -/
#guard_msgs in #eval ((3 : P) + ε - 2 * H).leadExp

/-- info: none -/
#guard_msgs in #eval (0 : P).leadExp

/-- info: some 1 -/
#guard_msgs in #eval (ε : P).leadExp

/-- info: (true, false, false, true) -/
#guard_msgs in
#eval (decide (ε : P).IsInfinitesimal, decide (1 : P).IsInfinitesimal, decide (H : P).IsFinite,
  decide ((3 : P) + ε).IsFinite)

/-- info: 7 -/
#guard_msgs in #eval stdPart (⟨(7 : P) - 5 * ε ^ 2, by decide +kernel⟩ : finiteSubring)

/-! ### Accessors (kernel) -/

theorem std_example : ((3 : P) + ε - 2 * H).std = 3 := by decide +kernel

theorem coeff_example : ((3 : P) + ε - 2 * H).coeff (-1) = -2 := by decide +kernel

theorem leadExp_example : ((3 : P) + ε - 2 * H).leadExp = ((-1 : ℤ) : WithTop ℤ) := by
  decide +kernel

theorem isInfinitesimal_eps : (ε : P).IsInfinitesimal := by decide +kernel

theorem not_isInfinitesimal_one : ¬ (1 : P).IsInfinitesimal := by decide +kernel

theorem not_isFinite_H : ¬ (H : P).IsFinite := by decide +kernel

theorem isFinite_three_add_eps : ((3 : P) + ε).IsFinite := by decide +kernel

theorem not_isInfinitesimal_three_add_eps : ¬ ((3 : P) + ε).IsInfinitesimal := by decide +kernel

theorem isInfinitesimal_eps_sub_eps_sq : ((ε : P) - 7 * ε ^ 2).IsInfinitesimal := by decide +kernel

/-- `Poly ℤ ℤ`: plain `decide`, no attribute changes. -/
theorem int_isInfinitesimal_eps : (ε : Poly ℤ ℤ).IsInfinitesimal := by decide

theorem int_not_isFinite_H : ¬ (H : Poly ℤ ℤ).IsFinite := by decide

theorem stdPart_three_add_eps :
    stdPart (⟨(3 : P) + ε, by decide +kernel⟩ : finiteSubring) = 3 := by decide +kernel

/-- `stdPart` is a ring hom, so `stdPart ((3 + ε) * (2 - ε)) = 3 * 2` with no computation. -/
theorem stdPart_mul_example :
    stdPart ((⟨(3 : P) + ε, by decide +kernel⟩ : finiteSubring) * ⟨2 - ε, by decide +kernel⟩) =
      6 := by
  rw [map_mul, stdPart_three_add_eps]
  have : stdPart (⟨(2 : P) - ε, by decide +kernel⟩ : finiteSubring) = 2 := by decide +kernel
  rw [this]; norm_num

/-- The characterization theorem in action: `|ε| < C r` for every standard `r > 0`. -/
theorem abs_eps_lt (r : ℚ) (hr : 0 < r) : |(ε : P)| < C r :=
  isInfinitesimal_iff_forall_abs_lt.1 isInfinitesimal_eps r hr

/-- ... and `|1 - ε| ≤ C 2`, i.e. `1 - ε` is finite. -/
theorem one_sub_eps_bounded : ∃ r : ℚ, |(1 : P) - ε| ≤ C r :=
  isFinite_iff_exists_abs_le.1 (by decide +kernel)

/-! ### ε-AD -/

/-- info: 14 -/
#guard_msgs in #eval dualDeriv (fun x : P => x ^ 3 + 2 * x) 2

-- `3 · (-1/2)² + 2 = 11/4`
/-- info: 11 / 4 -/
#guard_msgs in #eval dualDeriv (fun x : P => x ^ 3 + 2 * x) (-1 / 2)

/-- `d/dx (x³ + 2x) = 3x² + 2`, which is `14` at `2`; checked by the kernel. -/
theorem ad_example_kernel : dualDeriv (fun x : P => x ^ 3 + 2 * x) 2 = 14 := by decide +kernel

/-- The same value via the general theorem (no evaluation of `Poly` arithmetic). -/
theorem ad_example_theorem :
    dualDeriv (fun x : P => aeval x (X ^ 3 + 2 * X : Polynomial ℚ)) 2 = 14 := by
  rw [dualDeriv_aeval_int]
  simp only [Polynomial.derivative_add, Polynomial.derivative_X_pow, Polynomial.derivative_mul,
    Polynomial.derivative_ofNat, Polynomial.derivative_X, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_zero, Polynomial.eval_one]
  norm_num

/-- `aeval` agrees with direct evaluation on this polynomial, so the kernel check and the theorem
are about the same function. -/
theorem aeval_eq_direct (x : P) : aeval x (X ^ 3 + 2 * X : Polynomial ℚ) = x ^ 3 + 2 * x := by
  simp [map_ofNat]

/-- The full expansion `(2 + ε)³ + 2(2 + ε) = 12 + 14ε + 6ε² + ε³`. -/
theorem cube_expansion :
    (C 2 + ε : P) ^ 3 + 2 * (C 2 + ε) = 12 + 14 * ε + 6 * ε ^ 2 + ε ^ 3 := by decide +kernel

/-! ### Two independent infinitesimals: `Γ = MultiEps 2 = FinLex 2 ℤ`

`FinLex k ℤ` (`LeviCivita/ForMathlib/Order/FinLex.lean`) is `ℤ`-tuples with a *computable*
lexicographic `LinearOrder`. (Mathlib's `Lex (Fin 2 → ℤ)` order is noncomputable; until M5 this
file installed a local computable instance on it.) It is order-isomorphic to Mathlib's
`Lex (Fin 2 → ℤ)` (`FinLex.toLexOrderAddIso`).

Ordering: `ε₁ = ε^(1,0)`, `ε₂ = ε^(0,1)`. The exponent `(1,0)` is lexicographically *larger*
than `(0,1)` (first coordinate decides), and a larger exponent means a *smaller* magnitude. So
`ε₁ < ε₂`; in fact `ε₁ < ε₂ⁿ` for every `n` (`(1,0) > (0,n)`): `ε₁` is infinitesimal relative
to `ε₂`. -/

/-- Exponents for two independent infinitesimals. -/
abbrev G2 := MultiEps 2

open FinLex (toFinLex)

/-- The bigger infinitesimal is `ε₂`; `ε₁` is infinitely smaller. -/
abbrev ε₁ : Poly G2 ℚ := single (toFinLex ![1, 0]) 1
abbrev ε₂ : Poly G2 ℚ := single (toFinLex ![0, 1]) 1

/-- `ε₁, ε₂` are the library's `epsI 0, epsI 1`. -/
theorem eps1_eq_epsI : ε₁ = epsI 0 := by decide +kernel

/-- info: 1 -/
#guard_msgs in #eval (ε₁ * ε₂).coeff (toFinLex ![1, 1])

-- `Repr` works for `Poly (MultiEps 2) ℚ`.
/-- info: 1 ε^![0, 1] + 1 ε^![1, 0] + 2 ε^![1, 1] -/
#guard_msgs in #eval ε₁ + ε₂ + 2 * ε₁ * ε₂

/-- info: (true, false, true) -/
#guard_msgs in #eval (decide (ε₁ < ε₂), decide (ε₂ < ε₁), decide (ε₁ < ε₂ ^ 5))

theorem eps1_lt_eps2 : ε₁ < ε₂ := by decide +kernel

theorem eps1_pos : 0 < ε₁ := by decide +kernel

theorem eps1_mul_eps2_pos : 0 < ε₁ * ε₂ := by decide +kernel

theorem eps1_mul_eps2_lt_eps1 : ε₁ * ε₂ < ε₁ := by decide +kernel

theorem eps1_lt_eps2_pow : ε₁ < ε₂ ^ 5 := by decide +kernel

theorem eps2_lt_one_thousandth : ε₂ < C (1 / 1000) := by decide +kernel

theorem eps1_isInfinitesimal : ε₁.IsInfinitesimal := by decide +kernel

/-- With `ℤ` coefficients plain `decide` works here too. -/
theorem int_eps1_lt_eps2 :
    (single (toFinLex ![1, 0]) 1 : Poly G2 ℤ) < single (toFinLex ![0, 1]) 1 := by decide

theorem int_eps1_mul_eps2_pos :
    (0 : Poly G2 ℤ) < single (toFinLex ![1, 0]) 1 * single (toFinLex ![0, 1]) 1 := by decide

/-- Plain `decide`, `ℤ` coefficients: `ε₁ < ε₂ ^ 3`. -/
theorem int_eps1_lt_eps2_pow :
    (epsI 0 : Poly G2 ℤ) < epsI 1 ^ 3 := by decide

/-- The same fact via the general theorem (no evaluation). -/
theorem eps1_lt_eps2' : (epsI 0 : Poly G2 ℚ) < epsI 1 := epsI_lt_epsI (by decide)

end LeviCivita.TestM2
