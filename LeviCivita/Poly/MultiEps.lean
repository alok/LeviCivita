/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Poly.Std
import LeviCivita.ForMathlib.Order.FinLex

/-!
# Several independent infinitesimals

`MultiEps k = FinLex k ℤ` is the exponent group for `k` independent infinitesimals
`ε 0, …, ε (k-1)`, with `ε i = ε^(eᵢ)` for the basis vector `eᵢ = FinLex.single i 1`.
The lexicographic order is computable (`LeviCivita/ForMathlib/Order/FinLex.lean`), so
`Poly (MultiEps k) R` can be `#eval`ed and `decide`d.

Ordering: `eᵢ > eⱼ` for `i < j` (the first index decides), and a larger exponent means a
smaller magnitude, so `ε i < ε j` for `i < j`: `ε 0` is the smallest. In fact `ε i < (ε j)ⁿ`
for every `n`.
-/

namespace LeviCivita

/-- Exponents for `k` independent infinitesimals: `ℤ`-tuples, ordered lexicographically. -/
abbrev MultiEps (k : ℕ) := FinLex k ℤ

namespace Poly

variable {k : ℕ} {R : Type*} [CommRing R] [DecidableEq R]

/-- The `i`-th independent infinitesimal `ε^(eᵢ)` in `Poly (MultiEps k) R`. -/
def epsI (i : Fin k) : Poly (MultiEps k) R := single (FinLex.single i 1) 1

theorem isInfinitesimal_epsI [NeZero (1 : R)] (i : Fin k) :
    (epsI i : Poly (MultiEps k) R).IsInfinitesimal := by
  rw [IsInfinitesimal, epsI, leadExp_single one_ne_zero]
  exact WithTop.coe_lt_coe.2 (FinLex.single_pos i one_pos)

variable [LinearOrder R] [IsStrictOrderedRing R]

theorem epsI_pos (i : Fin k) : 0 < (epsI i : Poly (MultiEps k) R) := by
  rw [← leadCoeff_pos_iff]
  simp [epsI, single, leadCoeff]

/-- `ε i ≪ ε j` for `i < j`; here just `ε i < ε j`. -/
theorem epsI_lt_epsI {i j : Fin k} (hij : i < j) :
    (epsI i : Poly (MultiEps k) R) < epsI j := by
  have hlt : FinLex.single j (1 : ℤ) < FinLex.single i 1 := FinLex.single_lt_single hij one_pos
  rw [lt_iff_exists_coeff]
  refine ⟨FinLex.single j 1, fun g hg => ?_, ?_⟩
  · simp [epsI, hg.ne, (hg.trans hlt).ne]
  · simp [epsI, hlt.ne]

end Poly

end LeviCivita
