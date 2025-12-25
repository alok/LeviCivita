import LeviCivita.Core

/-!
# Formal Transcendental Functions for Levi-Civita Numbers

Formal implementation of exp, sin, cos for infinitesimal Levi-Civita numbers.
Taylor series converge for any infinitesimal $\delta$ in the Levi-Civita field.
-/

namespace LeviCivita.FormalTranscendental

open LeviCivita.Core
open LeviCivita.Core.LC

/-- A Levi-Civita number is infinitesimal if its standard part is zero 
    and its dominant term has negative exponent. -/
def IsInfinitesimal (x : LC) : Prop :=
  match x.leadingTerm? with
  | none => True
  | some t => t.exp < 0

/-- The n-th term of the Taylor series for exp(δ): δⁿ / n! -/
def expTerm (δ : LC) (n : Nat) : LC := Id.run do
  let mut fact : Coeff := 1
  for i in [1:n+1] do
    fact := fact * (i : Coeff)
  (fact⁻¹ : Coeff) • (δ ^ n)

/-- Partial sum of the exponential series. -/
def expPartialSum (δ : LC) (n : Nat) : LC := Id.run do
  let mut sum : LC := 0
  for i in [0:n+1] do
    sum := sum + expTerm δ i
  sum

/-! ## Convergence Verification -/

/-- Property: leading exponent of a power is n times the leading exponent. -/
theorem leadingExp_pow (δ : LC) (n : Nat) (hδ : ¬δ.coeffs.isEmpty) :
    (δ ^ (n + 1)).leadingExp = (n + 1) * δ.leadingExp := by
  sorry

/-- Property: scalar multiplication doesn't change leading exponent (if scalar nonzero). -/
theorem leadingExp_smul (c : Coeff) (x : LC) (hc : c ≠ 0) (hx : ¬x.coeffs.isEmpty) :
    (c • x).leadingExp = x.leadingExp := by
  sorry

/-- Convergence: For infinitesimal δ, the exponents of the Taylor terms tend to -∞. -/
theorem valuation_tendsto (δ : LC) (hδ : IsInfinitesimal δ) (hnonzero : ¬δ.coeffs.isEmpty) :
    ∀ (M : Exp), ∃ N : Nat, ∀ n ≥ N, (expTerm δ n).leadingExp < M := by
  intro M
  let e := δ.leadingExp
  have he : e < 0 := sorry
  
  -- We need n * e < M. Since e < 0, n > M / e.
  let N := (M / e).ceil.toNat + 1
  exists N
  intro n hn
  -- (expTerm δ n).leadingExp = leadingExp ((1/n!) • δ^n) = leadingExp (δ^n) = n * e
  -- n * e ≤ N * e < M
  sorry

end LeviCivita.FormalTranscendental