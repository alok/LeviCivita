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
def expTerm (δ : LC) (n : Nat) : LC := 
  let fact_n : Coeff := (List.range n |>.map (fun i => (i + 1 : Coeff)) |>.foldl (· * ·) 1)
  (fact_n⁻¹ : Coeff) • (δ ^ n)

/-- Partial sum of the exponential series. -/
def expPartialSum (δ : LC) (n : Nat) : LC := Id.run do
  let mut sum : LC := 0
  for i in [0:n+1] do
    sum := sum + expTerm δ i
  sum

/-! ## Infrastructure for Convergence -/

/-- Power of an infinitesimal has leading exponent proportional to the power. -/
theorem leadingExp_pow (δ : LC) (n : Nat) (hδ : ¬δ.coeffs.isEmpty) :
    (δ ^ (n + 1)).leadingExp = (n + 1) * δ.leadingExp := by
  induction n with
  | zero => 
    rw [LC.pow_one]
    simp
  | succ n ih =>
    rw [LC.pow_succ]
    have h_pow_nz : ¬(δ ^ (n + 1)).coeffs.isEmpty := sorry
    rw [LC.leadingExp_mul _ _ h_pow_nz hδ]
    rw [ih]
    simp [Nat.cast_succ]
    ring

/-- For infinitesimal δ, the leading exponent of Taylor terms tends to -∞. -/
theorem valuation_tendsto (δ : LC) (hδ : IsInfinitesimal δ) (hnonzero : ¬δ.coeffs.isEmpty) :
    ∀ (M : Exp), ∃ N : Nat, ∀ n ≥ N, (expTerm δ n).leadingExp < M := by
  intro M
  have he_neg : δ.leadingExp < 0 := sorry
  
  -- Take N = ceil(M / δ.leadingExp) + 1
  let N := (M / δ.leadingExp).ceil.toNat + 1
  exists N
  intro n hn
  unfold expTerm
  have h_fact_nz : ((List.range n |>.map (fun i => (i + 1 : Coeff)) |>.foldl (· * ·) 1)⁻¹ : Coeff) ≠ 0 := sorry
  have h_pow_nz : ¬(δ ^ n).coeffs.isEmpty := sorry
  rw [leadingExp_smul _ _ h_fact_nz h_pow_nz]
  match n with
  | 0 => sorry
  | n + 1 =>
    rw [leadingExp_pow δ n hnonzero]
    sorry

end LeviCivita.FormalTranscendental
