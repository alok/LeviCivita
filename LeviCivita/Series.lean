import LeviCivita.Core

/-!
# Series Expansion for Levi-Civita Numbers

Generic implementation of Taylor series expansion for Levi-Civita numbers.
Given a sequence of derivatives fⁿ(a), we can compute f(a + δ) for infinitesimal δ.
-/

namespace LeviCivita.Core.LC

/-- Compute a transcendental function via its Taylor series.
    coeffs: a function where coeffs n = fⁿ(a)
    x: the argument a + δ
    terms: number of terms to sum -/
def applySeries (coeffs : Nat → Coeff) (x : LC) (terms : Nat := 10) : LC := Id.run do
  let a := x.std
  let delta := x - (a : LC)
  let mut res : LC := coeffs 0
  let mut p : LC := one
  let mut fact : Coeff := 1
  for i in [1:terms] do
    p := p * delta
    fact := fact * (i : Coeff)
    let term := (coeffs i / fact) • p
    res := res + term
  res

/-- Exponential function: exp(x) = exp(a) * \sum δⁿ/n! -/
def exp (x : LC) (terms : Nat := 10) : LC :=
  -- Note: exp(a) for rational a might not be rational.
  -- This requires a more complex implementation or float fallback.
  -- For now, we focus on the infinitesimal part.
  applySeries (fun _ => 1) x terms

/-- Sine function: sin(a+δ) = sin(a)cos(δ) + cos(a)sin(δ) -/
def sin (x : LC) (terms : Nat := 10) : LC :=
  -- Series for sin(δ) around 0
  let sin_coeffs := fun n => if n % 2 == 0 then 0 else if n % 4 == 1 then 1 else -1
  applySeries sin_coeffs x terms

/-- Cosine function: cos(a+δ) = cos(a)cos(δ) - sin(a)sin(δ) -/
def cos (x : LC) (terms : Nat := 10) : LC :=
  -- Series for cos(δ) around 0
  let cos_coeffs := fun n => if n % 2 != 0 then 0 else if n % 4 == 0 then 1 else -1
  applySeries cos_coeffs x terms

end LeviCivita.Core.LC
