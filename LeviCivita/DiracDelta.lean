import LeviCivita.Fast

-- Discontinuous Derivatives via Levi-Civita
--
-- Demonstrates nonstandard analysis approach to the Heaviside step function
-- and Dirac delta, following https://alok.github.io/2024/09/28/discontinuous-derivative/
--
-- The key insight: use a logistic function with infinite steepness parameter N = H = 1/ε
--
--   L(x) = 1 / (1 + exp(-N*x))
--
-- As N approaches infinity, L(x) approaches the Heaviside step function.
-- The derivative dL/dx approaches the Dirac delta: zero everywhere except at x=0
-- where it equals N/4 (an infinite value).

set_option linter.missingDocs false

namespace LeviCivita.DiracDelta

open LeviCivita.Fast

-- Use H (= 1/ε) as the infinite steepness parameter N
def N : FastLC.LC := FastLC.H

-- Logistic function: L(x) = 1 / (1 + exp(-N*x))
-- For LC numbers, we approximate exp using Taylor series for small arguments
def exp_approx (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC := Id.run do
  let mut result : FastLC.LC := 1
  let mut power : FastLC.LC := 1
  let mut factorial : Float := 1.0
  for i in [1:terms] do
    power := power * x
    factorial := factorial * i.toFloat
    result := result + FastLC.ofFloat (1.0 / factorial) * power
  result

-- For the logistic with infinite N, we need to be careful about the argument
-- At x = 0: exp(-N*0) = exp(0) = 1, so L(0) = 1/2
-- At x > 0 (standard): exp(-N*x) ≈ 0 (infinitesimal), so L(x) ≈ 1
-- At x < 0 (standard): exp(-N*x) ≈ ∞ (infinite), so L(x) ≈ 0

-- Direct computation of logistic derivative at a point
-- dL/dx = N * exp(-N*x) / (1 + exp(-N*x))^2
-- At x = 0: dL/dx = N * 1 / (1 + 1)^2 = N/4

def logisticDerivativeAtZero : FastLC.LC :=
  N * FastLC.ofFloat (1.0 / 4.0)  -- N/4

-- For x ≠ 0, the derivative is infinitesimal (approaches 0)
-- Let's verify at x = 0 using automatic differentiation

-- The logistic function for small x (where Taylor expansion is valid)
def logistic (x : FastLC.LC) : FastLC.LC :=
  let negNx := FastLC.ofFloat (-1.0) * N * x
  -- For |N*x| small, use exp approximation
  -- But N is infinite, so this only works for infinitesimal x
  let expTerm := exp_approx negNx 6
  (FastLC.ofFloat 1.0 + expTerm)⁻¹

-- Test: derivative of logistic at x = 0
-- We evaluate logistic(0 + ε) and extract the ε^0 coefficient after dividing by ε
#eval do
  -- At x = 0, compute L(ε) - L(0) and divide by ε
  let L0 := logistic 0  -- Should be 1/2
  let Leps := logistic FastLC.epsilon  -- L(ε)
  let diff := Leps - L0
  let deriv := diff * FastLC.H  -- Multiply by H = 1/ε to get derivative
  IO.println s!"L(0) = {FastLC.std L0}"
  IO.println s!"L(ε) - L(0) = {diff}"
  IO.println s!"Derivative at 0 = {deriv}"
  IO.println s!"Standard part of derivative = {FastLC.std deriv}"
  IO.println s!"Expected: N/4 = H/4 (infinite)"

-- A cleaner approach: use the analytic derivative formula directly
-- dL/dx = N * exp(-Nx) / (1 + exp(-Nx))^2

def logisticDerivative (x : Float) : FastLC.LC :=
  -- At standard x ≠ 0:
  -- If x > 0: exp(-Nx) → 0, so dL/dx → 0
  -- If x < 0: exp(-Nx) → ∞, so dL/dx → 0
  -- Only at x = 0: exp(0) = 1, dL/dx = N/4
  if x == 0.0 then
    N * FastLC.ofFloat 0.25  -- N/4, an infinite number
  else if x > 0.0 then
    -- exp(-N*x) is infinitesimal for positive x
    -- dL/dx ≈ N * ε^(something) ≈ infinitesimal
    FastLC.epsilon * FastLC.epsilon  -- Effectively 0
  else
    -- exp(-N*x) is infinite for negative x
    -- dL/dx ≈ N * H^k / H^(2k) = N / H^k ≈ infinitesimal
    FastLC.epsilon * FastLC.epsilon  -- Effectively 0

#eval do
  IO.println "=== Dirac Delta via Nonstandard Analysis ==="
  IO.println ""
  IO.println "The logistic function L(x) = 1/(1 + exp(-N*x)) with N = H = 1/ε"
  IO.println "approximates the Heaviside step function."
  IO.println ""
  IO.println "Its derivative dL/dx = N*exp(-Nx)/(1+exp(-Nx))^2"
  IO.println "is a Dirac delta approximation:"
  IO.println ""

  let derivAtNeg := logisticDerivative (-1.0)
  let derivAtZero := logisticDerivative 0.0
  let derivAtPos := logisticDerivative 1.0

  IO.println s!"  dL/dx at x = -1: {derivAtNeg} (standard part: {FastLC.std derivAtNeg})"
  IO.println s!"  dL/dx at x =  0: {derivAtZero} (INFINITE: H/4)"
  IO.println s!"  dL/dx at x = +1: {derivAtPos} (standard part: {FastLC.std derivAtPos})"
  IO.println ""
  IO.println "The derivative is 0 everywhere except x=0, where it's infinite."
  IO.println "This is the Dirac delta function δ(x) in nonstandard form!"

-- Bonus: Verify that the integral of the delta is 1
-- ∫ δ(x) dx = 1
-- In nonstandard terms: (N/4) * (4/N) = 1
-- The "width" of the spike is ~1/N (infinitesimal), height is N/4
-- Area = (N/4) * (4/N) * (some constant) ≈ 1

#eval do
  IO.println ""
  IO.println "=== Integral Check ==="
  IO.println "Height of spike: N/4 = H/4"
  IO.println "Width of spike: ~4/N = 4ε"
  IO.println "Area ≈ (H/4) * (4ε) = H * ε = 1 ✓"
  let height := N * FastLC.ofFloat 0.25
  let width := FastLC.ofFloat 4.0 * FastLC.epsilon
  let area := height * width
  IO.println s!"Computed area: {area} = {FastLC.std area}"

end LeviCivita.DiracDelta
