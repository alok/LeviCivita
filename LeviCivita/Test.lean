import LeviCivita.Field

/-!
# Levi-Civita Field Tests

Tests and examples for the Levi-Civita field implementation.
-/

open LeviCivita.Field

namespace LeviCivita.Test

/-! ## Basic Arithmetic Tests -/

-- Create some numbers
#eval toString (ε : LC)  -- should print "ε"
#eval toString (H : LC)  -- should print "H"
#eval toString ((1 : LC) + ε)  -- should print "1 + ε"
#eval toString ((2 : LC) * ε)  -- should print "2ε"

-- Arithmetic
#eval toString (ε * H)  -- should be 1
#eval toString (ε * ε)  -- should be ε²
#eval toString (H * H)  -- should be H²

-- Signum tests
#eval LC.signum ε  -- 1 (positive infinitesimal)
#eval LC.signum (-ε)  -- -1
#eval LC.signum ((1 : LC) - ε)  -- 1 (1 is dominant)
#eval LC.signum (ε - (1 : LC))  -- -1

/-! ## Inversion Tests -/

-- Pure inversions
#eval toString (LC.invert (2 : LC))  -- 0.5
#eval toString (LC.invert H)  -- ε
#eval toString (LC.invert ε)  -- H

-- Non-pure inversion using series expansion
-- 1/(1+ε) ≈ 1 - ε + ε² - ε³ + ...
#eval toString (LC.invert ((1 : LC) + ε) 5)

/-! ## Derivative Tests -/

-- f(x) = x², f'(x) = 2x
-- At x = 3: f'(3) = 6
def square (x : LC) : LC := x * x
#eval LC.derivative square (3 : LC)  -- should be 6

-- f(x) = x³, f'(x) = 3x²
-- At x = 2: f'(2) = 12
def cube (x : LC) : LC := x * x * x
#eval LC.derivative cube (2 : LC)  -- should be 12

-- Higher derivatives
-- f(x) = x³, f''(x) = 6x
-- At x = 2: f''(2) = 12
#eval LC.nthDerivative cube (2 : LC) 2  -- should be 12

/-! ## Polynomial Evaluation -/

-- p(x) = 2x² + 3x + 1
-- p'(x) = 4x + 3
-- At x = 1: p'(1) = 7
def poly (x : LC) : LC := (2 : LC) * x * x + (3 : LC) * x + (1 : LC)
#eval LC.derivative poly (1 : LC)  -- should be 7

/-! ## Comparison Tests -/

#eval ε < (1 : LC)  -- true (infinitesimal < finite)
#eval (1 : LC) < H  -- true (finite < infinite)
#eval ε < ε * ε  -- false (ε > ε²)
#eval ε * ε < ε  -- true (ε² < ε)

/-! ## Transcendental Function Tests -/

-- exp(ε) = 1 + ε + ε²/2! + ε³/3! + ...
#eval toString (LC.exp ε 5)

-- sin(ε) ≈ ε - ε³/6 + ...
#eval toString (LC.sin ε 3)

-- cos(ε) ≈ 1 - ε²/2 + ...
#eval toString (LC.cos ε 3)

-- Verify sin²(ε) + cos²(ε) ≈ 1
-- (This won't be exact due to truncation, but should be close)
private def sincos_identity : LC :=
  let s := LC.sin ε 5
  let c := LC.cos ε 5
  s * s + c * c
#eval toString sincos_identity

-- Derivative of exp at 0 should be exp(0) = 1
-- d/dx exp(x) = exp(x), so at x=0, derivative = 1
#eval LC.derivative (fun x => LC.exp x 8) (0 : LC)

-- Derivative of sin at 0 should be cos(0) = 1
#eval LC.derivative (fun x => LC.sin x 8) (0 : LC)

end LeviCivita.Test
