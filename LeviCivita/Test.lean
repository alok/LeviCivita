import LeviCivita.Core
import LeviCivita.Field

/-!
# Levi-Civita Field Tests

Tests and examples for the Levi-Civita field implementation.
-/

open LeviCivita.Core
open LeviCivita.Core.LC
open scoped LeviCivita.Core.LC
open LeviCivita.Field

namespace LeviCivita.Test

/-! ## Basic Arithmetic Tests -/

-- Create some numbers
#eval! toString (ε : LC)
#eval! toString (H : LC)
#eval! toString ((1 : LC) + ε)
#eval! toString ((2 : LC) * ε)

-- Arithmetic
#eval! toString (ε * H)
#eval! toString (ε * ε)
#eval! toString (H * H)

-- Signum tests
#eval! signum ε
#eval! signum (-ε)
#eval! signum ((1 : LC) - ε)
#eval! signum (ε - (1 : LC))

/-! ## Inversion Tests -/

-- Pure inversions
#eval! toString (invert (2 : LC))
#eval! toString (invert H)
#eval! toString (invert ε)

-- Non-pure inversion using series expansion
#eval! toString (invert ((1 : LC) + ε) 5)

/-! ## Derivative Tests -/

def square (x : LC) : LC := x * x
#eval! derivative square (3 : LC)

def cube (x : LC) : LC := x * x * x
#eval! derivative cube (2 : LC)

-- Higher derivatives
#eval! nthDerivative cube (2 : LC) 2

/-! ## Polynomial Evaluation -/

def poly (x : LC) : LC := (2 : LC) * x * x + (3 : LC) * x + (1 : LC)
#eval! derivative poly (1 : LC)

/-! ## Comparison Tests -/

-- Note: Comparison #evals are commented out because instLinearOrder
-- is noncomputable (depends on classical.choice). The proofs work
-- but runtime comparison is not executable.
-- #eval! ε < (1 : LC)
-- #eval! (1 : LC) < H
-- #eval! ε < ε * ε
-- #eval! ε * ε < ε

/-! ## Transcendental Function Tests -/

#eval! toString (LeviCivita.Field.exp ε 5)
#eval! toString (LeviCivita.Field.sin ε 3)
#eval! toString (LeviCivita.Field.cos ε 3)

-- Derivative of exp at 0 should be exp(0) = 1
#eval! derivative (fun x => LeviCivita.Field.exp x 8) (0 : LC)

-- Derivative of sin at 0 should be cos(0) = 1
#eval! derivative (fun x => LeviCivita.Field.sin x 8) (0 : LC)

end LeviCivita.Test
