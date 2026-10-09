/-!
# Levi-Civita Numbers for Lean 4

A library for working with Levi-Civita numbers - a non-Archimedean ordered field
containing infinitesimals and infinite numbers. Useful for:

- Automatic differentiation via infinitesimals
- Non-standard analysis
- Symbolic computation with infinitesimals

## Main modules

- `Core`: Full mathematical implementation with proofs
- `Fast`: Optimized Float-based implementation for computation
- `PackedLC`: FloatArray-based implementation (no boxing overhead)
- `CompactLC`: Fixed exponent range [-3, 3] for maximum speed
- `Transcendental`: exp, log, sin, cos, etc.

## Quick Start

```lean
import LeviCivita

open LeviCivita.Fast.FastLC

-- Compute derivative of x³ at x = 2
#eval derivative (fun x => x * x * x) (ofFloat 2.0)  -- 12.0

-- Work with infinitesimals
#eval (ofFloat 1.0 + epsilon) * (ofFloat 2.0 + epsilon)
```
-/

import LeviCivita.Core
import LeviCivita.Field
import LeviCivita.Fast
import LeviCivita.UltraFast
import LeviCivita.CompactLC
import LeviCivita.PackedLC
import LeviCivita.Transcendental
import LeviCivita.HyperBivector
