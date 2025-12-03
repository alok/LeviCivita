# LeviCivita

A Lean 4 library for Levi-Civita numbers - a non-Archimedean ordered field containing infinitesimals and infinite numbers.

## Features

- **Automatic Differentiation**: Compute exact derivatives using infinitesimals
- **Multiple Implementations**: Choose between mathematical correctness and computational speed
- **Transcendental Functions**: exp, log, sin, cos, and more
- **Non-standard Analysis**: Work with infinitesimals and infinite numbers

## Installation

Add to your `lakefile.lean`:

```lean
require LeviCivita from git "https://github.com/alok/LeviCivita" @ "main"
```

Then run:
```bash
lake update
```

## Quick Start

```lean
import LeviCivita

open LeviCivita.Fast.FastLC

-- Compute derivative of x³ at x = 2
#eval derivative (fun x => x * x * x) (ofFloat 2.0)  -- 12.0

-- Work with infinitesimals
#eval (ofFloat 1.0 + epsilon) * (ofFloat 2.0 + epsilon)
-- 2 + 3ε + ε²
```

## Implementations

| Module | Storage | Speed | Use Case |
|--------|---------|-------|----------|
| `Core` | Rational coefficients | Slow | Proofs, exact computation |
| `Fast` | Array of Float terms | Fast | General computation |
| `PackedLC` | FloatArray (7 slots) | Fastest | AD with small exponents |
| `CompactLC` | Array Float (7 slots) | Fast | Fixed exponent range |

## Performance

Native compilation achieves **~1 billion ops/sec** for basic operations.

## License

MIT
