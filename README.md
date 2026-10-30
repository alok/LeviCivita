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

Everything builds on Lean `v4.35.0-rc3` (`lake build`, `lake test`).

## Performance

Native compilation achieves **~1 billion ops/sec** for basic operations.

## Analysis: order, roots and exact jets (`LeviCivita.Analysis`)

`FastLC` is an ordered field: `x < y` compares the leading term of `y − x`. On top of
that: `abs`, `max`, `min` (at a tie in the standard part they pick the larger
infinitesimal part, so a seed `x + εv` yields a one-sided directional derivative),
`sqrt` by the binomial series, `grad`/`valueAndGrad`, and **exact Taylor jets** of
`sin`, `cos`, `exp`, `log`, `sinh`, `cosh`, `tan` and real powers: `f(a + ε)` carries
`f(a), f'(a), f''(a)/2, …` exactly through `ε⁴`, via `taylorAt`.

## Riemannian geometry (`LeviCivita.Geometry`)

Write a metric in LC arithmetic and get its curvature exactly, with no step sizes:

```lean
import LeviCivita.Geometry
open LeviCivita.Geometry LeviCivita.Fast.FastLC

-- Schwarzschild, (t, r, θ, φ), G = c = 1
let J := (MetricJet.at? (schwarzschild 1) (fun i => #[0, 5, 1, 0.5][i.val]!)).get!
J.ricci.maxAbs      -- ≈ 1e-17   (vacuum)
J.kretschmann       -- 48 M²/r⁶ = 0.003072
```

Evaluating `g` at `x + εv` gives `∂ᵥg` (the `ε¹` coefficient) and `½∂ᵥ²g` (`ε²`);
mixed partials follow by polarization, `∂ₖ∂ₗg = c₂(eₖ+eₗ) − c₂(eₖ) − c₂(eₗ)`. On that
exact 2-jet (`MetricJet`):

| | |
|---|---|
| `christoffel`, `christoffelFirst`, `christoffelDeriv` | `Γᵏᵢⱼ`, `Γₗᵢⱼ`, `∂ₘΓᵏᵢⱼ` |
| `riemann`, `riemannLower`, `ricci`, `scalarCurvature`, `einstein`, `kretschmann`, `sectional` | curvature |
| `covariantDerivVector`, `covariantDerivCovector`, `metricCompatibility` | `∇` of LC tensor fields |
| `geodesic`, `geodesicStep`, `parallelTransport` | RK4 on `ẍᵏ = −Γᵏᵢⱼẋⁱẋʲ` and `ẇᵏ = −Γᵏᵢⱼẋⁱwʲ` |
| `induced` | pull-back metric of an embedding `F : ℝⁿ → ℝᵐ` (second infinitesimal `ε^(1/1024)`) |
| `sphere2`, `sphere3`, `hyperbolicPlane`, `flatPolar`, `torus`, `schwarzschild` | examples |

`lake test` runs 35 checks against closed forms: Christoffel symbols of S², scalar
curvature of S² (2/r²), S³ (6/r²), H² (−2) and the torus, flat polar coordinates,
Schwarzschild Ricci-flatness and Kretschmann scalar, Riemann symmetries and the first
Bianchi identity, metric compatibility, the induced metric of S² ⊂ ℝ³, the Killing
equation for `∂_φ`, great-circle geodesics, conserved E and L on Schwarzschild
orbits, and parallel transport. See `docs/GEOMETRY.md` for how it works.

## License

MIT
