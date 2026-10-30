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

## The field, analysis and nonstandard analysis

Four modules on top of `Fast` (all exercised by `lake test`, 58 checks against
closed forms). `docs/NSA.md` is a guided tour.

### `LeviCivita.Analysis`: the ordered field

* Order: `x < y` compares the leading term of `y − x`; `signum`, `abs`, `max`, `min`
  (`max (1 + ε) (1 + 2ε) = 1 + 2ε`), and the valuation `valuation?` (`ν(ε) = 1`, `ν(H) = −1`).
* Division and roots with adaptive precision: `x = l (1 + δ)` splits off the leading
  monomial, and `invertTo`/`div?`, `rpow` (any real power of a positive element, finite
  or infinite), `sqrt`, `root n` (odd roots of negatives too) sum a series in `δ`
  until it passes a requested valuation. `(H + 1)^{1/3} = H^{1/3} + ⅓H^{−2/3} − …`,
  `∛(−ε) = −ε^{1/3}`.
* Exact Taylor germs of `sin`, `cos`, `exp`, `log`, `sinh`, `cosh`, `tan`: `f(a + ε)`
  carries `f(a), f'(a), f''(a)/2, …` through `ε⁴`. Outside the domain (`exp H`, `log ε`)
  the result is `undefined`.
* `grad`/`valueAndGrad`: the whole gradient in **one** evaluation, coordinate `i`
  seeded at its own scale `ε^{1+i/n}`. At creases of `max`/`min`/`abs` this is a
  lexicographic derivative (one smooth piece), not a mix of one-sided partials.

### `LeviCivita.NSA`: standard part and transfer

* `isInfinitesimal`, `isFinite`, `isInfinite`, `isStandard`, `st?` (standard part,
  `none` for infinite), `infinitelyClose`.
* `RealLike`: write a function once; at `Float` it is `f`, at `LC` its natural
  extension `*f`. `Ext` wraps one and computes the nonstandard definitions:

```lean
import LeviCivita.NSA
open LeviCivita

def sinc : Ext := ⟨fun x => RealLike.sin x / x⟩
#eval sinc.limit? 0                                   -- some 1.0   (st (sin ε / ε))
def r : Ext := ⟨fun x => (RealLike.ofFloat 3 * x * x + RealLike.ofFloat 1) / (x * x - RealLike.ofFloat 5)⟩
#eval r.limitAtInfinity?                              -- some 3.0   (st *r(H))
def a : Ext := ⟨fun x => RealLike.abs x⟩
#eval a.deriv? 0                                      -- none: quotients ±1 at δ = ±ε
```

### `LeviCivita.Germ`: fast exact gradients

`Germ` is a finite element modulo valuation `≥ 2`, a ring quotient, so truncating
after every operation is exact for first derivatives. `Germ.grad` stays `n + 1`
terms long; RayTrace4D computes every surface normal with it.

### `LeviCivita.Hyperfinite`: integrals as hyperfinite sums

For a polynomial, the Riemann sum with `N` steps has a closed form in `N`
(Faulhaber), so it can be evaluated at `N = H`. The standard part is the integral.
The infinitesimal tail is the rule's exact error: for the left rule `−(b−a)(f(b)−f(a))/2 · ε`,
and for the midpoint rule `−(b−a)²(f'(b)−f'(a))/24 · ε²`.

## License

MIT
