/-
Copyright (c) 2024-2025. All rights reserved.
Released under MIT license.
-/
import VersoManual

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- Enable inline Lean code with hover
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Levi-Civita Numbers" =>
%%%
authors := ["Alok Beniwal"]
%%%

A Lean 4 library for *Levi-Civita numbers* — a non-Archimedean ordered field
containing infinitesimals and infinite numbers.

# Introduction
%%%
tag := "intro"
%%%

Levi-Civita numbers extend the real numbers with infinitesimals, providing:

* *Automatic differentiation* via infinitesimals
* *Non-standard analysis* computations
* *Symbolic manipulation* of infinitesimal quantities

The key insight is that for a function `f`, we can compute:

```
f(x + ε) = f(x) + f'(x)ε + f''(x)/2 ε² + ⋯
```

where `ε` is an infinitesimal (nilpotent element satisfying `εⁿ = 0` for some `n`).

# Quick Start
%%%
tag := "quickstart"
%%%

## Using lakefile.toml (Recommended)

Add to your `lakefile.toml`:

```
[[require]]
name = "LeviCivita"
git = "https://github.com/alok/LeviCivita"
rev = "main"
```

## Using lakefile.lean

Alternatively, add to your `lakefile.lean`:

```
require LeviCivita from git "https://github.com/alok/LeviCivita" @ "main"
```

## Usage

Then run `lake update` and import the library:

```
import LeviCivita
open LeviCivita.Fast.FastLC

-- Compute derivative of x³ at x = 2
#eval derivative (fun x => x * x * x) (ofFloat 2.0)  -- 12.0

-- Work with infinitesimals
#eval (ofFloat 1.0 + epsilon) * (ofFloat 2.0 + epsilon)
-- 2 + 3ε + ε²
```

# Implementations
%%%
tag := "implementations"
%%%

LeviCivita provides multiple implementations optimized for different use cases:

## Core
%%%
tag := "impl-core"
%%%

The mathematically rigorous implementation using {lean}`Rat` coefficients.
Best for proofs and exact symbolic computation.

*Storage*: {lean}`Rat` coefficients
*Speed*: Slow
*Use Case*: Proofs, exact computation

## Fast
%%%
tag := "impl-fast"
%%%

{lean}`Array`-based implementation using {lean}`Float` coefficients.
Good balance of speed and flexibility for general computation.

*Storage*: {lean}`Array` of {lean}`Float` terms
*Speed*: Fast
*Use Case*: General computation

## PackedLC
%%%
tag := "impl-packed"
%%%

{lean}`FloatArray`-based implementation with 7 fixed slots.
Fastest for automatic differentiation with small exponent ranges.
Achieves approximately 1 billion ops/sec with native compilation.

*Storage*: {lean}`FloatArray` (7 slots)
*Speed*: Fastest
*Use Case*: AD with small exponents

## CompactLC
%%%
tag := "impl-compact"
%%%

Fixed exponent range `[-3, 3]` using {lean}`Array Float`.
Maximum speed for applications that fit within the exponent bounds.

*Storage*: {lean}`Array Float` (7 slots)
*Speed*: Fast
*Use Case*: Fixed exponent range

# Mathematical Background
%%%
tag := "math-background"
%%%

## Definition
%%%
tag := "definition"
%%%

A Levi-Civita number is a formal power series:

```
x = Σ_{q ∈ ℚ} aₑ εᵠ
```

where:
- `aₑ ∈ ℝ` (or `ℚ` for exact computation)
- The support `{q : aₑ ≠ 0}` is left-finite (bounded below)
- `ε` is an infinitesimal satisfying `0 < εᵠ < r` for all `r > 0, q > 0`

## Properties
%%%
tag := "properties"
%%%

The Levi-Civita field has remarkable properties:

1. *Non-Archimedean*: Contains infinitesimals and infinite elements
2. *Real-closed*: Every polynomial with an odd degree has a root
3. *Cauchy-complete*: Every Cauchy sequence converges
4. *Totally ordered*: Compatible with the field operations

## Automatic Differentiation
%%%
tag := "autodiff"
%%%

For smooth functions, Taylor expansion gives:

```
f(a + ε) = f(a) + f'(a)ε + f''(a)/2! ε² + ⋯
```

Extracting the coefficient of `ε` yields the exact derivative `f'(a)`.

# API Reference
%%%
tag := "api"
%%%

## Core Operations
%%%
tag := "api-core"
%%%

- `epsilon` : The infinitesimal generator ε
- `ofFloat` / `ofRat` : Lift real numbers
- `derivative` : Compute derivatives via infinitesimals
- `+`, `-`, `*`, `/` : Field operations
- `<`, `≤`, `>`, `≥` : Total ordering

## Transcendental Functions
%%%
tag := "api-transcendental"
%%%

- `exp`, `log` : Exponential and logarithm
- `sin`, `cos`, `tan` : Trigonometric functions
- `sqrt` : Square root (for positive numbers)

# Performance
%%%
tag := "performance"
%%%

Benchmark results (native compilation):

| Implementation | Ops/sec | Use Case |
|----------------|---------|----------|
| Core           | ~1M     | Proofs   |
| Fast           | ~100M   | General  |
| PackedLC       | ~1B     | AD       |

# License
%%%
tag := "license"
%%%

MIT License. See the [repository](https://github.com/alok/LeviCivita) for details.
