# Curvature from infinitesimals: how `LeviCivita.Geometry` works

This guide explains the design of the differential-geometry module well enough
for you to rebuild it yourself. It also explains the decisions that were not obvious.

## 1. The problem

Riemannian curvature is built from second derivatives of a metric `gᵢⱼ(x)`. The usual
choices each have a flaw:

- **Symbolic algebra** is exact but needs a computer algebra system.
- **Finite differences** need a step size `h`. Second derivatives lose precision
  like `ε_machine / h²`, so `R` is good to maybe 6 digits.
- **Hand-derived Christoffel symbols** do not scale beyond toy metrics.

A non-Archimedean field gives a fourth way. In the Levi-Civita field an infinitesimal
`ε` is a genuine number, so `g(x + εv)` is a genuine element whose coefficients are
the Taylor coefficients of `g` along `v`. Nothing is approximated except Float
rounding of the coefficients themselves.

## 2. Jets of elementary functions (`Analysis.lean`)

Arithmetic in `FastLC` already propagates Taylor coefficients of polynomials and
rational functions to every order. Before this work, transcendental functions
stopped at first order: `sin(a + bε) = sin a + b cos a · ε`, with `ε²` silently
dropped. That is fine for gradients and wrong for curvature.

`taylorAt derivs x` writes `x = a + δ` (`a` the standard part, `δ` infinitesimal) and
returns `Σₖ derivs[k]/k! · δᵏ`. Each power of `δ` is truncated below `ε^order`, so
long expressions do not explode. Given the closed-form derivatives (`sin`: the
cycle `s, c, −s, −c`; `log`: `(−1)^(k−1)(k−1)!/aᵏ`; `rpow`: falling factorials),
every elementary function is exact through `ε⁴`. Test it with identities whose
higher coefficients are non-trivial: `sin² + cos² = 1` through `ε⁴`, and
`exp(log(a + ε))`, whose `ε²` coefficient must vanish.

## 3. The metric 2-jet

Evaluate the metric at `x + εv`:

```
gᵢⱼ(x + εv) = gᵢⱼ + ε ∂ᵥgᵢⱼ + ε² ½ ∂ᵥ²gᵢⱼ + …
```

Seeding `v = eₖ` gives `∂ₖg` and `∂ₖ²g`. Mixed partials come from **polarization**:
since `c₂(v) = ½ vᵀHv` is a quadratic form,

```
∂ₖ∂ₗ g = c₂(eₖ + eₗ) − c₂(eₖ) − c₂(eₗ)
```

So `1 + n + n(n−1)/2` metric evaluations give the full 2-jet. That is 11 evaluations
for Schwarzschild, each of 16 components. `MetricJet` stores `g`, `g⁻¹`
(Gauss–Jordan with pivoting), `∂g` and `∂∂g` as flat row-major `Tensor`s.

Why not nest two infinitesimals and differentiate Γ directly? Because the jet
approach keeps all tensor algebra in plain Floats. The LC arithmetic only ever sees
the user's metric expression, which keeps the cost predictable.

## 4. From jet to curvature

All closed forms over the jet:

```
Γₗᵢⱼ   = ½ (∂ᵢgⱼₗ + ∂ⱼgᵢₗ − ∂ₗgᵢⱼ)
Γᵏᵢⱼ   = gᵏˡ Γₗᵢⱼ
∂ₘgᵏˡ  = −gᵏᵃ (∂ₘgₐᵦ) gᵝˡ
∂ₘΓᵏᵢⱼ = (∂ₘgᵏˡ) Γₗᵢⱼ + gᵏˡ ½ (∂ₘ∂ᵢgⱼₗ + ∂ₘ∂ⱼgᵢₗ − ∂ₘ∂ₗgᵢⱼ)
Rᵖ_σμν = ∂_μΓᵖ_νσ − ∂_νΓᵖ_μσ + Γᵖ_μλ Γˡ_νσ − Γᵖ_νλ Γˡ_μσ
```

Then Ricci `R_σν = Rᵖ_σρν`, scalar `gˢᵛR_σν`, Einstein, Kretschmann (raise all four
indices of `R_abcd` and contract), and sectional curvature. **Sign conventions** are
the classic place to go wrong. Pin them with a test whose answer you know in closed
form: the unit sphere has `R^θ_φθφ = sin²θ` and `R = 2`.

## 5. Covariant derivatives of fields

A vector field is also written in LC arithmetic, `V : (Fin n → LC) → Fin n → LC`. The
partial `∂ᵢVᵏ` is the `ε¹` coefficient of `V(x + εeᵢ)`, and then
`∇ᵢVᵏ = ∂ᵢVᵏ + ΓᵏᵢⱼVʲ`. Two checks fall out naturally:

- `∇g = 0`: the Levi-Civita connection is metric-compatible. This exercises the
  whole pipeline, including index placement.
- The **Killing equation** `∇₍ᵢVⱼ₎ = 0` for the rotation field `∂_φ` on the sphere.

## 6. Geodesics and parallel transport

RK4 on the first-order system `(x, ẋ)` with `ẍᵏ = −Γᵏᵢⱼẋⁱẋʲ`. Christoffel symbols
need only first derivatives, so `MetricJet.firstOrder?` skips the `ε²` work (4×
fewer metric evaluations in 4D). Tests use conserved quantities, not trajectories:

- `g(ẋ, ẋ)` is constant along any geodesic;
- on the sphere the embedded curve stays in one plane through the origin, a great circle;
- on Schwarzschild, the Killing vectors `∂_t` and `∂_φ` give conserved
  `E = (1 − 2M/r) ṫ` and `L = r² φ̇`.

## 7. Induced metrics, and a second infinitesimal

For an embedding `F : ℝⁿ → ℝᵐ` the metric is `gᵢⱼ = ∂ᵢF · ∂ⱼF`. Those first derivatives
must be computed *inside* LC arithmetic, because the jet code will evaluate `g` at
`x + εv` and read `ε¹` and `ε²`. Using `ε` again would mix the two differentiations.
The trick is a second infinitesimal `δ = ε^(1/1024)`. A term `δᵃεᵇ` has exponent
`−(a/1024 + b)`, so the `δ¹` part (exponents `−1/1024 − b`) never collides with pure
`εᵇ` terms. The exponents are dyadic, so Float sums of them are exact and equal
exponents merge. Check: the induced metric of the unit sphere in ℝ³ equals
`dθ² + sin²θ dφ²` to 1e-12, and its scalar curvature is 2.

## 8. Testing philosophy

Every check compares against a closed form, a symmetry or a conservation law:
quantities the implementation does not compute directly. A mutation test (flip one
sign in `christoffelFirst`) fails half the suite immediately, which shows the suite
can see errors.
