# A guided tour: the Levi-Civita field as working nonstandard analysis

This guide walks through `Analysis`, `NSA`, `Germ` and `Hyperfinite`: what each
computes, why it is correct, and how to rebuild it yourself. It assumes you know
Lean 4 and calculus. No nonstandard analysis is assumed.

## 1. The field

A Levi-Civita number is a formal sum

```
x = Σᵢ aᵢ ε^{qᵢ}      (aᵢ ∈ ℝ, qᵢ ∈ ℝ, and only finitely many qᵢ below any bound)
```

with `ε` a positive infinitesimal and `H = 1/ε`. In `FastLC` a number is an
array of `Term`s `⟨exp, coeff⟩` sorted by `exp` descending. The convention is
`exp = −q`, so `H` is `⟨1, 1⟩`, `1` is `⟨0, 1⟩` and `ε` is `⟨−1, 1⟩`. The first
term is the **leading term**, the dominant one.

### What the implementation is, exactly

`FastLC` stores coefficients *and* exponents as `Float`. Read every claim below
with that in mind (§7 has the full precision model):

* **Exponents are exact rationals.** Every exponent the arithmetic creates is put
  in canonical form by `snapExp`: within `10⁻¹²` of a rational `p/q`
  (`q ≤ 10⁶`) it becomes the correctly rounded Float `p/q`. So `ε^{0.1} · ε^{0.2}`
  is the same term as `ε^{0.3}`, `ε^{1/3}` cubed is `ε`, and `x − x` is `0`.
  Without this, two computations of one exponent could differ in the last bit
  and leave a pair of uncancelled terms side by side.
* **Coefficients are Floats.** Sums of products round as Float arithmetic does.
  "Exact" below means *exact up to Float rounding of the coefficients*: the right
  terms, with the right coefficients to working precision, and no term that the
  computation does not determine.
* **Series are truncated honestly.** Every power series (inverse, roots, the
  elementary functions) is cut at a stated valuation, and each function returns
  only terms below that cut. A term it cannot get right is dropped, never
  returned with a partial coefficient.

Three facts make this a good setting for analysis.

1. **It is an ordered field.** The sign of `x` is the sign of its leading
   coefficient. Every positive real is larger than every positive power of `ε`,
   and `H` is larger than every real. So the field is non-Archimedean: no
   integer multiple of `ε` reaches `1`.
2. **It is real closed.** Every positive element has a square root, and every
   odd-degree polynomial has a root. Real-closed fields are elementarily
   equivalent to `ℝ` in the language of ordered fields (Tarski). Any first-order
   statement built from `+ × < = ∀ ∃` is true in `ℝ` iff it is true here. That
   is the **transfer principle** for this fragment, and it is what lets us read
   off real answers from computations with `ε`.
3. **It is Cauchy complete** in its order topology, and it is the smallest field
   with these properties. Ultrapower hyperreals are huge and non-constructive.
   This field is small enough to compute in.

## 2. `Analysis`: the field operations

### Order

```lean
def signum (x : LC) : Int        -- sign of the leading coefficient
instance : LT LC := ⟨fun x y => signum (y - x) > 0⟩
```

`max (1 + ε) (1 + 2ε) = 1 + 2ε`: when the standard parts tie, the infinitesimal
parts decide. This one line is why the ray tracer's normals behave at creases
(§4).

**Valuation.** `ν(x) = −(exponent of the leading term)`, so `ν(ε) = 1`, `ν(1) = 0`
and `ν(H) = −1`. It turns products into sums (`ν(xy) = ν(x) + ν(y)`), which is
how all the precision bookkeeping works.

### Division and roots: split off the leading monomial

Every nonzero `x` factors as

```
x = l · (1 + δ),   l = leading term (a monomial),   ν(δ) > 0
```

(`splitLead?`). Monomials are easy: `(c ε^q)^p = c^p ε^{qp}`. The rest is a power
series in the infinitesimal `δ`:

```
1/x   = l⁻¹ · Σ (−δ)ᵏ
x^p   = l^p · Σ C(p, k) δᵏ          (x > 0, any real p)
```

`seriesTo c δ prec` sums `Σ c(k) δᵏ` and stops when `δᵏ` passes valuation `prec`.
After every multiplication it also drops terms beyond `prec`. Multiplying by `δ`
only raises valuations, so a dropped term could never have come back. The result
is exact for every term below `prec`.

Compare `Fast.invert` (what `x⁻¹` and `/` use), which always sums 10 powers. That
is too many when `ν(δ) = 1` and you need first order, and too few when
`ν(δ) = 0.01`. It now keeps only the terms of relative valuation `< 10 · ν(δ)`,
the ones those 10 powers determine. Precision measured in valuation is the right
unit.

If `ν(δ)` is so small that `prec / ν(δ)` exceeds `maxTerms` (64), `seriesTo` cuts
its result at `64 · ν(δ)` instead of returning a sum that is wrong beyond it.

What falls out:

| expression | value |
|---|---|
| `rpow (H + 1) (1/3)` | `H^{1/3} + ⅓ H^{−2/3} − ⅑ H^{−5/3} + …` |
| `root 3 (−ε)` | `−ε^{1/3}` |
| `sqrt ε` | `ε^{1/2}`, and `√ε · √ε == ε` exactly |
| `root 3 (−8 + ε)` | `−2 + ε/12 + …` (the derivative of `∛x` at `−8` is `1/12`) |

### Transcendental functions: Taylor germs

`sin (a + δ)` for finite `a + δ` is `Σ sin⁽ᵏ⁾(a) δᵏ / k!` (`taylorSeries`), and
every term of valuation `< 5` is exact. The number of Taylor terms adapts to
`ν(δ)`: `sin (a + ε)` needs 5 (through `ε⁴`), `sin √ε` needs 10 and comes out
exact through `ε^{9/2}`. `sin`, `cos`, `exp`, `log`, `sinh`, `cosh` and `atan`
generate their Taylor coefficients in closed form for any `k`, so the precision
is a parameter (`jetOrder`), not a hard-coded number of derivatives. For an infinite argument there is no such element: `sin H` would
need to "know" `sin` at an infinite point, and no Levi-Civita number does. So
the result is `undefined`, a NaN standard part, and `st?` reports `none`. The
same goes for `log ε`: `log ε = −log H` is infinite but not a power series in `ε`.

## 3. `NSA`: definitions you can run

### Standard part

Every finite `x` is infinitely close to exactly one real, the ε⁰ coefficient.
`st? x` returns it, or `none` when `x` is infinite or undefined. Use it, not
`std`: `std H = 0` is meaningless.

### Natural extensions via a type class

In Robinson's framework every real function `f` has an extension `*f` to the
hyperreals. Here the extension comes from writing `f` once, generically:

```lean
class RealLike (α : Type) extends Add α, Sub α, Mul α, Neg α, Div α where
  ofFloat : Float → α
  inv sqrt abs exp log sin cos : α → α
  max min : α → α → α
  lt : α → α → Bool

structure Ext where
  run : {α : Type} → [RealLike α] → α → α
```

`F.run (α := Float)` is `f` and `F.run (α := LC)` is `*f`. `Ext.extendsStd`
checks the defining property: `*f` maps reals to reals and agrees with `f` there.

The extension also has the same **domain**. `FastLC` itself is total, with the
usual conventions `x⁻¹ = 0` at `0` and `sqrt = 0` below `0`. Inside `RealLike LC`,
`inv`, `/` and `sqrt` instead return `undefined` exactly where Float gives `∞` or
NaN, and `undefined` propagates (`0 · undefined` is undefined, as `0 · NaN` is NaN).
So `st? (*f x)` is `none` exactly where `f x` is not a real number, and
`extendsStd` checks that too.

### The classical definitions, nonstandard style

| notion | nonstandard definition | `Ext` method |
|---|---|---|
| right limit at `x` | `st *f(x + δ)`, `δ > 0` infinitesimal | `limitRight?` |
| limit at `x` | both one-sided ones exist and agree | `limit?` |
| limit at `∞` | `st *f(N)`, `N` infinite | `limitAtInfinity?` |
| continuity | `*f(x + δ) ≈ f(x)` for infinitesimal `δ` | `continuousAt` |
| derivative | `st ((*f(x+δ) − f(x))/δ)`, the same for all `δ ≠ 0` | `deriv?` |
| second derivative | `st ((*f(x+δ) − 2f(x) + *f(x−δ))/δ²)` | `deriv2?` |

The quantifier "for all infinitesimal `δ`" is replaced by the witnesses `δ = ±ε`.
Why is that enough here? Functions built from field operations, roots, the order
and Taylor germs are piecewise analytic. The leading behaviour of `*f(x + δ)` then
depends only on the sign of `δ`, not its size. Outside that class (`sin (1/x)`,
say), the witnesses still detect non-existence: `sin (1/ε)` is undefined, so
`limit?` is `none`.

The same rule makes some answers *conservative*. `x² sin (1/x)` is differentiable
at `0` with derivative `0`, but `sin H` is not an element of the field, so
`deriv?` returns `none` there. A `none` means "could not be decided from the
witnesses", and a `some` is the derivative (or limit). Likewise `atan H` has no
Taylor germ, so `limitAtInfinity?` of `atan` is `none`, not `π/2`.

Each row is a few lines of code. For example:

```lean
def deriv? (F : Ext) (x : Float) (tol := 1e-9) : Option Float := do
  let fx := F.star (ofFloat x)
  let q (δ : LC) := st? ((F.star (ofFloat x + δ) - fx) / δ)
  let r ← q epsilon
  let l ← q (-epsilon)
  if close r l tol then some r else none
```

`|x|` at `0` gives quotients `+1` and `−1`, so `none`. `√x` at `0` gives
`ε^{1/2}/ε = H^{1/2}`, which is infinite, so `none`. `x³ − 2x` at `1.5` gives
`4.75`.

**Why the cancellation in `*f(x+ε) − f(x)` is exact.** The ε⁰ coefficient of a
product of finite elements comes only from the ε⁰ × ε⁰ pair. The inverse's ε⁰
coefficient is `1/a` and the root's is `√a`, so the standard part of `*f(x + ε)`
goes through the same Float operations as `f(x)`. The difference has no standard
part left, and the quotient is finite.

## 4. Gradients: one evaluation, `n` infinitesimal scales

Dual numbers have one `ε` with `ε² = 0`. A gradient then needs `n` independent
duals, or `n` evaluations. The Levi-Civita field has a whole continuum of
infinitesimal scales, so `valueAndGrad` seeds coordinate `i` at scale `ε^{eᵢ}`
with `eᵢ = 1 + i/n`:

```
f(x + Σᵢ ε^{eᵢ} eᵢ) = f(x) + Σᵢ ∂ᵢf(x) ε^{eᵢ} + (valuation ≥ 2)
```

The exponents `eᵢ` are distinct and lie in `[1, 2)`. Any product of two seeds has
`eᵢ + eⱼ ≥ 2`, so it never lands on a first-order slot.

**Creases.** The order compares `ε` before `ε^{1+1/n}` before `ε^{1+2/n}` and so
on, so ties are broken lexicographically by `∂₀`, then `∂₁`, …. At a crease of
`max`/`min`/`abs`, every branch decision uses the same rule. The result is the
gradient of one smooth piece, the one active just off `x` in the lexicographic
direction. This is Nesterov's *lexicographic derivative*, which nonsmooth
optimisation uses for exactly this reason. Contrast `partialAt`, one seed per
coordinate. For `max(x, y)` at `x = y` its partials are `1` and `1`, the
gradient of no piece. `valueAndGrad` gives `(1, 0)`.

### `Germ`: making it cheap

Full arithmetic also drags along every term of valuation `≥ 2`. Among *finite*
elements those terms form an ideal: finite times valuation-`≥ 2` is still
valuation `≥ 2`. So "drop them" (`Germ.cut`) is a ring homomorphism, and
truncating after every operation gives exactly the coefficients that survive.
A germ is at most `n + 1` terms long. RayTrace4D evaluates every surface normal
this way.

The precondition is *finite*. If a denominator or root argument has an
infinitesimal standard part (`√` at `0`), the computation leaves the finite
elements, and both the truncation and the classical gradient stop making sense.

## 5. `Hyperfinite`: the integral as a sum with `H` terms

The nonstandard integral is `∫ₐᵇ f = st Σ_{k<N} f(a + kh) h`, with `N` infinite
and `h = (b − a)/N`. You can't loop to `H`. For a polynomial `f`, though, expand
`f(a + kh)` in powers of `k` and sum each power in closed form (Faulhaber):

```
Σ_{k<N} kᵐ = (1/(m+1)) Σ_{j≤m} C(m+1, j) Bⱼ N^{m+1−j}       (B₁ = −½)
```

This is a polynomial identity in `N`, true for every standard `N`. By transfer
it is true at `N = H`, so `riemannSum` evaluates it there. Every `H^{m+1}` meets
an `h^{m+1} = ((b−a)ε)^{m+1}`, so the result is finite:

```
riemannSum (x²) 0 1 H       = 1/3 − ½ ε + ⅙ ε²
riemannSum (x²) 0 1 H (θ=½) = 1/3 − 1/12 ε²
```

The standard part is the integral. The tail is the **exact** error expansion of
the rule, so Euler–Maclaurin is a computation, not a derivation. For the left
rule the ε coefficient is `−(b−a)(f(b) − f(a))/2`, and the midpoint rule has no
ε term and an ε² coefficient of `−(b−a)²(f'(b) − f'(a))/24`. `lake test` checks
both, and checks the transfer itself: at `N = 37` the closed form equals the
plain 37-term sum.

The trapezoid rule (`trapezoidSum`, the mean of the left and right sums) has no
ε term and an ε² coefficient of `+(b−a)²(f'(b) − f'(a))/12`, twice the midpoint
rule's with the opposite sign. That is why Simpson's `⅔ midpoint + ⅓ trapezoid`
cancels the ε² term.

## 6. How it is tested

`lake test` runs about a hundred checks in two groups.

* **Closed forms** (`tests/Main.lean`): Taylor coefficients, field identities,
  classical limits and derivatives, Euler–Maclaurin coefficients, and regression
  checks for the precision model (`sin √ε` through `ε^{9/2}`, canonical exponents,
  domains of natural extensions).
* **Randomized properties** (`tests/Properties.lean`, deterministic seeds).
  Elements with dyadic coefficients and exponents in thirds, quarters and sixths,
  so the ring axioms must hold *exactly*: commutativity, associativity,
  distributivity, `a − a = 0`. The order axioms are checked on pairs that tie in
  the standard part. `st` and `ν` are checked as a homomorphism and a valuation.
  Inverse and roots are checked against `a · a⁻¹ = 1` and `(a^{1/3})³ = a`, and
  `invert` against `invertTo`. Random expression trees built from `+ − ×`,
  `sin`, `cos`, `exp`, `atan`, `√(1 + u²)` and `1/(2 + u²)` are differentiated by
  `deriv?`, `deriv2?`, `derivs`, `FastLC.grad` and `Germ.grad`. Each result is
  compared with a second-order forward-mode jet over plain Float, which shares
  no code with the Levi-Civita implementation.

The randomized checks were mutation-tested: turning off `snapExp` fails the
associativity, exponent, inverse and root properties, and returning `invert`'s
untruncated sum fails the `invert`/`invertTo` agreement.

## 7. Precision model

Three sources of error, in decreasing order of importance:

1. **Float rounding of coefficients.** A coefficient is as accurate as the Float
   computation that produced it. Series with large ratios between terms
   (`1/(1 − 6ε^{1/6})` has coefficients `6ᵏ`) lose absolute accuracy in the
   high-valuation terms, just as the Float series would. A cancellation that is
   exact in ℝ can leave a `10⁻¹⁶`-sized coefficient, and the order then treats it
   as genuine: `ofFloat 0.1 * 3 - 0.3` is a positive real, as it is in Float.
   Derivatives avoid this because `*f(x + ε)` computes its standard part with the
   same Float operations as `f(x)` (§3), so that cancellation is exact.
2. **Truncation.** Every series stops at a stated valuation (`prec`, `jetOrder`,
   `10 · ν(δ)` for `invert`, `64 · ν(δ)` for a capped series) and returns only the
   terms below it.
3. **Exponents.** Exact rationals with denominator up to `10⁶` (see §1). An
   exponent that is not within `10⁻¹²` of such a rational is kept as computed.

## 8. Exercises

1. Make `limitAtInfinity?` work for `exp (−x)`. You will need a decision: `exp (−H)`
   is a positive infinitesimal smaller than every `ε^q`, so it is *not* in the
   field. Return `0` as a standard part without constructing the element?
2. Give `atan` an asymptotic expansion at infinity (`atan x = π/2 − 1/x + 1/(3x³) − …`
   for `x > 0` infinite) so that `limitAtInfinity?` of `atan` is `π/2`.
3. Add Simpson's rule to `Hyperfinite` and check that its error starts at `ε⁴`.
4. Prove (in `Core`, over `Rat`) that `cut` is multiplicative on finite
   elements: the algebraic fact the `Germ` docstring relies on.
