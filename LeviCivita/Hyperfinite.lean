import LeviCivita.NSA

/-!
# Hyperfinite Riemann sums

In nonstandard analysis the integral is a sum: split `[a, b]` into an *infinite*
number `N` of steps of infinitesimal width `h = (b − a)/N`. Then

  `∫ₐᵇ f = st Σ_{k=0}^{N−1} f(a + k h) h`.

`N` is not a natural number of the Levi-Civita field, so the sum cannot be
computed term by term. For a polynomial `f`, though, it has a closed form in `N`.
Expand `f(a + kh)` in powers of `k` and use Faulhaber's formula for
`Σ_{k<N} kᵐ`. That is an identity between polynomials in `N`, true for every
standard `N`, so by transfer it holds for a hyperfinite `N`. Evaluating it at
`N = H` gives an element of the field:

  `Σ_{k<H} f(a + k h) h = ∫ₐᵇ f + c₁ ε + c₂ ε² + …`

Its standard part is the integral. The infinitesimal tail is the exact error of
the rule, so the Euler–Maclaurin coefficients can be read off rather than derived.
For the left rule, `c₁ = −(b − a)(f(b) − f(a))/2`. For the midpoint rule (`θ = ½`)
`c₁ = 0` and `c₂ = −(b − a)²(f'(b) − f'(a))/24`.

At a standard `N` the same closed form must equal the plain finite sum; `lake test`
checks that this is so.
-/

namespace LeviCivita.Hyperfinite

open Fast FastLC

/-- `C(n, k)` for naturals. -/
def choose (n k : Nat) : Nat :=
  if k > n then 0 else (List.range k).foldl (fun acc i => acc * (n - i) / (i + 1)) 1

/-- The Bernoulli numbers `B₀ … B_m` with `B₁ = −½`, exact, from
`Σ_{j≤k} C(k+1, j) Bⱼ = 0`. -/
def bernoulli (m : Nat) : Array Rat := Id.run do
  let mut b : Array Rat := #[1]
  for k in [1:m + 1] do
    let s := (List.range k).foldl (fun acc j => acc + (choose (k + 1) j : Rat) * b[j]!) 0
    b := b.push (-s / (k + 1 : Rat))
  return b

/-- A rational as a Float. -/
@[inline] def ratToFloat (q : Rat) : Float := Float.ofInt q.num / q.den.toFloat

/-- Faulhaber: `Σ_{k=0}^{N−1} kᵐ = (1/(m+1)) Σ_{j≤m} C(m+1, j) Bⱼ N^{m+1−j}`, for
any `N` in the field (a standard count, or a hyperfinite one like `H`). -/
def powerSum (m : Nat) (N : LC) : LC :=
  let B := bernoulli m
  (List.range (m + 1)).foldl (fun acc j =>
    acc + smul (ratToFloat ((choose (m + 1) j : Rat) * B[j]! / (m + 1 : Rat))) (N ^ (m + 1 - j))) 0

/-- A polynomial `c₀ + c₁ x + c₂ x² + …`. -/
structure Poly where
  /-- Coefficients, constant term first. -/
  coeffs : Array Float
  deriving Inhabited, Repr

namespace Poly

/-- Evaluate at a real. -/
def eval (p : Poly) (x : Float) : Float := p.coeffs.foldr (fun c acc => acc * x + c) 0

/-- The derivative. -/
def deriv (p : Poly) : Poly := ⟨(p.coeffs.toList.drop 1).toArray.mapIdx fun i c => (i + 1).toFloat * c⟩

/-- The exact integral over `[a, b]`, from the antiderivative. -/
def integral (p : Poly) (a b : Float) : Float :=
  let F (x : Float) : Float :=
    (p.coeffs.mapIdx fun j c => c * Float.pow x (j + 1).toFloat / (j + 1).toFloat).foldl (· + ·) 0
  F b - F a

end Poly

/-- The Riemann sum `Σ_{k=0}^{N−1} p(a + (k + θ) h) h` with `h = (b − a)/N`, in
closed form, for any `N` (standard or hyperfinite) and any endpoints in the
field. `θ = 0` is the left rule and `θ = ½` the midpoint rule. With
`a' = a + θh`, `p(a' + kh) = Σⱼ cⱼ Σₘ C(j, m) a'^{j−m} hᵐ kᵐ`, and the sum over
`k` is `powerSum`. -/
def riemannSum (p : Poly) (a b N : LC) (θ : Float := 0) : LC :=
  let h := (b - a) / N
  let a' := a + smul θ h
  (List.range p.coeffs.size).foldl (fun acc j =>
    (List.range (j + 1)).foldl (fun acc m =>
      acc + smul (p.coeffs[j]! * (choose j m).toFloat) (a' ^ (j - m) * h ^ (m + 1) * powerSum m N))
      acc) 0

/-- The same sum by brute force, for a standard number of steps. -/
def riemannSumDirect (p : Poly) (a b : Float) (N : Nat) (θ : Float := 0) : Float :=
  let h := (b - a) / N.toFloat
  (List.range N).foldl (fun acc k => acc + p.eval (a + (k.toFloat + θ) * h) * h) 0

/-- `∫ₐᵇ p` as the standard part of the hyperfinite left Riemann sum with `H` steps. -/
def integral (p : Poly) (a b : Float) : Option Float :=
  st? (riemannSum p (FastLC.ofFloat a) (FastLC.ofFloat b) H)

end LeviCivita.Hyperfinite
