import LeviCivita.Fast

/-!
# Ordered-field analysis on `FastLC`

The Levi-Civita field is a real-closed ordered field: every element has a sign
(the sign of its leading term), and every positive element has a square root.
This module exposes that structure for the Float-coefficient implementation
`FastLC`, which is what non-smooth geometric code (signed distance functions,
ray marchers, collision tests) needs:

* `signum`, `abs`, a decidable `<`/`≤`, `max`, `min`: the order compares the
  leading term of the difference, so `max (1 + ε) (1 + 2ε) = 1 + 2ε` — ties in
  the standard part are broken by the infinitesimal part. Applied to a seed
  `x + ε·v`, this makes `max`/`min`/`abs` return the *one-sided directional
  derivative* along `v` instead of an arbitrary subgradient.
* Field operations with adaptive precision: `x = l (1 + δ)` splits off the leading
  monomial `l`, and `invertTo`/`div?`, `rpow` (any real power of a positive
  element, finite or infinite), `sqrt` and `root` (odd roots of negatives too) are
  `l`'s power times a series in the infinitesimal `δ`, summed until its terms pass
  a requested valuation. `sqrt (bε)` is `√b · ε^{1/2}`, so a kink in a distance
  function shows up as a fractional exponent rather than a NaN.
* `valuation?`, the field's valuation `ν` (`ν(ε) = 1`, `ν(H) = −1`).
* `grad`/`valueAndGrad`: the exact gradient of `f : (Fin n → LC) → LC` from **one**
  evaluation, with coordinate `i` seeded at its own infinitesimal scale `ε^{1+i/n}`
  (see `valueAndGrad` for why this is lexicographic differentiation).
* Exact Taylor germs of `exp`, `log`, `sinh`, `cosh`, `tan` (and `sin`, `cos` in
  `Fast`): `f(a + ε)` carries `f(a), f'(a), f''(a)/2, …` through `ε⁴`.

`LeviCivita.NSA` builds standard parts, limits, continuity and derivatives on top
of this; `LeviCivita.Germ` is the truncated arithmetic that makes `grad` cheap.
-/

namespace LeviCivita.Fast.FastLC

instance : BEq LC := ⟨fun a b => a.terms == b.terms⟩

/-- The dominant term (largest exponent), if the number is nonzero. -/
@[inline] def lead? (x : LC) : Option Term := x.terms[0]?

/-- Sign of the leading term: `1`, `-1` or `0`. -/
@[inline] def signum (x : LC) : Int :=
  match lead? x with
  | some t => if t.coeff > 0.0 then 1 else if t.coeff < 0.0 then -1 else 0
  | none => 0

/-- Absolute value in the ordered field. -/
@[inline] def abs (x : LC) : LC := if signum x < 0 then -x else x

/-- `x < y` iff `y - x` is positive. -/
instance : LT LC := ⟨fun x y => signum (y - x) > 0⟩
/-- `x ≤ y` iff `y - x` is not negative. -/
instance : LE LC := ⟨fun x y => signum (y - x) ≥ 0⟩

instance (x y : LC) : Decidable (x < y) :=
  inferInstanceAs (Decidable (signum (y - x) > 0))
instance (x y : LC) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (signum (y - x) ≥ 0))

instance : Max LC := ⟨fun x y => if x < y then y else x⟩
instance : Min LC := ⟨fun x y => if y < x then y else x⟩

/-- Scale by a Float. -/
@[inline] def smul (c : Float) (x : LC) : LC :=
  if c == 0.0 then 0 else { terms := x.terms.map fun t => ⟨t.exp, c * t.coeff⟩ }

/-- Drop every term with exponent below `minExp`. Forward-mode AD only needs
terms down to `ε¹` (exponent `-1`); truncating keeps arrays short in long
expressions without changing those coefficients. -/
@[inline] def truncBelow (minExp : Float) (x : LC) : LC :=
  { terms := x.terms.filter (·.exp ≥ minExp) }

/-- The valuation `ν(x)`: minus the exponent of the leading term, so `ν(ε) = 1`,
`ν(3) = 0`, `ν(H) = −1`, `ν(√ε) = ½`. `none` for zero (whose valuation is `∞`). -/
@[inline] def valuation? (x : LC) : Option Float := (lead? x).map (- ·.exp)

/-- `x = l (1 + δ)`: the leading term `l` and the relative remainder `δ`, which is
infinitesimal (`ν(δ) > 0`). `none` for zero. Every power, root and inverse below is
`l`'s (a monomial, computed exactly) times a power series in `δ`. -/
def splitLead? (x : LC) : Option (Term × LC) := do
  let l ← lead? x
  let lInv : LC := { terms := #[⟨-l.exp, 1.0 / l.coeff⟩] }
  some (l, (x - { terms := #[l] }) * lInv)

/-- `Σₖ c(k) δᵏ` for an infinitesimal `δ`, exact for every term of valuation
`< prec`: each power `δᵏ` is truncated at `prec` (terms beyond it cannot come back,
since multiplying by `δ` only raises valuations), and the sum stops when `δᵏ` is
gone. Capped at `maxTerms` powers (reached only when `ν(δ)` is tiny). -/
def seriesTo (c : Nat → Float) (delta : LC) (prec : Float) (maxTerms : Nat := 64) : LC := Id.run do
  let keep (y : LC) : LC := { terms := y.terms.filter (- ·.exp < prec) }
  let mut acc : LC := keep (ofFloat (c 0))
  let mut pow : LC := 1
  for k in [1:maxTerms] do
    pow := keep (pow * delta)
    if pow.terms.isEmpty then break
    acc := acc + smul (c k) pow
  return acc

/-- Generalized binomial coefficient `C(p, k) = p (p−1) ⋯ (p−k+1) / k!`. -/
def binom (p : Float) (k : Nat) : Float :=
  (List.range k).foldl (fun acc i => acc * (p - i.toFloat) / (i + 1).toFloat) 1.0

/-- `1/x` with relative precision `prec`: `x = l (1 + δ)` gives
`l⁻¹ Σ (−δ)ᵏ`, exact for every term up to valuation `ν(l⁻¹) + prec`. Unlike the
fixed-length series of `invert`, the number of terms adapts to `ν(δ)`. `none` for
zero. -/
def invertTo (x : LC) (prec : Float := 8) : Option LC := do
  let (l, δ) ← splitLead? x
  some ({ terms := #[⟨-l.exp, 1.0 / l.coeff⟩] } *
    seriesTo (fun k => if k % 2 == 0 then 1.0 else -1.0) δ prec)

/-- `x / y`, or `none` when `y = 0` (see `invertTo`). -/
def div? (x y : LC) (prec : Float := 8) : Option LC := (invertTo y prec).map (x * ·)

/-- Real power `x^p` of a positive element, finite or not, with relative precision
`prec` (default: exact through `ε⁴` relative to the leading term). With
`x = c εᵉ (1 + δ)`, `x^p = c^p ε^{ep} Σₖ C(p, k) δᵏ`. So `(ε)^½ = ε^{1/2}`,
`(H + 1)^{1/3} = H^{1/3} + ⅓ H^{−2/3} − …`, and `(a + ε)^p` carries
`a^p, p a^{p−1}, …` exactly. Nonpositive input gives `0`, as a total function:
callers that care test `signum` first. -/
def rpow (x : LC) (p : Float) (prec : Float := 5) : LC :=
  match splitLead? x with
  | some (l, δ) =>
    if l.coeff ≤ 0.0 then 0
    else { terms := #[⟨l.exp * p, Float.pow l.coeff p⟩] } * seriesTo (binom p) δ prec
  | none => 0

/-- Square root (`rpow x ½`): `√(a + bε) = √a + (b / 2√a) ε + …`, and `√(bε) = √b ε^{1/2}`,
so a kink in a distance function shows up as a fractional exponent rather than a
NaN. `0` for negative input. -/
def sqrt (x : LC) (prec : Float := 5) : LC := rpow x 0.5 prec

/-- The real `n`-th root: `rpow x (1/n)`, extended to negative `x` for odd `n`
(`∛(−ε) = −ε^{1/3}`). `0` for negative `x` and even `n`, and for `n = 0`. -/
def root (n : Nat) (x : LC) (prec : Float := 5) : LC :=
  if n == 0 then 0
  else if signum x < 0 then (if n % 2 == 1 then -rpow (-x) (1.0 / n.toFloat) prec else 0)
  else rpow x (1.0 / n.toFloat) prec

/-- Euclidean norm of a coordinate tuple. -/
def norm {n : Nat} (v : Fin n → LC) : LC :=
  sqrt ((List.finRange n).foldl (fun acc i => acc + v i * v i) 0)

/-- The infinitesimal scale of coordinate `i` of `n` in a one-pass gradient:
`ε^{eᵢ}` with `eᵢ = 1 + i/n ∈ [1, 2)`. Distinct exponents keep the coordinates
apart, and any product of two of them has exponent `≥ 2`, beyond every `eⱼ`, so it
never lands on a first-order coefficient. -/
@[inline] def seedExp (n i : Nat) : Float := 1.0 + i.toFloat / n.toFloat

/-- Value and exact gradient of `f` at `x` in **one** evaluation: coordinate `i`
is seeded as `xᵢ + ε^{eᵢ}` (`seedExp`), and `∂ᵢf` is the coefficient of `ε^{eᵢ}`
in `f (x + Σᵢ ε^{eᵢ} eᵢ)`.

This is the Levi-Civita field doing what dual numbers cannot: the `n` directions
live at `n` different infinitesimal scales of one ε. The order of the field is
then lexicographic in the directions (`ε ≫ ε^{5/4} ≫ ε^{3/2} ≫ …`), so where
`max`, `min` or `abs` meet a tie (a crease of a distance function), every
comparison is decided by the same rule: first `∂₀`, then `∂₁`, and so on. The
result is the gradient of the one smooth piece that is active on the
lexicographic side of `x` (Nesterov's *lexicographic derivative*), never a mix of
pieces from different coordinates. Exact up to Float rounding for any `f` built
from field operations, roots and the elementary functions below, provided no
denominator or root argument is infinitesimal at `x`. -/
def valueAndGrad {n : Nat} (f : (Fin n → LC) → LC) (x : Fin n → Float) :
    Float × Array Float :=
  let y := f fun i => ofFloat (x i) + { terms := #[⟨-seedExp n i.val, 1.0⟩] }
  (std y, (List.finRange n).toArray.map fun i => getCoeff y (-seedExp n i.val))

/-- Exact gradient of `f` at `x` (see `valueAndGrad`). -/
def grad {n : Nat} (f : (Fin n → LC) → LC) (x : Fin n → Float) : Array Float :=
  (valueAndGrad f x).2

/-- Partial derivative `∂ᵢf(x)` alone, from the single seed `xᵢ + ε`. Away from
creases this agrees with `grad`; at a crease it is the one-sided derivative along
`+eᵢ`, so stacking `n` of them can mix pieces (which `grad` never does). -/
def partialAt {n : Nat} (f : (Fin n → LC) → LC) (x : Fin n → Float) (i : Fin n) : Float :=
  getCoeff (f fun j => if j == i then ofFloat (x j) + epsilon else ofFloat (x j)) (-1.0)

/-! ## Elementary functions as exact jets

Each is `taylorAt` with the closed-form derivatives at the standard part, so a
seed `a + ε` yields `f(a), f'(a), f''(a)/2, …` exactly through `ε⁴`. They are
defined on finite elements (and `log` on positive elements of valuation 0); outside
that, `exp H` or `log ε` is not an element of the field, and the result is
`undefined`. -/

/-- `exp`, exact through `ε⁴`. -/
def exp (x : LC) : LC :=
  let e := Float.exp (std x)
  taylorAt (Array.replicate jetOrder e) x

/-- Natural log of a positive finite element, exact through `ε⁴`:
`log⁽ᵏ⁾(a) = (−1)^(k−1) (k−1)! / aᵏ`. -/
def log (x : LC) : LC :=
  let a := std x
  if valuation? x != some 0.0 || a ≤ 0.0 then undefined else
  taylorAt (Array.ofFn (n := jetOrder) fun k =>
    if k.val == 0 then Float.log a
    else
      let m := k.val - 1
      let fact := (List.range m).foldl (fun acc i => acc * (i + 1).toFloat) 1.0
      (if m % 2 == 0 then 1.0 else -1.0) * fact / Float.pow a k.val.toFloat) x

/-- `sinh`, exact through `ε⁴`. -/
def sinh (x : LC) : LC :=
  let a := std x
  taylorAt (Array.ofFn (n := jetOrder) fun k =>
    if k.val % 2 == 0 then Float.sinh a else Float.cosh a) x

/-- `cosh`, exact through `ε⁴`. -/
def cosh (x : LC) : LC :=
  let a := std x
  taylorAt (Array.ofFn (n := jetOrder) fun k =>
    if k.val % 2 == 0 then Float.cosh a else Float.sinh a) x

/-- `tan = sin / cos`. -/
def tan (x : LC) : LC := sin x / cos x

/-- Coefficient of `εᵏ` (exponent `−k`). -/
@[inline] def epsCoeff (x : LC) (k : Nat) : Float := getCoeff x (-k.toFloat)

end LeviCivita.Fast.FastLC
