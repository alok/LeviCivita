import LeviCivita.Analysis

/-!
# Nonstandard analysis in the Levi-Civita field

The Levi-Civita field `R` is a real-closed, non-Archimedean ordered field that
contains `ℝ` (here: `Float`) together with the infinitesimal `ε` and the infinite
`H = 1/ε`. Elements are classified by their leading term:

| | leading exponent of ε | examples |
|---|---|---|
| infinitesimal | `> 0` (or the element is `0`) | `ε`, `−3ε²`, `ε^{1/2}` |
| finite (limited) | `≥ 0` | `2 + ε`, `ε` |
| appreciable | `= 0` | `2 + ε` |
| infinite | `< 0` | `H`, `H − 7` |

Every finite `x` is infinitely close to exactly one real number, its **standard
part** `st x` (`st?` here, `none` for infinite or undefined elements).

## Transfer

The classical tool is the *natural extension*: a real function `f` extends to
`*f` on the bigger field, and statements about `f` transfer to `*f`. Here a
function is written once over the class `RealLike`. At `α = Float` it is `f`;
at `α = LC` it is `*f`. That holds exactly for anything built from the
ordered-field operations and roots, because the Levi-Civita field is real closed
and so elementarily equivalent to `ℝ` for that language. The elementary
transcendental functions extend to the finite elements through their Taylor
germs (`exp`, `sin`, … in `Analysis`).

An `Ext` packages such a function. Its nonstandard characterizations become
computations:

| classical notion | nonstandard definition | here |
|---|---|---|
| `lim_{t→x⁺} f t` | `st *f(x + δ)`, `δ > 0` infinitesimal | `limitRight?` (δ = ε) |
| `lim_{t→∞} f t` | `st *f(N)`, `N` infinite | `limitAtInfinity?` (N = H) |
| continuity at `x` | `*f(x + δ) ≈ f(x)` for all infinitesimal `δ` | `continuousAt` (δ = ±ε) |
| `f'(x)` | `st ((*f(x + δ) − f(x)) / δ)`, the same for all `δ ≠ 0` | `deriv?` (δ = ±ε) |

These checks use the witnesses `±ε`, not every infinitesimal. For functions built
from field operations, roots, order comparisons and the elementary functions,
the left and right witnesses are enough: such functions are piecewise analytic,
so `*f(x + δ)` has the same leading behaviour for every `δ` of a fixed sign.
-/

namespace LeviCivita.Fast.FastLC

/-- `x` is infinitesimal: every term has a negative exponent (a positive power of
`ε`). `0` is infinitesimal. -/
@[inline] def isInfinitesimal (x : LC) : Bool := x.terms.all (·.exp < 0.0)

/-- `x` is finite (limited): no term is a positive power of `H`. -/
@[inline] def isFinite (x : LC) : Bool := x.terms.all (·.exp ≤ 0.0)

/-- `x` is infinite: larger in absolute value than every real. -/
@[inline] def isInfinite (x : LC) : Bool := !isFinite x

/-- `x` is appreciable: finite and not infinitesimal. -/
@[inline] def isAppreciable (x : LC) : Bool := isFinite x && !isInfinitesimal x

/-- `x` is a real number (its only term is `ε⁰`, or it is `0`). -/
@[inline] def isStandard (x : LC) : Bool := x.terms.all (·.exp == 0.0)

/-- No coefficient is NaN (see `undefined`). -/
@[inline] def isDefined (x : LC) : Bool := x.terms.all fun t => !t.coeff.isNaN

/-- The standard part: the unique real infinitely close to a finite `x`; `none`
for an infinite or undefined `x`. -/
@[inline] def st? (x : LC) : Option Float :=
  if isFinite x && isDefined x then some (std x) else none

/-- `x ≈ y`: the difference is infinitesimal. -/
@[inline] def infinitelyClose (x y : LC) : Bool := isInfinitesimal (x - y)

end LeviCivita.Fast.FastLC

namespace LeviCivita

open Fast FastLC

/-- The operations a function needs so it can be evaluated on reals (`Float`)
and on Levi-Civita numbers alike; see "Transfer" in the module docs. -/
class RealLike (α : Type) extends Add α, Sub α, Mul α, Neg α, Div α where
  /-- Embed a real. -/
  ofFloat : Float → α
  /-- Multiplicative inverse. -/
  inv : α → α
  /-- Square root (`0` for negative elements of the field, NaN for negative Floats). -/
  sqrt : α → α
  /-- Absolute value. -/
  abs : α → α
  /-- Maximum in the order. -/
  max : α → α → α
  /-- Minimum in the order. -/
  min : α → α → α
  /-- Strict order, decided. -/
  lt : α → α → Bool
  /-- Exponential. -/
  exp : α → α
  /-- Natural logarithm. -/
  log : α → α
  /-- Sine. -/
  sin : α → α
  /-- Cosine. -/
  cos : α → α

instance : RealLike Float where
  ofFloat x := x
  inv x := 1.0 / x
  sqrt := Float.sqrt
  abs := Float.abs
  max := Max.max
  min := Min.min
  lt a b := a < b
  exp := Float.exp
  log := Float.log
  sin := Float.sin
  cos := Float.cos

instance : RealLike LC where
  ofFloat := FastLC.ofFloat
  inv x := x⁻¹
  sqrt x := FastLC.sqrt x
  abs := FastLC.abs
  max := Max.max
  min := Min.min
  lt a b := decide (a < b)
  exp := FastLC.exp
  log := FastLC.log
  sin := FastLC.sin
  cos := FastLC.cos

/-- A real function together with its natural extension: `run` at `Float` is
`f`, at `LC` it is `*f`. Build one as `⟨fun x => x * x - RealLike.ofFloat 2⟩`. -/
structure Ext where
  /-- The function, for every `RealLike` scalar. -/
  run : {α : Type} → [RealLike α] → α → α

namespace Ext

/-- The standard function `f`. -/
@[inline] def std (F : Ext) (x : Float) : Float := F.run x

/-- The natural extension `*f`. -/
@[inline] def star (F : Ext) (x : LC) : LC := F.run x

/-- Relative closeness of two reals. -/
@[inline] def close (a b : Float) (tol : Float) : Bool :=
  (a - b).abs ≤ tol * (1.0 + a.abs + b.abs)

/-- `*f` agrees with `f` on the given reals and maps them to reals: the
defining property of a natural extension, checked pointwise. -/
def extendsStd (F : Ext) (xs : List Float) (tol : Float := 1e-12) : Bool :=
  xs.all fun x =>
    let y := F.star (FastLC.ofFloat x)
    isStandard y && isDefined y && close (FastLC.std y) (F.std x) tol

/-- `lim_{t→x⁺} f t = st *f(x + ε)`. -/
def limitRight? (F : Ext) (x : Float) : Option Float := st? (F.star (FastLC.ofFloat x + epsilon))

/-- `lim_{t→x⁻} f t = st *f(x − ε)`. -/
def limitLeft? (F : Ext) (x : Float) : Option Float := st? (F.star (FastLC.ofFloat x - epsilon))

/-- The two-sided limit, when both one-sided limits exist and agree. `f` need not
be defined at `x` itself (`sin t / t` at `0` has limit `1`). -/
def limit? (F : Ext) (x : Float) (tol : Float := 1e-9) : Option Float := do
  let r ← limitRight? F x
  let l ← limitLeft? F x
  if close r l tol then some r else none

/-- `lim_{t→∞} f t = st *f(H)`. -/
def limitAtInfinity? (F : Ext) : Option Float := st? (F.star H)

/-- `lim_{t→−∞} f t = st *f(−H)`. -/
def limitAtNegInfinity? (F : Ext) : Option Float := st? (F.star (-H))

/-- Continuity at `x`: `*f(x ± ε) ≈ f(x)`. -/
def continuousAt (F : Ext) (x : Float) (tol : Float := 1e-9) : Bool :=
  match limit? F x tol with
  | some l => close l (F.std x) tol
  | none => false

/-- The derivative `st ((*f(x + δ) − f(x)) / δ)` for `δ = ±ε`; `none` unless both
quotients are finite and agree (so `|t|` at `0`, with quotients `±1`, and `√t` at
`0`, with an infinite quotient, have none). -/
def deriv? (F : Ext) (x : Float) (tol : Float := 1e-9) : Option Float := do
  let fx := F.star (FastLC.ofFloat x)
  let q (δ : LC) : Option Float := st? ((F.star (FastLC.ofFloat x + δ) - fx) / δ)
  let r ← q epsilon
  let l ← q (-epsilon)
  if close r l tol then some r else none

/-- The second derivative `st ((*f(x + ε) − 2 f(x) + *f(x − ε)) / ε²)`. -/
def deriv2? (F : Ext) (x : Float) : Option Float :=
  let a := FastLC.ofFloat x
  st? ((F.star (a + epsilon) - smul 2.0 (F.star a) + F.star (a - epsilon)) * (H * H))

/-- The derivatives `f(x), f'(x), …, f⁽ᵏ⁾(x)` read off one evaluation of
`*f(x + ε)`: the coefficient of `εʲ` is `f⁽ʲ⁾(x)/j!`. Exact for `k` up to the
germ order of the functions involved (4 for the elementary ones). -/
def derivs (F : Ext) (x : Float) (k : Nat) : Array Float :=
  let y := F.star (FastLC.ofFloat x + epsilon)
  (Array.range (k + 1)).map fun j =>
    epsCoeff y j * (List.range j).foldl (fun acc i => acc * (i + 1).toFloat) 1.0

end Ext

end LeviCivita
