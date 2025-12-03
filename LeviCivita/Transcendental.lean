import LeviCivita.Fast

/-!
# Transcendental Functions for Levi-Civita Numbers

LC-aware implementations of exp, log, sin, cos, tan, sqrt, pow, etc.
These properly handle infinitesimal arguments to enable automatic differentiation.

Key insight: For f(a + bε) where a is standard and b is the infinitesimal coefficient:
  f(a + bε) ≈ f(a) + b·f'(a)·ε  (first-order Taylor expansion)

This gives us automatic differentiation "for free" - the coefficient of ε
in f(x + ε) is exactly f'(x).
-/

set_option linter.missingDocs false

namespace LeviCivita.Transcendental

open LeviCivita.Fast

-- Constants not always available in Float
private def nan : Float := 0.0 / 0.0
private def pi : Float := 3.14159265358979323846

/-! ## Exponential and Logarithm -/

/-- Exponential function for LC numbers.
    exp(a + bε) = exp(a) + b·exp(a)·ε = exp(a)·(1 + bε)
    For standard a, infinitesimal bε. -/
def exp (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x                    -- standard part
  let b := FastLC.getCoeff x (-1.0)        -- coefficient of ε
  let expA := Float.exp a
  -- exp(a + bε) = exp(a) · (1 + bε) = exp(a) + b·exp(a)·ε
  FastLC.ofFloat expA + { terms := #[⟨-1.0, b * expA⟩] }

/-- Natural logarithm for LC numbers.
    log(a + bε) = log(a) + (b/a)·ε  for a > 0
    Derivative: d/dx log(x) = 1/x -/
def log (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  if a <= 0.0 then
    FastLC.ofFloat nan  -- log undefined for non-positive
  else
    let logA := Float.log a
    -- log(a + bε) = log(a) + (b/a)·ε
    FastLC.ofFloat logA + { terms := #[⟨-1.0, b / a⟩] }

/-- Base-10 logarithm -/
def log10 (x : FastLC.LC) : FastLC.LC :=
  log x * FastLC.ofFloat (1.0 / Float.log 10.0)

/-- Base-2 logarithm -/
def log2 (x : FastLC.LC) : FastLC.LC :=
  log x * FastLC.ofFloat (1.0 / Float.log 2.0)

/-- Exponential base e, alias for exp -/
def exp1 := exp

/-- Exponential base 2: 2^x -/
def exp2 (x : FastLC.LC) : FastLC.LC :=
  exp (x * FastLC.ofFloat (Float.log 2.0))

/-- Exponential base 10: 10^x -/
def exp10 (x : FastLC.LC) : FastLC.LC :=
  exp (x * FastLC.ofFloat (Float.log 10.0))

/-! ## Trigonometric Functions -/

/-- Sine function for LC numbers.
    sin(a + bε) = sin(a) + b·cos(a)·ε -/
def sin (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let sinA := Float.sin a
  let cosA := Float.cos a
  FastLC.ofFloat sinA + { terms := #[⟨-1.0, b * cosA⟩] }

/-- Cosine function for LC numbers.
    cos(a + bε) = cos(a) - b·sin(a)·ε -/
def cos (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let sinA := Float.sin a
  let cosA := Float.cos a
  FastLC.ofFloat cosA + { terms := #[⟨-1.0, -b * sinA⟩] }

/-- Tangent function for LC numbers.
    tan(a + bε) = tan(a) + b·sec²(a)·ε = tan(a) + b/(cos²(a))·ε -/
def tan (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let cosA := Float.cos a
  if cosA.abs < 1e-10 then
    FastLC.ofFloat nan  -- tan undefined at odd multiples of π/2
  else
    let tanA := Float.tan a
    let sec2A := 1.0 / (cosA * cosA)
    FastLC.ofFloat tanA + { terms := #[⟨-1.0, b * sec2A⟩] }

/-- Cotangent: cot(x) = cos(x)/sin(x) -/
def cot (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let sinA := Float.sin a
  if sinA.abs < 1e-10 then
    FastLC.ofFloat nan
  else
    let cotA := Float.cos a / sinA
    let csc2A := 1.0 / (sinA * sinA)
    FastLC.ofFloat cotA + { terms := #[⟨-1.0, -b * csc2A⟩] }

/-- Secant: sec(x) = 1/cos(x) -/
def sec (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let cosA := Float.cos a
  if cosA.abs < 1e-10 then
    FastLC.ofFloat nan
  else
    let secA := 1.0 / cosA
    let tanA := Float.tan a
    -- d/dx sec(x) = sec(x)·tan(x)
    FastLC.ofFloat secA + { terms := #[⟨-1.0, b * secA * tanA⟩] }

/-- Cosecant: csc(x) = 1/sin(x) -/
def csc (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let sinA := Float.sin a
  if sinA.abs < 1e-10 then
    FastLC.ofFloat nan
  else
    let cscA := 1.0 / sinA
    let cotA := Float.cos a / sinA
    -- d/dx csc(x) = -csc(x)·cot(x)
    FastLC.ofFloat cscA + { terms := #[⟨-1.0, -b * cscA * cotA⟩] }

/-! ## Inverse Trigonometric Functions -/

-- Arcsine: arcsin(x), domain -1 to 1
-- d/dx arcsin(x) = 1/sqrt(1-x^2)
def asin (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  if a.abs > 1.0 then
    FastLC.ofFloat nan
  else
    let asinA := Float.asin a
    let deriv := 1.0 / Float.sqrt (1.0 - a * a)
    FastLC.ofFloat asinA + { terms := #[⟨-1.0, b * deriv⟩] }

-- Arccosine: arccos(x), domain -1 to 1
-- d/dx arccos(x) = -1/sqrt(1-x^2)
def acos (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  if a.abs > 1.0 then
    FastLC.ofFloat nan
  else
    let acosA := Float.acos a
    let deriv := -1.0 / Float.sqrt (1.0 - a * a)
    FastLC.ofFloat acosA + { terms := #[⟨-1.0, b * deriv⟩] }

/-- Arctangent: arctan(x)
    d/dx arctan(x) = 1/(1+x²) -/
def atan (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let atanA := Float.atan a
  let deriv := 1.0 / (1.0 + a * a)
  FastLC.ofFloat atanA + { terms := #[⟨-1.0, b * deriv⟩] }

/-- Two-argument arctangent: atan2(y, x) -/
def atan2 (y x : FastLC.LC) : FastLC.LC :=
  let ya := FastLC.std y
  let xa := FastLC.std x
  let yb := FastLC.getCoeff y (-1.0)
  let xb := FastLC.getCoeff x (-1.0)
  let atan2A := Float.atan2 ya xa
  let r2 := xa * xa + ya * ya
  if r2 < 1e-20 then
    FastLC.ofFloat nan
  else
    -- d/dy atan2(y,x) = x/(x²+y²), d/dx atan2(y,x) = -y/(x²+y²)
    let deriv := (yb * xa - xb * ya) / r2
    FastLC.ofFloat atan2A + { terms := #[⟨-1.0, deriv⟩] }

/-! ## Hyperbolic Functions -/

/-- Hyperbolic sine: sinh(x) = (e^x - e^(-x))/2
    d/dx sinh(x) = cosh(x) -/
def sinh (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let sinhA := Float.sinh a
  let coshA := Float.cosh a
  FastLC.ofFloat sinhA + { terms := #[⟨-1.0, b * coshA⟩] }

/-- Hyperbolic cosine: cosh(x) = (e^x + e^(-x))/2
    d/dx cosh(x) = sinh(x) -/
def cosh (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let sinhA := Float.sinh a
  let coshA := Float.cosh a
  FastLC.ofFloat coshA + { terms := #[⟨-1.0, b * sinhA⟩] }

/-- Hyperbolic tangent: tanh(x) = sinh(x)/cosh(x)
    d/dx tanh(x) = sech²(x) = 1 - tanh²(x) -/
def tanh (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let tanhA := Float.tanh a
  let sech2A := 1.0 - tanhA * tanhA
  FastLC.ofFloat tanhA + { terms := #[⟨-1.0, b * sech2A⟩] }

/-- Hyperbolic cotangent: coth(x) = cosh(x)/sinh(x) -/
def coth (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let sinhA := Float.sinh a
  if sinhA.abs < 1e-10 then
    FastLC.ofFloat nan
  else
    let cothA := Float.cosh a / sinhA
    let csch2A := 1.0 / (sinhA * sinhA)
    FastLC.ofFloat cothA + { terms := #[⟨-1.0, -b * csch2A⟩] }

/-- Hyperbolic secant: sech(x) = 1/cosh(x) -/
def sech (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let coshA := Float.cosh a
  let sechA := 1.0 / coshA
  let tanhA := Float.tanh a
  -- d/dx sech(x) = -sech(x)·tanh(x)
  FastLC.ofFloat sechA + { terms := #[⟨-1.0, -b * sechA * tanhA⟩] }

/-- Hyperbolic cosecant: csch(x) = 1/sinh(x) -/
def csch (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let sinhA := Float.sinh a
  if sinhA.abs < 1e-10 then
    FastLC.ofFloat nan
  else
    let cschA := 1.0 / sinhA
    let cothA := Float.cosh a / sinhA
    -- d/dx csch(x) = -csch(x)·coth(x)
    FastLC.ofFloat cschA + { terms := #[⟨-1.0, -b * cschA * cothA⟩] }

/-! ## Inverse Hyperbolic Functions -/

/-- Inverse hyperbolic sine: asinh(x) = ln(x + √(x²+1))
    d/dx asinh(x) = 1/√(x²+1) -/
def asinh (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let asinhA := Float.log (a + Float.sqrt (a * a + 1.0))
  let deriv := 1.0 / Float.sqrt (a * a + 1.0)
  FastLC.ofFloat asinhA + { terms := #[⟨-1.0, b * deriv⟩] }

/-- Inverse hyperbolic cosine: acosh(x) = ln(x + √(x²-1)), x ≥ 1
    d/dx acosh(x) = 1/√(x²-1) -/
def acosh (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  if a < 1.0 then
    FastLC.ofFloat nan
  else
    let acoshA := Float.log (a + Float.sqrt (a * a - 1.0))
    let deriv := 1.0 / Float.sqrt (a * a - 1.0)
    FastLC.ofFloat acoshA + { terms := #[⟨-1.0, b * deriv⟩] }

/-- Inverse hyperbolic tangent: atanh(x) = ln((1+x)/(1-x))/2, |x| < 1
    d/dx atanh(x) = 1/(1-x²) -/
def atanh (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  if a.abs >= 1.0 then
    FastLC.ofFloat nan
  else
    let atanhA := 0.5 * Float.log ((1.0 + a) / (1.0 - a))
    let deriv := 1.0 / (1.0 - a * a)
    FastLC.ofFloat atanhA + { terms := #[⟨-1.0, b * deriv⟩] }

/-! ## Power and Root Functions -/

/-- Square root: sqrt(x) = x^(1/2)
    d/dx sqrt(x) = 1/(2·sqrt(x)) -/
def sqrt (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  if a < 0.0 then
    FastLC.ofFloat nan
  else if a == 0.0 then
    -- sqrt(bε) for infinitesimal - this is tricky
    -- For now, return 0 (could extend to fractional exponents)
    FastLC.ofFloat 0.0
  else
    let sqrtA := Float.sqrt a
    let deriv := 1.0 / (2.0 * sqrtA)
    FastLC.ofFloat sqrtA + { terms := #[⟨-1.0, b * deriv⟩] }

/-- Cube root: cbrt(x) = x^(1/3)
    d/dx cbrt(x) = 1/(3·x^(2/3)) = 1/(3·cbrt(x)²) -/
def cbrt (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let cbrtA := Float.pow a.abs (1.0/3.0) * (if a < 0.0 then -1.0 else 1.0)
  if a == 0.0 then
    FastLC.ofFloat 0.0
  else
    let deriv := 1.0 / (3.0 * cbrtA * cbrtA)
    FastLC.ofFloat cbrtA + { terms := #[⟨-1.0, b * deriv⟩] }

/-- General power: x^y for LC numbers
    d/dx x^y = y·x^(y-1), d/dy x^y = x^y·ln(x)
    x^(a+bε) = x^a · x^(bε) ≈ x^a · (1 + bε·ln(x)) for small bε -/
def pow (x y : FastLC.LC) : FastLC.LC :=
  let xa := FastLC.std x
  let xb := FastLC.getCoeff x (-1.0)
  let ya := FastLC.std y
  let yb := FastLC.getCoeff y (-1.0)

  if xa <= 0.0 && ya != ya.floor then
    FastLC.ofFloat nan  -- negative base with non-integer exponent
  else if xa == 0.0 then
    if ya > 0.0 then FastLC.ofFloat 0.0
    else if ya == 0.0 then FastLC.ofFloat 1.0  -- 0^0 = 1 convention
    else FastLC.ofFloat nan  -- 0^negative undefined
  else
    let powA := Float.pow xa ya
    -- d/dx x^y · dx + d/dy x^y · dy
    -- = y·x^(y-1)·xb·ε + x^y·ln(x)·yb·ε
    let derivX := ya * Float.pow xa (ya - 1.0) * xb
    let derivY := powA * Float.log xa * yb
    FastLC.ofFloat powA + { terms := #[⟨-1.0, derivX + derivY⟩] }

/-- Integer power (more efficient for integer exponents) -/
def powi (x : FastLC.LC) (n : Int) : FastLC.LC :=
  if n == 0 then FastLC.ofFloat 1.0
  else if n > 0 then x ^ n.toNat
  else (x ^ (-n).toNat)⁻¹

/-! ## Special Functions -/

/-- Absolute value with subgradient at 0
    |a + bε| = |a| + sign(a)·b·ε for a ≠ 0
    At a = 0, derivative is undefined (we use 0) -/
def abs (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let absA := a.abs
  let sign := if a > 0.0 then 1.0 else if a < 0.0 then -1.0 else 0.0
  FastLC.ofFloat absA + { terms := #[⟨-1.0, sign * b⟩] }

/-- Sign function (returns -1, 0, or 1) -/
def sign (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  FastLC.ofFloat (if a > 0.0 then 1.0 else if a < 0.0 then -1.0 else 0.0)

/-- Floor function -/
def floor (x : FastLC.LC) : FastLC.LC :=
  FastLC.ofFloat (FastLC.std x).floor

/-- Ceiling function -/
def ceil (x : FastLC.LC) : FastLC.LC :=
  FastLC.ofFloat (FastLC.std x).ceil

/-- Round to nearest integer -/
def round (x : FastLC.LC) : FastLC.LC :=
  FastLC.ofFloat (FastLC.std x).round

/-- Fractional part: x - floor(x) -/
def fract (x : FastLC.LC) : FastLC.LC :=
  x - floor x

/-- Modulo operation -/
def fmod (x y : FastLC.LC) : FastLC.LC :=
  let xa := FastLC.std x
  let ya := FastLC.std y
  if ya == 0.0 then FastLC.ofFloat nan
  else FastLC.ofFloat (xa - ya * (xa / ya).floor)

/-- Gaussian/Error function approximation: erf(x)
    Using Horner form of rational approximation -/
def erf (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  -- Approximation for erf using tanh-based formula
  -- erf(x) ≈ tanh(√π · x · (1 + 0.147·x²)/(1 + 0.147·x²))
  -- For simplicity, use built-in approximation
  let t := 1.0 / (1.0 + 0.5 * a.abs)
  let tau := t * Float.exp (-a*a - 1.26551223 +
    t * (1.00002368 + t * (0.37409196 + t * (0.09678418 +
    t * (-0.18628806 + t * (0.27886807 + t * (-1.13520398 +
    t * (1.48851587 + t * (-0.82215223 + t * 0.17087277)))))))))
  let erfA := if a >= 0.0 then 1.0 - tau else tau - 1.0
  -- d/dx erf(x) = (2/√π)·e^(-x²)
  let deriv := (2.0 / Float.sqrt pi) * Float.exp (-a * a)
  FastLC.ofFloat erfA + { terms := #[⟨-1.0, b * deriv⟩] }

/-- Complementary error function: erfc(x) = 1 - erf(x) -/
def erfc (x : FastLC.LC) : FastLC.LC :=
  FastLC.ofFloat 1.0 - erf x

/-- Sigmoid/Logistic function: σ(x) = 1/(1 + e^(-x))
    d/dx σ(x) = σ(x)·(1 - σ(x)) -/
def sigmoid (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let sigA := 1.0 / (1.0 + Float.exp (-a))
  let deriv := sigA * (1.0 - sigA)
  FastLC.ofFloat sigA + { terms := #[⟨-1.0, b * deriv⟩] }

/-- Softplus: ln(1 + e^x), smooth approximation to ReLU
    d/dx softplus(x) = σ(x) -/
def softplus (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let softplusA := Float.log (1.0 + Float.exp a)
  let sigA := 1.0 / (1.0 + Float.exp (-a))
  FastLC.ofFloat softplusA + { terms := #[⟨-1.0, b * sigA⟩] }

/-- ReLU: max(0, x) with subgradient
    d/dx ReLU(x) = 1 if x > 0, 0 if x < 0, undefined at 0 (we use 0) -/
def relu (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  if a > 0.0 then
    FastLC.ofFloat a + { terms := #[⟨-1.0, b⟩] }
  else
    FastLC.ofFloat 0.0

/-- Leaky ReLU: max(αx, x) where α is small (default 0.01) -/
def leakyRelu (x : FastLC.LC) (alpha : Float := 0.01) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  if a > 0.0 then
    FastLC.ofFloat a + { terms := #[⟨-1.0, b⟩] }
  else
    FastLC.ofFloat (alpha * a) + { terms := #[⟨-1.0, alpha * b⟩] }

/-- GELU: Gaussian Error Linear Unit
    GELU(x) = x · Φ(x) where Φ is the CDF of standard normal
    Approximation: GELU(x) ≈ 0.5x(1 + tanh(√(2/π)(x + 0.044715x³))) -/
def gelu (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let sqrt2pi := Float.sqrt (2.0 / pi)
  let inner := sqrt2pi * (a + 0.044715 * a * a * a)
  let tanhInner := Float.tanh inner
  let geluA := 0.5 * a * (1.0 + tanhInner)
  -- Derivative is complex, approximate numerically for now
  let h := 1e-7
  let geluAh := 0.5 * (a + h) * (1.0 + Float.tanh (sqrt2pi * ((a+h) + 0.044715 * (a+h)*(a+h)*(a+h))))
  let deriv := (geluAh - geluA) / h
  FastLC.ofFloat geluA + { terms := #[⟨-1.0, b * deriv⟩] }

end LeviCivita.Transcendental

/-! ## Tests -/

namespace LeviCivita.Transcendental.Test

open LeviCivita.Fast
open LeviCivita.Transcendental

-- Verify derivatives by comparing f(x+ε) coefficient with known f'(x)

#eval do
  IO.println "═══ Transcendental Function Tests ═══"
  IO.println ""

  let x := FastLC.ofFloat 1.0
  let xε := x + FastLC.epsilon

  -- exp
  let expResult := exp xε
  let expDeriv := FastLC.getCoeff expResult (-1.0)
  IO.println s!"exp(1 + ε) = {FastLC.std expResult} + {expDeriv}ε"
  IO.println s!"  Expected derivative: e^1 = {Float.exp 1.0}"
  IO.println ""

  -- log
  let logResult := log xε
  let logDeriv := FastLC.getCoeff logResult (-1.0)
  IO.println s!"log(1 + ε) = {FastLC.std logResult} + {logDeriv}ε"
  IO.println s!"  Expected derivative: 1/1 = 1.0"
  IO.println ""

  -- sin at x = π/4
  let y : FastLC.LC := FastLC.ofFloat (pi / 4.0)
  let yε := y + FastLC.epsilon
  let sinResult := sin yε
  let sinDeriv := FastLC.getCoeff sinResult (-1.0)
  IO.println s!"sin(π/4 + ε) = {FastLC.std sinResult} + {sinDeriv}ε"
  IO.println s!"  Expected: sin(π/4)={Float.sin (pi/4)}, deriv=cos(π/4)={Float.cos (pi/4)}"
  IO.println ""

  -- cos
  let cosResult := cos yε
  let cosDeriv := FastLC.getCoeff cosResult (-1.0)
  IO.println s!"cos(π/4 + ε) = {FastLC.std cosResult} + {cosDeriv}ε"
  IO.println s!"  Expected: cos(π/4)={Float.cos (pi/4)}, deriv=-sin(π/4)={-Float.sin (pi/4)}"
  IO.println ""

  -- sqrt
  let z := FastLC.ofFloat 4.0
  let zε := z + FastLC.epsilon
  let sqrtResult := sqrt zε
  let sqrtDeriv := FastLC.getCoeff sqrtResult (-1.0)
  IO.println s!"sqrt(4 + ε) = {FastLC.std sqrtResult} + {sqrtDeriv}ε"
  IO.println s!"  Expected: sqrt(4)=2, deriv=1/(2·sqrt(4))=0.25"
  IO.println ""

  -- tanh
  let tanhResult := tanh xε
  let tanhDeriv := FastLC.getCoeff tanhResult (-1.0)
  let tanhVal := Float.tanh 1.0
  let sech2 := 1.0 - tanhVal * tanhVal
  IO.println s!"tanh(1 + ε) = {FastLC.std tanhResult} + {tanhDeriv}ε"
  IO.println s!"  Expected: tanh(1)={tanhVal}, deriv=sech²(1)={sech2}"
  IO.println ""

  -- sigmoid
  let sigResult := sigmoid xε
  let sigDeriv := FastLC.getCoeff sigResult (-1.0)
  let sigVal := 1.0 / (1.0 + Float.exp (-1.0))
  IO.println s!"sigmoid(1 + ε) = {FastLC.std sigResult} + {sigDeriv}ε"
  IO.println s!"  Expected: σ(1)={sigVal}, deriv=σ(1)(1-σ(1))={sigVal * (1.0 - sigVal)}"

end LeviCivita.Transcendental.Test
