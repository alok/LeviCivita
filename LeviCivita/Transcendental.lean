import LeviCivita.Fast

/-!
# Transcendental Functions for Levi-Civita Numbers

LC-aware implementations of exp, log, sin, cos, tan, sqrt, pow, etc.
These properly handle infinitesimal arguments to enable automatic differentiation.

Key insight: For f(a + δ) where a is standard and δ is the infinitesimal part:
  f(a + δ) = f(a) + f'(a)δ + f''(a)δ²/2! + ...

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
    exp(a + δ) = exp(a) · exp(δ) where a is the standard part and δ is infinitesimal.
    Uses Taylor series expansion for the infinitesimal part. -/
def exp (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC := Id.run do
  if !FastLC.isFinite x then
    return FastLC.ofFloat nan
  let a := FastLC.std x
  let delta := FastLC.infinitesimalPart x
  let expA := Float.exp a
  let mut res : FastLC.LC := 1
  let mut p : FastLC.LC := 1
  let mut fact := 1.0
  for i in [1:terms] do
    p := p * delta
    fact := fact * i.toFloat
    res := res + p * FastLC.ofFloat (1.0 / fact)
  FastLC.ofFloat expA * res

/-- Natural logarithm for LC numbers.
    log(a + δ) = log(a) + log(1 + δ/a) for a > 0, δ infinitesimal.
    Uses Taylor series: log(1+u) = u - u²/2 + u³/3 - ... -/
def log (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC := Id.run do
  let a := FastLC.std x
  if a <= 0.0 || !FastLC.isFinite x then
    return FastLC.ofFloat nan
  let delta := FastLC.infinitesimalPart x
  let u := delta * FastLC.ofFloat (1.0 / a)
  let logA := Float.log a
  let mut res : FastLC.LC := 0
  let mut p : FastLC.LC := u
  for i in [1:terms] do
    let sign := if i % 2 == 1 then 1.0 else -1.0
    res := res + p * FastLC.ofFloat (sign / i.toFloat)
    p := p * u
  FastLC.ofFloat logA + res

/-- Base-10 logarithm -/
def log10 (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  log x terms * FastLC.ofFloat (1.0 / Float.log 10.0)

/-- Base-2 logarithm -/
def log2 (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  log x terms * FastLC.ofFloat (1.0 / Float.log 2.0)

/-- Exponential base e, alias for exp -/
def exp1 := exp

/-- Exponential base 2: 2^x -/
def exp2 (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  exp (x * FastLC.ofFloat (Float.log 2.0)) terms

/-- Exponential base 10: 10^x -/
def exp10 (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  exp (x * FastLC.ofFloat (Float.log 10.0)) terms

/-! ## Trigonometric Functions -/

/-- Sine function for LC numbers.
    sin(a + δ) = sin(a)cos(δ) + cos(a)sin(δ)
    Uses Taylor series for sin(δ) and cos(δ). -/
def sin (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC := Id.run do
  if !FastLC.isFinite x then return FastLC.ofFloat nan
  let a := FastLC.std x
  let delta := FastLC.infinitesimalPart x
  let sinA := Float.sin a
  let cosA := Float.cos a
  
  -- Compute sin(delta) and cos(delta)
  let mut sinD : FastLC.LC := 0
  let mut cosD : FastLC.LC := 1
  let mut p : FastLC.LC := delta
  let mut fact := 1.0
  
  for i in [1:terms] do
    fact := fact * i.toFloat
    if i % 4 == 1 then
      sinD := sinD + p * FastLC.ofFloat (1.0 / fact)
    else if i % 4 == 2 then
      cosD := cosD - p * FastLC.ofFloat (1.0 / fact)
    else if i % 4 == 3 then
      sinD := sinD - p * FastLC.ofFloat (1.0 / fact)
    else -- i % 4 == 0
      cosD := cosD + p * FastLC.ofFloat (1.0 / fact)
    p := p * delta
    
  FastLC.ofFloat sinA * cosD + FastLC.ofFloat cosA * sinD

/-- Cosine function for LC numbers.
    cos(a + δ) = cos(a)cos(δ) - sin(a)sin(δ) -/
def cos (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC := Id.run do
  if !FastLC.isFinite x then return FastLC.ofFloat nan
  let a := FastLC.std x
  let delta := FastLC.infinitesimalPart x
  let sinA := Float.sin a
  let cosA := Float.cos a
  
  -- Compute sin(delta) and cos(delta)
  let mut sinD : FastLC.LC := 0
  let mut cosD : FastLC.LC := 1
  let mut p : FastLC.LC := delta
  let mut fact := 1.0
  
  for i in [1:terms] do
    fact := fact * i.toFloat
    if i % 4 == 1 then
      sinD := sinD + p * FastLC.ofFloat (1.0 / fact)
    else if i % 4 == 2 then
      cosD := cosD - p * FastLC.ofFloat (1.0 / fact)
    else if i % 4 == 3 then
      sinD := sinD - p * FastLC.ofFloat (1.0 / fact)
    else -- i % 4 == 0
      cosD := cosD + p * FastLC.ofFloat (1.0 / fact)
    p := p * delta
    
  FastLC.ofFloat cosA * cosD - FastLC.ofFloat sinA * sinD

/-- Tangent function for LC numbers. -/
def tan (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  sin x terms / cos x terms

/-- Cotangent function. -/
def cot (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  cos x terms / sin x terms

/-- Secant function. -/
def sec (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  1 / cos x terms

/-- Cosecant function. -/
def csc (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  1 / sin x terms

/-! ## Power and Root Functions -/

/-- Square root: sqrt(x) = x^(1/2) -/
def sqrt (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC := Id.run do
  if x.terms.isEmpty then return 0
  let lead := x.terms[0]!
  if lead.coeff < 0.0 then return FastLC.ofFloat nan
  
  let c := lead.coeff
  let e := lead.exp
  let resLead : FastLC.Term := ⟨e / 2.0, Float.sqrt c⟩
  
  let leadLC := FastLC.ofTerm lead
  let delta := x / leadLC - 1
  
  let mut res : FastLC.LC := 1
  let mut p : FastLC.LC := 1
  let mut binom := 1.0
  for n in [1:terms] do
    p := p * delta
    binom := binom * (0.5 - n.toFloat + 1.0) / n.toFloat
    res := res + p * FastLC.ofFloat binom
    
  FastLC.ofTerm resLead * res

/-- Cube root: cbrt(x) = x^(1/3) -/
def cbrt (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC := Id.run do
  if x.terms.isEmpty then return 0
  let lead := x.terms[0]!
  
  let c := lead.coeff
  let e := lead.exp
  let resLead : FastLC.Term := ⟨e / 3.0, Float.pow c (1.0/3.0)⟩
  
  let leadLC := FastLC.ofTerm lead
  let delta := x / leadLC - 1
  
  let mut res : FastLC.LC := 1
  let mut p : FastLC.LC := 1
  let mut binom := 1.0
  for n in [1:terms] do
    p := p * delta
    binom := binom * (1.0/3.0 - n.toFloat + 1.0) / n.toFloat
    res := res + p * FastLC.ofFloat binom
    
  FastLC.ofTerm resLead * res

/-- General power: x^y for LC numbers -/
def pow (x y : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  exp (y * log x terms) terms

/-- Integer power (more efficient for integer exponents) -/
def powi (x : FastLC.LC) (n : Int) : FastLC.LC :=
  if n == 0 then FastLC.ofFloat 1.0
  else if n > 0 then x ^ n.toNat
  else (x ^ (-n).toNat)⁻¹

/-! ## Inverse Trigonometric Functions -/

-- Arcsine: arcsin(x), domain -1 to 1
-- d/dx arcsin(x) = 1/sqrt(1-x^2)
def asin (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  let a := FastLC.std x
  if a.abs > 1.0 then FastLC.ofFloat nan
  else
    -- Use derivative and Taylor
    -- For now, keep it simple or implement via other identities
    let b := FastLC.getCoeff x (-1.0)
    let asinA := Float.asin a
    let deriv := 1.0 / Float.sqrt (1.0 - a * a)
    FastLC.ofFloat asinA + FastLC.ofTerm ⟨-1.0, b * deriv⟩

-- Arccosine: arccos(x), domain -1 to 1
def acos (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  FastLC.ofFloat (pi / 2.0) - asin x terms

/-- Arctangent: arctan(x) -/
def atan (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  -- atan(x) = i/2 * (log(1-ix) - log(1+ix)) -- but we don't have complex
  -- For now, first order
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let atanA := Float.atan a
  let deriv := 1.0 / (1.0 + a * a)
  FastLC.ofFloat atanA + FastLC.ofTerm ⟨-1.0, b * deriv⟩

/-- Two-argument arctangent: atan2(y, x) -/
def atan2 (y x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  let ya := FastLC.std y
  let xa := FastLC.std x
  let yb := FastLC.getCoeff y (-1.0)
  let xb := FastLC.getCoeff x (-1.0)
  let atan2A := Float.atan2 ya xa
  let r2 := xa * xa + ya * ya
  if r2 < 1e-20 then
    FastLC.ofFloat nan
  else
    let deriv := (yb * xa - xb * ya) / r2
    FastLC.ofFloat atan2A + FastLC.ofTerm ⟨-1.0, deriv⟩

/-! ## Hyperbolic Functions -/

/-- Hyperbolic sine: sinh(x) = (e^x - e^(-x))/2 -/
def sinh (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  (exp x terms - exp (-x) terms) * FastLC.ofFloat 0.5

/-- Hyperbolic cosine: cosh(x) = (e^x + e^(-x))/2 -/
def cosh (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  (exp x terms + exp (-x) terms) * FastLC.ofFloat 0.5

/-- Hyperbolic tangent: tanh(x) = sinh(x)/cosh(x) -/
def tanh (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  sinh x terms / cosh x terms

/-- Hyperbolic cotangent: coth(x) = cosh(x)/sinh(x) -/
def coth (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  cosh x terms / sinh x terms

/-- Hyperbolic secant: sech(x) = 1/cosh(x) -/
def sech (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  1 / cosh x terms

/-- Hyperbolic cosecant: csch(x) = 1/sinh(x) -/
def csch (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  1 / sinh x terms

/-! ## Inverse Hyperbolic Functions -/

/-- Inverse hyperbolic sine: asinh(x) = ln(x + √(x²+1)) -/
def asinh (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  log (x + sqrt (x * x + 1) terms) terms

/-- Inverse hyperbolic cosine: acosh(x) = ln(x + √(x²-1)), x ≥ 1 -/
def acosh (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  log (x + sqrt (x * x - 1) terms) terms

/-- Inverse hyperbolic tangent: atanh(x) = ln((1+x)/(1-x))/2, |x| < 1 -/
def atanh (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  log ((1 + x) / (1 - x)) terms * FastLC.ofFloat 0.5

/-! ## Special Functions -/

/-- Absolute value with subgradient at 0 -/
def abs (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let absA := a.abs
  let sign := if a > 0.0 then 1.0 else if a < 0.0 then -1.0 else 0.0
  FastLC.ofFloat absA + FastLC.ofTerm ⟨-1.0, sign * b⟩

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

/-- Gaussian/Error function approximation: erf(x) -/
def erf (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  -- For now, first order + built-in approximation
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let t := 1.0 / (1.0 + 0.5 * a.abs)
  let tau := t * Float.exp (-a*a - 1.26551223 +
    t * (1.00002368 + t * (0.37409196 + t * (0.09678418 +
    t * (-0.18628806 + t * (0.27886807 + t * (-1.13520398 +
    t * (1.48851587 + t * (-0.82215223 + t * 0.17087277)))))))))
  let erfA := if a >= 0.0 then 1.0 - tau else tau - 1.0
  let deriv := (2.0 / Float.sqrt pi) * Float.exp (-a * a)
  FastLC.ofFloat erfA + FastLC.ofTerm ⟨-1.0, b * deriv⟩

/-- Complementary error function: erfc(x) = 1 - erf(x) -/
def erfc (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  FastLC.ofFloat 1.0 - erf x terms

/-- Sigmoid/Logistic function: σ(x) = 1/(1 + e^(-x)) -/
def sigmoid (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  1 / (1 + exp (-x) terms)

/-- Softplus: ln(1 + e^x) -/
def softplus (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  log (1 + exp x terms) terms

/-- ReLU: max(0, x) -/
def relu (x : FastLC.LC) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  if a > 0.0 then
    FastLC.ofFloat a + FastLC.ofTerm ⟨-1.0, b⟩
  else
    FastLC.ofFloat 0.0

/-- Leaky ReLU: max(αx, x) -/
def leakyRelu (x : FastLC.LC) (alpha : Float := 0.01) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  if a > 0.0 then
    FastLC.ofFloat a + FastLC.ofTerm ⟨-1.0, b⟩
  else
    FastLC.ofFloat (alpha * a) + FastLC.ofTerm ⟨-1.0, alpha * b⟩

/-- GELU: Gaussian Error Linear Unit -/
def gelu (x : FastLC.LC) (terms : Nat := 10) : FastLC.LC :=
  let a := FastLC.std x
  let b := FastLC.getCoeff x (-1.0)
  let sqrt2pi := Float.sqrt (2.0 / pi)
  let inner := sqrt2pi * (a + 0.044715 * a * a * a)
  let tanhInner := Float.tanh inner
  let geluA := 0.5 * a * (1.0 + tanhInner)
  let h := 1e-7
  let geluAh := 0.5 * (a + h) * (1.0 + Float.tanh (sqrt2pi * ((a+h) + 0.044715 * (a+h)*(a+h)*(a+h))))
  let deriv := (geluAh - geluA) / h
  FastLC.ofFloat geluA + FastLC.ofTerm ⟨-1.0, b * deriv⟩

end LeviCivita.Transcendental

/-! ## Tests -/

namespace LeviCivita.Transcendental.Test

open LeviCivita.Fast
open LeviCivita.Transcendental

#eval do
  IO.println "═══ Transcendental Function Tests ═══"
  IO.println ""

  let x := FastLC.ofFloat 1.0
  let xε := x + FastLC.epsilon

  let expResult := exp xε
  let expDeriv := FastLC.getCoeff expResult (-1.0)
  IO.println s!"exp(1 + ε) = {FastLC.std expResult} + {expDeriv}ε"
  IO.println s!"  Expected derivative: e^1 = {Float.exp 1.0}"
  IO.println ""

  let logResult := log xε
  let logDeriv := FastLC.getCoeff logResult (-1.0)
  IO.println s!"log(1 + ε) = {FastLC.std logResult} + {logDeriv}ε"
  IO.println s!"  Expected derivative: 1/1 = 1.0"
  IO.println ""

  let y : FastLC.LC := FastLC.ofFloat (pi / 4.0)
  let yε := y + FastLC.epsilon
  let sinResult := sin yε
  let sinDeriv := FastLC.getCoeff sinResult (-1.0)
  IO.println s!"sin(π/4 + ε) = {FastLC.std sinResult} + {sinDeriv}ε"
  IO.println s!"  Expected: sin(π/4)={Float.sin (pi/4)}, deriv=cos(π/4)={Float.cos (pi/4)}"
  IO.println ""

  let cosResult := cos yε
  let cosDeriv := FastLC.getCoeff cosResult (-1.0)
  IO.println s!"cos(π/4 + ε) = {FastLC.std cosResult} + {cosDeriv}ε"
  IO.println s!"  Expected: cos(π/4)={Float.cos (pi/4)}, deriv=-sin(π/4)={-Float.sin (pi/4)}"
  IO.println ""

  let z := FastLC.ofFloat 4.0
  let zε := z + FastLC.epsilon
  let sqrtResult := sqrt zε
  let sqrtDeriv := FastLC.getCoeff sqrtResult (-1.0)
  IO.println s!"sqrt(4 + ε) = {FastLC.std sqrtResult} + {sqrtDeriv}ε"
  IO.println s!"  Expected: sqrt(4)=2, deriv=1/(2·sqrt(4))=0.25"
  IO.println ""

  let tanhResult := tanh xε
  let tanhDeriv := FastLC.getCoeff tanhResult (-1.0)
  let tanhVal := Float.tanh 1.0
  let sech2 := 1.0 - tanhVal * tanhVal
  IO.println s!"tanh(1 + ε) = {FastLC.std tanhResult} + {tanhDeriv}ε"
  IO.println s!"  Expected: tanh(1)={tanhVal}, deriv=sech²(1)={sech2}"
  IO.println ""

  let sigResult := sigmoid xε
  let sigDeriv := FastLC.getCoeff sigResult (-1.0)
  let sigVal := 1.0 / (1.0 + Float.exp (-1.0))
  IO.println s!"sigmoid(1 + ε) = {FastLC.std sigResult} + {sigDeriv}ε"
  IO.println s!"  Expected: σ(1)={sigVal}, deriv=σ(1)(1-σ(1))={sigVal * (1.0 - sigVal)}"

end LeviCivita.Transcendental.Test