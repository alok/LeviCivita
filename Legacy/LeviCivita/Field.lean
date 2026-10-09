import Std

/-!
# Levi-Civita Field

The Levi-Civita field is a non-Archimedean ordered field containing infinite and infinitesimal
quantities. It is the smallest such field that is Cauchy-complete and real closed.

Key features:
- Numbers are formal power series Σ aᵢ εʳⁱ where aᵢ ∈ ℚ and rᵢ ∈ ℚ
- Supports infinitesimals (ε, ε², ...) and infinite numbers (H = 1/ε, H², ...)
- Enables automatic differentiation via f'(x) = (f(x+ε) - f(x)) / ε

Reference: "Non-Standard Analysis Revisited" (DOI: 10.34768/amcs-2022-0006)
-/

namespace LeviCivita.Field

/-! ## Basic Types -/

/-- Exponents are rational numbers to support fractional powers of ε. -/
abbrev Exp := Rat

/-- Coefficients are rational numbers. -/
abbrev Coeff := Rat

/-- A term in a Levi-Civita number: coefficient × ε^exponent -/
structure Term where
  /-- The coefficient of this term. -/
  coeff : Coeff
  /-- The exponent of ε in this term. Negative means infinitesimal, positive means infinite. -/
  exp : Exp
deriving BEq, Inhabited, Repr

instance : ToString Term where
  toString t :=
    if t.exp == 0 then s!"{t.coeff}"
    else if t.exp == 1 then s!"{t.coeff}H"
    else if t.exp == -1 then s!"{t.coeff}ε"
    else if t.exp > 0 then s!"{t.coeff}H^{t.exp}"
    else s!"{t.coeff}ε^{-t.exp}"

/-- Map from exponents to coefficients (sparse representation). -/
abbrev CoeffMap := Std.HashMap Exp Coeff

/-- Prune zero coefficients from a coefficient map. -/
def filterZeros (m : CoeffMap) : CoeffMap := Id.run do
  let mut r : CoeffMap := {}
  for (e, c) in m do
    if c != 0 then r := r.insert e c
  r

/-! ## Levi-Civita Number -/

/-- A number in the Levi-Civita field.
    Represented as a sparse polynomial in ε with rational exponents.

    - Terms with exp < 0 are infinitesimal (ε, ε², ...)
    - Terms with exp = 0 are the standard part
    - Terms with exp > 0 are infinite (H = ε⁻¹, H², ...)
-/
structure LC where
  /-- Sparse map from exponents to coefficients. -/
  coeffs : CoeffMap := {}
deriving Inhabited

namespace LC

/-- The zero element. -/
def zero : LC := { coeffs := {} }

/-- The one element. -/
def one : LC := { coeffs := Std.HashMap.ofList [(0, 1)] }

/-- The infinitesimal ε (= ε¹). -/
def epsilon : LC := { coeffs := Std.HashMap.ofList [(-1, 1)] }

/-- The infinite unit H = 1/ε. -/
def H : LC := { coeffs := Std.HashMap.ofList [(1, 1)] }

/-- Normalize by removing zero coefficients. -/
def normalize (x : LC) : LC := { coeffs := filterZeros x.coeffs }

/-- Check if the number is zero. -/
def isZero (x : LC) : Bool := (filterZeros x.coeffs).size == 0

/-- Get the coefficient at a given exponent. -/
def getCoeff (x : LC) (e : Exp) : Coeff := x.coeffs.getD e 0

/-- Set the coefficient at a given exponent. -/
def setCoeff (x : LC) (e : Exp) (c : Coeff) : LC :=
  { coeffs := x.coeffs.insert e c }

/-- Get all terms sorted by exponent (descending, so largest terms first). -/
def toTerms (x : LC) : Array Term := Id.run do
  let mut out := #[]
  for (e, c) in x.coeffs do
    if c != 0 then out := out.push { coeff := c, exp := e }
  out.qsort (fun a b => a.exp > b.exp)

/-- Get the standard (real) part (coefficient at ε⁰). -/
def std (x : LC) : Coeff := x.getCoeff 0

/-- Create from a rational number. -/
def ofRat (q : Coeff) : LC := { coeffs := Std.HashMap.ofList [(0, q)] }

instance : Zero LC where zero := zero
instance : One LC where one := one

instance : OfNat LC n where
  ofNat := ofRat (n : Nat)

instance : Coe Coeff LC where
  coe := ofRat

/-! ## Arithmetic Operations -/

instance : Add LC where
  add x y := Id.run do
    let mut r := x.coeffs
    for (e, c) in y.coeffs do
      let prev := r.getD e 0
      r := r.insert e (prev + c)
    normalize { coeffs := r }

instance : Neg LC where
  neg x := { coeffs := x.coeffs.map (fun _ v => -v) }

instance : Sub LC where
  sub x y := x + (-y)

instance : Mul LC where
  mul x y := Id.run do
    let mut r : CoeffMap := {}
    for (ex, cx) in x.coeffs do
      for (ey, cy) in y.coeffs do
        let e := ex + ey
        let prev := r.getD e 0
        r := r.insert e (prev + (cx * cy))
    normalize { coeffs := r }

/-- Natural number power. -/
instance : HPow LC Nat LC where
  hPow x n := Id.run do
    let mut acc := (1 : LC)
    for _ in [0:n] do
      acc := acc * x
    acc

/-! ## Ordering -/

/-- Get the leading term (highest exponent with nonzero coefficient). -/
def leadingTerm (x : LC) : Option Term :=
  (filterZeros x.coeffs).fold (init := none) fun acc e c =>
    match acc with
    | none => some { coeff := c, exp := e }
    | some t => if e > t.exp then some { coeff := c, exp := e } else acc

/-- Sign of a Levi-Civita number (-1, 0, or 1).
    Determined by the sign of the leading (most infinite) nonzero term. -/
def signum (x : LC) : Int :=
  match x.leadingTerm with
  | none => 0
  | some t => if t.coeff > 0 then 1 else if t.coeff < 0 then -1 else 0

/-- Less-than comparison for Levi-Civita numbers. -/
def lt (x y : LC) : Bool := (x - y).signum == -1

/-- Less-than-or-equal comparison for Levi-Civita numbers. -/
def le (x y : LC) : Bool := (x - y).signum <= 0

instance : LT LC where
  lt x y := lt x y = true

instance : LE LC where
  le x y := le x y = true

instance (x y : LC) : Decidable (x < y) :=
  if h : lt x y = true then isTrue h else isFalse h

instance (x y : LC) : Decidable (x ≤ y) :=
  if h : le x y = true then isTrue h else isFalse h

instance : BEq LC where
  beq x y := (x - y).isZero

/-! ## Inversion and Division -/

/-- Check if the number is "pure" (only one nonzero term). -/
def isPure (x : LC) : Bool := (filterZeros x.coeffs).size == 1

/-- Invert a pure (single-term) number. -/
def invertPure (x : LC) : Option LC := do
  if !x.isPure then none
  match x.leadingTerm with
  | none => none
  | some t =>
    if t.coeff == 0 then none
    else some { coeffs := Std.HashMap.ofList [(-t.exp, t.coeff⁻¹)] }

/-- Series expansion for 1/(1 + δ) where δ is small.
    Uses: 1/(1+δ) = 1 - δ + δ² - δ³ + ... (geometric series) -/
def expandInverseSmall (delta : LC) (n : Nat := 10) : LC := Id.run do
  let mut result := (1 : LC)
  let mut power := delta
  for i in [1:n] do
    let sign := if i % 2 == 1 then -1 else 1
    result := result + (sign : Coeff) * power
    power := power * delta
  result

/-- Invert a Levi-Civita number using series expansion.
    For x = a·ε^e · (1 + δ) where δ is small:
    x⁻¹ = (a⁻¹·ε^(-e)) · (1 - δ + δ² - ...) -/
def invert (x : LC) (terms : Nat := 10) : Option LC := do
  -- Find leading term
  let lead ← x.leadingTerm
  if lead.coeff == 0 then none

  -- Factor out leading term: x = lead · (1 + rest/lead)
  let leadLC : LC := { coeffs := Std.HashMap.ofList [(lead.exp, lead.coeff)] }
  let leadInv : LC := { coeffs := Std.HashMap.ofList [(-lead.exp, lead.coeff⁻¹)] }

  -- Compute δ = (x - lead) / lead = rest/lead
  let rest := x - leadLC
  let delta := rest * leadInv

  -- 1/x = (1/lead) · 1/(1 + δ)
  let seriesInv := expandInverseSmall delta terms
  some (leadInv * seriesInv)

instance : Inv LC where
  inv x := (invert x).getD 0

instance : Div LC where
  div x y := x * y⁻¹

/-! ## Pretty Printing -/

private def digitToSuperscript (c : Char) : Char :=
  match c with
  | '0' => '⁰' | '1' => '¹' | '2' => '²' | '3' => '³' | '4' => '⁴'
  | '5' => '⁵' | '6' => '⁶' | '7' => '⁷' | '8' => '⁸' | '9' => '⁹'
  | '-' => '⁻' | '/' => 'ᐟ'
  | _ => c

private def toSuperscript (s : String) : String :=
  String.ofList (s.toList.map digitToSuperscript)

instance : ToString LC where
  toString x := Id.run do
    let terms := x.toTerms
    if terms.isEmpty then return "0"

    let mut parts := #[]
    for t in terms do
      let coeff := if t.coeff == 1 && t.exp != 0 then ""
                   else if t.coeff == -1 && t.exp != 0 then "-"
                   else s!"{t.coeff}"
      let unit :=
        if t.exp == 0 then ""
        else if t.exp == 1 then "H"
        else if t.exp == -1 then "ε"
        else if t.exp > 0 then s!"H{toSuperscript (toString t.exp)}"
        else s!"ε{toSuperscript (toString (-t.exp))}"
      parts := parts.push (coeff ++ unit)

    return String.intercalate " + " parts.toList

instance : Repr LC where
  reprPrec x _ := toString x

/-! ## Automatic Differentiation -/

/-- Compute the derivative of a function at a point using infinitesimals.
    f'(x) = st((f(x + ε) - f(x)) / ε)
    where st extracts the standard part. -/
def derivative (f : LC → LC) (x : LC) : Coeff :=
  let delta := f (x + epsilon) - f x
  let quotient := delta * H  -- divide by ε = multiply by H
  quotient.std

/-- Compute higher-order derivative using ε^n. -/
def nthDerivative (f : LC → LC) (x : LC) (n : Nat) : Coeff := Id.run do
  if n == 0 then return (f x).std
  -- Use Taylor: f(x + ε) = f(x) + f'(x)ε + f''(x)ε²/2! + ...
  -- So coefficient of ε^n in f(x + ε) is f^(n)(x) / n!
  let fx := f (x + epsilon)
  let coeff := fx.getCoeff (-(n : Int))
  -- Multiply by n! to get the derivative
  let mut factorial : Coeff := 1
  for i in [1:n+1] do
    factorial := factorial * i
  coeff * factorial

/-! ## Transcendental Functions -/

/-- Factorial function. -/
def factorial (n : Nat) : Coeff := Id.run do
  let mut r : Coeff := 1
  for i in [1:n+1] do
    r := r * i
  r

/-- Exponential function via Taylor series: exp(x) = Σ xⁿ/n!
    For LC numbers, we compute exp(a + δ) = exp(a) · exp(δ) where δ is infinitesimal.
    Since exp(δ) = 1 + δ + δ²/2! + ..., we just need the series for small δ. -/
def exp (x : LC) (terms : Nat := 10) : LC := Id.run do
  -- For now, assume x is infinitesimal (std part = 0)
  -- TODO: factor out standard part and use exp(a+δ) = exp(a)·exp(δ)
  let mut result := (1 : LC)
  let mut power := (1 : LC)
  for n in [1:terms] do
    power := power * x
    let coeff := (factorial n)⁻¹
    result := result + coeff * power
  result

/-- Natural logarithm via Taylor series: log(1 + x) = x - x²/2 + x³/3 - ...
    Only valid for |x| < 1 (i.e., x infinitesimal). -/
def log1p (x : LC) (terms : Nat := 10) : LC := Id.run do
  let mut result := (0 : LC)
  let mut power := x
  for n in [1:terms] do
    let sign := if n % 2 == 1 then 1 else -1
    let coeff : Coeff := sign / n
    result := result + coeff * power
    power := power * x
  result

/-- Sine via Taylor series: sin(x) = x - x³/3! + x⁵/5! - ... -/
def sin (x : LC) (terms : Nat := 10) : LC := Id.run do
  let mut result := (0 : LC)
  let mut power := x
  let x2 := x * x
  for n in [0:terms] do
    let k := 2 * n + 1  -- odd terms: 1, 3, 5, ...
    let sign := if n % 2 == 0 then 1 else -1
    let coeff : Coeff := sign / factorial k
    result := result + coeff * power
    power := power * x2  -- advance by x² for next odd power
  result

/-- Cosine via Taylor series: cos(x) = 1 - x²/2! + x⁴/4! - ... -/
def cos (x : LC) (terms : Nat := 10) : LC := Id.run do
  let mut result := (0 : LC)
  let mut power := (1 : LC)
  let x2 := x * x
  for n in [0:terms] do
    let k := 2 * n  -- even terms: 0, 2, 4, ...
    let sign := if n % 2 == 0 then 1 else -1
    let coeff : Coeff := sign / factorial k
    result := result + coeff * power
    power := power * x2  -- advance by x²
  result

/-- Hyperbolic sine: sinh(x) = (exp(x) - exp(-x)) / 2 -/
def sinh (x : LC) (terms : Nat := 10) : LC :=
  let ex := exp x terms
  let emx := exp (-x) terms
  ((1 : Coeff) / 2) * (ex - emx)

/-- Hyperbolic cosine: cosh(x) = (exp(x) + exp(-x)) / 2 -/
def cosh (x : LC) (terms : Nat := 10) : LC :=
  let ex := exp x terms
  let emx := exp (-x) terms
  ((1 : Coeff) / 2) * (ex + emx)

end LC

/-! ## Notation -/

/-- The infinitesimal ε -/
scoped notation "ε" => LC.epsilon
/-- The infinite unit H = 1/ε -/
scoped notation "H" => LC.H

end LeviCivita.Field
