import Std

/-!
# Fast Levi-Civita Implementations

Multiple implementations for benchmarking computational performance:
1. FastLC - Float coefficients, Float exponents (fastest arithmetic)
2. BinaryLC - Sorted array with binary search for lookups
-/

set_option linter.missingDocs false

namespace LeviCivita.Fast

/-! ## 1. FastLC - Float-based for maximum speed -/

namespace FastLC

/-- A term with Float coefficient and Float exponent. -/
structure Term where
  exp : Float
  coeff : Float
deriving BEq, Inhabited, Repr

/-- Fast LC using Float arithmetic throughout. -/
structure LC where
  terms : Array Term := #[]
deriving Inhabited, Repr

instance : Zero LC where zero := { terms := #[] }
instance : One LC where one := { terms := #[⟨0.0, 1.0⟩] }

/-- The infinitesimal ε. -/
def epsilon : LC := { terms := #[⟨-1.0, 1.0⟩] }

/-- The infinite unit H = 1/ε. -/
def H : LC := { terms := #[⟨1.0, 1.0⟩] }

/-- From Float constant. -/
def ofFloat (x : Float) : LC :=
  if x == 0.0 then { terms := #[] } else { terms := #[⟨0.0, x⟩] }

instance : OfNat LC n where
  ofNat := ofFloat n.toFloat

instance : Coe Float LC where
  coe := ofFloat

/-- `1.5 · 2⁵²`. The constants of `snapExp` are top-level definitions so that
they are computed once, not per call in the inner loop of `*`. -/
def roundingMagic : Float := 6755399441055744.0
/-- `lcm(1, …, 16)`. -/
def snapDenominator : Float := 720720.0
/-- Relative tolerance of `snapExp`. -/
def snapTol : Float := 1e-12
/-- Largest continued-fraction denominator `snapExp` tries. -/
def snapMaxDen : Float := 1e6

/-- `e` is an integer (for `|e| < 2⁵¹`). Adding and removing `1.5 · 2⁵²` rounds
to an integer in plain Float arithmetic, which is much cheaper than a call to
`Float.round`. -/
@[inline] def isIntegral (e : Float) : Bool :=
  (e + roundingMagic) - roundingMagic == e

/-- Canonical form of an exponent (`snapExp`; this is its non-integer path).

Exponents are Floats, and two computations of the same rational exponent can
disagree in the last bit: `0.1 + 0.2 ≠ 0.3`, and `ε^{0.1} · ε^{0.2}` would land
next to `ε^{0.3}` instead of on it, so `x - x` could leave two uncancelled terms
and `isStandard (ε^{0.1} ε^{0.2} H^{0.3})` would fail. Every exponent the
arithmetic creates goes through `snapExp`: an exponent within `1e-12` (relative)
of a rational `p/q` with `q ≤ 10⁶` is replaced by the correctly rounded Float
`p/q`, which is the same value whichever way `p/q` was reached (and the value of
a literal such as `0.3` or `1/3`). Integers are left alone.

Fast path: a denominator dividing `720720 = lcm(1, …, 16)` is found with one
multiplication, and `k / 720720` rounds to the same Float as the reduced `p/q`
(both are the correctly rounded value of one rational). Other denominators fall
back to continued fractions. -/
def snapExpSlow (e : Float) : Float := Id.run do
  if e.isNaN || e.isInf then return e
  let tol := snapTol * (if e.abs > 1 then e.abs else 1)
  let scaled := e * snapDenominator
  let k := (scaled + roundingMagic) - roundingMagic
  if (scaled - k).abs ≤ tol * snapDenominator then return k / snapDenominator
  -- Continued-fraction convergents p/q of e.
  let mut x := e
  let mut p0 : Float := 1.0
  let mut q0 : Float := 0.0
  let mut p1 : Float := e.floor
  let mut q1 : Float := 1.0
  for _ in [0:40] do
    if (e - p1 / q1).abs ≤ tol then return p1 / q1
    let frac := x - x.floor
    if frac == 0.0 then break
    x := 1.0 / frac
    let a := x.floor
    let p2 := a * p1 + p0
    let q2 := a * q1 + q0
    if q2 > snapMaxDen then break
    p0 := p1; q0 := q1; p1 := p2; q1 := q2
  return e

@[inherit_doc snapExpSlow, inline]
def snapExp (e : Float) : Float := if isIntegral e then e else snapExpSlow e

/-- Merge sorted arrays (descending by exp). -/
@[inline] private def mergeSorted (xs ys : Array Term) : Array Term := Id.run do
  let mut i := 0
  let mut j := 0
  let mut acc : Array Term := #[]
  while i < xs.size || j < ys.size do
    if hi : i < xs.size then
      if hj : j < ys.size then
        let xi := xs[i]
        let yj := ys[j]
        if xi.exp > yj.exp then
          if xi.coeff != 0.0 then acc := acc.push xi
          i := i + 1
        else if xi.exp < yj.exp then
          if yj.coeff != 0.0 then acc := acc.push yj
          j := j + 1
        else
          let c := xi.coeff + yj.coeff
          if c != 0.0 then acc := acc.push ⟨xi.exp, c⟩
          i := i + 1
          j := j + 1
      else
        if xs[i].coeff != 0.0 then acc := acc.push xs[i]
        i := i + 1
    else
      if hj : j < ys.size then
        if ys[j].coeff != 0.0 then acc := acc.push ys[j]
        j := j + 1
      else
        break
  acc

instance : Add LC where
  add x y := { terms := mergeSorted x.terms y.terms }

instance : Neg LC where
  neg x := { terms := x.terms.map fun t => ⟨t.exp, -t.coeff⟩ }

instance : Sub LC where
  sub x y := x + (-y)

/-- `x · t`, with every new exponent put in canonical form (`snapExp`). -/
@[inline] private def mulByTerm (x : LC) (t : Term) : LC := Id.run do
  if t.coeff == 0.0 then return { terms := #[] }
  let mut out : Array Term := Array.mkEmpty x.terms.size
  for s in x.terms do
    let e := s.exp + t.exp
    out := out.push ⟨if isIntegral e then e else snapExpSlow e, s.coeff * t.coeff⟩
  return { terms := out }

instance : Mul LC where
  mul x y := Id.run do
    if x.terms.isEmpty || y.terms.isEmpty then
      -- `0 · NaN = NaN`, as for Float: an undefined factor stays undefined.
      if (x.terms ++ y.terms).any (·.coeff.isNaN) then return { terms := #[⟨0.0, 0.0 / 0.0⟩] }
      return { terms := #[] }
    let mut result : LC := { terms := #[] }
    for t in y.terms do
      result := result + mulByTerm x t
    result

instance : HPow LC Nat LC where
  hPow x n := Id.run do
    if n == 0 then return 1
    let mut result : LC := 1
    let mut base := x
    let mut exp := n
    while exp > 0 do
      if exp % 2 == 1 then
        result := result * base
      base := base * base
      exp := exp / 2
    result

/-- Get coefficient at exponent (linear search - fast for small arrays). -/
def getCoeff (x : LC) (e : Float) : Float :=
  let e := snapExp e
  match x.terms.find? (·.exp == e) with
  | some t => t.coeff
  | none => 0.0

/-- Standard part. -/
def std (x : LC) : Float := getCoeff x 0.0

/-- Derivative via infinitesimal. -/
def derivative (f : LC → LC) (pt : LC) : Float :=
  let delta := f (pt + epsilon) - f pt
  let quotient := delta * H
  std quotient

/-- Inversion via geometric series. -/
def invert (x : LC) (terms : Nat := 10) : Option LC := do
  let lead ← x.terms[0]?
  if lead.coeff == 0.0 then none
  let leadInv : LC := { terms := #[⟨-lead.exp, 1.0 / lead.coeff⟩] }
  let leadLC : LC := { terms := #[lead] }
  let delta := (x - leadLC) * leadInv
  let mut result : LC := 1
  let mut power : LC := 1
  for i in [1:terms] do
    power := power * delta
    let sign := if i % 2 == 1 then -1.0 else 1.0
    result := result + { terms := power.terms.map fun t => ⟨t.exp, sign * t.coeff⟩ }
  -- `δ^terms` is the first power left out, so only terms of relative valuation
  -- `< terms · ν(δ)` are complete; drop the rest rather than return wrong ones.
  let exact : LC := match delta.terms[0]? with
    | some t => { terms := result.terms.filter (- ·.exp < terms.toFloat * -t.exp) }
    | none => result
  some (leadInv * exact)

instance : Inv LC where
  inv x := (invert x).getD 0

instance : Div LC where
  div x y := x * y⁻¹

instance : ToString LC where
  toString x := Id.run do
    if x.terms.isEmpty then return "0"
    let mut parts := #[]
    for t in x.terms do
      let coeff := if t.coeff == 1.0 && t.exp != 0.0 then ""
                   else if t.coeff == -1.0 && t.exp != 0.0 then "-"
                   else s!"{t.coeff}"
      let unit :=
        if t.exp == 0.0 then ""
        else if t.exp == 1.0 then "H"
        else if t.exp == -1.0 then "ε"
        else if t.exp > 0.0 then s!"H^{t.exp}"
        else s!"ε^{-t.exp}"
      parts := parts.push (coeff ++ unit)
    String.intercalate " + " parts.toList

/-- The value of a function outside its domain (e.g. `exp H`, `log ε`): a single
NaN standard part, which `st?` reports as `none`. -/
def undefined : LC := { terms := #[⟨0.0, 0.0 / 0.0⟩] }

/-- `Σₖ c(k) δᵏ` with `δ = x − std x`, the Taylor series of a function at the
standard part `a = std x` when `c k = f⁽ᵏ⁾(a) / k!`. Every term of valuation
`< prec` is exact: each power of `δ` is truncated at `prec` (a dropped term cannot
come back, since multiplying by the infinitesimal `δ` only raises valuations), and
the sum stops once `δᵏ` is entirely beyond `prec`. That takes `⌈prec / ν(δ)⌉`
powers, so `sin (a + ε)` needs 5 and `sin (a + √ε)` needs 10. Past `maxTerms`
powers (only when `ν(δ) < prec / maxTerms`) the result is cut at valuation
`maxTerms · ν(δ)`, below which it is still exact. Only finite `x` have a Taylor
germ: for an infinite `x` (any `H` term) the result is `undefined`. -/
def taylorSeries (c : Nat → Float) (x : LC) (prec : Float := 5) (maxTerms : Nat := 64) : LC := Id.run do
  if x.terms.any (·.exp > 0.0) then return undefined
  let delta := x - ofFloat (std x)
  let keep (y : LC) (bound : Float) : LC := { terms := y.terms.filter (- ·.exp < bound) }
  let mut acc : LC := ofFloat (c 0)
  let mut pow : LC := 1
  let mut done := false
  for k in [1:maxTerms + 1] do
    pow := keep (pow * delta) prec
    if pow.terms.isEmpty then
      done := true
      break
    let ck := c k
    acc := acc + { terms := pow.terms.map fun t => ⟨t.exp, ck * t.coeff⟩ }
  if done then return acc
  match delta.terms[0]? with
  | some t => return keep acc (maxTerms.toFloat * -t.exp)
  | none => return acc

/-- `0!, 1!, …, 170!` (`171!` overflows a Float). -/
def factorialTable : Array Float :=
  (List.range 170).foldl (fun acc i => acc.push (acc.back! * (i + 1).toFloat)) #[1.0]

/-- `k!` as a Float (`∞` past `170!`). -/
@[inline] def factorial (k : Nat) : Float :=
  if h : k < factorialTable.size then factorialTable[k] else 1.0 / 0.0

/-- Taylor expansion from a finite list of derivatives `derivs[k] = f⁽ᵏ⁾(a)` at
`a = std x`: `Σ_{k < n} derivs[k] / k! · δᵏ` with `n = derivs.size`. The result
keeps exactly the terms this determines: those of valuation `< n` (through `ε^{n−1}`
for a seed `a + ε`) and `< n · ν(δ)` (the first term `δⁿ` that is missing). So
`taylorAt` with five derivatives gives `f(a + ε)` through `ε⁴`, and `f(a + √ε)`
through `ε²`. Infinite input is `undefined`. -/
def taylorAt (derivs : Array Float) (x : LC) : LC :=
  let n := derivs.size
  let y := taylorSeries (fun k => if k < n then derivs[k]! / factorial k else 0.0) x n.toFloat n
  let delta := x - ofFloat (std x)
  match delta.terms[0]? with
  | some t => if x.terms.any (·.exp > 0.0) then y
              else { terms := y.terms.filter (- ·.exp < n.toFloat * -t.exp) }
  | none => y

/-- Precision of the elementary functions: every term of valuation `< jetOrder`
is exact, so `f(a + ε)` carries `f(a), f'(a), …, f⁽⁴⁾(a)/4!`. -/
def jetOrder : Nat := 5

/-- Sine: exact for every term of valuation `< jetOrder` (see `taylorSeries`). -/
def sin (x : LC) : LC :=
  let a := std x
  let s := Float.sin a
  let c := Float.cos a
  taylorSeries (fun k => (match k % 4 with | 0 => s | 1 => c | 2 => -s | _ => -c) / factorial k) x jetOrder.toFloat

/-- Cosine: exact for every term of valuation `< jetOrder` (see `taylorSeries`). -/
def cos (x : LC) : LC :=
  let a := std x
  let s := Float.sin a
  let c := Float.cos a
  taylorSeries (fun k => (match k % 4 with | 0 => c | 1 => -s | 2 => -c | _ => s) / factorial k) x jetOrder.toFloat

end FastLC

/-! ## 2. BinaryLC - Sorted array with binary search -/

namespace BinaryLC

/-- A term with Rat coefficient and Rat exponent. -/
structure Term where
  exp : Rat
  coeff : Rat
deriving BEq, Inhabited, Repr, DecidableEq

/-- Binary-search LC: sorted descending by exponent. -/
structure LC where
  terms : Array Term := #[]
deriving Inhabited, Repr

instance : Zero LC where zero := { terms := #[] }
instance : One LC where one := { terms := #[⟨0, 1⟩] }

def epsilon : LC := { terms := #[⟨-1, 1⟩] }
def H : LC := { terms := #[⟨1, 1⟩] }

def ofRat (q : Rat) : LC :=
  if q == 0 then { terms := #[] } else { terms := #[⟨0, q⟩] }

instance : OfNat LC n where
  ofNat := ofRat n

instance : Coe Rat LC where
  coe := ofRat

/-- Binary search for exponent in sorted (descending) array.
    Returns index where exp should be, or where it is. -/
@[inline] def binarySearch (arr : Array Term) (e : Rat) : Nat := Id.run do
  if arr.isEmpty then return 0
  let mut lo := 0
  let mut hi := arr.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if arr[mid]!.exp > e then
      lo := mid + 1
    else
      hi := mid
  lo

/-- Get coefficient at exponent using binary search. -/
def getCoeff (x : LC) (e : Rat) : Rat :=
  let idx := binarySearch x.terms e
  if h : idx < x.terms.size then
    let t := x.terms[idx]
    if t.exp == e then t.coeff else 0
  else 0

/-- Merge sorted arrays. -/
@[inline] private def mergeSorted (xs ys : Array Term) : Array Term := Id.run do
  let mut i := 0
  let mut j := 0
  let mut acc : Array Term := #[]
  while i < xs.size || j < ys.size do
    if hi : i < xs.size then
      if hj : j < ys.size then
        let xi := xs[i]
        let yj := ys[j]
        if xi.exp > yj.exp then
          if xi.coeff != 0 then acc := acc.push xi
          i := i + 1
        else if xi.exp < yj.exp then
          if yj.coeff != 0 then acc := acc.push yj
          j := j + 1
        else
          let c := xi.coeff + yj.coeff
          if c != 0 then acc := acc.push ⟨xi.exp, c⟩
          i := i + 1
          j := j + 1
      else
        if xs[i].coeff != 0 then acc := acc.push xs[i]
        i := i + 1
    else
      if hj : j < ys.size then
        if ys[j].coeff != 0 then acc := acc.push ys[j]
        j := j + 1
      else
        break
  acc

instance : Add LC where
  add x y := { terms := mergeSorted x.terms y.terms }

instance : Neg LC where
  neg x := { terms := x.terms.map fun t => ⟨t.exp, -t.coeff⟩ }

instance : Sub LC where
  sub x y := x + (-y)

@[inline] private def mulByTerm (x : LC) (t : Term) : LC :=
  if t.coeff == 0 then { terms := #[] }
  else { terms := x.terms.map fun s => ⟨s.exp + t.exp, s.coeff * t.coeff⟩ }

instance : Mul LC where
  mul x y := Id.run do
    if x.terms.isEmpty || y.terms.isEmpty then return { terms := #[] }
    let mut result : LC := { terms := #[] }
    for t in y.terms do
      result := result + mulByTerm x t
    result

instance : HPow LC Nat LC where
  hPow x n := Id.run do
    if n == 0 then return 1
    let mut result : LC := 1
    let mut base := x
    let mut exp := n
    while exp > 0 do
      if exp % 2 == 1 then
        result := result * base
      base := base * base
      exp := exp / 2
    result

def std (x : LC) : Rat := getCoeff x 0

def derivative (f : LC → LC) (pt : LC) : Rat :=
  let delta := f (pt + epsilon) - f pt
  let quotient := delta * H
  std quotient

def invert (x : LC) (terms : Nat := 10) : Option LC := do
  let lead ← x.terms[0]?
  if lead.coeff == 0 then none
  let leadInv : LC := { terms := #[⟨-lead.exp, lead.coeff⁻¹⟩] }
  let leadLC : LC := { terms := #[lead] }
  let delta := (x - leadLC) * leadInv
  let mut result : LC := 1
  let mut power : LC := 1
  for i in [1:terms] do
    power := power * delta
    let sign : Rat := if i % 2 == 1 then -1 else 1
    result := result + { terms := power.terms.map fun t => ⟨t.exp, sign * t.coeff⟩ }
  some (leadInv * result)

instance : Inv LC where
  inv x := (invert x).getD 0

instance : Div LC where
  div x y := x * y⁻¹

end BinaryLC

end LeviCivita.Fast
