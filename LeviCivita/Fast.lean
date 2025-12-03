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

/-- Multiply LC by a single term. -/
@[inline] private def mulByTerm (x : LC) (t : Term) : LC :=
  if t.coeff == 0.0 then { terms := #[] }
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

/-- Get coefficient at exponent (linear search - fast for small arrays). -/
def getCoeff (x : LC) (e : Float) : Float :=
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
  some (leadInv * result)

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

-- LC-aware trig functions that properly handle infinitesimals
-- sin(a + bε + ...) = sin(a) + bε·cos(a) + higher order terms
-- cos(a + bε + ...) = cos(a) - bε·sin(a) + higher order terms

def sin (x : LC) : LC :=
  let a := std x  -- standard part
  let sinA := Float.sin a
  let cosA := Float.cos a
  -- Get the infinitesimal coefficient (ε^(-1) term)
  let b := getCoeff x (-1.0)
  -- sin(a) + b·cos(a)·ε
  ofFloat sinA + { terms := #[⟨-1.0, b * cosA⟩] }

def cos (x : LC) : LC :=
  let a := std x  -- standard part
  let sinA := Float.sin a
  let cosA := Float.cos a
  -- Get the infinitesimal coefficient (ε^(-1) term)
  let b := getCoeff x (-1.0)
  -- cos(a) - b·sin(a)·ε
  ofFloat cosA + { terms := #[⟨-1.0, -b * sinA⟩] }

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
