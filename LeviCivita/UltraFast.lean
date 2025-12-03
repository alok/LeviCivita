import Std
import LeviCivita.Fast

/-!
# Ultra-Fast Levi-Civita Implementation

Highly optimized LC implementation with:
1. Array-based multiplication with late sorting
2. Specialized fast paths for small polynomials
3. Minimal allocations
-/

set_option linter.missingDocs false

namespace LeviCivita.UltraFast

/-! ## UltraLC - Maximum performance -/

/-- A term with Float coefficient and Float exponent. -/
structure Term where
  exp : Float
  coeff : Float
deriving BEq, Inhabited, Repr

/-- Ultra-fast LC using optimized operations. -/
structure LC where
  terms : Array Term := #[]
deriving Inhabited, Repr

namespace LC

instance : Zero LC where zero := { terms := #[] }
instance : One LC where one := { terms := #[⟨0.0, 1.0⟩] }

/-- The infinitesimal ε. -/
@[inline] def epsilon : LC := { terms := #[⟨-1.0, 1.0⟩] }

/-- The infinite unit H = 1/ε. -/
@[inline] def H : LC := { terms := #[⟨1.0, 1.0⟩] }

/-- From Float constant. -/
@[inline] def ofFloat (x : Float) : LC :=
  if x == 0.0 then { terms := #[] } else { terms := #[⟨0.0, x⟩] }

instance : OfNat LC n where
  ofNat := ofFloat n.toFloat

instance : Coe Float LC where
  coe := ofFloat

@[inline] def size (x : LC) : Nat := x.terms.size
@[inline] def isEmpty (x : LC) : Bool := x.terms.isEmpty

/-- Get coefficient at exponent via linear search. -/
@[inline] def getCoeff (x : LC) (e : Float) : Float :=
  match x.terms.find? (·.exp == e) with
  | some t => t.coeff
  | none => 0.0

/-- Standard part (coefficient at exp 0). -/
@[inline] def std (x : LC) : Float := x.getCoeff 0.0

/-! ## Addition - optimized merge -/

/-- Merge two sorted LC numbers (descending by exp). -/
@[inline] def add (x y : LC) : LC := Id.run do
  if x.isEmpty then return y
  if y.isEmpty then return x

  -- Pre-allocate for common case
  let mut result : Array Term := Array.mkEmpty (x.size + y.size)
  let mut i := 0
  let mut j := 0

  while i < x.size || j < y.size do
    if i < x.size then
      if j < y.size then
        let xi := x.terms[i]!
        let yj := y.terms[j]!
        if xi.exp > yj.exp then
          if xi.coeff != 0.0 then result := result.push xi
          i := i + 1
        else if xi.exp < yj.exp then
          if yj.coeff != 0.0 then result := result.push yj
          j := j + 1
        else
          let c := xi.coeff + yj.coeff
          if c != 0.0 then result := result.push ⟨xi.exp, c⟩
          i := i + 1
          j := j + 1
      else
        if x.terms[i]!.coeff != 0.0 then result := result.push x.terms[i]!
        i := i + 1
    else
      if j < y.size then
        if y.terms[j]!.coeff != 0.0 then result := result.push y.terms[j]!
        j := j + 1
      else
        break

  { terms := result }

instance : Add LC where add := add

/-- Negation. -/
@[inline] def neg (x : LC) : LC :=
  { terms := x.terms.map fun t => ⟨t.exp, -t.coeff⟩ }

instance : Neg LC where neg := neg
instance : Sub LC where sub x y := x + (-y)

/-! ## Multiplication - optimized with fast paths -/

/-- Multiply by single term (very common case). -/
@[inline] private def mulByTerm (x : LC) (e : Float) (c : Float) : Array Term :=
  if c == 0.0 then #[]
  else x.terms.map fun t => ⟨t.exp + e, t.coeff * c⟩

/-- Merge adjacent terms with same exponent (assumes sorted input). -/
private def mergeAdjacent (products : Array Term) : LC := Id.run do
  if products.isEmpty then return 0

  let mut result : Array Term := Array.mkEmpty products.size
  let mut curExp := products[0]!.exp
  let mut curCoeff := products[0]!.coeff

  for i in [1:products.size] do
    let t := products[i]!
    if t.exp == curExp then
      curCoeff := curCoeff + t.coeff
    else
      if curCoeff != 0.0 then
        result := result.push ⟨curExp, curCoeff⟩
      curExp := t.exp
      curCoeff := t.coeff

  if curCoeff != 0.0 then
    result := result.push ⟨curExp, curCoeff⟩

  { terms := result }

/-- Optimized multiplication with fast paths for common cases. -/
def mul (x y : LC) : LC := Id.run do
  if x.isEmpty || y.isEmpty then return 0

  -- Fast path: single term × anything
  if x.size == 1 then
    let t := x.terms[0]!
    return { terms := mulByTerm y t.exp t.coeff }

  if y.size == 1 then
    let t := y.terms[0]!
    return { terms := mulByTerm x t.exp t.coeff }

  -- Fast path: 2 terms × 2 terms (common in derivatives)
  if x.size == 2 && y.size == 2 then
    let x0 := x.terms[0]!
    let x1 := x.terms[1]!
    let y0 := y.terms[0]!
    let y1 := y.terms[1]!

    -- 4 products
    let mut products : Array Term := #[]
    products := products.push ⟨x0.exp + y0.exp, x0.coeff * y0.coeff⟩
    products := products.push ⟨x0.exp + y1.exp, x0.coeff * y1.coeff⟩
    products := products.push ⟨x1.exp + y0.exp, x1.coeff * y0.coeff⟩
    products := products.push ⟨x1.exp + y1.exp, x1.coeff * y1.coeff⟩

    -- Sort and merge
    products := products.qsort fun a b => a.exp > b.exp
    return mergeAdjacent products

  -- General case: collect all products then sort and merge
  let mut products : Array Term := Array.mkEmpty (x.size * y.size)

  for i in [:x.size] do
    let xi := x.terms[i]!
    for j in [:y.size] do
      let yj := y.terms[j]!
      let c := xi.coeff * yj.coeff
      if c != 0.0 then
        products := products.push ⟨xi.exp + yj.exp, c⟩

  if products.isEmpty then return 0

  -- Sort descending by exponent
  products := products.qsort fun a b => a.exp > b.exp

  mergeAdjacent products

instance : Mul LC where mul := mul

/-! ## Power - binary exponentiation -/

def pow (x : LC) (n : Nat) : LC := Id.run do
  if n == 0 then return 1
  if n == 1 then return x
  let mut result : LC := 1
  let mut base := x
  let mut exp := n
  while exp > 0 do
    if exp % 2 == 1 then
      result := result * base
    base := base * base
    exp := exp / 2
  result

instance : HPow LC Nat LC where hPow := pow

/-! ## Inversion - geometric series -/

def invert (x : LC) (numTerms : Nat := 10) : Option LC := do
  if x.isEmpty then none
  let lead := x.terms[0]!
  if lead.coeff == 0.0 then none

  let leadInv : LC := { terms := #[⟨-lead.exp, 1.0 / lead.coeff⟩] }
  let leadLC : LC := { terms := #[lead] }
  let delta := (x - leadLC) * leadInv

  let mut result : LC := 1
  let mut power : LC := 1

  for i in [1:numTerms] do
    power := power * delta
    let sign := if i % 2 == 1 then -1.0 else 1.0
    let signedPower : LC := { terms := power.terms.map fun t => ⟨t.exp, sign * t.coeff⟩ }
    result := result + signedPower

  some (leadInv * result)

instance : Inv LC where
  inv x := (invert x).getD 0

instance : Div LC where
  div x y := x * y⁻¹

/-! ## Derivative -/

/-- Compute derivative using infinitesimal. -/
@[inline] def derivative (f : LC → LC) (pt : LC) : Float :=
  let delta := f (pt + epsilon) - f pt
  let quotient := delta * H
  quotient.std

/-! ## Display -/

instance : ToString LC where
  toString x := Id.run do
    if x.isEmpty then return "0"
    let mut parts : Array String := #[]
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

end LC

end LeviCivita.UltraFast

/-! ## Benchmarks comparing FastLC vs UltraFast -/

namespace LeviCivita.Bench

open LeviCivita.Fast.FastLC
open LeviCivita.UltraFast

-- Aliases for clarity
abbrev FastLC := LeviCivita.Fast.FastLC.LC
abbrev UltraLC := LeviCivita.UltraFast.LC

-- Timing helper
def bench (name : String) (iters : Nat) (f : Unit → α) : IO Unit := do
  -- Warmup
  for _ in [:50] do
    let _ := f ()
  -- Time
  let start ← IO.monoMsNow
  for _ in [:iters] do
    let _ := f ()
  let elapsed := (← IO.monoMsNow) - start
  let opsPerSec := if elapsed > 0 then (iters.toFloat * 1000.0) / elapsed.toFloat else 0.0
  IO.println s!"{name}: {elapsed}ms for {iters} iters ({opsPerSec.round} ops/sec)"

#eval do
  IO.println "════════════════════════════════════════════════════════"
  IO.println "         LC Implementation Benchmarks"
  IO.println "════════════════════════════════════════════════════════"
  IO.println ""

  -- Constants
  let fastX := LeviCivita.Fast.FastLC.ofFloat 3.14159
  let fastY := LeviCivita.Fast.FastLC.ofFloat 2.71828
  let ultraX := LeviCivita.UltraFast.LC.ofFloat 3.14159
  let ultraY := LeviCivita.UltraFast.LC.ofFloat 2.71828

  IO.println "── Constant operations (single term) ──"
  bench "FastLC  add (const)" 100000 fun _ => fastX + fastY
  bench "UltraLC add (const)" 100000 fun _ => ultraX + ultraY
  IO.println ""
  bench "FastLC  mul (const)" 100000 fun _ => fastX * fastY
  bench "UltraLC mul (const)" 100000 fun _ => ultraX * ultraY
  IO.println ""

  -- 2-term polynomials (common in derivatives)
  let fastPoly2a := LeviCivita.Fast.FastLC.ofFloat 1.0 + LeviCivita.Fast.FastLC.epsilon
  let fastPoly2b := LeviCivita.Fast.FastLC.ofFloat 2.0 + LeviCivita.Fast.FastLC.H
  let ultraPoly2a := LeviCivita.UltraFast.LC.ofFloat 1.0 + LeviCivita.UltraFast.LC.epsilon
  let ultraPoly2b := LeviCivita.UltraFast.LC.ofFloat 2.0 + LeviCivita.UltraFast.LC.H

  IO.println "── 2-term polynomial operations ──"
  bench "FastLC  add (2-term)" 50000 fun _ => fastPoly2a + fastPoly2b
  bench "UltraLC add (2-term)" 50000 fun _ => ultraPoly2a + ultraPoly2b
  IO.println ""
  bench "FastLC  mul (2-term)" 50000 fun _ => fastPoly2a * fastPoly2b
  bench "UltraLC mul (2-term)" 50000 fun _ => ultraPoly2a * ultraPoly2b
  IO.println ""

  -- 3-term polynomials
  let fastPoly3 := LeviCivita.Fast.FastLC.ofFloat 1.0 + LeviCivita.Fast.FastLC.epsilon + LeviCivita.Fast.FastLC.epsilon * LeviCivita.Fast.FastLC.epsilon
  let ultraPoly3 := LeviCivita.UltraFast.LC.ofFloat 1.0 + LeviCivita.UltraFast.LC.epsilon + LeviCivita.UltraFast.LC.epsilon * LeviCivita.UltraFast.LC.epsilon

  IO.println "── 3-term polynomial operations ──"
  bench "FastLC  mul (3-term)" 20000 fun _ => fastPoly3 * fastPoly3
  bench "UltraLC mul (3-term)" 20000 fun _ => ultraPoly3 * ultraPoly3
  IO.println ""

  -- Power operations
  IO.println "── Power operations ──"
  bench "FastLC  x^5" 20000 fun _ => fastPoly2a ^ 5
  bench "UltraLC x^5" 20000 fun _ => ultraPoly2a ^ 5
  IO.println ""
  bench "FastLC  x^10" 10000 fun _ => fastPoly2a ^ 10
  bench "UltraLC x^10" 10000 fun _ => ultraPoly2a ^ 10
  IO.println ""

  -- Derivative computation
  IO.println "── Derivative computation ──"
  let f_fast := fun (x : LeviCivita.Fast.FastLC.LC) => x * x * x
  let f_ultra := fun (x : LeviCivita.UltraFast.LC) => x * x * x
  bench "FastLC  d/dx(x³)" 20000 fun _ => LeviCivita.Fast.FastLC.derivative f_fast (LeviCivita.Fast.FastLC.ofFloat 2.0)
  bench "UltraLC d/dx(x³)" 20000 fun _ => LeviCivita.UltraFast.LC.derivative f_ultra (LeviCivita.UltraFast.LC.ofFloat 2.0)
  IO.println ""

  -- Verify correctness
  IO.println "════════════════════════════════════════════════════════"
  IO.println "         Correctness Verification"
  IO.println "════════════════════════════════════════════════════════"
  IO.println ""

  let fastDeriv := LeviCivita.Fast.FastLC.derivative (fun x => x * x * x) (LeviCivita.Fast.FastLC.ofFloat 2.0)
  let ultraDeriv := LeviCivita.UltraFast.LC.derivative (fun x => x * x * x) (LeviCivita.UltraFast.LC.ofFloat 2.0)
  IO.println s!"d/dx(x³) at x=2:"
  IO.println s!"  FastLC:  {fastDeriv}"
  IO.println s!"  UltraLC: {ultraDeriv}"
  IO.println s!"  Expected: 12.0"
  IO.println ""

  let fastDeriv5 := LeviCivita.Fast.FastLC.derivative (fun x => x * x * x * x * x) (LeviCivita.Fast.FastLC.ofFloat 3.0)
  let ultraDeriv5 := LeviCivita.UltraFast.LC.derivative (fun x => x * x * x * x * x) (LeviCivita.UltraFast.LC.ofFloat 3.0)
  IO.println s!"d/dx(x⁵) at x=3:"
  IO.println s!"  FastLC:  {fastDeriv5}"
  IO.println s!"  UltraLC: {ultraDeriv5}"
  IO.println s!"  Expected: 405.0"

end LeviCivita.Bench
