import Std
import LeviCivita.Fast

/-!
# Compact Levi-Civita for Automatic Differentiation

Ultra-optimized LC for the common AD case:
- Exponents are small integers: -3 to +3
- Fixed array storage eliminates sorting
-/

set_option linter.missingDocs false

namespace LeviCivita.Compact

/-! ## CompactLC - Fixed exponent range for maximum speed

Stores coefficients for exponents -3 to +3.
Index mapping: exp e maps to index (e + 3)
-/

/-- Number of exponent slots. -/
def numSlots : Nat := 7

/-- Offset to convert exponent to index. -/
def expOffset : Int := 3

/-- Compact LC with fixed exponent slots. -/
structure LC where
  c : Array Float  -- 7 elements for exps -3, -2, -1, 0, 1, 2, 3
deriving Inhabited

namespace LC

/-- Zero array. -/
private def zeroArr : Array Float := #[0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]

/-- Create zero LC. -/
@[inline] def zero : LC := { c := zeroArr }
instance : Zero LC where zero := zero

/-- Create LC = 1. -/
@[inline] def one : LC := { c := #[0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0] }
instance : One LC where one := one

/-- The infinitesimal epsilon (exp = -1, index = 2). -/
@[inline] def epsilon : LC := { c := #[0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0] }

/-- The infinite unit H = 1/epsilon (exp = 1, index = 4). -/
@[inline] def H : LC := { c := #[0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0] }

/-- From Float constant (exp = 0, index = 3). -/
@[inline] def ofFloat (x : Float) : LC :=
  { c := #[0.0, 0.0, 0.0, x, 0.0, 0.0, 0.0] }

instance : OfNat LC n where ofNat := ofFloat n.toFloat
instance : Coe Float LC where coe := ofFloat

/-- Get coefficient at exponent. -/
@[inline] def getCoeff (x : LC) (exp : Int) : Float :=
  let idx := (exp + expOffset).toNat
  if idx < 7 then x.c[idx]! else 0.0

/-- Standard part (coefficient at exp 0). -/
@[inline] def std (x : LC) : Float := x.c[3]!

/-- Addition - element-wise. -/
@[inline] def add (x y : LC) : LC :=
  { c := #[x.c[0]! + y.c[0]!, x.c[1]! + y.c[1]!, x.c[2]! + y.c[2]!,
           x.c[3]! + y.c[3]!, x.c[4]! + y.c[4]!, x.c[5]! + y.c[5]!,
           x.c[6]! + y.c[6]!] }

instance : Add LC where add := add

/-- Negation. -/
@[inline] def neg (x : LC) : LC :=
  { c := #[-x.c[0]!, -x.c[1]!, -x.c[2]!, -x.c[3]!, -x.c[4]!, -x.c[5]!, -x.c[6]!] }

instance : Neg LC where neg := neg
instance : Sub LC where sub x y := x + (-y)

/-- Multiplication - convolution with truncation. -/
def mul (x y : LC) : LC := Id.run do
  let mut c := zeroArr

  -- Unrolled multiplication: c[k] = sum of x[i] * y[j] where i + j - 6 = k - 3
  -- That is, exp_i + exp_j = exp_k, where exp_i = i - 3

  -- idx 0 (exp -3): from (0,0), but also check (1,-1), (2,-2) etc
  -- More directly: for output idx k, we sum x[i]*y[j] where i+j = k+3-3+3 = k+3? No...
  -- exp_out = (i-3) + (j-3) = i + j - 6
  -- idx_out = exp_out + 3 = i + j - 3
  -- So for idx_out in [0..6], we need i + j = idx_out + 3 in [3..9]

  for i in [:7] do
    for j in [:7] do
      let outIdx := i + j
      if outIdx >= 3 && outIdx <= 9 then
        let k := outIdx - 3
        if k < 7 then
          c := c.set! k (c[k]! + x.c[i]! * y.c[j]!)

  { c }

instance : Mul LC where mul := mul

/-- Scalar multiplication. -/
@[inline] def smul (s : Float) (x : LC) : LC :=
  { c := #[s * x.c[0]!, s * x.c[1]!, s * x.c[2]!, s * x.c[3]!,
           s * x.c[4]!, s * x.c[5]!, s * x.c[6]!] }

instance : HMul Float LC LC where hMul := smul

/-- Power via binary exponentiation. -/
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

/-- Derivative using infinitesimal. -/
@[inline] def derivative (f : LC → LC) (pt : LC) : Float :=
  let result := f (pt + epsilon)
  -- The epsilon coefficient of f(x+epsilon) is f'(x)
  result.c[2]!  -- index 2 = exp -1

instance : ToString LC where
  toString x := Id.run do
    let names := #["ε³", "ε²", "ε", "", "H", "H²", "H³"]
    let mut parts : Array String := #[]
    for i in [:7] do
      let coeff := x.c[i]!
      if coeff.abs > 1e-15 then
        let name := names[i]!
        if name == "" then
          parts := parts.push s!"{coeff}"
        else if coeff == 1.0 then
          parts := parts.push name
        else if coeff == -1.0 then
          parts := parts.push s!"-{name}"
        else
          parts := parts.push s!"{coeff}{name}"
    if parts.isEmpty then "0" else String.intercalate " + " parts.toList

end LC

end LeviCivita.Compact

/-! ## Benchmarks -/

namespace LeviCivita.CompactBench

def bench (name : String) (iters : Nat) (f : Unit → α) : IO Unit := do
  for _ in [:50] do let _ := f ()
  let start ← IO.monoMsNow
  for _ in [:iters] do let _ := f ()
  let elapsed := (← IO.monoMsNow) - start
  let opsPerSec := if elapsed > 0 then (iters.toFloat * 1000.0) / elapsed.toFloat else 0.0
  IO.println s!"{name}: {elapsed}ms for {iters} iters ({opsPerSec.round} ops/sec)"

#eval do
  IO.println "════════════════════════════════════════════════════════"
  IO.println "         CompactLC vs FastLC Benchmarks"
  IO.println "════════════════════════════════════════════════════════"
  IO.println ""

  let fastX := LeviCivita.Fast.FastLC.ofFloat 3.14159
  let fastY := LeviCivita.Fast.FastLC.ofFloat 2.71828
  let compactX := LeviCivita.Compact.LC.ofFloat 3.14159
  let compactY := LeviCivita.Compact.LC.ofFloat 2.71828

  IO.println "── Constant operations ──"
  bench "FastLC    add" 100000 fun _ => fastX + fastY
  bench "CompactLC add" 100000 fun _ => compactX + compactY
  bench "FastLC    mul" 100000 fun _ => fastX * fastY
  bench "CompactLC mul" 100000 fun _ => compactX * compactY
  IO.println ""

  let fastPoly2a := LeviCivita.Fast.FastLC.ofFloat 1.0 + LeviCivita.Fast.FastLC.epsilon
  let fastPoly2b := LeviCivita.Fast.FastLC.ofFloat 2.0 + LeviCivita.Fast.FastLC.H
  let compactPoly2a := LeviCivita.Compact.LC.ofFloat 1.0 + LeviCivita.Compact.LC.epsilon
  let compactPoly2b := LeviCivita.Compact.LC.ofFloat 2.0 + LeviCivita.Compact.LC.H

  IO.println "── 2-term polynomial operations ──"
  bench "FastLC    add (2-term)" 50000 fun _ => fastPoly2a + fastPoly2b
  bench "CompactLC add (2-term)" 50000 fun _ => compactPoly2a + compactPoly2b
  bench "FastLC    mul (2-term)" 50000 fun _ => fastPoly2a * fastPoly2b
  bench "CompactLC mul (2-term)" 50000 fun _ => compactPoly2a * compactPoly2b
  IO.println ""

  IO.println "── Power operations ──"
  bench "FastLC    x^5" 20000 fun _ => fastPoly2a ^ 5
  bench "CompactLC x^5" 20000 fun _ => compactPoly2a ^ 5
  bench "FastLC    x^10" 10000 fun _ => fastPoly2a ^ 10
  bench "CompactLC x^10" 10000 fun _ => compactPoly2a ^ 10
  IO.println ""

  IO.println "── Derivative computation ──"
  bench "FastLC    d/dx(x³)" 50000 fun _ =>
    LeviCivita.Fast.FastLC.derivative (fun x => x * x * x) (LeviCivita.Fast.FastLC.ofFloat 2.0)
  bench "CompactLC d/dx(x³)" 50000 fun _ =>
    LeviCivita.Compact.LC.derivative (fun x => x * x * x) (LeviCivita.Compact.LC.ofFloat 2.0)
  bench "FastLC    d/dx(x⁵)" 20000 fun _ =>
    LeviCivita.Fast.FastLC.derivative (fun x => x * x * x * x * x) (LeviCivita.Fast.FastLC.ofFloat 3.0)
  bench "CompactLC d/dx(x⁵)" 20000 fun _ =>
    LeviCivita.Compact.LC.derivative (fun x => x * x * x * x * x) (LeviCivita.Compact.LC.ofFloat 3.0)
  IO.println ""

  IO.println "════════════════════════════════════════════════════════"
  IO.println "         Correctness Verification"
  IO.println "════════════════════════════════════════════════════════"
  IO.println ""

  let fastDeriv := LeviCivita.Fast.FastLC.derivative (fun x => x * x * x) (LeviCivita.Fast.FastLC.ofFloat 2.0)
  let compactDeriv := LeviCivita.Compact.LC.derivative (fun x => x * x * x) (LeviCivita.Compact.LC.ofFloat 2.0)
  IO.println s!"d/dx(x³) at x=2: FastLC={fastDeriv}, CompactLC={compactDeriv}, expected=12.0"

  let fastDeriv5 := LeviCivita.Fast.FastLC.derivative (fun x => x * x * x * x * x) (LeviCivita.Fast.FastLC.ofFloat 3.0)
  let compactDeriv5 := LeviCivita.Compact.LC.derivative (fun x => x * x * x * x * x) (LeviCivita.Compact.LC.ofFloat 3.0)
  IO.println s!"d/dx(x⁵) at x=3: FastLC={fastDeriv5}, CompactLC={compactDeriv5}, expected=405.0"

end LeviCivita.CompactBench
