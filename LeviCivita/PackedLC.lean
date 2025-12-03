import Std

/-!
# Packed Levi-Civita Numbers

Uses FloatArray (packed doubles) to avoid boxing overhead.
No extern C - pure Lean but with efficient storage.
-/

set_option linter.missingDocs false

namespace LeviCivita.Packed

/-! ## PackedLC - FloatArray storage, pure Lean ops

Uses FloatArray for packed storage - no boxing per element.
-/

/-- Packed LC with FloatArray storage (7 packed doubles). -/
structure LC where
  c : FloatArray  -- 7 elements for exps -3, -2, -1, 0, 1, 2, 3
deriving Inhabited

namespace LC

/-- Size bound proof helper. -/
private theorem size_7_bound : ∀ i, i < 7 → i < 7 := fun _ h => h

/-- Create a 7-element FloatArray filled with zeros. -/
@[inline] private def mkZeroArr : FloatArray :=
  FloatArray.empty.push 0.0 |>.push 0.0 |>.push 0.0 |>.push 0.0
    |>.push 0.0 |>.push 0.0 |>.push 0.0

/-- Create zero LC. -/
@[inline] def zero : LC := { c := mkZeroArr }
instance : Zero LC where zero := zero

/-- Create LC = 1. -/
@[inline] def one : LC := { c := mkZeroArr.set! 3 1.0 }
instance : One LC where one := one

/-- The infinitesimal epsilon (exp = -1, index = 2). -/
@[inline] def epsilon : LC := { c := mkZeroArr.set! 2 1.0 }

/-- The infinite unit H = 1/epsilon (exp = 1, index = 4). -/
@[inline] def H : LC := { c := mkZeroArr.set! 4 1.0 }

/-- From Float constant (exp = 0, index = 3). -/
@[inline] def ofFloat (x : Float) : LC := { c := mkZeroArr.set! 3 x }

instance : OfNat LC n where ofNat := ofFloat n.toFloat
instance : Coe Float LC where coe := ofFloat

-- Unchecked access - using get! since FloatArray.uget has USize issues
@[always_inline] private def get0 (a : FloatArray) : Float := a.get! 0
@[always_inline] private def get1 (a : FloatArray) : Float := a.get! 1
@[always_inline] private def get2 (a : FloatArray) : Float := a.get! 2
@[always_inline] private def get3 (a : FloatArray) : Float := a.get! 3
@[always_inline] private def get4 (a : FloatArray) : Float := a.get! 4
@[always_inline] private def get5 (a : FloatArray) : Float := a.get! 5
@[always_inline] private def get6 (a : FloatArray) : Float := a.get! 6

/-- Get coefficient at exponent. -/
@[inline] def getCoeff (x : LC) (exp : Int) : Float :=
  let idx := (exp + 3).toNat
  if idx < 7 then x.c.get! idx else 0.0

/-- Standard part (coefficient at exp 0). -/
@[inline] def std (x : LC) : Float := get3 x.c

/-- Addition - unrolled for speed. -/
@[always_inline] def add (x y : LC) : LC :=
  let a := x.c
  let b := y.c
  { c := FloatArray.empty
      |>.push (get0 a + get0 b)
      |>.push (get1 a + get1 b)
      |>.push (get2 a + get2 b)
      |>.push (get3 a + get3 b)
      |>.push (get4 a + get4 b)
      |>.push (get5 a + get5 b)
      |>.push (get6 a + get6 b) }

instance : Add LC where add := add

/-- Negation - unrolled. -/
@[always_inline] def neg (x : LC) : LC :=
  let a := x.c
  { c := FloatArray.empty
      |>.push (-get0 a) |>.push (-get1 a) |>.push (-get2 a) |>.push (-get3 a)
      |>.push (-get4 a) |>.push (-get5 a) |>.push (-get6 a) }

instance : Neg LC where neg := neg
instance : Sub LC where sub x y := x + (-y)

/-- Multiplication - unrolled convolution.
    result_k corresponds to exponent (k - 3).
    For exp_out = exp_a + exp_b, we have (i-3) + (j-3) = (k-3), so i + j = k + 3. -/
@[always_inline] def mul (x y : LC) : LC :=
  let a := x.c
  let b := y.c
  let a0 := get0 a; let a1 := get1 a; let a2 := get2 a; let a3 := get3 a
  let a4 := get4 a; let a5 := get5 a; let a6 := get6 a
  let b0 := get0 b; let b1 := get1 b; let b2 := get2 b; let b3 := get3 b
  let b4 := get4 b; let b5 := get5 b; let b6 := get6 b

  -- k=0: i+j=3 -> (0,3), (1,2), (2,1), (3,0)
  let c0 := a0*b3 + a1*b2 + a2*b1 + a3*b0

  -- k=1: i+j=4 -> (0,4), (1,3), (2,2), (3,1), (4,0)
  let c1 := a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0

  -- k=2: i+j=5 -> (0,5), (1,4), (2,3), (3,2), (4,1), (5,0)
  let c2 := a0*b5 + a1*b4 + a2*b3 + a3*b2 + a4*b1 + a5*b0

  -- k=3: i+j=6 -> (0,6), (1,5), (2,4), (3,3), (4,2), (5,1), (6,0)
  let c3 := a0*b6 + a1*b5 + a2*b4 + a3*b3 + a4*b2 + a5*b1 + a6*b0

  -- k=4: i+j=7 -> (1,6), (2,5), (3,4), (4,3), (5,2), (6,1)
  let c4 := a1*b6 + a2*b5 + a3*b4 + a4*b3 + a5*b2 + a6*b1

  -- k=5: i+j=8 -> (2,6), (3,5), (4,4), (5,3), (6,2)
  let c5 := a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2

  -- k=6: i+j=9 -> (3,6), (4,5), (5,4), (6,3)
  let c6 := a3*b6 + a4*b5 + a5*b4 + a6*b3

  { c := FloatArray.empty.push c0 |>.push c1 |>.push c2 |>.push c3
      |>.push c4 |>.push c5 |>.push c6 }

instance : Mul LC where mul := mul

/-- Scalar multiplication. -/
@[always_inline] def smul (s : Float) (x : LC) : LC :=
  let a := x.c
  { c := FloatArray.empty
      |>.push (s * get0 a) |>.push (s * get1 a) |>.push (s * get2 a)
      |>.push (s * get3 a) |>.push (s * get4 a) |>.push (s * get5 a)
      |>.push (s * get6 a) }

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
@[always_inline] def derivative (f : LC → LC) (pt : LC) : Float :=
  let result := f (pt + epsilon)
  get2 result.c  -- index 2 = exp -1

instance : ToString LC where
  toString x := Id.run do
    let names := #["ε³", "ε²", "ε", "", "H", "H²", "H³"]
    let mut parts : Array String := #[]
    for i in [:7] do
      let coeff := x.c.get! i
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

end LeviCivita.Packed
