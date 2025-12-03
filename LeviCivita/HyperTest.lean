import LeviCivita.HyperBivector

-- Hyperfinite Bivector Tests
-- Demonstrates automatic differentiation of bivector and rotor-valued functions.

set_option linter.missingDocs false

namespace LeviCivita.Hyper.Test

open LeviCivita.Fast
open LeviCivita.Hyper

-- Test 1: Simple linear bivector field
-- A bivector that scales linearly: B(t) = t e12 + 2t e23
def linearBivector (t : FastLC.LC) : Bivector3 :=
  ⟨t, 0, FastLC.ofFloat 2.0 * t⟩

-- Test: derivative should be (1, 0, 2)
#eval do
  let t0 : FastLC.LC := 1
  let dB := bivectorDerivative linearBivector t0
  IO.println s!"Derivative of linear bivector: {dB.std}"
  IO.println s!"Expected: (1, 0, 2)"

-- Test 2: Quadratic bivector
-- B(t) = t^2 e12
def quadraticBivector (t : FastLC.LC) : Bivector3 :=
  ⟨t * t, 0, 0⟩

-- Test: derivative at t=3 should be 2*3 = 6
#eval do
  let t0 : FastLC.LC := 3
  let dB := bivectorDerivative quadraticBivector t0
  IO.println s!"Derivative of t^2 e12 at t=3: {dB.std}"
  IO.println s!"Expected: (6, 0, 0)"

-- Test 3: Cubic vector function
-- v(t) = (t^3, t^2, t)
def cubicVector (t : FastLC.LC) : Vector3 :=
  ⟨t * t * t, t * t, t⟩

-- Test: derivative at t=2 should be (12, 4, 1)
#eval do
  let t0 : FastLC.LC := 2
  let dv := vectorDerivative cubicVector t0
  IO.println s!"Derivative of (t^3, t^2, t) at t=2: {dv.std}"
  IO.println s!"Expected: (12, 4, 1)"

-- Test 4: Rotor derivative
-- Rotation rotor: R(t) = cos(t) + sin(t) e12
-- Uses LC-aware trig functions for automatic differentiation
def rotatingRotor (t : FastLC.LC) : Rotor3 :=
  ⟨FastLC.cos t,
   ⟨FastLC.sin t, 0, 0⟩⟩

#eval do
  let t0 : FastLC.LC := 0
  let dR := rotorDerivative rotatingRotor t0
  IO.println s!"Derivative of rotating rotor at t=0:"
  IO.println s!"  Scalar part: {FastLC.std dR.scalar}"
  IO.println s!"  Bivector part: {dR.biv.std}"
  IO.println s!"Expected: scalar=0, bivector=(1,0,0)"

-- Test 5: Angular Velocity
#eval do
  let t0 : FastLC.LC := 0
  let omega := angularVelocity rotatingRotor t0
  IO.println s!"Angular velocity of rotating rotor: {omega.std}"
  IO.println s!"Expected: (2, 0, 0) corresponding to 2 e12"

-- Test 6: Polynomial bivector
-- B(t) = t^3 e12 + t^2 e13 + t e23
def polynomialBivector (t : FastLC.LC) : Bivector3 :=
  ⟨t * t * t, t * t, t⟩

#eval do
  let t0 : FastLC.LC := 2
  let dB := bivectorDerivative polynomialBivector t0
  IO.println s!"Derivative of (t^3, t^2, t) bivector at t=2: {dB.std}"
  IO.println s!"Expected: (12, 4, 1)"

-- Benchmark: Many derivative computations
def benchDerivatives (n : Nat) : IO Unit := do
  let f := fun (t : FastLC.LC) => Vector3.mk (t * t * t) (t * t) t
  let mut sumX : Float := 0.0
  let mut sumY : Float := 0.0
  let mut sumZ : Float := 0.0
  let start ← IO.monoNanosNow
  for i in [0:n] do
    let t : FastLC.LC := FastLC.ofFloat (i.toFloat / n.toFloat)
    let dv := vectorDerivative f t
    let (x, y, z) := dv.std
    sumX := sumX + x
    sumY := sumY + y
    sumZ := sumZ + z
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"Computed {n} vector derivatives in {elapsed / 1000000}ms ({elapsed / n}ns/op)"
  IO.println s!"Checksum: ({sumX}, {sumY}, {sumZ})"

#eval benchDerivatives 1000

-- Test 7: Verify basic algebra
#eval do
  -- Test Vector3 operations
  let v1 := Vector3.ofFloats 1.0 2.0 3.0
  let v2 := Vector3.ofFloats 4.0 5.0 6.0
  let sum := v1 + v2
  IO.println s!"Vector sum: {sum.std}"
  IO.println s!"Expected: (5, 7, 9)"

  let cross := Vector3.cross v1 v2
  IO.println s!"Cross product: {cross.std}"
  IO.println s!"Expected: (-3, 6, -3)"

#eval do
  -- Test Bivector3 operations
  let b1 := Bivector3.ofFloats 1.0 2.0 3.0
  let b2 := Bivector3.ofFloats 4.0 5.0 6.0
  let sum := b1 + b2
  IO.println s!"Bivector sum: {sum.std}"
  IO.println s!"Expected: (5, 7, 9)"

end LeviCivita.Hyper.Test
