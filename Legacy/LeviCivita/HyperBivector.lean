import LeviCivita.Fast

/-!
# Hyperfinite Bivectors

Bivectors with Levi-Civita coefficients, enabling automatic differentiation
of bivector-valued functions.
-/

set_option linter.missingDocs false

namespace LeviCivita.Hyper

open LeviCivita.Fast

/-! ## Hyperfinite Bivector in 3D -/

/-- A 3D bivector with hyperfinite (Levi-Civita) coefficients.
    Components: xy (e12), xz (e13), yz (e23) -/
structure Bivector3 where
  xy : FastLC.LC  -- coefficient of e12
  xz : FastLC.LC  -- coefficient of e13
  yz : FastLC.LC  -- coefficient of e23
deriving Inhabited, Repr

namespace Bivector3

/-- Zero bivector -/
def zero : Bivector3 := ⟨0, 0, 0⟩

/-- From standard Float components -/
def ofFloats (xy xz yz : Float) : Bivector3 :=
  ⟨FastLC.ofFloat xy, FastLC.ofFloat xz, FastLC.ofFloat yz⟩

instance : Zero Bivector3 where zero := zero

instance : Add Bivector3 where
  add a b := ⟨a.xy + b.xy, a.xz + b.xz, a.yz + b.yz⟩

instance : Neg Bivector3 where
  neg a := ⟨-a.xy, -a.xz, -a.yz⟩

instance : Sub Bivector3 where
  sub a b := a + (-b)

/-- Scalar multiplication by LC -/
instance : HMul FastLC.LC Bivector3 Bivector3 where
  hMul s b := ⟨s * b.xy, s * b.xz, s * b.yz⟩

/-- Scalar multiplication by Float -/
def smulFloat (s : Float) (b : Bivector3) : Bivector3 :=
  FastLC.ofFloat s * b

/-- Squared norm (negative of geometric product with itself for bivectors) -/
def normSq (b : Bivector3) : FastLC.LC :=
  b.xy * b.xy + b.xz * b.xz + b.yz * b.yz

/-- Wedge product of two vectors to bivector -/
def wedge (v1 v2 : Float × Float × Float) : Bivector3 :=
  let (x1, y1, z1) := v1
  let (x2, y2, z2) := v2
  ⟨FastLC.ofFloat (x1 * y2 - x2 * y1),   -- xy component
   FastLC.ofFloat (x1 * z2 - x2 * z1),   -- xz component
   FastLC.ofFloat (y1 * z2 - y2 * z1)⟩   -- yz component

/-- Standard parts of coefficients -/
def std (b : Bivector3) : Float × Float × Float :=
  (FastLC.std b.xy, FastLC.std b.xz, FastLC.std b.yz)

instance : ToString Bivector3 where
  toString b :=
    let parts := #[
      if b.xy.terms.isEmpty then "" else s!"{b.xy}e12",
      if b.xz.terms.isEmpty then "" else s!"{b.xz}e13",
      if b.yz.terms.isEmpty then "" else s!"{b.yz}e23"
    ].filter (· != "")
    if parts.isEmpty then "0" else String.intercalate " + " parts.toList

end Bivector3

/-! ## Hyperfinite Vector in 3D -/

/-- A 3D vector with hyperfinite coefficients -/
structure Vector3 where
  x : FastLC.LC
  y : FastLC.LC
  z : FastLC.LC
deriving Inhabited, Repr

namespace Vector3

def zero : Vector3 := ⟨0, 0, 0⟩

def ofFloats (x y z : Float) : Vector3 :=
  ⟨FastLC.ofFloat x, FastLC.ofFloat y, FastLC.ofFloat z⟩

instance : Zero Vector3 where zero := zero

instance : Add Vector3 where
  add a b := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

instance : Neg Vector3 where
  neg a := ⟨-a.x, -a.y, -a.z⟩

instance : Sub Vector3 where
  sub a b := a + (-b)

instance : HMul FastLC.LC Vector3 Vector3 where
  hMul s v := ⟨s * v.x, s * v.y, s * v.z⟩

def smulFloat (s : Float) (v : Vector3) : Vector3 :=
  FastLC.ofFloat s * v

/-- Dot product -/
def dot (a b : Vector3) : FastLC.LC :=
  a.x * b.x + a.y * b.y + a.z * b.z

/-- Cross product -/
def cross (a b : Vector3) : Vector3 :=
  ⟨a.y * b.z - a.z * b.y,
   a.z * b.x - a.x * b.z,
   a.x * b.y - a.y * b.x⟩

/-- Squared norm -/
def normSq (v : Vector3) : FastLC.LC :=
  v.x * v.x + v.y * v.y + v.z * v.z

/-- Standard parts -/
def std (v : Vector3) : Float × Float × Float :=
  (FastLC.std v.x, FastLC.std v.y, FastLC.std v.z)

/-- Wedge product of two vectors -/
def wedge (v1 v2 : Vector3) : Bivector3 :=
  ⟨v1.x * v2.y - v1.y * v2.x,   -- xy
   v1.x * v2.z - v1.z * v2.x,   -- xz
   v1.y * v2.z - v1.z * v2.y⟩   -- yz

instance : ToString Vector3 where
  toString v :=
    s!"({v.x}, {v.y}, {v.z})"

end Vector3

/-! ## Rotor (Spinor) with Hyperfinite Coefficients -/

/-- A rotor in 3D: scalar + bivector representation -/
structure Rotor3 where
  scalar : FastLC.LC   -- cos(theta/2) term
  biv : Bivector3  -- sin(theta/2)*B term
deriving Inhabited, Repr

namespace Rotor3

/-- Identity rotor (no rotation) -/
def one : Rotor3 := ⟨1, Bivector3.zero⟩

/-- From angle (radians) and axis (unit bivector) -/
def fromAngleAxis (angle : Float) (axis : Bivector3) : Rotor3 :=
  let halfAngle := angle / 2.0
  let c := FastLC.ofFloat (Float.cos halfAngle)
  let s := FastLC.ofFloat (Float.sin halfAngle)
  ⟨c, s * axis⟩

/-- Rotor multiplication (geometric product) -/
def mul (r1 r2 : Rotor3) : Rotor3 :=
  -- (a + B1)(c + B2) = ac + aB2 + cB1 + B1B2
  -- For bivectors in 3D: B1B2 = -B1.B2 + B1xB2 (as bivector)
  -- Simplified: assume orthogonal bivectors for now
  let scalarPart := r1.scalar * r2.scalar -
    (r1.biv.xy * r2.biv.xy + r1.biv.xz * r2.biv.xz + r1.biv.yz * r2.biv.yz)
  let bivPart : Bivector3 :=
    ⟨r1.scalar * r2.biv.xy + r2.scalar * r1.biv.xy +
       (r1.biv.xz * r2.biv.yz - r1.biv.yz * r2.biv.xz),
     r1.scalar * r2.biv.xz + r2.scalar * r1.biv.xz +
       (r1.biv.yz * r2.biv.xy - r1.biv.xy * r2.biv.yz),
     r1.scalar * r2.biv.yz + r2.scalar * r1.biv.yz +
       (r1.biv.xy * r2.biv.xz - r1.biv.xz * r2.biv.xy)⟩
  ⟨scalarPart, bivPart⟩

instance : Mul Rotor3 where mul := mul
instance : One Rotor3 where one := one

/-- Reverse (conjugate) of rotor: a - B -/
def reverse (r : Rotor3) : Rotor3 := ⟨r.scalar, -r.biv⟩

/-- Rotate a vector by this rotor: v' = R*v*rev(R) -/
def rotate (r : Rotor3) (v : Vector3) : Vector3 :=
  -- Full sandwich product R*v*rev(R)
  -- For a rotor R = a + B and vector v:
  -- R*v*rev(R) projects v and rotates in the plane of B

  -- Simplified formula for unit rotor:
  -- v' = v + 2a(BxV) + 2Bx(BxV)
  -- where BxV is the commutator [B,v]/2

  -- For 3D with bivector B = b12*e12 + b13*e13 + b23*e23 and vector v = (x,y,z):
  -- B acting on v gives rotation in planes

  let a := r.scalar
  let b12 := r.biv.xy
  let b13 := r.biv.xz
  let b23 := r.biv.yz

  -- Compute 2B×v (cross product with dual vector of bivector)
  -- dual(B) = (b23, -b13, b12) in 3D
  let dualB : Vector3 := ⟨b23, -b13, b12⟩
  let crossBv := Vector3.cross dualB v

  -- v' ≈ v + 2a·crossBv + 2·cross(dualB, crossBv)
  let term1 := v
  let term2 := (FastLC.ofFloat 2.0 * a) * crossBv
  let term3 := FastLC.ofFloat 2.0 * (Vector3.cross dualB crossBv)

  term1 + term2 + term3

instance : ToString Rotor3 where
  toString r := s!"{r.scalar} + {r.biv}"

end Rotor3

/-! ## Derivatives of Bivector and Rotor Functions -/

/-- Derivative of a vector-valued function at a point -/
def vectorDerivative (f : FastLC.LC → Vector3) (pt : FastLC.LC) : Vector3 :=
  let delta := f (pt + FastLC.epsilon) - f pt
  let dx := delta.x * FastLC.H
  let dy := delta.y * FastLC.H
  let dz := delta.z * FastLC.H
  ⟨FastLC.ofFloat (FastLC.std dx),
   FastLC.ofFloat (FastLC.std dy),
   FastLC.ofFloat (FastLC.std dz)⟩

/-- Derivative of a bivector-valued function at a point -/
def bivectorDerivative (f : FastLC.LC → Bivector3) (pt : FastLC.LC) : Bivector3 :=
  let delta := f (pt + FastLC.epsilon) - f pt
  let dxy := delta.xy * FastLC.H
  let dxz := delta.xz * FastLC.H
  let dyz := delta.yz * FastLC.H
  ⟨FastLC.ofFloat (FastLC.std dxy),
   FastLC.ofFloat (FastLC.std dxz),
   FastLC.ofFloat (FastLC.std dyz)⟩

/-- Derivative of a rotor-valued function at a point -/
def rotorDerivative (f : FastLC.LC → Rotor3) (pt : FastLC.LC) : Rotor3 :=
  let delta_scalar := (f (pt + FastLC.epsilon)).scalar - (f pt).scalar
  let delta_biv := (f (pt + FastLC.epsilon)).biv - (f pt).biv
  let ds := delta_scalar * FastLC.H
  let dxy := delta_biv.xy * FastLC.H
  let dxz := delta_biv.xz * FastLC.H
  let dyz := delta_biv.yz * FastLC.H
  ⟨FastLC.ofFloat (FastLC.std ds),
   ⟨FastLC.ofFloat (FastLC.std dxy),
    FastLC.ofFloat (FastLC.std dxz),
    FastLC.ofFloat (FastLC.std dyz)⟩⟩

/-! ## Angular Velocity from Rotor -/

/-- Compute angular velocity from time-varying rotor -/
def angularVelocity (R : FastLC.LC → Rotor3) (t : FastLC.LC) : Bivector3 :=
  let dR := rotorDerivative R t
  let Rrev := Rotor3.reverse (R t)
  let product := dR * Rrev
  -- Angular velocity bivector is 2× the bivector part
  Bivector3.smulFloat 2.0 product.biv

end LeviCivita.Hyper
