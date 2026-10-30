import LeviCivita.Analysis
import LeviCivita.Geometry

/-!
# `lake test`: analysis and differential-geometry checks

Every check compares against a closed-form value (curvature of spheres,
hyperbolic space, Schwarzschild, …). Exit code 1 on any failure.
-/

open LeviCivita.Fast FastLC
open LeviCivita.Geometry

structure Check where
  name : String
  ok : Bool
  detail : String

def π : Float := 3.141592653589793

def approx (a b : Float) (tol : Float := 1e-9) : Bool := (a - b).abs ≤ tol * (1.0 + b.abs)

def check (name : String) (got want : Float) (tol : Float := 1e-9) : Check :=
  { name, ok := approx got want tol, detail := s!"got {got}, want {want}" }

def checkSmall (name : String) (got : Float) (tol : Float := 1e-9) : Check :=
  { name, ok := got.abs ≤ tol, detail := s!"|·| = {got}" }

def pt (xs : List Float) {n : Nat} : Fin n → Float := fun i => xs.getD i.val 0.0

def jet {n : Nat} (g : Metric n) (x : List Float) : MetricJet := (MetricJet.at? g (pt x)).get!

def analysisChecks : List Check :=
  let a := 0.7
  let sx := sin (ofFloat a + epsilon)
  let ex := exp (ofFloat a + epsilon)
  let lx := log (ofFloat a + epsilon)
  let px := rpow (ofFloat a + epsilon) 2.5
  [ check "sin jet ε¹" (epsCoeff sx 1) (Float.cos a),
    check "sin jet ε² = −sin/2" (epsCoeff sx 2) (-(Float.sin a) / 2),
    check "sin jet ε³ = −cos/6" (epsCoeff sx 3) (-(Float.cos a) / 6),
    check "exp jet ε²" (epsCoeff ex 2) (Float.exp a / 2),
    check "log jet ε² = −1/(2a²)" (epsCoeff lx 2) (-1 / (2 * a * a)),
    check "rpow jet ε² = p(p−1)a^(p−2)/2" (epsCoeff px 2) (2.5 * 1.5 * Float.pow a 0.5 / 2),
    check "sin² + cos² = 1 through ε⁴"
      (let s := sin (ofFloat a + epsilon); let c := cos (ofFloat a + epsilon)
       (List.range 5).foldl (fun m k => m + (epsCoeff (s * s + c * c) k - if k == 0 then 1 else 0).abs) 0)
      0 1e-12,
    check "exp ∘ log = id (ε² coefficient)" (epsCoeff (exp (log (ofFloat a + epsilon))) 2) 0 1e-12 ]

def geometryChecks : List Check :=
  let r := 2.0
  let θ := 0.9
  let S2 := jet (sphere2 r) [θ, 0.3]
  let Γ := S2.christoffel
  let S3 := jet (sphere3 r) [0.8, 1.1, 0.2]
  let Hp := jet hyperbolicPlane [0.4, 1.7]
  let Fp := jet flatPolar [1.3, 0.4]
  let M := 1.0
  let rs := 5.0
  let Sch := jet (schwarzschild M) [0.0, rs, 1.0, 0.5]
  let T := jet (torus 3 1) [0.6, 0.0]
  -- unit 2-sphere embedded in ℝ³; induced metric must equal sphere2 1
  let emb : Coords 2 → Fin 3 → LC := fun x a =>
    match a.val with
    | 0 => sin (x 0) * cos (x 1)
    | 1 => sin (x 0) * sin (x 1)
    | _ => cos (x 0)
  let Ind := jet (induced emb) [θ, 0.3]
  -- great-circle geodesic on the unit sphere starting on the equator heading NE
  let traj := geodesic (sphere2 1) #[π / 2, 0.0] #[0.6, 0.8] 0.01 300
  let last := traj.back!
  let normStart := (jet (sphere2 1) [π / 2, 0.0]).norm2 #[0.6, 0.8]
  let normEnd := (jet (sphere2 1) [last.x[0]!, last.x[1]!]).norm2 last.v
  -- embedded point on the sphere for the great-circle test
  let toR3 := fun (s : GeodesicState) =>
    #[Float.sin s.x[0]! * Float.cos s.x[1]!, Float.sin s.x[0]! * Float.sin s.x[1]!, Float.cos s.x[0]!]
  let p0 := toR3 traj[0]!; let p1 := toR3 traj[50]!
  let nrm := #[p0[1]! * p1[2]! - p0[2]! * p1[1]!, p0[2]! * p1[0]! - p0[0]! * p1[2]!, p0[0]! * p1[1]! - p0[1]! * p1[0]!]
  let offPlane := traj.foldl (fun m s => let q := toR3 s
    max m (q[0]! * nrm[0]! + q[1]! * nrm[1]! + q[2]! * nrm[2]!).abs) 0.0
  -- Schwarzschild circular-ish orbit: conserved E = f ṫ and L = r² φ̇
  let f := fun (r : Float) => 1 - 2 * M / r
  let orbit := geodesic (schwarzschild M) #[0, 8, π / 2, 0] #[1.2, 0, 0, 0.04] 0.05 400
  let EL := fun (s : GeodesicState) => (f s.x[1]! * s.v[0]!, s.x[1]! * s.x[1]! * s.v[3]!)
  let (E0, L0) := EL orbit[0]!
  let (E1, L1) := EL orbit.back!
  -- holonomy: parallel transport around the equator (a geodesic) keeps the angle with ẋ
  let (_, w) := (parallelTransport (sphere2 1) #[π / 2, 0] #[0, 1] #[1, 0] 0.01 628).get!
  [ check "S² Γ^θ_φφ = −sinθ cosθ" (Γ.get [0, 1, 1]) (-(Float.sin θ) * Float.cos θ),
    check "S² Γ^φ_θφ = cotθ" (Γ.get [1, 0, 1]) (Float.cos θ / Float.sin θ),
    check "S² scalar curvature = 2/r²" S2.scalarCurvature (2 / (r * r)) 1e-8,
    check "S² sectional curvature = 1/r²" (S2.sectional #[1, 0] #[0, 1]) (1 / (r * r)) 1e-8,
    check "S² R^θ_φθφ = sin²θ" (S2.riemann.get [0, 1, 0, 1]) (Float.sin θ ^ 2) 1e-8,
    check "S³ scalar curvature = 6/r²" S3.scalarCurvature (6 / (r * r)) 1e-8,
    check "S³ Ricci = (2/r²) g" ((S3.ricci.get [1, 1]) / (S3.g.get [1, 1])) (2 / (r * r)) 1e-8,
    check "H² scalar curvature = −2" Hp.scalarCurvature (-2) 1e-8,
    checkSmall "flat polar: Riemann = 0" Fp.riemann.maxAbs 1e-10,
    check "torus Gaussian curvature = cos u/(ρ(R+ρ cos u))" (T.scalarCurvature / 2)
      (Float.cos 0.6 / (1 * (3 + Float.cos 0.6))) 1e-8,
    checkSmall "Schwarzschild is Ricci-flat" Sch.ricci.maxAbs 1e-10,
    check "Schwarzschild Kretschmann = 48M²/r⁶" Sch.kretschmann (48 * M * M / rs ^ 6) 1e-8,
    checkSmall "Schwarzschild Einstein tensor = 0" Sch.einstein.maxAbs 1e-10,
    checkSmall "Riemann antisymmetric in last pair"
      (let R := Sch.riemann; (Tensor.ofFn 4 4 fun | [a, b, c, d] => R.get [a, b, c, d] + R.get [a, b, d, c] | _ => 0).maxAbs) 1e-12,
    checkSmall "R_abcd = R_cdab"
      (let R := S3.riemannLower; (Tensor.ofFn 3 4 fun | [a, b, c, d] => R.get [a, b, c, d] - R.get [c, d, a, b] | _ => 0).maxAbs) 1e-10,
    checkSmall "first Bianchi identity R^a_[bcd] = 0"
      (let R := Sch.riemann; (Tensor.ofFn 4 4 fun
        | [a, b, c, d] => R.get [a, b, c, d] + R.get [a, c, d, b] + R.get [a, d, b, c] | _ => 0).maxAbs) 1e-10,
    checkSmall "∇g = 0 on Schwarzschild" ((metricCompatibility (schwarzschild M) (pt [0, 4, 1.2, 0])).get!.maxAbs) 1e-10,
    checkSmall "∇g = 0 on S³" ((metricCompatibility (sphere3 1) (pt [0.4, 0.9, 0])).get!.maxAbs) 1e-10,
    checkSmall "induced metric of S² ⊂ ℝ³ = round metric" (Tensor.maxDiff Ind.g (jet (sphere2 1) [θ, 0.3]).g) 1e-12,
    check "induced S² ⊂ ℝ³ scalar curvature = 2" Ind.scalarCurvature 2 1e-7,
    check "∇ᵢVᵏ of the rotation field ∂_φ on S²: ∇_θ V^φ = cotθ"
      ((covariantDerivVector (sphere2 1) (fun _ k => if k.val == 1 then 1 else 0) (pt [θ, 0])).get!.get [0, 1])
      (Float.cos θ / Float.sin θ),
    checkSmall "Killing field ∂_φ: ∇_(i V_j) = 0"
      (let D := (covariantDerivCovector (sphere2 1) (fun x k => if k.val == 1 then sin (x 0) * sin (x 0) else 0) (pt [θ, 0])).get!
       (D.get [0, 1] + D.get [1, 0]).abs + (D.get [0, 0]).abs + (D.get [1, 1]).abs) 1e-12,
    check "geodesic keeps |v|²" normEnd normStart 1e-8,
    checkSmall "geodesic on S² is a great circle" offPlane 1e-6,
    check "Schwarzschild geodesic conserves E" E1 E0 1e-7,
    check "Schwarzschild geodesic conserves L" L1 L0 1e-7,
    check "parallel transport around the equator: no rotation" w[0]! 1 1e-6 ]

def main : IO UInt32 := do
  let all := analysisChecks ++ geometryChecks
  let mut failed := 0
  for c in all do
    if c.ok then IO.println s!"  ok    {c.name}"
    else
      failed := failed + 1
      IO.println s!"  FAIL  {c.name}: {c.detail}"
  IO.println s!"{all.length - failed}/{all.length} passed"
  return if failed == 0 then 0 else 1
