import LeviCivita.Analysis

/-!
# Riemannian geometry with exact derivatives

A metric is given as a function of coordinates written in Levi-Civita
arithmetic, `g : (Fin n → LC) → Fin n → Fin n → LC`. Evaluating it at a seed
`x + ε v` returns, for every component, `g(x)`, the directional derivative
`∂ᵥ g` (the `ε¹` coefficient) and half the second directional derivative
`½ ∂ᵥ∂ᵥ g` (the `ε²` coefficient), all exact up to Float rounding. Mixed
partials come from polarization:

    ∂ₖ∂ₗ g = c₂(eₖ + eₗ) − c₂(eₖ) − c₂(eₗ),    c₂(v) = ε²-coefficient of g(x + εv).

That 2-jet (`MetricJet`) is all the Levi-Civita connection and its curvature
need, so every quantity below is computed from closed-form formulas over the
jet — no finite-difference step sizes:

* `christoffel`: `Γᵏᵢⱼ = ½ gᵏˡ (∂ᵢ gⱼₗ + ∂ⱼ gᵢₗ − ∂ₗ gᵢⱼ)`
* `christoffelDeriv`: `∂ₘ Γᵏᵢⱼ`, using `∂ₘ gᵏˡ = −gᵏᵃ (∂ₘ gₐᵦ) gᵝˡ`
* `riemann`: `Rᵖ_σμν = ∂_μ Γᵖ_νσ − ∂_ν Γᵖ_μσ + Γᵖ_μλ Γˡ_νσ − Γᵖ_νλ Γˡ_μσ`
* `ricci` (`R_σν = Rᵖ_σρν`), `scalarCurvature`, `einstein`, `kretschmann`,
  `sectional`
* `covariantDerivVector`/`covariantDerivCovector`/`metricCompatibility`:
  `∇` of LC-valued tensor fields, again differentiated through `ε`
* `geodesicAccel`, `geodesic` (RK4 on `ẍᵏ = −Γᵏᵢⱼ ẋⁱ ẋʲ`), and
  `parallelTransport` along a geodesic.

Tensors are flat `Array Float`s in row-major index order; `Tensor.get` reads
them. Dimensions are small (≤ 4 or 5), so clarity wins over blocking.
-/

namespace LeviCivita.Geometry

open LeviCivita.Fast FastLC

/-- Coordinates of a point, as LC numbers (so the point can carry a seed). -/
abbrev Coords (n : Nat) := Fin n → LC

/-- A metric field: components `g x i j`, written in LC arithmetic. -/
abbrev Metric (n : Nat) := Coords n → Fin n → Fin n → LC

/-- A vector field `Vᵏ(x)` (or covector field `ωₖ(x)`). -/
abbrev VectorField (n : Nat) := Coords n → Fin n → LC

/-- A dense tensor with every index of range `n`, stored row-major. -/
structure Tensor where
  /-- Range of every index. -/
  n : Nat
  /-- Number of indices. -/
  rank : Nat
  /-- Components, `n ^ rank` of them. -/
  data : Array Float
  deriving Inhabited, Repr

namespace Tensor

/-- Flat offset of a multi-index. -/
@[inline] def offset (n : Nat) (idx : List Nat) : Nat := idx.foldl (fun acc i => acc * n + i) 0

/-- Component at a multi-index (`0` if out of range). -/
@[inline] def get (t : Tensor) (idx : List Nat) : Float := t.data.getD (offset t.n idx) 0.0

/-- Build from a component function of a list of indices. -/
def ofFn (n rank : Nat) (f : List Nat → Float) : Tensor :=
  { n, rank, data := (Array.range (n ^ rank)).map fun flat =>
      f ((List.range rank).reverse.map fun p => flat / n ^ p % n) }

/-- Largest absolute component. -/
def maxAbs (t : Tensor) : Float := t.data.foldl (fun m x => max m x.abs) 0.0

/-- Largest absolute difference of two equally shaped tensors. -/
def maxDiff (a b : Tensor) : Float :=
  (a.data.zip b.data).foldl (fun m (x, y) => max m (x - y).abs) 0.0

end Tensor

/-- Unit vector `eₖ` as a Float tuple. -/
@[inline] def basis (n : Nat) (k : Nat) : Fin n → Float := fun j => if j.val == k then 1.0 else 0.0

/-- Seed `x + ε v`. -/
@[inline] def seed {n : Nat} (x v : Fin n → Float) : Coords n :=
  fun j => ofFloat (x j) + smul (v j) epsilon

/-- Invert a dense `n × n` matrix (row-major) by Gauss–Jordan with partial
pivoting. Returns `none` for a singular matrix. -/
def invertMatrix (n : Nat) (m : Array Float) : Option (Array Float) := Id.run do
  let mut a := m
  let mut inv := Tensor.ofFn n 2 (fun | [i, j] => if i == j then 1.0 else 0.0 | _ => 0.0) |>.data
  for col in [0:n] do
    let mut piv := col
    for r in [col + 1:n] do
      if (a[r * n + col]!).abs > (a[piv * n + col]!).abs then piv := r
    let p := a[piv * n + col]!
    if p.abs < 1e-300 then return none
    if piv != col then
      for c in [0:n] do
        let t := a[col * n + c]!; a := a.set! (col * n + c) a[piv * n + c]!; a := a.set! (piv * n + c) t
        let u := inv[col * n + c]!; inv := inv.set! (col * n + c) inv[piv * n + c]!; inv := inv.set! (piv * n + c) u
    for c in [0:n] do
      a := a.set! (col * n + c) (a[col * n + c]! / p)
      inv := inv.set! (col * n + c) (inv[col * n + c]! / p)
    for r in [0:n] do
      if r != col then
        let f := a[r * n + col]!
        if f != 0.0 then
          for c in [0:n] do
            a := a.set! (r * n + c) (a[r * n + c]! - f * a[col * n + c]!)
            inv := inv.set! (r * n + c) (inv[r * n + c]! - f * inv[col * n + c]!)
  return some inv

/-- The metric and its first and second partial derivatives at a point. -/
structure MetricJet where
  /-- Dimension. -/
  n : Nat
  /-- `g_ij`. -/
  g : Tensor
  /-- `g^ij`. -/
  ginv : Tensor
  /-- `∂_k g_ij`, indexed `[k, i, j]`. -/
  dg : Tensor
  /-- `∂_k ∂_l g_ij`, indexed `[k, l, i, j]`. -/
  ddg : Tensor
  deriving Inhabited

/-- Evaluate every component of the metric at a seed `x + εv`, returning the
`ε⁰`, `ε¹` and `ε²` coefficients as flat `n × n` arrays. -/
def metricCoeffs {n : Nat} (g : Metric n) (x v : Fin n → Float) :
    Array Float × Array Float × Array Float := Id.run do
  let p := seed x v
  let mut c0 := #[]; let mut c1 := #[]; let mut c2 := #[]
  for i in List.finRange n do
    for j in List.finRange n do
      let gij := g p i j
      c0 := c0.push (std gij); c1 := c1.push (epsCoeff gij 1); c2 := c2.push (epsCoeff gij 2)
  return (c0, c1, c2)

/-- The exact 2-jet of a metric at `x` (`none` if `g(x)` is singular). -/
def MetricJet.at? {n : Nat} (g : Metric n) (x : Fin n → Float) : Option MetricJet := do
  let (g0, _, _) := metricCoeffs g x (fun _ => 0.0)
  let ginv ← invertMatrix n g0
  -- c1 and c2 along each axis, and c2 along each eₖ + eₗ (k < l).
  let axis := (Array.range n).map fun k => metricCoeffs g x (basis n k)
  let pair := fun k l =>
    if k == l then (axis[k]!.2.2).map (2.0 * ·)
    else
      let (_, _, cs) := metricCoeffs g x (fun j => if j.val == k || j.val == l then 1.0 else 0.0)
      ((cs.zip axis[k]!.2.2).zip axis[l]!.2.2).map fun ((s, a), b) => s - a - b
  let pairs := (Array.range n).map fun k => (Array.range n).map fun l =>
    if l < k then #[] else pair k l
  let dg := Tensor.ofFn n 3 fun | [k, i, j] => axis[k]!.2.1[i * n + j]! | _ => 0.0
  let ddg := Tensor.ofFn n 4 fun
    | [k, l, i, j] => if k ≤ l then pairs[k]![l]![i * n + j]! else pairs[l]![k]![i * n + j]!
    | _ => 0.0
  return { n, g := ⟨n, 2, g0⟩, ginv := ⟨n, 2, ginv⟩, dg, ddg }

/-- Like `MetricJet.at?` but only the first derivatives (cheaper; enough for
Christoffel symbols and geodesics). `ddg` is zero. -/
def MetricJet.firstOrder? {n : Nat} (g : Metric n) (x : Fin n → Float) : Option MetricJet := do
  let (g0, _, _) := metricCoeffs g x (fun _ => 0.0)
  let ginv ← invertMatrix n g0
  let axis := (Array.range n).map fun k => (metricCoeffs g x (basis n k)).2.1
  let dg := Tensor.ofFn n 3 fun | [k, i, j] => axis[k]![i * n + j]! | _ => 0.0
  return { n, g := ⟨n, 2, g0⟩, ginv := ⟨n, 2, ginv⟩, dg,
           ddg := ⟨n, 4, Array.replicate (n ^ 4) 0.0⟩ }

/-- `Σ_{a < n} f a`. -/
@[inline] def sumRange (n : Nat) (f : Nat → Float) : Float :=
  (List.range n).foldl (fun acc a => acc + f a) 0.0

namespace MetricJet

variable (J : MetricJet)

/-- Christoffel symbols of the first kind `Γ_lij = ½ (∂ᵢ gⱼₗ + ∂ⱼ gᵢₗ − ∂ₗ gᵢⱼ)`,
indexed `[l, i, j]`. -/
def christoffelFirst : Tensor :=
  Tensor.ofFn J.n 3 fun
    | [l, i, j] => 0.5 * (J.dg.get [i, j, l] + J.dg.get [j, i, l] - J.dg.get [l, i, j])
    | _ => 0.0

/-- Christoffel symbols of the second kind `Γᵏᵢⱼ`, indexed `[k, i, j]`. -/
def christoffel : Tensor :=
  let c1 := J.christoffelFirst
  Tensor.ofFn J.n 3 fun
    | [k, i, j] => sumRange J.n fun l => J.ginv.get [k, l] * c1.get [l, i, j]
    | _ => 0.0

/-- `∂ₘ gᵏˡ = −gᵏᵃ (∂ₘ gₐᵦ) gᵝˡ`, indexed `[m, k, l]`. -/
def dginv : Tensor :=
  Tensor.ofFn J.n 3 fun
    | [m, k, l] => -(sumRange J.n fun a => sumRange J.n fun b =>
        J.ginv.get [k, a] * J.dg.get [m, a, b] * J.ginv.get [b, l])
    | _ => 0.0

/-- `∂ₘ Γᵏᵢⱼ`, indexed `[m, k, i, j]`. -/
def christoffelDeriv : Tensor :=
  let c1 := J.christoffelFirst
  let dgi := J.dginv
  Tensor.ofFn J.n 4 fun
    | [m, k, i, j] => sumRange J.n fun l =>
        dgi.get [m, k, l] * c1.get [l, i, j]
        + J.ginv.get [k, l] * 0.5 *
            (J.ddg.get [m, i, j, l] + J.ddg.get [m, j, i, l] - J.ddg.get [m, l, i, j])
    | _ => 0.0

/-- Riemann tensor `Rᵖ_σμν`, indexed `[ρ, σ, μ, ν]`, with the convention
`[∇_μ, ∇_ν] Vᵖ = Rᵖ_σμν Vˢ` (the unit 2-sphere has `R^θ_φθφ = sin²θ`). -/
def riemann : Tensor :=
  let Γ := J.christoffel
  let dΓ := J.christoffelDeriv
  Tensor.ofFn J.n 4 fun
    | [ρ, σ, μ, ν] =>
        dΓ.get [μ, ρ, ν, σ] - dΓ.get [ν, ρ, μ, σ]
        + sumRange J.n fun l => Γ.get [ρ, μ, l] * Γ.get [l, ν, σ] - Γ.get [ρ, ν, l] * Γ.get [l, μ, σ]
    | _ => 0.0

/-- Fully covariant Riemann tensor `R_ρσμν = g_ρa Rᵃ_σμν`. -/
def riemannLower : Tensor :=
  let R := J.riemann
  Tensor.ofFn J.n 4 fun
    | [ρ, σ, μ, ν] => sumRange J.n fun a => J.g.get [ρ, a] * R.get [a, σ, μ, ν]
    | _ => 0.0

/-- Ricci tensor `R_σν = Rᵖ_σρν`. -/
def ricci : Tensor :=
  let R := J.riemann
  Tensor.ofFn J.n 2 fun
    | [σ, ν] => sumRange J.n fun ρ => R.get [ρ, σ, ρ, ν]
    | _ => 0.0

/-- Scalar curvature `R = gˢᵛ R_σν` (`2/r²` on a 2-sphere of radius `r`). -/
def scalarCurvature : Float :=
  let Ric := J.ricci
  sumRange J.n fun a => sumRange J.n fun b => J.ginv.get [a, b] * Ric.get [a, b]

/-- Einstein tensor `G_μν = R_μν − ½ R g_μν`. -/
def einstein : Tensor :=
  let Ric := J.ricci
  let R := J.scalarCurvature
  Tensor.ofFn J.n 2 fun
    | [μ, ν] => Ric.get [μ, ν] - 0.5 * R * J.g.get [μ, ν]
    | _ => 0.0

/-- Kretschmann scalar `R_abcd R^abcd` (`48 M²/r⁶` for Schwarzschild). -/
def kretschmann : Float :=
  let Rl := J.riemannLower
  -- raise all four indices of a copy
  let n := J.n
  let raise1 := fun (t : Tensor) (pos : Nat) => Tensor.ofFn n 4 fun idx =>
    sumRange n fun a => J.ginv.get [idx[pos]!, a] * t.get (idx.set pos a)
  let Ru := raise1 (raise1 (raise1 (raise1 Rl 0) 1) 2) 3
  (Rl.data.zip Ru.data).foldl (fun acc (x, y) => acc + x * y) 0.0

/-- Sectional curvature of the plane spanned by `u`, `v`:
`K = R_abcd uᵃ vᵇ uᶜ vᵈ / (g(u,u) g(v,v) − g(u,v)²)`. -/
def sectional (u v : Array Float) : Float :=
  let n := J.n
  let Rl := J.riemannLower
  let gf := fun (a b : Array Float) => sumRange n fun i => sumRange n fun j => J.g.get [i, j] * a[i]! * b[j]!
  let num := sumRange n fun a => sumRange n fun b => sumRange n fun c => sumRange n fun d =>
    Rl.get [a, b, c, d] * u[a]! * v[b]! * u[c]! * v[d]!
  num / (gf u u * gf v v - gf u v * gf u v)

/-- Geodesic acceleration `ẍᵏ = −Γᵏᵢⱼ ẋⁱ ẋʲ`. -/
def geodesicAccel (v : Array Float) : Array Float :=
  let Γ := J.christoffel
  (Array.range J.n).map fun k => -(sumRange J.n fun i => sumRange J.n fun j => Γ.get [k, i, j] * v[i]! * v[j]!)

/-- Squared length `g(v, v)`. -/
def norm2 (v : Array Float) : Float :=
  sumRange J.n fun i => sumRange J.n fun j => J.g.get [i, j] * v[i]! * v[j]!

end MetricJet

/-- Christoffel symbols of a metric at a point. -/
def christoffelAt {n : Nat} (g : Metric n) (x : Fin n → Float) : Option Tensor :=
  (MetricJet.firstOrder? g x).map (·.christoffel)

/-- Covariant derivative of a vector field, `∇ᵢ Vᵏ = ∂ᵢ Vᵏ + Γᵏᵢⱼ Vʲ`,
indexed `[i, k]`. `∂ᵢ` is read off `V(x + ε eᵢ)`. -/
def covariantDerivVector {n : Nat} (g : Metric n) (V : VectorField n) (x : Fin n → Float) :
    Option Tensor := do
  let Γ ← christoffelAt g x
  let v0 := V (seed x fun _ => 0.0)
  let dV := (Array.range n).map fun i => let vi := V (seed x (basis n i)); fun k => epsCoeff (vi k) 1
  return Tensor.ofFn n 2 fun
    | [i, k] =>
      if hk : k < n then
        dV[i]! ⟨k, hk⟩ + sumRange n fun j => if hj : j < n then Γ.get [k, i, j] * std (v0 ⟨j, hj⟩) else 0.0
      else 0.0
    | _ => 0.0

/-- Covariant derivative of a covector field, `∇ᵢ ωₖ = ∂ᵢ ωₖ − Γʲᵢₖ ωⱼ`,
indexed `[i, k]`. -/
def covariantDerivCovector {n : Nat} (g : Metric n) (ω : VectorField n) (x : Fin n → Float) :
    Option Tensor := do
  let Γ ← christoffelAt g x
  let w0 := ω (seed x fun _ => 0.0)
  let dω := (Array.range n).map fun i => let wi := ω (seed x (basis n i)); fun k => epsCoeff (wi k) 1
  return Tensor.ofFn n 2 fun
    | [i, k] =>
      if hk : k < n then
        dω[i]! ⟨k, hk⟩ - sumRange n fun j => if hj : j < n then Γ.get [j, i, k] * std (w0 ⟨j, hj⟩) else 0.0
      else 0.0
    | _ => 0.0

/-- `∇ₖ gᵢⱼ = ∂ₖ gᵢⱼ − Γˡₖᵢ gₗⱼ − Γˡₖⱼ gᵢₗ`, indexed `[k, i, j]`. The
Levi-Civita connection is metric-compatible, so this vanishes identically; it is
a consistency check of the whole pipeline. -/
def metricCompatibility {n : Nat} (g : Metric n) (x : Fin n → Float) : Option Tensor := do
  let J ← MetricJet.firstOrder? g x
  let Γ := J.christoffel
  return Tensor.ofFn n 3 fun
    | [k, i, j] => J.dg.get [k, i, j]
        - sumRange n (fun l => Γ.get [l, k, i] * J.g.get [l, j] + Γ.get [l, k, j] * J.g.get [i, l])
    | _ => 0.0

/-- A state on the tangent bundle: position and velocity. -/
structure GeodesicState where
  /-- Coordinates. -/
  x : Array Float
  /-- Velocity `ẋ`. -/
  v : Array Float
  deriving Inhabited, Repr

private def axpy (a : Float) (x y : Array Float) : Array Float :=
  (x.zip y).map fun (p, q) => p + a * q

private def toFin {n : Nat} (x : Array Float) : Fin n → Float := fun i => x[i.val]!

/-- One RK4 step of the geodesic equation. Returns `none` if the metric is
singular somewhere along the step. -/
def geodesicStep {n : Nat} (g : Metric n) (h : Float) (s : GeodesicState) :
    Option GeodesicState := do
  let accel := fun (x v : Array Float) => do
    let J ← MetricJet.firstOrder? g (toFin x)
    pure (J.geodesicAccel v)
  let a1 ← accel s.x s.v
  let x2 := axpy (h / 2.0) s.x s.v; let v2 := axpy (h / 2.0) s.v a1
  let a2 ← accel x2 v2
  let x3 := axpy (h / 2.0) s.x v2; let v3 := axpy (h / 2.0) s.v a2
  let a3 ← accel x3 v3
  let x4 := axpy h s.x v3; let v4 := axpy h s.v a3
  let a4 ← accel x4 v4
  let comb := fun (p k1 k2 k3 k4 : Array Float) =>
    (Array.range p.size).map fun i => p[i]! + h / 6.0 * (k1[i]! + 2.0 * k2[i]! + 2.0 * k3[i]! + k4[i]!)
  return { x := comb s.x s.v v2 v3 v4, v := comb s.v a1 a2 a3 a4 }

/-- Integrate a geodesic for `steps` RK4 steps of size `h`; the result starts
with the initial state and stops early at a singularity. -/
def geodesic {n : Nat} (g : Metric n) (x0 v0 : Array Float) (h : Float) (steps : Nat) :
    Array GeodesicState := Id.run do
  let mut s : GeodesicState := { x := x0, v := v0 }
  let mut out := #[s]
  for _ in [0:steps] do
    match geodesicStep g h s with
    | some s' => s := s'; out := out.push s
    | none => break
  return out

/-- Parallel-transport `w` along the geodesic from `(x0, v0)`:
`ẇᵏ = −Γᵏᵢⱼ ẋⁱ wʲ`, integrated jointly with the geodesic by RK4. Returns the
final geodesic state and transported vector. -/
def parallelTransport {n : Nat} (g : Metric n) (x0 v0 w0 : Array Float) (h : Float) (steps : Nat) :
    Option (GeodesicState × Array Float) := do
  let rhs := fun (x v w : Array Float) => do
    let J ← MetricJet.firstOrder? g (toFin x)
    let Γ := J.christoffel
    let dw := (Array.range n).map fun k =>
      -(sumRange n fun i => sumRange n fun j => Γ.get [k, i, j] * v[i]! * w[j]!)
    pure (J.geodesicAccel v, dw)
  let mut x := x0; let mut v := v0; let mut w := w0
  for _ in [0:steps] do
    let (a1, b1) ← rhs x v w
    let (a2, b2) ← rhs (axpy (h/2.0) x v) (axpy (h/2.0) v a1) (axpy (h/2.0) w b1)
    let v2 := axpy (h/2.0) v a1
    let (a3, b3) ← rhs (axpy (h/2.0) x v2) (axpy (h/2.0) v a2) (axpy (h/2.0) w b2)
    let v3 := axpy (h/2.0) v a2
    let (a4, b4) ← rhs (axpy h x v3) (axpy h v a3) (axpy h w b3)
    let v4 := axpy h v a3
    let comb := fun (p k1 k2 k3 k4 : Array Float) =>
      (Array.range p.size).map fun i => p[i]! + h / 6.0 * (k1[i]! + 2.0 * k2[i]! + 2.0 * k3[i]! + k4[i]!)
    x := comb x v v2 v3 v4
    v := comb v a1 a2 a3 a4
    w := comb w b1 b2 b3 b4
  return ({ x, v }, w)

/-! ## Example metrics -/

/-- Round 2-sphere of radius `r` in `(θ, φ)`: `r² dθ² + r² sin²θ dφ²`. -/
def sphere2 (r : Float) : Metric 2 := fun x i j =>
  match i.val, j.val with
  | 0, 0 => ofFloat (r * r)
  | 1, 1 => let s := sin (x 0); smul (r * r) (s * s)
  | _, _ => 0

/-- Round 3-sphere of radius `r` in hyperspherical `(ψ, θ, φ)`. -/
def sphere3 (r : Float) : Metric 3 := fun x i j =>
  let s1 := sin (x 0); let s2 := sin (x 1)
  match i.val, j.val with
  | 0, 0 => ofFloat (r * r)
  | 1, 1 => smul (r * r) (s1 * s1)
  | 2, 2 => smul (r * r) (s1 * s1 * s2 * s2)
  | _, _ => 0

/-- Poincaré upper half-plane `(dx² + dy²) / y²` (curvature −1). -/
def hyperbolicPlane : Metric 2 := fun x i j =>
  if i == j then (x 1 * x 1)⁻¹ else 0

/-- Flat plane in polar coordinates `dr² + r² dφ²`. -/
def flatPolar : Metric 2 := fun x i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 1 => x 0 * x 0
  | _, _ => 0

/-- Schwarzschild metric (signature −+++) in `(t, r, θ, φ)`, `G = c = 1`. -/
def schwarzschild (M : Float) : Metric 4 := fun x i j =>
  let f := 1 - smul (2 * M) (x 1)⁻¹
  let s := sin (x 2)
  match i.val, j.val with
  | 0, 0 => -f
  | 1, 1 => f⁻¹
  | 2, 2 => x 1 * x 1
  | 3, 3 => x 1 * x 1 * s * s
  | _, _ => 0

/-- Flat torus embedded in ℝ³ with radii `R > ρ`: `ρ² du² + (R + ρ cos u)² dv²`.
Gaussian curvature `cos u / (ρ (R + ρ cos u))`, positive outside, negative inside. -/
def torus (R ρ : Float) : Metric 2 := fun x i j =>
  match i.val, j.val with
  | 0, 0 => ofFloat (ρ * ρ)
  | 1, 1 => let w := ofFloat R + smul ρ (cos (x 0)); w * w
  | _, _ => 0

/-- Pull-back metric `gᵢⱼ = ∂ᵢF · ∂ⱼF` of a parametrized submanifold
`F : (Fin n → LC) → Fin m → LC` of Euclidean `ℝᵐ`.

The jet machinery evaluates the metric at `x + ε v` and reads `ε⁰…ε²`, so `∂ᵢF`
itself must be computed *inside* LC arithmetic without disturbing those
coefficients. We use a second, independent-looking infinitesimal
`δ = ε^(1/1024)`: a term `δᵃ εᵇ` has exponent `−(a/1024 + b)`, so the `δ¹`
part (exponents `−1/1024 − b`) never collides with pure `εᵇ` terms for any
power that occurs here. All exponents are dyadic, so Float sums of them are
exact and equal exponents merge. -/
def induced {n m : Nat} (F : Coords n → Fin m → LC) : Metric n := fun x i j =>
  let e : Float := 1.0 / 1024.0
  let δ : LC := { terms := #[⟨-e, 1.0⟩] }
  let dF := fun (k : Fin n) =>
    let shifted := F fun l => if l == k then x l + δ else x l
    fun a : Fin m =>
      ({ terms := (shifted a).terms.filterMap fun t =>
          let b := -(t.exp + e)
          if b ≥ 0.0 && b ≤ 4.0 && b == b.floor then some ⟨t.exp + e, t.coeff⟩ else none } : LC)
  let di := dF i; let dj := dF j
  (List.finRange m).foldl (fun acc a => acc + di a * dj a) 0

end LeviCivita.Geometry
