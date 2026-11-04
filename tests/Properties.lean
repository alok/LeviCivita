import LeviCivita.NSA
import LeviCivita.Germ
import tests.Harness

/-!
# Randomized property tests

Deterministic pseudo-random elements of the field, checked against the axioms
and against independent oracles.

* **Exact arithmetic.** Coefficients are small dyadic rationals (`±1, ±2, ±3, ±½,
  ±¼, ±1½, ±5`), so every sum and product below is exact in Float. The ring axioms
  then hold *exactly*, and the checks compare term arrays with `==`. Exponents
  include thirds, quarters and sixths, so they also exercise `snapExp`: `ε^{1/3}`
  times `ε^{1/6}` must land exactly on `ε^{1/2}`.
* **Order.** Trichotomy, transitivity, and compatibility with `+` and with `×` by
  positives, on pairs that tie in the standard part and differ only infinitesimally
  (the lexicographic case).
* **Standard part and valuation** are a ring homomorphism and a valuation.
* **Inverse and roots** agree with the field identities to the precision they
  promise, and the fixed-length `invert` never returns a wrong term.
* **Derivatives.** Random expression trees over `RealLike` are differentiated by
  `Ext.deriv?`, `Ext.deriv2?`, `Ext.derivs`, `FastLC.grad` and `Germ.grad`, and
  compared against a second-order forward-mode jet written directly over Float,
  which shares no code with the Levi-Civita implementation.
-/

open LeviCivita LeviCivita.Fast FastLC

namespace Props

/-! ## A small deterministic generator -/

/-- A 64-bit linear congruential generator (Knuth's MMIX constants). -/
abbrev Gen := StateM UInt64

def nextNat (bound : Nat) : Gen Nat := do
  let s ← get
  let s' := s * 6364136223846793005 + 1442695040888963407
  set s'
  return ((s' >>> 33).toNat) % bound

def pick {α : Type} [Inhabited α] (xs : Array α) : Gen α := do
  return xs[← nextNat xs.size]!

/-- Run `n` trials from a fixed seed. -/
def trials {α : Type} (n : Nat) (seed : UInt64) (g : Gen α) : List α :=
  ((List.range n).foldl (fun (acc, s) _ => let (a, s') := g.run s; (a :: acc, s')) ([], seed)).1.reverse

/-- Exponents (`exp = −q`, so `ε^q` has exponent `−q`), written as quotients so
that the same rational can arise from different Float computations. -/
def expPool : Array Float :=
  #[-3, -2, -1, 0, 1, 2, -1/2, 1/2, -1/3, 1/3, -2/3, 2/3, -3/4, 1/4, -5/6, 1/6, -3/2]

/-- Exponents for finite elements only (no `H` terms). -/
def finiteExpPool : Array Float := expPool.filter (· ≤ 0)

/-- Half-integer exponents: series in `δ` stay short. -/
def halfExpPool : Array Float := #[-3, -2, -3/2, -1, -1/2, 0, 1/2, 1]

/-- Dyadic coefficients: all arithmetic on them below is exact. -/
def coeffPool : Array Float := #[1, -1, 2, -2, 3, -3, 0.5, -0.5, 0.25, -0.25, 1.5, -1.5, 5, -5]

def monomial (e c : Float) : LC := { terms := #[⟨e, c⟩] }

/-- A random element with up to `k` terms drawn from `pool`. -/
def genLC (pool : Array Float := expPool) (k : Nat := 3) : Gen LC := do
  let n := (← nextNat k) + 1
  let mut x : LC := 0
  for _ in [0:n] do
    x := x + monomial (← pick pool) (← pick coeffPool)
  return x

def genNonzero (pool : Array Float := expPool) : Gen LC := do
  let x ← genLC pool
  return if x.terms.isEmpty then monomial 0 1 else x

def genPositive (pool : Array Float := expPool) : Gen LC := do
  let x ← genNonzero pool
  return if signum x < 0 then -x else x

/-- `x` and `x + (a term below x's leading term)`: equal standard parts when `x`
is finite and appreciable, so the order must look past them. -/
def genTiePair : Gen (LC × LC) := do
  let x ← genNonzero
  let lead := (lead? x).map (·.exp) |>.getD 0
  let below := lead - (← pick #[1/3, 1/2, 1, 2])
  return (x, x + monomial below (← pick coeffPool))

/-! ## Reporting -/

/-- Run a property over the trials and report the first counterexample. -/
def prop {α : Type} (name : String) (xs : List α) (p : α → Bool) (render : α → String) : Check :=
  match xs.find? (! p ·) with
  | none => { name := s!"{name} ({xs.length} cases)", ok := true, detail := "" }
  | some x => { name, ok := false, detail := render x }

def sh (x : LC) : String := toString (x.terms.toList.map fun t => (t.exp, t.coeff))
def sh2 (p : LC × LC) : String := s!"{sh p.1}, {sh p.2}"
def sh3 (p : LC × LC × LC) : String := s!"{sh p.1}, {sh p.2.1}, {sh p.2.2}"

def isZero (x : LC) : Bool := x.terms.isEmpty

/-- Every term of `x` of valuation `< prec` has a coefficient below `tol`. -/
def smallBelow (x : LC) (prec tol : Float) : Bool :=
  x.terms.all fun t => -t.exp ≥ prec || t.coeff.abs ≤ tol

/-- Largest coefficient, at least `1`: the scale of Float rounding in `x`.
Series like `1/(1 − 6ε^{1/6})` have coefficients `6ᵏ`, so a residual that is zero
in exact arithmetic is only zero *relative* to that scale. -/
def scale (x : LC) : Float := x.terms.foldl (fun m t => max m t.coeff.abs) 1

def N : Nat := 400

def triples : List (LC × LC × LC) :=
  trials N 1 do return (← genLC, ← genLC, ← genLC)

def pairs : List (LC × LC) := trials N 2 do return (← genLC, ← genLC)

def finitePairs : List (LC × LC) := trials N 3 do return (← genLC finiteExpPool, ← genLC finiteExpPool)

/-! ## Ring axioms, exactly -/

def ringChecks : List Check :=
  [ prop "a + b = b + a" pairs (fun (a, b) => a + b == b + a) sh2,
    prop "(a + b) + c = a + (b + c)" triples (fun (a, b, c) => (a + b) + c == a + (b + c)) sh3,
    prop "a · b = b · a" pairs (fun (a, b) => isZero (a * b - b * a)) sh2,
    prop "(a · b) · c = a · (b · c)" triples (fun (a, b, c) => isZero ((a * b) * c - a * (b * c))) sh3,
    prop "a · (b + c) = a · b + a · c" triples (fun (a, b, c) => isZero (a * (b + c) - (a * b + a * c))) sh3,
    prop "a − a = 0 and a + 0 = a, a · 1 = a" pairs (fun (a, _) => isZero (a - a) && a + 0 == a && a * 1 == a) sh2,
    prop "terms stay sorted, distinct and nonzero under · and +" triples (fun (a, b, c) =>
      let y := a * b + c
      (List.range (y.terms.size - 1)).all (fun i => y.terms[i]!.exp > y.terms[i + 1]!.exp) &&
        y.terms.all (·.coeff != 0)) sh3,
    prop "exponent arithmetic is exact: ε^{1/3} ε^{1/6} = ε^{1/2}, ε^{1/3} ε^{1/3} ε^{1/3} = ε"
      [()] (fun _ =>
        monomial (-1/3) 1 * monomial (-1/6) 1 == monomial (-1/2) 1 &&
        monomial (-1/3) 1 * monomial (-1/3) 1 * monomial (-1/3) 1 == epsilon &&
        isStandard (monomial (-0.1) 1 * monomial (-0.2) 1 * monomial 0.3 1) &&
        isZero (monomial (-0.1) 1 * monomial (-0.2) 1 - monomial (-0.3) 1)) (fun _ => "") ]

/-! ## Order -/

def orderChecks : List Check :=
  let ties := trials N 4 genTiePair
  let tieTriples : List (LC × LC × LC) := trials N 5 do
    let (a, b) ← genTiePair
    return (a, b, ← genLC)
  let lt (x y : LC) : Bool := decide (x < y)
  [ prop "trichotomy: exactly one of a < b, a = b, b < a" (pairs ++ ties) (fun (a, b) =>
      [lt a b, isZero (a - b), lt b a].countP id == 1) sh2,
    prop "transitivity" triples (fun (a, b, c) => !(lt a b && lt b c) || lt a c) sh3,
    prop "a < b → a + c < b + c" (triples ++ tieTriples) (fun (a, b, c) => !(lt a b) || lt (a + c) (b + c)) sh3,
    prop "a < b, 0 < c → a c < b c" (triples ++ tieTriples) (fun (a, b, c) =>
      !(lt a b && lt 0 c) || lt (a * c) (b * c)) sh3,
    prop "0 < ε^q < r < H^q for every real r > 0 and q > 0"
      (trials N 6 do return (← pick #[1/3, 1/2, 1, 2, 7/3], ← pick coeffPool)) (fun (q, r) =>
        let r := r.abs
        lt 0 (rpow epsilon q) && lt (rpow epsilon q) (ofFloat r) && lt (ofFloat r) (rpow H q))
      (fun (q, r) => s!"{q}, {r}"),
    prop "|a b| = |a| |b| and |a + b| ≤ |a| + |b|" pairs (fun (a, b) =>
      abs (a * b) == abs a * abs b && !(lt (abs a + abs b) (abs (a + b)))) sh2 ]

/-! ## Standard part and valuation -/

def stChecks : List Check :=
  let ν (x : LC) : Float := (valuation? x).getD 0
  [ prop "st (a + b) = st a + st b, st (a b) = st a · st b (finite a, b)" finitePairs (fun (a, b) =>
      st? (a + b) == (do return (← st? a) + (← st? b)) &&
      st? (a * b) == (do return (← st? a) * (← st? b))) sh2,
    prop "a ≈ st a for finite a" finitePairs (fun (a, _) =>
      match st? a with | some r => infinitelyClose a (ofFloat r) | none => false) sh2,
    prop "finite elements: infinitesimal ↔ st = 0" finitePairs (fun (a, _) =>
      isInfinitesimal a == (st? a == some 0)) sh2,
    prop "ν(a b) = ν(a) + ν(b)" pairs (fun (a, b) =>
      isZero a || isZero b || valuation? (a * b) == some (snapExp (ν a + ν b))) sh2,
    prop "ν(a + b) ≥ min ν(a) ν(b)" pairs (fun (a, b) =>
      isZero a || isZero b || isZero (a + b) || ν (a + b) ≥ min (ν a) (ν b)) sh2,
    prop "infinite ↔ 1/a is a nonzero infinitesimal" (trials N 7 genNonzero) (fun a =>
      isInfinite a == (let i := (invertTo a).get!; isInfinitesimal i && !isZero i)) sh ]

/-! ## Inverse and roots -/

def inverseChecks : List Check :=
  let nz := trials N 8 genNonzero
  let halves := trials N 9 (genNonzero halfExpPool)
  let pos := trials N 10 genPositive
  [ prop "a · invertTo a 4 = 1 below valuation 4" nz (fun a =>
      let i := (invertTo a 4).get!
      smallBelow (a * i - 1) 4 (1e-13 * scale a * scale i)) sh,
    prop "invert never returns a wrong term (each agrees with invertTo a 12 below valuation 12)" halves (fun a =>
      let ref := (invertTo a 12).get!
      let v := (valuation? ref).getD 0
      ((invert a).get!).terms.all fun t =>
        -t.exp ≥ v + 12 || approx t.coeff (getCoeff ref t.exp) 1e-12) sh,
    prop "(a^{1/3})³ = a and (√a)² = a below relative valuation 5 (a > 0)" pos (fun a =>
      let v := (valuation? a).getD 0
      let r := rpow a (1/3)
      let s := sqrt a
      smallBelow (r ^ 3 - a) (v + 5) (1e-13 * scale r ^ 3) &&
        smallBelow (s * s - a) (v + 5) (1e-13 * scale s ^ 2)) sh,
    prop "∛ is odd: ∛(−a) = −∛a" pos (fun a => isZero (root 3 (-a) + root 3 a)) sh ]

/-! ## Derivatives against an independent forward-mode oracle -/

/-- Random expressions in variables `x₀ … x₃`. Every node is smooth on all of `ℝ`
(`sqrt1p u = √(1 + u²)`, `recip2p u = 1/(2 + u²)`), so derivatives always exist. -/
inductive E where
  | var (i : Nat)
  | const (c : Float)
  | add (a b : E)
  | sub (a b : E)
  | mul (a b : E)
  | sin (a : E)
  | cos (a : E)
  | exp (a : E)
  | atan (a : E)
  | sqrt1p (a : E)
  | recip2p (a : E)
  deriving Inhabited

def E.toString : E → String
  | .var i => s!"x{i}"
  | .const c => s!"{c}"
  | .add a b => s!"({a.toString} + {b.toString})"
  | .sub a b => s!"({a.toString} - {b.toString})"
  | .mul a b => s!"({a.toString} * {b.toString})"
  | .sin a => s!"sin {a.toString}"
  | .cos a => s!"cos {a.toString}"
  | .exp a => s!"exp {a.toString}"
  | .atan a => s!"atan {a.toString}"
  | .sqrt1p a => s!"√(1 + {a.toString}²)"
  | .recip2p a => s!"1/(2 + {a.toString}²)"

/-- Evaluate over any `RealLike`; at `LC` this is the natural extension. -/
def E.eval {α : Type} [RealLike α] (env : Nat → α) : E → α
  | .var i => env i
  | .const c => RealLike.ofFloat c
  | .add a b => a.eval env + b.eval env
  | .sub a b => a.eval env - b.eval env
  | .mul a b => a.eval env * b.eval env
  | .sin a => RealLike.sin (a.eval env)
  | .cos a => RealLike.cos (a.eval env)
  | .exp a => RealLike.exp (a.eval env)
  | .atan a => RealLike.atan (a.eval env)
  | .sqrt1p a => let u := a.eval env; RealLike.sqrt (RealLike.ofFloat 1 + u * u)
  | .recip2p a => let u := a.eval env; RealLike.inv (RealLike.ofFloat 2 + u * u)

/-- A second-order jet `(f, f', f'')` along one direction, over Float. -/
structure J where
  v : Float
  d : Float
  dd : Float

/-- Compose a scalar function, given its value and two derivatives at `u.v`. -/
def J.chain (u : J) (g g' g'' : Float) : J := ⟨g, g' * u.d, g'' * u.d * u.d + g' * u.dd⟩

/-- Forward-mode second-order differentiation of `e` along `dir`. -/
def E.jet (x : Nat → Float) (dir : Nat → Float) : E → J
  | .var i => ⟨x i, dir i, 0⟩
  | .const c => ⟨c, 0, 0⟩
  | .add a b => let u := a.jet x dir; let w := b.jet x dir; ⟨u.v + w.v, u.d + w.d, u.dd + w.dd⟩
  | .sub a b => let u := a.jet x dir; let w := b.jet x dir; ⟨u.v - w.v, u.d - w.d, u.dd - w.dd⟩
  | .mul a b => let u := a.jet x dir; let w := b.jet x dir
                ⟨u.v * w.v, u.d * w.v + u.v * w.d, u.dd * w.v + 2 * u.d * w.d + u.v * w.dd⟩
  | .sin a => let u := a.jet x dir; u.chain (Float.sin u.v) (Float.cos u.v) (-(Float.sin u.v))
  | .cos a => let u := a.jet x dir; u.chain (Float.cos u.v) (-(Float.sin u.v)) (-(Float.cos u.v))
  | .exp a => let u := a.jet x dir; let e := Float.exp u.v; u.chain e e e
  | .atan a => let u := a.jet x dir; let w := 1 + u.v * u.v
               u.chain (Float.atan u.v) (1 / w) (-2 * u.v / (w * w))
  | .sqrt1p a => let u := a.jet x dir; let w := 1 + u.v * u.v; let r := Float.sqrt w
                 -- g(u) = √(1 + u²): g' = u/r, g'' = 1/r³
                 u.chain r (u.v / r) (1 / (r * r * r))
  | .recip2p a => let u := a.jet x dir; let w := 2 + u.v * u.v
                  -- g(u) = 1/(2 + u²): g' = −2u/w², g'' = (6u² − 4)/w³
                  u.chain (1 / w) (-2 * u.v / (w * w)) ((6 * u.v * u.v - 4) / (w * w * w))

def genE (nvars : Nat) : Nat → Gen E
  | 0 => do
    if (← nextNat 3) == 0 then return .const (← pick #[0.5, -1.5, 2, 0.3, -0.7])
    else return .var (← nextNat nvars)
  | d + 1 => do
    match ← nextNat 11 with
    | 0 => return .add (← genE nvars d) (← genE nvars d)
    | 1 => return .sub (← genE nvars d) (← genE nvars d)
    | 2 | 3 => return .mul (← genE nvars d) (← genE nvars d)
    | 4 => return .sin (← genE nvars d)
    | 5 => return .cos (← genE nvars d)
    | 6 => return .exp (.mul (.const 0.3) (← genE nvars d))
    | 7 => return .atan (← genE nvars d)
    | 8 => return .sqrt1p (← genE nvars d)
    | 9 => return .recip2p (← genE nvars d)
    | _ => genE nvars 0

def genPoint : Gen Float := do
  return ((← nextNat 2001).toFloat - 1000) / 500

/-- Relative agreement, scaled by the size of the reference. -/
def near (a b : Float) (tol : Float) : Bool := (a - b).abs ≤ tol * (1 + b.abs)

def derivChecks : List Check :=
  let univariate : List (E × Float) := trials 300 11 do return (← genE 1 4, ← genPoint)
  let ext (e : E) : Ext := ⟨fun x => e.eval fun _ => x⟩
  let oracle (e : E) (x : Float) : J := e.jet (fun _ => x) (fun _ => 1)
  let showU : E × Float → String := fun (e, x) =>
    let j := oracle e x
    s!"f = {e.toString} at {x}: oracle {(j.v, j.d, j.dd)}, deriv? {(ext e).deriv? x}, " ++
      s!"deriv2? {(ext e).deriv2? x}, derivs {(ext e).derivs x 2}"
  let multivariate : List (E × Array Float) := trials 200 12 do
    return (← genE 4 4, #[← genPoint, ← genPoint, ← genPoint, ← genPoint])
  let gradOracle (e : E) (x : Array Float) : Array Float :=
    #[0, 1, 2, 3].map fun i => (e.jet (fun k => x[k]!) (fun k => if k == i then 1 else 0)).d
  let showM : E × Array Float → String := fun (e, x) =>
    s!"f = {e.toString} at {x}: oracle {gradOracle e x}, " ++
      s!"LC {FastLC.grad (n := 4) (fun v => e.eval fun k => v ⟨k % 4, Nat.mod_lt _ (by decide)⟩) (fun i => x[i]!)}, " ++
      s!"Germ {Germ.grad (n := 4) (fun v => e.eval fun k => v ⟨k % 4, Nat.mod_lt _ (by decide)⟩) (fun i => x[i]!)}"
  let lcGrad (e : E) (x : Array Float) : Array Float :=
    FastLC.grad (n := 4) (fun v => e.eval fun k => v ⟨k % 4, Nat.mod_lt _ (by decide)⟩) (fun i => x[i]!)
  let germGrad (e : E) (x : Array Float) : Array Float :=
    Germ.grad (n := 4) (fun v => e.eval fun k => v ⟨k % 4, Nat.mod_lt _ (by decide)⟩) (fun i => x[i]!)
  let agree (g ref : Array Float) : Bool := g.size == ref.size && (g.zip ref).all fun (a, b) => near a b 1e-9
  [ prop "natural extension: *f(x) = f(x) at reals (random f)" univariate (fun (e, x) =>
      (ext e).extendsStd [x] 1e-13) showU,
    prop "deriv? = f' (forward-mode oracle, random f)" univariate (fun (e, x) =>
      match (ext e).deriv? x with
      | some d => near d (oracle e x).d 1e-9
      | none => false) showU,
    prop "deriv2? = f'' (random f)" univariate (fun (e, x) =>
      match (ext e).deriv2? x with
      | some d => near d (oracle e x).dd 1e-7
      | none => false) showU,
    prop "derivs reads f, f', f'' off one evaluation (random f)" univariate (fun (e, x) =>
      let j := oracle e x
      let ds := (ext e).derivs x 2
      ds.size == 3 && near ds[0]! j.v 1e-12 && near ds[1]! j.d 1e-9 && near ds[2]! j.dd 1e-7) showU,
    prop "one-pass FastLC.grad = oracle gradient (random f : ℝ⁴ → ℝ)" multivariate (fun (e, x) =>
      agree (lcGrad e x) (gradOracle e x)) showM,
    prop "one-pass Germ.grad = oracle gradient (random f : ℝ⁴ → ℝ)" multivariate (fun (e, x) =>
      agree (germGrad e x) (gradOracle e x)) showM ]

def all : List Check := ringChecks ++ orderChecks ++ stChecks ++ inverseChecks ++ derivChecks

end Props
