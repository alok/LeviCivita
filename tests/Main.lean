import LeviCivita.Analysis
import LeviCivita.NSA
import LeviCivita.Germ
import LeviCivita.Hyperfinite
import tests.Harness
import tests.Properties

/-!
# `lake test`: the Levi-Civita field, nonstandard analysis, exact gradients

Every check compares against a closed form: field identities, classical limits
and derivatives, Euler–Maclaurin coefficients. Exit code 1 on any failure.
-/

open LeviCivita LeviCivita.Fast FastLC LeviCivita.Hyperfinite

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
       diffBelow (s * s + c * c) 1 5) 0 1e-12,
    check "exp ∘ log = id through ε⁴" (diffBelow (exp (log (ofFloat a + epsilon))) (ofFloat a + epsilon) 5) 0 1e-12,
    check "atan jet ε¹ = 1/(1 + a²)" (epsCoeff (atan (ofFloat a + epsilon)) 1) (1 / (1 + a * a)),
    check "atan jet ε³ = (3a² − 1)/(3(1 + a²)³)" (epsCoeff (atan (ofFloat a + epsilon)) 3)
      ((3 * a * a - 1) / (3 * (1 + a * a) ^ 3)),
    check "atan ∘ tan = id through ε⁴" (diffBelow (atan (tan (ofFloat a + epsilon))) (ofFloat a + epsilon) 5) 0 1e-12,
    check "sin √ε = √ε − ε^{3/2}/6 + ε^{5/2}/120 − ε^{7/2}/5040 + ε^{9/2}/362880 (fractional jets)"
      (diffBelow (sin (sqrt epsilon))
        (sqrt epsilon - smul (1/6) (rpow epsilon 1.5) + smul (1/120) (rpow epsilon 2.5)
          - smul (1/5040) (rpow epsilon 3.5) + smul (1/362880) (rpow epsilon 4.5)) 5) 0 1e-15,
    checkB "exp ε^{1/100} is cut where its 64-term series stops being exact"
      (let y := exp (rpow epsilon 0.01)
       y.terms.all (fun t => -t.exp < 0.64) && approx (getCoeff y (-0.63)) (1 / factorial 63) 1e-9) ]

def fieldChecks : List Check :=
  let x : LC := ofFloat 3 + smul 2 epsilon - epsilon * epsilon
  let inf : LC := H + 1
  [ check "x · x⁻¹ = 1 through ε⁷ (invertTo)" (diffBelow (x * (invertTo x).get!) 1 8) 0 1e-14,
    check "(H + 1)(H + 1)⁻¹ = 1" (diffBelow (inf * (invertTo inf).get!) 1 8) 0 1e-14,
    checkB "div? by zero is none" (div? x 0).isNone,
    checkB "ν(ε) = 1, ν(H) = −1, ν(3 + ε) = 0, ν(√ε) = ½"
      (valuation? epsilon == some 1 && valuation? H == some (-1) && valuation? x == some 0 &&
       valuation? (sqrt epsilon) == some 0.5),
    checkB "√ε · √ε = ε" ((sqrt epsilon * sqrt epsilon) == epsilon),
    check "(⁵√x)⁵ = x through ε⁴" (diffBelow ((root 5 x) ^ 5) x 5) 0 1e-13,
    check "∛(−8 + ε) = −2 + ε/12: standard part" (std (root 3 (ofFloat (-8) + epsilon))) (-2),
    check "∛(−8 + ε) = −2 + ε/12: ε coefficient" (epsCoeff (root 3 (ofFloat (-8) + epsilon)) 1) (1 / 12),
    checkB "∛(−ε) = −ε^{1/3}" (match lead? (root 3 (-epsilon)) with
      | some t => approx t.exp (-1 / 3) 1e-15 && t.coeff == -1 | none => false),
    checkB "(H + 1)^{1/3} = H^{1/3} + ⅓ H^{−2/3} + …" (let y := rpow inf (1 / 3)
      match y.terms[0]?, y.terms[1]? with
      | some t0, some t1 => approx t0.exp (1 / 3) 1e-15 && t0.coeff == 1 && approx t1.exp (-2 / 3) 1e-15 && approx t1.coeff (1 / 3)
      | _, _ => false),
    checkB "√ of a negative element is 0" (sqrt (-epsilon) == 0),
    checkB "0 < ε < 10⁻³⁰⁰ and H > 10³⁰⁰"
      (decide ((0 : LC) < epsilon) && decide (epsilon < ofFloat 1e-300) && decide (ofFloat 1e300 < H)),
    checkB "1 − ε < 1 < 1 + ε²" (decide ((1 : LC) - epsilon < 1) && decide ((1 : LC) < 1 + epsilon * epsilon)),
    checkB "max (1 + ε) (1 + 2ε) = 1 + 2ε" (max ((1 : LC) + epsilon) (1 + smul 2 epsilon) == 1 + smul 2 epsilon),
    checkB "exponents are canonical: ε^{0.1} ε^{0.2} H^{0.3} = 1, ε^{1/3} ε^{1/3} ε^{1/3} = ε"
      (rpow epsilon 0.1 * rpow epsilon 0.2 * rpow H 0.3 == 1 &&
       rpow epsilon (1/3) * rpow epsilon (1/3) * rpow epsilon (1/3) == epsilon),
    checkB "0 · undefined is undefined (NaN propagates, as for Float)" (!isDefined (0 * undefined)) ]

/-- Some standard functions, written once over `RealLike`. -/
def cube : Ext := ⟨fun x => x * x * x - RealLike.ofFloat 2 * x⟩
def absF : Ext := ⟨fun x => RealLike.abs x⟩
def sqrtF : Ext := ⟨fun x => RealLike.sqrt x⟩
def step : Ext := ⟨fun {α} _ x => if RealLike.lt x (RealLike.ofFloat (α := α) 0) then RealLike.ofFloat 0 else RealLike.ofFloat 1⟩
def sinc : Ext := ⟨fun x => RealLike.sin x / x⟩
def versine : Ext := ⟨fun x => (RealLike.ofFloat 1 - RealLike.cos x) / (x * x)⟩
def rational : Ext := ⟨fun x => (RealLike.ofFloat 3 * x * x + RealLike.ofFloat 1) / (x * x - RealLike.ofFloat 5)⟩
def sqrtGap : Ext := ⟨fun x => RealLike.sqrt (x * x + x) - x⟩
def sinRecip : Ext := ⟨fun x => RealLike.sin (RealLike.inv x)⟩
def sinSq : Ext := ⟨fun x => RealLike.sin (x * x)⟩
def sinF : Ext := ⟨fun x => RealLike.sin x⟩
def expF : Ext := ⟨fun x => RealLike.exp x⟩
def recipF : Ext := ⟨fun x => RealLike.inv x⟩
def quotF : Ext := ⟨fun x => RealLike.ofFloat 1 / x⟩
def atanF : Ext := ⟨fun x => RealLike.atan x⟩

def nsaChecks : List Check :=
  let pts := [-2.5, -1, 0, 0.3, 1.5, 4]
  [ checkB "ε infinitesimal, 1 not; 2 + ε finite; H infinite"
      (isInfinitesimal epsilon && !isInfinitesimal 1 && isFinite (2 + epsilon) && isInfinite H),
    checkOpt "st (2 + 3ε − ε²) = 2" (st? (2 + smul 3 epsilon - epsilon * epsilon)) 2,
    checkB "st H, st (exp H) and st (log ε) do not exist"
      ((st? H).isNone && (st? (exp H)).isNone && (st? (log epsilon)).isNone),
    checkB "1 + ε ≈ 1, 1 + ε ≉ 1 + ε⁰·10⁻¹²"
      (infinitelyClose (1 + epsilon) 1 && !infinitelyClose (1 + epsilon) (ofFloat (1 + 1e-12))),
    checkB "natural extensions agree with f on the reals"
      ([cube, absF, sinF, expF, rational, sinSq].all fun F => F.extendsStd pts),
    checkOpt "(x³ − 2x)' at 1.5 = 4.75" (cube.deriv? 1.5) 4.75,
    checkOpt "(sin x²)' at 0.7 = 1.4 cos 0.49 (chain rule)" (sinSq.deriv? 0.7) (1.4 * Float.cos 0.49),
    checkB "|x| has no derivative at 0" (absF.deriv? 0).isNone,
    checkOpt "|x|' at −1 = −1" (absF.deriv? (-1)) (-1),
    checkB "√x has no derivative at 0 (infinite quotient)" (sqrtF.deriv? 0).isNone,
    checkOpt "sin'' at 0.3 = −sin 0.3" (sinF.deriv2? 0.3) (-(Float.sin 0.3)),
    checkB "derivs of exp at ½ are all e^½"
      ((expF.derivs 0.5 4).all fun d => approx d (Float.exp 0.5) 1e-12),
    checkB "step is discontinuous at 0, continuous at 1"
      (!step.continuousAt 0 && step.continuousAt 1),
    checkB "step: left limit 0, right limit 1, no limit at 0"
      (step.limitLeft? 0 == some 0 && step.limitRight? 0 == some 1 && (step.limit? 0).isNone),
    checkB "x³ − 2x and |x| are continuous at 0" (cube.continuousAt 0 && absF.continuousAt 0),
    checkOpt "lim_{x→0} sin x / x = 1" (sinc.limit? 0) 1,
    checkOpt "lim_{x→0} (1 − cos x)/x² = ½" (versine.limit? 0) 0.5,
    checkB "lim_{x→0} sin(1/x) does not exist" (sinRecip.limit? 0).isNone,
    checkOpt "lim_{x→∞} (3x² + 1)/(x² − 5) = 3" rational.limitAtInfinity? 3,
    checkOpt "lim_{x→−∞} (3x² + 1)/(x² − 5) = 3" rational.limitAtNegInfinity? 3,
    checkOpt "lim_{x→∞} √(x² + x) − x = ½" sqrtGap.limitAtInfinity? 0.5,
    checkB "*f has the domain of f: 1/x, 1 / x at 0 and √x at −1 have no standard part"
      ((st? (recipF.star 0)).isNone && (st? (quotF.star 0)).isNone && (st? (sqrtF.star (ofFloat (-1)))).isNone),
    checkB "… so extendsStd holds at points outside the domain too"
      (recipF.extendsStd [0, 2] && quotF.extendsStd [0, -3] && sqrtF.extendsStd [-1, 4]),
    checkB "atan H is undefined (no germ at an infinite point), so limitAtInfinity? is none"
      atanF.limitAtInfinity?.isNone,
    checkOpt "(atan x)' at 2 = 1/5" (atanF.deriv? 2) 0.2 ]

/-- A smooth test function on ℝ⁴, over any `RealLike`. -/
def smooth4 {α : Type} [RealLike α] (v : Fin 4 → α) : α :=
  let o : Float → α := RealLike.ofFloat
  RealLike.sqrt (v 0 * v 0 + v 1 * v 1 + o 0.3) * RealLike.sin (v 2) +
    RealLike.inv (o 2 + v 3 * v 3) - v 0 * v 3 + RealLike.exp (v 1 * o 0.2)

/-- `max` of two affine pieces that tie along `x₀ = x₁`. -/
def crease {α : Type} [RealLike α] (v : Fin 2 → α) : α := RealLike.max (v 0) (v 1)

/-- A tesseract-like distance with creases where coordinates tie. -/
def boxish {α : Type} [RealLike α] (v : Fin 4 → α) : α :=
  RealLike.max (RealLike.max (RealLike.abs (v 0)) (RealLike.abs (v 1)))
    (RealLike.max (RealLike.abs (v 2)) (RealLike.abs (v 3))) - RealLike.ofFloat 1

def pt (xs : List Float) {n : Nat} : Fin n → Float := fun i => xs.getD i.val 0.0

def gradChecks : List Check :=
  let xs : List (List Float) := [[0.3, -1.2, 0.8, 0.5], [1.7, 0.4, -2.1, -0.9], [-0.6, 2.2, 3.0, 1.1]]
  let worst (g : (Fin 4 → Float) → Array Float) : Float :=
    xs.foldl (fun m x =>
      let ref := (List.finRange 4).toArray.map fun i => partialAt (n := 4) smooth4 (pt x) i
      (g (pt x)).zip ref |>.foldl (fun m (a, b) => max m (a - b).abs) m) 0
  let oneLC := FastLC.grad (n := 4) smooth4
  let oneGerm := Germ.grad (n := 4) smooth4
  let gc := FastLC.grad (n := 2) crease (pt [1, 1])
  let stack := (List.finRange 2).toArray.map fun i => partialAt (n := 2) crease (pt [1, 1]) i
  let gb := Germ.grad (n := 4) boxish (pt [1, 1, -1, 0.2])
  let longest := xs.foldl (fun m x =>
    let y : Germ := smooth4 fun (i : Fin 4) => (⟨ofFloat (pt x i) + { terms := #[⟨-seedExp 4 i.val, 1.0⟩] }⟩ : Germ)
    max m y.val.terms.size) 0
  [ check "one-pass LC gradient = per-coordinate partials (smooth)" (worst oneLC) 0 1e-12,
    check "one-pass Germ gradient = per-coordinate partials (smooth)" (worst oneGerm) 0 1e-12,
    check "Germ value = Float value"
      ((Germ.valueAndGrad (n := 4) smooth4 (pt [0.3, -1.2, 0.8, 0.5])).1) (smooth4 (α := Float) (pt [0.3, -1.2, 0.8, 0.5])) 1e-15,
    checkB "germs stay n + 1 terms long" (longest ≤ 5) s!"longest = {longest}",
    checkB "crease max(x, y) at x = y: one-pass gradient is one piece, (1, 0)"
      (gc == #[1, 0]) s!"{gc}",
    checkB "… while stacking one-sided partials mixes pieces, (1, 1)" (stack == #[1, 1]) s!"{stack}",
    checkB "box corner: unit gradient of a single face" (gb.foldl (fun s g => s + g * g) 0 == 1) s!"{gb}" ]

def hyperfiniteChecks : List Check :=
  let p : Poly := ⟨#[1, -2, 3, 0.5, -0.25]⟩
  let (a, b) := (-1.0, 2.0)
  let left := riemannSum p (ofFloat a) (ofFloat b) H
  let mid := riemannSum p (ofFloat a) (ofFloat b) H 0.5
  let B := bernoulli 4
  [ checkB "Bernoulli B₀…B₄ = 1, −½, ⅙, 0, −1/30"
      (B == #[1, -1/2, 1/6, 0, -1/30]) s!"{B.toList}",
    checkOpt "Σ_{k<10} k³ = 2025 (Faulhaber at a standard N)" (st? (powerSum 3 10)) 2025,
    checkOpt "st of the hyperfinite sum = ∫ p" (integral p a b) (p.integral a b) 1e-12,
    check "left rule: ε¹ coefficient = −(b−a)(p(b)−p(a))/2" (epsCoeff left 1)
      (-(b - a) * (p.eval b - p.eval a) / 2) 1e-12,
    check "midpoint rule: ε¹ coefficient = 0" (epsCoeff mid 1) 0 1e-12,
    check "midpoint rule: ε² coefficient = −(b−a)²(p'(b)−p'(a))/24" (epsCoeff mid 2)
      (-(b - a) ^ 2 * (p.deriv.eval b - p.deriv.eval a) / 24) 1e-12,
    checkB "the hyperfinite sum is finite (no H terms)" (isFinite left && isFinite mid),
    check "trapezoid rule: ε¹ coefficient = 0" (epsCoeff (trapezoidSum p (ofFloat a) (ofFloat b) H) 1) 0 1e-12,
    check "trapezoid rule: ε² coefficient = +(b−a)²(p'(b)−p'(a))/12"
      (epsCoeff (trapezoidSum p (ofFloat a) (ofFloat b) H) 2)
      ((b - a) ^ 2 * (p.deriv.eval b - p.deriv.eval a) / 12) 1e-12,
    check "transfer: closed form at N = 37 = the plain sum"
      (std (riemannSum p (ofFloat a) (ofFloat b) 37 0.5)) (riemannSumDirect p a b 37 0.5) 1e-12 ]

def main : IO UInt32 := do
  let all := analysisChecks ++ fieldChecks ++ nsaChecks ++ gradChecks ++ hyperfiniteChecks ++ Props.all
  let mut failed := 0
  for c in all do
    if c.ok then IO.println s!"  ok    {c.name}"
    else
      failed := failed + 1
      IO.println s!"  FAIL  {c.name}: {c.detail}"
  IO.println s!"{all.length - failed}/{all.length} passed"
  return if failed == 0 then 0 else 1
