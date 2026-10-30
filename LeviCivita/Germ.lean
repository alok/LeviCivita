import LeviCivita.NSA

/-!
# First-order germs: fast exact gradients

`FastLC.valueAndGrad` evaluates `f` once at `x + Σᵢ ε^{eᵢ} eᵢ`, with
`eᵢ = 1 + i/n ∈ [1, 2)`, and reads `∂ᵢf` off the coefficient of `ε^{eᵢ}`. In full
Levi-Civita arithmetic that is exact but wasteful: every product also creates
second-order terms (`ε^{eᵢ + eⱼ}`, valuation `≥ 2`) that are never read.

A `Germ` is a Levi-Civita number with every term of valuation `≥ 2` dropped.
Among finite elements those terms form an ideal (a finite element times
something of valuation `≥ 2` still has valuation `≥ 2`), so truncating after each
operation is a ring homomorphism: the coefficients that survive are exactly the
ones full arithmetic would give. A germ stays at most `n + 1` terms long (the
value and one term per coordinate).

The order on germs is the field order on the representatives, so `max`, `min`
and `abs` stay lexicographic in the coordinates, just like `FastLC.valueAndGrad`.
Only arguments with an infinitesimal standard part, such as `√` at `0` or
`1/x` at `x ≈ 0`, step outside the finite elements. There the truncation is no
longer exact, as is the gradient itself.
-/

namespace LeviCivita

open Fast FastLC

/-- A finite Levi-Civita number modulo terms of valuation `≥ 2`. -/
structure Germ where
  /-- A representative, with no term of valuation `≥ 2`. -/
  val : LC
  deriving Inhabited, Repr

namespace Germ

/-- Drop every term of valuation `≥ 2` (exponent `≤ −2`). -/
@[inline] def cut (x : LC) : Germ := ⟨{ terms := x.terms.filter (·.exp > -2.0) }⟩

instance : Add Germ := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : Sub Germ := ⟨fun a b => ⟨a.val - b.val⟩⟩
instance : Neg Germ := ⟨fun a => ⟨-a.val⟩⟩
instance : Mul Germ := ⟨fun a b => cut (a.val * b.val)⟩

/-- Inverse to the precision a germ keeps. -/
@[inline] def inv (a : Germ) : Germ := cut ((invertTo a.val 2.0).getD 0)

instance : Div Germ := ⟨fun a b => a * inv b⟩

/-- A germ `f(a + δ) = f(a) + f'(a) δ` from the value and derivative at the
standard part (`taylorAt` with three terms, so nothing of valuation `< 2` is
lost, then cut). Infinite input is `undefined`. -/
@[inline] def lift (f f' f'' : Float → Float) (a : Germ) : Germ :=
  let s := std a.val
  cut (taylorAt #[f s, f' s, f'' s] a.val)

/-- Strict order: the sign of the leading term of the difference. -/
@[inline] def lt (a b : Germ) : Bool := signum (b.val - a.val) > 0

instance : RealLike Germ where
  ofFloat x := ⟨FastLC.ofFloat x⟩
  inv := inv
  sqrt a := cut (rpow a.val 0.5 2.0)
  abs a := if signum a.val < 0 then -a else a
  max a b := if lt a b then b else a
  min a b := if lt b a then b else a
  lt := lt
  exp := lift Float.exp Float.exp Float.exp
  log := lift Float.log (fun x => 1.0 / x) (fun x => -1.0 / (x * x))
  sin := lift Float.sin Float.cos (fun x => -Float.sin x)
  cos := lift Float.cos (fun x => -Float.sin x) (fun x => -Float.cos x)

/-- Value and exact gradient of `f` at `x` in one evaluation on germs (the
seeding of `FastLC.valueAndGrad`). -/
def valueAndGrad {n : Nat} (f : (Fin n → Germ) → Germ) (x : Fin n → Float) :
    Float × Array Float :=
  let y := (f fun i => ⟨FastLC.ofFloat (x i) + { terms := #[⟨-seedExp n i.val, 1.0⟩] }⟩).val
  (std y, (List.finRange n).toArray.map fun i => getCoeff y (-seedExp n i.val))

/-- Exact gradient of `f` at `x` (see `valueAndGrad`). -/
def grad {n : Nat} (f : (Fin n → Germ) → Germ) (x : Fin n → Float) : Array Float :=
  (valueAndGrad f x).2

end Germ

end LeviCivita
