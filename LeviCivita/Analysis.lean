import LeviCivita.Fast

/-!
# Ordered-field analysis on `FastLC`

The Levi-Civita field is a real-closed ordered field: every element has a sign
(the sign of its leading term), and every positive element has a square root.
This module exposes that structure for the Float-coefficient implementation
`FastLC`, which is what non-smooth geometric code (signed distance functions,
ray marchers, collision tests) needs:

* `signum`, `abs`, a decidable `<`/`≤`, `max`, `min`: the order compares the
  leading term of the difference, so `max (1 + ε) (1 + 2ε) = 1 + 2ε` — ties in
  the standard part are broken by the infinitesimal part. Applied to a seed
  `x + ε·v`, this makes `max`/`min`/`abs` return the *one-sided directional
  derivative* along `v` instead of an arbitrary subgradient.
* `sqrt`: binomial series around the leading term. `sqrt (a + bε)` with `a > 0`
  is `√a + (b / 2√a) ε + …`; `sqrt (bε)` is `√b · ε^{1/2}`, so a kink in a
  distance function shows up as a fractional exponent rather than a NaN.
* `grad`/`valueAndGrad`: forward-mode gradient of `f : (Fin n → LC) → LC`,
  seeding one coordinate at a time with `ε` and reading the `ε¹` coefficient.
  The result is the exact derivative up to Float rounding — there is no
  finite-difference step to tune.
-/

namespace LeviCivita.Fast.FastLC

/-- The dominant term (largest exponent), if the number is nonzero. -/
@[inline] def lead? (x : LC) : Option Term := x.terms[0]?

/-- Sign of the leading term: `1`, `-1` or `0`. -/
@[inline] def signum (x : LC) : Int :=
  match lead? x with
  | some t => if t.coeff > 0.0 then 1 else if t.coeff < 0.0 then -1 else 0
  | none => 0

/-- Absolute value in the ordered field. -/
@[inline] def abs (x : LC) : LC := if signum x < 0 then -x else x

/-- `x < y` iff `y - x` is positive. -/
instance : LT LC := ⟨fun x y => signum (y - x) > 0⟩
/-- `x ≤ y` iff `y - x` is not negative. -/
instance : LE LC := ⟨fun x y => signum (y - x) ≥ 0⟩

instance (x y : LC) : Decidable (x < y) :=
  inferInstanceAs (Decidable (signum (y - x) > 0))
instance (x y : LC) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (signum (y - x) ≥ 0))

instance : Max LC := ⟨fun x y => if x < y then y else x⟩
instance : Min LC := ⟨fun x y => if y < x then y else x⟩

/-- Scale by a Float. -/
@[inline] def smul (c : Float) (x : LC) : LC :=
  if c == 0.0 then 0 else { terms := x.terms.map fun t => ⟨t.exp, c * t.coeff⟩ }

/-- Drop every term with exponent below `minExp`. Forward-mode AD only needs
terms down to `ε¹` (exponent `-1`); truncating keeps arrays short in long
expressions without changing those coefficients. -/
@[inline] def truncBelow (minExp : Float) (x : LC) : LC :=
  { terms := x.terms.filter (·.exp ≥ minExp) }

/-- Square root of a non-negative element by the binomial series
`√(a εᵉ (1 + δ)) = √a ε^{e/2} Σₖ C(½,k) δᵏ`, summed to `order` terms of `δ`.
Returns `0` for negative input (as a total function; callers that care test
`signum` first). -/
def sqrt (x : LC) (order : Nat := 4) : LC := Id.run do
  let some l := lead? x | return 0
  if l.coeff ≤ 0.0 then return 0
  let leadInv : LC := { terms := #[⟨-l.exp, 1.0 / l.coeff⟩] }
  let delta := (x - { terms := #[l] }) * leadInv
  let mut acc : LC := 1
  let mut pow : LC := 1
  let mut c : Float := 1.0
  for k in [1:order + 1] do
    -- C(½,k) = C(½,k-1) · (½ - (k-1)) / k
    c := c * (0.5 - (k - 1).toFloat) / k.toFloat
    pow := pow * delta
    acc := acc + smul c pow
  return { terms := #[⟨l.exp / 2.0, Float.sqrt l.coeff⟩] } * acc

/-- Euclidean norm of a coordinate tuple. -/
def norm {n : Nat} (v : Fin n → LC) : LC :=
  sqrt ((List.finRange n).foldl (fun acc i => acc + v i * v i) 0)

/-- Value and exact gradient of `f` at `x`: coordinate `i` is seeded with `ε`,
and `∂ᵢf` is the `ε¹` coefficient of `f (x + ε eᵢ)`. -/
def valueAndGrad {n : Nat} (f : (Fin n → LC) → LC) (x : Fin n → Float) :
    Float × Array Float :=
  let base : Fin n → LC := fun j => ofFloat (x j)
  let value := std (f base)
  let grads := (List.finRange n).toArray.map fun i =>
    getCoeff (f fun j => if j == i then base j + epsilon else base j) (-1.0)
  (value, grads)

/-- Exact gradient of `f` at `x` (see `valueAndGrad`). -/
def grad {n : Nat} (f : (Fin n → LC) → LC) (x : Fin n → Float) : Array Float :=
  (valueAndGrad f x).2

end LeviCivita.Fast.FastLC
