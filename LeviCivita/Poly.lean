import LeviCivita.Series

/-!
# Polynomials over an ordered field

A polynomial is a power series `p : PS F` together with a degree bound `n`
(`IsPoly n p`: every coefficient above `n` vanishes). So polynomials inherit the
ring structure of `PS F` (the Cauchy product is polynomial multiplication).

* `eval n p x = Σ_{i ≤ n} pᵢ xⁱ`, a ring map (`eval_add`, `eval_mul`, …).
* `eval_eq_zero`: the identity theorem. A polynomial that vanishes at every
  point is zero, so polynomial identities can be proved by evaluating.
* `tay n p c`: the Taylor expansion of `p` at `c`, with `eval (tay n p c) z = p(c + z)`.
* `deriv p`: the formal derivative, a derivation; the Taylor coefficients of
  derivatives are `(tay (deriv p) c)ⱼ = (j + 1) (tay p c)ⱼ₊₁`.
* `Tendsto` and the limit rules for sums, products and polynomial evaluation.

Everything is generic over a `Lean.Grind` ordered field and proved without `sorry`.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita.Poly

open Lean.Grind Series Series.PS Classical

attribute [local instance] Semiring.natCast Ring.intCast
attribute [local instance high] Semiring.ofNat

/-! ## More finite sums -/

section Sums
variable {F : Type u} [CommRing F]

theorem S_comm (n m : Nat) (f : Nat → Nat → F) :
    S n (fun i => S m (fun j => f i j)) = S m (fun j => S n (fun i => f i j)) := by
  induction n with
  | zero => simp; exact (S_eq_zero (fun _ _ => rfl)).symm
  | succ n ih =>
    rw [S_succ, ih, ← S_add]
    apply S_congr; intro j _; rw [S_succ]

/-- Extend a sum by terms that vanish. -/
theorem S_extend {n m : Nat} (h : n ≤ m) {f : Nat → F} (hf : ∀ i, n ≤ i → i < m → f i = 0) :
    S m f = S n f := by
  induction m with
  | zero => have : n = 0 := by omega
            subst this; rfl
  | succ m ih =>
    by_cases hnm : n = m + 1
    · subst hnm; rfl
    · rw [S_succ, ih (by omega) (fun i h1 h2 => hf i h1 (by omega)), hf m (by omega) (by omega)]
      grind

theorem S_pow_mul (n : Nat) (f : Nat → F) (x : F) :
    S n (fun i => f i * x ^ (i + 1)) = x * S n (fun i => f i * x ^ i) := by
  rw [← S_mul_left]; apply S_congr; intro i _; rw [Semiring.pow_succ]; grind

end Sums

/-! ## Absolute values in an ordered field -/

section Abs
variable {F : Type u} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F]
  [OrderedRing F]

/-- `|x|`. -/
noncomputable def abs (x : F) : F := if 0 ≤ x then x else -x

theorem abs_of_nonneg {x : F} (h : 0 ≤ x) : abs x = x := by simp [abs, h]
theorem abs_of_neg {x : F} (h : x < 0) : abs x = -x := by
  have : ¬ 0 ≤ x := by grind
  simp [abs, this]
theorem abs_nonneg (x : F) : 0 ≤ abs x := by
  unfold abs; split <;> grind
theorem le_abs (x : F) : x ≤ abs x := by unfold abs; split <;> grind
theorem neg_le_abs (x : F) : -x ≤ abs x := by unfold abs; split <;> grind
theorem abs_neg (x : F) : abs (-x) = abs x := by
  unfold abs; split <;> split <;> grind
theorem abs_zero : abs (0 : F) = 0 := abs_of_nonneg (by grind)
theorem abs_le_iff {x d : F} : abs x ≤ d ↔ x ≤ d ∧ -x ≤ d := by
  unfold abs; split <;> constructor <;> intro h <;> grind
theorem abs_lt_iff {x d : F} : abs x < d ↔ x < d ∧ -x < d := by
  unfold abs; split <;> constructor <;> intro h <;> grind
theorem abs_add_le (x y : F) : abs (x + y) ≤ abs x + abs y := by
  rw [abs_le_iff]; have := le_abs x; have := le_abs y; have := neg_le_abs x
  have := neg_le_abs y; constructor <;> grind
theorem abs_sub_comm (x y : F) : abs (x - y) = abs (y - x) := by
  rw [← abs_neg]; congr 1; grind
theorem abs_eq_zero {x : F} : abs x = 0 ↔ x = 0 := by
  unfold abs; split <;> constructor <;> intro h <;> grind
theorem abs_pos {x : F} (h : x ≠ 0) : 0 < abs x := by
  have := abs_nonneg x; have : abs x ≠ 0 := fun h' => h (abs_eq_zero.mp h'); grind

theorem abs_mul (x y : F) : abs (x * y) = abs x * abs y := by
  rcases (by grind : 0 ≤ x ∨ x < 0) with hx | hx <;>
  rcases (by grind : 0 ≤ y ∨ y < 0) with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg (OrderedRing.mul_nonneg hx hy)]
  · rw [abs_of_nonneg hx, abs_of_neg hy]
    rcases (by grind : x = 0 ∨ 0 < x) with h | h
    · subst h; rw [abs_of_nonneg (by grind)]; grind
    · rw [abs_of_neg (OrderedRing.mul_neg_of_pos_of_neg h hy)]; grind
  · rw [abs_of_neg hx, abs_of_nonneg hy]
    rcases (by grind : y = 0 ∨ 0 < y) with h | h
    · subst h; rw [abs_of_nonneg (by grind)]; grind
    · rw [abs_of_neg (OrderedRing.mul_neg_of_neg_of_pos hx h)]; grind
  · rw [abs_of_neg hx, abs_of_neg hy,
      abs_of_nonneg (Std.le_of_lt (OrderedRing.mul_pos_of_neg_of_neg hx hy))]; grind

theorem abs_pow (x : F) (n : Nat) : abs (x ^ n) = abs x ^ n := by
  induction n with
  | zero => rw [Semiring.pow_zero, Semiring.pow_zero, abs_of_nonneg (by grind)]
  | succ n ih => rw [Semiring.pow_succ, Semiring.pow_succ, abs_mul, ih]

theorem mul_le_mul_of_le {a b c d : F} (h1 : a ≤ b) (h2 : c ≤ d) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    a * c ≤ b * d := by
  have : a * c ≤ a * d := OrderedRing.mul_le_mul_of_nonneg_left h2 ha
  have : a * d ≤ b * d := OrderedRing.mul_le_mul_of_nonneg_right h1 (by grind)
  grind

theorem pow_nonneg {x : F} (h : 0 ≤ x) (n : Nat) : 0 ≤ x ^ n := by
  induction n with
  | zero => rw [Semiring.pow_zero]; grind
  | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih h

theorem pow_le_pow_left {x y : F} (h0 : 0 ≤ x) (h : x ≤ y) (n : Nat) : x ^ n ≤ y ^ n := by
  induction n with
  | zero => grind
  | succ n ih => rw [Semiring.pow_succ, Semiring.pow_succ]
                 exact mul_le_mul_of_le ih h (pow_nonneg h0 n) h0

theorem one_pow (n : Nat) : (1 : F) ^ n = 1 := by
  induction n with
  | zero => rw [Semiring.pow_zero]
  | succ n ih => rw [Semiring.pow_succ, ih]; grind

theorem pow_le_one {x : F} (h0 : 0 ≤ x) (h : x ≤ 1) (n : Nat) : x ^ n ≤ 1 := by
  have := pow_le_pow_left h0 h n
  rw [one_pow] at this; exact this

theorem S_nonneg {n : Nat} {f : Nat → F} (h : ∀ i, i < n → 0 ≤ f i) : 0 ≤ S n f := by
  induction n with
  | zero => exact Std.le_refl _
  | succ n ih => rw [S_succ]; have := ih (fun i hi => h i (by omega)); have := h n (by omega); grind

theorem S_le {n : Nat} {f g : Nat → F} (h : ∀ i, i < n → f i ≤ g i) : S n f ≤ S n g := by
  induction n with
  | zero => exact Std.le_refl _
  | succ n ih => rw [S_succ, S_succ]; have := ih (fun i hi => h i (by omega)); have := h n (by omega); grind

theorem abs_S_le (n : Nat) (f : Nat → F) : abs (S n f) ≤ S n (fun i => abs (f i)) := by
  induction n with
  | zero => simp; rw [abs_zero]; grind
  | succ n ih => rw [S_succ, S_succ]; have := abs_add_le (S n f) (f n); grind

end Abs

/-! ## Polynomials and evaluation -/

variable {F : Type u} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F]
  [OrderedRing F]

/-- `p` has degree at most `n`. -/
def IsPoly (n : Nat) (p : PS F) : Prop := ∀ i, n < i → p.coeff i = 0

/-- `p(x) = Σ_{i ≤ n} pᵢ xⁱ`. -/
def eval (n : Nat) (p : PS F) (x : F) : F := S (n + 1) (fun i => p.coeff i * x ^ i)

theorem IsPoly.mono {n m : Nat} {p : PS F} (h : IsPoly n p) (hnm : n ≤ m) : IsPoly m p :=
  fun i hi => h i (by omega)

/-- The value does not depend on the degree bound. -/
theorem eval_mono {n m : Nat} {p : PS F} (h : IsPoly n p) (hnm : n ≤ m) (x : F) :
    eval m p x = eval n p x :=
  S_extend (by omega) (fun i h1 _ => by rw [h i (by omega)]; grind)

theorem isPoly_C (c : F) : IsPoly 0 (C c) := fun i hi => by simp; omega
theorem isPoly_X : IsPoly 1 (X : PS F) := fun i hi => by simp; omega
theorem isPoly_zero (n : Nat) : IsPoly n (0 : PS F) := fun i _ => coeff_zero i
theorem isPoly_one (n : Nat) : IsPoly n (1 : PS F) := (isPoly_C 1).mono (by omega)
theorem isPoly_add {n : Nat} {p q : PS F} (hp : IsPoly n p) (hq : IsPoly n q) :
    IsPoly n (p + q) := fun i hi => by rw [coeff_add, hp i hi, hq i hi]; grind
theorem isPoly_neg {n : Nat} {p : PS F} (hp : IsPoly n p) : IsPoly n (-p) :=
  fun i hi => by rw [coeff_neg, hp i hi]; grind
theorem isPoly_sub {n : Nat} {p q : PS F} (hp : IsPoly n p) (hq : IsPoly n q) :
    IsPoly n (p - q) := fun i hi => by rw [coeff_sub, hp i hi, hq i hi]; grind
theorem isPoly_mul {n m : Nat} {p q : PS F} (hp : IsPoly n p) (hq : IsPoly m q) :
    IsPoly (n + m) (p * q) := fun k hk => by
  rw [coeff_mul]; apply S_eq_zero; intro i hi
  by_cases h : n < i
  · rw [hp i h]; grind
  · rw [hq (k - i) (by omega)]; grind
theorem isPoly_pow {n : Nat} {p : PS F} (hp : IsPoly n p) (k : Nat) : IsPoly (n * k) (p ^ k) := by
  induction k with
  | zero => exact isPoly_one _
  | succ k ih => rw [Nat.mul_succ]; exact isPoly_mul ih hp

theorem eval_add {n : Nat} (p q : PS F) (x : F) : eval n (p + q) x = eval n p x + eval n q x := by
  unfold eval; rw [← S_add]; apply S_congr; intro i _; simp; grind

theorem eval_neg {n : Nat} (p : PS F) (x : F) : eval n (-p) x = -eval n p x := by
  unfold eval; rw [← S_neg]; apply S_congr; intro i _; simp; grind

theorem eval_sub {n : Nat} (p q : PS F) (x : F) : eval n (p - q) x = eval n p x - eval n q x := by
  unfold eval; rw [show (fun i => (p - q).coeff i * x ^ i) =
    fun i => p.coeff i * x ^ i + -(q.coeff i * x ^ i) from funext fun i => by simp; grind,
    S_add, S_neg]; grind

theorem eval_C (n : Nat) (c x : F) : eval n (C c) x = c := by
  unfold eval; rw [S_eq_single (j := 0) (by omega) (fun i _ hi => by simp [hi]; grind)]
  simp; rw [Semiring.pow_zero]; grind

theorem eval_X {n : Nat} (hn : 1 ≤ n) (x : F) : eval n (X : PS F) x = x := by
  unfold eval; rw [S_eq_single (j := 1) (by omega) (fun i _ hi => by simp [hi]; grind)]
  simp; rw [Semiring.pow_one]; grind

theorem eval_zero (n : Nat) (x : F) : eval n (0 : PS F) x = 0 := eval_C n 0 x
theorem eval_one (n : Nat) (x : F) : eval n (1 : PS F) x = 1 := eval_C n 1 x

/-- Evaluation is multiplicative. -/
theorem eval_mul {n m : Nat} {p q : PS F} (hp : IsPoly n p) (hq : IsPoly m q) (x : F) :
    eval (n + m) (p * q) x = eval n p x * eval m q x := by
  unfold eval
  simp only [coeff_mul]
  -- Σ_{k ≤ n+m} Σ_{i ≤ k} pᵢ q_{k-i} xᵏ = Σ_{i ≤ n+m} Σ_{j < n+m+1-i} pᵢ qⱼ x^{i+j}
  rw [S_congr (g := fun k => S (k + 1) (fun i => p.coeff i * q.coeff (k - i) * x ^ k))
    (fun k _ => by rw [← S_mul_right]), S_swap]
  rw [S_extend (n := n + 1) (by omega) (fun i h1 _ => S_eq_zero (fun j _ => by
    rw [hp i (by omega)]; grind))]
  rw [← S_mul_right]
  apply S_congr; intro i hi
  rw [← S_mul_left]
  rw [S_extend (n := m + 1) (f := fun j => p.coeff i * q.coeff (i + j - i) * x ^ (i + j))
    (by omega) (fun j h1 _ => by simp only [Nat.add_sub_cancel_left]; rw [hq j (by omega)]; grind)]
  apply S_congr; intro j _
  rw [Nat.add_sub_cancel_left, Semiring.pow_add]; grind

theorem eval_pow {n : Nat} {p : PS F} (hp : IsPoly n p) (k : Nat) (x : F) :
    eval (n * k) (p ^ k) x = eval n p x ^ k := by
  induction k with
  | zero => show eval 0 (1 : PS F) x = _; rw [eval_one, Semiring.pow_zero]
  | succ k ih =>
    show eval (n * (k + 1)) (p ^ k * p) x = _
    rw [show n * (k + 1) = n * k + n from Nat.mul_succ n k, eval_mul (isPoly_pow hp k) hp, ih,
      Semiring.pow_succ]

/-- Evaluate with any larger bound. -/
theorem eval_mul' {n m N : Nat} {p q : PS F} (hp : IsPoly n p) (hq : IsPoly m q) (hN : n + m ≤ N)
    (x : F) : eval N (p * q) x = eval n p x * eval m q x := by
  rw [eval_mono (isPoly_mul hp hq) hN, eval_mul hp hq]

/-! ## The identity theorem -/

/-- Drop the constant term: `(shiftDown p)ᵢ = pᵢ₊₁`. -/
def shiftDown (p : PS F) : PS F := ⟨fun i => p.coeff (i + 1)⟩

theorem eval_succ (n : Nat) (p : PS F) (x : F) :
    eval (n + 1) p x = p.coeff 0 + x * eval n (shiftDown p) x := by
  unfold eval; rw [S_succ_left, Semiring.pow_zero, ← S_pow_mul]; simp [shiftDown]; grind

theorem abs_eval_le (n : Nat) (p : PS F) {x : F} (hx : abs x ≤ 1) :
    abs (eval n p x) ≤ S (n + 1) (fun i => abs (p.coeff i)) := by
  unfold eval
  refine Std.le_trans (abs_S_le _ _) (S_le fun i _ => ?_)
  rw [abs_mul, abs_pow]
  have h1 := pow_le_one (abs_nonneg x) hx i
  have := OrderedRing.mul_le_mul_of_nonneg_left h1 (abs_nonneg (p.coeff i))
  grind

/-- **Identity theorem**: a polynomial that vanishes at every positive point is zero. -/
theorem eq_zero_of_eval_pos {n : Nat} {p : PS F} (hp : IsPoly n p)
    (h : ∀ x, 0 < x → eval n p x = 0) : p = 0 := by
  induction n generalizing p with
  | zero =>
    ext i
    cases i with
    | zero => have := h 1 OrderedRing.zero_lt_one
              unfold eval at this; simp at this; rw [Semiring.pow_zero] at this; simp; grind
    | succ i => rw [hp (i + 1) (by omega)]; simp
  | succ n ih =>
    have hq : IsPoly n (shiftDown p) := fun i hi => hp (i + 1) (by omega)
    -- the constant term vanishes
    have h0 : p.coeff 0 = 0 := by
      apply Classical.byContradiction; intro hne
      let B := S (n + 1) (fun i => abs ((shiftDown p).coeff i)) + 1
      have hB : 0 < B := by
        have := S_nonneg (n := n + 1) (f := fun i => abs ((shiftDown p).coeff i))
          (fun i _ => abs_nonneg _); grind
      have ha := abs_pos hne
      let x := abs (p.coeff 0) * (B + abs (p.coeff 0))⁻¹
      have hden : 0 < B + abs (p.coeff 0) := by grind
      have hinv := Field.IsOrdered.inv_pos_iff.mpr hden
      have hx : 0 < x := OrderedRing.mul_pos ha hinv
      have hx1 : x * (B + abs (p.coeff 0)) = abs (p.coeff 0) := by
        have := Field.mul_inv_cancel (show B + abs (p.coeff 0) ≠ 0 by grind)
        show abs (p.coeff 0) * (B + abs (p.coeff 0))⁻¹ * (B + abs (p.coeff 0)) = _
        grind
      have hxle : x ≤ 1 := by
        apply Classical.byContradiction; intro hlt
        have : 1 * (B + abs (p.coeff 0)) < x * (B + abs (p.coeff 0)) :=
          OrderedRing.mul_lt_mul_of_pos_right (by grind) hden
        grind
      have hev := h x hx
      rw [eval_succ] at hev
      have hb := abs_eval_le n (shiftDown p) (x := x) (by rw [abs_of_nonneg (by grind)]; exact hxle)
      -- |p₀| = x |q(x)| ≤ x (B - 1) < x B
      have e : abs (p.coeff 0) = x * abs (eval n (shiftDown p) x) := by
        rw [show p.coeff 0 = -(x * eval n (shiftDown p) x) by grind, abs_neg, abs_mul,
          abs_of_nonneg (Std.le_of_lt hx)]
      have : x * abs (eval n (shiftDown p) x) ≤ x * (B - 1) :=
        OrderedRing.mul_le_mul_of_nonneg_left (by grind) (Std.le_of_lt hx)
      have : x * (B - 1) < x * B := OrderedRing.mul_lt_mul_of_pos_left (by grind) hx
      -- but x B < |p₀| since x (B + |p₀|) = |p₀|
      have : x * B < abs (p.coeff 0) := by
        have : 0 < x * abs (p.coeff 0) := OrderedRing.mul_pos hx ha
        grind
      grind
    have hs : shiftDown p = 0 := ih hq (fun x hx => by
      have := h x hx; rw [eval_succ, h0] at this
      have hne : x ≠ 0 := by grind
      have hinv := Field.inv_mul_cancel hne
      calc eval n (shiftDown p) x = x⁻¹ * (0 + x * eval n (shiftDown p) x) := by grind
        _ = 0 := by rw [this]; grind)
    ext i
    cases i with
    | zero => rw [h0]; simp
    | succ i => have := congrArg (fun q => q.coeff i) hs; simp [shiftDown] at this; simp; exact this

/-- Polynomials that agree at every positive point are equal. -/
theorem eq_of_eval_pos {n : Nat} {p q : PS F} (hp : IsPoly n p) (hq : IsPoly n q)
    (h : ∀ x, 0 < x → eval n p x = eval n q x) : p = q := by
  have := eq_zero_of_eval_pos (isPoly_sub hp hq) (fun x hx => by rw [eval_sub, h x hx]; grind)
  grind

/-! ## Sums of polynomials -/

theorem coeff_S (k : Nat) (f : Nat → PS F) (j : Nat) :
    (S k f).coeff j = S k (fun i => (f i).coeff j) := by
  induction k with
  | zero => show (0 : PS F).coeff j = 0; simp
  | succ k ih => rw [S_succ, S_succ, coeff_add, ih]

theorem isPoly_S {n k : Nat} {f : Nat → PS F} (h : ∀ i, i < k → IsPoly n (f i)) :
    IsPoly n (S k f) := fun j hj => by
  rw [coeff_S]; exact S_eq_zero (fun i hi => h i hi j hj)

theorem eval_S (n k : Nat) (f : Nat → PS F) (x : F) :
    eval n (S k f) x = S k (fun i => eval n (f i) x) := by
  induction k with
  | zero => exact eval_zero n x
  | succ k ih => rw [S_succ, S_succ, eval_add, ih]

theorem C_mul' (a b : F) : C (a * b) = C a * C b := by
  rw [C_mul]; ext n; simp; split <;> grind

theorem C_neg (a : F) : C (-a) = -C a := by ext n; simp; split <;> grind

theorem C_natCast (k : Nat) : C (k : F) = (k : PS F) := rfl

/-! ## Taylor expansion -/

/-- The Taylor expansion of `p` at `c`: the polynomial `z ↦ p(c + z)`,
`Σ_{i ≤ n} pᵢ (c + z)ⁱ`. Its coefficients are the Taylor coefficients of `p` at `c`. -/
def tay (n : Nat) (p : PS F) (c : F) : PS F := S (n + 1) (fun i => C (p.coeff i) * (C c + X) ^ i)

theorem isPoly_lin (c : F) : IsPoly 1 (C c + X : PS F) :=
  isPoly_add ((isPoly_C c).mono (by omega)) isPoly_X

theorem isPoly_tay (n : Nat) (p : PS F) (c : F) : IsPoly n (tay n p c) :=
  isPoly_S fun i hi => by
    have := isPoly_mul (isPoly_C (p.coeff i)) (isPoly_pow (isPoly_lin c) i)
    exact this.mono (by omega)

theorem eval_lin (c z : F) : eval 1 (C c + X : PS F) z = c + z := by
  rw [eval_add, eval_C, eval_X (Nat.le_refl 1)]

/-- `tay n p c` is `z ↦ p(c + z)`. -/
theorem eval_tay (n : Nat) (p : PS F) (c z : F) : eval n (tay n p c) z = eval n p (c + z) := by
  unfold tay; rw [eval_S]
  show _ = S (n + 1) (fun i => p.coeff i * (c + z) ^ i)
  apply S_congr; intro i hi
  rw [eval_mul' (isPoly_C (p.coeff i)) (isPoly_pow (isPoly_lin c) i) (N := n) (by omega),
    eval_C, eval_pow (isPoly_lin c), eval_lin]

/-- The constant Taylor coefficient is the value. -/
theorem tay_coeff_zero (n : Nat) (p : PS F) (c : F) : (tay n p c).coeff 0 = eval n p c := by
  have := eval_tay n p c 0
  unfold eval at this
  rw [S_succ_left, Semiring.pow_zero, S_eq_zero (fun i _ => by
    rw [Semiring.pow_succ]; grind)] at this
  rw [show c + 0 = c by grind] at this; unfold eval; grind

/-- Taylor expansion at `0` does nothing. -/
theorem tay_zero {n : Nat} {p : PS F} (hp : IsPoly n p) : tay n p 0 = p :=
  eq_of_eval_pos (isPoly_tay n p 0) hp (fun z _ => by rw [eval_tay]; congr 1; grind)

/-- Re-expanding: the expansion of `tay p c` at `w` is the expansion of `p` at `c + w`. -/
theorem tay_tay (n : Nat) (p : PS F) (c w : F) : tay n (tay n p c) w = tay n p (c + w) :=
  eq_of_eval_pos (isPoly_tay _ _ _) (isPoly_tay _ _ _) (fun z _ => by
    rw [eval_tay, eval_tay, eval_tay]; congr 1; grind)

/-! ## The formal derivative -/

/-- `(Σ pᵢ Xⁱ)' = Σ (i + 1) pᵢ₊₁ Xⁱ`. -/
def deriv (p : PS F) : PS F := ⟨fun i => ((i + 1 : Nat) : F) * p.coeff (i + 1)⟩

@[simp] theorem coeff_deriv (p : PS F) (i : Nat) :
    (deriv p).coeff i = ((i + 1 : Nat) : F) * p.coeff (i + 1) := rfl

theorem isPoly_deriv {n : Nat} {p : PS F} (hp : IsPoly n p) : IsPoly n (deriv p) :=
  fun i hi => by rw [coeff_deriv, hp (i + 1) (by omega)]; grind

theorem deriv_add (p q : PS F) : deriv (p + q) = deriv p + deriv q := by
  ext i; simp; grind

theorem deriv_C (c : F) : deriv (C c) = 0 := by ext i; simp; grind

theorem deriv_X : deriv (X : PS F) = 1 := by
  ext i; rw [coeff_deriv, coeff_X, one_eq, coeff_C]
  by_cases h : i = 0
  · subst h; simp; rw [Semiring.natCast_one]; grind
  · simp [h]; grind

/-- **Leibniz rule**. -/
theorem deriv_mul (p q : PS F) : deriv (p * q) = deriv p * q + p * deriv q := by
  ext k
  simp only [coeff_deriv, coeff_add, coeff_mul]
  -- (k + 1) = i + (k + 1 - i)
  have split : ∀ i, i < k + 1 + 1 → ((k + 1 : Nat) : F) * (p.coeff i * q.coeff (k + 1 - i)) =
      (i : F) * (p.coeff i * q.coeff (k + 1 - i)) +
        ((k + 1 - i : Nat) : F) * (p.coeff i * q.coeff (k + 1 - i)) := fun i hi => by
    rw [show k + 1 = i + (k + 1 - i) by omega, Semiring.natCast_add]
    rw [show i + (k + 1 - i) - i = k + 1 - i by omega]; grind
  rw [← S_mul_left, S_congr split, S_add]
  congr 1
  · rw [S_succ_left, Semiring.natCast_zero]
    apply Eq.trans (by grind : _ = S (k + 1) (fun i => ((i + 1 : Nat) : F) *
      (p.coeff (i + 1) * q.coeff (k + 1 - (i + 1)))))
    apply S_congr; intro i hi
    rw [show k + 1 - (i + 1) = k - i by omega]; grind
  · rw [S_succ, Nat.sub_self, Semiring.natCast_zero]
    apply Eq.trans (by grind : _ = S (k + 1) (fun i => ((k + 1 - i : Nat) : F) *
      (p.coeff i * q.coeff (k + 1 - i))))
    apply S_congr; intro i hi
    rw [show k + 1 - i = k - i + 1 by omega]; grind

theorem deriv_C_mul (c : F) (p : PS F) : deriv (C c * p) = C c * deriv p := by
  rw [deriv_mul, deriv_C]; grind

theorem deriv_pow (q : PS F) (i : Nat) :
    deriv (q ^ (i + 1)) = ((i + 1 : Nat) : PS F) * q ^ i * deriv q := by
  induction i with
  | zero =>
    show deriv (1 * q) = _
    rw [show ((0 + 1 : Nat) : PS F) = 1 from Semiring.natCast_one]; grind
  | succ i ih =>
    show deriv (q ^ (i + 1) * q) = _
    rw [deriv_mul, ih, Semiring.natCast_add (i + 1) 1, Semiring.natCast_one]
    show _ = (_ + 1) * (q ^ i * q) * deriv q
    rw [show q ^ (i + 1) = q ^ i * q from rfl]; grind

theorem deriv_S (k : Nat) (f : Nat → PS F) : deriv (S k f) = S k (fun i => deriv (f i)) := by
  induction k with
  | zero => show deriv (0 : PS F) = 0; ext i; simp; grind
  | succ k ih => rw [S_succ, S_succ, deriv_add, ih]

/-- The derivative commutes with Taylor expansion. -/
theorem deriv_tay {n : Nat} {p : PS F} (hp : IsPoly n p) (c : F) :
    deriv (tay n p c) = tay n (deriv p) c := by
  unfold tay
  rw [deriv_S, S_succ_left, S_succ]
  have hlin : deriv (C c + X : PS F) = 1 := by rw [deriv_add, deriv_C, deriv_X]; grind
  have h0 : deriv (C (p.coeff 0) * (C c + X) ^ 0) = 0 := by
    show deriv (C (p.coeff 0) * 1) = 0; rw [deriv_C_mul]
    show C (p.coeff 0) * deriv (C 1) = 0; rw [deriv_C]; grind
  have hlast : C ((deriv p).coeff n) * (C c + X) ^ n = 0 := by
    rw [coeff_deriv, hp (n + 1) (by omega)]
    show C (((n + 1 : Nat) : F) * 0) * _ = 0
    rw [show ((n + 1 : Nat) : F) * 0 = 0 by grind]
    show (0 : PS F) * _ = 0; grind
  rw [h0, hlast]
  have : S n (fun i => deriv (C (p.coeff (i + 1)) * (C c + X) ^ (i + 1))) =
      S n (fun i => C ((deriv p).coeff i) * (C c + X) ^ i) := by
    apply S_congr; intro i _
    rw [deriv_C_mul, deriv_pow, hlin, coeff_deriv, C_mul', C_natCast]; grind
  rw [this]; grind

/-- Taylor coefficients of the derivative: `(p')⁽ʲ⁾(c)/j! = (j + 1) · p⁽ʲ⁺¹⁾(c)/(j + 1)!`. -/
theorem tay_deriv_coeff {n : Nat} {p : PS F} (hp : IsPoly n p) (c : F) (j : Nat) :
    (tay n (deriv p) c).coeff j = ((j + 1 : Nat) : F) * (tay n p c).coeff (j + 1) := by
  rw [← deriv_tay hp]; rfl

/-! ### Iterated derivatives -/

/-- `ff j k = (j + 1) (j + 2) ⋯ (j + k)`. -/
def ff : Nat → Nat → Nat
  | _, 0 => 1
  | j, k + 1 => (j + 1) * ff (j + 1) k

theorem ff_pos (j k : Nat) : 0 < ff j k := by
  induction k generalizing j with
  | zero => simp [ff]
  | succ k ih => simp only [ff]; exact Nat.mul_pos (by omega) (ih (j + 1))

/-- The `k`-th derivative. -/
def derivN : Nat → PS F → PS F
  | 0, p => p
  | k + 1, p => deriv (derivN k p)

theorem isPoly_derivN {n : Nat} {p : PS F} (hp : IsPoly n p) (k : Nat) : IsPoly n (derivN k p) := by
  induction k with
  | zero => exact hp
  | succ k ih => exact isPoly_deriv ih

theorem coeff_derivN (p : PS F) (k i : Nat) :
    (derivN k p).coeff i = (ff i k : F) * p.coeff (i + k) := by
  induction k generalizing i with
  | zero => show p.coeff i = _; simp [ff]; rw [Semiring.natCast_one]; grind
  | succ k ih =>
    show (deriv (derivN k p)).coeff i = _
    rw [coeff_deriv, ih, show i + (k + 1) = i + 1 + k by omega]
    simp only [ff]; rw [Semiring.natCast_mul]; grind

theorem tay_derivN_coeff {n : Nat} {p : PS F} (hp : IsPoly n p) (c : F) (k j : Nat) :
    (tay n (derivN k p) c).coeff j = (ff j k : F) * (tay n p c).coeff (j + k) := by
  induction k generalizing j with
  | zero => show (tay n p c).coeff j = _; simp [ff]; rw [Semiring.natCast_one]; grind
  | succ k ih =>
    show (tay n (deriv (derivN k p)) c).coeff j = _
    rw [tay_deriv_coeff (isPoly_derivN hp k), ih, show j + (k + 1) = j + 1 + k by omega]
    simp only [ff]; rw [Semiring.natCast_mul]; grind

end LeviCivita.Poly
