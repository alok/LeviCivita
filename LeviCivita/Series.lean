import LeviCivita.Frac

/-!
# Exact power and Laurent series in ε

`PS` is the ring of formal power series `Σₙ aₙ εⁿ` with rational coefficients:
infinite sums, no truncation. Multiplication is the Cauchy product, which needs
only finite sums. We prove that `PS` is an ordered integral domain, ordered by
the sign of its lowest nonzero coefficient, so `ε` is a positive infinitesimal.

Its field of fractions `Laurent := Frac PS` is the field `ℚ((ε))` of Laurent
series, an ordered field (`Lean.Grind.Field`, `Lean.Grind.OrderedRing`). It is a
subfield of the Levi-Civita field (the integer-exponent part). Unlike `LCFrac`
it contains `√(1 + ε)` (`Laurent.sqrtOnePlusEps_sq`) and the exact series
`1/(1 − ε) = Σ εⁿ` (`Laurent.inv_one_sub_eps`).

Everything is proved without `sorry`. The field operations use classical
decidability of equality (equality of infinite sequences is undecidable), but
every coefficient of a power series is computable: `#eval (sqrtOnePlus.coeff 5)`.
-/

namespace LeviCivita.Series

/-! ## Finite sums -/

/-- `S n f = f 0 + ⋯ + f (n - 1)`. -/
def S : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | n + 1, f => S n f + f n

@[simp] theorem S_zero (f : Nat → Rat) : S 0 f = 0 := rfl
theorem S_succ (n : Nat) (f : Nat → Rat) : S (n + 1) f = S n f + f n := rfl

theorem S_congr {n : Nat} {f g : Nat → Rat} (h : ∀ i, i < n → f i = g i) : S n f = S n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [S_succ, S_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem S_add (n : Nat) (f g : Nat → Rat) : S n (fun i => f i + g i) = S n f + S n g := by
  induction n with
  | zero => simp <;> grind
  | succ n ih => rw [S_succ, S_succ, S_succ, ih]; grind

theorem S_neg (n : Nat) (f : Nat → Rat) : S n (fun i => -f i) = -S n f := by
  induction n with
  | zero => simp <;> grind
  | succ n ih => rw [S_succ, S_succ, ih]; grind

theorem S_mul_left (n : Nat) (c : Rat) (f : Nat → Rat) : S n (fun i => c * f i) = c * S n f := by
  induction n with
  | zero => simp <;> grind
  | succ n ih => rw [S_succ, S_succ, ih]; grind

theorem S_mul_right (n : Nat) (c : Rat) (f : Nat → Rat) : S n (fun i => f i * c) = S n f * c := by
  induction n with
  | zero => simp <;> grind
  | succ n ih => rw [S_succ, S_succ, ih]; grind

theorem S_eq_zero {n : Nat} {f : Nat → Rat} (h : ∀ i, i < n → f i = 0) : S n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [S_succ, ih (fun i hi => h i (by omega)), h n (by omega)]; grind

/-- A sum with a single nonzero term. -/
theorem S_eq_single {n j : Nat} {f : Nat → Rat} (hj : j < n) (h : ∀ i, i < n → i ≠ j → f i = 0) :
    S n f = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [S_succ]
    by_cases hjn : j = n
    · subst hjn; rw [S_eq_zero (fun i hi => h i (by omega) (by omega))]; grind
    · rw [ih (by omega) (fun i hi hij => h i (by omega) hij), h n (by omega) (Ne.symm hjn)]; grind

/-- Peel off the first term. -/
theorem S_succ_left (n : Nat) (f : Nat → Rat) : S (n + 1) f = f 0 + S n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [S_succ] <;> grind
  | succ n ih => rw [S_succ, ih, S_succ]; grind

/-- Reverse the order of summation. -/
theorem S_reflect (n : Nat) (f : Nat → Rat) : S n f = S n (fun i => f (n - 1 - i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [S_succ, S_succ_left, ih]
    have : S n (fun i => f (n - 1 - i)) = S n (fun i => f (n + 1 - 1 - (i + 1))) :=
      S_congr (fun i hi => by congr 1; omega)
    rw [this]; simp only [Nat.add_sub_cancel]; grind

/-- Swap a triangular double sum. -/
theorem S_swap (N : Nat) (g : Nat → Nat → Rat) :
    S N (fun m => S (m + 1) (fun i => g i m)) = S N (fun i => S (N - i) (fun j => g i (i + j))) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [S_succ, ih]
    have h1 : S (N + 1) (fun i => S (N + 1 - i) (fun j => g i (i + j))) =
        S (N + 1) (fun i => S (N - i) (fun j => g i (i + j)) + g i N) := by
      apply S_congr; intro i hi
      rw [show N + 1 - i = (N - i) + 1 by omega, S_succ, show i + (N - i) = N by omega]
    rw [h1, S_add, S_succ (n := N) (f := fun i => S (N - i) _), Nat.sub_self, S_zero]
    grind

/-! ## Power series -/

/-- A formal power series `Σ coeff n · εⁿ`. -/
structure PS where
  coeff : Nat → Rat

namespace PS

@[ext] theorem ext {a b : PS} (h : ∀ n, a.coeff n = b.coeff n) : a = b := by
  cases a; cases b; congr; funext n; exact h n

/-- The constant series `c`. -/
def C (c : Rat) : PS := ⟨fun n => if n = 0 then c else 0⟩
/-- The series `ε`. -/
def X : PS := ⟨fun n => if n = 1 then 1 else 0⟩

instance : Zero PS := ⟨C 0⟩
instance : One PS := ⟨C 1⟩
instance : Add PS := ⟨fun a b => ⟨fun n => a.coeff n + b.coeff n⟩⟩
instance : Neg PS := ⟨fun a => ⟨fun n => -a.coeff n⟩⟩
instance : Sub PS := ⟨fun a b => a + -b⟩
/-- The Cauchy product: `(ab)ₙ = Σ_{i ≤ n} aᵢ bₙ₋ᵢ`. -/
instance : Mul PS := ⟨fun a b => ⟨fun n => S (n + 1) (fun i => a.coeff i * b.coeff (n - i))⟩⟩
instance : NatCast PS := ⟨fun n => C n⟩
instance : IntCast PS := ⟨fun i => C i⟩
instance : OfNat PS n := ⟨C n⟩
instance : SMul Nat PS := ⟨fun n a => C n * a⟩
instance : SMul Int PS := ⟨fun i a => C i * a⟩

/-- Powers by repeated multiplication. -/
def pow (a : PS) : Nat → PS
  | 0 => 1
  | n + 1 => pow a n * a

instance : HPow PS Nat PS := ⟨pow⟩

@[simp] theorem coeff_add (a b : PS) (n : Nat) : (a + b).coeff n = a.coeff n + b.coeff n := rfl
@[simp] theorem coeff_neg (a : PS) (n : Nat) : (-a).coeff n = -a.coeff n := rfl
@[simp] theorem coeff_sub (a b : PS) (n : Nat) : (a - b).coeff n = a.coeff n - b.coeff n := by
  show a.coeff n + -b.coeff n = _; grind
theorem coeff_mul (a b : PS) (n : Nat) :
    (a * b).coeff n = S (n + 1) (fun i => a.coeff i * b.coeff (n - i)) := rfl
@[simp] theorem coeff_C (c : Rat) (n : Nat) : (C c).coeff n = if n = 0 then c else 0 := rfl
@[simp] theorem coeff_zero (n : Nat) : (0 : PS).coeff n = 0 := by
  show (C 0).coeff n = 0; simp
theorem one_eq : (1 : PS) = C 1 := rfl
@[simp] theorem coeff_X (n : Nat) : X.coeff n = if n = 1 then 1 else 0 := rfl

theorem mul_C (a : PS) (c : Rat) : a * C c = ⟨fun n => a.coeff n * c⟩ := by
  ext n; rw [coeff_mul]
  rw [S_eq_single (j := n) (by omega) (fun i hi hin => by simp [show n - i ≠ 0 by omega])]
  simp

theorem mul_comm (a b : PS) : a * b = b * a := by
  ext n; rw [coeff_mul, coeff_mul, S_reflect]
  apply S_congr; intro i hi
  rw [show n + 1 - 1 - i = n - i by omega, show n - (n - i) = i by omega]; grind

theorem C_mul (c : Rat) (a : PS) : C c * a = ⟨fun n => c * a.coeff n⟩ := by
  rw [mul_comm, mul_C]; ext n; grind

theorem mul_assoc (a b c : PS) : a * b * c = a * (b * c) := by
  ext n; simp only [coeff_mul]
  rw [S_congr (g := fun m => S (m + 1) (fun i => a.coeff i * b.coeff (m - i) * c.coeff (n - m)))
    (fun m _ => by rw [← S_mul_right]), S_swap]
  apply S_congr; intro i hi
  rw [← S_mul_left, show n + 1 - i = n - i + 1 by omega]
  apply S_congr; intro j hj
  rw [show i + j - i = j by omega, show n - (i + j) = n - i - j by omega]; grind

theorem left_distrib (a b c : PS) : a * (b + c) = a * b + a * c := by
  ext n; simp only [coeff_mul, coeff_add]; rw [← S_add]; apply S_congr; intro i _; grind

theorem C_add (a b : Rat) : C (a + b) = C a + C b := by ext n; simp; split <;> grind

open Lean.Grind in
instance : CommRing PS where
  add_zero a := by ext n <;> simp <;> grind
  add_comm a b := by ext n <;> simp <;> grind
  add_assoc a b c := by ext n <;> simp <;> grind
  mul_assoc := mul_assoc
  mul_one a := by rw [one_eq, mul_C]; ext n <;> simp <;> grind
  one_mul a := by rw [one_eq, C_mul]; ext n <;> simp <;> grind
  left_distrib := left_distrib
  right_distrib a b c := by rw [mul_comm, left_distrib, mul_comm c, mul_comm c]
  zero_mul a := by
    show C 0 * a = C 0; rw [C_mul]; ext n <;> simp <;> grind
  mul_zero a := by
    show a * C 0 = C 0; rw [mul_C]; ext n <;> simp <;> grind
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := by
    show C ((n + 1 : Nat) : Rat) = C (n : Rat) + C 1
    rw [← C_add, Rat.natCast_add]; rfl
  ofNat_eq_natCast _ := rfl
  nsmul_eq_natCast_mul _ _ := rfl
  neg_add_cancel a := by ext n <;> simp <;> grind
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i a := by
    show C ((-i : Int) : Rat) * a = -(C (i : Rat) * a)
    rw [C_mul, C_mul]; ext n; simp only [coeff_neg]; rw [Rat.intCast_neg]; grind
  zsmul_natCast_eq_nsmul n a := by
    show C ((n : Int) : Rat) * a = C (n : Rat) * a
    rw [Rat.intCast_natCast]
  intCast_ofNat n := by
    show C ((n : Int) : Rat) = C (n : Rat)
    rw [Rat.intCast_natCast]
  intCast_neg i := by
    show C ((-i : Int) : Rat) = -C (i : Rat)
    ext n; simp only [coeff_neg, coeff_C]; rw [Rat.intCast_neg]; split <;> grind
  mul_comm := mul_comm

/-! ## Lowest terms, the order, and no zero divisors -/

/-- `p` is the order of `a`: the lowest index with a nonzero coefficient. -/
def IsOrd (a : PS) (p : Nat) : Prop := (∀ m, m < p → a.coeff m = 0) ∧ a.coeff p ≠ 0

private theorem exists_ord_aux (a : PS) :
    ∀ N, (∃ n, n < N ∧ a.coeff n ≠ 0) → ∃ p, IsOrd a p := by
  intro N
  induction N with
  | zero => intro ⟨n, hn, _⟩; omega
  | succ N ih =>
    intro ⟨n, hn, hne⟩
    by_cases h : ∃ m, m < N ∧ a.coeff m ≠ 0
    · exact ih h
    · have hnN : n = N := by
        apply Classical.byContradiction; intro hne'; exact h ⟨n, by omega, hne⟩
      subst hnN
      exact ⟨n, fun m hm => Classical.byContradiction fun h' => h ⟨m, hm, h'⟩, hne⟩

theorem exists_ord (a : PS) (h : a ≠ 0) : ∃ p, IsOrd a p := by
  have : ∃ n, a.coeff n ≠ 0 := Classical.byContradiction fun hn =>
    h (by ext n; simp; exact Classical.byContradiction fun h' => hn ⟨n, h'⟩)
  obtain ⟨n, hn⟩ := this
  exact exists_ord_aux a (n + 1) ⟨n, by omega, hn⟩

/-- The lowest coefficient of a product is the product of the lowest coefficients. -/
theorem mul_low (a b : PS) (p q : Nat) (ha : ∀ m, m < p → a.coeff m = 0)
    (hb : ∀ m, m < q → b.coeff m = 0) :
    (∀ k, k < p + q → (a * b).coeff k = 0) ∧ (a * b).coeff (p + q) = a.coeff p * b.coeff q := by
  constructor
  · intro k hk; rw [coeff_mul]; apply S_eq_zero; intro i hi
    by_cases hip : i < p
    · rw [ha i hip]; grind
    · rw [hb (k - i) (by omega)]; grind
  · rw [coeff_mul, S_eq_single (j := p) (by omega)]
    · rw [show p + q - p = q by omega]
    · intro i hi hip
      by_cases h : i < p
      · rw [ha i h]; grind
      · rw [hb (p + q - i) (by omega)]; grind

theorem mul_ne_zero {a b : PS} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  obtain ⟨p, hp0, hp⟩ := exists_ord a ha
  obtain ⟨q, hq0, hq⟩ := exists_ord b hb
  intro h
  have := (mul_low a b p q hp0 hq0).2
  rw [h, coeff_zero] at this
  rcases Rat.mul_eq_zero.mp this.symm with h | h
  · exact hp h
  · exact hq h

instance : Frac.IsDomain PS where
  zero_ne_one h := by
    have := congrArg (fun a : PS => a.coeff 0) h
    simp [one_eq] at this
  mul_ne_zero := mul_ne_zero

/-- `a` is positive: its lowest nonzero coefficient is positive. -/
def IsPos (a : PS) : Prop := ∃ p, (∀ m, m < p → a.coeff m = 0) ∧ 0 < a.coeff p

private theorem isPos_add {a b : PS} (ha : IsPos a) (hb : IsPos b) : IsPos (a + b) := by
  obtain ⟨p, hp0, hp⟩ := ha; obtain ⟨q, hq0, hq⟩ := hb
  refine ⟨min p q, fun m hm => ?_, ?_⟩
  · simp; rw [hp0 m (by omega), hq0 m (by omega)]; grind
  · simp
    rcases Nat.lt_trichotomy p q with h | h | h
    · rw [Nat.min_eq_left (by omega), hq0 p h]; grind
    · subst h; rw [Nat.min_self]; grind
    · rw [Nat.min_eq_right (by omega), hp0 q h]; grind

private theorem isPos_mul {a b : PS} (ha : IsPos a) (hb : IsPos b) : IsPos (a * b) := by
  obtain ⟨p, hp0, hp⟩ := ha; obtain ⟨q, hq0, hq⟩ := hb
  obtain ⟨h0, h1⟩ := mul_low a b p q hp0 hq0
  exact ⟨p + q, h0, by rw [h1]; exact Rat.mul_pos hp hq⟩

private theorem not_isPos_both (a : PS) (h1 : IsPos a) (h2 : IsPos (-a)) : False := by
  obtain ⟨p, hp0, hp⟩ := h1; obtain ⟨q, hq0, hq⟩ := h2
  simp only [coeff_neg] at hq0 hq
  rcases Nat.lt_trichotomy p q with h | h | h
  · have := hq0 p h; grind
  · subst h; grind
  · have := hp0 q h; grind

private theorem isPos_tri (a : PS) : a = 0 ∨ IsPos a ∨ IsPos (-a) := by
  by_cases h : a = 0
  · exact Or.inl h
  · obtain ⟨p, hp0, hp⟩ := exists_ord a h
    right
    rcases Nat.lt_or_ge 0 1 with _ | _
    · by_cases hpos : 0 < a.coeff p
      · exact Or.inl ⟨p, hp0, hpos⟩
      · exact Or.inr ⟨p, fun m hm => by simp [hp0 m hm], by simp <;> grind⟩
    · omega

private theorem not_isPos_zero : ¬ IsPos (0 : PS) := fun ⟨p, _, h⟩ => by simp at h

instance : LT PS := ⟨fun x y => IsPos (y - x)⟩
instance : LE PS := ⟨fun x y => x = y ∨ x < y⟩

theorem lt_def (x y : PS) : x < y ↔ IsPos (y - x) := Iff.rfl

theorem lt_irrefl (x : PS) : ¬ x < x := by
  rw [lt_def]; have : x - x = 0 := by grind
  rw [this]; exact not_isPos_zero

theorem lt_trans {x y z : PS} (h1 : x < y) (h2 : y < z) : x < z := by
  rw [lt_def] at *; have : z - x = (z - y) + (y - x) := by grind
  rw [this]; exact isPos_add h2 h1

theorem lt_asymm {x y : PS} (h1 : x < y) (h2 : y < x) : False := by
  rw [lt_def] at *; have : x - y = -(y - x) := by grind
  rw [this] at h2; exact not_isPos_both _ h1 h2

theorem lt_trichotomy (x y : PS) : x < y ∨ x = y ∨ y < x := by
  rcases isPos_tri (y - x) with h | h | h
  · exact Or.inr (Or.inl (by grind))
  · exact Or.inl h
  · right; right; rw [lt_def]; have : x - y = -(y - x) := by grind
    rw [this]; exact h

instance : Std.IsLinearOrder PS where
  le_refl _ := Or.inl rfl
  le_trans _ _ _ h1 h2 := by
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · exact Or.inl rfl
    · exact Or.inr h2
    · exact Or.inr h1
    · exact Or.inr (lt_trans h1 h2)
  le_antisymm _ _ h1 h2 := by
    rcases h1 with h1 | h1
    · exact h1
    · rcases h2 with h2 | h2
      · exact h2.symm
      · exact (lt_asymm h1 h2).elim
  le_total x y := by
    rcases lt_trichotomy x y with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)

instance : Std.LawfulOrderLT PS where
  lt_iff x y := by
    constructor
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (h' | h')
      · subst h'; exact lt_irrefl _ h
      · exact lt_asymm h h'
    · rintro ⟨h1 | h1, h2⟩
      · subst h1; exact (h2 (Or.inl rfl)).elim
      · exact h1

open Lean.Grind in
instance : OrderedAdd PS where
  add_le_left_iff {a b} c := by
    have key : b + c - (a + c) = b - a := by grind
    constructor
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr (by rw [lt_def, key]; exact h)
    · rintro (h | h)
      · left; have : a = a + c - c := by grind
        rw [this, h]; grind
      · exact Or.inr (by rw [lt_def, ← key]; exact h)

open Lean.Grind in
instance : OrderedRing PS where
  zero_lt_one := by
    rw [lt_def]; have : (1 : PS) - 0 = 1 := by grind
    rw [this]; exact ⟨0, fun m hm => by omega, by simp [one_eq] <;> decide⟩
  mul_lt_mul_of_pos_left {a b c} h hc := by
    rw [lt_def] at *; have : c * b - c * a = (c - 0) * (b - a) := by grind
    rw [this]; exact isPos_mul hc h
  mul_lt_mul_of_pos_right {a b c} h hc := by
    rw [lt_def] at *; have : b * c - a * c = (b - a) * (c - 0) := by grind
    rw [this]; exact isPos_mul h hc

/-! ## Exact series -/

/-- `ε` is a positive infinitesimal: `0 < ε < q` for every rational `q > 0`. -/
theorem X_pos : 0 < X :=
  ⟨1, fun m hm => by have : m = 0 := by omega
                     subst this; simp <;> grind, by simp <;> grind⟩

theorem X_lt_C {q : Rat} (hq : 0 < q) : X < C q := by
  rw [lt_def]; exact ⟨0, fun m hm => by omega, by simp; grind⟩

/-- The geometric series `1 + ε + ε² + ⋯`. -/
def geom : PS := ⟨fun _ => 1⟩

/-- `(1 − ε) · Σ εⁿ = 1`, exactly. -/
theorem one_sub_X_mul_geom : (1 - X) * geom = 1 := by
  ext n; rw [coeff_mul]
  cases n with
  | zero => simp [S_succ, one_eq, geom] <;> grind
  | succ n =>
    rw [S_succ_left, S_succ_left]
    rw [S_eq_zero (fun i hi => by
      simp [one_eq] <;> grind)]
    simp [one_eq, geom] <;> grind

/-- Coefficients of `√(1 + ε)`: `s₀ = 1` and `sₙ = −(Σ_{0<i<n} sᵢ sₙ₋ᵢ)/2`
(plus `1/2` at `n = 1`), from `Σ_{i ≤ n} sᵢ sₙ₋ᵢ = [n = 0] + [n = 1]`. -/
def sqrtCoeff : Nat → Rat
  | 0 => 1
  | n + 1 =>
    let inner := S n (fun i => if _ : i < n then sqrtCoeff (i + 1) * sqrtCoeff (n - i) else 0)
    ((if n = 0 then 1 else 0) - inner) / 2
termination_by n => n
decreasing_by all_goals omega

/-- `√(1 + ε) = 1 + ε/2 − ε²/8 + ε³/16 − ⋯` as an exact power series. -/
def sqrtOnePlus : PS := ⟨sqrtCoeff⟩

private theorem inner_eq (n : Nat) :
    S n (fun i => if _ : i < n then sqrtCoeff (i + 1) * sqrtCoeff (n - i) else 0) =
    S n (fun i => sqrtCoeff (i + 1) * sqrtCoeff (n - i)) :=
  S_congr (fun i hi => by simp [hi])

/-- `√(1 + ε)² = 1 + ε`, exactly. -/
theorem sqrtOnePlus_sq : sqrtOnePlus * sqrtOnePlus = 1 + X := by
  ext n; rw [coeff_mul]
  cases n with
  | zero => simp [S_succ, sqrtOnePlus, sqrtCoeff, one_eq] <;> grind
  | succ n =>
    -- Σ_{i ≤ n+1} sᵢ sₙ₊₁₋ᵢ = 2 s₀ sₙ₊₁ + Σ_{0<i<n+1} sᵢ sₙ₊₁₋ᵢ
    rw [S_succ_left, S_succ]
    simp only [sqrtOnePlus, Nat.sub_zero, Nat.sub_self]
    have hs : sqrtCoeff (n + 1) =
        ((if n = 0 then 1 else 0) - S n (fun i => sqrtCoeff (i + 1) * sqrtCoeff (n - i))) / 2 := by
      rw [sqrtCoeff, inner_eq]
    have hmid : S n (fun i => sqrtCoeff (i + 1) * sqrtCoeff (n + 1 - (i + 1))) =
        S n (fun i => sqrtCoeff (i + 1) * sqrtCoeff (n - i)) :=
      S_congr (fun i hi => by rw [show n + 1 - (i + 1) = n - i by omega])
    rw [hmid, hs, show sqrtCoeff 0 = 1 by rw [sqrtCoeff]]
    simp [one_eq]
    split <;> grind

end PS

/-! ## The Laurent series field -/

open PS Frac Lean.Grind

noncomputable instance : DecidableEq PS := fun a b => Classical.propDecidable (a = b)

/-- `ℚ((ε))`: Laurent series in `ε`, the fractions of power series. An ordered
field, and a subfield of the Levi-Civita field. -/
abbrev Laurent := Frac PS

namespace Laurent

/-- The infinitesimal `ε`. -/
def eps : Laurent := ofRing X
/-- A rational number. -/
def ofRat (q : Rat) : Laurent := ofRing (C q)
/-- `√(1 + ε)`. -/
def sqrtOnePlusEps : Laurent := ofRing sqrtOnePlus

theorem eps_pos : 0 < eps := ofRing_lt.mpr X_pos
theorem eps_lt_ofRat {q : Rat} (hq : 0 < q) : eps < ofRat q := ofRing_lt.mpr (X_lt_C hq)

theorem eps_ne_zero : eps ≠ 0 := fun h => by have := eps_pos; rw [h] at this; grind

/-- `H = ε⁻¹` is larger than every rational. -/
theorem ofRat_lt_inv_eps (q : Rat) : ofRat q < eps⁻¹ := by
  have he := eps_pos
  by_cases hq : q < 0
  · -- q < 0 < ε⁻¹
    have : ofRat q < 0 := ofRing_lt (R := PS) (a := C q) (b := C 0) |>.mpr
      (by rw [lt_def]; exact ⟨0, fun m hm => by omega, by simp; grind⟩)
    have : 0 < eps⁻¹ := Field.IsOrdered.inv_pos_iff.mpr he
    grind
  · -- ε < 1/(q+1), so q < q + 1 < ε⁻¹
    have h1 : eps < ofRat (1 / (q + 1)) := eps_lt_ofRat (by
      have : 0 < q + 1 := by grind
      have := Field.IsOrdered.inv_pos_iff.mpr this
      grind)
    have hq1 : ofRat (1 / (q + 1)) * ofRat (q + 1) = 1 := by
      unfold ofRat; rw [← ofRing_mul]
      have : C (1 / (q + 1)) * C (q + 1) = C 1 := by
        rw [mul_C]; ext n; simp; split
        · rw [Rat.div_mul_cancel (by grind)]
        · grind
      rw [this]; rfl
    have hadd : ofRat (q + 1) = ofRat q + 1 := by
      unfold ofRat; rw [C_add, ofRing_add]; rfl
    have hpos : 0 < ofRat (q + 1) := ofRing_lt.mpr (by
      rw [PS.lt_def]; exact ⟨0, fun m hm => by omega, by simp; grind⟩)
    -- ε · (q + 1) < 1, so q + 1 < ε⁻¹
    have : eps * ofRat (q + 1) < 1 := by
      rw [← hq1]; exact OrderedRing.mul_lt_mul_of_pos_right h1 hpos
    have : ofRat (q + 1) < eps⁻¹ := by
      have hinv := Field.mul_inv_cancel eps_ne_zero
      have := OrderedRing.mul_lt_mul_of_pos_left this (Field.IsOrdered.inv_pos_iff.mpr he)
      rw [← Semiring.mul_assoc, Field.inv_mul_cancel eps_ne_zero, Semiring.one_mul,
        Semiring.mul_one] at this
      exact this
    grind

/-- `√(1 + ε)² = 1 + ε` in the field. -/
theorem sqrtOnePlusEps_sq : sqrtOnePlusEps * sqrtOnePlusEps = 1 + eps := by
  unfold sqrtOnePlusEps eps; rw [← ofRing_mul, sqrtOnePlus_sq, ofRing_add]; rfl

/-- `1/(1 − ε) = 1 + ε + ε² + ⋯`, exactly. -/
theorem inv_one_sub_eps : (1 - eps)⁻¹ = ofRing geom := by
  have h : (1 - eps) * ofRing geom = 1 := by
    unfold eps
    have : (1 : Laurent) - ofRing X = ofRing (1 - X) := by
      show ofRing 1 + -ofRing X = ofRing (1 + -X)
      rw [ofRing_add]; rfl
    rw [this, ← ofRing_mul, one_sub_X_mul_geom]; rfl
  have hne : (1 : Laurent) - eps ≠ 0 := fun h0 => by rw [h0] at h; grind
  grind

end Laurent

end LeviCivita.Series
