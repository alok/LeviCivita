import LeviCivita.RCF

/-!
# Non-archimedean ordered fields with a residue field: standard parts and Hensel

`LCData R L` packages what the real-closedness proof needs to know about the
Levi-Civita field `L` over a coefficient field `R`:

* an ordered embedding `ι : R → L`;
* rational powers `e q = ε^q`, a homomorphism `(ℚ, +) → (L^×, ·)` with `e q`
  positive and infinitesimal for `q > 0`;
* **leading terms**: every `x ≠ 0` is `ι r · ε^q · (1 + δ)` with `r ≠ 0` and `δ`
  infinitesimal;
* Cauchy completeness.

From these we build the standard part `st : L → R` on finite elements, a ring
map, and prove **Hensel's lemma** (`hensel`): a simple root of the residue
polynomial lifts to a root, by Newton's method. The Newton iterates converge
quadratically: `ι K |P(xₖ)| ≤ ε^{μ 2ᵏ}`.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita

open Lean.Grind Series Series.PS Poly Limits Classical

attribute [local instance] Semiring.natCast Ring.intCast
attribute [local instance high] Semiring.ofNat

universe u v

/-- The structure of a Levi-Civita-like field `L` over a coefficient field `R`. -/
structure LCData (R : Type u) (L : Type v)
    [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
    [Field L] [LE L] [LT L] [Std.IsLinearOrder L] [Std.LawfulOrderLT L] [OrderedRing L] where
  ι : R → L
  ι_add : ∀ a b, ι (a + b) = ι a + ι b
  ι_mul : ∀ a b, ι (a * b) = ι a * ι b
  ι_one : ι 1 = 1
  ι_lt : ∀ {a b}, a < b → ι a < ι b
  /-- `e q = ε^q`. -/
  e : Rat → L
  e_add : ∀ p q, e (p + q) = e p * e q
  e_pos : ∀ q, 0 < e q
  /-- `ε^q` is infinitesimal for `q > 0`. -/
  e_small : ∀ q, 0 < q → ∀ r : R, 0 < r → e q < ι r
  /-- Leading terms. -/
  lead : ∀ x : L, x ≠ 0 → ∃ (r : R) (q : Rat) (δ : L), r ≠ 0 ∧
    (∀ s : R, 0 < s → abs δ < ι s) ∧ x = ι r * e q * (1 + δ)
  complete : ∀ s : Nat → L, Cauchy.IsCauchy s → ∃ x, Tendsto s x

namespace LCData

variable {R : Type u} {L : Type v}
  [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
  [Field L] [LE L] [LT L] [Std.IsLinearOrder L] [Std.LawfulOrderLT L] [OrderedRing L]
  (D : LCData R L)

/-! ## The embedding -/

theorem ι_zero : D.ι 0 = 0 := by
  have := D.ι_add 0 0; rw [show (0 : R) + 0 = 0 by grind] at this; grind

theorem ι_neg (a : R) : D.ι (-a) = -D.ι a := by
  have := D.ι_add a (-a); rw [show a + -a = 0 by grind, D.ι_zero] at this; grind

theorem ι_sub (a b : R) : D.ι (a - b) = D.ι a - D.ι b := by
  rw [show a - b = a + -b by grind, D.ι_add, D.ι_neg]; grind

theorem ι_lt_iff {a b : R} : D.ι a < D.ι b ↔ a < b := by
  constructor
  · intro h; apply Classical.byContradiction; intro h'
    rcases (by grind : b < a ∨ b = a) with h2 | h2
    · have := D.ι_lt h2; grind
    · subst h2; grind
  · exact D.ι_lt

theorem ι_le_iff {a b : R} : D.ι a ≤ D.ι b ↔ a ≤ b := by
  constructor
  · intro h; apply Classical.byContradiction; intro h'
    have := D.ι_lt (show b < a by grind); grind
  · intro h; rcases (by grind : a < b ∨ a = b) with h | h
    · exact Std.le_of_lt (D.ι_lt h)
    · subst h; exact Std.le_refl _

theorem ι_inj {a b : R} (h : D.ι a = D.ι b) : a = b := by
  apply Classical.byContradiction; intro hne
  rcases (by grind : a < b ∨ b < a) with h' | h'
  · have := D.ι_lt h'; grind
  · have := D.ι_lt h'; grind

theorem ι_pos {a : R} (h : 0 < a) : 0 < D.ι a := by have := D.ι_lt h; rwa [D.ι_zero] at this

theorem ι_natCast (k : Nat) : D.ι (k : R) = (k : L) := by
  induction k with
  | zero => rw [Semiring.natCast_zero, Semiring.natCast_zero, D.ι_zero]
  | succ k ih => rw [Semiring.natCast_add, Semiring.natCast_add, D.ι_add, ih, Semiring.natCast_one,
      Semiring.natCast_one, D.ι_one]

theorem ι_two : D.ι (2 : R) = (2 : L) := by
  rw [show (2 : R) = ((2 : Nat) : R) from (Semiring.ofNat_eq_natCast 2), D.ι_natCast,
    ← Semiring.ofNat_eq_natCast]; rfl

theorem ι_inv {a : R} (h : a ≠ 0) : D.ι a⁻¹ = (D.ι a)⁻¹ := by
  have h1 : D.ι a * D.ι a⁻¹ = 1 := by rw [← D.ι_mul, Field.mul_inv_cancel h, D.ι_one]
  have hne : D.ι a ≠ 0 := fun h0 => by rw [h0] at h1; grind
  have := Field.inv_mul_cancel hne
  calc D.ι a⁻¹ = (D.ι a)⁻¹ * (D.ι a * D.ι a⁻¹) := by grind
    _ = (D.ι a)⁻¹ := by rw [h1]; grind

theorem ι_pow (a : R) (k : Nat) : D.ι (a ^ k) = D.ι a ^ k := by
  induction k with
  | zero => rw [Semiring.pow_zero, Semiring.pow_zero, D.ι_one]
  | succ k ih => rw [Semiring.pow_succ, Semiring.pow_succ, D.ι_mul, ih]

theorem ι_S (n : Nat) (f : Nat → R) : D.ι (S n f) = S n (fun i => D.ι (f i)) := by
  induction n with
  | zero => exact D.ι_zero
  | succ n ih => rw [S_succ, S_succ, D.ι_add, ih]

theorem ι_abs (a : R) : D.ι (abs a) = abs (D.ι a) := by
  rcases (by grind : 0 ≤ a ∨ a < 0) with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by have := D.ι_le_iff.mpr h; rwa [D.ι_zero] at this)]
  · rw [abs_of_neg h, abs_of_neg (by have := D.ι_lt h; rwa [D.ι_zero] at this), D.ι_neg]

/-! ## Powers of `ε` -/

theorem e_zero : D.e 0 = 1 := by
  have := D.e_add 0 0; rw [show (0 : Rat) + 0 = 0 by grind] at this
  have hp := D.e_pos 0
  have := Field.mul_inv_cancel (show D.e 0 ≠ 0 by grind)
  calc D.e 0 = D.e 0 * D.e 0 * (D.e 0)⁻¹ := by grind
    _ = 1 := by rw [← this]; grind

theorem e_ne_zero (q : Rat) : D.e q ≠ 0 := by have := D.e_pos q; grind

theorem e_neg (q : Rat) : D.e (-q) = (D.e q)⁻¹ := by
  have h := D.e_add q (-q); rw [show q + -q = 0 by grind, D.e_zero] at h
  exact Field.eq_inv_of_mul_eq_one (by rw [CommSemiring.mul_comm]; exact h.symm)

theorem e_sub (p q : Rat) : D.e (p - q) = D.e p * (D.e q)⁻¹ := by
  rw [show p - q = p + -q by grind, D.e_add, D.e_neg]

theorem e_lt_one {q : Rat} (h : 0 < q) : D.e q < 1 := by
  have := D.e_small q h 1 (by grind); rwa [D.ι_one] at this

theorem e_le_one {q : Rat} (h : 0 ≤ q) : D.e q ≤ 1 := by
  rcases (by grind : q = 0 ∨ 0 < q) with h | h
  · subst h; rw [D.e_zero]; exact Std.le_refl _
  · exact Std.le_of_lt (D.e_lt_one h)

theorem e_anti {p q : Rat} (h : p ≤ q) : D.e q ≤ D.e p := by
  have e1 : D.e q = D.e p * D.e (q - p) := by rw [← D.e_add]; congr 1; grind
  rw [e1]
  have := OrderedRing.mul_le_mul_of_nonneg_left (D.e_le_one (show 0 ≤ q - p by grind))
    (Std.le_of_lt (D.e_pos p))
  grind

theorem e_strict_anti {p q : Rat} (h : p < q) : D.e q < D.e p := by
  have e1 : D.e q = D.e p * D.e (q - p) := by rw [← D.e_add]; congr 1; grind
  rw [e1]
  have := OrderedRing.mul_lt_mul_of_pos_left (D.e_lt_one (show 0 < q - p by grind)) (D.e_pos p)
  grind

theorem e_natMul (q : Rat) (k : Nat) : D.e ((k : Rat) * q) = D.e q ^ k := by
  induction k with
  | zero => rw [Semiring.pow_zero, show ((0 : Nat) : Rat) * q = 0 by simp, D.e_zero]
  | succ k ih =>
    rw [Semiring.pow_succ, ← ih, ← D.e_add]; congr 1
    rw [show ((k + 1 : Nat) : Rat) = (k : Rat) + 1 by simp]; grind

/-! ## Infinitesimal and finite elements -/

/-- `|x| < r` for every positive coefficient `r`. -/
def Inf (x : L) : Prop := ∀ r : R, 0 < r → abs x < D.ι r

/-- `|x| ≤ r` for some coefficient `r`. -/
def Fin (x : L) : Prop := ∃ r : R, abs x ≤ D.ι r

theorem inf_zero : D.Inf 0 := fun r hr => by rw [abs_zero]; exact D.ι_pos hr

theorem inf_neg {x : L} (h : D.Inf x) : D.Inf (-x) := fun r hr => by rw [abs_neg]; exact h r hr

theorem inf_add {x y : L} (hx : D.Inf x) (hy : D.Inf y) : D.Inf (x + y) := fun r hr => by
  have h1 := hx (r / 2) (by grind); have h2 := hy (r / 2) (by grind)
  have := abs_add_le x y
  have : D.ι (r / 2) + D.ι (r / 2) = D.ι r := by rw [← D.ι_add]; congr 1; grind
  grind

theorem inf_sub {x y : L} (hx : D.Inf x) (hy : D.Inf y) : D.Inf (x - y) := by
  rw [show x - y = x + -y by grind]; exact D.inf_add hx (D.inf_neg hy)

theorem fin_of_inf {x : L} (h : D.Inf x) : D.Fin x := ⟨1, Std.le_of_lt (h 1 (by grind))⟩

theorem fin_ι (a : R) : D.Fin (D.ι a) := ⟨abs a, by rw [D.ι_abs]; exact Std.le_refl _⟩

theorem fin_add {x y : L} (hx : D.Fin x) (hy : D.Fin y) : D.Fin (x + y) := by
  obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by rw [D.ι_add]; have := abs_add_le x y; grind⟩

theorem fin_neg {x : L} (h : D.Fin x) : D.Fin (-x) := by
  obtain ⟨a, ha⟩ := h; exact ⟨a, by rw [abs_neg]; exact ha⟩

theorem fin_sub {x y : L} (hx : D.Fin x) (hy : D.Fin y) : D.Fin (x - y) := by
  rw [show x - y = x + -y by grind]; exact D.fin_add hx (D.fin_neg hy)

theorem fin_mul {x y : L} (hx : D.Fin x) (hy : D.Fin y) : D.Fin (x * y) := by
  obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
  refine ⟨a * b, ?_⟩
  rw [abs_mul, D.ι_mul]
  exact mul_le_mul_of_le ha hb (abs_nonneg _) (abs_nonneg _)

theorem inf_mul {x y : L} (hx : D.Inf x) (hy : D.Fin y) : D.Inf (x * y) := fun r hr => by
  obtain ⟨b, hb⟩ := hy
  have hb1 : 0 < abs b + 1 := by have := abs_nonneg b; grind
  have hb' : abs y ≤ D.ι (abs b + 1) := by
    have : D.ι b ≤ D.ι (abs b + 1) := D.ι_le_iff.mpr (by have := le_abs b; grind)
    grind
  have h1 := hx (r * (abs b + 1)⁻¹)
    (OrderedRing.mul_pos hr (Field.IsOrdered.inv_pos_iff.mpr hb1))
  rw [abs_mul]
  have hy0 := abs_nonneg y
  have hx0 := abs_nonneg x
  have : abs x * abs y ≤ abs x * D.ι (abs b + 1) := OrderedRing.mul_le_mul_of_nonneg_left hb' hx0
  have : abs x * D.ι (abs b + 1) < D.ι (r * (abs b + 1)⁻¹) * D.ι (abs b + 1) :=
    OrderedRing.mul_lt_mul_of_pos_right h1 (D.ι_pos hb1)
  rw [← D.ι_mul, Semiring.mul_assoc, Field.inv_mul_cancel (by grind), Semiring.mul_one] at this
  grind

theorem inf_mul' {x y : L} (hx : D.Fin x) (hy : D.Inf y) : D.Inf (x * y) := by
  rw [CommSemiring.mul_comm]; exact D.inf_mul hy hx

theorem inf_ι {a : R} (h : D.Inf (D.ι a)) : a = 0 := by
  apply Classical.byContradiction; intro hne
  have := h (abs a) (abs_pos hne); rw [D.ι_abs] at this; grind

theorem inf_e {q : Rat} (h : 0 < q) : D.Inf (D.e q) := fun r hr => by
  rw [abs_of_nonneg (Std.le_of_lt (D.e_pos q))]; exact D.e_small q h r hr

theorem fin_e {q : Rat} (h : 0 ≤ q) : D.Fin (D.e q) :=
  ⟨1, by rw [abs_of_nonneg (Std.le_of_lt (D.e_pos q)), D.ι_one]; exact D.e_le_one h⟩

theorem fin_natCast (k : Nat) : D.Fin (k : L) := by rw [← D.ι_natCast]; exact D.fin_ι _

theorem fin_S {n : Nat} {f : Nat → L} (h : ∀ i, i < n → D.Fin (f i)) : D.Fin (S n f) := by
  induction n with
  | zero => exact ⟨0, by show abs (0 : L) ≤ _; rw [abs_zero, D.ι_zero]; exact Std.le_refl _⟩
  | succ n ih => rw [S_succ]; exact D.fin_add (ih fun i hi => h i (by omega)) (h n (by omega))

theorem inf_S {n : Nat} {f : Nat → L} (h : ∀ i, i < n → D.Inf (f i)) : D.Inf (S n f) := by
  induction n with
  | zero => exact D.inf_zero
  | succ n ih => rw [S_succ]; exact D.inf_add (ih fun i hi => h i (by omega)) (h n (by omega))

theorem fin_pow {x : L} (h : D.Fin x) (k : Nat) : D.Fin (x ^ k) := by
  induction k with
  | zero => rw [Semiring.pow_zero, ← D.ι_one]; exact D.fin_ι 1
  | succ k ih => rw [Semiring.pow_succ]; exact D.fin_mul ih h

/-- `1 + δ` is not small. -/
theorem one_add_inf_bounds {δ : L} (h : D.Inf δ) : 2⁻¹ ≤ 1 + δ ∧ 1 + δ ≤ 2 := by
  have := h (2⁻¹) (Field.IsOrdered.inv_pos_iff.mpr (by grind))
  rw [abs_lt_iff] at this
  have e : D.ι (2⁻¹ : R) = (2 : L)⁻¹ := by
    rw [D.ι_inv (by grind), show (2 : R) = ((2 : Nat) : R) from (Semiring.ofNat_eq_natCast 2),
      D.ι_natCast, ← Semiring.ofNat_eq_natCast]; rfl
  rw [e] at this
  have : (2 : L)⁻¹ ≤ 1 := by
    have := Field.IsOrdered.inv_pos_iff.mpr (show (0 : L) < 2 by grind)
    have := Field.mul_inv_cancel (show (2 : L) ≠ 0 by grind); grind
  constructor <;> grind

/-- An element with a nonzero leading coefficient is not infinitesimal. -/
theorem not_inf_lead {r : R} {δ : L} (hr : r ≠ 0) (hδ : D.Inf δ) : ¬ D.Inf (D.ι r * (1 + δ)) := by
  intro h
  have hb := D.one_add_inf_bounds hδ
  have h1 := h (abs r * 2⁻¹) (OrderedRing.mul_pos (abs_pos hr) (Field.IsOrdered.inv_pos_iff.mpr (by grind)))
  rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 + δ by grind), D.ι_mul, ← D.ι_abs] at h1
  have e : D.ι (2⁻¹ : R) = (2 : L)⁻¹ := by
    rw [D.ι_inv (by grind), show (2 : R) = ((2 : Nat) : R) from (Semiring.ofNat_eq_natCast 2),
      D.ι_natCast, ← Semiring.ofNat_eq_natCast]; rfl
  rw [e] at h1
  have hra := D.ι_pos (abs_pos hr)
  have := OrderedRing.mul_le_mul_of_nonneg_left hb.1 (Std.le_of_lt hra)
  grind

/-- `ε^q` is not finite for `q < 0`. -/
theorem not_fin_e {q : Rat} (h : q < 0) : ¬ D.Fin (D.e q) := by
  rintro ⟨r, hr⟩
  rw [abs_of_nonneg (Std.le_of_lt (D.e_pos q))] at hr
  -- `1 = ε^q ε^{-q} ≤ r ε^{-q}`, but `r ε^{-q}` is infinitesimal
  have hinf := D.inf_mul' (D.fin_ι r) (D.inf_e (show 0 < -q by grind))
  have := hinf 1 (by grind)
  rw [D.ι_one, abs_of_nonneg (OrderedRing.mul_nonneg ?_ (Std.le_of_lt (D.e_pos _)))] at this
  · have h2 := OrderedRing.mul_le_mul_of_nonneg_right hr (Std.le_of_lt (D.e_pos (-q)))
    rw [← D.e_add, show q + -q = 0 by grind, D.e_zero] at h2
    grind
  · have := D.e_pos q; grind

/-! ## Leading terms -/

theorem lead' (x : L) (hx : x ≠ 0) : ∃ (r : R) (q : Rat) (δ : L), r ≠ 0 ∧ D.Inf δ ∧
    x = D.ι r * D.e q * (1 + δ) := D.lead x hx

/-- A nonzero infinitesimal is bounded by a positive power of `ε`. -/
theorem inf_le_e {x : L} (h : D.Inf x) : ∃ μ : Rat, 0 < μ ∧ abs x ≤ D.e μ := by
  by_cases hx : x = 0
  · exact ⟨1, by grind, by rw [hx, abs_zero]; exact Std.le_of_lt (D.e_pos 1)⟩
  obtain ⟨r, q, δ, hr, hδ, hxe⟩ := D.lead' x hx
  have hb := D.one_add_inf_bounds hδ
  -- `q > 0`, else `x` is not infinitesimal
  have hq : 0 < q := by
    apply Classical.byContradiction; intro hq
    apply D.not_inf_lead hr hδ
    have : D.ι r * (1 + δ) = x * D.e (-q) := by
      rw [hxe, D.e_neg]
      have := Field.mul_inv_cancel (D.e_ne_zero q); grind
    rw [this]; exact D.inf_mul h (D.fin_e (by grind))
  refine ⟨q / 2, by grind, ?_⟩
  -- `|x| ≤ 2|r| ε^q = (2|r| ε^{q/2}) ε^{q/2} ≤ ε^{q/2}`
  have hsplit : D.e q = D.e (q / 2) * D.e (q / 2) := by rw [← D.e_add]; congr 1; grind
  have hsmall := D.e_small (q / 2) (by grind) ((abs r * 2)⁻¹)
    (Field.IsOrdered.inv_pos_iff.mpr (OrderedRing.mul_pos (abs_pos hr) (by grind)))
  rw [D.ι_inv (by have := abs_pos hr; grind), D.ι_mul, D.ι_abs, D.ι_two] at hsmall
  have hpos : 0 < abs (D.ι r) * 2 := by
    have := abs_pos (show D.ι r ≠ 0 by
      intro h0; apply hr; apply D.ι_inj; rw [h0, D.ι_zero]); grind
  rw [hxe, abs_mul, abs_mul, abs_of_nonneg (Std.le_of_lt (D.e_pos q)),
    abs_of_nonneg (show 0 ≤ 1 + δ by grind)]
  have h1 : abs (D.ι r) * D.e q * (1 + δ) ≤ abs (D.ι r) * D.e q * 2 :=
    OrderedRing.mul_le_mul_of_nonneg_left hb.2
      (OrderedRing.mul_nonneg (abs_nonneg _) (Std.le_of_lt (D.e_pos q)))
  have h2 : (abs (D.ι r) * 2) * D.e (q / 2) < (abs (D.ι r) * 2) * (abs (D.ι r) * 2)⁻¹ :=
    OrderedRing.mul_lt_mul_of_pos_left hsmall hpos
  rw [Field.mul_inv_cancel (by grind)] at h2
  have h3 := OrderedRing.mul_lt_mul_of_pos_right h2 (D.e_pos (q / 2))
  rw [hsplit] at h1 ⊢
  have e1 : abs (D.ι r) * (D.e (q / 2) * D.e (q / 2)) * 2 =
      abs (D.ι r) * 2 * D.e (q / 2) * D.e (q / 2) := by grind
  rw [Semiring.one_mul] at h3
  exact Std.le_trans h1 (by rw [e1]; exact Std.le_of_lt h3)

/-- Positive powers of `ε` are coinitial among positive elements. -/
theorem exists_e_lt {d : L} (hd : 0 < d) : ∃ μ : Rat, D.e μ < d := by
  obtain ⟨r, q, δ, hr, hδ, hde⟩ := D.lead' d (by grind)
  have hb := D.one_add_inf_bounds hδ
  have hr0 : 0 < r := by
    apply Classical.byContradiction; intro h
    have : D.ι r ≤ 0 := by have := D.ι_le_iff.mpr (show r ≤ 0 by grind); rwa [D.ι_zero] at this
    have := OrderedRing.mul_nonneg (Std.le_of_lt (D.e_pos q)) (show 0 ≤ 1 + δ by grind)
    have : D.ι r * D.e q * (1 + δ) ≤ 0 := by
      rw [Semiring.mul_assoc]; exact OrderedRing.mul_nonpos_of_nonpos_of_nonneg (by grind) this
    grind
  refine ⟨q + 1, ?_⟩
  rw [D.e_add]
  have h1 := D.e_small 1 (by grind) (r * 2⁻¹) (OrderedRing.mul_pos hr0 (Field.IsOrdered.inv_pos_iff.mpr (by grind)))
  have h2 := OrderedRing.mul_lt_mul_of_pos_left h1 (D.e_pos q)
  -- `ι (r/2) ≤ ι r (1 + δ)`
  have e : D.ι (2⁻¹ : R) = (2 : L)⁻¹ := by
    rw [D.ι_inv (by grind), show (2 : R) = ((2 : Nat) : R) from (Semiring.ofNat_eq_natCast 2),
      D.ι_natCast, ← Semiring.ofNat_eq_natCast]; rfl
  rw [D.ι_mul, e] at h2
  have h3 : D.ι r * (2 : L)⁻¹ ≤ D.ι r * (1 + δ) :=
    OrderedRing.mul_le_mul_of_nonneg_left hb.1 (Std.le_of_lt (D.ι_pos hr0))
  have h4 := OrderedRing.mul_le_mul_of_nonneg_left h3 (Std.le_of_lt (D.e_pos q))
  grind

/-! ## Standard parts -/

theorem exists_st {x : L} (h : D.Fin x) : ∃ s : R, D.Inf (x - D.ι s) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, D.ι_zero, show (0 : L) - 0 = 0 by grind]; exact D.inf_zero⟩
  obtain ⟨r, q, δ, hr, hδ, hxe⟩ := D.lead' x hx
  rcases (by grind : q < 0 ∨ q = 0 ∨ 0 < q) with hq | hq | hq
  · -- infinite: impossible
    exfalso; apply D.not_fin_e hq
    have hb := D.one_add_inf_bounds hδ
    have hu : D.Fin (1 + δ)⁻¹ := ⟨2, by
      have hpos : 0 < 1 + δ := by grind
      rw [abs_of_nonneg (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.mpr hpos)),
        show (2 : R) = ((2 : Nat) : R) from (Semiring.ofNat_eq_natCast 2), D.ι_natCast,
        ← Semiring.ofNat_eq_natCast]
      have := Field.mul_inv_cancel (show 1 + δ ≠ 0 by grind)
      have := OrderedRing.mul_le_mul_of_nonneg_left hb.1
        (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.mpr hpos))
      grind⟩
    have : D.e q = x * (1 + δ)⁻¹ * D.ι r⁻¹ := by
      rw [hxe, D.ι_inv hr]
      have := Field.mul_inv_cancel (show 1 + δ ≠ 0 by have := D.one_add_inf_bounds hδ; grind)
      have := Field.mul_inv_cancel (show D.ι r ≠ 0 by
        intro h0; apply hr; apply D.ι_inj; rw [h0, D.ι_zero])
      grind
    rw [this]; exact D.fin_mul (D.fin_mul h hu) (D.fin_ι _)
  · subst hq
    refine ⟨r, ?_⟩
    rw [hxe, D.e_zero, show D.ι r * 1 * (1 + δ) - D.ι r = D.ι r * δ by grind]
    exact D.inf_mul' (D.fin_ι r) hδ
  · refine ⟨0, ?_⟩
    rw [D.ι_zero, show x - 0 = x by grind, hxe, Semiring.mul_assoc]
    have hb := D.one_add_inf_bounds hδ
    exact D.inf_mul' (D.fin_ι r) (D.inf_mul (D.inf_e hq) ⟨2, by
      rw [abs_of_nonneg (show 0 ≤ 1 + δ by grind),
        show (2 : R) = ((2 : Nat) : R) from (Semiring.ofNat_eq_natCast 2), D.ι_natCast,
        ← Semiring.ofNat_eq_natCast]; exact hb.2⟩)

/-- The standard part of a finite element (junk `0` otherwise). -/
noncomputable def st (x : L) : R := if h : D.Fin x then Classical.choose (D.exists_st h) else 0

theorem st_spec {x : L} (h : D.Fin x) : D.Inf (x - D.ι (D.st x)) := by
  unfold st; simp only [h, ↓reduceDIte]; exact Classical.choose_spec (D.exists_st h)

theorem fin_of_inf_sub {x : L} {s : R} (h : D.Inf (x - D.ι s)) : D.Fin x := by
  have := D.fin_add (D.fin_of_inf h) (D.fin_ι s); rwa [show x - D.ι s + D.ι s = x by grind] at this

theorem st_eq {x : L} {s : R} (h : D.Inf (x - D.ι s)) : D.st x = s := by
  have h2 := D.st_spec (D.fin_of_inf_sub h)
  have := D.inf_ι (a := D.st x - s) (by
    rw [D.ι_sub, show D.ι (D.st x) - D.ι s = (x - D.ι s) - (x - D.ι (D.st x)) by grind]
    exact D.inf_sub h h2)
  grind

theorem st_eq_aux {x : L} {s : R} (h : D.Inf (x - D.ι s)) : D.st x - s = 0 := by
  have h2 := D.st_spec (D.fin_of_inf_sub h)
  apply D.inf_ι (a := D.st x - s)
  rw [D.ι_sub, show D.ι (D.st x) - D.ι s = (x - D.ι s) - (x - D.ι (D.st x)) by grind]
  exact D.inf_sub h h2

theorem st_ι (a : R) : D.st (D.ι a) = a :=
  D.st_eq (by rw [show D.ι a - D.ι a = 0 by grind]; exact D.inf_zero)

theorem st_add {x y : L} (hx : D.Fin x) (hy : D.Fin y) : D.st (x + y) = D.st x + D.st y :=
  D.st_eq (by
    rw [D.ι_add, show x + y - (D.ι (D.st x) + D.ι (D.st y)) =
      (x - D.ι (D.st x)) + (y - D.ι (D.st y)) by grind]
    exact D.inf_add (D.st_spec hx) (D.st_spec hy))

theorem st_neg {x : L} (hx : D.Fin x) : D.st (-x) = -D.st x :=
  D.st_eq (by
    rw [D.ι_neg, show -x - -D.ι (D.st x) = -(x - D.ι (D.st x)) by grind]
    exact D.inf_neg (D.st_spec hx))

theorem st_sub {x y : L} (hx : D.Fin x) (hy : D.Fin y) : D.st (x - y) = D.st x - D.st y := by
  rw [show x - y = x + -y by grind, D.st_add hx (D.fin_neg hy), D.st_neg hy]; grind

theorem st_mul {x y : L} (hx : D.Fin x) (hy : D.Fin y) : D.st (x * y) = D.st x * D.st y :=
  D.st_eq (by
    rw [D.ι_mul]
    have e : x * y - D.ι (D.st x) * D.ι (D.st y) =
        (x - D.ι (D.st x)) * y + D.ι (D.st x) * (y - D.ι (D.st y)) := by grind
    rw [e]
    exact D.inf_add (D.inf_mul (D.st_spec hx) hy) (D.inf_mul' (D.fin_ι _) (D.st_spec hy)))

theorem st_pow {x : L} (hx : D.Fin x) (k : Nat) : D.st (x ^ k) = D.st x ^ k := by
  induction k with
  | zero => rw [Semiring.pow_zero, Semiring.pow_zero, ← D.ι_one, D.st_ι]
  | succ k ih => rw [Semiring.pow_succ, Semiring.pow_succ, D.st_mul (D.fin_pow hx k) hx, ih]

theorem st_S {n : Nat} {f : Nat → L} (h : ∀ i, i < n → D.Fin (f i)) :
    D.st (S n f) = S n (fun i => D.st (f i)) := by
  induction n with
  | zero => show D.st 0 = 0; rw [← D.ι_zero, D.st_ι]
  | succ n ih =>
    rw [S_succ, S_succ, D.st_add (D.fin_S fun i hi => h i (by omega)) (h n (by omega)),
      ih fun i hi => h i (by omega)]

theorem st_natCast (k : Nat) : D.st (k : L) = (k : R) := by rw [← D.ι_natCast, D.st_ι]

theorem inf_iff_st {x : L} (hx : D.Fin x) : D.Inf x ↔ D.st x = 0 := by
  constructor
  · intro h; exact D.st_eq (by rw [D.ι_zero, show x - 0 = x by grind]; exact h)
  · intro h; have := D.st_spec hx; rwa [h, D.ι_zero, show x - 0 = x by grind] at this

theorem st_e {q : Rat} (hq : 0 < q) : D.st (D.e q) = 0 :=
  (D.inf_iff_st (D.fin_of_inf (D.inf_e hq))).mp (D.inf_e hq)

/-- A finite element is bounded by `|st x| + 1`. -/
theorem abs_le_st {x : L} (hx : D.Fin x) : abs x ≤ D.ι (abs (D.st x) + 1) := by
  have h := D.st_spec hx 1 (by grind)
  rw [D.ι_add, D.ι_one, D.ι_abs]
  have := abs_add_le (x - D.ι (D.st x)) (D.ι (D.st x))
  rw [show x - D.ι (D.st x) + D.ι (D.st x) = x by grind] at this
  rw [D.ι_one] at h
  grind

/-- Units: an element with nonzero standard part has a finite inverse. -/
theorem st_inv {x : L} (hx : D.Fin x) (h : D.st x ≠ 0) :
    x ≠ 0 ∧ D.Fin x⁻¹ ∧ D.st x⁻¹ = (D.st x)⁻¹ := by
  have hspec := D.st_spec hx
  have hx0 : x ≠ 0 := fun h0 => by
    rw [h0, ← D.ι_zero, D.st_ι] at h; exact h rfl
  -- `|x| ≥ |st x| / 2`
  have hsa := abs_pos h
  have h1 := hspec (abs (D.st x) * 2⁻¹)
    (OrderedRing.mul_pos hsa (Field.IsOrdered.inv_pos_iff.mpr (by grind)))
  have hlow : D.ι (abs (D.st x) * 2⁻¹) ≤ abs x := by
    have := abs_add_le (D.ι (D.st x) - x) x
    rw [show D.ι (D.st x) - x + x = D.ι (D.st x) by grind, ← D.ι_abs, abs_sub_comm] at this
    have e : D.ι (abs (D.st x)) = D.ι (abs (D.st x) * 2⁻¹) + D.ι (abs (D.st x) * 2⁻¹) := by
      rw [← D.ι_add]; congr 1; have := Field.mul_inv_cancel (show (2 : R) ≠ 0 by grind); grind
    grind
  have hpos : 0 < D.ι (abs (D.st x) * 2⁻¹) :=
    D.ι_pos (OrderedRing.mul_pos hsa (Field.IsOrdered.inv_pos_iff.mpr (by grind)))
  have hfin : D.Fin x⁻¹ := by
    refine ⟨(abs (D.st x) * 2⁻¹)⁻¹, ?_⟩
    rw [D.ι_inv (by grind)]
    have hax := abs_pos hx0
    -- `|x⁻¹| = |x|⁻¹ ≤ (|st x|/2)⁻¹`
    have e : abs x⁻¹ = (abs x)⁻¹ := by
      have := Field.mul_inv_cancel hx0
      have h2 : abs x * abs x⁻¹ = 1 := by
        rw [← abs_mul, this, abs_of_nonneg (by grind)]
      exact Field.eq_inv_of_mul_eq_one (by rw [CommSemiring.mul_comm]; exact h2)
    rw [e]
    have i1 := Field.IsOrdered.inv_pos_iff.mpr hax
    have i2 := Field.IsOrdered.inv_pos_iff.mpr hpos
    have := OrderedRing.mul_le_mul_of_nonneg_left hlow (Std.le_of_lt (OrderedRing.mul_pos i1 i2))
    rw [Semiring.mul_assoc, Field.inv_mul_cancel (by grind), Semiring.mul_one,
      CommSemiring.mul_comm (abs x)⁻¹, Semiring.mul_assoc, Field.inv_mul_cancel (by grind),
      Semiring.mul_one] at this
    exact this
  refine ⟨hx0, hfin, ?_⟩
  have := D.st_mul hx hfin
  rw [Field.mul_inv_cancel hx0, ← D.ι_one, D.st_ι] at this
  exact Field.eq_inv_of_mul_eq_one (by rw [CommSemiring.mul_comm]; exact this.symm)

end LCData

end LeviCivita
