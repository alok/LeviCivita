import LeviCivita.Completion
import LeviCivita.Poly

/-!
# Limits of sequences in an ordered field

`Tendsto x c`: for every `d > 0`, eventually `|xₙ − c| < d`. The usual rules:
limits are unique, respect `≤`, and commute with sums, products, powers and
polynomial evaluation. Generic over a `Lean.Grind` ordered field, no `sorry`.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita.Limits

open Lean.Grind Series Series.PS Poly Classical

attribute [local instance] Semiring.natCast Ring.intCast
attribute [local instance high] Semiring.ofNat

variable {F : Type u} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F]
  [OrderedRing F]

/-- `xₙ → c`. -/
def Tendsto (x : Nat → F) (c : F) : Prop := ∀ d, 0 < d → ∃ N, ∀ n, N ≤ n → abs (x n - c) < d

theorem near_iff {a b d : F} : Cauchy.Near a b d ↔ abs (a - b) < d := by
  rw [abs_lt_iff]; unfold Cauchy.Near; constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> grind

theorem tendsto_of_near {x : Nat → F} {c : F}
    (h : ∀ D, 0 < D → ∃ N, ∀ n, N ≤ n → Cauchy.Near (x n) c D) : Tendsto x c :=
  fun d hd => let ⟨N, hN⟩ := h d hd; ⟨N, fun n hn => near_iff.mp (hN n hn)⟩

theorem half_pos {d : F} (h : 0 < d) : 0 < d / 2 := by grind

theorem abs_sub_lt_of {a b c : F} {d e : F} (h1 : abs (a - b) < d) (h2 : abs (b - c) < e) :
    abs (a - c) < d + e := by
  have := abs_add_le (a - b) (b - c)
  have : a - b + (b - c) = a - c := by grind
  grind

theorem tendsto_const (c : F) : Tendsto (fun _ => c) c := fun d hd =>
  ⟨0, fun n _ => by rw [show c - c = 0 by grind, abs_zero]; exact hd⟩

theorem tendsto_unique {x : Nat → F} {a b : F} (ha : Tendsto x a) (hb : Tendsto x b) : a = b := by
  apply Classical.byContradiction; intro hne
  have hd := abs_pos (show a - b ≠ 0 by grind)
  obtain ⟨N, hN⟩ := ha _ (half_pos hd)
  obtain ⟨M, hM⟩ := hb _ (half_pos hd)
  have h1 := hN (max N M) (by omega)
  have h2 := hM (max N M) (by omega)
  rw [abs_sub_comm] at h1
  have := abs_sub_lt_of h1 h2
  grind

theorem tendsto_add {x y : Nat → F} {a b : F} (hx : Tendsto x a) (hy : Tendsto y b) :
    Tendsto (fun n => x n + y n) (a + b) := fun d hd => by
  obtain ⟨N, hN⟩ := hx _ (half_pos hd)
  obtain ⟨M, hM⟩ := hy _ (half_pos hd)
  refine ⟨max N M, fun n hn => ?_⟩
  have h1 := hN n (by omega); have h2 := hM n (by omega)
  have := abs_add_le (x n - a) (y n - b)
  rw [show x n + y n - (a + b) = x n - a + (y n - b) by grind]; grind

theorem tendsto_neg {x : Nat → F} {a : F} (hx : Tendsto x a) : Tendsto (fun n => -x n) (-a) :=
  fun d hd => let ⟨N, hN⟩ := hx d hd
  ⟨N, fun n hn => by rw [show -x n - -a = -(x n - a) by grind, abs_neg]; exact hN n hn⟩

theorem tendsto_mul {x y : Nat → F} {a b : F} (hx : Tendsto x a) (hy : Tendsto y b) :
    Tendsto (fun n => x n * y n) (a * b) := fun d hd => by
  have hA : 0 < abs a + 1 + (abs b + 1) := by have := abs_nonneg a; have := abs_nonneg b; grind
  obtain ⟨h, hh, hlt⟩ := Cauchy.exists_mul_lt hd hA
  let e := if h ≤ 1 then h else 1
  have he : 0 < e := by show 0 < (if h ≤ 1 then h else 1); split <;> grind
  have he1 : e ≤ 1 := by show (if h ≤ 1 then h else 1) ≤ 1; split <;> grind
  have heh : e ≤ h := by show (if h ≤ 1 then h else 1) ≤ h; split <;> grind
  obtain ⟨N, hN⟩ := hx e he
  obtain ⟨M, hM⟩ := hy e he
  refine ⟨max N M, fun n hn => ?_⟩
  have h1 := hN n (by omega); have h2 := hM n (by omega)
  have hxa : abs (x n) ≤ abs a + 1 := by
    have := abs_add_le (x n - a) a; rw [show x n - a + a = x n by grind] at this; grind
  rw [show x n * y n - a * b = x n * (y n - b) + b * (x n - a) by grind]
  have := abs_add_le (x n * (y n - b)) (b * (x n - a))
  rw [abs_mul, abs_mul] at this
  have t1 : abs (x n) * abs (y n - b) ≤ (abs a + 1) * e :=
    mul_le_mul_of_le hxa (Std.le_of_lt h2) (abs_nonneg _) (abs_nonneg _)
  have t2 : abs b * abs (x n - a) ≤ (abs b + 1) * e :=
    mul_le_mul_of_le (by grind) (Std.le_of_lt h1) (abs_nonneg _) (abs_nonneg _)
  have t3 : (abs a + 1 + (abs b + 1)) * e ≤ (abs a + 1 + (abs b + 1)) * h :=
    OrderedRing.mul_le_mul_of_nonneg_left heh (Std.le_of_lt hA)
  grind

theorem tendsto_pow {x : Nat → F} {a : F} (hx : Tendsto x a) (k : Nat) :
    Tendsto (fun n => x n ^ k) (a ^ k) := by
  induction k with
  | zero => simp only [Semiring.pow_zero]; exact tendsto_const 1
  | succ k ih => simp only [Semiring.pow_succ]; exact tendsto_mul ih hx

theorem tendsto_S {m : Nat} {f : Nat → Nat → F} {g : Nat → F}
    (h : ∀ i, i < m → Tendsto (fun n => f n i) (g i)) :
    Tendsto (fun n => S m (f n)) (S m g) := by
  induction m with
  | zero => exact tendsto_const 0
  | succ m ih =>
    simp only [S_succ]
    exact tendsto_add (ih fun i hi => h i (by omega)) (h m (by omega))

/-- Polynomials are continuous. -/
theorem tendsto_eval (k : Nat) (p : PS F) {x : Nat → F} {a : F} (hx : Tendsto x a) :
    Tendsto (fun n => eval k p (x n)) (eval k p a) := by
  unfold eval
  exact tendsto_S fun i _ => tendsto_mul (tendsto_const _) (tendsto_pow hx i)

/-- Weak inequalities pass to the limit. -/
theorem le_of_tendsto {x : Nat → F} {a b : F} (hx : Tendsto x a) (h : ∀ n, x n ≤ b) : a ≤ b := by
  apply Classical.byContradiction; intro hlt
  obtain ⟨N, hN⟩ := hx (a - b) (by grind)
  have := hN N (Nat.le_refl _); have := h N
  rw [abs_lt_iff] at *; grind

theorem ge_of_tendsto {x : Nat → F} {a b : F} (hx : Tendsto x a) (h : ∀ n, b ≤ x n) : b ≤ a := by
  have := le_of_tendsto (tendsto_neg hx) (b := -b) (fun n => by have := h n; grind)
  grind

/-- Bounds that hold from some index on pass to the limit. -/
theorem le_of_tendsto' {x : Nat → F} {a b : F} (hx : Tendsto x a) {N : Nat}
    (h : ∀ n, N ≤ n → x n ≤ b) : a ≤ b := by
  apply le_of_tendsto (x := fun n => x (n + N)) (fun d hd => by
    obtain ⟨M, hM⟩ := hx d hd
    exact ⟨M, fun n hn => hM (n + N) (by omega)⟩)
  intro n; exact h (n + N) (by omega)

theorem ge_of_tendsto' {x : Nat → F} {a b : F} (hx : Tendsto x a) {N : Nat}
    (h : ∀ n, N ≤ n → b ≤ x n) : b ≤ a := by
  apply ge_of_tendsto (x := fun n => x (n + N)) (fun d hd => by
    obtain ⟨M, hM⟩ := hx d hd
    exact ⟨M, fun n hn => hM (n + N) (by omega)⟩)
  intro n; exact h (n + N) (by omega)

theorem inv_pow (x : F) (k : Nat) : (x⁻¹) ^ k = (x ^ k)⁻¹ := by
  induction k with
  | zero => rw [Semiring.pow_zero, Semiring.pow_zero, Field.inv_one]
  | succ k ih => rw [Semiring.pow_succ, Semiring.pow_succ, ih, Field.inv_mul]

theorem pow_pos {x : F} (h : 0 < x) (k : Nat) : 0 < x ^ k := by
  induction k with
  | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
  | succ k ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih h

/-- `a⁻¹ < b` gives `b⁻¹ < a` for positive `a, b`. -/
theorem inv_lt_of_inv_lt {a b : F} (ha : 0 < a) (hb : 0 < b) (h : a⁻¹ < b) : b⁻¹ < a := by
  have hb' := Field.IsOrdered.inv_pos_iff.mpr hb
  have := OrderedRing.mul_lt_mul_of_pos_right h (OrderedRing.mul_pos ha hb')
  have e1 : a⁻¹ * (a * b⁻¹) = b⁻¹ := by
    rw [← Semiring.mul_assoc, Field.inv_mul_cancel (by grind), Semiring.one_mul]
  have e2 : b * (a * b⁻¹) = a := by
    rw [CommSemiring.mul_comm a, ← Semiring.mul_assoc, Field.mul_inv_cancel (by grind), Semiring.one_mul]
  rw [e1, e2] at this; exact this

/-- A Cauchy sequence in the sense of `Cauchy.IsCauchy`, phrased with `abs`. -/
theorem isCauchy_of {x : Nat → F}
    (h : ∀ d, 0 < d → ∃ N, ∀ m n, N ≤ m → N ≤ n → abs (x m - x n) < d) : Cauchy.IsCauchy x :=
  fun d hd => let ⟨N, hN⟩ := h d hd; ⟨N, fun m n hm hn => near_iff.mpr (hN m n hm hn)⟩

end LeviCivita.Limits
