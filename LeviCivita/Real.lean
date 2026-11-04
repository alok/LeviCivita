import LeviCivita.Limits

/-!
# The real numbers, and the intermediate value theorem for polynomials

`Real := Completion ℚ`, the Cauchy completion of the rationals. It is a
Cauchy-complete Archimedean ordered field, and polynomials over it have the
intermediate value property (`Real.ivt`), proved by bisection.

`IVT F` is the intermediate value property for polynomials over an ordered field
`F`. It is one of the standard equivalent definitions of a real closed field.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita

open Lean.Grind Series Series.PS Poly Limits Classical

attribute [local instance] Semiring.natCast Ring.intCast
attribute [local instance high] Semiring.ofNat

/-- **Real closed, IVT form**: every polynomial that changes sign on `[a, b]` has a
root there. -/
def IVT (F : Type u) [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F]
    [OrderedRing F] : Prop :=
  ∀ (n : Nat) (p : PS F) (a b : F), a ≤ b → eval n p a ≤ 0 → 0 ≤ eval n p b →
    ∃ c, a ≤ c ∧ c ≤ b ∧ eval n p c = 0

/-- The real numbers: the Cauchy completion of `ℚ`. -/
abbrev Real := Completion Rat

namespace Real

open Completion

theorem rat_archimedean (q : Rat) : ∃ n : Nat, q < (n : Rat) := by
  refine ⟨(q.floor + 1).toNat, ?_⟩
  have h1 := Rat.lt_floor_add_one q
  have h2 : (q.floor + 1) ≤ ((q.floor + 1).toNat : Int) := Int.self_le_toNat _
  have h3 : ((q.floor + 1 : Int) : Rat) ≤ (((q.floor + 1).toNat : Int) : Rat) :=
    Rat.intCast_le_intCast.mpr h2
  rw [Rat.intCast_natCast] at h3
  grind

/-- `1/(k+1) → 0` in `ℚ`. -/
theorem rat_hasNullSeq : HasNullSeq Rat := by
  have hpos : ∀ k : Nat, (0 : Rat) < k + 1 := fun k => by
    have : (0 : Rat) ≤ k := Rat.natCast_nonneg; grind
  refine ⟨fun k => ((k : Rat) + 1)⁻¹, fun k => Field.IsOrdered.inv_pos_iff.mpr (hpos k),
    fun d hd => ?_⟩
  obtain ⟨K, hK⟩ := rat_archimedean d⁻¹
  refine ⟨K, fun k hk => inv_lt_of_inv_lt hd (hpos k) ?_⟩
  have : (K : Rat) ≤ k := Rat.natCast_le_natCast.mpr hk
  grind

/-- **ℝ is Cauchy-complete.** -/
theorem complete (x : Nat → Real) (hx : Cauchy.IsCauchy x) : ∃ L, Tendsto x L := by
  obtain ⟨L, hL⟩ := Completion.complete rat_hasNullSeq x hx
  exact ⟨L, tendsto_of_near hL⟩

theorem natCast_eq (n : Nat) : (n : Real) = const (n : Rat) := rfl

/-- **ℝ is Archimedean.** -/
theorem archimedean (x : Real) : ∃ n : Nat, x < (n : Real) := by
  obtain ⟨c, hc⟩ := dense x (δ := (1 : Rat)) (by decide)
  obtain ⟨n, hn⟩ := rat_archimedean (c + 1)
  refine ⟨n, ?_⟩
  have h1 : x < const c + const 1 := by have := hc.1; grind
  rw [← const_add] at h1
  exact lt_trans h1 (const_lt.mpr hn)

theorem natCast_nonneg (n : Nat) : (0 : Real) ≤ (n : Real) := by
  rw [natCast_eq]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact Std.le_refl _
  · exact Std.le_of_lt (const_lt.mpr (by
      have : (1 : Rat) ≤ n := by
        have := Rat.natCast_le_natCast.mpr (show 1 ≤ n by omega); simpa using this
      grind))

/-- `k + 1 ≤ 2ᵏ`. -/
theorem succ_le_two_pow (k : Nat) : ((k + 1 : Nat) : Real) ≤ (2 : Real) ^ k := by
  induction k with
  | zero => rw [Semiring.pow_zero]; show const ((0 + 1 : Nat) : Rat) ≤ 1; exact Or.inl rfl
  | succ k ih =>
    rw [Semiring.pow_succ, Semiring.natCast_add]
    have : (1 : Real) ≤ 2 ^ k := by
      have := natCast_nonneg k; rw [Semiring.natCast_add] at ih; grind
    rw [Semiring.natCast_add] at ih
    have := natCast_nonneg k
    grind

theorem natCast_le {m n : Nat} (h : m ≤ n) : (m : Real) ≤ (n : Real) := by
  rw [natCast_eq, natCast_eq]
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact Std.le_of_lt (const_lt.mpr (Rat.natCast_lt_natCast.mpr h))
  · rw [h]; exact Std.le_refl _

/-- `w · 2⁻ᵏ → 0`. -/
theorem tendsto_halving (w : Real) : Tendsto (fun k => w * ((2 : Real)⁻¹) ^ k) 0 := by
  intro d hd
  obtain ⟨N, hN⟩ := archimedean (abs w * d⁻¹)
  refine ⟨N, fun k hk => ?_⟩
  have hpow : 0 < (2 : Real) ^ k := pow_pos (by grind) k
  rw [show w * (2 : Real)⁻¹ ^ k - 0 = w * (2 : Real)⁻¹ ^ k by grind, abs_mul, inv_pow,
    abs_of_nonneg (Std.le_of_lt (Field.IsOrdered.inv_pos_iff.mpr hpow))]
  -- |w| < N d ≤ (k + 1) d ≤ 2ᵏ d
  have hk1 := succ_le_two_pow k
  rw [Semiring.natCast_add] at hk1
  have hNk := natCast_le hk
  have hdinv : d⁻¹ * d = 1 := Field.inv_mul_cancel (by grind)
  have h3 : abs w < (N : Real) * d := by
    have := OrderedRing.mul_lt_mul_of_pos_right hN hd
    rw [Semiring.mul_assoc, hdinv, Semiring.mul_one] at this; exact this
  have h4 : (N : Real) * d ≤ (2 : Real) ^ k * d :=
    OrderedRing.mul_le_mul_of_nonneg_right (by grind) (Std.le_of_lt hd)
  have := OrderedRing.mul_lt_mul_of_pos_left (show abs w < (2 : Real) ^ k * d by grind)
    (Field.IsOrdered.inv_pos_iff.mpr hpow)
  rw [← Semiring.mul_assoc, Field.inv_mul_cancel (show (2 : Real) ^ k ≠ 0 by grind),
    Semiring.one_mul] at this
  grind

/-! ## Bisection -/

/-- The bisection intervals for a sign change of `p` on `[a, b]`. -/
noncomputable def bisect (n : Nat) (p : PS Real) (a b : Real) : Nat → Real × Real
  | 0 => (a, b)
  | k + 1 =>
    let lo := (bisect n p a b k).1
    let hi := (bisect n p a b k).2
    if eval n p ((lo + hi) / 2) ≤ 0 then ((lo + hi) / 2, hi) else (lo, (lo + hi) / 2)

theorem bisect_spec (n : Nat) (p : PS Real) {a b : Real} (hab : a ≤ b) (ha : eval n p a ≤ 0)
    (hb : 0 ≤ eval n p b) (k : Nat) :
    let lo := (bisect n p a b k).1
    let hi := (bisect n p a b k).2
    a ≤ lo ∧ lo ≤ hi ∧ hi ≤ b ∧ hi - lo = (b - a) * ((2 : Real)⁻¹) ^ k ∧
      eval n p lo ≤ 0 ∧ 0 ≤ eval n p hi ∧
      lo ≤ (bisect n p a b (k + 1)).1 ∧ (bisect n p a b (k + 1)).2 ≤ hi := by
  induction k with
  | zero =>
    simp only [bisect]
    refine ⟨Std.le_refl _, hab, Std.le_refl _, by rw [Semiring.pow_zero]; grind, ha, hb, ?_, ?_⟩ <;>
    by_cases hm : eval n p ((a + b) / 2) ≤ 0 <;> simp [hm] <;> grind
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, _, _⟩ := ih
    have hstep : (bisect n p a b (k + 1)) = (if eval n p (((bisect n p a b k).1 +
        (bisect n p a b k).2) / 2) ≤ 0 then (((bisect n p a b k).1 + (bisect n p a b k).2) / 2,
        (bisect n p a b k).2) else ((bisect n p a b k).1,
        ((bisect n p a b k).1 + (bisect n p a b k).2) / 2)) := rfl
    have hstep2 : (bisect n p a b (k + 1 + 1)) = (if eval n p (((bisect n p a b (k + 1)).1 +
        (bisect n p a b (k + 1)).2) / 2) ≤ 0 then (((bisect n p a b (k + 1)).1 +
        (bisect n p a b (k + 1)).2) / 2, (bisect n p a b (k + 1)).2)
        else ((bisect n p a b (k + 1)).1,
        ((bisect n p a b (k + 1)).1 + (bisect n p a b (k + 1)).2) / 2)) := rfl
    simp only
    rw [hstep2]
    generalize hlo : (bisect n p a b k).1 = lo at *
    generalize hhi : (bisect n p a b k).2 = hi at *
    rw [hstep]
    have hpow : ((2 : Real)⁻¹) ^ (k + 1) = ((2 : Real)⁻¹) ^ k * (2 : Real)⁻¹ := Semiring.pow_succ _ _
    by_cases hm : eval n p ((lo + hi) / 2) ≤ 0
    · simp only [hm, ↓reduceIte]
      refine ⟨by grind, by grind, h3, by rw [hpow]; grind, trivial, h6, ?_, ?_⟩ <;>
      by_cases hm' : eval n p (((lo + hi) / 2 + hi) / 2) ≤ 0 <;> simp [hm'] <;> grind
    · simp only [hm, ↓reduceIte]
      refine ⟨h1, by grind, by grind, by rw [hpow]; grind, h5, by grind, ?_, ?_⟩ <;>
      by_cases hm' : eval n p ((lo + (lo + hi) / 2) / 2) ≤ 0 <;> simp [hm'] <;> grind

/-- **The intermediate value theorem for real polynomials.** -/
theorem ivt : IVT Real := by
  intro n p a b hab ha hb
  have spec := bisect_spec n p hab ha hb
  let lo := fun k => (bisect n p a b k).1
  let hi := fun k => (bisect n p a b k).2
  have hmono : ∀ k j, k ≤ j → lo k ≤ lo j ∧ hi j ≤ hi k := by
    intro k j hkj
    induction j with
    | zero => have : k = 0 := by omega
              subst this; exact ⟨Std.le_refl _, Std.le_refl _⟩
    | succ j ih =>
      rcases Nat.lt_or_eq_of_le hkj with h | h
      · obtain ⟨u, v⟩ := ih (by omega)
        obtain ⟨_, _, _, _, _, _, s7, s8⟩ := spec j
        exact ⟨Std.le_trans u s7, Std.le_trans s8 v⟩
      · subst h; exact ⟨Std.le_refl _, Std.le_refl _⟩
  have hw := tendsto_halving (b - a)
  -- `lo` is Cauchy
  have hC : Cauchy.IsCauchy lo := isCauchy_of fun d hd => by
    obtain ⟨N, hN⟩ := hw d hd
    refine ⟨N, fun m j hm hj => ?_⟩
    have key : ∀ m j, N ≤ m → m ≤ j → abs (lo m - lo j) < d := by
      intro m j hm hmj
      obtain ⟨u, v⟩ := hmono m j hmj
      obtain ⟨_, s2, _, s4, _⟩ := spec m
      obtain ⟨_, t2, _⟩ := spec j
      have := hN m hm
      rw [show (b - a) * (2 : Real)⁻¹ ^ m - 0 = hi m - lo m by rw [s4]; grind] at this
      rw [abs_sub_comm, abs_of_nonneg (by grind)]
      rw [abs_of_nonneg (by grind)] at this
      grind
    rcases Nat.le_total m j with h | h
    · exact key m j hm h
    · rw [abs_sub_comm]; exact key j m hj h
  obtain ⟨c, hc⟩ := complete lo hC
  have hhi : Tendsto hi c := by
    have := tendsto_add hc hw
    rw [show c + 0 = c by grind] at this
    intro d hd; obtain ⟨N, hN⟩ := this d hd
    exact ⟨N, fun k hk => by
      obtain ⟨_, _, _, s4, _⟩ := spec k
      have := hN k hk
      simp only at this
      rw [show lo k + (b - a) * (2 : Real)⁻¹ ^ k = hi k by grind] at this; exact this⟩
  refine ⟨c, ge_of_tendsto hc (fun k => (spec k).1), le_of_tendsto hhi (fun k => (spec k).2.2.1), ?_⟩
  have e1 := le_of_tendsto (tendsto_eval n p hc) (fun k => (spec k).2.2.2.2.1)
  have e2 := ge_of_tendsto (tendsto_eval n p hhi) (fun k => (spec k).2.2.2.2.2.1)
  grind

end Real

end LeviCivita
