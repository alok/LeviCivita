/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Poly.Hahn
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.Algebra.Order.Ring.InjSurj

/-!
# The order on `Poly Γ R`

The order is the one pulled back from the lexicographic order on `Lex R⟦Γ⟧`:
`p < q ↔ toLex (toHahn p) < toLex (toHahn q)`. Its decidability instances are **computable**:
they compute the sign of the leading coefficient of `q - p` (`lt_iff_sign`, `le_iff_sign`).
So `decide` can evaluate statements like `(ε : Poly ℤ ℚ) < C (1/1000)`, and the proposition
it decides is the one about Hahn series.

`IsStrictOrderedRing (Poly Γ R)` is transported from `Lex R⟦Γ⟧` along the injective map.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita

open HahnSeries

namespace Poly

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq R]

/-- The denotation as an element of the lexicographically ordered Hahn series. -/
noncomputable abbrev toLexHahn (p : Poly Γ R) : Lex R⟦Γ⟧ := toLex (toHahn p)

theorem toLexHahn_injective : Function.Injective (toLexHahn : Poly Γ R → Lex R⟦Γ⟧) :=
  fun _ _ h => toHahn_injective (toLex.injective h)

/-! ### Sign -/

theorem sign_eq_one_iff (p : Poly Γ R) : p.sign = 1 ↔ 0 < toLex (toHahn p) := by
  rw [← leadingCoeff_pos_iff, ofLex_toLex, toHahn_apply, leadingCoeff_toHahnFun, sign]
  split_ifs with h₁ h₂ <;> simp [h₁]

theorem sign_eq_neg_one_iff (p : Poly Γ R) : p.sign = -1 ↔ toLex (toHahn p) < 0 := by
  rw [← leadingCoeff_neg_iff, ofLex_toLex, toHahn_apply, leadingCoeff_toHahnFun, sign]
  split_ifs with h₁ h₂
  · simp [h₁.asymm]
  · simp [h₂]
  · simp [h₂]

theorem sign_eq_zero_iff (p : Poly Γ R) : p.sign = 0 ↔ p = 0 := by
  rw [← leadCoeff_eq_zero_iff, sign]
  split_ifs with h₁ h₂
  · simp [h₁.ne']
  · simp [h₂.ne]
  · simp only [true_iff]
    exact le_antisymm (not_lt.1 h₁) (not_lt.1 h₂)

theorem sign_trichotomy (p : Poly Γ R) : p.sign = 1 ∨ p.sign = 0 ∨ p.sign = -1 := by
  unfold sign; split_ifs <;> simp

/-! ### Order instances -/

instance : LT (Poly Γ R) := ⟨fun p q => toLexHahn p < toLexHahn q⟩
instance : LE (Poly Γ R) := ⟨fun p q => toLexHahn p ≤ toLexHahn q⟩

theorem lt_def {p q : Poly Γ R} : p < q ↔ toLex (toHahn p) < toLex (toHahn q) := Iff.rfl
theorem le_def {p q : Poly Γ R} : p ≤ q ↔ toLex (toHahn p) ≤ toLex (toHahn q) := Iff.rfl

theorem lt_iff_sign {p q : Poly Γ R} : p < q ↔ (q - p).sign = 1 := by
  rw [sign_eq_one_iff, map_sub, lt_def, ← sub_pos]
  rfl

theorem le_iff_sign {p q : Poly Γ R} : p ≤ q ↔ (q - p).sign ≠ -1 := by
  rw [Ne, sign_eq_neg_one_iff, map_sub, le_def, ← sub_nonneg, ← not_lt]
  rfl

/-- `<` is decided by computing the sign of the difference. -/
instance decidableLT : DecidableLT (Poly Γ R) := fun _ _ => decidable_of_iff _ lt_iff_sign.symm

/-- `≤` is decided by computing the sign of the difference. -/
instance decidableLE : DecidableLE (Poly Γ R) := fun _ _ => decidable_of_iff _ le_iff_sign.symm

instance : Max (Poly Γ R) := ⟨fun p q => if p ≤ q then q else p⟩
instance : Min (Poly Γ R) := ⟨fun p q => if p ≤ q then p else q⟩
instance : Ord (Poly Γ R) := ⟨fun p q => compareOfLessAndEq p q⟩

/-- Auxiliary: the linear order pulled back from `Lex R⟦Γ⟧`. It is noncomputable only because it
mentions the (noncomputable) order on `Lex R⟦Γ⟧` as an argument; `instLinearOrder` restates the
data fields computably. -/
noncomputable abbrev linearOrderAux : LinearOrder (Poly Γ R) :=
  toLexHahn_injective.linearOrder _ Iff.rfl Iff.rfl
    (fun p q => by
      change toLexHahn (if p ≤ q then p else q) = _
      rw [min_def]
      split_ifs with h₁ h₂ h₂ <;> first | rfl | exact absurd h₁ h₂ | exact absurd h₂ h₁)
    (fun p q => by
      change toLexHahn (if p ≤ q then q else p) = _
      rw [max_def]
      split_ifs with h₁ h₂ h₂ <;> first | rfl | exact absurd h₁ h₂ | exact absurd h₂ h₁)
    (fun p q => by
      change _ = compareOfLessAndEq p q
      rw [LinearOrder.compare_eq_compareOfLessAndEq]
      have e₁ : (p < q) = (toLexHahn p < toLexHahn q) := rfl
      have e₂ : (p = q) = (toLexHahn p = toLexHahn q) :=
        propext toLexHahn_injective.eq_iff.symm
      simp only [compareOfLessAndEq, e₁, e₂])

/-- The linear order pulled back from `Lex R⟦Γ⟧`, with computable decidability, `min`, `max`
and `compare` (all via `sign`). -/
instance instLinearOrder : LinearOrder (Poly Γ R) where
  le := (· ≤ ·)
  lt := (· < ·)
  min := min
  max := max
  compare := compare
  toDecidableLE := decidableLE
  toDecidableLT := decidableLT
  toDecidableEq := inferInstance
  le_refl := linearOrderAux.le_refl
  le_trans := linearOrderAux.le_trans
  lt_iff_le_not_ge := linearOrderAux.lt_iff_le_not_ge
  le_antisymm := linearOrderAux.le_antisymm
  le_total := linearOrderAux.le_total
  min_def p q := by convert linearOrderAux.min_def p q
  max_def p q := by convert linearOrderAux.max_def p q
  compare_eq_compareOfLessAndEq p q := by
    convert linearOrderAux.compare_eq_compareOfLessAndEq p q

theorem toLexHahn_strictMono : StrictMono (toLexHahn : Poly Γ R → Lex R⟦Γ⟧) := fun _ _ h => h

theorem toLexHahn_le_iff {p q : Poly Γ R} : toLexHahn p ≤ toLexHahn q ↔ p ≤ q := Iff.rfl
theorem toLexHahn_lt_iff {p q : Poly Γ R} : toLexHahn p < toLexHahn q ↔ p < q := Iff.rfl

theorem pos_iff_sign {p : Poly Γ R} : 0 < p ↔ p.sign = 1 := by
  rw [lt_iff_sign, sub_zero]

/-- The ordered-ring structure, transported from `Lex R⟦Γ⟧`. -/
instance instIsStrictOrderedRing : IsStrictOrderedRing (Poly Γ R) :=
  Function.Injective.isStrictOrderedRing (toLexHahn : Poly Γ R → Lex R⟦Γ⟧)
    (by simp [toLexHahn]) (by simp [toLexHahn])
    (fun p q => by simp [toLexHahn]) (fun p q => by simp [toLexHahn])
    Iff.rfl Iff.rfl

end Poly

end LeviCivita
