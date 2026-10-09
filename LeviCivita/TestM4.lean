/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Approx

/-!
# Tests for M4: precision-tracked approximations

`#guard_msgs` `#eval`s run the compiled code; named `decide +kernel` theorems are checked by the
kernel (no `native_decide`). Coefficients are in `ℚ` (the inverse needs a field), so plain
`decide` would need the `semireducible` workaround of `LeviCivita.Test`; `+kernel` is used.
-/

namespace LeviCivita.TestM4

open LeviCivita.Poly LeviCivita.Approx

abbrev P := Poly ℤ ℚ
abbrev A := Approx ℤ ℚ

/-! ### Inverse of `1 + ε` -/

/-- `1 + ε + O(ε⁵)`. -/
def a : A := (exact (1 + ε : P)).withPrec 5

/-- info: 1 ε^0 + 1 ε^1 + O(ε^5) -/
#guard_msgs in #eval a

/-- info: some 1 ε^0 + -1 ε^1 + 1 ε^2 + -1 ε^3 + 1 ε^4 + O(ε^5) -/
#guard_msgs in #eval a.inv? 3

-- Newton doubles the relative precision: 2, 4, then capped at the input precision 5.
/-- info: some 1 ε^0 + -1 ε^1 + O(ε^2) -/
#guard_msgs in #eval a.inv? 1

/-- info: some 1 ε^0 + -1 ε^1 + 1 ε^2 + -1 ε^3 + O(ε^4) -/
#guard_msgs in #eval a.inv? 2

-- `(1 + ε)⁻¹ * (1 + ε) = 1 + O(ε⁵)`
/-- info: some 1 ε^0 + O(ε^5) -/
#guard_msgs in #eval (a.inv? 3).map (· * a)

-- An exact input: the precision comes only from the residual certificate.
/-- info: some 1 ε^0 + -1 ε^1 + 1 ε^2 + -1 ε^3 + 1 ε^4 + -1 ε^5 + 1 ε^6 + -1 ε^7 + O(ε^8) -/
#guard_msgs in #eval (exact (1 + ε : P)).inv? 3

theorem inv_one_add_eps :
    (a.inv? 3).map Approx.val = some (1 - ε + ε ^ 2 - ε ^ 3 + ε ^ 4) ∧
      (a.inv? 3).map Approx.prec = some 5 := by
  decide +kernel

theorem inv_mul_self_val :
    (a.inv? 3).map (fun b => (b * a).val) = some 1 ∧
      (a.inv? 3).map (fun b => (b * a).prec) = some 5 := by
  decide +kernel

/-- `(1 + ε)⁻¹ * (1 + ε)` represents `1` at the claimed precision, by the soundness theorems
(no computation of Hahn series). -/
theorem inv_mul_self_represents {b : A} (hb : a.inv? 3 = some b) : (b * a).Represents 1 := by
  have ha : a.Represents (toHahn (1 + ε : P)) := (represents_exact _).withPrec 5
  have hc : a.Certified := by decide +kernel
  have h := (ha.inv? hb).mul ha
  rwa [inv_mul_cancel₀ (ha.ne_zero hc)] at h

/-! ### Inverse with a nontrivial leading term: `2ε + 3ε² + O(ε⁴)` -/

def b : A := ⟨2 * ε + 3 * ε ^ 2 + ε ^ 7, 4⟩

-- relative precision `4 - 1 = 3`, so `b⁻¹` is known to `-1 + 3 = 2`
/-- info: some (1 : Rat)/2 ε^-1 + (-3 : Rat)/4 ε^0 + (9 : Rat)/8 ε^1 + O(ε^2) -/
#guard_msgs in #eval b.inv? 4

-- the product rule: `min (2 + ord b) (4 + ord b⁻¹) = min 3 3`
/-- info: some 1 ε^0 + O(ε^3) -/
#guard_msgs in #eval (b.inv? 4).map (· * b)

theorem inv_b_prec : (b.inv? 4).map Approx.prec = some 2 := by decide +kernel

/-! ### Γ = ℚ: `(1 + √ε)⁻¹` -/

def s : Approx ℚ ℚ := (exact (1 + single (1/2) 1 : Poly ℚ ℚ)).withPrec 2

/-- info: some 1 ε^0 + -1 ε^(1 : Rat)/2 + 1 ε^1 + -1 ε^(3 : Rat)/2 + O(ε^2) -/
#guard_msgs in #eval s.inv? 3

/-! ### Precision rules for `+` and `*` -/

-- `(ε + O(ε³)) * (1 + O(ε²))`: `min (3 + 0) (2 + 1) = 3`
/-- info: 1 ε^1 + O(ε^3) -/
#guard_msgs in #eval ofPoly (ε : P) 3 * ofPoly 1 2

-- unknown order: `O(ε²) * 1 = O(ε²)` (`ord` of `0 + O(ε²)` is `2`)
/-- info: 0 + O(ε^2) -/
#guard_msgs in #eval (⟨0, 2⟩ : A) * exact 1

/-- info: 1 ε^0 + 2 ε^1 + O(ε^3) -/
#guard_msgs in #eval ofPoly (1 + ε : P) 3 + ofPoly (ε + ε ^ 4 : P) 7

theorem mul_prec_example : (ofPoly (ε : P) 3 * ofPoly 1 2).prec = 3 := by decide +kernel

theorem mul_unknown_order : ((⟨0, 2⟩ : A) * exact 1).prec = 2 := by decide +kernel

/-! ### Certified sign -/

-- `0 + O(ε)`: unresolved
/-- info: none -/
#guard_msgs in #eval (ofPoly (ε ^ 2 : P) 1).sign?

/-- info: some 1 -/
#guard_msgs in #eval (ofPoly (ε - ε ^ 3 : P) 2).sign?

/-- info: LeviCivita.Approx.Verdict.reject -/
#guard_msgs in #eval (ofPoly (-ε : P) 2).decidePos?

/-- info: LeviCivita.Approx.Verdict.unresolved -/
#guard_msgs in #eval (ofPoly (ε ^ 2 : P) 1).decidePos?

theorem sign_unresolved : (ofPoly (ε ^ 2 : P) 1).sign? = none := by decide +kernel

theorem sign_resolved : (ofPoly (ε - ε ^ 3 : P) 2).sign? = some 1 := by decide +kernel

theorem sign_exact_zero : (exact (0 : P)).sign? = some 0 := by decide +kernel

theorem accept_example : (⟨ε, 2⟩ : A).decidePos? = .accept := by decide +kernel

/-- Every series that is `ε + O(ε²)` is positive. -/
theorem pos_of_approx {x : HahnSeries ℤ ℚ} (hx : (⟨ε, 2⟩ : A).Represents x) : 0 < toLex x :=
  decidePos?_accept accept_example hx

/-- The inverse of anything `1 + ε + O(ε⁵)` is positive: the certified sign of the computed
inverse. -/
theorem inv_pos_example {x : HahnSeries ℤ ℚ} (hx : a.Represents x) : 0 < toLex x⁻¹ := by
  have hb : a.inv? 3 = some ⟨1 - ε + ε ^ 2 - ε ^ 3 + ε ^ 4, 5⟩ := by decide +kernel
  exact (sign?_sound (by decide +kernel) (hx.inv? hb)).1.1 rfl

end LeviCivita.TestM4
