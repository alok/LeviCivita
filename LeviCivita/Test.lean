/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Poly

/-!
# Tests for `Poly`

`#eval` examples (compiled code) and kernel-checked `decide` examples (no `native_decide`, no
`Lean.ofReduceBool`). Every `decide` example is a named theorem so `AxiomAudit` can check it.

Core's `Rat.add`/`Rat.mul`/`Rat.sub`/`Rat.inv` are `@[irreducible]`, so the elaborator's `whnf`
cannot evaluate even `(1 : ℚ) + 1 = 2` with plain `decide`. Two workarounds, both used below:
* `decide +kernel` skips the elaborator and lets the kernel (which ignores reducibility hints)
  evaluate the `Decidable` instance;
* plain `decide` after locally marking those four `Rat` operations `semireducible`. That
  attribute only affects elaboration-time unfolding, not what the kernel accepts.
-/

namespace LeviCivita.Test

open LeviCivita.Poly

abbrev P := LeviCivita.Poly ℤ ℚ

/-! ### `#eval` -/

/-- info: 1 ε^0 + -1 ε^2 -/
#guard_msgs in #eval ((1 : P) + ε) * (1 - ε)

/-- info: 1 ε^0 -/
#guard_msgs in #eval (ε : P) * H

/-- info: 1 ε^-3 + 3 ε^-1 + 3 ε^1 + 1 ε^3 -/
#guard_msgs in #eval ((H : P) + ε) ^ 3

/-- info: 1000000000 ε^0 -/
#guard_msgs in #eval (10 : P) ^ 9

/-- info: true -/
#guard_msgs in #eval decide ((ε : P) < C (1 / 1000))

/-- info: 1 -/
#guard_msgs in #eval (C (1 / 1000) - ε : P).sign

/-- info: -1 -/
#guard_msgs in #eval (ε - H : P).sign

/-- info: 0 -/
#guard_msgs in #eval ((1 + ε) * (1 - ε) - (1 - ε ^ 2) : P).sign

/-- info: 1 ε^-1 -/
#guard_msgs in #eval max (H : P) 1000000

/-- info: (7 : Rat)/2 ε^0 + (1 : Rat)/2 ε^1 -/
#guard_msgs in #eval ((1/2 : ℚ) • ((7 : P) + ε))

/-! ### Kernel-checked `decide +kernel` -/

theorem eps_lt_one_thousandth : (ε : P) < C (1 / 1000) := by decide +kernel

theorem eps_pos : (0 : P) < ε := by decide +kernel

theorem eps_sq_lt_eps : (ε : P) ^ 2 < ε := by decide +kernel

theorem ten_pow_nine_lt_H : (10 : P) ^ 9 < H := by decide +kernel

theorem eps_mul_H : (ε : P) * H = 1 := by decide +kernel

theorem one_add_eps_mul_one_sub_eps : ((1 : P) + ε) * (1 - ε) = 1 - ε ^ 2 := by decide +kernel

theorem H_sq_gt : (1000000 : P) * H < H ^ 2 := by decide +kernel

theorem neg_eps_lt_zero : -(ε : P) < 0 := by decide +kernel

theorem eps_le_eps : (ε : P) ≤ ε := by decide +kernel

theorem not_H_le_eps : ¬ (H : P) ≤ ε := by decide +kernel

/-! ### Plain `decide` -/

section PlainDecide

attribute [local semireducible] Rat.add Rat.mul Rat.sub Rat.inv

theorem eps_lt_one_thousandth' : (ε : P) < C (1 / 1000) := by decide

theorem eps_pos' : (0 : P) < ε := by decide

theorem eps_sq_lt_eps' : (ε : P) ^ 2 < ε := by decide

theorem ten_pow_nine_lt_H' : (10 : P) ^ 9 < H := by decide

theorem eps_mul_H' : (ε : P) * H = 1 := by decide

theorem one_add_eps_mul_one_sub_eps' : ((1 : P) + ε) * (1 - ε) = 1 - ε ^ 2 := by decide

end PlainDecide

/-! ### `Poly ℤ ℤ`: plain `decide` with no attribute changes -/

theorem int_eps_mul_H : (ε : Poly ℤ ℤ) * H = 1 := by decide

theorem int_ten_pow_nine_lt_H : (10 : Poly ℤ ℤ) ^ 9 < H := by decide

theorem int_eps_pos : (0 : Poly ℤ ℤ) < ε := by decide

/-! ### Consequences via the transported structure (no computation) -/

/-- An ordered-ring fact derived from the transported `IsStrictOrderedRing` instance. -/
theorem eps_sq_pos : (0 : P) < ε ^ 2 := pow_pos eps_pos 2

/-- The denotation of `ε` is Mathlib's `single 1 1`. -/
theorem toHahn_eps : toHahn (ε : P) = HahnSeries.single 1 1 := toHahn_ε

end LeviCivita.Test
