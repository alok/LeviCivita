/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Geometry
import LeviCivita.TestM3

/-!
# Tests for M5: `FinLex`, `MultiEps`, SoS with independent infinitesimals

`#guard_msgs` `#eval`s run the compiled code (which uses the `@[csimp]` loop for
`Fin.lexCmp`). Named `decide` theorems are checked by the kernel; there is no `native_decide`.
-/

namespace LeviCivita.TestM5

open LeviCivita.Poly LeviCivita.Geometry FinLex

/-! ### `FinLex` -/

/-- info: (true, false, Ordering.lt, ![1, 5], ![2, 3, 0]) -/
#guard_msgs in
#eval (decide ((toFinLex ![0, 5] : FinLex 2 ℤ) < toFinLex ![1, 0]),
  decide ((toFinLex ![1, 0] : FinLex 2 ℤ) < toFinLex ![0, 5]),
  compare (toFinLex ![1, 0] : FinLex 2 ℤ) (toFinLex ![1, 5]),
  max (toFinLex ![1, 0] : FinLex 2 ℤ) (toFinLex ![1, 5]),
  (FinLex.single 1 3 : FinLex 3 ℤ) + FinLex.single 0 2)

theorem finLex_lt : (toFinLex ![0, 5] : FinLex 2 ℤ) < toFinLex ![1, 0] := by decide

theorem finLex_le : (toFinLex ![1, 5] : FinLex 2 ℤ) ≤ toFinLex ![1, 5] := by decide

theorem finLex_ne : (toFinLex ![1, 5] : FinLex 2 ℤ) ≠ toFinLex ![1, 0] := by decide

theorem finLex_single_lt : (FinLex.single 2 1 : FinLex 3 ℤ) < FinLex.single 0 1 := by decide

theorem finLex_min :
    min (toFinLex ![3, -1, 7] : FinLex 3 ℤ) (toFinLex ![3, -1, 2]) = toFinLex ![3, -1, 2] := by
  decide

/-- The transfer: `toLexOrderAddIso` maps `<` to Mathlib's `<` on `Lex (Fin 2 → ℤ)`. -/
theorem finLex_transfer : toLex ![0, 5] < (toLex ![1, 0] : Lex (Fin 2 → ℤ)) :=
  (toLexOrderIso.lt_iff_lt.2 finLex_lt :)

-- A compiled comparison of two long tuples (`k = 2000`): the `@[csimp]` loop is linear.
/-- info: Ordering.gt -/
#guard_msgs in
#eval compare (FinLex.single 1999 1 : FinLex 2000 ℤ) (FinLex.single 1999 1 + FinLex.single 1999 (-1))

/-! ### SoS with independent infinitesimals (same inputs as `TestM3`) -/

open LeviCivita.TestM3 (pts pts3 circ sph)

/-- info: (1, -1, 1, -1, -1) -/
#guard_msgs in #eval ((orient2dSoSMulti pts 0 1 2).sign, (orient2dSoSMulti pts 1 0 2).sign,
  (orient2dSoSMulti pts 1 2 0).sign, (orient2dSoSMulti pts 1 3 4).sign,
  (orient2dSoSMulti pts 0 1 4).sign)

-- collinear points get a definite sign, and swapping two points flips it. On this degenerate
-- input the multi-ε scheme picks the opposite sign to M3's `orient2dSoS 4` (a different, equally
-- valid perturbation; see `NOTES-M5.md`).
theorem multi_collinear : (orient2dSoSMulti pts 0 1 2).sign = 1 := by decide +kernel
theorem multi_collinear_swap : (orient2dSoSMulti pts 1 0 2).sign = -1 := by decide +kernel
-- coincident points `1` and `3`
theorem multi_coincident : (orient2dSoSMulti pts 1 3 4).sign = -1 := by decide +kernel
-- nondegenerate input: the classical sign, by evaluation and by the theorem
theorem multi_generic :
    (orient2dSoSMulti pts 0 1 4).sign = (orient2d (pts 0) (pts 1) (pts 4)).sign := by
  decide +kernel
theorem multi_generic' :
    (orient2dSoSMulti pts 0 1 4).sign = (orient2d (pts 0) (pts 1) (pts 4)).sign := by
  rw [orient2dSoSMulti_sign _ _ _ _ (by decide), signOf_int]

theorem multi_ne_zero (x : Fin 5 → Fin 2 → ℤ) : orient2dSoSMulti x 0 1 2 ≠ 0 :=
  orient2dSoSMulti_ne_zero x (by decide) (by decide) (by decide)

theorem multi_sign_ne_zero (x : Fin 5 → Fin 2 → ℚ) : (orient2dSoSMulti x 0 1 2).sign ≠ 0 :=
  orient2dSoSMulti_sign_ne_zero x (by decide) (by decide) (by decide)

/-- info: (-1, 1) -/
#guard_msgs in #eval ((orient3dSoSMulti pts3 0 1 2 3).sign, (orient3dSoSMulti pts3 1 0 2 3).sign)

/-- info: (1, -1) -/
#guard_msgs in #eval ((incircleSoSMulti circ 0 1 2 3).sign, (incircleSoSMulti circ 1 0 2 3).sign)

theorem multi_cocircular : (incircleSoSMulti circ 0 1 2 3).sign = 1 := by decide +kernel

theorem multi_incircle_ne_zero (x : Fin 4 → Fin 2 → ℤ) : incircleSoSMulti x 0 1 2 3 ≠ 0 :=
  incircleSoSMulti_ne_zero (by norm_num) x (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- info: true -/
#guard_msgs in #eval (insphereSoSMulti sph 0 1 2 3 4).sign != 0

/-! ### Upstream simulation

What `UPSTREAM.md` proposes for Mathlib, simulated locally: remove `Pi.Lex.linearOrder` from
instance search, install the instance-argument version and the `Fintype` decision procedure,
and run the M2 two-infinitesimal tests on Mathlib's own `Lex (Fin 2 → ℤ)`. -/

section UpstreamSim

attribute [-instance] Pi.Lex.linearOrder

/-- The proposed `Pi.Lex.linearOrder`: decidability is an instance argument. -/
instance simLinearOrder {ι : Type*} {β : ι → Type*} [LinearOrder ι] [WellFoundedLT ι]
    [∀ a, LinearOrder (β a)] [DecidableLT (Lex (∀ i, β i))] : LinearOrder (Lex (∀ i, β i)) :=
  @linearOrderOfSTO (Πₗ i, β i) (· < ·) { trichotomous := (Pi.trichotomous_lex _ _).1 }
    inferInstance

attribute [local instance] Pi.Lex.decidableLTOfFintype

abbrev L2 := Lex (Fin 2 → ℤ)

/-- info: (true, false, true) -/
#guard_msgs in
#eval (decide ((single (toLex ![1, 0]) 1 : Poly L2 ℚ) < single (toLex ![0, 1]) 1),
  decide ((single (toLex ![0, 1]) 1 : Poly L2 ℚ) < single (toLex ![1, 0]) 1),
  decide ((single (toLex ![1, 0]) 1 : Poly L2 ℚ) < single (toLex ![0, 1]) 1 ^ 5))

theorem sim_eps1_lt_eps2 : (single (toLex ![1, 0]) 1 : Poly L2 ℚ) < single (toLex ![0, 1]) 1 := by
  decide +kernel

theorem sim_eps1_lt_eps2_pow :
    (single (toLex ![1, 0]) 1 : Poly L2 ℚ) < single (toLex ![0, 1]) 1 ^ 5 := by decide +kernel

theorem sim_int_eps1_lt_eps2 :
    (single (toLex ![1, 0]) 1 : Poly L2 ℤ) < single (toLex ![0, 1]) 1 := by decide

theorem sim_lex_lt : toLex ![0, 5] < (toLex ![1, 0] : L2) := by decide

/-- The instance found is propositionally Mathlib's original one. -/
theorem sim_linearOrder_eq : (inferInstance : LinearOrder L2) = Pi.Lex.linearOrder :=
  LinearOrder.ext fun _ _ => Iff.rfl

end UpstreamSim

end LeviCivita.TestM5
