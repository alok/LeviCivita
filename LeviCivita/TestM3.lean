/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Geometry

/-!
# Tests for M3: exact predicates, SoS, lazy sign

`#guard_msgs` `#eval`s run the compiled code; named `decide` theorems are checked by the kernel
(no `native_decide`). The SoS base is `b = 4`, which serves all four predicates.
-/

namespace LeviCivita.TestM3

open LeviCivita.Poly LeviCivita.Geometry LeviCivita.LazySign

/-! ### Exact predicates over `ℤ` and `ℚ` -/

/-- info: 1 -/
#guard_msgs in #eval orient2d (K := ℤ) ![0, 0] ![1, 0] ![0, 1]

/-- info: 0 -/
#guard_msgs in #eval orient2d (K := ℤ) ![0, 0] ![1, 1] ![2, 2]

/-- info: -1 / 4 -/
#guard_msgs in #eval orient2d (K := ℚ) ![0, 0] ![1/2, 0] ![0, -1/2]

/-- info: 1 -/
#guard_msgs in #eval orient3d (K := ℤ) ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] ![0, 0, 0]

-- `(0, 0)` is inside the circle through the counterclockwise `(1,0), (0,1), (-1,0)`
/-- info: 2 -/
#guard_msgs in #eval incircle (K := ℤ) ![1, 0] ![0, 1] ![-1, 0] ![0, 0]

-- `(0, -1)` is on that circle
/-- info: 0 -/
#guard_msgs in #eval incircle (K := ℤ) ![1, 0] ![0, 1] ![-1, 0] ![0, -1]

/-- info: 2 -/
#guard_msgs in #eval insphere (K := ℤ) ![1, 0, 0] ![0, 1, 0] ![0, 0, 1] ![-1, 0, 0] ![0, 0, 0]

theorem orient2d_ccw : orient2d (K := ℤ) ![0, 0] ![1, 0] ![0, 1] = 1 := by decide

theorem incircle_inside : 0 < incircle (K := ℤ) ![1, 0] ![0, 1] ![-1, 0] ![1, 1] ∨
    incircle (K := ℤ) ![1, 0] ![0, 1] ![-1, 0] ![1, 1] ≤ 0 := by decide

theorem orient2d_rat : orient2d (K := ℚ) ![0, 0] ![1/2, 0] ![0, 1/2] = 1/4 := by
  rw [orient2d_eq_det, Matrix.det_fin_three]; norm_num

/-! ### SoS -/

/-- Degenerate input: three collinear points, a duplicate, and a generic point. -/
def pts : Fin 5 → Fin 2 → ℤ := ![![0, 0], ![1, 1], ![2, 2], ![1, 1], ![1, 0]]

/-- info: -1 ε^1 + 1 ε^4 + 2 ε^16 + -1 ε^20 + -2 ε^64 + 1 ε^65 + -1 ε^256 + 1 ε^260 + -1 ε^320 + 1 ε^1024 + -1 ε^1025 + 1 ε^1040 -/
#guard_msgs in #eval orient2dSoS 4 pts 0 1 2

/-- info: (-1, 1, -1, 1, -1) -/
#guard_msgs in #eval ((orient2dSoS 4 pts 0 1 2).sign, (orient2dSoS 4 pts 1 0 2).sign,
  (orient2dSoS 4 pts 1 2 0).sign, (orient2dSoS 4 pts 1 3 4).sign,
  (orient2dSoS 4 pts 0 1 4).sign)

-- collinear points get a definite sign, and swapping two points flips it
theorem sos_collinear : (orient2dSoS 4 pts 0 1 2).sign = -1 := by decide
theorem sos_collinear_swap : (orient2dSoS 4 pts 1 0 2).sign = 1 := by decide
-- coincident points `1` and `3`
theorem sos_coincident : (orient2dSoS 4 pts 1 3 4).sign = 1 := by decide
theorem sos_coincident_swap : (orient2dSoS 4 pts 3 1 4).sign = -1 := by decide
-- nondegenerate input: the classical sign
theorem sos_generic : (orient2dSoS 4 pts 0 1 4).sign = (orient2d (pts 0) (pts 1) (pts 4)).sign :=
  by decide

-- the same facts from the theorems, for arbitrary input
theorem sos_ne_zero (x : Fin 5 → Fin 2 → ℤ) : orient2dSoS 4 x 0 1 2 ≠ 0 :=
  orient2dSoS_ne_zero (by norm_num) x (by decide) (by decide) (by decide)

theorem sos_sign_ne_zero (x : Fin 5 → Fin 2 → ℚ) : (orient2dSoS 4 x 0 1 2).sign ≠ 0 :=
  orient2dSoS_sign_ne_zero (by norm_num) x (by decide) (by decide) (by decide)

theorem sos_generic' : (orient2dSoS 4 pts 0 1 4).sign = (orient2d (pts 0) (pts 1) (pts 4)).sign :=
  by rw [orient2dSoS_sign (by norm_num) _ _ _ _ (by decide), signOf_int]

/-- Four coplanar points in space (all on `z = 0`), one of them repeated. -/
def pts3 : Fin 5 → Fin 3 → ℤ := ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1]]

/-- info: (0, -1, 1, -1) -/
#guard_msgs in #eval (orient3d (pts3 0) (pts3 1) (pts3 2) (pts3 3),
  (orient3dSoS 4 pts3 0 1 2 3).sign, (orient3dSoS 4 pts3 1 0 2 3).sign,
  (orient3dSoS 4 pts3 0 1 2 4).sign)

theorem sos3_coplanar : (orient3dSoS 4 pts3 0 1 2 3).sign = -1 := by decide
theorem sos3_coplanar_swap : (orient3dSoS 4 pts3 1 0 2 3).sign = 1 := by decide

/-- Four cocircular points. -/
def circ : Fin 4 → Fin 2 → ℤ := ![![1, 0], ![0, 1], ![-1, 0], ![0, -1]]

/-- info: (0, 1, -1) -/
#guard_msgs in #eval (incircle (circ 0) (circ 1) (circ 2) (circ 3),
  (incircleSoS 4 circ 0 1 2 3).sign, (incircleSoS 4 circ 1 0 2 3).sign)

theorem sos_cocircular : (incircleSoS 4 circ 0 1 2 3).sign = 1 := by decide +kernel

theorem sos_incircle_ne_zero (x : Fin 4 → Fin 2 → ℤ) : incircleSoS 4 x 0 1 2 3 ≠ 0 :=
  incircleSoS_ne_zero le_rfl (by norm_num) x (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- Five cospherical points. -/
def sph : Fin 5 → Fin 3 → ℤ := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![-1, 0, 0], ![0, -1, 0]]

/-- info: (0, true) -/
#guard_msgs in #eval (insphere (sph 0) (sph 1) (sph 2) (sph 3) (sph 4),
  (insphereSoS 4 sph 0 1 2 3 4).sign != 0)

/-! ### Lazy sign -/

/-- info: (none, some (-1), some (-1)) -/
#guard_msgs in #eval (lazySign 1 (orient2dExpr 4 pts 0 1 2), lazySign 4 (orient2dExpr 4 pts 0 1 2),
  orient2dLazy 4 pts 0 1 2)

-- nondegenerate input: resolved by the first, unperturbed pass
/-- info: some (-1) -/
#guard_msgs in #eval lazySign 1 (orient2dExpr 4 pts 0 1 4)

theorem lazy_collinear : orient2dLazy 4 pts 0 1 2 = some (-1) := by decide

theorem lazy_agrees : orient2dLazy 4 pts 0 1 2 = some (orient2dSoS 4 pts 0 1 2).sign := by decide

theorem lazy_sound_example {s : ℤ} (h : orient2dLazy 4 pts 1 3 4 = some s) :
    (orient2dSoS 4 pts 1 3 4).sign = s :=
  orient2dLazy_sound h

theorem truncLT_example : (((1 : Poly ℤ ℤ) + ε) * (1 + ε)).truncLT 2 = 1 + 2 * ε := by decide

theorem mulTrunc_example : mulTrunc 2 ((1 : Poly ℤ ℤ) + ε) (1 + ε) = 1 + 2 * ε := by decide

end LeviCivita.TestM3
