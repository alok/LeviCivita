/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.Ring

/-!
# Exact geometric predicates

The four classical predicates of computational geometry, as explicit polynomials in the point
coordinates (Shewchuk's formulas, translated so that the last point is the origin):

* `orient2d a b c`: positive iff `a, b, c` are counterclockwise,
* `orient3d a b c d`,
* `incircle a b c d`: positive iff `d` is inside the circle through counterclockwise `a, b, c`,
* `insphere a b c d e`.

The formulas only use `+`, `-`, `*`, so they are stated for any type with these operations: the
same definition runs on `ℤ`, `ℚ`, `Poly Γ R`, `Float` (see `bench/`), and on the syntax trees of
`LeviCivita.Geometry.LazySign`.

The specification is the determinant of the standard matrix (`orient2d_eq_det`, …,
`insphere_eq_det`). For commutative rings we also prove antisymmetry, translation invariance and
naturality along ring homs (`map_orient2d`, …). Naturality is what transfers results along
`toHahn` and `stdPart`.
-/

open Matrix

namespace LeviCivita.Geometry

variable {K L : Type*}

section Formulas
variable [Add K] [Sub K] [Mul K]

/-- The 3×3 determinant `|a b c; d e f; g h i|` (cofactor expansion along the first row). -/
def det3 (a b c d e f g h i : K) : K :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- The 4×4 determinant, by cofactor expansion along the first row. -/
def det4 (a b c d e f g h i j k l m n o p : K) : K :=
  a * det3 f g h j k l n o p - b * det3 e g h i k l m o p + c * det3 e f h i j l m n p
    - d * det3 e f g i j k m n o

/-- Orientation of three points in the plane: `> 0` iff counterclockwise. -/
def orient2d (a b c : Fin 2 → K) : K :=
  (a 0 - c 0) * (b 1 - c 1) - (a 1 - c 1) * (b 0 - c 0)

/-- Orientation of four points in space. -/
def orient3d (a b c d : Fin 3 → K) : K :=
  det3 (a 0 - d 0) (a 1 - d 1) (a 2 - d 2)
       (b 0 - d 0) (b 1 - d 1) (b 2 - d 2)
       (c 0 - d 0) (c 1 - d 1) (c 2 - d 2)

/-- In-circle test: `> 0` iff `d` is inside the circle through the counterclockwise `a, b, c`. -/
def incircle (a b c d : Fin 2 → K) : K :=
  let ax := a 0 - d 0; let ay := a 1 - d 1
  let bx := b 0 - d 0; let by' := b 1 - d 1
  let cx := c 0 - d 0; let cy := c 1 - d 1
  det3 ax ay (ax * ax + ay * ay) bx by' (bx * bx + by' * by') cx cy (cx * cx + cy * cy)

/-- In-sphere test for five points in space. -/
def insphere (a b c d e : Fin 3 → K) : K :=
  let ax := a 0 - e 0; let ay := a 1 - e 1; let az := a 2 - e 2
  let bx := b 0 - e 0; let by' := b 1 - e 1; let bz := b 2 - e 2
  let cx := c 0 - e 0; let cy := c 1 - e 1; let cz := c 2 - e 2
  let dx := d 0 - e 0; let dy := d 1 - e 1; let dz := d 2 - e 2
  det4 ax ay az (ax * ax + ay * ay + az * az) bx by' bz (bx * bx + by' * by' + bz * bz)
    cx cy cz (cx * cx + cy * cy + cz * cz) dx dy dz (dx * dx + dy * dy + dz * dz)

end Formulas

section CommRing
variable [CommRing K] [CommRing L]

/-! ### Determinant specifications -/

theorem orient2d_eq_det (a b c : Fin 2 → K) :
    orient2d a b c = !![a 0, a 1, 1; b 0, b 1, 1; c 0, c 1, 1].det := by
  simp [orient2d, Matrix.det_fin_three]; ring

theorem orient3d_eq_det (a b c d : Fin 3 → K) :
    orient3d a b c d =
      !![a 0, a 1, a 2, 1; b 0, b 1, b 2, 1; c 0, c 1, c 2, 1; d 0, d 1, d 2, 1].det := by
  simp [orient3d, det3, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem incircle_eq_det (a b c d : Fin 2 → K) :
    incircle a b c d =
      !![a 0, a 1, a 0 ^ 2 + a 1 ^ 2, 1; b 0, b 1, b 0 ^ 2 + b 1 ^ 2, 1;
         c 0, c 1, c 0 ^ 2 + c 1 ^ 2, 1; d 0, d 1, d 0 ^ 2 + d 1 ^ 2, 1].det := by
  simp [incircle, det3, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem insphere_eq_det (a b c d e : Fin 3 → K) :
    insphere a b c d e =
      !![a 0, a 1, a 2, a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2, 1;
         b 0, b 1, b 2, b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2, 1;
         c 0, c 1, c 2, c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2, 1;
         d 0, d 1, d 2, d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2, 1;
         e 0, e 1, e 2, e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2, 1].det := by
  simp [insphere, det4, det3, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-! ### Antisymmetry -/

theorem orient2d_swap₁₂ (a b c : Fin 2 → K) : orient2d b a c = -orient2d a b c := by
  simp only [orient2d]; ring

theorem orient2d_swap₂₃ (a b c : Fin 2 → K) : orient2d a c b = -orient2d a b c := by
  simp only [orient2d]; ring

theorem orient2d_swap₁₃ (a b c : Fin 2 → K) : orient2d c b a = -orient2d a b c := by
  simp only [orient2d]; ring

theorem orient2d_rotate (a b c : Fin 2 → K) : orient2d b c a = orient2d a b c := by
  simp only [orient2d]; ring

theorem orient3d_swap₁₂ (a b c d : Fin 3 → K) : orient3d b a c d = -orient3d a b c d := by
  simp only [orient3d, det3]; ring

theorem orient3d_swap₂₃ (a b c d : Fin 3 → K) : orient3d a c b d = -orient3d a b c d := by
  simp only [orient3d, det3]; ring

theorem orient3d_swap₃₄ (a b c d : Fin 3 → K) : orient3d a b d c = -orient3d a b c d := by
  simp only [orient3d, det3]; ring

theorem incircle_swap₁₂ (a b c d : Fin 2 → K) : incircle b a c d = -incircle a b c d := by
  simp only [incircle, det3]; ring

theorem incircle_swap₃₄ (a b c d : Fin 2 → K) : incircle a b d c = -incircle a b c d := by
  simp only [incircle, det3]; ring

theorem insphere_swap₁₂ (a b c d e : Fin 3 → K) :
    insphere b a c d e = -insphere a b c d e := by
  simp only [insphere, det4, det3]; ring

theorem insphere_swap₄₅ (a b c d e : Fin 3 → K) :
    insphere a b c e d = -insphere a b c d e := by
  simp only [insphere, det4, det3]; ring

/-! ### Translation invariance -/

theorem orient2d_add_const (a b c t : Fin 2 → K) :
    orient2d (a + t) (b + t) (c + t) = orient2d a b c := by
  simp only [orient2d, Pi.add_apply]; ring

theorem orient3d_add_const (a b c d t : Fin 3 → K) :
    orient3d (a + t) (b + t) (c + t) (d + t) = orient3d a b c d := by
  simp only [orient3d, det3, Pi.add_apply]; ring

theorem incircle_add_const (a b c d t : Fin 2 → K) :
    incircle (a + t) (b + t) (c + t) (d + t) = incircle a b c d := by
  simp only [incircle, det3, Pi.add_apply]; ring

theorem insphere_add_const (a b c d e t : Fin 3 → K) :
    insphere (a + t) (b + t) (c + t) (d + t) (e + t) = insphere a b c d e := by
  simp only [insphere, det4, det3, Pi.add_apply]; ring

/-! ### Naturality along ring homs -/

section Map
variable {F : Type*} [FunLike F K L] [RingHomClass F K L] (f : F)

theorem map_det3 (a b c d e g h i j : K) :
    f (det3 a b c d e g h i j) = det3 (f a) (f b) (f c) (f d) (f e) (f g) (f h) (f i) (f j) := by
  simp only [det3, map_add, map_sub, map_mul]

theorem map_det4 (a b c d e g h i j k l m n o p q : K) :
    f (det4 a b c d e g h i j k l m n o p q) =
      det4 (f a) (f b) (f c) (f d) (f e) (f g) (f h) (f i) (f j) (f k) (f l) (f m) (f n) (f o)
        (f p) (f q) := by
  simp only [det4, map_add, map_sub, map_mul, map_det3]

theorem map_orient2d (a b c : Fin 2 → K) :
    f (orient2d a b c) = orient2d (f ∘ a) (f ∘ b) (f ∘ c) := by
  simp only [orient2d, map_sub, map_mul, Function.comp_apply]

theorem map_orient3d (a b c d : Fin 3 → K) :
    f (orient3d a b c d) = orient3d (f ∘ a) (f ∘ b) (f ∘ c) (f ∘ d) := by
  simp only [orient3d, map_det3, map_sub, Function.comp_apply]

theorem map_incircle (a b c d : Fin 2 → K) :
    f (incircle a b c d) = incircle (f ∘ a) (f ∘ b) (f ∘ c) (f ∘ d) := by
  simp only [incircle, map_det3, map_add, map_sub, map_mul, Function.comp_apply]

theorem map_insphere (a b c d e : Fin 3 → K) :
    f (insphere a b c d e) = insphere (f ∘ a) (f ∘ b) (f ∘ c) (f ∘ d) (f ∘ e) := by
  simp only [insphere, map_det4, map_add, map_sub, map_mul, Function.comp_apply]

end Map

end CommRing
end LeviCivita.Geometry
