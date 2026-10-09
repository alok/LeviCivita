/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Poly.Order
import Mathlib.Algebra.Order.Hom.Ring

/-!
# `R`-algebra structure and bundled order map

* `CHom : R →+* Poly Γ R`, the constant embedding as a ring hom.
* `Algebra R (Poly Γ R)` (hence `Module R (Poly Γ R)`). The data fields are the computable
  `•` and `C`; the two laws are checked through `toHahn`.
* `toHahnAlg : Poly Γ R →ₐ[R] R⟦Γ⟧`, the denotation as an `R`-algebra hom.
* `toLexHahnHom : Poly Γ R →+*o Lex R⟦Γ⟧`, the order-preserving ring hom into the ordered Hahn
  series, and `toLexHahnEmb : Poly Γ R ↪o Lex R⟦Γ⟧`, the same map as an order embedding.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita

open HahnSeries

namespace Poly

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] [DecidableEq R]

section Algebra

@[simp] theorem C_zero : (C 0 : Poly Γ R) = 0 :=
  toHahn_injective (by simp)

@[simp] theorem C_one : (C 1 : Poly Γ R) = 1 :=
  toHahn_injective (by simp)

@[simp] theorem C_add (a b : R) : (C (a + b) : Poly Γ R) = C a + C b :=
  toHahn_injective (by simp)

@[simp] theorem C_mul (a b : R) : (C (a * b) : Poly Γ R) = C a * C b :=
  toHahn_injective (by simp)

/-- The constant embedding as a ring hom. -/
def CHom : R →+* Poly Γ R where
  toFun := C
  map_zero' := C_zero
  map_one' := C_one
  map_add' := C_add
  map_mul' := C_mul

@[simp] theorem CHom_apply (a : R) : (CHom a : Poly Γ R) = C a := rfl

theorem smul_eq_C_mul (r : R) (p : Poly Γ R) : r • p = C r * p :=
  toHahn_injective (by simp)

/-- `Poly Γ R` is an `R`-algebra: `•` is coefficientwise scaling, `algebraMap = C`. Both are
computable. -/
instance instAlgebra : Algebra R (Poly Γ R) where
  algebraMap := CHom
  commutes' _ _ := mul_comm _ _
  smul_def' := smul_eq_C_mul

@[simp] theorem algebraMap_apply (r : R) : algebraMap R (Poly Γ R) r = C r := rfl

/-- The `Module R` instance is the one induced by the algebra; its `•` is the computable one. -/
example : Module R (Poly Γ R) := inferInstance

/-- The denotation is an `R`-algebra hom. -/
noncomputable def toHahnAlg : Poly Γ R →ₐ[R] R⟦Γ⟧ where
  __ := toHahn
  commutes' r := by simp [HahnSeries.algebraMap_apply]

@[simp] theorem toHahnAlg_apply (p : Poly Γ R) : toHahnAlg p = toHahn p := rfl

theorem toHahnAlg_injective : Function.Injective (toHahnAlg : Poly Γ R →ₐ[R] R⟦Γ⟧) :=
  toHahn_injective

end Algebra

section Order
variable [LinearOrder R] [IsStrictOrderedRing R]

/-- The denotation into the lexicographically ordered Hahn series, as an ordered ring hom. -/
noncomputable def toLexHahnHom : Poly Γ R →+*o Lex R⟦Γ⟧ where
  toFun := toLexHahn
  map_zero' := by simp [toLexHahn]
  map_one' := by simp [toLexHahn]
  map_add' _ _ := by simp [toLexHahn]
  map_mul' _ _ := by simp [toLexHahn]
  monotone' _ _ h := h

@[simp] theorem toLexHahnHom_apply (p : Poly Γ R) : toLexHahnHom p = toLex (toHahn p) := rfl

theorem toLexHahnHom_strictMono : StrictMono (toLexHahnHom : Poly Γ R →+*o Lex R⟦Γ⟧) :=
  toLexHahn_strictMono

theorem toLexHahnHom_injective : Function.Injective (toLexHahnHom : Poly Γ R →+*o Lex R⟦Γ⟧) :=
  toLexHahn_injective

/-- The denotation is an order embedding. -/
noncomputable def toLexHahnEmb : Poly Γ R ↪o Lex R⟦Γ⟧ :=
  OrderEmbedding.ofStrictMono toLexHahn toLexHahn_strictMono

@[simp] theorem toLexHahnEmb_apply (p : Poly Γ R) : toLexHahnEmb p = toLex (toHahn p) := rfl

theorem toLexHahn_neg (p : Poly Γ R) : toLexHahn (-p) = -toLexHahn p := by simp [toLexHahn]

theorem toLexHahn_abs (p : Poly Γ R) : toLexHahn |p| = |toLexHahn p| :=
  map_abs toLexHahnHom p

end Order

end Poly

end LeviCivita
