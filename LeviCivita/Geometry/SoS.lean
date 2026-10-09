/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Geometry.Predicates
import LeviCivita.Poly.Std
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Combinatorics.Colex

set_option linter.unusedSectionVars false

namespace LeviCivita.Geometry

open Poly MvPolynomial

variable {R : Type*} [CommRing R] [DecidableEq R]

section Key
variable {σ : Type*}

/-- The SoS substitution: variable `k` ↦ `ε^(2^(w k))`. -/
noncomputable def sosSubst (w : σ → ℕ) : MvPolynomial σ R →ₐ[R] Poly ℤ R :=
  aeval fun k => single ((2 ^ w k : ℕ) : ℤ) 1

/-- The exponent of the monomial `m` under `sosSubst w`. -/
def sosExpo (w : σ → ℕ) (m : σ →₀ ℕ) : ℕ := ∑ i ∈ m.support, m i * 2 ^ w i

theorem prod_single_pow (s : Finset σ) (a : σ → ℤ) (d : σ → ℕ) :
    ∏ i ∈ s, (HahnSeries.single (a i) (1 : R) : HahnSeries ℤ R) ^ d i =
      HahnSeries.single (∑ i ∈ s, d i • a i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, HahnSeries.single_pow,
      HahnSeries.single_mul_single, one_pow, one_mul]

theorem toHahn_sosSubst (w : σ → ℕ) (D : MvPolynomial σ R) :
    toHahn (sosSubst w D) =
      ∑ m ∈ D.support, HahnSeries.single ((sosExpo w m : ℕ) : ℤ) (D.coeff m) := by
  have h1 : toHahn (sosSubst w D) = toHahnAlg (sosSubst w D) := rfl
  rw [h1, sosSubst, ← AlgHom.comp_apply, comp_aeval, aeval_def, eval₂_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [toHahnAlg_apply, toHahn_single]
  rw [prod_single_pow, ← HahnSeries.C_eq_algebraMap, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one]
  congr 1
  simp [sosExpo]

theorem sosExpo_injOn {w : σ → ℕ} (hw : Function.Injective w) {m m' : σ →₀ ℕ}
    (hm : ∀ k, m k ≤ 1) (hm' : ∀ k, m' k ≤ 1) (h : sosExpo w m = sosExpo w m') : m = m' := by
  have key : ∀ m : σ →₀ ℕ, (∀ k, m k ≤ 1) →
      sosExpo w m = ∑ j ∈ m.support.map ⟨w, hw⟩, 2 ^ j := by
    intro m hm
    rw [Finset.sum_map, sosExpo]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : m i = 1 := by have := hm i; have := Finsupp.mem_support_iff.1 hi; omega
    simp [this]
  rw [key m hm, key m' hm'] at h
  have hs := Finset.map_injective _ (Finset.geomSum_injective le_rfl h)
  classical
  ext k
  have e : ∀ m : σ →₀ ℕ, (∀ k, m k ≤ 1) → m k = if k ∈ m.support then 1 else 0 := by
    intro m hm
    split_ifs with hk
    · have := hm k; have := Finsupp.mem_support_iff.1 hk; omega
    · exact Finsupp.notMem_support_iff.1 hk
  rw [e m hm, e m' hm', hs]

/-- **Key lemma.** A nonzero polynomial of degree `≤ 1` in each variable stays nonzero under
the SoS substitution `X k ↦ ε^(2^(w k))`, for injective `w`: distinct squarefree monomials go to
distinct powers of `ε` (binary expansion), so no cancellation can occur. -/
theorem sosSubst_ne_zero {w : σ → ℕ} (hw : Function.Injective w) {D : MvPolynomial σ R}
    (hD : D ≠ 0) (hsq : ∀ m ∈ D.support, ∀ k, m k ≤ 1) : sosSubst w D ≠ 0 := by
  obtain ⟨m₀, hm₀⟩ := MvPolynomial.ne_zero_iff.1 hD
  have hmem : m₀ ∈ D.support := MvPolynomial.mem_support_iff.2 hm₀
  intro h
  have := congrArg (fun p => (toHahn p).coeff ((sosExpo w m₀ : ℕ) : ℤ)) h
  simp only [toHahn_sosSubst, HahnSeries.coeff_sum, HahnSeries.coeff_single, map_zero,
    HahnSeries.coeff_zero] at this
  rw [Finset.sum_eq_single m₀ (fun m hm hne => ?_) (fun h => absurd hmem h), ite_eq_left rfl] at this
  · exact hm₀ this
  · rw [ite_eq_right]
    intro he
    exact hne (sosExpo_injOn hw (hsq m hm) (hsq m₀ hmem) (Nat.cast_injective he).symm)

end Key

/-! ### Column-degree bookkeeping

`DegLe S f`: every variable `(i, j)` occurs in `f` with degree `≤ 1` if the coordinate `j ∈ S`,
and does not occur otherwise. A product of polynomials with disjoint coordinate sets adds the
sets, so the determinant of a matrix whose column `j` only mentions coordinate `j` is multilinear:
degree `≤ 1` in every variable. -/

section DegLe
variable [Nontrivial R] {n d : ℕ}

/-- See the section docstring. -/
def DegLe (S : Finset (Fin d)) (f : MvPolynomial (Fin n × Fin d) R) : Prop :=
  ∀ k, degreeOf k f ≤ if k.2 ∈ S then 1 else 0

theorem DegLe.mono {S T : Finset (Fin d)} {f : MvPolynomial (Fin n × Fin d) R} (h : DegLe S f)
    (hST : S ⊆ T) : DegLe T f := fun k => by
  have := h k
  by_cases h₁ : k.2 ∈ S
  · simpa [h₁, hST h₁] using this
  · simp only [h₁, ite_false] at this; omega

theorem DegLe.add {S : Finset (Fin d)} {f g : MvPolynomial (Fin n × Fin d) R} (hf : DegLe S f)
    (hg : DegLe S g) : DegLe S (f + g) := fun k =>
  (degreeOf_add_le k f g).trans (max_le (hf k) (hg k))

theorem DegLe.sub {S : Finset (Fin d)} {f g : MvPolynomial (Fin n × Fin d) R} (hf : DegLe S f)
    (hg : DegLe S g) : DegLe S (f - g) := fun k =>
  (degreeOf_sub_le k f g).trans (max_le (hf k) (hg k))

theorem DegLe.mul {S T : Finset (Fin d)} {f g : MvPolynomial (Fin n × Fin d) R} (hf : DegLe S f)
    (hg : DegLe T g) (hST : Disjoint S T) : DegLe (S ∪ T) (f * g) := fun k => by
  refine (degreeOf_mul_le k f g).trans ?_
  have h1 := hf k; have h2 := hg k
  by_cases hS : k.2 ∈ S
  · have hT : k.2 ∉ T := Finset.disjoint_left.1 hST hS
    simp only [hS, hT, ite_true, ite_false, Finset.mem_union, true_or] at h1 h2 ⊢; omega
  · by_cases hT : k.2 ∈ T
    · simp only [hS, hT, ite_true, ite_false, Finset.mem_union, or_true] at h1 h2 ⊢; omega
    · simp only [hS, hT, ite_false] at h1 h2; omega

theorem degLe_C_add_X (c : R) (i : Fin n) (j : Fin d) :
    DegLe {j} (MvPolynomial.C c + X (i, j) : MvPolynomial (Fin n × Fin d) R) := fun k => by
  classical
  refine (degreeOf_add_le k _ _).trans (max_le (by simp) ?_)
  by_cases hk : k = (i, j)
  · subst hk; simp
  · rw [degreeOf_X_of_ne hk]; exact Nat.zero_le _

theorem DegLe.det3 {S₀ S₁ S₂ : Finset (Fin d)} (h01 : Disjoint S₀ S₁) (h02 : Disjoint S₀ S₂)
    (h12 : Disjoint S₁ S₂) {a b c e f g h i j : MvPolynomial (Fin n × Fin d) R}
    (ha : DegLe S₀ a) (hb : DegLe S₁ b) (hc : DegLe S₂ c) (he : DegLe S₀ e) (hf : DegLe S₁ f)
    (hg : DegLe S₂ g) (hh : DegLe S₀ h) (hi : DegLe S₁ i) (hj : DegLe S₂ j) :
    DegLe (S₀ ∪ S₁ ∪ S₂) (Geometry.det3 a b c e f g h i j) := by
  have m12 : ∀ {x y : MvPolynomial (Fin n × Fin d) R}, DegLe S₁ x → DegLe S₂ y →
      DegLe (S₁ ∪ S₂) (x * y) := fun hx hy => hx.mul hy h12
  have m21 : ∀ {x y : MvPolynomial (Fin n × Fin d) R}, DegLe S₂ x → DegLe S₁ y →
      DegLe (S₁ ∪ S₂) (x * y) := fun hx hy => (hx.mul hy h12.symm).mono (by
        rw [Finset.union_comm])
  have m02 : ∀ {x y : MvPolynomial (Fin n × Fin d) R}, DegLe S₀ x → DegLe S₂ y →
      DegLe (S₀ ∪ S₂) (x * y) := fun hx hy => hx.mul hy h02
  have m20 : ∀ {x y : MvPolynomial (Fin n × Fin d) R}, DegLe S₂ x → DegLe S₀ y →
      DegLe (S₀ ∪ S₂) (x * y) := fun hx hy => (hx.mul hy h02.symm).mono (by
        rw [Finset.union_comm])
  have m01 : ∀ {x y : MvPolynomial (Fin n × Fin d) R}, DegLe S₀ x → DegLe S₁ y →
      DegLe (S₀ ∪ S₁) (x * y) := fun hx hy => hx.mul hy h01
  have m10 : ∀ {x y : MvPolynomial (Fin n × Fin d) R}, DegLe S₁ x → DegLe S₀ y →
      DegLe (S₀ ∪ S₁) (x * y) := fun hx hy => (hx.mul hy h01.symm).mono (by
        rw [Finset.union_comm])
  have d0 : Disjoint S₀ (S₁ ∪ S₂) := Finset.disjoint_union_right.2 ⟨h01, h02⟩
  have d1 : Disjoint S₁ (S₀ ∪ S₂) := Finset.disjoint_union_right.2 ⟨h01.symm, h12⟩
  have d2 : Disjoint S₂ (S₀ ∪ S₁) := Finset.disjoint_union_right.2 ⟨h02.symm, h12.symm⟩
  have u0 : S₀ ∪ (S₁ ∪ S₂) = S₀ ∪ S₁ ∪ S₂ := (Finset.union_assoc _ _ _).symm
  have u1 : S₁ ∪ (S₀ ∪ S₂) ⊆ S₀ ∪ S₁ ∪ S₂ := by
    intro x; simp only [Finset.mem_union]; tauto
  have u2 : S₂ ∪ (S₀ ∪ S₁) ⊆ S₀ ∪ S₁ ∪ S₂ := by
    intro x; simp only [Finset.mem_union]; tauto
  unfold Geometry.det3
  refine ((DegLe.sub ?_ ?_).add ?_)
  · exact u0 ▸ ha.mul ((m12 hf hj).sub (m21 hg hi)) d0
  · exact (hb.mul ((m02 he hj).sub (m20 hg hh)) d1).mono u1
  · exact (hc.mul ((m01 he hi).sub (m10 hf hh)) d2).mono u2

theorem DegLe.le_one {f : MvPolynomial (Fin n × Fin d) R} {S : Finset (Fin d)} (h : DegLe S f) :
    ∀ m ∈ f.support, ∀ k, m k ≤ 1 := fun m hm k => by
  refine (monomial_le_degreeOf k hm).trans ((h k).trans ?_)
  split_ifs <;> omega

end DegLe

/-! ### The perturbation -/

section Perturb
variable {n d : ℕ}

/-- The perturbation index of coordinate `j` of point `i` (`finProdFinEquiv`, so injective). -/
def sosIdx (k : Fin n × Fin d) : ℕ := k.2 + d * k.1

theorem sosIdx_injective : Function.Injective (sosIdx : Fin n × Fin d → ℕ) := fun _ _ h =>
  finProdFinEquiv.injective (Fin.ext h)

/-- **SoS perturbed point**: coordinate `j` of input point `i` becomes
`x i j + ε^(2^(j + d i))`. Computable. All perturbation exponents are distinct powers of two. -/
def sosPoint (x : Fin n → Fin d → R) (i : Fin n) : Fin d → Poly ℤ R :=
  fun j => Poly.C (x i j) + single ((2 ^ sosIdx (i, j) : ℕ) : ℤ) 1

/-- The symbolic version of `sosPoint`: the perturbation is the variable `X (i, j)`. -/
noncomputable def mvPoint (x : Fin n → Fin d → R) (i : Fin n) :
    Fin d → MvPolynomial (Fin n × Fin d) R :=
  fun j => MvPolynomial.C (x i j) + X (i, j)

theorem sosSubst_mvPoint (x : Fin n → Fin d → R) (i : Fin n) :
    (sosSubst sosIdx : MvPolynomial (Fin n × Fin d) R →ₐ[R] _) ∘ mvPoint x i = sosPoint x i := by
  funext j
  simp [mvPoint, sosPoint, sosSubst, Poly.algebraMap_apply]

theorem degLe_mvPoint [Nontrivial R] (x : Fin n → Fin d → R) (i : Fin n) (j : Fin d) :
    DegLe {j} (mvPoint x i j) := degLe_C_add_X _ _ _

theorem degLe_mvPoint_sub [Nontrivial R] (x : Fin n → Fin d → R) (i i' : Fin n) (j : Fin d) :
    DegLe {j} (mvPoint x i j - mvPoint x i' j) :=
  (degLe_mvPoint x i j).sub (degLe_mvPoint x i' j)

/-- Evaluating the symbolic point at `v = t - x` gives the point `t`. -/
theorem eval_mvPoint (x t : Fin n → Fin d → R) (i : Fin n) :
    (MvPolynomial.eval fun k : Fin n × Fin d => t k.1 k.2 - x k.1 k.2) ∘ mvPoint x i = t i := by
  funext j; simp [mvPoint]

end Perturb

/-! ### `orient2d` -/

section Orient2d
variable {n : ℕ}

/-- SoS-perturbed `orient2d` of input points `i, k, l`. Computable. -/
def orient2dSoS (x : Fin n → Fin 2 → R) (i k l : Fin n) : Poly ℤ R :=
  orient2d (sosPoint x i) (sosPoint x k) (sosPoint x l)

/-- **SoS nonvanishing.** For any input coordinates, even degenerate (collinear or coincident
points), the perturbed `orient2d` is nonzero as soon as the three point indices are distinct. -/
theorem orient2dSoS_ne_zero [Nontrivial R] (x : Fin n → Fin 2 → R) {i k l : Fin n}
    (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) : orient2dSoS x i k l ≠ 0 := by
  set D := orient2d (mvPoint x i) (mvPoint x k) (mvPoint x l) with hD
  have hsub : sosSubst sosIdx D = orient2dSoS x i k l := by
    rw [hD, map_orient2d, sosSubst_mvPoint, sosSubst_mvPoint, sosSubst_mvPoint]; rfl
  rw [← hsub]
  refine sosSubst_ne_zero sosIdx_injective ?_ ?_
  · -- evaluate at the point making the perturbed points `(1,0), (0,1), (0,0)`
    intro h0
    let t : Fin n → Fin 2 → R := fun a j =>
      if a = i ∧ j = 0 then 1 else if a = k ∧ j = 1 then 1 else 0
    have := congrArg (MvPolynomial.eval fun q : Fin n × Fin 2 => t q.1 q.2 - x q.1 q.2) h0
    rw [hD, map_orient2d, eval_mvPoint, eval_mvPoint, eval_mvPoint, map_zero] at this
    simp [orient2d, t, hik, hik.symm, hil.symm, hkl.symm] at this
  · have h := ((degLe_mvPoint_sub x i l 0).mul (degLe_mvPoint_sub x k l 1) (by decide)).sub
      (((degLe_mvPoint_sub x i l 1).mul (degLe_mvPoint_sub x k l 0) (by decide)).mono
        (by decide))
    exact DegLe.le_one h

end Orient2d

/-! ### `orient3d` -/

section Orient3d
variable {n : ℕ}

/-- SoS-perturbed `orient3d` of input points `i, k, l, m`. Computable. -/
def orient3dSoS (x : Fin n → Fin 3 → R) (i k l m : Fin n) : Poly ℤ R :=
  orient3d (sosPoint x i) (sosPoint x k) (sosPoint x l) (sosPoint x m)

/-- **SoS nonvanishing for `orient3d`**: nonzero for any input as soon as the four point indices
are pairwise distinct. -/
theorem orient3dSoS_ne_zero [Nontrivial R] (x : Fin n → Fin 3 → R) {i k l m : Fin n}
    (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    orient3dSoS x i k l m ≠ 0 := by
  set D := orient3d (mvPoint x i) (mvPoint x k) (mvPoint x l) (mvPoint x m) with hD
  have hsub : sosSubst sosIdx D = orient3dSoS x i k l m := by
    rw [hD, map_orient3d, sosSubst_mvPoint, sosSubst_mvPoint, sosSubst_mvPoint,
      sosSubst_mvPoint]; rfl
  rw [← hsub]
  refine sosSubst_ne_zero sosIdx_injective ?_ ?_
  · -- evaluate at the point making the perturbed points `e₀, e₁, e₂, 0`
    intro h0
    let t : Fin n → Fin 3 → R := fun a j =>
      if a = i ∧ j = 0 then 1 else if a = k ∧ j = 1 then 1 else if a = l ∧ j = 2 then 1 else 0
    have := congrArg (MvPolynomial.eval fun q : Fin n × Fin 3 => t q.1 q.2 - x q.1 q.2) h0
    rw [hD, map_orient3d, eval_mvPoint, eval_mvPoint, eval_mvPoint, eval_mvPoint,
      map_zero] at this
    simp [orient3d, det3, t, hik, hil, hkl, hik.symm, hil.symm, him.symm,
      hkl.symm, hkm.symm, hlm.symm] at this
  · have h := DegLe.det3 (S₀ := {0}) (S₁ := {1}) (S₂ := {2}) (by decide) (by decide) (by decide)
      (degLe_mvPoint_sub x i m 0) (degLe_mvPoint_sub x i m 1) (degLe_mvPoint_sub x i m 2)
      (degLe_mvPoint_sub x k m 0) (degLe_mvPoint_sub x k m 1) (degLe_mvPoint_sub x k m 2)
      (degLe_mvPoint_sub x l m 0) (degLe_mvPoint_sub x l m 1) (degLe_mvPoint_sub x l m 2)
    exact DegLe.le_one h

end Orient3d

/-! ### Sign agreement with the unperturbed predicate

The perturbed value is a finite element whose standard part is the unperturbed value
(naturality of the predicates along `stdPart`). So when the unperturbed value is nonzero it is
the leading coefficient, and the signs agree. -/

section StdPart
variable {n d : ℕ}

/-- The sign of an element of an ordered ring, with the same shape as `Poly.sign`. -/
def signOf [Zero R] [LinearOrder R] (r : R) : ℤ := if 0 < r then 1 else if r < 0 then -1 else 0

theorem sign_eq_signOf_leadCoeff [LinearOrder R] (p : Poly ℤ R) :
    p.sign = signOf p.leadCoeff := rfl

theorem signOf_int (r : ℤ) : signOf r = r.sign := by
  unfold signOf
  rcases lt_trichotomy r 0 with h | rfl | h
  · simp [h, h.not_gt, Int.sign_eq_neg_one_of_neg h]
  · simp
  · simp [h, Int.sign_eq_one_of_pos h]

theorem isFinite_sosPoint (x : Fin n → Fin d → R) (i : Fin n) (j : Fin d) :
    (sosPoint x i j).IsFinite := by
  refine (isFinite_C _).add ?_
  unfold IsFinite
  by_cases h : (1 : R) = 0
  · simp [single, h]
  · rw [leadExp_single h]; exact WithTop.coe_le_coe.2 (by positivity)

theorem std_sosPoint (x : Fin n → Fin d → R) (i : Fin n) (j : Fin d) :
    (sosPoint x i j).std = x i j := by
  simp only [sosPoint, std]
  simp only [Poly.coeff_add, Poly.coeff_C, Poly.coeff_single, ite_true]
  rw [ite_eq_right (by positivity : (0 : ℤ) < _).ne, add_zero]

/-- The perturbed point as a point of the finite subring. -/
def sosPointFin (x : Fin n → Fin d → R) (i : Fin n) : Fin d → (finiteSubring : Subring (Poly ℤ R)) :=
  fun j => ⟨sosPoint x i j, isFinite_sosPoint x i j⟩

theorem stdPart_sosPointFin (x : Fin n → Fin d → R) (i : Fin n) :
    stdPart ∘ sosPointFin x i = x i := by
  funext j; exact std_sosPoint x i j

theorem subtype_sosPointFin (x : Fin n → Fin d → R) (i : Fin n) :
    (finiteSubring : Subring (Poly ℤ R)).subtype ∘ sosPointFin x i = sosPoint x i := rfl

/-- A finite element with nonzero standard part has that standard part as leading coefficient. -/
theorem sign_of_isFinite_of_std_ne_zero [LinearOrder R] {p : Poly ℤ R} (hp : p.IsFinite)
    (h : p.std ≠ 0) : p.sign = signOf p.std := by
  have hle : p.leadExp = ((0 : ℤ) : WithTop ℤ) := by
    refine le_antisymm ?_ hp
    by_contra hlt
    exact h (coeff_eq_zero_of_lt_leadExp (lt_of_not_ge hlt))
  rw [sign_eq_signOf_leadCoeff, std, coeff_leadExp hle]

theorem orient2dSoS_isFinite (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    (orient2dSoS x i k l).IsFinite := by
  have := (orient2d (sosPointFin x i) (sosPointFin x k) (sosPointFin x l)).2
  rwa [← Subring.coe_subtype, map_orient2d, subtype_sosPointFin, subtype_sosPointFin,
    subtype_sosPointFin] at this

/-- The standard part of the perturbed `orient2d` is the unperturbed `orient2d`. -/
theorem orient2dSoS_std (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    (orient2dSoS x i k l).std = orient2d (x i) (x k) (x l) := by
  have h := map_orient2d stdPart (sosPointFin x i) (sosPointFin x k) (sosPointFin x l)
  rw [stdPart_sosPointFin, stdPart_sosPointFin, stdPart_sosPointFin, stdPart_apply] at h
  rw [← h]
  have := map_orient2d (finiteSubring : Subring (Poly ℤ R)).subtype
    (sosPointFin x i) (sosPointFin x k) (sosPointFin x l)
  rw [subtype_sosPointFin, subtype_sosPointFin, subtype_sosPointFin] at this
  rw [orient2dSoS, ← this]; rfl

/-- **SoS agrees with the exact predicate on nondegenerate input.** -/
theorem orient2dSoS_sign [LinearOrder R] (x : Fin n → Fin 2 → R) (i k l : Fin n)
    (h : orient2d (x i) (x k) (x l) ≠ 0) :
    (orient2dSoS x i k l).sign = signOf (orient2d (x i) (x k) (x l)) := by
  rw [← orient2dSoS_std] at h ⊢
  exact sign_of_isFinite_of_std_ne_zero (orient2dSoS_isFinite x i k l) h

theorem orient3dSoS_isFinite (x : Fin n → Fin 3 → R) (i k l m : Fin n) :
    (orient3dSoS x i k l m).IsFinite := by
  have := (orient3d (sosPointFin x i) (sosPointFin x k) (sosPointFin x l) (sosPointFin x m)).2
  rwa [← Subring.coe_subtype, map_orient3d, subtype_sosPointFin, subtype_sosPointFin,
    subtype_sosPointFin, subtype_sosPointFin] at this

theorem orient3dSoS_std (x : Fin n → Fin 3 → R) (i k l m : Fin n) :
    (orient3dSoS x i k l m).std = orient3d (x i) (x k) (x l) (x m) := by
  have h := map_orient3d stdPart (sosPointFin x i) (sosPointFin x k) (sosPointFin x l)
    (sosPointFin x m)
  rw [stdPart_sosPointFin, stdPart_sosPointFin, stdPart_sosPointFin, stdPart_sosPointFin,
    stdPart_apply] at h
  rw [← h]
  have := map_orient3d (finiteSubring : Subring (Poly ℤ R)).subtype
    (sosPointFin x i) (sosPointFin x k) (sosPointFin x l) (sosPointFin x m)
  rw [subtype_sosPointFin, subtype_sosPointFin, subtype_sosPointFin, subtype_sosPointFin] at this
  rw [orient3dSoS, ← this]; rfl

theorem orient3dSoS_sign [LinearOrder R] (x : Fin n → Fin 3 → R) (i k l m : Fin n)
    (h : orient3d (x i) (x k) (x l) (x m) ≠ 0) :
    (orient3dSoS x i k l m).sign = signOf (orient3d (x i) (x k) (x l) (x m)) := by
  rw [← orient3dSoS_std] at h ⊢
  exact sign_of_isFinite_of_std_ne_zero (orient3dSoS_isFinite x i k l m) h

end StdPart

/-! ### Consistency under relabeling -/

section Swap
variable {n : ℕ}

theorem orient2dSoS_swap₁₂ (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    orient2dSoS x k i l = -orient2dSoS x i k l := orient2d_swap₁₂ _ _ _

theorem orient2dSoS_swap₂₃ (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    orient2dSoS x i l k = -orient2dSoS x i k l := orient2d_swap₂₃ _ _ _

theorem orient3dSoS_swap₁₂ (x : Fin n → Fin 3 → R) (i k l m : Fin n) :
    orient3dSoS x k i l m = -orient3dSoS x i k l m := orient3d_swap₁₂ _ _ _ _

theorem sign_neg [LinearOrder R] [IsStrictOrderedRing R] (p : Poly ℤ R) :
    (-p).sign = -p.sign := by
  rw [sign_eq_signOf_leadCoeff, sign_eq_signOf_leadCoeff, leadCoeff_eq_leadingCoeff,
    leadCoeff_eq_leadingCoeff, map_neg, HahnSeries.leadingCoeff_neg]
  generalize (toHahn p).leadingCoeff = c
  unfold signOf
  rcases lt_trichotomy c 0 with h | rfl | h
  · simp [h.not_gt, neg_pos.2 h, h]
  · simp
  · simp [h, h.not_gt]

/-- Swapping two input points flips the SoS sign. -/
theorem orient2dSoS_sign_swap₁₂ [LinearOrder R] [IsStrictOrderedRing R]
    (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    (orient2dSoS x k i l).sign = -(orient2dSoS x i k l).sign := by
  rw [orient2dSoS_swap₁₂, sign_neg]

/-- The SoS sign is never `0` for distinct indices. -/
theorem orient2dSoS_sign_ne_zero [LinearOrder R] [IsStrictOrderedRing R]
    (x : Fin n → Fin 2 → R) {i k l : Fin n} (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) :
    (orient2dSoS x i k l).sign ≠ 0 := fun h =>
  orient2dSoS_ne_zero x hik hil hkl ((sign_eq_zero_iff _).1 h)

theorem orient3dSoS_sign_ne_zero [LinearOrder R] [IsStrictOrderedRing R]
    (x : Fin n → Fin 3 → R) {i k l m : Fin n} (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    (orient3dSoS x i k l m).sign ≠ 0 := fun h =>
  orient3dSoS_ne_zero x hik hil him hkl hkm hlm ((sign_eq_zero_iff _).1 h)

end Swap

end LeviCivita.Geometry
