/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Geometry.SoS
import LeviCivita.Poly.MultiEps

/-!
# Simulation of Simplicity with independent infinitesimals

M3's SoS (`LeviCivita.Geometry.SoS`) perturbs coordinate `j` of point `i` by `ε^(b^(j + d i))`,
a power of one infinitesimal. Here every coordinate gets its **own** infinitesimal: coordinate
`(i, j)` is perturbed by `epsI (idx (i, j))` in `Γ = MultiEps (n * d)`, where
`idx = finProdFinEquiv` (so `idx (i, j) = j + d i`). The exponent of a perturbation is the basis
vector `FinLex.single (idx (i, j)) 1`.

The proof of nonvanishing is M3's, with a simpler key lemma: the exponent of a monomial
`∏ X_k ^ m_k` is the vector `∑ m_k • e_{w k}` (`multiExpo`). That vector *is* `m`, read through
`w`, so the map from monomials to exponents is injective for **every** degree
(`multiExpo_injective`). The base-`b` digit argument and the degree bounds (`DegLe`/`DegBd`,
`b ≥ 4`) disappear:

* `multiSubst_ne_zero`: a nonzero polynomial stays nonzero under `X k ↦ ε_{w k}` for injective
  `w`. There is no degree hypothesis.
* `orient2dSoSMulti_ne_zero`, `orient3dSoSMulti_ne_zero`, `incircleSoSMulti_ne_zero`,
  `insphereSoSMulti_ne_zero`: nonzero for any input and pairwise distinct indices. The lifted
  predicates still need `(2 : R) ≠ 0`, from the evaluation certificate (M3 note 4).
* `orient2dSoSMulti_sign`, …: on nondegenerate input the SoS sign is the exact sign.

The order of the infinitesimals: `epsI a < epsI b` for `a < b`
(`LeviCivita.Poly.epsI_lt_epsI`). So the perturbation of point `0`, coordinate `0`, is the
*smallest*. M3 makes it the largest: `ε^(b^0)` is the biggest of its perturbations. Both are
valid SoS schemes. They are different schemes and can choose different signs on degenerate
input (see `NOTES-M5.md`).
-/

set_option linter.unusedSectionVars false

namespace LeviCivita.Geometry

open Poly MvPolynomial

variable {R : Type*} [CommRing R] [DecidableEq R]

section Key
variable {σ : Type*} {N : ℕ}

/-- The multi-ε substitution: variable `k` ↦ `ε_{w k}`. -/
noncomputable def multiSubst (w : σ → Fin N) : MvPolynomial σ R →ₐ[R] Poly (MultiEps N) R :=
  aeval fun k => epsI (w k)

/-- The exponent of the monomial `m` under `multiSubst w`: `∑ₖ mₖ • e_{w k}`. -/
def multiExpo (w : σ → Fin N) (m : σ →₀ ℕ) : MultiEps N :=
  ∑ i ∈ m.support, m i • FinLex.single (w i) 1

theorem prod_single_pow_gen {Γ : Type*} [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ] (s : Finset σ) (a : σ → Γ) (d : σ → ℕ) :
    ∏ i ∈ s, (HahnSeries.single (a i) (1 : R) : HahnSeries Γ R) ^ d i =
      HahnSeries.single (∑ i ∈ s, d i • a i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, HahnSeries.single_pow,
      HahnSeries.single_mul_single, one_pow, one_mul]

theorem toHahn_multiSubst (w : σ → Fin N) (D : MvPolynomial σ R) :
    toHahn (multiSubst w D) =
      ∑ m ∈ D.support, HahnSeries.single (multiExpo w m) (D.coeff m) := by
  have h1 : toHahn (multiSubst w D) = toHahnAlg (multiSubst w D) := rfl
  rw [h1, multiSubst, ← AlgHom.comp_apply, comp_aeval, aeval_def, eval₂_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [epsI, toHahnAlg_apply, toHahn_single]
  rw [prod_single_pow_gen, ← HahnSeries.C_eq_algebraMap, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one]
  rfl

/-- Reading coordinate `w k` of the exponent recovers the degree of `X k`. -/
theorem multiExpo_apply {w : σ → Fin N} (hw : Function.Injective w) (m : σ →₀ ℕ) (k : σ) :
    multiExpo w m (w k) = m k := by
  classical
  have : multiExpo w m (w k) = ∑ i ∈ m.support, (m i : ℤ) * (if w k = w i then 1 else 0) := by
    rw [multiExpo, ← FinLex.evalAddMonoidHom_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Pi.single_apply]
  rw [this, Finset.sum_eq_single k]
  · simp
  · intro i _ hik; simp [hw.ne (Ne.symm hik)]
  · intro hk; simp [Finsupp.notMem_support_iff.1 hk]

/-- **Distinct monomials have distinct exponents**, for any degrees. -/
theorem multiExpo_injective {w : σ → Fin N} (hw : Function.Injective w) :
    Function.Injective (multiExpo w) := fun m m' h => by
  ext k
  have := congrArg (fun e : MultiEps N => e (w k)) h
  simp only [multiExpo_apply hw] at this
  exact_mod_cast this

/-- **Key lemma (independent infinitesimals).** A nonzero polynomial stays nonzero under
`X k ↦ ε_{w k}` for injective `w`. Unlike `sosSubst_ne_zero`, there is no degree hypothesis. -/
theorem multiSubst_ne_zero {w : σ → Fin N} (hw : Function.Injective w)
    {D : MvPolynomial σ R} (hD : D ≠ 0) : multiSubst w D ≠ 0 := by
  obtain ⟨m₀, hm₀⟩ := MvPolynomial.ne_zero_iff.1 hD
  have hmem : m₀ ∈ D.support := MvPolynomial.mem_support_iff.2 hm₀
  intro h
  have := congrArg (fun p => (toHahn p).coeff (multiExpo w m₀)) h
  simp only [toHahn_multiSubst, HahnSeries.coeff_sum, HahnSeries.coeff_single, map_zero,
    HahnSeries.coeff_zero] at this
  rw [Finset.sum_eq_single m₀ (fun m _ hne => ?_) (fun h => absurd hmem h), ite_eq_left rfl]
    at this
  · exact hm₀ this
  · rw [ite_eq_right]
    intro he
    exact hne (multiExpo_injective hw he.symm)

end Key

/-! ### The perturbation -/

section Perturb
variable {n d : ℕ}

/-- **Multi-ε SoS perturbed point**: coordinate `j` of point `i` becomes
`x i j + ε_{j + d i}`. Computable. -/
def multiPoint (x : Fin n → Fin d → R) (i : Fin n) : Fin d → Poly (MultiEps (n * d)) R :=
  fun j => Poly.C (x i j) + epsI (finProdFinEquiv (i, j))

theorem multiSubst_mvPoint (x : Fin n → Fin d → R) (i : Fin n) :
    (multiSubst finProdFinEquiv : MvPolynomial (Fin n × Fin d) R →ₐ[R] _) ∘ mvPoint x i =
      multiPoint x i := by
  funext j
  simp [mvPoint, multiPoint, multiSubst, Poly.algebraMap_apply]

end Perturb

/-! ### Nonvanishing -/

section NeZero
variable [Nontrivial R] {n : ℕ}

/-- Multi-ε SoS `orient2d`. Computable. -/
def orient2dSoSMulti (x : Fin n → Fin 2 → R) (i k l : Fin n) : Poly (MultiEps (n * 2)) R :=
  orient2d (multiPoint x i) (multiPoint x k) (multiPoint x l)

/-- Multi-ε SoS `orient3d`. Computable. -/
def orient3dSoSMulti (x : Fin n → Fin 3 → R) (i k l m : Fin n) : Poly (MultiEps (n * 3)) R :=
  orient3d (multiPoint x i) (multiPoint x k) (multiPoint x l) (multiPoint x m)

/-- Multi-ε SoS `incircle`. Computable. -/
def incircleSoSMulti (x : Fin n → Fin 2 → R) (i k l m : Fin n) : Poly (MultiEps (n * 2)) R :=
  incircle (multiPoint x i) (multiPoint x k) (multiPoint x l) (multiPoint x m)

/-- Multi-ε SoS `insphere`. Computable. -/
def insphereSoSMulti (x : Fin n → Fin 3 → R) (i k l m o : Fin n) :
    Poly (MultiEps (n * 3)) R :=
  insphere (multiPoint x i) (multiPoint x k) (multiPoint x l) (multiPoint x m) (multiPoint x o)

/-- **Multi-ε SoS nonvanishing for `orient2d`**: any input, distinct indices. -/
theorem orient2dSoSMulti_ne_zero (x : Fin n → Fin 2 → R) {i k l : Fin n}
    (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) : orient2dSoSMulti x i k l ≠ 0 := by
  set D := orient2d (mvPoint x i) (mvPoint x k) (mvPoint x l) with hD
  have hsub : multiSubst finProdFinEquiv D = orient2dSoSMulti x i k l := by
    rw [hD, map_orient2d, multiSubst_mvPoint, multiSubst_mvPoint, multiSubst_mvPoint]; rfl
  rw [← hsub]
  refine multiSubst_ne_zero finProdFinEquiv.injective fun h0 => ?_
  let t : Fin n → Fin 2 → R := fun a j =>
    if a = i ∧ j = 0 then 1 else if a = k ∧ j = 1 then 1 else 0
  have := congrArg (MvPolynomial.eval fun q : Fin n × Fin 2 => t q.1 q.2 - x q.1 q.2) h0
  rw [hD, map_orient2d, eval_mvPoint, eval_mvPoint, eval_mvPoint, map_zero] at this
  simp [orient2d, t, hik, hik.symm, hil.symm, hkl.symm] at this

/-- **Multi-ε SoS nonvanishing for `orient3d`**. -/
theorem orient3dSoSMulti_ne_zero (x : Fin n → Fin 3 → R) {i k l m : Fin n}
    (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    orient3dSoSMulti x i k l m ≠ 0 := by
  set D := orient3d (mvPoint x i) (mvPoint x k) (mvPoint x l) (mvPoint x m) with hD
  have hsub : multiSubst finProdFinEquiv D = orient3dSoSMulti x i k l m := by
    rw [hD, map_orient3d, multiSubst_mvPoint, multiSubst_mvPoint, multiSubst_mvPoint,
      multiSubst_mvPoint]; rfl
  rw [← hsub]
  refine multiSubst_ne_zero finProdFinEquiv.injective fun h0 => ?_
  let t : Fin n → Fin 3 → R := fun a j =>
    if a = i ∧ j = 0 then 1 else if a = k ∧ j = 1 then 1 else if a = l ∧ j = 2 then 1 else 0
  have := congrArg (MvPolynomial.eval fun q : Fin n × Fin 3 => t q.1 q.2 - x q.1 q.2) h0
  rw [hD, map_orient3d, eval_mvPoint, eval_mvPoint, eval_mvPoint, eval_mvPoint,
    map_zero] at this
  simp [orient3d, det3, t, hik, hil, hkl, hik.symm, hil.symm, him.symm,
    hkl.symm, hkm.symm, hlm.symm] at this

/-- **Multi-ε SoS nonvanishing for `incircle`** (`(2 : R) ≠ 0`; no condition on degrees). -/
theorem incircleSoSMulti_ne_zero (h2 : (2 : R) ≠ 0) (x : Fin n → Fin 2 → R) {i k l m : Fin n}
    (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    incircleSoSMulti x i k l m ≠ 0 := by
  set D := incircle (mvPoint x i) (mvPoint x k) (mvPoint x l) (mvPoint x m) with hD
  have hsub : multiSubst finProdFinEquiv D = incircleSoSMulti x i k l m := by
    rw [hD, map_incircle, multiSubst_mvPoint, multiSubst_mvPoint, multiSubst_mvPoint,
      multiSubst_mvPoint]; rfl
  rw [← hsub]
  refine multiSubst_ne_zero finProdFinEquiv.injective fun h0 => ?_
  let t : Fin n → Fin 2 → R := fun a j =>
    if a = i ∧ j = 0 then 1 else if a = k ∧ j = 1 then 1 else if a = l ∧ j = 0 then -1 else 0
  have := congrArg (MvPolynomial.eval fun q : Fin n × Fin 2 => t q.1 q.2 - x q.1 q.2) h0
  rw [hD, map_incircle, eval_mvPoint, eval_mvPoint, eval_mvPoint, eval_mvPoint,
    map_zero] at this
  simp [incircle, det3, t, hik, hil, hkl, hik.symm, hil.symm, him.symm, hkl.symm, hkm.symm,
    hlm.symm] at this
  exact h2 (by rw [← one_add_one_eq_two]; exact this)

/-- **Multi-ε SoS nonvanishing for `insphere`** (`(2 : R) ≠ 0`). -/
theorem insphereSoSMulti_ne_zero (h2 : (2 : R) ≠ 0) (x : Fin n → Fin 3 → R) {i k l m o : Fin n}
    (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hio : i ≠ o) (hkl : k ≠ l) (hkm : k ≠ m)
    (hko : k ≠ o) (hlm : l ≠ m) (hlo : l ≠ o) (hmo : m ≠ o) :
    insphereSoSMulti x i k l m o ≠ 0 := by
  set D := insphere (mvPoint x i) (mvPoint x k) (mvPoint x l) (mvPoint x m) (mvPoint x o)
    with hD
  have hsub : multiSubst finProdFinEquiv D = insphereSoSMulti x i k l m o := by
    rw [hD, map_insphere, multiSubst_mvPoint, multiSubst_mvPoint, multiSubst_mvPoint,
      multiSubst_mvPoint, multiSubst_mvPoint]; rfl
  rw [← hsub]
  refine multiSubst_ne_zero finProdFinEquiv.injective fun h0 => ?_
  let t : Fin n → Fin 3 → R := fun a j =>
    if a = i ∧ j = 0 then 1 else if a = k ∧ j = 1 then 1 else if a = l ∧ j = 2 then 1
    else if a = m ∧ j = 0 then -1 else 0
  have := congrArg (MvPolynomial.eval fun q : Fin n × Fin 3 => t q.1 q.2 - x q.1 q.2) h0
  rw [hD, map_insphere, eval_mvPoint, eval_mvPoint, eval_mvPoint, eval_mvPoint, eval_mvPoint,
    map_zero] at this
  simp [insphere, det4, det3, t, hik, hil, him, hkl, hkm, hlm, hik.symm, hil.symm, him.symm,
    hio.symm, hkl.symm, hkm.symm, hko.symm, hlm.symm, hlo.symm, hmo.symm] at this
  exact h2 (by rw [← one_add_one_eq_two]; exact this)

end NeZero

/-! ### Sign agreement with the unperturbed predicate -/

section StdPart
variable {n d : ℕ}

theorem isFinite_multiPoint (x : Fin n → Fin d → R) (i : Fin n) (j : Fin d) :
    (multiPoint x i j).IsFinite := by
  refine (isFinite_C _).add ?_
  unfold IsFinite
  by_cases h : (1 : R) = 0
  · simp [epsI, single, h]
  · rw [epsI, leadExp_single h]
    exact WithTop.coe_le_coe.2 (FinLex.single_pos _ one_pos).le

theorem std_multiPoint (x : Fin n → Fin d → R) (i : Fin n) (j : Fin d) :
    (multiPoint x i j).std = x i j := by
  simp only [multiPoint, std, epsI, Poly.coeff_add, Poly.coeff_C, Poly.coeff_single, ite_true]
  rw [ite_eq_right (FinLex.single_pos _ (one_pos : (0 : ℤ) < 1)).ne, add_zero]

/-- The perturbed point as a point of the finite subring. -/
def multiPointFin (x : Fin n → Fin d → R) (i : Fin n) :
    Fin d → (finiteSubring : Subring (Poly (MultiEps (n * d)) R)) :=
  fun j => ⟨multiPoint x i j, isFinite_multiPoint x i j⟩

theorem stdPart_multiPointFin (x : Fin n → Fin d → R) (i : Fin n) :
    stdPart ∘ multiPointFin x i = x i := by
  funext j; exact std_multiPoint x i j

theorem subtype_multiPointFin (x : Fin n → Fin d → R) (i : Fin n) :
    (finiteSubring : Subring (Poly (MultiEps (n * d)) R)).subtype ∘ multiPointFin x i =
      multiPoint x i := rfl

theorem orient2dSoSMulti_isFinite (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    (orient2dSoSMulti x i k l).IsFinite := by
  have := (orient2d (multiPointFin x i) (multiPointFin x k) (multiPointFin x l)).2
  rwa [← Subring.coe_subtype, map_orient2d, subtype_multiPointFin, subtype_multiPointFin,
    subtype_multiPointFin] at this

/-- The standard part of the multi-ε SoS `orient2d` is the unperturbed `orient2d`. -/
theorem orient2dSoSMulti_std (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    (orient2dSoSMulti x i k l).std = orient2d (x i) (x k) (x l) := by
  have h := map_orient2d stdPart (multiPointFin x i) (multiPointFin x k) (multiPointFin x l)
  rw [stdPart_multiPointFin, stdPart_multiPointFin, stdPart_multiPointFin, stdPart_apply] at h
  rw [← h]
  have := map_orient2d (finiteSubring : Subring (Poly (MultiEps (n * 2)) R)).subtype
    (multiPointFin x i) (multiPointFin x k) (multiPointFin x l)
  rw [subtype_multiPointFin, subtype_multiPointFin, subtype_multiPointFin] at this
  rw [orient2dSoSMulti, ← this]; rfl

/-- **Multi-ε SoS agrees with the exact `orient2d` on nondegenerate input.** -/
theorem orient2dSoSMulti_sign [LinearOrder R] (x : Fin n → Fin 2 → R) (i k l : Fin n)
    (h : orient2d (x i) (x k) (x l) ≠ 0) :
    (orient2dSoSMulti x i k l).sign = signOf (orient2d (x i) (x k) (x l)) := by
  rw [← orient2dSoSMulti_std] at h ⊢
  exact sign_of_isFinite_of_std_ne_zero (orient2dSoSMulti_isFinite x i k l) h

theorem incircleSoSMulti_isFinite (x : Fin n → Fin 2 → R) (i k l m : Fin n) :
    (incircleSoSMulti x i k l m).IsFinite := by
  have := (incircle (multiPointFin x i) (multiPointFin x k) (multiPointFin x l)
    (multiPointFin x m)).2
  rwa [← Subring.coe_subtype, map_incircle, subtype_multiPointFin, subtype_multiPointFin,
    subtype_multiPointFin, subtype_multiPointFin] at this

theorem incircleSoSMulti_std (x : Fin n → Fin 2 → R) (i k l m : Fin n) :
    (incircleSoSMulti x i k l m).std = incircle (x i) (x k) (x l) (x m) := by
  have h := map_incircle stdPart (multiPointFin x i) (multiPointFin x k) (multiPointFin x l)
    (multiPointFin x m)
  rw [stdPart_multiPointFin, stdPart_multiPointFin, stdPart_multiPointFin,
    stdPart_multiPointFin, stdPart_apply] at h
  rw [← h]
  have := map_incircle (finiteSubring : Subring (Poly (MultiEps (n * 2)) R)).subtype
    (multiPointFin x i) (multiPointFin x k) (multiPointFin x l) (multiPointFin x m)
  rw [subtype_multiPointFin, subtype_multiPointFin, subtype_multiPointFin,
    subtype_multiPointFin] at this
  rw [incircleSoSMulti, ← this]; rfl

/-- **Multi-ε SoS agrees with the exact `incircle` on nondegenerate input.** -/
theorem incircleSoSMulti_sign [LinearOrder R] (x : Fin n → Fin 2 → R) (i k l m : Fin n)
    (h : incircle (x i) (x k) (x l) (x m) ≠ 0) :
    (incircleSoSMulti x i k l m).sign = signOf (incircle (x i) (x k) (x l) (x m)) := by
  rw [← incircleSoSMulti_std] at h ⊢
  exact sign_of_isFinite_of_std_ne_zero (incircleSoSMulti_isFinite x i k l m) h

end StdPart

/-! ### Relabeling -/

section Swap
variable {n : ℕ}

theorem orient2dSoSMulti_swap₁₂ (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    orient2dSoSMulti x k i l = -orient2dSoSMulti x i k l := orient2d_swap₁₂ _ _ _

/-- The multi-ε SoS sign of `orient2d` is never `0` for distinct indices. -/
theorem orient2dSoSMulti_sign_ne_zero [LinearOrder R] [IsStrictOrderedRing R]
    (x : Fin n → Fin 2 → R) {i k l : Fin n} (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) :
    (orient2dSoSMulti x i k l).sign ≠ 0 := fun h =>
  orient2dSoSMulti_ne_zero x hik hil hkl ((sign_eq_zero_iff _).1 h)

end Swap

end LeviCivita.Geometry
