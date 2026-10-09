/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Geometry.Predicates
import LeviCivita.Poly.Std
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Combinatorics.Colex
import Mathlib.Tactic.Ring


/-!
# Simulation of Simplicity (SoS) over `Poly ℤ R`

Coordinate `j` of input point `i` is perturbed to `x i j + ε^(b^(j + d·i))` (`sosPoint`). A
predicate evaluated on perturbed points (`orient2dSoS`, `orient3dSoS`, `incircleSoS`,
`insphereSoS`) is an exact, computable element of `Poly ℤ R`.

Main results (any nontrivial commutative ring `R`, any input, even fully degenerate):

* `orient2dSoS_ne_zero`, `orient3dSoS_ne_zero` (`b ≥ 2`), `incircleSoS_ne_zero`,
  `insphereSoS_ne_zero` (`b ≥ 4`, `(2 : R) ≠ 0`): the perturbed value is never `0` when the
  point indices are pairwise distinct;
* `orient2dSoS_sign` etc.: when the unperturbed value is nonzero, the perturbed sign is its sign
  (the standard part of the perturbed value is the unperturbed value);
* `orient2dSoS_swap₁₂` etc.: relabeling acts by the sign of the permutation.

Proof of nonvanishing. Replace each perturbation by a variable: `D ∈ MvPolynomial (Fin n × Fin d) R`
is the predicate on points `C (x i j) + X (i, j)`, and the perturbed value is the image of `D`
under `X k ↦ ε^(b^(w k))` (`sosSubst`, by naturality `map_orient2d`).
1. `D ≠ 0`: evaluating at `X (i, j) := t i j - x i j` gives the predicate at chosen points `t`
   (e.g. `(1,0), (0,1), (0,0)`), which is `1` (or `2` for the lifted predicates).
2. Every variable has degree `< b` in `D` (`DegLe`/`DegBd`: the matrix columns involve
   disjoint coordinates, so the determinant is multilinear in them, plus `2` for a lifted column).
3. `sosSubst_ne_zero`: monomials with exponents `< b` go to distinct powers of `ε` (base-`b`
   digits, `digit_extract`), so the coefficient of `D` at any monomial survives.

`b = 4` is a single perturbation that works for all four predicates.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita.Geometry

open Poly MvPolynomial

variable {R : Type*} [CommRing R] [DecidableEq R]

section Digits

/-! ### Base-`b` digits

A finite sum `∑ dᵢ bʷ⁽ⁱ⁾` with digits `dᵢ < b` and distinct positions `w i` determines the
digits (`digit_extract`). -/

theorem digit_sum_lt {ι : Type*} {b : ℕ} (hb : 0 < b) (w : ι → ℕ) (d : ι → ℕ) :
    ∀ (W : ℕ) (T : Finset ι), Set.InjOn w T → (∀ i ∈ T, w i < W) → (∀ i ∈ T, d i < b) →
      ∑ i ∈ T, d i * b ^ w i < b ^ W := by
  classical
  intro W
  induction W with
  | zero =>
    intro T _ hW _
    rcases T.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · simp
    · exact absurd (hW i hi) (Nat.not_lt_zero _)
  | succ W ih =>
    intro T hinj hW hd
    rw [← Finset.sum_filter_add_sum_filter_not T (fun i => w i < W)]
    have h1 := ih (T.filter fun i => w i < W) (hinj.mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))
      (by simp) (fun i hi => hd i (Finset.mem_of_mem_filter i hi))
    have hc : (T.filter fun i => ¬ w i < W).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [Finset.mem_filter] at hx hy
      exact hinj hx.1 hy.1 (by have := hW x hx.1; have := hW y hy.1; omega)
    have h2 : ∑ i ∈ T.filter (fun i => ¬ w i < W), d i * b ^ w i ≤ (b - 1) * b ^ W := by
      refine (Finset.sum_le_card_nsmul _ _ ((b - 1) * b ^ W) fun i hi => ?_).trans ?_
      · simp only [Finset.mem_filter] at hi
        have hwx : w i = W := by have := hW i hi.1; omega
        rw [hwx]
        exact Nat.mul_le_mul_right _ (by have := hd i hi.1; omega)
      · rw [smul_eq_mul]
        exact (Nat.mul_le_mul_right _ hc).trans (by simp)
    have hbW : 0 < b ^ W := pow_pos hb W
    have : b ^ (W + 1) = b ^ W + (b - 1) * b ^ W := by
      rw [pow_succ]; cases b with
      | zero => omega
      | succ b => simp; ring
    omega

theorem digit_extract {ι : Type*} {b : ℕ} (hb : 0 < b) {w : ι → ℕ} {d : ι → ℕ} {s : Finset ι}
    (hw : Set.InjOn w s) (hd : ∀ i ∈ s, d i < b) {k : ι} (hk : k ∈ s) :
    (∑ i ∈ s, d i * b ^ w i) / b ^ w k % b = d k := by
  classical
  have hsplit : ∑ i ∈ s, d i * b ^ w i = ∑ i ∈ s.filter (fun i => w i < w k), d i * b ^ w i
      + b ^ w k * (d k + b * ((∑ i ∈ s.filter (fun i => w k < w i), d i * b ^ w i) / b ^ (w k + 1))) := by
    have hU : b ^ (w k + 1) ∣ ∑ i ∈ s.filter (fun i => w k < w i), d i * b ^ w i :=
      Finset.dvd_sum fun i hi => Dvd.dvd.mul_left
        (pow_dvd_pow b (by simp only [Finset.mem_filter] at hi; omega)) _
    have hE : s.filter (fun i => ¬ w i < w k) = insert k (s.filter fun i => w k < w i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert, not_lt]
      constructor
      · rintro ⟨hi, hle⟩
        rcases hle.lt_or_eq with hlt | heq
        · exact Or.inr ⟨hi, hlt⟩
        · exact Or.inl (hw hi hk heq.symm)
      · rintro (rfl | ⟨hi, hlt⟩)
        · exact ⟨hk, le_rfl⟩
        · exact ⟨hi, hlt.le⟩
    obtain ⟨Q, hQ⟩ := hU
    rw [← Finset.sum_filter_add_sum_filter_not s (fun i => w i < w k), hE,
      Finset.sum_insert (by simp), hQ, Nat.mul_div_cancel_left _ (pow_pos hb _)]
    ring
  have hlow := digit_sum_lt hb w d (w k) (s.filter fun i => w i < w k)
    (hw.mono (Finset.coe_subset.2 (Finset.filter_subset _ _))) (by simp)
    (fun i hi => hd i (Finset.mem_of_mem_filter i hi))
  rw [hsplit, Nat.add_mul_div_left _ _ (pow_pos hb _), Nat.div_eq_of_lt hlow, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd k hk)]

end Digits

section Key
variable {σ : Type*}

/-- The SoS substitution: variable `k` ↦ `ε^(b^(w k))`. -/
noncomputable def sosSubst (b : ℕ) (w : σ → ℕ) : MvPolynomial σ R →ₐ[R] Poly ℤ R :=
  aeval fun k => single ((b ^ w k : ℕ) : ℤ) 1

/-- The exponent of the monomial `m` under `sosSubst b w`. -/
def sosExpo (b : ℕ) (w : σ → ℕ) (m : σ →₀ ℕ) : ℕ := ∑ i ∈ m.support, m i * b ^ w i

theorem prod_single_pow (s : Finset σ) (a : σ → ℤ) (d : σ → ℕ) :
    ∏ i ∈ s, (HahnSeries.single (a i) (1 : R) : HahnSeries ℤ R) ^ d i =
      HahnSeries.single (∑ i ∈ s, d i • a i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, HahnSeries.single_pow,
      HahnSeries.single_mul_single, one_pow, one_mul]

theorem toHahn_sosSubst (b : ℕ) (w : σ → ℕ) (D : MvPolynomial σ R) :
    toHahn (sosSubst b w D) =
      ∑ m ∈ D.support, HahnSeries.single ((sosExpo b w m : ℕ) : ℤ) (D.coeff m) := by
  have h1 : toHahn (sosSubst b w D) = toHahnAlg (sosSubst b w D) := rfl
  rw [h1, sosSubst, ← AlgHom.comp_apply, comp_aeval, aeval_def, eval₂_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [toHahnAlg_apply, toHahn_single]
  rw [prod_single_pow, ← HahnSeries.C_eq_algebraMap, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one]
  congr 1
  simp [sosExpo]

theorem sosExpo_eq_sum_of_subset (b : ℕ) (w : σ → ℕ) {m : σ →₀ ℕ} {s : Finset σ}
    (hs : m.support ⊆ s) : sosExpo b w m = ∑ i ∈ s, m i * b ^ w i :=
  Finset.sum_subset hs fun i _ hi => by rw [Finsupp.notMem_support_iff.1 hi, zero_mul]

/-- Monomials with all exponents `< b` have distinct SoS exponents. -/
theorem sosExpo_injOn {b : ℕ} {w : σ → ℕ} (hw : Function.Injective w) {m m' : σ →₀ ℕ}
    (hm : ∀ k, m k < b) (hm' : ∀ k, m' k < b) (h : sosExpo b w m = sosExpo b w m') :
    m = m' := by
  classical
  ext k
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) (hm k)
  set s := m.support ∪ m'.support ∪ {k}
  have hks : k ∈ s := by simp [s]
  have e1 := sosExpo_eq_sum_of_subset b w (s := s) (m := m) (by
    intro i hi; simp [s, Finsupp.mem_support_iff.1 hi])
  have e2 := sosExpo_eq_sum_of_subset b w (s := s) (m := m') (by
    intro i hi; simp [s, Finsupp.mem_support_iff.1 hi])
  have := digit_extract hb (hw.injOn (s := ↑s)) (fun i _ => hm i) hks
  have := digit_extract hb (hw.injOn (s := ↑s)) (fun i _ => hm' i) hks
  rw [← e1] at *; rw [← e2] at *
  rw [h] at *
  omega

/-- **Key lemma.** A nonzero polynomial of degree `< b` in each variable stays nonzero under
the SoS substitution `X k ↦ ε^(b^(w k))`, for injective `w`: distinct monomials go to distinct
powers of `ε` (base-`b` expansion), so no cancellation can occur. -/
theorem sosSubst_ne_zero {b : ℕ} {w : σ → ℕ} (hw : Function.Injective w)
    {D : MvPolynomial σ R} (hD : D ≠ 0) (hdeg : ∀ m ∈ D.support, ∀ k, m k < b) :
    sosSubst b w D ≠ 0 := by
  obtain ⟨m₀, hm₀⟩ := MvPolynomial.ne_zero_iff.1 hD
  have hmem : m₀ ∈ D.support := MvPolynomial.mem_support_iff.2 hm₀
  intro h
  have := congrArg (fun p => (toHahn p).coeff ((sosExpo b w m₀ : ℕ) : ℤ)) h
  simp only [toHahn_sosSubst, HahnSeries.coeff_sum, HahnSeries.coeff_single, map_zero,
    HahnSeries.coeff_zero] at this
  rw [Finset.sum_eq_single m₀ (fun m hm hne => ?_) (fun h => absurd hmem h), ite_eq_left rfl]
    at this
  · exact hm₀ this
  · rw [ite_eq_right]
    intro he
    exact hne (sosExpo_injOn hw (hdeg m hm) (hdeg m₀ hmem) (Nat.cast_injective he).symm)

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

/-! ### Degree bounds with multiplicities (for the lifted predicates) -/

section DegBd
variable [Nontrivial R] {n d : ℕ}

/-- `DegBd β f`: variable `k` occurs in `f` with degree `≤ β k`. -/
def DegBd (β : Fin n × Fin d → ℕ) (f : MvPolynomial (Fin n × Fin d) R) : Prop :=
  ∀ k, degreeOf k f ≤ β k

theorem DegBd.mono {β γ : Fin n × Fin d → ℕ} {f : MvPolynomial (Fin n × Fin d) R}
    (h : DegBd β f) (hle : ∀ k, β k ≤ γ k) : DegBd γ f := fun k => (h k).trans (hle k)

theorem DegBd.add {β : Fin n × Fin d → ℕ} {f g : MvPolynomial (Fin n × Fin d) R}
    (hf : DegBd β f) (hg : DegBd β g) : DegBd β (f + g) := fun k =>
  (degreeOf_add_le k f g).trans (max_le (hf k) (hg k))

theorem DegBd.sub {β : Fin n × Fin d → ℕ} {f g : MvPolynomial (Fin n × Fin d) R}
    (hf : DegBd β f) (hg : DegBd β g) : DegBd β (f - g) := fun k =>
  (degreeOf_sub_le k f g).trans (max_le (hf k) (hg k))

theorem DegBd.mul {β γ : Fin n × Fin d → ℕ} {f g : MvPolynomial (Fin n × Fin d) R}
    (hf : DegBd β f) (hg : DegBd γ g) : DegBd (β + γ) (f * g) := fun k =>
  (degreeOf_mul_le k f g).trans (Nat.add_le_add (hf k) (hg k))

/-- A 3×3 determinant whose column `c` has degree bound `βc` has bound `β₀ + β₁ + β₂`. -/
theorem DegBd.det3 {β₀ β₁ β₂ : Fin n × Fin d → ℕ} {a b c e f g h i j : MvPolynomial (Fin n × Fin d) R}
    (ha : DegBd β₀ a) (hb : DegBd β₁ b) (hc : DegBd β₂ c) (he : DegBd β₀ e) (hf : DegBd β₁ f)
    (hg : DegBd β₂ g) (hh : DegBd β₀ h) (hi : DegBd β₁ i) (hj : DegBd β₂ j) :
    DegBd (β₀ + β₁ + β₂) (Geometry.det3 a b c e f g h i j) := by
  unfold Geometry.det3
  have t : ∀ {x y z : MvPolynomial (Fin n × Fin d) R} {γ : Fin n × Fin d → ℕ},
      DegBd γ x → DegBd γ y → DegBd γ z → DegBd γ (x - y + z) :=
    fun hx hy hz => (hx.sub hy).add hz
  refine t ?_ ?_ ?_
  · exact (ha.mul (((hf.mul hj).sub ((hg.mul hi).mono fun k => by
      simp only [Pi.add_apply]; omega)))).mono fun k => by simp only [Pi.add_apply]; omega
  · exact (hb.mul (((he.mul hj).sub ((hg.mul hh).mono fun k => by
      simp only [Pi.add_apply]; omega)))).mono fun k => by simp only [Pi.add_apply]; omega
  · exact (hc.mul (((he.mul hi).sub ((hf.mul hh).mono fun k => by
      simp only [Pi.add_apply]; omega)))).mono fun k => by simp only [Pi.add_apply]; omega

/-- A 4×4 determinant whose column `c` has degree bound `βc` has bound `β₀ + β₁ + β₂ + β₃`. -/
theorem DegBd.det4 {β₀ β₁ β₂ β₃ : Fin n × Fin d → ℕ}
    {a b c e f g h i j k l m o p q r : MvPolynomial (Fin n × Fin d) R}
    (ha : DegBd β₀ a) (hb : DegBd β₁ b) (hc : DegBd β₂ c) (he : DegBd β₃ e)
    (hf : DegBd β₀ f) (hg : DegBd β₁ g) (hh : DegBd β₂ h) (hi : DegBd β₃ i)
    (hj : DegBd β₀ j) (hk : DegBd β₁ k) (hl : DegBd β₂ l) (hm : DegBd β₃ m)
    (ho : DegBd β₀ o) (hp : DegBd β₁ p) (hq : DegBd β₂ q) (hr : DegBd β₃ r) :
    DegBd (β₀ + β₁ + β₂ + β₃) (Geometry.det4 a b c e f g h i j k l m o p q r) := by
  unfold Geometry.det4
  have e : ∀ {γ : Fin n × Fin d → ℕ}, (∀ x, γ x = β₀ x + β₁ x + β₂ x + β₃ x) →
      ∀ x, γ x ≤ (β₀ + β₁ + β₂ + β₃) x := fun h x => by
    have := h x; simp only [Pi.add_apply]; omega
  refine (((?_ : DegBd _ _).sub ?_).add ?_).sub ?_
  · exact (ha.mul (DegBd.det3 hg hh hi hk hl hm hp hq hr)).mono (e fun x => by
      simp only [Pi.add_apply]; omega)
  · exact (hb.mul (DegBd.det3 hf hh hi hj hl hm ho hq hr)).mono (e fun x => by
      simp only [Pi.add_apply]; omega)
  · exact (hc.mul (DegBd.det3 hf hg hi hj hk hm ho hp hr)).mono (e fun x => by
      simp only [Pi.add_apply]; omega)
  · exact (he.mul (DegBd.det3 hf hg hh hj hk hl ho hp hq)).mono (e fun x => by
      simp only [Pi.add_apply]; omega)

theorem DegBd.lt_of_le {β : Fin n × Fin d → ℕ} {f : MvPolynomial (Fin n × Fin d) R}
    (h : DegBd β f) {b : ℕ} (hb : ∀ k, β k < b) : ∀ m ∈ f.support, ∀ k, m k < b :=
  fun _ hm k => lt_of_le_of_lt ((monomial_le_degreeOf k hm).trans (h k)) (hb k)

end DegBd

/-! ### The perturbation -/

section Perturb
variable {n d : ℕ}

/-- The perturbation index of coordinate `j` of point `i` (`finProdFinEquiv`, so injective). -/
def sosIdx (k : Fin n × Fin d) : ℕ := k.2 + d * k.1

theorem sosIdx_injective : Function.Injective (sosIdx : Fin n × Fin d → ℕ) := fun _ _ h =>
  finProdFinEquiv.injective (Fin.ext h)

/-- **SoS perturbed point**: coordinate `j` of input point `i` becomes
`x i j + ε^(b^(j + d i))`. Computable. All perturbation exponents are distinct powers of two. -/
def sosPoint (b : ℕ) (x : Fin n → Fin d → R) (i : Fin n) : Fin d → Poly ℤ R :=
  fun j => Poly.C (x i j) + single ((b ^ sosIdx (i, j) : ℕ) : ℤ) 1

/-- The symbolic version of `sosPoint`: the perturbation is the variable `X (i, j)`. -/
noncomputable def mvPoint (x : Fin n → Fin d → R) (i : Fin n) :
    Fin d → MvPolynomial (Fin n × Fin d) R :=
  fun j => MvPolynomial.C (x i j) + X (i, j)

theorem sosSubst_mvPoint (b : ℕ) (x : Fin n → Fin d → R) (i : Fin n) :
    (sosSubst b sosIdx : MvPolynomial (Fin n × Fin d) R →ₐ[R] _) ∘ mvPoint x i = sosPoint b x i := by
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
def orient2dSoS (b : ℕ) (x : Fin n → Fin 2 → R) (i k l : Fin n) : Poly ℤ R :=
  orient2d (sosPoint b x i) (sosPoint b x k) (sosPoint b x l)

/-- **SoS nonvanishing.** For any input coordinates, even degenerate (collinear or coincident
points), the perturbed `orient2d` is nonzero as soon as the three point indices are distinct. -/
theorem orient2dSoS_ne_zero [Nontrivial R] {b : ℕ} (hb : 2 ≤ b) (x : Fin n → Fin 2 → R) {i k l : Fin n}
    (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) : orient2dSoS b x i k l ≠ 0 := by
  set D := orient2d (mvPoint x i) (mvPoint x k) (mvPoint x l) with hD
  have hsub : sosSubst b sosIdx D = orient2dSoS b x i k l := by
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
    exact fun m hm k => by have := DegLe.le_one h m hm k; omega

end Orient2d

/-! ### `orient3d` -/

section Orient3d
variable {n : ℕ}

/-- SoS-perturbed `orient3d` of input points `i, k, l, m`. Computable. -/
def orient3dSoS (b : ℕ) (x : Fin n → Fin 3 → R) (i k l m : Fin n) : Poly ℤ R :=
  orient3d (sosPoint b x i) (sosPoint b x k) (sosPoint b x l) (sosPoint b x m)

/-- **SoS nonvanishing for `orient3d`**: nonzero for any input as soon as the four point indices
are pairwise distinct. -/
theorem orient3dSoS_ne_zero [Nontrivial R] {b : ℕ} (hb : 2 ≤ b) (x : Fin n → Fin 3 → R) {i k l m : Fin n}
    (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    orient3dSoS b x i k l m ≠ 0 := by
  set D := orient3d (mvPoint x i) (mvPoint x k) (mvPoint x l) (mvPoint x m) with hD
  have hsub : sosSubst b sosIdx D = orient3dSoS b x i k l m := by
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
    exact fun m hm k => by have := DegLe.le_one h m hm k; omega

end Orient3d

/-! ### `incircle` and `insphere`

The lifted column `|p - d|²` has degree `2` in the perturbation variables, so the perturbed
determinants have degree `≤ 3` in each variable (one from a linear column, two from the lifted
column, in the variables of the base point that occurs in every row). The base `b` must therefore
be at least `4`; `b = 4` works for all four predicates at once. -/

section Lifted
variable {n : ℕ}

/-- Indicator bound of coordinate `j`. -/
def coordBd {d : ℕ} (j : Fin d) : Fin n × Fin d → ℕ := fun k => if k.2 ∈ ({j} : Finset _) then 1 else 0

theorem degBd_mvPoint_sub [Nontrivial R] {d : ℕ} (x : Fin n → Fin d → R) (i i' : Fin n)
    (j : Fin d) : DegBd (coordBd j) (mvPoint x i j - mvPoint x i' j) :=
  degLe_mvPoint_sub x i i' j

/-- SoS-perturbed `incircle`. Computable. -/
def incircleSoS (b : ℕ) (x : Fin n → Fin 2 → R) (i k l m : Fin n) : Poly ℤ R :=
  incircle (sosPoint b x i) (sosPoint b x k) (sosPoint b x l) (sosPoint b x m)

/-- SoS-perturbed `insphere`. Computable. -/
def insphereSoS (b : ℕ) (x : Fin n → Fin 3 → R) (i k l m o : Fin n) : Poly ℤ R :=
  insphere (sosPoint b x i) (sosPoint b x k) (sosPoint b x l) (sosPoint b x m) (sosPoint b x o)

/-- **SoS nonvanishing for `incircle`** (base `b ≥ 4`, distinct indices). The proof certifies
`D ≠ 0` by an evaluation with value `2`, hence the hypothesis `(2 : R) ≠ 0` (true for `ℤ`, `ℚ`,
any ordered ring). -/
theorem incircleSoS_ne_zero [Nontrivial R] {b : ℕ} (hb : 4 ≤ b) (h2 : (2 : R) ≠ 0)
    (x : Fin n → Fin 2 → R) {i k l m : Fin n}
    (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    incircleSoS b x i k l m ≠ 0 := by
  set D := incircle (mvPoint x i) (mvPoint x k) (mvPoint x l) (mvPoint x m) with hD
  have hsub : sosSubst b sosIdx D = incircleSoS b x i k l m := by
    rw [hD, map_incircle, sosSubst_mvPoint, sosSubst_mvPoint, sosSubst_mvPoint,
      sosSubst_mvPoint]; rfl
  rw [← hsub]
  refine sosSubst_ne_zero sosIdx_injective ?_ ?_
  · -- evaluate at the point making the perturbed points `(1,0), (0,1), (-1,0), (0,0)`
    intro h0
    let t : Fin n → Fin 2 → R := fun a j =>
      if a = i ∧ j = 0 then 1 else if a = k ∧ j = 1 then 1 else if a = l ∧ j = 0 then -1 else 0
    have := congrArg (MvPolynomial.eval fun q : Fin n × Fin 2 => t q.1 q.2 - x q.1 q.2) h0
    rw [hD, map_incircle, eval_mvPoint, eval_mvPoint, eval_mvPoint, eval_mvPoint,
      map_zero] at this
    simp [incircle, det3, t, hik, hil, hkl, hik.symm, hil.symm, him.symm, hkl.symm, hkm.symm,
      hlm.symm] at this
    exact h2 (by rw [← one_add_one_eq_two]; exact this)
  · have sq : ∀ q : Fin n, DegBd (fun _ => 2)
        ((mvPoint x q 0 - mvPoint x m 0) * (mvPoint x q 0 - mvPoint x m 0) +
          (mvPoint x q 1 - mvPoint x m 1) * (mvPoint x q 1 - mvPoint x m 1)) := fun q =>
      ((degBd_mvPoint_sub x q m 0).mul (degBd_mvPoint_sub x q m 0)).mono
          (fun k => by simp only [coordBd, Pi.add_apply]; split_ifs <;> omega) |>.add
        (((degBd_mvPoint_sub x q m 1).mul (degBd_mvPoint_sub x q m 1)).mono
          (fun k => by simp only [coordBd, Pi.add_apply]; split_ifs <;> omega))
    have h := DegBd.det3 (degBd_mvPoint_sub x i m 0) (degBd_mvPoint_sub x i m 1) (sq i)
      (degBd_mvPoint_sub x k m 0) (degBd_mvPoint_sub x k m 1) (sq k)
      (degBd_mvPoint_sub x l m 0) (degBd_mvPoint_sub x l m 1) (sq l)
    refine h.lt_of_le fun q => ?_
    simp only [coordBd, Pi.add_apply, Finset.mem_singleton]
    split_ifs <;> omega

/-- **SoS nonvanishing for `insphere`** (base `b ≥ 4`, distinct indices, `(2 : R) ≠ 0`). -/
theorem insphereSoS_ne_zero [Nontrivial R] {b : ℕ} (hb : 4 ≤ b) (h2 : (2 : R) ≠ 0)
    (x : Fin n → Fin 3 → R) {i k l m o : Fin n}
    (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hio : i ≠ o) (hkl : k ≠ l) (hkm : k ≠ m)
    (hko : k ≠ o) (hlm : l ≠ m) (hlo : l ≠ o) (hmo : m ≠ o) :
    insphereSoS b x i k l m o ≠ 0 := by
  set D := insphere (mvPoint x i) (mvPoint x k) (mvPoint x l) (mvPoint x m) (mvPoint x o)
    with hD
  have hsub : sosSubst b sosIdx D = insphereSoS b x i k l m o := by
    rw [hD, map_insphere, sosSubst_mvPoint, sosSubst_mvPoint, sosSubst_mvPoint,
      sosSubst_mvPoint, sosSubst_mvPoint]; rfl
  rw [← hsub]
  refine sosSubst_ne_zero sosIdx_injective ?_ ?_
  · -- perturbed points `e₀, e₁, e₂, -e₀, 0`
    intro h0
    let t : Fin n → Fin 3 → R := fun a j =>
      if a = i ∧ j = 0 then 1 else if a = k ∧ j = 1 then 1 else if a = l ∧ j = 2 then 1
      else if a = m ∧ j = 0 then -1 else 0
    have := congrArg (MvPolynomial.eval fun q : Fin n × Fin 3 => t q.1 q.2 - x q.1 q.2) h0
    rw [hD, map_insphere, eval_mvPoint, eval_mvPoint, eval_mvPoint, eval_mvPoint, eval_mvPoint,
      map_zero] at this
    simp [insphere, det4, det3, t, hik, hil, him, hkl, hkm, hlm, hik.symm, hil.symm, him.symm,
      hio.symm, hkl.symm, hkm.symm, hko.symm, hlm.symm, hlo.symm, hmo.symm] at this
    exact h2 (by rw [← one_add_one_eq_two]; exact this)
  · have sq : ∀ q : Fin n, DegBd (fun _ => 2)
        ((mvPoint x q 0 - mvPoint x o 0) * (mvPoint x q 0 - mvPoint x o 0) +
          (mvPoint x q 1 - mvPoint x o 1) * (mvPoint x q 1 - mvPoint x o 1) +
          (mvPoint x q 2 - mvPoint x o 2) * (mvPoint x q 2 - mvPoint x o 2)) := fun q =>
      ((((degBd_mvPoint_sub x q o 0).mul (degBd_mvPoint_sub x q o 0)).mono
          (fun k => by simp only [coordBd, Pi.add_apply]; split_ifs <;> omega)).add
        (((degBd_mvPoint_sub x q o 1).mul (degBd_mvPoint_sub x q o 1)).mono
          (fun k => by simp only [coordBd, Pi.add_apply]; split_ifs <;> omega))).add
        (((degBd_mvPoint_sub x q o 2).mul (degBd_mvPoint_sub x q o 2)).mono
          (fun k => by simp only [coordBd, Pi.add_apply]; split_ifs <;> omega))
    have h := DegBd.det4
      (degBd_mvPoint_sub x i o 0) (degBd_mvPoint_sub x i o 1) (degBd_mvPoint_sub x i o 2) (sq i)
      (degBd_mvPoint_sub x k o 0) (degBd_mvPoint_sub x k o 1) (degBd_mvPoint_sub x k o 2) (sq k)
      (degBd_mvPoint_sub x l o 0) (degBd_mvPoint_sub x l o 1) (degBd_mvPoint_sub x l o 2) (sq l)
      (degBd_mvPoint_sub x m o 0) (degBd_mvPoint_sub x m o 1) (degBd_mvPoint_sub x m o 2) (sq m)
    refine h.lt_of_le fun q => ?_
    simp only [coordBd, Pi.add_apply, Finset.mem_singleton]
    split_ifs <;> omega

end Lifted

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

theorem isFinite_sosPoint (b : ℕ) (x : Fin n → Fin d → R) (i : Fin n) (j : Fin d) :
    (sosPoint b x i j).IsFinite := by
  refine (isFinite_C _).add ?_
  unfold IsFinite
  by_cases h : (1 : R) = 0
  · simp [single, h]
  · rw [leadExp_single h]; exact WithTop.coe_le_coe.2 (by positivity)

theorem std_sosPoint {b : ℕ} (hb : 0 < b) (x : Fin n → Fin d → R) (i : Fin n) (j : Fin d) :
    (sosPoint b x i j).std = x i j := by
  simp only [sosPoint, std]
  simp only [Poly.coeff_add, Poly.coeff_C, Poly.coeff_single, ite_true]
  rw [ite_eq_right (Nat.cast_pos.2 (pow_pos hb _) : (0 : ℤ) < _).ne, add_zero]

/-- The perturbed point as a point of the finite subring. -/
def sosPointFin (b : ℕ) (x : Fin n → Fin d → R) (i : Fin n) :
    Fin d → (finiteSubring : Subring (Poly ℤ R)) :=
  fun j => ⟨sosPoint b x i j, isFinite_sosPoint b x i j⟩

theorem stdPart_sosPointFin {b : ℕ} (hb : 0 < b) (x : Fin n → Fin d → R) (i : Fin n) :
    stdPart ∘ sosPointFin b x i = x i := by
  funext j; exact std_sosPoint hb x i j

theorem subtype_sosPointFin (b : ℕ) (x : Fin n → Fin d → R) (i : Fin n) :
    (finiteSubring : Subring (Poly ℤ R)).subtype ∘ sosPointFin b x i = sosPoint b x i := rfl

/-- A finite element with nonzero standard part has that standard part as leading coefficient. -/
theorem sign_of_isFinite_of_std_ne_zero [LinearOrder R] {p : Poly ℤ R} (hp : p.IsFinite)
    (h : p.std ≠ 0) : p.sign = signOf p.std := by
  have hle : p.leadExp = ((0 : ℤ) : WithTop ℤ) := by
    refine le_antisymm ?_ hp
    by_contra hlt
    exact h (coeff_eq_zero_of_lt_leadExp (lt_of_not_ge hlt))
  rw [sign_eq_signOf_leadCoeff, std, coeff_leadExp hle]

theorem orient2dSoS_isFinite (b : ℕ) (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    (orient2dSoS b x i k l).IsFinite := by
  have := (orient2d (sosPointFin b x i) (sosPointFin b x k) (sosPointFin b x l)).2
  rwa [← Subring.coe_subtype, map_orient2d, subtype_sosPointFin, subtype_sosPointFin,
    subtype_sosPointFin] at this

/-- The standard part of the perturbed `orient2d` is the unperturbed `orient2d`. -/
theorem orient2dSoS_std {b : ℕ} (hb : 0 < b) (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    (orient2dSoS b x i k l).std = orient2d (x i) (x k) (x l) := by
  have h := map_orient2d stdPart (sosPointFin b x i) (sosPointFin b x k) (sosPointFin b x l)
  rw [stdPart_sosPointFin hb, stdPart_sosPointFin hb, stdPart_sosPointFin hb, stdPart_apply] at h
  rw [← h]
  have := map_orient2d (finiteSubring : Subring (Poly ℤ R)).subtype
    (sosPointFin b x i) (sosPointFin b x k) (sosPointFin b x l)
  rw [subtype_sosPointFin, subtype_sosPointFin, subtype_sosPointFin] at this
  rw [orient2dSoS, ← this]; rfl

/-- **SoS agrees with the exact predicate on nondegenerate input.** -/
theorem orient2dSoS_sign [LinearOrder R] {b : ℕ} (hb : 0 < b) (x : Fin n → Fin 2 → R) (i k l : Fin n)
    (h : orient2d (x i) (x k) (x l) ≠ 0) :
    (orient2dSoS b x i k l).sign = signOf (orient2d (x i) (x k) (x l)) := by
  rw [← orient2dSoS_std hb] at h ⊢
  exact sign_of_isFinite_of_std_ne_zero (orient2dSoS_isFinite b x i k l) h

theorem orient3dSoS_isFinite (b : ℕ) (x : Fin n → Fin 3 → R) (i k l m : Fin n) :
    (orient3dSoS b x i k l m).IsFinite := by
  have := (orient3d (sosPointFin b x i) (sosPointFin b x k) (sosPointFin b x l) (sosPointFin b x m)).2
  rwa [← Subring.coe_subtype, map_orient3d, subtype_sosPointFin, subtype_sosPointFin,
    subtype_sosPointFin, subtype_sosPointFin] at this

theorem orient3dSoS_std {b : ℕ} (hb : 0 < b) (x : Fin n → Fin 3 → R) (i k l m : Fin n) :
    (orient3dSoS b x i k l m).std = orient3d (x i) (x k) (x l) (x m) := by
  have h := map_orient3d stdPart (sosPointFin b x i) (sosPointFin b x k) (sosPointFin b x l)
    (sosPointFin b x m)
  rw [stdPart_sosPointFin hb, stdPart_sosPointFin hb, stdPart_sosPointFin hb, stdPart_sosPointFin hb,
    stdPart_apply] at h
  rw [← h]
  have := map_orient3d (finiteSubring : Subring (Poly ℤ R)).subtype
    (sosPointFin b x i) (sosPointFin b x k) (sosPointFin b x l) (sosPointFin b x m)
  rw [subtype_sosPointFin, subtype_sosPointFin, subtype_sosPointFin, subtype_sosPointFin] at this
  rw [orient3dSoS, ← this]; rfl

theorem orient3dSoS_sign [LinearOrder R] {b : ℕ} (hb : 0 < b) (x : Fin n → Fin 3 → R) (i k l m : Fin n)
    (h : orient3d (x i) (x k) (x l) (x m) ≠ 0) :
    (orient3dSoS b x i k l m).sign = signOf (orient3d (x i) (x k) (x l) (x m)) := by
  rw [← orient3dSoS_std hb] at h ⊢
  exact sign_of_isFinite_of_std_ne_zero (orient3dSoS_isFinite b x i k l m) h

theorem incircleSoS_isFinite (b : ℕ) (x : Fin n → Fin 2 → R) (i k l m : Fin n) :
    (incircleSoS b x i k l m).IsFinite := by
  have := (incircle (sosPointFin b x i) (sosPointFin b x k) (sosPointFin b x l)
    (sosPointFin b x m)).2
  rwa [← Subring.coe_subtype, map_incircle, subtype_sosPointFin, subtype_sosPointFin,
    subtype_sosPointFin, subtype_sosPointFin] at this

theorem incircleSoS_std {b : ℕ} (hb : 0 < b) (x : Fin n → Fin 2 → R) (i k l m : Fin n) :
    (incircleSoS b x i k l m).std = incircle (x i) (x k) (x l) (x m) := by
  have h := map_incircle stdPart (sosPointFin b x i) (sosPointFin b x k) (sosPointFin b x l)
    (sosPointFin b x m)
  rw [stdPart_sosPointFin hb, stdPart_sosPointFin hb, stdPart_sosPointFin hb,
    stdPart_sosPointFin hb, stdPart_apply] at h
  rw [← h]
  have := map_incircle (finiteSubring : Subring (Poly ℤ R)).subtype
    (sosPointFin b x i) (sosPointFin b x k) (sosPointFin b x l) (sosPointFin b x m)
  rw [subtype_sosPointFin, subtype_sosPointFin, subtype_sosPointFin, subtype_sosPointFin] at this
  rw [incircleSoS, ← this]; rfl

theorem incircleSoS_sign [LinearOrder R] {b : ℕ} (hb : 0 < b) (x : Fin n → Fin 2 → R)
    (i k l m : Fin n) (h : incircle (x i) (x k) (x l) (x m) ≠ 0) :
    (incircleSoS b x i k l m).sign = signOf (incircle (x i) (x k) (x l) (x m)) := by
  rw [← incircleSoS_std hb] at h ⊢
  exact sign_of_isFinite_of_std_ne_zero (incircleSoS_isFinite b x i k l m) h

theorem insphereSoS_isFinite (b : ℕ) (x : Fin n → Fin 3 → R) (i k l m o : Fin n) :
    (insphereSoS b x i k l m o).IsFinite := by
  have := (insphere (sosPointFin b x i) (sosPointFin b x k) (sosPointFin b x l)
    (sosPointFin b x m) (sosPointFin b x o)).2
  rwa [← Subring.coe_subtype, map_insphere, subtype_sosPointFin, subtype_sosPointFin,
    subtype_sosPointFin, subtype_sosPointFin, subtype_sosPointFin] at this

theorem insphereSoS_std {b : ℕ} (hb : 0 < b) (x : Fin n → Fin 3 → R) (i k l m o : Fin n) :
    (insphereSoS b x i k l m o).std = insphere (x i) (x k) (x l) (x m) (x o) := by
  have h := map_insphere stdPart (sosPointFin b x i) (sosPointFin b x k) (sosPointFin b x l)
    (sosPointFin b x m) (sosPointFin b x o)
  rw [stdPart_sosPointFin hb, stdPart_sosPointFin hb, stdPart_sosPointFin hb,
    stdPart_sosPointFin hb, stdPart_sosPointFin hb, stdPart_apply] at h
  rw [← h]
  have := map_insphere (finiteSubring : Subring (Poly ℤ R)).subtype
    (sosPointFin b x i) (sosPointFin b x k) (sosPointFin b x l) (sosPointFin b x m)
    (sosPointFin b x o)
  rw [subtype_sosPointFin, subtype_sosPointFin, subtype_sosPointFin, subtype_sosPointFin,
    subtype_sosPointFin] at this
  rw [insphereSoS, ← this]; rfl

theorem insphereSoS_sign [LinearOrder R] {b : ℕ} (hb : 0 < b) (x : Fin n → Fin 3 → R)
    (i k l m o : Fin n) (h : insphere (x i) (x k) (x l) (x m) (x o) ≠ 0) :
    (insphereSoS b x i k l m o).sign = signOf (insphere (x i) (x k) (x l) (x m) (x o)) := by
  rw [← insphereSoS_std hb] at h ⊢
  exact sign_of_isFinite_of_std_ne_zero (insphereSoS_isFinite b x i k l m o) h

end StdPart

/-! ### Consistency under relabeling -/

section Swap
variable {n : ℕ}

theorem orient2dSoS_swap₁₂ (b : ℕ) (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    orient2dSoS b x k i l = -orient2dSoS b x i k l := orient2d_swap₁₂ _ _ _

theorem orient2dSoS_swap₂₃ (b : ℕ) (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    orient2dSoS b x i l k = -orient2dSoS b x i k l := orient2d_swap₂₃ _ _ _

theorem orient3dSoS_swap₁₂ (b : ℕ) (x : Fin n → Fin 3 → R) (i k l m : Fin n) :
    orient3dSoS b x k i l m = -orient3dSoS b x i k l m := orient3d_swap₁₂ _ _ _ _

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
    (b : ℕ) (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    (orient2dSoS b x k i l).sign = -(orient2dSoS b x i k l).sign := by
  rw [orient2dSoS_swap₁₂, sign_neg]

/-- The SoS sign is never `0` for distinct indices. -/
theorem orient2dSoS_sign_ne_zero [LinearOrder R] [IsStrictOrderedRing R] {b : ℕ} (hb : 2 ≤ b)
    (x : Fin n → Fin 2 → R) {i k l : Fin n} (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) :
    (orient2dSoS b x i k l).sign ≠ 0 := fun h =>
  orient2dSoS_ne_zero hb x hik hil hkl ((sign_eq_zero_iff _).1 h)

theorem orient3dSoS_sign_ne_zero [LinearOrder R] [IsStrictOrderedRing R] {b : ℕ} (hb : 2 ≤ b)
    (x : Fin n → Fin 3 → R) {i k l m : Fin n} (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    (orient3dSoS b x i k l m).sign ≠ 0 := fun h =>
  orient3dSoS_ne_zero hb x hik hil him hkl hkm hlm ((sign_eq_zero_iff _).1 h)

end Swap

end LeviCivita.Geometry
