/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Poly.Algebra
import Mathlib.RingTheory.Ideal.Maps

/-!
# Accessors, finite and infinitesimal elements, standard part

Computable accessors on `Poly Γ R`, each proved equal to the matching Hahn-series notion:

* `coeff p g` (`coeff_eq : p.coeff g = (toHahn p).coeff g`),
* `leadExp p : WithTop Γ` (`leadExp_eq_orderTop : p.leadExp = (toHahn p).orderTop`, `⊤` for `0`),
* `std p := p.coeff 0`, the raw coefficient at exponent `0`.

Predicates (both decidable, by comparing `leadExp` with `0`):

* `IsInfinitesimal p := 0 < p.leadExp` (every exponent is positive; `0` is infinitesimal),
* `IsFinite p := 0 ≤ p.leadExp` (no negative exponent).

Results:

* closure: finite elements form a subring `finiteSubring`; infinitesimals are closed under `+`,
  `-`, and multiplication by finite elements;
* `stdPart : finiteSubring →+* R`, computable, with `p - C (stdPart p)` infinitesimal and kernel
  the infinitesimals;
* order characterizations (`R` a strictly ordered ring):
  `isFinite_iff_exists_abs_le : p.IsFinite ↔ ∃ r, |p| ≤ C r`, and, for densely ordered `R`,
  `isInfinitesimal_iff_forall_abs_lt : p.IsInfinitesimal ↔ ∀ r, 0 < r → |p| < C r`.
  The density hypothesis is needed: in `Poly ℤ ℤ`, `|1 - ε| < C r` for every integer `r > 0`
  but `1 - ε` is not infinitesimal.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita

open HahnSeries

namespace Poly

variable {Γ R : Type*}

section Defs
variable [LinearOrder Γ]

/-- Coefficient of `ε^g` in a raw term list (the sum of all matching entries, so that it agrees
with the denotation for any list). -/
def coeffL [Zero R] [Add R] (g : Γ) : List (Γ × R) → R
  | [] => 0
  | t :: l => (if g = t.1 then t.2 else 0) + coeffL g l

/-- The coefficient of `ε^g`. -/
def coeff [Zero R] [Add R] (p : Poly Γ R) (g : Γ) : R := coeffL g p.terms

/-- The leading (smallest) exponent, `⊤` for the zero polynomial. -/
def leadExp [Zero R] (p : Poly Γ R) : WithTop Γ :=
  match p.terms with
  | [] => ⊤
  | t :: _ => t.1

/-- The coefficient at exponent `0`. For finite `p` this is the standard part (`stdPart`). -/
def std [Zero Γ] [Zero R] [Add R] (p : Poly Γ R) : R := p.coeff 0

/-- `p` is infinitesimal: all its exponents are positive. `0` is infinitesimal. -/
def IsInfinitesimal [Zero Γ] [Zero R] (p : Poly Γ R) : Prop := 0 < p.leadExp

/-- `p` is finite: it has no negative exponent. -/
def IsFinite [Zero Γ] [Zero R] (p : Poly Γ R) : Prop := 0 ≤ p.leadExp

instance [Zero Γ] [Zero R] (p : Poly Γ R) : Decidable p.IsInfinitesimal :=
  inferInstanceAs (Decidable (0 < p.leadExp))

instance [Zero Γ] [Zero R] (p : Poly Γ R) : Decidable p.IsFinite :=
  inferInstanceAs (Decidable (0 ≤ p.leadExp))

end Defs

section Denote
variable [LinearOrder Γ] [AddCommGroup R]

theorem coeff_hahnL (g : Γ) : ∀ l : List (Γ × R), (hahnL l).coeff g = coeffL g l
  | [] => rfl
  | t :: l => by simp [coeffL, coeff_single, coeff_hahnL g l]

theorem coeff_eq_coeff_toHahnFun (p : Poly Γ R) (g : Γ) : p.coeff g = (toHahnFun p).coeff g :=
  (coeff_hahnL g p.terms).symm

theorem leadExp_eq_orderTop_toHahnFun (p : Poly Γ R) : p.leadExp = (toHahnFun p).orderTop := by
  obtain ⟨_ | ⟨⟨e, c⟩, l⟩, s, n⟩ := p
  · simp [toHahnFun, leadExp]
  · have s' := List.pairwise_cons.1 s
    have hc : c ≠ 0 := n _ List.mem_cons_self
    simp only [toHahnFun, leadExp, hahnL_cons]
    rw [orderTop_add_eq_left, orderTop_single hc]
    rw [orderTop_single hc]
    exact lt_orderTop_hahnL s'.1

end Denote

/-- A Hahn series whose coefficients vanish at every `g ≤ i` has `orderTop > i`. -/
theorem _root_.HahnSeries.lt_orderTop_of_coeff_eq_zero {Γ R : Type*} [LinearOrder Γ] [Zero R]
    {x : R⟦Γ⟧} {i : Γ} (h : ∀ g ≤ i, x.coeff g = 0) : (i : WithTop Γ) < x.orderTop := by
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
  exact coeff_orderTop_ne hg.symm (h g (WithTop.coe_le_coe.1 (hg ▸ hle)))

section Ring
variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
  [DecidableEq R]

/-! ### Coefficients and leading exponent -/

theorem coeff_eq (p : Poly Γ R) (g : Γ) : p.coeff g = (toHahn p).coeff g :=
  coeff_eq_coeff_toHahnFun p g

theorem leadExp_eq_orderTop (p : Poly Γ R) : p.leadExp = (toHahn p).orderTop :=
  leadExp_eq_orderTop_toHahnFun p

theorem leadCoeff_eq_leadingCoeff (p : Poly Γ R) : p.leadCoeff = (toHahn p).leadingCoeff :=
  (leadingCoeff_toHahnFun p).symm

theorem coeff_injective : Function.Injective (coeff : Poly Γ R → Γ → R) := fun p q h =>
  toHahn_injective (HahnSeries.ext (funext fun g => by rw [← coeff_eq, ← coeff_eq, h]))

@[simp] theorem coeff_zero (g : Γ) : (0 : Poly Γ R).coeff g = 0 := rfl

@[simp] theorem coeff_add (p q : Poly Γ R) (g : Γ) : (p + q).coeff g = p.coeff g + q.coeff g := by
  simp [coeff_eq]

@[simp] theorem coeff_neg (p : Poly Γ R) (g : Γ) : (-p).coeff g = -p.coeff g := by
  simp [coeff_eq]

@[simp] theorem coeff_sub (p q : Poly Γ R) (g : Γ) : (p - q).coeff g = p.coeff g - q.coeff g := by
  simp [coeff_eq]

@[simp] theorem coeff_smul (r : R) (p : Poly Γ R) (g : Γ) : (r • p).coeff g = r * p.coeff g := by
  simp [coeff_eq]

@[simp] theorem coeff_single (e g : Γ) (c : R) :
    (single e c : Poly Γ R).coeff g = if g = e then c else 0 := by
  rw [coeff_eq, toHahn_single, HahnSeries.coeff_single]; congr

@[simp] theorem coeff_C (r : R) (g : Γ) : (C r : Poly Γ R).coeff g = if g = 0 then r else 0 :=
  coeff_single 0 g r

@[simp] theorem leadExp_zero : (0 : Poly Γ R).leadExp = ⊤ := rfl

@[simp] theorem leadExp_eq_top_iff {p : Poly Γ R} : p.leadExp = ⊤ ↔ p = 0 := by
  rw [leadExp_eq_orderTop, orderTop_eq_top, map_eq_zero_iff _ toHahn_injective]

theorem leadExp_single {e : Γ} {c : R} (hc : c ≠ 0) : (single e c : Poly Γ R).leadExp = e := by
  rw [leadExp_eq_orderTop, toHahn_single, orderTop_single hc]

theorem coeff_eq_zero_of_lt_leadExp {p : Poly Γ R} {g : Γ} (h : (g : WithTop Γ) < p.leadExp) :
    p.coeff g = 0 := by
  rw [leadExp_eq_orderTop] at h
  rw [coeff_eq, coeff_eq_zero_of_lt_orderTop h]

theorem coeff_leadExp {p : Poly Γ R} {e : Γ} (h : p.leadExp = e) : p.coeff e = p.leadCoeff := by
  rw [leadExp_eq_orderTop] at h
  have hx : (toHahn p).orderTop ≠ ⊤ := by rw [h]; exact WithTop.coe_ne_top
  have := coeff_untop_eq_leadingCoeff hx
  simp only [h, WithTop.untop_coe] at this
  rw [coeff_eq, this, leadCoeff_eq_leadingCoeff]

theorem lt_leadExp_of_coeff_eq_zero {p : Poly Γ R} {i : Γ} (h : ∀ g ≤ i, p.coeff g = 0) :
    (i : WithTop Γ) < p.leadExp := by
  rw [leadExp_eq_orderTop]
  exact lt_orderTop_of_coeff_eq_zero fun g hg => by rw [← coeff_eq, h g hg]

/-! ### `std` -/

@[simp] theorem std_zero : (0 : Poly Γ R).std = 0 := rfl

@[simp] theorem std_add (p q : Poly Γ R) : (p + q).std = p.std + q.std := coeff_add p q 0

@[simp] theorem std_neg (p : Poly Γ R) : (-p).std = -p.std := coeff_neg p 0

@[simp] theorem std_sub (p q : Poly Γ R) : (p - q).std = p.std - q.std := coeff_sub p q 0

@[simp] theorem std_C (r : R) : (C r : Poly Γ R).std = r := by simp [std]

@[simp] theorem std_one : (1 : Poly Γ R).std = 1 := by rw [← C_one, std_C]

/-! ### Infinitesimal and finite elements -/

theorem isInfinitesimal_iff_orderTop {p : Poly Γ R} :
    p.IsInfinitesimal ↔ 0 < (toHahn p).orderTop := by
  rw [IsInfinitesimal, leadExp_eq_orderTop]

theorem isFinite_iff_orderTop {p : Poly Γ R} : p.IsFinite ↔ 0 ≤ (toHahn p).orderTop := by
  rw [IsFinite, leadExp_eq_orderTop]

theorem IsInfinitesimal.isFinite {p : Poly Γ R} (h : p.IsInfinitesimal) : p.IsFinite := h.le

@[simp] theorem isInfinitesimal_zero : (0 : Poly Γ R).IsInfinitesimal := WithTop.coe_lt_top 0

@[simp] theorem isFinite_zero : (0 : Poly Γ R).IsFinite := isInfinitesimal_zero.isFinite

theorem isFinite_C (r : R) : (C r : Poly Γ R).IsFinite := by
  rw [isFinite_iff_orderTop, toHahn_C, HahnSeries.C_apply]
  exact orderTop_single_le

@[simp] theorem isFinite_one : (1 : Poly Γ R).IsFinite := C_one (Γ := Γ) (R := R) ▸ isFinite_C 1

theorem IsInfinitesimal.add {p q : Poly Γ R} (hp : p.IsInfinitesimal) (hq : q.IsInfinitesimal) :
    (p + q).IsInfinitesimal := by
  rw [isInfinitesimal_iff_orderTop] at *
  rw [map_add]
  exact lt_of_lt_of_le (lt_min hp hq) min_orderTop_le_orderTop_add

theorem IsFinite.add {p q : Poly Γ R} (hp : p.IsFinite) (hq : q.IsFinite) : (p + q).IsFinite := by
  rw [isFinite_iff_orderTop] at *
  rw [map_add]
  exact le_trans (le_min hp hq) min_orderTop_le_orderTop_add

@[simp] theorem isInfinitesimal_neg {p : Poly Γ R} : (-p).IsInfinitesimal ↔ p.IsInfinitesimal := by
  rw [isInfinitesimal_iff_orderTop, isInfinitesimal_iff_orderTop, map_neg, orderTop_neg]

@[simp] theorem isFinite_neg {p : Poly Γ R} : (-p).IsFinite ↔ p.IsFinite := by
  rw [isFinite_iff_orderTop, isFinite_iff_orderTop, map_neg, orderTop_neg]

theorem IsInfinitesimal.neg {p : Poly Γ R} (hp : p.IsInfinitesimal) : (-p).IsInfinitesimal :=
  isInfinitesimal_neg.2 hp

theorem IsFinite.neg {p : Poly Γ R} (hp : p.IsFinite) : (-p).IsFinite := isFinite_neg.2 hp

theorem IsInfinitesimal.sub {p q : Poly Γ R} (hp : p.IsInfinitesimal) (hq : q.IsInfinitesimal) :
    (p - q).IsInfinitesimal := by
  rw [sub_eq_add_neg]; exact hp.add hq.neg

theorem IsFinite.sub {p q : Poly Γ R} (hp : p.IsFinite) (hq : q.IsFinite) : (p - q).IsFinite := by
  rw [sub_eq_add_neg]; exact hp.add hq.neg

theorem IsFinite.mul {p q : Poly Γ R} (hp : p.IsFinite) (hq : q.IsFinite) : (p * q).IsFinite := by
  rw [isFinite_iff_orderTop] at *
  rw [map_mul]
  exact le_trans (add_nonneg hp hq) orderTop_add_le_mul

/-- Infinitesimals absorb multiplication by finite elements (on the left). -/
theorem IsInfinitesimal.mul_left {p q : Poly Γ R} (hq : q.IsFinite) (hp : p.IsInfinitesimal) :
    (q * p).IsInfinitesimal := by
  rw [isFinite_iff_orderTop] at hq
  rw [isInfinitesimal_iff_orderTop] at *
  rw [map_mul]
  exact lt_of_lt_of_le hp (le_trans (le_add_of_nonneg_left hq) orderTop_add_le_mul)

/-- Infinitesimals absorb multiplication by finite elements (on the right). -/
theorem IsInfinitesimal.mul_right {p q : Poly Γ R} (hp : p.IsInfinitesimal) (hq : q.IsFinite) :
    (p * q).IsInfinitesimal := by
  rw [mul_comm]; exact hp.mul_left hq

theorem IsInfinitesimal.mul {p q : Poly Γ R} (hp : p.IsInfinitesimal) (hq : q.IsInfinitesimal) :
    (p * q).IsInfinitesimal :=
  hp.mul_right hq.isFinite

theorem IsInfinitesimal.std_eq_zero {p : Poly Γ R} (hp : p.IsInfinitesimal) : p.std = 0 :=
  coeff_eq_zero_of_lt_leadExp hp

/-- A finite element differs from its standard part by an infinitesimal. -/
theorem IsFinite.isInfinitesimal_sub_C_std {p : Poly Γ R} (hp : p.IsFinite) :
    (p - C p.std).IsInfinitesimal := by
  refine lt_leadExp_of_coeff_eq_zero fun g hg => ?_
  rw [coeff_sub, coeff_C]
  rcases hg.lt_or_eq with hg | rfl
  · rw [ite_eq_right hg.ne, coeff_eq_zero_of_lt_leadExp (lt_of_lt_of_le (WithTop.coe_lt_coe.2 hg) hp),
      sub_zero]
  · rw [ite_eq_left rfl, std, sub_self]

/-- For finite `p`, `p` is infinitesimal iff its standard part vanishes. -/
theorem IsFinite.isInfinitesimal_iff_std_eq_zero {p : Poly Γ R} (hp : p.IsFinite) :
    p.IsInfinitesimal ↔ p.std = 0 := by
  refine ⟨IsInfinitesimal.std_eq_zero, fun h => ?_⟩
  have := hp.isInfinitesimal_sub_C_std
  rwa [h, C_zero, sub_zero] at this

/-- The standard part is multiplicative on finite elements. -/
theorem std_mul {p q : Poly Γ R} (hp : p.IsFinite) (hq : q.IsFinite) :
    (p * q).std = p.std * q.std := by
  have key : p * q - C (p.std * q.std) = (p - C p.std) * q + C p.std * (q - C q.std) := by
    rw [C_mul]; ring
  have hinf : (p * q - C (p.std * q.std)).IsInfinitesimal := by
    rw [key]
    exact (hp.isInfinitesimal_sub_C_std.mul_right hq).add
      (hq.isInfinitesimal_sub_C_std.mul_left (isFinite_C _))
  have := hinf.std_eq_zero
  rwa [std_sub, std_C, sub_eq_zero] at this

/-! ### The finite subring and the standard-part map -/

/-- The subring of finite elements. Membership is decidable. -/
def finiteSubring : Subring (Poly Γ R) where
  carrier := {p | p.IsFinite}
  mul_mem' := IsFinite.mul
  one_mem' := isFinite_one
  add_mem' := IsFinite.add
  zero_mem' := isFinite_zero
  neg_mem' := IsFinite.neg

@[simp] theorem mem_finiteSubring {p : Poly Γ R} : p ∈ finiteSubring ↔ p.IsFinite := Iff.rfl

instance : DecidablePred (· ∈ (finiteSubring : Subring (Poly Γ R))) := fun p =>
  inferInstanceAs (Decidable p.IsFinite)

/-- The standard part of a finite element: its coefficient at `ε^0`. Computable. -/
def stdPart : (finiteSubring : Subring (Poly Γ R)) →+* R where
  toFun p := p.1.std
  map_zero' := std_zero
  map_one' := std_one
  map_add' p q := std_add p.1 q.1
  map_mul' p q := std_mul p.2 q.2

@[simp] theorem stdPart_apply (p : (finiteSubring : Subring (Poly Γ R))) :
    stdPart p = p.1.std := rfl

@[simp] theorem stdPart_C (r : R) :
    stdPart (⟨C r, isFinite_C r⟩ : (finiteSubring : Subring (Poly Γ R))) = r := std_C r

theorem isInfinitesimal_sub_C_stdPart (p : (finiteSubring : Subring (Poly Γ R))) :
    (p.1 - C (stdPart p)).IsInfinitesimal :=
  p.2.isInfinitesimal_sub_C_std

/-- The kernel of `stdPart` is exactly the infinitesimals. -/
theorem mem_ker_stdPart {p : (finiteSubring : Subring (Poly Γ R))} :
    p ∈ RingHom.ker stdPart ↔ p.1.IsInfinitesimal := by
  rw [RingHom.mem_ker, stdPart_apply, p.2.isInfinitesimal_iff_std_eq_zero]

/-- The infinitesimals, as an ideal of the finite subring (the kernel of `stdPart`). -/
def infinitesimalIdeal : Ideal (finiteSubring : Subring (Poly Γ R)) := RingHom.ker stdPart

theorem mem_infinitesimalIdeal {p : (finiteSubring : Subring (Poly Γ R))} :
    p ∈ infinitesimalIdeal ↔ p.1.IsInfinitesimal :=
  mem_ker_stdPart

/-! ### `ε` -/

theorem leadExp_ε [One Γ] [NeZero (1 : R)] : (ε : Poly Γ R).leadExp = (1 : Γ) :=
  leadExp_single one_ne_zero

theorem isInfinitesimal_ε [One Γ] [NeZero (1 : R)] (h : (0 : Γ) < 1) :
    (ε : Poly Γ R).IsInfinitesimal := by
  rw [IsInfinitesimal, leadExp_ε]; exact WithTop.coe_lt_coe.2 h

theorem std_ε [One Γ] (h : (0 : Γ) < 1) : (ε : Poly Γ R).std = 0 := by
  simp [std, ε, h.ne]

/-! ### Order characterizations -/

section Order
variable [LinearOrder R] [IsStrictOrderedRing R]

theorem lt_iff_exists_coeff {p q : Poly Γ R} :
    p < q ↔ ∃ i, (∀ j < i, p.coeff j = q.coeff j) ∧ p.coeff i < q.coeff i := by
  rw [lt_def, HahnSeries.lt_iff]
  simp only [ofLex_toLex, coeff_eq]

theorem leadCoeff_pos_iff {p : Poly Γ R} : 0 < p.leadCoeff ↔ 0 < p := by
  rw [leadCoeff_eq_leadingCoeff, lt_def, map_zero]
  exact HahnSeries.leadingCoeff_pos_iff

@[simp] theorem leadExp_abs (p : Poly Γ R) : |p|.leadExp = p.leadExp := by
  rw [leadExp_eq_orderTop, leadExp_eq_orderTop]
  have := orderTop_abs (toLexHahn p)
  rwa [← toLexHahn_abs] at this

@[simp] theorem isFinite_abs {p : Poly Γ R} : |p|.IsFinite ↔ p.IsFinite := by
  rw [IsFinite, IsFinite, leadExp_abs]

@[simp] theorem isInfinitesimal_abs {p : Poly Γ R} :
    |p|.IsInfinitesimal ↔ p.IsInfinitesimal := by
  rw [IsInfinitesimal, IsInfinitesimal, leadExp_abs]

/-- If `p` has a negative or zero leading exponent `e`, it exceeds `C r` as soon as `r` is below
the coefficient of `p` at `0` (vacuous when `e < 0`). -/
private theorem C_lt_of_leadExp {p : Poly Γ R} {e : Γ} (he : p.leadExp = e) (he0 : e ≤ 0) {r : R}
    (hr : (if e = 0 then r else 0) < p.leadCoeff) : C r < p := by
  rw [lt_iff_exists_coeff]
  refine ⟨e, fun j hj => ?_, ?_⟩
  · rw [coeff_C, ite_eq_right (hj.trans_le he0).ne,
      coeff_eq_zero_of_lt_leadExp (he ▸ WithTop.coe_lt_coe.2 hj)]
  · rwa [coeff_C, coeff_leadExp he]

/-- Finite elements are exactly those bounded by a standard element. -/
theorem isFinite_iff_exists_abs_le {p : Poly Γ R} : p.IsFinite ↔ ∃ r : R, |p| ≤ C r := by
  constructor
  · intro hp
    refine ⟨|p|.std + 1, le_of_lt ?_⟩
    rw [lt_iff_exists_coeff]
    refine ⟨0, fun j hj => ?_, ?_⟩
    · rw [coeff_C, ite_eq_right hj.ne, coeff_eq_zero_of_lt_leadExp]
      rw [leadExp_abs]
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 hj) hp
    · rw [coeff_C, ite_eq_left rfl]
      exact lt_add_one _
  · rintro ⟨r, hr⟩
    by_contra hp
    have hlt : p.leadExp < 0 := lt_of_not_ge hp
    obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.1 (hlt.trans (WithTop.coe_lt_top (0 : Γ))).ne
    have he0 : e < 0 := WithTop.coe_lt_coe.1 (he ▸ hlt)
    have hp0 : p ≠ 0 := by rintro rfl; exact hp isFinite_zero
    refine hr.not_gt (C_lt_of_leadExp (by rw [leadExp_abs, he]) he0.le ?_)
    rw [ite_eq_right he0.ne]
    exact leadCoeff_pos_iff.2 (abs_pos.2 hp0)

/-- Infinitesimals are exactly the elements smaller in absolute value than every positive
standard element. Needs `R` densely ordered (e.g. a field); see the module docstring. -/
theorem isInfinitesimal_iff_forall_abs_lt [DenselyOrdered R] {p : Poly Γ R} :
    p.IsInfinitesimal ↔ ∀ r : R, 0 < r → |p| < C r := by
  constructor
  · intro hp r hr
    rw [lt_iff_exists_coeff]
    refine ⟨0, fun j hj => ?_, ?_⟩
    · rw [coeff_C, ite_eq_right hj.ne, coeff_eq_zero_of_lt_leadExp]
      rw [leadExp_abs]
      exact (WithTop.coe_lt_coe.2 hj).trans hp
    · rw [coeff_C, ite_eq_left rfl, coeff_eq_zero_of_lt_leadExp (by rw [leadExp_abs]; exact hp)]
      exact hr
  · intro h
    by_contra hp
    have hle : p.leadExp ≤ 0 := le_of_not_gt hp
    obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.1 (hle.trans_lt (WithTop.coe_lt_top (0 : Γ))).ne
    have he0 : e ≤ 0 := WithTop.coe_le_coe.1 (he ▸ hle)
    have hp0 : p ≠ 0 := by rintro rfl; exact hp isInfinitesimal_zero
    have hc : 0 < |p|.leadCoeff := leadCoeff_pos_iff.2 (abs_pos.2 hp0)
    obtain ⟨r, hr0, hrc⟩ := exists_between hc
    refine (h r hr0).not_gt (C_lt_of_leadExp (by rw [leadExp_abs, he]) he0 ?_)
    split_ifs
    exacts [hrc, hc]

end Order

end Ring

end Poly

end LeviCivita
