/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Geometry.LazySign
import Mathlib.RingTheory.HahnSeries.Summable

/-!
# Precision-tracked approximations

`Approx Γ R` is a Levi-Civita number known up to `O(ε^prec)`: a `Poly` (the known part) and a
precision `prec : WithTop Γ` (`⊤` = exact). `a.Represents x` says that the Hahn series `x`
agrees with the known part at every exponent `< prec`. Equivalently
(`represents_iff_le_orderTop`) `prec ≤ (x - toHahn a.val).orderTop`, the "`x = val + O(ε^prec)`"
reading, which makes every soundness proof a valuation estimate.

* Truncation: `Poly.truncTop` (`Poly.truncLT` extended to `WithTop Γ`), `truncLT_truncLT`,
  `Represents.mono`, `exact`, `ofPoly`, `withPrec`.
* `HahnSeries.coeff_mul_eq_of_agree`: the coefficients of `x * y` below `c` only depend on the
  coefficients of `x` below `c - ord y` and of `y` below `c - ord x`
  (`truncLT_mul_of_orderTop` is the `truncLT` form, in the group setting).
* Sound arithmetic with p-adic precision rules: `add`, `neg`, `sub`, `mul`
  (`prec = min (pa + ord b) (pb + ord a)`, with `ord a = min (leadExp a.val) a.prec`).
* `inv?` (`R` a field, `Γ` a group): Newton iteration for a candidate inverse, whose precision is
  then **certified by a residual computation**; soundness does not depend on the iteration.
* `sign?` and `decidePos?`: the certified sign, `accept | reject | unresolved`.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita

open HahnSeries

/-! ### Hahn series: agreement below a precision -/

namespace HahnSeries

variable {Γ R : Type*}

section Agree
variable [LinearOrder Γ] [AddCommGroup R]

/-- Agreement below `c` is a valuation bound on the difference. -/
theorem agree_iff_le_orderTop {x y : R⟦Γ⟧} {c : WithTop Γ} :
    (∀ g : Γ, (g : WithTop Γ) < c → x.coeff g = y.coeff g) ↔ c ≤ (x - y).orderTop := by
  rw [le_orderTop_iff_forall]
  simp only [coeff_sub, sub_eq_zero]

end Agree

section Mul
variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]

/-- If all coefficients of `z` at `g` with `g + o < c` vanish, then `c ≤ ord z + o`. -/
theorem le_orderTop_add_of_coeff {z : R⟦Γ⟧} {o c : WithTop Γ}
    (h : ∀ g : Γ, (g : WithTop Γ) + o < c → z.coeff g = 0) : c ≤ z.orderTop + o := by
  by_cases hz : z = 0
  · simp [hz]
  · obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.1 (orderTop_ne_top.2 hz)
    rw [← hg]
    by_contra hlt
    exact coeff_orderTop_ne hg.symm (h g (not_le.1 hlt))

/-- **Our `truncLT_mul`** (valuation form). If `x` and `x'` agree below `c - oy`, `y` and `y'`
agree below `c - ox`, `ox ≤ ord x'` and `oy ≤ ord y`, then `x * y` and `x' * y'` agree below `c`.
Stated with `g + o < c` instead of `g < c - o`, so it holds over any ordered cancel monoid. -/
theorem coeff_mul_eq_of_agree {x x' y y' : R⟦Γ⟧} {ox oy c : WithTop Γ}
    (hx' : ox ≤ x'.orderTop) (hy : oy ≤ y.orderTop)
    (hxx : ∀ g : Γ, (g : WithTop Γ) + oy < c → x.coeff g = x'.coeff g)
    (hyy : ∀ g : Γ, (g : WithTop Γ) + ox < c → y.coeff g = y'.coeff g) :
    ∀ g : Γ, (g : WithTop Γ) < c → (x * y).coeff g = (x' * y').coeff g := by
  rw [agree_iff_le_orderTop]
  have h1 : c ≤ (x - x').orderTop + oy :=
    le_orderTop_add_of_coeff fun g hg => by rw [coeff_sub, hxx g hg, sub_self]
  have h2 : c ≤ (y - y').orderTop + ox :=
    le_orderTop_add_of_coeff fun g hg => by rw [coeff_sub, hyy g hg, sub_self]
  have e : x * y - x' * y' = (x - x') * y + x' * (y - y') := by ring
  rw [e]
  refine le_trans (le_min ?_ ?_) min_orderTop_le_orderTop_add
  · exact h1.trans ((add_le_add le_rfl hy).trans orderTop_add_le_mul)
  · rw [add_comm] at h2
    exact h2.trans ((add_le_add hx' le_rfl).trans orderTop_add_le_mul)

theorem orderTop_le_orderTop_truncLT [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧) :
    x.orderTop ≤ (truncLT c x).orderTop := by
  rw [le_orderTop_iff_forall]
  intro j hj
  rw [_root_.HahnSeries.coeff_truncLT, coeff_eq_zero_of_lt_orderTop hj, ite_self]

end Mul

section Group
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [CommRing R]

/-- **`truncLT_mul`, group form.** If `ox ≤ ord x` and `oy ≤ ord y`, the coefficients of `x * y`
below `c` only depend on the coefficients of `x` below `c - oy` and of `y` below `c - ox`. -/
theorem coeff_mul_eq_of_agree_sub {x x' y y' : R⟦Γ⟧} {ox oy c : Γ}
    (hx' : (ox : WithTop Γ) ≤ x'.orderTop) (hy : (oy : WithTop Γ) ≤ y.orderTop)
    (hxx : ∀ g : Γ, g < c - oy → x.coeff g = x'.coeff g)
    (hyy : ∀ g : Γ, g < c - ox → y.coeff g = y'.coeff g) :
    ∀ g : Γ, g < c → (x * y).coeff g = (x' * y').coeff g := by
  have := coeff_mul_eq_of_agree (c := (c : WithTop Γ)) hx' hy
    (fun g hg => hxx g (lt_sub_iff_add_lt.2 (by exact_mod_cast hg)))
    (fun g hg => hyy g (lt_sub_iff_add_lt.2 (by exact_mod_cast hg)))
  exact fun g hg => this g (by exact_mod_cast hg)

/-- `truncLT` form: `[x * y]_{<c} = [[x]_{<c-oy} * [y]_{<c-ox}]_{<c}` when `ox ≤ ord x`,
`oy ≤ ord y`. With `ox = oy = 0` this is M3's `truncLT_mul` for finite elements. -/
theorem truncLT_mul_of_orderTop [DecidableLT Γ] {x y : R⟦Γ⟧} {ox oy : Γ} (c : Γ)
    (hx : (ox : WithTop Γ) ≤ x.orderTop) (hy : (oy : WithTop Γ) ≤ y.orderTop) :
    truncLT c (x * y) = truncLT c (truncLT (c - oy) x * truncLT (c - ox) y) := by
  ext g
  rw [_root_.HahnSeries.coeff_truncLT, _root_.HahnSeries.coeff_truncLT]
  split_ifs with hg
  · refine coeff_mul_eq_of_agree_sub (hx.trans (orderTop_le_orderTop_truncLT _ _)) hy
      (fun g hg => ?_) (fun g hg => ?_) g hg
    · rw [_root_.HahnSeries.coeff_truncLT, ite_eq_left hg]
    · rw [_root_.HahnSeries.coeff_truncLT, ite_eq_left hg]
  · rfl

end Group

end HahnSeries

/-! ### `Poly`: truncation at a `WithTop` precision -/

namespace Poly

variable {Γ R : Type*}

section Trunc
variable [LinearOrder Γ] [Zero R]

/-- `truncLT` at a precision in `WithTop Γ` (`⊤`: no truncation). -/
def truncTop (c : WithTop Γ) (p : Poly Γ R) : Poly Γ R :=
  match c with
  | ⊤ => p
  | (c : Γ) => p.truncLT c

@[simp] theorem truncTop_top (p : Poly Γ R) : p.truncTop ⊤ = p := rfl

@[simp] theorem truncTop_coe (c : Γ) (p : Poly Γ R) : p.truncTop c = p.truncLT c := rfl

end Trunc

section Ring
variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
  [DecidableEq R]

theorem truncLT_truncLT (a b : Γ) (p : Poly Γ R) :
    (p.truncLT a).truncLT b = p.truncLT (min a b) := by
  ext1
  simp only [terms_truncLT, List.filter_filter, lt_min_iff]
  congr 1
  funext t
  exact Bool.and_comm _ _

theorem coeff_truncTop (c : WithTop Γ) (p : Poly Γ R) (g : Γ) :
    (p.truncTop c).coeff g = if (g : WithTop Γ) < c then p.coeff g else 0 := by
  cases c with
  | top => simp
  | coe c => simp [coeff_truncLT]

theorem truncTop_truncTop (a b : WithTop Γ) (p : Poly Γ R) :
    (p.truncTop a).truncTop b = p.truncTop (min a b) :=
  coeff_injective (funext fun g => by
    simp only [coeff_truncTop, lt_min_iff]
    by_cases ha : (g : WithTop Γ) < a <;> by_cases hb : (g : WithTop Γ) < b <;> simp [ha, hb])

/-- Truncated multiplication at a `WithTop` precision. -/
def mulTruncTop (c : WithTop Γ) (p q : Poly Γ R) : Poly Γ R :=
  match c with
  | ⊤ => p * q
  | (c : Γ) => mulTrunc c p q

theorem mulTruncTop_eq (c : WithTop Γ) (p q : Poly Γ R) :
    mulTruncTop c p q = (p * q).truncTop c := by
  cases c with
  | top => rfl
  | coe c => exact mulTrunc_eq c p q

theorem leadExp_le_orderTop_toHahn (p : Poly Γ R) : p.leadExp ≤ (toHahn p).orderTop :=
  (leadExp_eq_orderTop p).le

end Ring

end Poly

/-! ### Approximations -/

/-- A Levi-Civita number known up to `O(ε^prec)`: the known part `val` and the precision `prec`
(`⊤` = exact). Terms of `val` at exponents `≥ prec` carry no information; all operations below
truncate them away. -/
structure Approx (Γ R : Type*) [LinearOrder Γ] [Zero R] where
  /-- The known part. -/
  val : Poly Γ R
  /-- The absolute precision: `val` is correct at all exponents `< prec`. -/
  prec : WithTop Γ

namespace Approx

open Poly

variable {Γ R : Type*}

instance [LinearOrder Γ] [Zero R] [Repr Γ] [Repr R] : Repr (Approx Γ R) where
  reprPrec a _ :=
    match a.prec with
    | ⊤ => repr a.val
    | (c : Γ) => repr a.val ++ " + O(ε^" ++ repr c ++ ")"

section Defs
variable [LinearOrder Γ] [Zero R]

theorem ext_iff' {a b : Approx Γ R} : a = b ↔ a.val = b.val ∧ a.prec = b.prec := by
  cases a; cases b; simp

instance [DecidableEq R] : DecidableEq (Approx Γ R) := fun _ _ =>
  decidable_of_iff _ ext_iff'.symm

/-- The exact approximation of a `Poly`. -/
def exact (p : Poly Γ R) : Approx Γ R := ⟨p, ⊤⟩

/-- The lower bound `min (leadExp val) prec` on the order of any represented series. -/
def ord (a : Approx Γ R) : WithTop Γ := min a.val.leadExp a.prec

/-- The leading term of the known part is below the precision, so it is the leading term of
every represented series (`Represents.orderTop_eq`, `Represents.leadingCoeff_eq`). -/
def Certified (a : Approx Γ R) : Prop := a.val.leadExp < a.prec

instance (a : Approx Γ R) : Decidable a.Certified := inferInstanceAs (Decidable (_ < _))

end Defs

section Ring
variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
  [DecidableEq R]

/-- `x` agrees with the known part of `a` at every exponent below `a.prec`. -/
def Represents (a : Approx Γ R) (x : R⟦Γ⟧) : Prop :=
  ∀ g : Γ, (g : WithTop Γ) < a.prec → x.coeff g = (toHahn a.val).coeff g

/-- `x = val + O(ε^prec)`. -/
theorem represents_iff_le_orderTop {a : Approx Γ R} {x : R⟦Γ⟧} :
    a.Represents x ↔ a.prec ≤ (x - toHahn a.val).orderTop :=
  HahnSeries.agree_iff_le_orderTop

/-- For a finite precision, `Represents` is equality of Mathlib truncations. -/
theorem represents_iff_truncLT {a : Approx Γ R} {x : R⟦Γ⟧} {c : Γ} (hc : a.prec = c) :
    a.Represents x ↔ HahnSeries.truncLT c x = HahnSeries.truncLT c (toHahn a.val) := by
  rw [Represents, hc, HahnSeries.ext_iff]
  refine ⟨fun h => funext fun g => ?_, fun h g hg => ?_⟩
  · rw [_root_.HahnSeries.coeff_truncLT, _root_.HahnSeries.coeff_truncLT]
    split_ifs with hg
    · exact h g (WithTop.coe_lt_coe.2 hg)
    · rfl
  · have := congrFun h g
    rwa [_root_.HahnSeries.coeff_truncLT, _root_.HahnSeries.coeff_truncLT, ite_eq_left (WithTop.coe_lt_coe.1 hg), ite_eq_left
      (WithTop.coe_lt_coe.1 hg)] at this

/-- If the known part has no terms at or above `prec` (e.g. after `withPrec`), `Represents` is
`truncLT c x = toHahn val`, the formulation of the plan. -/
theorem represents_iff_truncLT_eq {a : Approx Γ R} {x : R⟦Γ⟧} {c : Γ} (hc : a.prec = c)
    (hv : a.val.truncLT c = a.val) :
    a.Represents x ↔ HahnSeries.truncLT c x = toHahn a.val := by
  rw [represents_iff_truncLT hc, ← toHahn_truncLT, hv]

/-- With precision `⊤`, `Represents` is equality. -/
theorem represents_top_iff {p : Poly Γ R} {x : R⟦Γ⟧} :
    (⟨p, ⊤⟩ : Approx Γ R).Represents x ↔ x = toHahn p := by
  rw [Represents]
  exact ⟨fun h => HahnSeries.ext (funext fun g => h g (WithTop.coe_lt_top g)),
    fun h g _ => h ▸ rfl⟩

theorem represents_exact (p : Poly Γ R) : (exact p).Represents (toHahn p) :=
  represents_top_iff.2 rfl

theorem represents_exact_iff {p : Poly Γ R} {x : R⟦Γ⟧} :
    (exact p).Represents x ↔ x = toHahn p := represents_top_iff

/-- Lowering the precision preserves `Represents`. -/
theorem Represents.mono {a : Approx Γ R} {x : R⟦Γ⟧} (h : a.Represents x) {c : WithTop Γ}
    (hc : c ≤ a.prec) : (⟨a.val, c⟩ : Approx Γ R).Represents x :=
  fun g hg => h g (hg.trans_le hc)

/-- Dropping the terms of `val` at or above some `c ≥ prec` does not change `Represents`. -/
theorem represents_truncTop_iff {p : Poly Γ R} {c P : WithTop Γ} (hc : P ≤ c) {x : R⟦Γ⟧} :
    (⟨p.truncTop c, P⟩ : Approx Γ R).Represents x ↔ (⟨p, P⟩ : Approx Γ R).Represents x := by
  simp only [Represents, ← coeff_eq, coeff_truncTop]
  refine forall_congr' fun g => imp_congr_right fun hg => ?_
  rw [ite_eq_left (hg.trans_le hc)]

/-- Every represented series has order at least `a.ord = min (leadExp val) prec`. -/
theorem Represents.ord_le {a : Approx Γ R} {x : R⟦Γ⟧} (h : a.Represents x) :
    a.ord ≤ x.orderTop := by
  have e : x = (x - toHahn a.val) + toHahn a.val := by abel
  rw [e]
  refine le_trans ?_ min_orderTop_le_orderTop_add
  rw [ord, min_comm]
  exact min_le_min (represents_iff_le_orderTop.1 h) (leadExp_le_orderTop_toHahn _)

/-- A certified approximation determines the order of the series. -/
theorem Represents.orderTop_eq {a : Approx Γ R} {x : R⟦Γ⟧} (h : a.Represents x)
    (hc : a.Certified) : x.orderTop = a.val.leadExp := by
  have e : x = toHahn a.val + (x - toHahn a.val) := by abel
  have hlt : (toHahn a.val).orderTop < (x - toHahn a.val).orderTop := by
    rw [← leadExp_eq_orderTop]; exact hc.trans_le (represents_iff_le_orderTop.1 h)
  rw [e, orderTop_add_eq_left hlt, leadExp_eq_orderTop]

/-- A certified approximation determines the leading coefficient of the series. -/
theorem Represents.leadingCoeff_eq {a : Approx Γ R} {x : R⟦Γ⟧} (h : a.Represents x)
    (hc : a.Certified) : x.leadingCoeff = a.val.leadCoeff := by
  have e : x = toHahn a.val + (x - toHahn a.val) := by abel
  have hlt : (toHahn a.val).orderTop < (x - toHahn a.val).orderTop := by
    rw [← leadExp_eq_orderTop]; exact hc.trans_le (represents_iff_le_orderTop.1 h)
  rw [e, leadingCoeff_add_eq_left hlt, leadCoeff_eq_leadingCoeff]

theorem Represents.ne_zero {a : Approx Γ R} {x : R⟦Γ⟧} (h : a.Represents x)
    (hc : a.Certified) : x ≠ 0 := by
  intro hx
  have := h.orderTop_eq hc
  rw [hx, orderTop_zero] at this
  exact (lt_top_iff_ne_top.1 (hc.trans_le le_top)) this.symm

/-! #### Truncation API -/

/-- An approximation of `p` at precision `c` (the terms at or above `c` are dropped). -/
def ofPoly (p : Poly Γ R) (c : WithTop Γ) : Approx Γ R := ⟨p.truncTop c, c⟩

theorem represents_ofPoly (p : Poly Γ R) (c : WithTop Γ) : (ofPoly p c).Represents (toHahn p) :=
  (represents_truncTop_iff le_rfl).2 ((represents_exact p).mono le_top)

/-- Lower the precision to `min c a.prec` and drop the terms that become meaningless. -/
def withPrec (c : WithTop Γ) (a : Approx Γ R) : Approx Γ R :=
  ⟨a.val.truncTop (min c a.prec), min c a.prec⟩

theorem Represents.withPrec {a : Approx Γ R} {x : R⟦Γ⟧} (h : a.Represents x) (c : WithTop Γ) :
    (a.withPrec c).Represents x :=
  (represents_truncTop_iff le_rfl).2 (h.mono (min_le_right _ _))

@[simp] theorem withPrec_prec (c : WithTop Γ) (a : Approx Γ R) :
    (a.withPrec c).prec = min c a.prec := rfl

/-! #### Arithmetic -/

/-- Sum: precision `min pa pb`. -/
def add (a b : Approx Γ R) : Approx Γ R :=
  ⟨(a.val + b.val).truncTop (min a.prec b.prec), min a.prec b.prec⟩

/-- Negation: same precision. -/
def neg (a : Approx Γ R) : Approx Γ R := ⟨-a.val, a.prec⟩

/-- Difference: precision `min pa pb`. -/
def sub (a b : Approx Γ R) : Approx Γ R :=
  ⟨(a.val - b.val).truncTop (min a.prec b.prec), min a.prec b.prec⟩

/-- The precision of a product: `min (pa + ord b) (pb + ord a)`. -/
def mulPrec (a b : Approx Γ R) : WithTop Γ := min (a.prec + b.ord) (b.prec + a.ord)

/-- Product, with the relative-precision rule `min (pa + ord b) (pb + ord a)`. Only the terms of
the product below that precision are computed (`mulTrunc`). -/
def mul (a b : Approx Γ R) : Approx Γ R :=
  ⟨mulTruncTop (mulPrec a b) a.val b.val, mulPrec a b⟩

instance : Add (Approx Γ R) := ⟨add⟩
instance : Neg (Approx Γ R) := ⟨neg⟩
instance : Sub (Approx Γ R) := ⟨sub⟩
instance : Mul (Approx Γ R) := ⟨mul⟩

theorem add_def (a b : Approx Γ R) : a + b = add a b := rfl
theorem neg_def (a : Approx Γ R) : -a = neg a := rfl
theorem sub_def (a b : Approx Γ R) : a - b = sub a b := rfl
theorem mul_def (a b : Approx Γ R) : a * b = mul a b := rfl

@[simp] theorem add_prec (a b : Approx Γ R) : (a + b).prec = min a.prec b.prec := rfl
@[simp] theorem neg_prec (a : Approx Γ R) : (-a).prec = a.prec := rfl
@[simp] theorem sub_prec (a b : Approx Γ R) : (a - b).prec = min a.prec b.prec := rfl
@[simp] theorem mul_prec (a b : Approx Γ R) : (a * b).prec = mulPrec a b := rfl

theorem Represents.add {a b : Approx Γ R} {x y : R⟦Γ⟧} (ha : a.Represents x)
    (hb : b.Represents y) : (a + b).Represents (x + y) := by
  refine (represents_truncTop_iff le_rfl).2 (represents_iff_le_orderTop.2 ?_)
  have e : x + y - toHahn (a.val + b.val) = (x - toHahn a.val) + (y - toHahn b.val) := by
    rw [map_add]; abel
  rw [e]
  exact (min_le_min (represents_iff_le_orderTop.1 ha) (represents_iff_le_orderTop.1 hb)).trans
    min_orderTop_le_orderTop_add

theorem Represents.neg {a : Approx Γ R} {x : R⟦Γ⟧} (ha : a.Represents x) :
    (-a).Represents (-x) := by
  refine represents_iff_le_orderTop.2 ?_
  have e : -x - toHahn (-a.val) = -(x - toHahn a.val) := by rw [map_neg]; abel
  rw [neg_def, Approx.neg, e, orderTop_neg]
  exact represents_iff_le_orderTop.1 ha

theorem Represents.sub {a b : Approx Γ R} {x y : R⟦Γ⟧} (ha : a.Represents x)
    (hb : b.Represents y) : (a - b).Represents (x - y) := by
  refine (represents_truncTop_iff le_rfl).2 (represents_iff_le_orderTop.2 ?_)
  have e : x - y - toHahn (a.val - b.val) = (x - toHahn a.val) - (y - toHahn b.val) := by
    rw [map_sub]; abel
  rw [e]
  exact (min_le_min (represents_iff_le_orderTop.1 ha) (represents_iff_le_orderTop.1 hb)).trans
    min_orderTop_le_orderTop_sub

/-- The product rule before truncation: `x * y = va * vb + O(ε^(min (pa + ord b) (pb + ord a)))`.
This is `HahnSeries.coeff_mul_eq_of_agree` with `x' = va`, `y' = y`, then `y' = vb`. -/
theorem represents_mul_val {a b : Approx Γ R} {x y : R⟦Γ⟧} (ha : a.Represents x)
    (hb : b.Represents y) : (⟨a.val * b.val, mulPrec a b⟩ : Approx Γ R).Represents (x * y) := by
  refine represents_iff_le_orderTop.2 ?_
  have e : x * y - toHahn (a.val * b.val) =
      (x - toHahn a.val) * y + toHahn a.val * (y - toHahn b.val) := by
    rw [map_mul]; ring
  rw [e]
  refine le_trans (min_le_min ?_ ?_) min_orderTop_le_orderTop_add
  · exact (add_le_add (represents_iff_le_orderTop.1 ha) hb.ord_le).trans orderTop_add_le_mul
  · rw [add_comm]
    refine (add_le_add ((min_le_left _ _).trans (leadExp_le_orderTop_toHahn _))
      (represents_iff_le_orderTop.1 hb)).trans orderTop_add_le_mul

theorem Represents.mul {a b : Approx Γ R} {x y : R⟦Γ⟧} (ha : a.Represents x)
    (hb : b.Represents y) : (a * b).Represents (x * y) := by
  rw [mul_def, Approx.mul, mulTruncTop_eq]
  exact (represents_truncTop_iff le_rfl).2 (represents_mul_val ha hb)

/-- Multiplication by an exact factor: precision `pa + ord q`. -/
theorem Represents.mul_exact {a : Approx Γ R} {x : R⟦Γ⟧} (ha : a.Represents x) (q : Poly Γ R) :
    (⟨mulTruncTop (a.prec + q.leadExp) a.val q, a.prec + q.leadExp⟩ : Approx Γ R).Represents
      (x * toHahn q) := by
  rw [mulTruncTop_eq]
  refine (represents_truncTop_iff le_rfl).2 ?_
  have h := represents_mul_val ha (represents_exact q)
  refine h.mono ?_
  simp only [mulPrec, exact, ord, min_top_right, WithTop.top_add, le_refl]

end Ring

/-! ### Certified sign: `accept | reject | unresolved` -/

section SignDef
variable [LinearOrder Γ] [Zero R] [LinearOrder R]

/-- The sign of the represented series, if the approximation determines it: always for exact
approximations, otherwise exactly when the leading term of the known part is below the precision.
`none` means "unresolved: raise the precision and retry". -/
def sign? (a : Approx Γ R) : Option ℤ :=
  if a.prec = ⊤ ∨ a.Certified then some a.val.sign else none

theorem sign?_exact (p : Poly Γ R) : (exact p).sign? = some p.sign :=
  ite_eq_left (Or.inl rfl)

theorem sign?_of_certified {a : Approx Γ R} (h : a.Certified) : a.sign? = some a.val.sign :=
  ite_eq_left (Or.inr h)

theorem sign?_eq_none_iff {a : Approx Γ R} : a.sign? = none ↔ a.prec ≠ ⊤ ∧ ¬a.Certified := by
  rw [sign?, ite_eq_right_iff]
  simp [not_or]

/-- The outcome of a certified positivity test. -/
inductive Verdict
  /-- The represented number is certainly positive. -/
  | accept
  /-- The represented number is certainly `≤ 0`. -/
  | reject
  /-- The precision is insufficient to decide. -/
  | unresolved
  deriving DecidableEq, Repr

/-- Certified test of `0 < x`. -/
def decidePos? (a : Approx Γ R) : Verdict :=
  match a.sign? with
  | none => .unresolved
  | some s => if s = 1 then .accept else .reject

theorem decidePos?_exact_ne (p : Poly Γ R) : (exact p).decidePos? ≠ .unresolved := by
  unfold decidePos?
  rw [sign?_exact]
  dsimp only
  split_ifs <;> simp

end SignDef

section Sign
variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
  [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq R]

/-- When `sign?` answers, the represented series has the leading coefficient of the known part. -/
theorem Represents.leadingCoeff_eq_of_sign? {a : Approx Γ R} {x : R⟦Γ⟧} {s : ℤ}
    (ha : a.Represents x) (hs : a.sign? = some s) :
    s = a.val.sign ∧ x.leadingCoeff = (toHahn a.val).leadingCoeff := by
  unfold sign? at hs
  split_ifs at hs with h
  · refine ⟨(Option.some.inj hs).symm, ?_⟩
    rcases h with h | h
    · obtain ⟨v, p⟩ := a
      cases h
      rw [represents_top_iff.1 ha]
    · rw [ha.leadingCoeff_eq h, leadCoeff_eq_leadingCoeff]

/-- **Soundness of `sign?`.** If it answers `some s`, then `s` is the sign of every represented
series in the lexicographic order of `Lex R⟦Γ⟧`. -/
theorem sign?_sound {a : Approx Γ R} {x : R⟦Γ⟧} {s : ℤ} (hs : a.sign? = some s)
    (ha : a.Represents x) :
    (s = 1 ↔ 0 < toLex x) ∧ (s = -1 ↔ toLex x < 0) ∧ (s = 0 ↔ x = 0) := by
  obtain ⟨rfl, hl⟩ := ha.leadingCoeff_eq_of_sign? hs
  refine ⟨?_, ?_, ?_⟩
  · rw [sign_eq_one_iff, ← leadingCoeff_pos_iff, ← leadingCoeff_pos_iff, ofLex_toLex,
      ofLex_toLex, hl]
  · rw [sign_eq_neg_one_iff, ← leadingCoeff_neg_iff, ← leadingCoeff_neg_iff, ofLex_toLex,
      ofLex_toLex, hl]
  · rw [sign_eq_zero_iff, ← leadingCoeff_eq_zero, hl, leadingCoeff_eq_zero, ← map_zero toHahn,
      toHahn_injective.eq_iff]

theorem decidePos?_accept {a : Approx Γ R} {x : R⟦Γ⟧} (h : a.decidePos? = .accept)
    (ha : a.Represents x) : 0 < toLex x := by
  unfold decidePos? at h
  split at h
  · cases h
  · rename_i s hs
    split_ifs at h with h1
    exact (sign?_sound hs ha).1.1 h1

theorem decidePos?_reject {a : Approx Γ R} {x : R⟦Γ⟧} (h : a.decidePos? = .reject)
    (ha : a.Represents x) : toLex x ≤ 0 := by
  unfold decidePos? at h
  split at h
  · cases h
  · rename_i s hs
    split_ifs at h with h1
    exact not_lt.1 fun hx => h1 ((sign?_sound hs ha).1.2 hx)

end Sign

/-! ### Inverse (`R` a field, `Γ` a group)

`inv?` computes a candidate `y ≈ x⁻¹` by Newton iteration and then **certifies** its precision
from the residual `1 - x y`: since `x⁻¹ - y = x⁻¹ (1 - x y)`,
`ord (x⁻¹ - y) = -ord x + ord (1 - x y)`, and `ord (1 - x y)` is bounded below by the order of a
sound approximation of `1 - x y`. The soundness theorem therefore holds for *any* candidate; the
Newton iteration only affects how good the certified precision is. -/

section Inv
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R] [DecidableEq R]

/-- `n` Newton steps `y ↦ y (2 - u y)` for `1 / u` from `y = 1`, truncated at precision `q`. For
`u = 1 + δ` with `0 < ord δ`, step `k` is correct below `min q (2^k ord δ)`. -/
def newtonInv (q : WithTop Γ) (u : Poly Γ R) : ℕ → Poly Γ R
  | 0 => 1
  | n + 1 =>
    let y := newtonInv q u n
    mulTruncTop q y (2 - mulTruncTop q u y)

/-- The certified precision of a candidate inverse `y` of `x ≈ a` with `ord x = e`:
`-e + ord(1 - x y)`, where `1 - x y` is approximated by `1 - a.val * y` at precision
`a.prec + ord y`. -/
def invPrec (a : Approx Γ R) (e : Γ) (y : Poly Γ R) : WithTop Γ :=
  let P := a.prec + y.leadExp
  min (1 - mulTruncTop P a.val y).leadExp P + ((-e : Γ) : WithTop Γ)

/-- The inverse given the leading exponent `e` and coefficient `r` of the known part: normalize
to `u = x / (r ε^e) = 1 + δ` (relative precision `a.prec - e`), run `n` Newton steps, scale back,
and certify the precision by the residual (`invPrec`). -/
def invCore (n : ℕ) (a : Approx Γ R) (e : Γ) (r : R) : Approx Γ R :=
  let s : Poly Γ R := single (-e) r⁻¹
  let q : WithTop Γ := a.prec + ((-e : Γ) : WithTop Γ)
  let y := s * newtonInv q (mulTruncTop q a.val s) n
  ⟨y.truncTop (invPrec a e y), invPrec a e y⟩

/-- Certified inverse with `n` Newton steps; `none` if the leading term of the known part is not
certified (then `x` might be `0`, and its order is unknown). -/
def inv? (n : ℕ) (a : Approx Γ R) : Option (Approx Γ R) :=
  match a.val.terms with
  | [] => none
  | (e, r) :: _ => if (e : WithTop Γ) < a.prec then some (invCore n a e r) else none

theorem orderTop_inv {x : R⟦Γ⟧} {e : Γ} (hx : x.orderTop = e) :
    x⁻¹.orderTop = ((-e : Γ) : WithTop Γ) := by
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  have h1 := orderTop_mul x x⁻¹
  rw [mul_inv_cancel₀ hx0, orderTop_one, hx] at h1
  have hne : x⁻¹.orderTop ≠ ⊤ := fun h => by simp [h] at h1
  obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hg, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at h1
  rw [← hg, eq_neg_of_add_eq_zero_right h1.symm]

/-- **Residual certificate.** For any candidate `y`, `y` approximates `x⁻¹` at precision
`invPrec a e y`, provided `a` is certified with leading exponent `e`. -/
theorem Represents.inv_of_residual {a : Approx Γ R} {x : R⟦Γ⟧} (ha : a.Represents x) {e : Γ}
    (he : a.val.leadExp = e) (hc : a.Certified) (y : Poly Γ R) :
    (⟨y, invPrec a e y⟩ : Approx Γ R).Represents x⁻¹ := by
  have hx0 := ha.ne_zero hc
  have hxe : x.orderTop = e := (ha.orderTop_eq hc).trans he
  set P := a.prec + y.leadExp
  -- `1 - a.val * y` approximates `1 - x y` at precision `P`
  have hm := ha.mul_exact y
  have hres : (⟨1 - mulTruncTop P a.val y, P⟩ : Approx Γ R).Represents (1 - x * toHahn y) := by
    refine represents_iff_le_orderTop.2 ?_
    have e1 : 1 - x * toHahn y - toHahn (1 - mulTruncTop P a.val y) =
        -(x * toHahn y - toHahn (mulTruncTop P a.val y)) := by
      rw [map_sub, map_one]; abel
    rw [e1, orderTop_neg]
    exact represents_iff_le_orderTop.1 hm
  have hle := hres.ord_le
  refine represents_iff_le_orderTop.2 ?_
  have e2 : x⁻¹ - toHahn y = x⁻¹ * (1 - x * toHahn y) := by
    rw [mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
  rw [e2, orderTop_mul, orderTop_inv hxe, add_comm]
  exact add_le_add hle le_rfl

theorem Represents.invCore {a : Approx Γ R} {x : R⟦Γ⟧} (ha : a.Represents x) {e : Γ}
    (he : a.val.leadExp = e) (hc : a.Certified) (n : ℕ) (r : R) :
    (invCore n a e r).Represents x⁻¹ :=
  (represents_truncTop_iff le_rfl).2 (ha.inv_of_residual he hc _)

theorem inv?_isSome {a : Approx Γ R} (hc : a.Certified) (n : ℕ) : (a.inv? n).isSome := by
  unfold inv?
  unfold Certified leadExp at hc
  split
  · rename_i h; rw [h] at hc; exact absurd hc (not_lt.2 le_top)
  · rename_i e r l h
    rw [h] at hc
    simp [hc]

/-- **Soundness of `inv?`.** -/
theorem Represents.inv? {a b : Approx Γ R} {x : R⟦Γ⟧} {n : ℕ} (ha : a.Represents x)
    (h : a.inv? n = some b) : b.Represents x⁻¹ := by
  unfold Approx.inv? at h
  split at h
  · cases h
  · rename_i e r l hterms
    split_ifs at h with hlt
    cases h
    have he : a.val.leadExp = e := by unfold leadExp; rw [hterms]
    exact ha.invCore he (by rw [Certified, he]; exact hlt) n r

/-- `inv?` in the form "certified, hence nonzero, hence invertible with a sound result". -/
theorem exists_inv?_represents {a : Approx Γ R} {x : R⟦Γ⟧} (ha : a.Represents x)
    (hc : a.Certified) (n : ℕ) : x ≠ 0 ∧ ∃ b, a.inv? n = some b ∧ b.Represents x⁻¹ := by
  refine ⟨ha.ne_zero hc, ?_⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (inv?_isSome hc n)
  exact ⟨b, hb, ha.inv? hb⟩

end Inv

end Approx

end LeviCivita
