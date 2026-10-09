/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Geometry.LazySign

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

end Approx

end LeviCivita
