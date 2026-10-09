/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Geometry.SoS


/-!
# Lazy sign evaluation

* `Poly.truncLT c p`: the terms of `p` with exponent `< c` (`toHahn_truncLT`: it is
  `HahnSeries.truncLT`).
* `Poly.mulTrunc c p q`: the product with every term of exponent `≥ c` dropped, without forming
  those terms (`mulTrunc_eq : mulTrunc c p q = (p * q).truncLT c`).
* `truncLT_mul`: for **finite** `p, q`, `(p * q).truncLT c = (p.truncLT c * q.truncLT c).truncLT c`.
  Finiteness is necessary (`ε² · ε⁻¹`).
* `LazySign.Expr`: ring expressions over `Poly` leaves; `evalTrunc c` evaluates with truncation
  at every node; `evalTrunc_eq`: for finite leaves this is the truncation of the exact value.
* `lazySign c e`: the sign of the truncated value, or `none` if it vanishes.
  `lazySign_sound`: `some s` is the exact sign. `lazySign_complete`: above all exponents it is
  exact.
* `lazySignIter`: precisions `c, 2c, 4c, …`; `orient2dLazy`: the lazy SoS `orient2d`. The first
  pass (`c = 1`) is the unperturbed computation; perturbation terms are only computed when it
  vanishes.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita

open HahnSeries

namespace Poly

variable {Γ R : Type*}

section Trunc
variable [LinearOrder Γ] [Zero R]

/-- Keep the terms with exponent `< c`. Computable (a list filter). -/
def truncLT (c : Γ) (p : Poly Γ R) : Poly Γ R :=
  ⟨p.terms.filter (fun t => t.1 < c), p.sorted.filter _,
    fun t ht => p.nz t (List.mem_of_mem_filter ht)⟩

theorem terms_truncLT (c : Γ) (p : Poly Γ R) :
    (p.truncLT c).terms = p.terms.filter (fun t => t.1 < c) := rfl

end Trunc

section Mul
variable [AddMonoid Γ] [LinearOrder Γ] [CommRing R] [DecidableEq R]

/-- Truncated multiplication: the product with every term of exponent `≥ c` dropped, computed
without forming those terms. See `mulTrunc_eq`. -/
def mulTrunc (c : Γ) (p q : Poly Γ R) : Poly Γ R :=
  p.terms.foldr (fun a acc => insertMap (fun b => (a.1 + b.1, a.2 * b.2))
    (q.terms.filter fun b => a.1 + b.1 < c) acc) 0

end Mul

section Spec
variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
  [DecidableEq R]

theorem coeffL_filter (c g : Γ) : ∀ l : List (Γ × R),
    coeffL g (l.filter (fun t => t.1 < c)) = if g < c then coeffL g l else 0
  | [] => by simp [coeffL]
  | t :: l => by
    have ih := coeffL_filter c g l
    by_cases ht : t.1 < c
    · rw [List.filter_cons_of_pos (by simpa using ht)]
      simp only [coeffL, ih]
      by_cases hg : g < c
      · simp [hg]
      · have : g ≠ t.1 := fun h => hg (h ▸ ht)
        simp [hg, this]
    · rw [List.filter_cons_of_neg (by simpa using ht), ih]
      simp only [coeffL]
      by_cases hg : g < c
      · have : g ≠ t.1 := fun h => ht (h ▸ hg)
        simp [hg, this]
      · simp [hg]

theorem coeff_truncLT (c : Γ) (p : Poly Γ R) (g : Γ) :
    (p.truncLT c).coeff g = if g < c then p.coeff g else 0 :=
  coeffL_filter c g p.terms

/-- **Spec of `truncLT`**: it is Mathlib's `HahnSeries.truncLT`. -/
theorem toHahn_truncLT (c : Γ) (p : Poly Γ R) :
    toHahn (p.truncLT c) = HahnSeries.truncLT c (toHahn p) := by
  ext g
  rw [← coeff_eq, HahnSeries.coeff_truncLT, ← coeff_eq, coeff_truncLT]

theorem truncLT_add (c : Γ) (p q : Poly Γ R) :
    (p + q).truncLT c = p.truncLT c + q.truncLT c :=
  toHahn_injective (by simp only [toHahn_truncLT, map_add, HahnSeries.truncLT_add])

theorem truncLT_neg (c : Γ) (p : Poly Γ R) : (-p).truncLT c = -p.truncLT c :=
  coeff_injective (funext fun g => by simp only [coeff_truncLT, coeff_neg]; split_ifs <;> simp)

theorem truncLT_sub (c : Γ) (p q : Poly Γ R) :
    (p - q).truncLT c = p.truncLT c - q.truncLT c := by
  rw [sub_eq_add_neg, truncLT_add, truncLT_neg, ← sub_eq_add_neg]

theorem truncLT_single_hahn (c e : Γ) (r : R) :
    HahnSeries.truncLT c (HahnSeries.single e r) = if e < c then HahnSeries.single e r else 0 := by
  ext g
  rw [HahnSeries.coeff_truncLT, HahnSeries.coeff_single]
  by_cases hge : g = e
  · subst hge; by_cases h : g < c <;> simp [h]
  · by_cases h : e < c
    · simp [h, hge]
    · simp [h, hge]

theorem sum_filter_single (c : Γ) (a : Γ × R) : ∀ m : List (Γ × R),
    ((m.filter fun b => a.1 + b.1 < c).map fun b =>
        HahnSeries.single (a.1 + b.1) (a.2 * b.2)).sum =
      HahnSeries.truncLT c (HahnSeries.single a.1 a.2 * hahnL m)
  | [] => by simp
  | b :: m => by
    rw [hahnL_cons, mul_add, HahnSeries.truncLT_add, single_mul_single, truncLT_single_hahn,
      ← sum_filter_single c a m]
    by_cases h : a.1 + b.1 < c
    · rw [List.filter_cons_of_pos (by simpa using h)]
      simp [h]
    · rw [List.filter_cons_of_neg (by simpa using h)]
      simp [h]

theorem toHahnFun_mulTrunc (c : Γ) (p q : Poly Γ R) :
    toHahnFun (mulTrunc c p q) = HahnSeries.truncLT c (toHahnFun p * toHahnFun q) := by
  unfold mulTrunc
  change _ = HahnSeries.truncLT c (hahnL p.terms * hahnL q.terms)
  induction p.terms with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, toHahnFun_insertMap, ih, hahnL_cons, add_mul, HahnSeries.truncLT_add,
      ← sum_filter_single]

/-- **Spec of `mulTrunc`**: the truncation of the full product. No hypothesis needed. -/
theorem mulTrunc_eq (c : Γ) (p q : Poly Γ R) : mulTrunc c p q = (p * q).truncLT c :=
  toHahn_injective (by
    rw [toHahn_truncLT, map_mul]
    exact toHahnFun_mulTrunc c p q)

/-! ### Truncation commutes with products of finite elements -/

theorem IsFinite.nonneg_of_mem {p : Poly Γ R} (hp : p.IsFinite) : ∀ t ∈ p.terms, 0 ≤ t.1 := by
  obtain ⟨_ | ⟨t₀, l⟩, s, n⟩ := p
  · simp
  · intro t ht
    have h0 : (0 : WithTop Γ) ≤ t₀.1 := hp
    have h0 : 0 ≤ t₀.1 := WithTop.coe_le_coe.1 h0
    rcases List.mem_cons.1 ht with rfl | ht
    · exact h0
    · exact h0.trans ((List.pairwise_cons.1 s).1 t ht).le

theorem foldr_filter_of_id {α β : Type*} (f : α → β → β) (P : α → Bool) (z : β) :
    ∀ l : List α, (∀ a ∈ l, P a = false → ∀ b, f a b = b) →
      (l.filter P).foldr f z = l.foldr f z
  | [], _ => rfl
  | a :: l, h => by
    have ih := foldr_filter_of_id f P z l fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
    by_cases ha : P a
    · rw [List.filter_cons_of_pos ha, List.foldr_cons, List.foldr_cons, ih]
    · rw [List.filter_cons_of_neg ha, List.foldr_cons, ih,
        h a List.mem_cons_self (by simpa using ha)]

theorem foldr_congr_mem {α β : Type*} {f g : α → β → β} (z : β) :
    ∀ l : List α, (∀ a ∈ l, ∀ b, f a b = g a b) → l.foldr f z = l.foldr g z
  | [], _ => rfl
  | a :: l, h => by
    rw [List.foldr_cons, List.foldr_cons, foldr_congr_mem z l fun a' ha' => h a'
      (List.mem_cons_of_mem _ ha'), h a List.mem_cons_self]

/-- Truncating the factors first does not change a truncated product of **finite** elements
(all exponents `≥ 0`). False without finiteness: `(ε^2 · ε^(-1)).truncLT 2 = ε`, but
`ε^2` truncates to `0`. -/
theorem mulTrunc_truncLT {c : Γ} {p q : Poly Γ R} (hp : p.IsFinite) (hq : q.IsFinite) :
    mulTrunc c (p.truncLT c) (q.truncLT c) = mulTrunc c p q := by
  have hp' := hp.nonneg_of_mem
  have hq' := hq.nonneg_of_mem
  unfold mulTrunc
  rw [terms_truncLT, terms_truncLT, foldr_filter_of_id]
  · refine foldr_congr_mem _ _ fun a ha acc => ?_
    congr 1
    rw [List.filter_filter]
    refine List.filter_congr fun b _ => ?_
    by_cases h : a.1 + b.1 < c
    · have : b.1 < c := lt_of_le_of_lt (le_add_of_nonneg_left (hp' a ha)) h
      simp [h, this]
    · simp [h]
  · intro a ha hac acc
    have hac : c ≤ a.1 := by simpa using hac
    rw [List.filter_eq_nil_iff.2]
    · rfl
    · intro b hb
      have := hq' b (List.mem_of_mem_filter hb)
      simpa using hac.trans (le_add_of_nonneg_right this)

theorem truncLT_mul {c : Γ} {p q : Poly Γ R} (hp : p.IsFinite) (hq : q.IsFinite) :
    (p * q).truncLT c = (p.truncLT c * q.truncLT c).truncLT c := by
  rw [← mulTrunc_eq, ← mulTrunc_eq, mulTrunc_truncLT hp hq]

end Spec

section Sign
variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
  [DecidableEq R]

/-- A nonzero truncation keeps the leading term, hence the sign. -/
theorem leadCoeff_truncLT {c : Γ} {p : Poly Γ R} (h : p.truncLT c ≠ 0) :
    (p.truncLT c).leadCoeff = p.leadCoeff := by
  obtain ⟨_ | ⟨t, l⟩, s, n⟩ := p
  · rfl
  · by_cases ht : t.1 < c
    · simp only [leadCoeff, truncLT]
      rw [List.filter_cons_of_pos (by simpa using ht)]
    · exfalso
      apply h
      ext1
      simp only [terms_truncLT, terms_zero, List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
      intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · exact not_lt.1 ht
      · exact (not_lt.1 ht).trans ((List.pairwise_cons.1 s).1 u hu).le

theorem sign_truncLT [LinearOrder R] {c : Γ} {p : Poly Γ R} (h : p.truncLT c ≠ 0) :
    (p.truncLT c).sign = p.sign := by
  unfold sign; rw [leadCoeff_truncLT h]

theorem truncLT_eq_self {c : Γ} {p : Poly Γ R} (h : ∀ t ∈ p.terms, t.1 < c) :
    p.truncLT c = p := by
  ext1; exact List.filter_eq_self.2 fun t ht => by simpa using h t ht

theorem isFinite_truncLT {p : Poly Γ R} (hp : p.IsFinite) (c : Γ) : (p.truncLT c).IsFinite := by
  obtain ⟨_ | ⟨t, l⟩, s, n⟩ := p
  · exact hp
  · have h0 : (0 : Γ) ≤ t.1 := WithTop.coe_le_coe.1 hp
    unfold IsFinite leadExp
    split
    · exact le_top
    · rename_i u l' hl
      have hu : u ∈ (Poly.truncLT c ⟨t :: l, s, n⟩).terms := by rw [hl]; exact List.mem_cons_self
      rw [terms_truncLT] at hu
      exact WithTop.coe_le_coe.2 (IsFinite.nonneg_of_mem hp u (List.mem_of_mem_filter hu))

end Sign

end Poly

/-! ### Lazy sign evaluation -/

namespace LazySign

open Poly

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] [DecidableEq R]

/-- Ring expressions over `Poly` leaves. The geometric predicates, being defined for any type
with `+ - *`, can be instantiated at `Expr` directly (`orient2d (K := Expr Γ R) …`). -/
inductive Expr (Γ R : Type*) [LinearOrder Γ] [Zero R] where
  | leaf : Poly Γ R → Expr Γ R
  | add : Expr Γ R → Expr Γ R → Expr Γ R
  | sub : Expr Γ R → Expr Γ R → Expr Γ R
  | neg : Expr Γ R → Expr Γ R
  | mul : Expr Γ R → Expr Γ R → Expr Γ R

namespace Expr

instance [Zero R] : Add (Expr Γ R) := ⟨add⟩
instance [Zero R] : Sub (Expr Γ R) := ⟨sub⟩
instance [Zero R] : Neg (Expr Γ R) := ⟨neg⟩
instance [Zero R] : Mul (Expr Γ R) := ⟨mul⟩

/-- Exact evaluation. -/
def eval : Expr Γ R → Poly Γ R
  | leaf p => p
  | add a b => a.eval + b.eval
  | sub a b => a.eval - b.eval
  | neg a => -a.eval
  | mul a b => a.eval * b.eval

/-- Evaluation with every intermediate result truncated below `ε^c`. -/
def evalTrunc (c : Γ) : Expr Γ R → Poly Γ R
  | leaf p => p.truncLT c
  | add a b => a.evalTrunc c + b.evalTrunc c
  | sub a b => a.evalTrunc c - b.evalTrunc c
  | neg a => -a.evalTrunc c
  | mul a b => mulTrunc c (a.evalTrunc c) (b.evalTrunc c)

/-- All leaves are finite (no negative exponents). -/
def LeavesFinite : Expr Γ R → Prop
  | leaf p => p.IsFinite
  | add a b => a.LeavesFinite ∧ b.LeavesFinite
  | sub a b => a.LeavesFinite ∧ b.LeavesFinite
  | neg a => a.LeavesFinite
  | mul a b => a.LeavesFinite ∧ b.LeavesFinite

@[simp] theorem eval_leaf (p : Poly Γ R) : (leaf p).eval = p := rfl
@[simp] theorem eval_add' (a b : Expr Γ R) : (a + b).eval = a.eval + b.eval := rfl
@[simp] theorem eval_sub' (a b : Expr Γ R) : (a - b).eval = a.eval - b.eval := rfl
@[simp] theorem eval_neg' (a : Expr Γ R) : (-a).eval = -a.eval := rfl
@[simp] theorem eval_mul' (a b : Expr Γ R) : (a * b).eval = a.eval * b.eval := rfl

@[simp] theorem leavesFinite_leaf (p : Poly Γ R) : (leaf p).LeavesFinite ↔ p.IsFinite := Iff.rfl
@[simp] theorem leavesFinite_add' (a b : Expr Γ R) :
    (a + b).LeavesFinite ↔ a.LeavesFinite ∧ b.LeavesFinite := Iff.rfl
@[simp] theorem leavesFinite_sub' (a b : Expr Γ R) :
    (a - b).LeavesFinite ↔ a.LeavesFinite ∧ b.LeavesFinite := Iff.rfl
@[simp] theorem leavesFinite_neg' (a : Expr Γ R) : (-a).LeavesFinite ↔ a.LeavesFinite := Iff.rfl
@[simp] theorem leavesFinite_mul' (a b : Expr Γ R) :
    (a * b).LeavesFinite ↔ a.LeavesFinite ∧ b.LeavesFinite := Iff.rfl

theorem LeavesFinite.eval {e : Expr Γ R} (h : e.LeavesFinite) : e.eval.IsFinite := by
  induction e with
  | leaf p => exact h
  | add a b iha ihb => exact (iha h.1).add (ihb h.2)
  | sub a b iha ihb => exact (iha h.1).sub (ihb h.2)
  | neg a iha => exact (iha h).neg
  | mul a b iha ihb => exact (iha h.1).mul (ihb h.2)

/-- **Truncated evaluation is the truncation of exact evaluation**, for finite leaves. -/
theorem evalTrunc_eq {c : Γ} {e : Expr Γ R} (h : e.LeavesFinite) :
    e.evalTrunc c = e.eval.truncLT c := by
  induction e with
  | leaf p => rfl
  | add a b iha ihb => simp only [evalTrunc, eval, iha h.1, ihb h.2, Poly.truncLT_add]
  | sub a b iha ihb => simp only [evalTrunc, eval, iha h.1, ihb h.2, Poly.truncLT_sub]
  | neg a iha => simp only [evalTrunc, eval, iha h, Poly.truncLT_neg]
  | mul a b iha ihb =>
    simp only [evalTrunc, eval, iha h.1, ihb h.2]
    rw [mulTrunc_truncLT h.1.eval h.2.eval, mulTrunc_eq]

end Expr

open Expr

/-- Lazy sign at precision `c`: the sign of the truncated value if it is nonzero, else `none`
(the value is `0` or needs more precision). -/
def lazySign [LinearOrder R] (c : Γ) (e : Expr Γ R) : Option ℤ :=
  if e.evalTrunc c = 0 then none else some (e.evalTrunc c).sign

/-- **Soundness.** -/
theorem lazySign_sound [LinearOrder R] {c : Γ} {e : Expr Γ R} (h : e.LeavesFinite) {s : ℤ}
    (hs : lazySign c e = some s) : e.eval.sign = s := by
  unfold lazySign at hs
  rw [evalTrunc_eq h] at hs
  split_ifs at hs with h0
  cases hs
  exact (sign_truncLT h0).symm

/-- **Completeness.** Once `c` exceeds every exponent of the exact value, `lazySign` returns the
exact sign (and `none` only for the value `0`). -/
theorem lazySign_complete [LinearOrder R] {c : Γ} {e : Expr Γ R} (h : e.LeavesFinite)
    (hc : ∀ t ∈ e.eval.terms, t.1 < c) :
    lazySign c e = if e.eval = 0 then none else some e.eval.sign := by
  unfold lazySign
  simp only [evalTrunc_eq h, truncLT_eq_self hc]

theorem lazySign_complete_of_ne_zero [LinearOrder R] {c : Γ} {e : Expr Γ R}
    (h : e.LeavesFinite) (hc : ∀ t ∈ e.eval.terms, t.1 < c) (h0 : e.eval ≠ 0) :
    lazySign c e = some e.eval.sign := by
  rw [lazySign_complete h hc, ite_eq_right h0]

/-! ### Iterative driver (`Γ = ℤ`) -/

section Driver
variable {R : Type*} [CommRing R] [DecidableEq R] [LinearOrder R]

/-- Try precisions `c, next c, next (next c), …`, at most `fuel` times. Start with `c = 1`: the
first pass keeps only the `ε^0` terms, i.e. it is the plain unperturbed computation. Soundness
holds for any `next`; completeness needs `next c ≥ 2c`. The SoS drivers use `c ↦ c² + 1`,
because SoS exponents are huge (`b^(j + d i)`): doubling would need thousands of passes. -/
def lazySignIter (e : Expr ℤ R) (next : ℤ → ℤ) : ℕ → ℤ → Option ℤ
  | 0, _ => none
  | fuel + 1, c =>
    match lazySign c e with
    | some s => some s
    | none => lazySignIter e next fuel (next c)

theorem lazySignIter_sound {e : Expr ℤ R} (h : e.LeavesFinite) {next : ℤ → ℤ} :
    ∀ {fuel : ℕ} {c s : ℤ}, lazySignIter e next fuel c = some s → e.eval.sign = s
  | 0, _, _, hs => by simp [lazySignIter] at hs
  | fuel + 1, c, s, hs => by
    unfold lazySignIter at hs
    split at hs
    · rename_i s' hs'
      cases hs
      exact lazySign_sound h hs'
    · exact lazySignIter_sound h hs

/-- **Completeness of the driver**: if `next` at least doubles positive precisions and
`2^fuel · c` exceeds every exponent of a nonzero value, the driver returns its sign. -/
theorem lazySignIter_complete {e : Expr ℤ R} (h : e.LeavesFinite) (h0 : e.eval ≠ 0)
    {next : ℤ → ℤ} (hnext : ∀ c, 0 < c → 2 * c ≤ next c) :
    ∀ {fuel : ℕ} {c : ℤ}, 0 < c → (∀ t ∈ e.eval.terms, t.1 < 2 ^ fuel * c) →
      lazySignIter e next (fuel + 1) c = some e.eval.sign
  | 0, c, _, hc => by
    simp only [pow_zero, one_mul] at hc
    simp [lazySignIter, lazySign_complete_of_ne_zero h hc h0]
  | fuel + 1, c, hpos, hc => by
    unfold lazySignIter
    split
    · rename_i s hs
      rw [lazySign_sound h hs]
    · have h2 := hnext c hpos
      refine lazySignIter_complete h h0 hnext (by omega) (fun t ht => ?_)
      have := hc t ht
      have hp : (0 : ℤ) < 2 ^ fuel := by positivity
      rw [pow_succ] at this
      nlinarith

/-- The squaring step used by the SoS drivers. -/
def sqStep (c : ℤ) : ℤ := c * c + 1

theorem sqStep_ge (c : ℤ) (hc : 0 < c) : 2 * c ≤ sqStep c := by
  unfold sqStep; nlinarith

end Driver

/-! ### Lazy SoS `orient2d` -/

section Orient2d
open Geometry
variable {R : Type*} [CommRing R] [DecidableEq R] {n : ℕ}

/-- The SoS-perturbed `orient2d` as an expression tree (the generic formula at `K = Expr`). -/
def orient2dExpr (b : ℕ) (x : Fin n → Fin 2 → R) (i k l : Fin n) : Expr ℤ R :=
  orient2d (fun j => leaf (sosPoint b x i j)) (fun j => leaf (sosPoint b x k j))
    (fun j => leaf (sosPoint b x l j))

theorem eval_orient2dExpr (b : ℕ) (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    (orient2dExpr b x i k l).eval = orient2dSoS b x i k l := by
  simp [orient2dExpr, orient2d, orient2dSoS]

theorem leavesFinite_orient2dExpr (b : ℕ) (x : Fin n → Fin 2 → R) (i k l : Fin n) :
    (orient2dExpr b x i k l).LeavesFinite := by
  simp [orient2dExpr, orient2d, isFinite_sosPoint]

/-- Lazy SoS `orient2d`: exact sign of the perturbed predicate, computing perturbation terms only
when the unperturbed value vanishes. -/
def orient2dLazy [LinearOrder R] (b : ℕ) (x : Fin n → Fin 2 → R) (i k l : Fin n) (fuel : ℕ := 64) :
    Option ℤ :=
  lazySignIter (orient2dExpr b x i k l) sqStep fuel 1

theorem orient2dLazy_sound [LinearOrder R] {b : ℕ} {x : Fin n → Fin 2 → R} {i k l : Fin n} {fuel : ℕ}
    {s : ℤ} (h : orient2dLazy b x i k l fuel = some s) : (orient2dSoS b x i k l).sign = s := by
  rw [← eval_orient2dExpr]
  exact lazySignIter_sound (leavesFinite_orient2dExpr b x i k l) h

/-- With enough fuel the lazy evaluator returns the SoS sign, which is never `0`. -/
theorem orient2dLazy_complete [LinearOrder R] [Nontrivial R] {b : ℕ} (hb : 2 ≤ b) (x : Fin n → Fin 2 → R)
    {i k l : Fin n} (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) {fuel : ℕ}
    (hc : ∀ t ∈ (orient2dSoS b x i k l).terms, t.1 < 2 ^ fuel) :
    orient2dLazy b x i k l (fuel + 1) = some (orient2dSoS b x i k l).sign := by
  have := lazySignIter_complete (leavesFinite_orient2dExpr b x i k l)
    (by rw [eval_orient2dExpr]; exact orient2dSoS_ne_zero hb x hik hil hkl)
    sqStep_ge (fuel := fuel) (c := 1) one_pos (by rw [eval_orient2dExpr]; simpa using hc)
  rwa [eval_orient2dExpr] at this

end Orient2d

/-! ### Lazy SoS `incircle` -/

section Incircle
open Geometry
variable {R : Type*} [CommRing R] [DecidableEq R] {n : ℕ}

/-- The SoS-perturbed `incircle` as an expression tree. -/
def incircleExpr (b : ℕ) (x : Fin n → Fin 2 → R) (i k l m : Fin n) : Expr ℤ R :=
  incircle (fun j => leaf (sosPoint b x i j)) (fun j => leaf (sosPoint b x k j))
    (fun j => leaf (sosPoint b x l j)) (fun j => leaf (sosPoint b x m j))

theorem eval_incircleExpr (b : ℕ) (x : Fin n → Fin 2 → R) (i k l m : Fin n) :
    (incircleExpr b x i k l m).eval = incircleSoS b x i k l m := by
  simp [incircleExpr, incircle, det3, incircleSoS]

theorem leavesFinite_incircleExpr (b : ℕ) (x : Fin n → Fin 2 → R) (i k l m : Fin n) :
    (incircleExpr b x i k l m).LeavesFinite := by
  simp [incircleExpr, incircle, det3, isFinite_sosPoint]

/-- Lazy SoS `incircle`. -/
def incircleLazy [LinearOrder R] (b : ℕ) (x : Fin n → Fin 2 → R) (i k l m : Fin n)
    (fuel : ℕ := 64) : Option ℤ :=
  lazySignIter (incircleExpr b x i k l m) sqStep fuel 1

theorem incircleLazy_sound [LinearOrder R] {b : ℕ} {x : Fin n → Fin 2 → R} {i k l m : Fin n}
    {fuel : ℕ} {s : ℤ} (h : incircleLazy b x i k l m fuel = some s) :
    (incircleSoS b x i k l m).sign = s := by
  rw [← eval_incircleExpr]
  exact lazySignIter_sound (leavesFinite_incircleExpr b x i k l m) h

end Incircle

end LazySign

end LeviCivita
