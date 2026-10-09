/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Geometry.SoS

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

end Poly

end LeviCivita
