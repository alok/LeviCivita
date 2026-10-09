/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeviCivita.Poly.Basic

/-!
# Denotation of `Poly Γ R` as Hahn series, and the transported `CommRing`

* `Poly.toHahnFun p = ∑ (e, c) ∈ p.terms, HahnSeries.single e c : R⟦Γ⟧`.
* `toHahnFun_injective`: uses the invariants stored in `Poly`.
* every operation commutes with `toHahnFun`, and the `CommRing` instance is
  `Function.Injective.commRing`. No ring axiom is proved by hand.
* `Poly.toHahn : Poly Γ R →+* R⟦Γ⟧` bundles the result.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita

open HahnSeries

namespace Poly

variable {Γ R : Type*}

section Denote
variable [LinearOrder Γ] [AddCommGroup R]

/-- Denotation of a raw term list. -/
noncomputable def hahnL (l : List (Γ × R)) : R⟦Γ⟧ := (l.map fun t => HahnSeries.single t.1 t.2).sum

@[simp] theorem hahnL_nil : hahnL ([] : List (Γ × R)) = 0 := rfl

@[simp] theorem hahnL_cons (t : Γ × R) (l : List (Γ × R)) :
    hahnL (t :: l) = HahnSeries.single t.1 t.2 + hahnL l := by
  simp [hahnL]

theorem coeff_hahnL_eq_zero {g : Γ} :
    ∀ {l : List (Γ × R)}, (∀ t ∈ l, t.1 ≠ g) → (hahnL l).coeff g = 0
  | [], _ => by simp
  | t :: l, h => by
    rw [hahnL_cons, coeff_add, coeff_single_of_ne (Ne.symm (h t List.mem_cons_self)),
      coeff_hahnL_eq_zero (fun s hs => h s (List.mem_cons_of_mem _ hs)), add_zero]

theorem lt_orderTop_hahnL {g : Γ} :
    ∀ {l : List (Γ × R)}, (∀ t ∈ l, g < t.1) → (g : WithTop Γ) < (hahnL l).orderTop
  | [], _ => by simp
  | t :: l, h => by
    rw [hahnL_cons]
    refine lt_of_lt_of_le ?_ min_orderTop_le_orderTop_add
    exact lt_min (lt_orderTop_single (h t List.mem_cons_self))
      (lt_orderTop_hahnL fun s hs => h s (List.mem_cons_of_mem _ hs))

/-- A sorted list with nonzero coefficients is determined by its denotation. -/
theorem eq_of_hahnL_eq :
    ∀ {l₁ l₂ : List (Γ × R)}, l₁.Pairwise (fun a b => a.1 < b.1) → (∀ t ∈ l₁, t.2 ≠ 0) →
      l₂.Pairwise (fun a b => a.1 < b.1) → (∀ t ∈ l₂, t.2 ≠ 0) → hahnL l₁ = hahnL l₂ → l₁ = l₂
  | [], [], _, _, _, _, _ => rfl
  | [], t :: l, _, _, s₂, n₂, h => by
    exfalso
    have := congrArg (fun x => x.coeff t.1) h
    simp only [hahnL_nil, coeff_zero, hahnL_cons, coeff_add, coeff_single_same] at this
    rw [coeff_hahnL_eq_zero fun s hs => ((List.pairwise_cons.1 s₂).1 s hs).ne', add_zero] at this
    exact n₂ t List.mem_cons_self this.symm
  | t :: l, [], s₁, n₁, _, _, h => by
    exfalso
    have := congrArg (fun x => x.coeff t.1) h
    simp only [hahnL_nil, coeff_zero, hahnL_cons, coeff_add, coeff_single_same] at this
    rw [coeff_hahnL_eq_zero fun s hs => ((List.pairwise_cons.1 s₁).1 s hs).ne', add_zero] at this
    exact n₁ t List.mem_cons_self this
  | (e₁, c₁) :: l₁, (e₂, c₂) :: l₂, s₁, n₁, s₂, n₂, h => by
    have s₁' := List.pairwise_cons.1 s₁
    have s₂' := List.pairwise_cons.1 s₂
    -- coefficient of the full denotation at any `g ≤ head`
    have key₁ : ∀ g, g ≤ e₁ → (hahnL ((e₁, c₁) :: l₁)).coeff g = if g = e₁ then c₁ else 0 := by
      intro g hg
      rw [hahnL_cons, coeff_add, coeff_single,
        coeff_hahnL_eq_zero fun s hs => (lt_of_le_of_lt hg (s₁'.1 s hs)).ne', add_zero]
      simp
    have key₂ : ∀ g, g ≤ e₂ → (hahnL ((e₂, c₂) :: l₂)).coeff g = if g = e₂ then c₂ else 0 := by
      intro g hg
      rw [hahnL_cons, coeff_add, coeff_single,
        coeff_hahnL_eq_zero fun s hs => (lt_of_le_of_lt hg (s₂'.1 s hs)).ne', add_zero]
      simp
    have hc₁ : c₁ ≠ 0 := n₁ _ List.mem_cons_self
    have hc₂ : c₂ ≠ 0 := n₂ _ List.mem_cons_self
    rcases lt_trichotomy e₁ e₂ with hlt | rfl | hgt
    · exfalso
      have := congrArg (fun x => x.coeff e₁) h
      rw [key₁ e₁ le_rfl, key₂ e₁ hlt.le] at this
      simp [hlt.ne] at this
      exact hc₁ this
    · have := congrArg (fun x => x.coeff e₁) h
      rw [key₁ e₁ le_rfl, key₂ e₁ le_rfl] at this
      simp only [↓reduceIte] at this
      subst this
      simp only [hahnL_cons] at h
      rw [eq_of_hahnL_eq s₁'.2 (fun s hs => n₁ s (List.mem_cons_of_mem _ hs)) s₂'.2
        (fun s hs => n₂ s (List.mem_cons_of_mem _ hs)) (add_left_cancel h)]
    · exfalso
      have := congrArg (fun x => x.coeff e₂) h
      rw [key₁ e₂ hgt.le, key₂ e₂ le_rfl] at this
      simp [hgt.ne] at this
      exact hc₂ this.symm

/-- Denotation of a `Poly` as a Hahn series. -/
noncomputable def toHahnFun (p : Poly Γ R) : R⟦Γ⟧ := hahnL p.terms

theorem toHahnFun_injective : Function.Injective (toHahnFun : Poly Γ R → R⟦Γ⟧) :=
  fun p q h => ext (eq_of_hahnL_eq p.sorted p.nz q.sorted q.nz h)

@[simp] theorem toHahnFun_zero : toHahnFun (0 : Poly Γ R) = 0 := rfl

theorem leadingCoeff_toHahnFun (p : Poly Γ R) : (toHahnFun p).leadingCoeff = p.leadCoeff := by
  obtain ⟨_ | ⟨⟨e, c⟩, l⟩, s, n⟩ := p
  · simp [toHahnFun, leadCoeff]
  · have s' := List.pairwise_cons.1 s
    have hc : c ≠ 0 := n _ List.mem_cons_self
    simp only [toHahnFun, leadCoeff, hahnL_cons]
    rw [leadingCoeff_add_eq_left, leadingCoeff_of_single]
    rw [orderTop_single hc]
    exact lt_orderTop_hahnL s'.1

theorem toHahnFun_eq_zero_iff {p : Poly Γ R} : toHahnFun p = 0 ↔ p = 0 :=
  ⟨fun h => toHahnFun_injective (h.trans toHahnFun_zero.symm), fun h => h ▸ toHahnFun_zero⟩

theorem leadCoeff_eq_zero_iff {p : Poly Γ R} : p.leadCoeff = 0 ↔ p = 0 := by
  rw [← leadingCoeff_toHahnFun, leadingCoeff_eq_zero, toHahnFun_eq_zero_iff]

end Denote

section Insert
variable [LinearOrder Γ] [AddCommGroup R] [DecidableEq R]

theorem hahnL_insertTerm (e : Γ) (c : R) :
    ∀ l : List (Γ × R), hahnL (insertTerm e c l) = HahnSeries.single e c + hahnL l
  | [] => by
    unfold insertTerm
    split_ifs with h <;> simp [h]
  | (e', c') :: l => by
    unfold insertTerm
    split_ifs with h₁ h₂ h₃ h₄
    · simp [h₂]
    · simp
    · subst h₃
      simp only [hahnL_cons, ← add_assoc, ← single_add, h₄, map_zero, zero_add]
    · subst h₃
      simp [← add_assoc, ← single_add]
    · rw [hahnL_cons, hahnL_cons, hahnL_insertTerm e c l, add_left_comm]

theorem toHahnFun_insert (e : Γ) (c : R) (p : Poly Γ R) :
    toHahnFun (p.insert e c) = HahnSeries.single e c + toHahnFun p :=
  hahnL_insertTerm e c p.terms

theorem toHahnFun_insertMap {α : Type*} (g : α → Γ × R) (acc : Poly Γ R) :
    ∀ l : List α, toHahnFun (insertMap g l acc) =
      (l.map fun t => HahnSeries.single (g t).1 (g t).2).sum + toHahnFun acc
  | [] => by simp [insertMap]
  | t :: l => by
    have ih := toHahnFun_insertMap g acc l
    simp only [insertMap, List.foldr_cons] at ih ⊢
    rw [toHahnFun_insert, ih, List.map_cons, List.sum_cons, add_assoc]

theorem toHahnFun_single (e : Γ) (c : R) : toHahnFun (Poly.single e c : Poly Γ R) = .single e c := by
  unfold Poly.single
  split_ifs with h
  · simp [h]
  · simp [toHahnFun]

end Insert

section Ring
variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R] [DecidableEq R]

@[simp] theorem toHahnFun_one : toHahnFun (1 : Poly Γ R) = 1 := by
  rw [one_def, toHahnFun_single]; rfl

@[simp] theorem toHahnFun_C (c : R) : toHahnFun (C c : Poly Γ R) = HahnSeries.C c := by
  rw [C, toHahnFun_single]; rfl

@[simp] theorem toHahnFun_add (p q : Poly Γ R) : toHahnFun (p + q) = toHahnFun p + toHahnFun q := by
  rw [add_def, toHahnFun_insertMap, add_comm]
  rfl

@[simp] theorem toHahnFun_smul (r : R) (p : Poly Γ R) : toHahnFun (r • p) = r • toHahnFun p := by
  rw [smul_def, toHahnFun_insertMap, toHahnFun_zero, add_zero]
  change _ = r • hahnL p.terms
  induction p.terms with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons, hahnL_cons, smul_add, ← ih]
    rw [← C_mul_eq_smul (x := HahnSeries.single _ _), C_apply, single_mul_single, zero_add]

@[simp] theorem toHahnFun_neg (p : Poly Γ R) : toHahnFun (-p) = -toHahnFun p := by
  rw [neg_def, toHahnFun_insertMap, toHahnFun_zero, add_zero]
  change _ = -hahnL p.terms
  induction p.terms with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons, hahnL_cons, neg_add, ← ih, single_neg]

@[simp] theorem toHahnFun_sub (p q : Poly Γ R) : toHahnFun (p - q) = toHahnFun p - toHahnFun q := by
  rw [sub_def, toHahnFun_add, toHahnFun_neg, sub_eq_add_neg]

@[simp] theorem toHahnFun_mul (p q : Poly Γ R) : toHahnFun (p * q) = toHahnFun p * toHahnFun q := by
  rw [mul_def]
  change _ = hahnL p.terms * hahnL q.terms
  induction p.terms with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, toHahnFun_insertMap, ih, hahnL_cons, add_mul]
    congr 1
    induction q.terms with
    | nil => simp
    | cons b m ih' => simp only [List.map_cons, List.sum_cons, hahnL_cons, mul_add, ih',
        single_mul_single]

@[simp] theorem toHahnFun_nsmul (n : ℕ) (p : Poly Γ R) : toHahnFun (n • p) = n • toHahnFun p := by
  rw [nsmul_def, toHahnFun_smul, Nat.cast_smul_eq_nsmul]

@[simp] theorem toHahnFun_zsmul (n : ℤ) (p : Poly Γ R) : toHahnFun (n • p) = n • toHahnFun p := by
  rw [zsmul_def, toHahnFun_smul, Int.cast_smul_eq_zsmul]

@[simp] theorem toHahnFun_pow (p : Poly Γ R) (n : ℕ) : toHahnFun (p ^ n) = toHahnFun p ^ n := by
  induction n with
  | zero => rw [pow_zero', toHahnFun_one, pow_zero]
  | succ n ih => rw [pow_succ', toHahnFun_mul, ih, pow_succ]

@[simp] theorem toHahnFun_natCast (n : ℕ) : toHahnFun (n : Poly Γ R) = n := by
  rw [natCast_def, toHahnFun_C, map_natCast]

@[simp] theorem toHahnFun_intCast (n : ℤ) : toHahnFun (n : Poly Γ R) = n := by
  rw [intCast_def, toHahnFun_C, map_intCast]

/-- Auxiliary transported ring structure (noncomputable only because `toHahnFun` appears as an
argument); see `instCommRing`. -/
noncomputable abbrev commRingAux : CommRing (Poly Γ R) :=
  toHahnFun_injective.commRing _ toHahnFun_zero toHahnFun_one toHahnFun_add toHahnFun_mul
    toHahnFun_neg toHahnFun_sub toHahnFun_nsmul toHahnFun_zsmul toHahnFun_pow
    toHahnFun_natCast toHahnFun_intCast

/-- The ring structure on `Poly Γ R`, transported from `R⟦Γ⟧` along the injective denotation
(`commRingAux`). The data fields are restated so that the instance is computable: they are the
operations defined in `LeviCivita.Poly.Basic`, and only proof fields come from the transport. -/
instance instCommRing : CommRing (Poly Γ R) where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := Neg.neg
  sub := Sub.sub
  nsmul := (· • ·)
  zsmul := (· • ·)
  npow n p := p ^ n
  natCast := Nat.cast
  intCast := Int.cast
  add_assoc := commRingAux.add_assoc
  zero_add := commRingAux.zero_add
  add_zero := commRingAux.add_zero
  nsmul_zero := commRingAux.nsmul_zero
  nsmul_succ := commRingAux.nsmul_succ
  sub_eq_add_neg := commRingAux.sub_eq_add_neg
  zsmul_zero' := commRingAux.zsmul_zero'
  zsmul_succ' := commRingAux.zsmul_succ'
  zsmul_neg' := commRingAux.zsmul_neg'
  neg_add_cancel := commRingAux.neg_add_cancel
  add_comm := commRingAux.add_comm
  left_distrib := commRingAux.left_distrib
  right_distrib := commRingAux.right_distrib
  zero_mul := commRingAux.zero_mul
  mul_zero := commRingAux.mul_zero
  mul_assoc := commRingAux.mul_assoc
  one_mul := commRingAux.one_mul
  mul_one := commRingAux.mul_one
  natCast_zero := commRingAux.natCast_zero
  natCast_succ := commRingAux.natCast_succ
  intCast_ofNat := commRingAux.intCast_ofNat
  intCast_negSucc := commRingAux.intCast_negSucc
  npow_zero := commRingAux.npow_zero
  npow_succ := commRingAux.npow_succ
  mul_comm := commRingAux.mul_comm

/-- The denotation as a ring homomorphism. -/
noncomputable def toHahn : Poly Γ R →+* R⟦Γ⟧ where
  toFun := toHahnFun
  map_zero' := toHahnFun_zero
  map_one' := toHahnFun_one
  map_add' := toHahnFun_add
  map_mul' := toHahnFun_mul

@[simp] theorem toHahn_apply (p : Poly Γ R) : toHahn p = toHahnFun p := rfl

theorem toHahn_injective : Function.Injective (toHahn : Poly Γ R →+* R⟦Γ⟧) :=
  toHahnFun_injective

@[simp] theorem toHahn_single (e : Γ) (c : R) : toHahn (Poly.single e c : Poly Γ R) = .single e c :=
  toHahnFun_single e c

@[simp] theorem toHahn_C (c : R) : toHahn (C c : Poly Γ R) = HahnSeries.C c := toHahnFun_C c

@[simp] theorem toHahn_smul (r : R) (p : Poly Γ R) : toHahn (r • p) = r • toHahn p :=
  toHahnFun_smul r p

@[simp] theorem toHahn_ε [One Γ] : toHahn (ε : Poly Γ R) = .single 1 1 := toHahn_single _ _

@[simp] theorem toHahn_H [One Γ] [Neg Γ] : toHahn (H : Poly Γ R) = .single (-1) 1 :=
  toHahn_single _ _

end Ring

end Poly

end LeviCivita
