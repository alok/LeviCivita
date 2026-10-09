/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Normalized sparse Hahn polynomials: data and raw operations

`Poly Γ R` is a finite formal sum `∑ cᵢ · ε^{eᵢ}` stored as a list of `(exponent, coeff)` pairs
with **strictly ascending exponents** and **nonzero coefficients**. Both invariants are fields of
the structure, so two `Poly`s are equal iff their term lists are equal, and the denotation into
Hahn series (`LeviCivita/Poly/Hahn.lean`) is injective.

Convention (Mathlib's Hahn convention): a *smaller* exponent means a *larger* magnitude, so the
head of the list is the leading term, `ε = ε^1` is a positive infinitesimal and `H = ε^(-1)`
is infinite.

Every arithmetic operation is built from one primitive, `insertTerm`, which is defined by
structural recursion on a list. This keeps all operations reducible by the kernel, so
`decide` works on closed terms such as `(ε : Poly ℤ ℚ) < C (1/1000)`. The quadratic-time list
operations are the *specification*; faster `Array` implementations can be attached later with
`@[csimp]` without changing any statement.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita

/-- Insert `c · ε^e` into a raw term list, combining with an existing term of the same exponent
and dropping it if the coefficient cancels. Assumes nothing about the input; preserves the
`Poly` invariants (see `insertTerm_sorted`, `insertTerm_nz`). -/
def insertTerm {Γ R : Type*} [LinearOrder Γ] [Zero R] [Add R] [DecidableEq R] (e : Γ) (c : R) :
    List (Γ × R) → List (Γ × R)
  | [] => if c = 0 then [] else [(e, c)]
  | (e', c') :: l =>
    if e < e' then
      if c = 0 then (e', c') :: l else (e, c) :: (e', c') :: l
    else if e = e' then
      if c + c' = 0 then l else (e, c + c') :: l
    else (e', c') :: insertTerm e c l

/-- Normalized finite Hahn series: strictly ascending exponents, nonzero coefficients. -/
structure Poly (Γ R : Type*) [LinearOrder Γ] [Zero R] where
  /-- The terms `(exponent, coefficient)`, leading (smallest-exponent) term first. -/
  terms : List (Γ × R)
  sorted : terms.Pairwise (fun a b => a.1 < b.1)
  nz : ∀ t ∈ terms, t.2 ≠ 0

namespace Poly

variable {Γ R : Type*} [LinearOrder Γ]

section Zero
variable [Zero R]

@[ext]
theorem ext {p q : Poly Γ R} (h : p.terms = q.terms) : p = q := by
  cases p; cases q; cases h; rfl

theorem ext_iff' {p q : Poly Γ R} : p = q ↔ p.terms = q.terms :=
  ⟨fun h => h ▸ rfl, ext⟩

instance [DecidableEq Γ] [DecidableEq R] : DecidableEq (Poly Γ R) := fun p q =>
  decidable_of_iff (p.terms = q.terms) ext_iff'.symm

instance : Zero (Poly Γ R) := ⟨⟨[], List.Pairwise.nil, by simp⟩⟩

@[simp] theorem terms_zero : (0 : Poly Γ R).terms = [] := rfl

/-- The monomial `c · ε^e` (zero if `c = 0`). -/
def single [DecidableEq R] (e : Γ) (c : R) : Poly Γ R :=
  if h : c = 0 then 0 else ⟨[(e, c)], List.pairwise_singleton _ _, by simpa using h⟩

/-- The leading (smallest-exponent) coefficient, `0` for the zero polynomial. -/
def leadCoeff (p : Poly Γ R) : R :=
  match p.terms with
  | [] => 0
  | t :: _ => t.2

end Zero

section Insert
variable [Zero R] [Add R] [DecidableEq R]

theorem mem_insertTerm {e : Γ} {c : R} :
    ∀ {l : List (Γ × R)} {t : Γ × R}, t ∈ insertTerm e c l → t.1 = e ∨ ∃ s ∈ l, s.1 = t.1
  | [], t, h => by
    unfold insertTerm at h
    split_ifs at h <;> simp_all
  | (e', c') :: l, t, h => by
    unfold insertTerm at h
    split_ifs at h with h₁ h₂ h₃ h₄
    · exact Or.inr ⟨t, h, rfl⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr ⟨t, h, rfl⟩
    · exact Or.inr ⟨t, List.mem_cons_of_mem _ h, rfl⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr ⟨t, List.mem_cons_of_mem _ h, rfl⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
      · rcases mem_insertTerm h with h | ⟨s, hs, hst⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, hst⟩

theorem insertTerm_sorted {e : Γ} {c : R} :
    ∀ {l : List (Γ × R)}, l.Pairwise (fun a b => a.1 < b.1) →
      (insertTerm e c l).Pairwise (fun a b => a.1 < b.1)
  | [], _ => by
    unfold insertTerm
    split_ifs <;> simp
  | (e', c') :: l, hl => by
    have hl' := List.pairwise_cons.1 hl
    unfold insertTerm
    split_ifs with h₁ h₂ h₃ h₄
    · exact hl
    · refine List.Pairwise.cons ?_ hl
      intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact h₁
      · exact h₁.trans (hl'.1 s hs)
    · exact hl'.2
    · subst h₃
      exact List.Pairwise.cons hl'.1 hl'.2
    · have hlt : e' < e := lt_of_le_of_ne (not_lt.1 h₁) (Ne.symm h₃)
      refine List.Pairwise.cons ?_ (insertTerm_sorted hl'.2)
      intro s hs
      rcases mem_insertTerm hs with h | ⟨s', hs', hss'⟩
      · exact h ▸ hlt
      · exact hss' ▸ hl'.1 s' hs'

theorem insertTerm_nz {e : Γ} {c : R} :
    ∀ {l : List (Γ × R)}, (∀ t ∈ l, t.2 ≠ 0) → ∀ t ∈ insertTerm e c l, t.2 ≠ 0
  | [], _ => by
    unfold insertTerm
    split_ifs with h <;> simp [h]
  | (e', c') :: l, hl => by
    unfold insertTerm
    split_ifs with h₁ h₂ h₃ h₄
    · exact hl
    · intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · exact h₂
      · exact hl t ht
    · exact fun t ht => hl t (List.mem_cons_of_mem _ ht)
    · intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · exact h₄
      · exact hl t (List.mem_cons_of_mem _ ht)
    · intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · exact hl _ List.mem_cons_self
      · exact insertTerm_nz (fun s hs => hl s (List.mem_cons_of_mem _ hs)) t ht

/-- Add the monomial `c · ε^e` to `p`. -/
def insert (e : Γ) (c : R) (p : Poly Γ R) : Poly Γ R :=
  ⟨insertTerm e c p.terms, insertTerm_sorted p.sorted, insertTerm_nz p.nz⟩

/-- Insert `g t` for every term `t` of a list into an accumulator. All ring operations are
instances of this. -/
def insertMap {α : Type*} (g : α → Γ × R) (l : List α) (acc : Poly Γ R) : Poly Γ R :=
  l.foldr (fun t acc => acc.insert (g t).1 (g t).2) acc

end Insert

section Ops
variable [AddMonoid Γ] [CommRing R] [DecidableEq R]

instance : One (Poly Γ R) := ⟨single 0 1⟩

/-- Constant (standard) polynomial. -/
def C (c : R) : Poly Γ R := single 0 c

instance : Add (Poly Γ R) := ⟨fun p q => insertMap id q.terms p⟩

instance : Neg (Poly Γ R) := ⟨fun p => insertMap (fun t => (t.1, -t.2)) p.terms 0⟩

instance : Sub (Poly Γ R) := ⟨fun p q => p + -q⟩

/-- Multiplication: insert every pairwise product of terms. -/
instance : Mul (Poly Γ R) :=
  ⟨fun p q => p.terms.foldr (fun a acc => insertMap (fun b => (a.1 + b.1, a.2 * b.2)) q.terms acc) 0⟩

/-- Scalar multiplication by a coefficient. -/
instance : SMul R (Poly Γ R) := ⟨fun r p => insertMap (fun t => (t.1, r * t.2)) p.terms 0⟩

instance : SMul ℕ (Poly Γ R) := ⟨fun n p => (n : R) • p⟩

instance : SMul ℤ (Poly Γ R) := ⟨fun n p => (n : R) • p⟩

/-- Natural powers by repeated multiplication (structural recursion, kernel-friendly). -/
protected def npow (p : Poly Γ R) : ℕ → Poly Γ R
  | 0 => 1
  | n + 1 => Poly.npow p n * p

instance : Pow (Poly Γ R) ℕ := ⟨Poly.npow⟩

instance : NatCast (Poly Γ R) := ⟨fun n => C (n : R)⟩

instance : IntCast (Poly Γ R) := ⟨fun n => C (n : R)⟩

theorem add_def (p q : Poly Γ R) : p + q = insertMap id q.terms p := rfl
theorem neg_def (p : Poly Γ R) : -p = insertMap (fun t => (t.1, -t.2)) p.terms 0 := rfl
theorem sub_def (p q : Poly Γ R) : p - q = p + -q := rfl
theorem mul_def (p q : Poly Γ R) :
    p * q = p.terms.foldr
      (fun a acc => insertMap (fun b => (a.1 + b.1, a.2 * b.2)) q.terms acc) 0 := rfl
theorem smul_def (r : R) (p : Poly Γ R) :
    r • p = insertMap (fun t => (t.1, r * t.2)) p.terms 0 := rfl
theorem nsmul_def (n : ℕ) (p : Poly Γ R) : n • p = (n : R) • p := rfl
theorem zsmul_def (n : ℤ) (p : Poly Γ R) : n • p = (n : R) • p := rfl
theorem pow_zero' (p : Poly Γ R) : p ^ 0 = 1 := rfl
theorem pow_succ' (p : Poly Γ R) (n : ℕ) : p ^ (n + 1) = p ^ n * p := rfl
theorem one_def : (1 : Poly Γ R) = single 0 1 := rfl
theorem natCast_def (n : ℕ) : (n : Poly Γ R) = C (n : R) := rfl
theorem intCast_def (n : ℤ) : (n : Poly Γ R) = C (n : R) := rfl

/-- The positive infinitesimal `ε = ε^1`. -/
def ε [One Γ] : Poly Γ R := single 1 1

/-- The positive infinite element `H = ε^(-1) = 1/ε`. -/
def H [One Γ] [Neg Γ] : Poly Γ R := single (-1) 1

end Ops

section Sign
variable [Zero R] [LinearOrder R]

/-- Sign of the leading term: `1`, `0` or `-1`. Computable; see `sign_eq_one_iff` etc. for its
meaning in the lexicographic order on Hahn series. -/
def sign (p : Poly Γ R) : ℤ :=
  if 0 < p.leadCoeff then 1 else if p.leadCoeff < 0 then -1 else 0

end Sign

end Poly

end LeviCivita
