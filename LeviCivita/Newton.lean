import LeviCivita.Hensel

/-!
# Hensel's lemma by Newton iteration

For a polynomial `P` over `L` with finite coefficients (`Integral P`), the residue
polynomial `stP P` over `R` is taken coefficientwise. **Hensel's lemma**
(`LCData.hensel`): a simple root `c` of `stP P` lifts to a root `r` of `P` with
`st r = c`.

The proof normalises to `H(w) = H₀ + w + w²(…)` with `H₀` infinitesimal and runs
Newton's method `wₖ₊₁ = wₖ − H(wₖ)/H'(wₖ)` from `w₀ = 0`. With `K = 4Y + 1`
(`Y` bounds the Taylor remainder on the unit ball) and `|K H₀| ≤ E = ε^μ`, one
step gives `K |H(wₖ₊₁)| ≤ (K |H(wₖ)|)²`, so `K |H(wₖ)| ≤ E^{k+1}`. The iterates
form a Cauchy sequence, and the limit is a root by continuity.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita

open Lean.Grind Series Series.PS Poly Limits Classical

attribute [local instance] Semiring.natCast Ring.intCast
attribute [local instance high] Semiring.ofNat

universe u v

namespace Poly

variable {F : Type u} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F]
  [OrderedRing F]

theorem one_le_ff (j k : Nat) : (1 : F) ≤ (ff j k : F) := by
  have := OrderedRing.natCast_le_natCast_of_le (R := F) 1 (ff j k) (ff_pos j k)
  rwa [Semiring.natCast_one] at this

theorem tay_coeff_ff {n : Nat} {p : PS F} (hp : IsPoly n p) (c : F) (k : Nat) :
    (ff 0 k : F) * (tay n p c).coeff k = eval n (derivN k p) c := by
  have := tay_derivN_coeff hp c k 0
  rw [tay_coeff_zero, Nat.zero_add] at this; exact this.symm

/-- The `k`-th Taylor coefficient is `p⁽ᵏ⁾(c) / k!`. -/
theorem tay_coeff_eq {n : Nat} {p : PS F} (hp : IsPoly n p) (c : F) (k : Nat) :
    (tay n p c).coeff k = eval n (derivN k p) c * ((ff 0 k : F))⁻¹ := by
  have h := tay_coeff_ff hp c k
  have hne : (ff 0 k : F) ≠ 0 := by have := one_le_ff (F := F) 0 k; grind
  rw [← h]
  have := Field.mul_inv_cancel hne
  grind

theorem abs_tay_coeff_le {n : Nat} {p : PS F} (hp : IsPoly n p) {w : F} (hw : abs w ≤ 1)
    (k : Nat) : abs ((tay n p w).coeff k) ≤ S (n + 1) (fun i => abs ((derivN k p).coeff i)) := by
  have h := tay_coeff_ff hp w k
  have h1 := abs_eval_le n (derivN k p) hw
  have hff := one_le_ff (F := F) 0 k
  rw [← h, abs_mul, abs_of_nonneg (Std.le_trans OrderedRing.zero_le_one hff)] at h1
  have := OrderedRing.mul_le_mul_of_nonneg_right hff (abs_nonneg ((tay n p w).coeff k))
  grind

/-- A bound for the second-order Taylor remainder on the unit ball. -/
noncomputable def tbound (n : Nat) (p : PS F) : F :=
  S (n + 1) (fun i => S (n + 1) (fun i' => abs ((derivN (i + 2) p).coeff i')))

theorem tbound_nonneg (n : Nat) (p : PS F) : 0 ≤ tbound n p :=
  S_nonneg fun _ _ => S_nonneg fun _ _ => abs_nonneg _

theorem eval_two (n : Nat) (t : PS F) (h : F) :
    eval (n + 2) t h = t.coeff 0 + t.coeff 1 * h + h * h * eval n (shiftDown (shiftDown t)) h := by
  have e : (shiftDown t).coeff 0 = t.coeff 1 := rfl
  show eval (n + 1 + 1) t h = _
  rw [eval_succ, eval_succ, e]; grind

/-- Second-order Taylor bound: `|p(w + h) − p(w) − p'(w) h| ≤ |h|² · tbound`. -/
theorem remainder {n : Nat} {p : PS F} (hp : IsPoly n p) {w h : F} (hw : abs w ≤ 1)
    (hh : abs h ≤ 1) :
    abs (eval n p (w + h) - eval n p w - (tay n p w).coeff 1 * h) ≤
      abs h * abs h * tbound n p := by
  have ht := isPoly_tay n p w
  rw [← eval_tay, ← eval_mono ht (show n ≤ n + 2 by omega), eval_two, tay_coeff_zero]
  rw [show eval n p w + (tay n p w).coeff 1 * h +
      h * h * eval n (shiftDown (shiftDown (tay n p w))) h - eval n p w - (tay n p w).coeff 1 * h =
      h * h * eval n (shiftDown (shiftDown (tay n p w))) h by grind]
  rw [abs_mul, abs_mul]
  apply OrderedRing.mul_le_mul_of_nonneg_left _
    (OrderedRing.mul_nonneg (abs_nonneg h) (abs_nonneg h))
  unfold tbound
  refine Std.le_trans (abs_eval_le n _ hh) (S_le fun i _ => ?_)
  exact abs_tay_coeff_le hp hw (i + 2)

/-- Scalar multiple of a polynomial. -/
def smul (a : F) (p : PS F) : PS F := ⟨fun i => a * p.coeff i⟩

theorem eval_smul (n : Nat) (a : F) (p : PS F) (x : F) :
    eval n (smul a p) x = a * eval n p x := by
  unfold eval; rw [← S_mul_left]
  exact S_congr fun i _ => by show a * p.coeff i * x ^ i = _; grind

theorem isPoly_smul {n : Nat} (a : F) {p : PS F} (hp : IsPoly n p) : IsPoly n (smul a p) :=
  fun i hi => by show a * p.coeff i = 0; rw [hp i hi]; grind

/-- Newton iterates from `0`. -/
def newton (n : Nat) (H : PS F) : Nat → F
  | 0 => 0
  | k + 1 => newton n H k - eval n H (newton n H k) * ((tay n H (newton n H k)).coeff 1)⁻¹

theorem pow_anti {x : F} (h0 : 0 ≤ x) (h1 : x ≤ 1) {i j : Nat} (h : i ≤ j) : x ^ j ≤ x ^ i := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  rw [Semiring.pow_add]
  have := OrderedRing.mul_le_mul_of_nonneg_left (pow_le_one h0 h1 d) (pow_nonneg h0 i)
  grind

end Poly

theorem exists_nat_mul_ge {μ : Rat} (hμ : 0 < μ) (ν : Rat) : ∃ N : Nat, ν ≤ ((N + 1 : Nat) : Rat) * μ := by
  obtain ⟨N, hN⟩ := Real.rat_archimedean (ν / μ)
  refine ⟨N, ?_⟩
  have h1 : (N : Rat) ≤ ((N + 1 : Nat) : Rat) := Rat.natCast_le_natCast.mpr (by omega)
  have h2 := OrderedRing.mul_lt_mul_of_pos_right hN hμ
  have h3 := OrderedRing.mul_le_mul_of_nonneg_right h1 (Std.le_of_lt hμ)
  have : ν / μ * μ = ν := by
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ (by grind), Rat.mul_one]
  grind

namespace LCData

variable {R : Type u} {L : Type v}
  [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
  [Field L] [LE L] [LT L] [Std.IsLinearOrder L] [Std.LawfulOrderLT L] [OrderedRing L]
  (D : LCData R L)

/-! ## Integral polynomials and residues -/

/-- All coefficients are finite. -/
def Integral (P : PS L) : Prop := ∀ i, D.Fin (P.coeff i)

/-- The residue polynomial. -/
noncomputable def stP (P : PS L) : PS R := ⟨fun i => D.st (P.coeff i)⟩

theorem stP_coeff (P : PS L) (i : Nat) : (D.stP P).coeff i = D.st (P.coeff i) := rfl

theorem st_zero : D.st (0 : L) = 0 := by rw [← D.ι_zero, D.st_ι]

theorem st_one : D.st (1 : L) = 1 := by rw [← D.ι_one, D.st_ι]

theorem fin_one : D.Fin (1 : L) := by rw [← D.ι_one]; exact D.fin_ι 1

theorem isPoly_stP {n : Nat} {P : PS L} (hP : IsPoly n P) : IsPoly n (D.stP P) := fun i hi => by
  rw [stP_coeff, hP i hi, D.st_zero]

theorem fin_abs {x : L} (h : D.Fin x) : D.Fin (abs x) := by
  obtain ⟨r, hr⟩ := h; exact ⟨r, by rw [abs_of_nonneg (abs_nonneg x)]; exact hr⟩

theorem fin_eval {n : Nat} {P : PS L} (hP : D.Integral P) {x : L} (hx : D.Fin x) :
    D.Fin (eval n P x) :=
  D.fin_S fun i _ => D.fin_mul (hP i) (D.fin_pow hx i)

theorem st_eval {n : Nat} {P : PS L} (hP : D.Integral P) {x : L} (hx : D.Fin x) :
    D.st (eval n P x) = eval n (D.stP P) (D.st x) := by
  unfold eval
  rw [D.st_S fun i _ => D.fin_mul (hP i) (D.fin_pow hx i)]
  exact S_congr fun i _ => by rw [D.st_mul (hP i) (D.fin_pow hx i), D.st_pow hx]; rfl

theorem integral_derivN {P : PS L} (hP : D.Integral P) (k : Nat) : D.Integral (derivN k P) :=
  fun i => by rw [coeff_derivN]; exact D.fin_mul (D.fin_natCast _) (hP _)

theorem stP_derivN {P : PS L} (hP : D.Integral P) (k : Nat) :
    D.stP (derivN k P) = derivN k (D.stP P) := by
  ext i
  rw [stP_coeff, coeff_derivN, coeff_derivN, D.st_mul (D.fin_natCast _) (hP _), D.st_natCast,
    stP_coeff]

theorem inv_ff (k : Nat) : ((ff 0 k : L))⁻¹ = D.ι ((ff 0 k : R)⁻¹) := by
  have : (ff 0 k : R) ≠ 0 := by have := one_le_ff (F := R) 0 k; grind
  rw [D.ι_inv this, D.ι_natCast]

theorem integral_tay {n : Nat} {P : PS L} (hn : IsPoly n P) (hP : D.Integral P) {c : L}
    (hc : D.Fin c) : D.Integral (tay n P c) := fun k => by
  rw [tay_coeff_eq hn, D.inv_ff]
  exact D.fin_mul (D.fin_eval (D.integral_derivN hP k) hc) (D.fin_ι _)

/-- Residues commute with Taylor expansion. -/
theorem stP_tay {n : Nat} {P : PS L} (hn : IsPoly n P) (hP : D.Integral P) {c : L}
    (hc : D.Fin c) : D.stP (tay n P c) = tay n (D.stP P) (D.st c) := by
  ext k
  rw [stP_coeff, tay_coeff_eq hn, D.inv_ff,
    D.st_mul (D.fin_eval (D.integral_derivN hP k) hc) (D.fin_ι _), D.st_ι,
    D.st_eval (D.integral_derivN hP k) hc, D.stP_derivN hP, tay_coeff_eq (D.isPoly_stP hn)]

/-! ## Newton's method -/

/-- **Hensel's lemma, normalised**: `H₀` infinitesimal and `H₁ = 1` give an infinitesimal
root. -/
theorem hensel_core {n : Nat} {H : PS L} (hn : IsPoly n H) (hI : D.Integral H)
    (h0 : D.Inf (H.coeff 0)) (h1 : H.coeff 1 = 1) : ∃ w, D.Inf w ∧ eval n H w = 0 := by
  -- constants
  have hY0 := tbound_nonneg n H
  have hYfin : D.Fin (tbound n H) :=
    D.fin_S fun i _ => D.fin_S fun i' _ => D.fin_abs (D.integral_derivN hI (i + 2) i')
  obtain ⟨Y, hY⟩ : ∃ Y, Y = tbound n H := ⟨_, rfl⟩
  rw [← hY] at hY0 hYfin
  obtain ⟨K, hK⟩ : ∃ K, K = Y + Y + Y + Y + 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by grind
  have hK0 : 0 ≤ K := by grind
  have hKfin : D.Fin K := by
    rw [hK]; exact D.fin_add (D.fin_add (D.fin_add (D.fin_add hYfin hYfin) hYfin) hYfin) D.fin_one
  obtain ⟨μ, hμ, hKH⟩ := D.inf_le_e (D.inf_mul' hKfin h0)
  rw [abs_mul, abs_of_nonneg hK0] at hKH
  obtain ⟨E, hE⟩ : ∃ E, E = D.e μ := ⟨_, rfl⟩
  rw [← hE] at hKH
  have hE0 : 0 < E := by rw [hE]; exact D.e_pos μ
  have hEinf : D.Inf E := by rw [hE]; exact D.inf_e hμ
  have hE2 : E + E ≤ 1 := by
    have := hEinf (2⁻¹) (Field.IsOrdered.inv_pos_iff.mpr (by grind))
    rw [abs_of_nonneg (Std.le_of_lt hE0), D.ι_inv (by grind), D.ι_two] at this
    have := Field.mul_inv_cancel (show (2 : L) ≠ 0 by grind)
    grind
  have h4inf : D.Inf (E + E + E + E) := D.inf_add (D.inf_add (D.inf_add hEinf hEinf) hEinf) hEinf
  have small : ∀ x : L, abs x ≤ E + E + E + E → D.Inf x ∧ abs x ≤ 1 := fun x hx => by
    have h4 : 0 ≤ E + E + E + E := by grind
    have h := h4inf 1 (by grind)
    rw [D.ι_one, abs_of_nonneg h4] at h
    refine ⟨fun r hr => ?_, by grind⟩
    have := h4inf r hr; rw [abs_of_nonneg h4] at this; grind
  -- one Newton step
  have step : ∀ x p : L, D.Inf x → abs x ≤ 1 → K * abs (eval n H x) ≤ p → 0 ≤ p → p ≤ E →
      abs (x - eval n H x * ((tay n H x).coeff 1)⁻¹ - x) ≤ p + p ∧
      K * abs (eval n H (x - eval n H x * ((tay n H x).coeff 1)⁻¹)) ≤ p * p := by
    intro x p hx hx1 hKa hp0 hpE
    have hxf := D.fin_of_inf hx
    have hTI := D.integral_tay hn hI hxf
    have hst1 : D.st ((tay n H x).coeff 1) = 1 := by
      have e := congrArg (fun q => q.coeff 1) (D.stP_tay hn hI hxf)
      simp only [stP_coeff] at e
      rw [e, (D.inf_iff_st hxf).mp hx, tay_zero (D.isPoly_stP hn), stP_coeff, h1, D.st_one]
    obtain ⟨htne, -, hstinv⟩ := D.st_inv (hTI 1) (by rw [hst1]; grind)
    have hinvfin := (D.st_inv (hTI 1) (by rw [hst1]; grind)).2.1
    rw [hst1, Field.inv_one] at hstinv
    have hinv2 : abs ((tay n H x).coeff 1)⁻¹ ≤ 1 + 1 := by
      have := D.abs_le_st hinvfin
      rwa [hstinv, abs_of_nonneg OrderedRing.zero_le_one, D.ι_add, D.ι_one] at this
    obtain ⟨t, ht⟩ : ∃ t, t = (tay n H x).coeff 1 := ⟨_, rfl⟩
    rw [← ht] at hinv2 htne ⊢
    obtain ⟨a, ha⟩ : ∃ a, a = eval n H x := ⟨_, rfl⟩
    rw [← ha] at hKa ⊢
    have hA : abs a ≤ p := by
      have := OrderedRing.mul_le_mul_of_nonneg_right hK1 (abs_nonneg a); grind
    have hh : abs (-(a * t⁻¹)) ≤ abs a + abs a := by
      rw [abs_neg, abs_mul]
      have := OrderedRing.mul_le_mul_of_nonneg_left hinv2 (abs_nonneg a); grind
    have hh1 : abs (-(a * t⁻¹)) ≤ 1 := by grind
    have hrem := remainder hn hx1 hh1
    rw [← ht, ← ha] at hrem
    have hz : eval n H (x + -(a * t⁻¹)) - a - t * -(a * t⁻¹) = eval n H (x + -(a * t⁻¹)) := by
      have := Field.mul_inv_cancel htne; grind
    rw [hz, ← hY] at hrem
    rw [show x - a * t⁻¹ = x + -(a * t⁻¹) by grind]
    refine ⟨by rw [show x + -(a * t⁻¹) - x = -(a * t⁻¹) by grind]; grind, ?_⟩
    have s1 := mul_le_mul_of_le hh hh (abs_nonneg _) (abs_nonneg _)
    have s2 := OrderedRing.mul_le_mul_of_nonneg_right s1 hY0
    have hAA : 0 ≤ abs a * abs a := OrderedRing.mul_nonneg (abs_nonneg a) (abs_nonneg a)
    have s3 : (abs a + abs a) * (abs a + abs a) * Y ≤ abs a * abs a * K := by
      have := OrderedRing.mul_le_mul_of_nonneg_left (show Y + Y + Y + Y ≤ K by grind) hAA
      grind
    have s4 := OrderedRing.mul_le_mul_of_nonneg_left
      (Std.le_trans hrem (Std.le_trans s2 s3)) hK0
    have s6 := mul_le_mul_of_le hKa hKa
      (OrderedRing.mul_nonneg hK0 (abs_nonneg a)) (OrderedRing.mul_nonneg hK0 (abs_nonneg a))
    have s5 : K * (abs a * abs a * K) = K * abs a * (K * abs a) := by grind
    rw [s5] at s4
    exact Std.le_trans s4 s6
  -- the invariant
  have hpow : ∀ k : Nat, 0 < E ^ (k + 1) ∧ E ^ (k + 1) ≤ E := fun k => by
    refine ⟨pow_pos hE0 _, ?_⟩
    rw [Semiring.pow_succ]
    have := OrderedRing.mul_le_mul_of_nonneg_right
      (pow_le_one (Std.le_of_lt hE0) (show E ≤ 1 by grind) k) (Std.le_of_lt hE0)
    grind
  have hinv : ∀ k : Nat, abs (newton n H k) + (E ^ (k + 1) + E ^ (k + 1) + E ^ (k + 1) +
      E ^ (k + 1)) ≤ E + E + E + E ∧ K * abs (eval n H (newton n H k)) ≤ E ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      have e0 : newton n H 0 = 0 := rfl
      rw [e0, abs_zero, RCF.eval_at_zero, Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul]
      exact ⟨by grind, hKH⟩
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      obtain ⟨hP0, hPE⟩ := hpow k
      have hx := small (newton n H k) (by grind)
      obtain ⟨s1, s2⟩ := step _ _ hx.1 hx.2 ih2 (Std.le_of_lt hP0) hPE
      have e : newton n H (k + 1) = newton n H k -
          eval n H (newton n H k) * ((tay n H (newton n H k)).coeff 1)⁻¹ := rfl
      rw [e, show E ^ (k + 1 + 1) = E ^ (k + 1) * E from Semiring.pow_succ _ _]
      constructor
      · have := abs_add_le (newton n H k - eval n H (newton n H k) *
          ((tay n H (newton n H k)).coeff 1)⁻¹ - newton n H k) (newton n H k)
        rw [show newton n H k - eval n H (newton n H k) * ((tay n H (newton n H k)).coeff 1)⁻¹ -
          newton n H k + newton n H k = newton n H k - eval n H (newton n H k) *
          ((tay n H (newton n H k)).coeff 1)⁻¹ by grind] at this
        have := OrderedRing.mul_le_mul_of_nonneg_left hE2 (Std.le_of_lt hP0)
        grind
      · exact Std.le_trans s2 (OrderedRing.mul_le_mul_of_nonneg_left hPE (Std.le_of_lt hP0))
  have hinc : ∀ k : Nat, abs (newton n H (k + 1) - newton n H k) ≤ E ^ (k + 1) + E ^ (k + 1) :=
    fun k => by
      obtain ⟨ih1, ih2⟩ := hinv k
      obtain ⟨hP0, hPE⟩ := hpow k
      have hx := small (newton n H k) (by grind)
      exact (step _ _ hx.1 hx.2 ih2 (Std.le_of_lt hP0) hPE).1
  -- telescoping
  have htel : ∀ k m : Nat, abs (newton n H (k + m) - newton n H k) +
      (E ^ (k + m + 1) + E ^ (k + m + 1) + E ^ (k + m + 1) + E ^ (k + m + 1)) ≤
      E ^ (k + 1) + E ^ (k + 1) + E ^ (k + 1) + E ^ (k + 1) := by
    intro k m
    induction m with
    | zero => rw [Nat.add_zero, show newton n H k - newton n H k = 0 by grind, abs_zero]; grind
    | succ m ih =>
      have h1 := hinc (k + m)
      have h2 := abs_add_le (newton n H (k + m + 1) - newton n H (k + m))
        (newton n H (k + m) - newton n H k)
      rw [show newton n H (k + m + 1) - newton n H (k + m) + (newton n H (k + m) - newton n H k) =
        newton n H (k + m + 1) - newton n H k by grind] at h2
      obtain ⟨hP0, -⟩ := hpow (k + m)
      have := OrderedRing.mul_le_mul_of_nonneg_left hE2 (Std.le_of_lt hP0)
      rw [show k + (m + 1) = k + m + 1 by omega,
        show E ^ (k + m + 1 + 1) = E ^ (k + m + 1) * E from Semiring.pow_succ _ _]
      grind
  have hsmallpow : ∀ d : L, 0 < d → ∃ N : Nat, E ^ (N + 1) < d := fun d hd => by
    obtain ⟨ν, hν⟩ := D.exists_e_lt hd
    obtain ⟨N, hN⟩ := exists_nat_mul_ge hμ ν
    refine ⟨N, ?_⟩
    rw [hE, ← D.e_natMul]
    exact Std.lt_of_le_of_lt (D.e_anti hN) hν
  -- Cauchy
  have hcauchy : Cauchy.IsCauchy (newton n H) := isCauchy_of fun d hd => by
    obtain ⟨N, hN⟩ := hsmallpow (d / 2 / 2 / 2) (half_pos (half_pos (half_pos hd)))
    refine ⟨N, fun a b ha hb => ?_⟩
    have t1 := htel N (a - N)
    have t2 := htel N (b - N)
    rw [show N + (a - N) = a by omega] at t1
    rw [show N + (b - N) = b by omega] at t2
    have := pow_pos hE0 (a + 1); have := pow_pos hE0 (b + 1)
    have h3 := abs_add_le (newton n H a - newton n H N) (newton n H N - newton n H b)
    rw [show newton n H a - newton n H N + (newton n H N - newton n H b) =
      newton n H a - newton n H b by grind, abs_sub_comm (newton n H N)] at h3
    grind
  obtain ⟨x, hx⟩ := D.complete _ hcauchy
  -- the limit is a root
  have hzero : Tendsto (fun k => eval n H (newton n H k)) 0 := fun d hd => by
    obtain ⟨N, hN⟩ := hsmallpow d hd
    refine ⟨N, fun k hk => ?_⟩
    have h1 := (hinv k).2
    have h2 := pow_anti (Std.le_of_lt hE0) (show E ≤ 1 by grind) (show N + 1 ≤ k + 1 by omega)
    have := OrderedRing.mul_le_mul_of_nonneg_right hK1 (abs_nonneg (eval n H (newton n H k)))
    rw [show eval n H (newton n H k) - 0 = eval n H (newton n H k) by grind]
    grind
  have hroot := tendsto_unique (tendsto_eval n H hx) hzero
  refine ⟨x, ?_, hroot⟩
  have hb : ∀ k, abs (newton n H k) ≤ E + E + E + E := fun k => by
    have := (hinv k).1; have := pow_pos hE0 (k + 1); grind
  have u := le_of_tendsto hx (b := E + E + E + E) fun k => ((abs_le_iff).mp (hb k)).1
  have l := ge_of_tendsto hx (b := -(E + E + E + E)) fun k => by
    have := ((abs_le_iff).mp (hb k)).2; grind
  exact (small x ((abs_le_iff).mpr ⟨u, by grind⟩)).1

/-- **Hensel's lemma**: a simple root `c` of the residue polynomial lifts to a root `r`
of `P` with `r − ι c` infinitesimal. -/
theorem hensel {n : Nat} {P : PS L} (hn : IsPoly n P) (hI : D.Integral P) {c : R}
    (hc : IsOrd (tay n (D.stP P) c) 1) : ∃ r, D.Inf (r - D.ι c) ∧ eval n P r = 0 := by
  have hcf := D.fin_ι c
  have hGI := D.integral_tay hn hI hcf
  have hst := D.stP_tay hn hI hcf
  rw [D.st_ι] at hst
  obtain ⟨hc0, hc1⟩ := hc
  have g0 : D.st ((tay n P (D.ι c)).coeff 0) = 0 := by
    have := congrArg (fun q => q.coeff 0) hst
    simp only [stP_coeff] at this; rw [this]; exact hc0 0 (by omega)
  have g1 : D.st ((tay n P (D.ι c)).coeff 1) ≠ 0 := by
    have := congrArg (fun q => q.coeff 1) hst
    simp only [stP_coeff] at this; rw [this]; exact hc1
  obtain ⟨hgne, hginv, -⟩ := D.st_inv (hGI 1) g1
  obtain ⟨w, hw, hw0⟩ := D.hensel_core (H := smul ((tay n P (D.ι c)).coeff 1)⁻¹ (tay n P (D.ι c)))
    (isPoly_smul _ (isPoly_tay n P _)) (fun i => D.fin_mul hginv (hGI i))
    (D.inf_mul' hginv ((D.inf_iff_st (hGI 0)).mpr g0)) (Field.inv_mul_cancel hgne)
  refine ⟨D.ι c + w, by rw [show D.ι c + w - D.ι c = w by grind]; exact hw, ?_⟩
  rw [eval_smul, eval_tay] at hw0
  have := Field.mul_inv_cancel hgne
  calc eval n P (D.ι c + w)
      = (tay n P (D.ι c)).coeff 1 * (((tay n P (D.ι c)).coeff 1)⁻¹ * eval n P (D.ι c + w)) := by
        rw [← Semiring.mul_assoc, this, Semiring.one_mul]
    _ = 0 := by rw [hw0]; grind

end LCData

end LeviCivita
