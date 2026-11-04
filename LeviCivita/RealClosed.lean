import LeviCivita.Newton

/-!
# Real-closedness of Levi-Civita-like fields

`IsRealClosed L`: every positive element is a square, and every odd-degree
polynomial has a root (the Artin–Schreier characterisation of real-closed
ordered fields).

**Main theorem** (`LCData.isRealClosed`): if `L` carries `LCData R L` and the
coefficient field `R` has the intermediate value property for polynomials
(`IVT R`), then `L` is real closed.

Proof of the odd-degree case:

1. Normalise `P` to be monic and rescale `w ↦ ε^λ w` with
   `λ = min_{j<n} v(Pⱼ)/(n − j)`. The rescaled polynomial `T` is integral and its
   residue `T̄` has odd degree `n`, so (IVT over `R`) `T̄` has a root `c` of odd
   multiplicity `m`.
2. **Descent** (`descent`), by strong induction on odd `m`: an integral `P` whose
   residue has a root `c` of odd multiplicity `m` has a root.
   * `m = 1`: Hensel's lemma.
   * `m > 1`: Hensel applied to `P⁽ᵐ⁻¹⁾` (residue root `c` is simple) gives `r₀`
     with `P⁽ᵐ⁻¹⁾(r₀) = 0`. Expand `G = P(r₀ + ·)`, so `G_{m−1} = 0`, and rescale by
     `λ = min_{j<m} v(Gⱼ)/(m − j) > 0`. The new residue has degree `m`, a zero
     coefficient at `m − 1` and a nonzero one below `m`. Its odd-multiplicity root
     therefore has multiplicity `< m`, and induction applies.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita

open Lean.Grind Series Series.PS Poly Limits Classical

attribute [local instance] Semiring.natCast Ring.intCast
attribute [local instance high] Semiring.ofNat

universe u v

/-- Artin–Schreier form of real-closedness. -/
def IsRealClosed (L : Type v) [Field L] [LE L] [LT L] [Std.IsLinearOrder L]
    [Std.LawfulOrderLT L] [OrderedRing L] : Prop :=
  (∀ x : L, 0 < x → ∃ y, y * y = x) ∧
  ∀ (n : Nat) (p : PS L), IsPoly n p → n % 2 = 1 → p.coeff n ≠ 0 → ∃ x, eval n p x = 0

namespace Poly

variable {F : Type u} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F]
  [OrderedRing F]

theorem mul_pow' (a b : F) (k : Nat) : (a * b) ^ k = a ^ k * b ^ k := by
  induction k with
  | zero => rw [Semiring.pow_zero, Semiring.pow_zero, Semiring.pow_zero, Semiring.mul_one]
  | succ k ih => rw [Semiring.pow_succ, Semiring.pow_succ, Semiring.pow_succ, ih]; grind

theorem mul_ne_zero' {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := fun h => by
  have : a⁻¹ * (a * b) = b := by
    rw [← Semiring.mul_assoc, Field.inv_mul_cancel ha, Semiring.one_mul]
  rw [h] at this; grind

theorem inv_ne_zero' {a : F} (ha : a ≠ 0) : a⁻¹ ≠ 0 := fun h => by
  have := Field.mul_inv_cancel ha; rw [h] at this; grind

theorem natCast_ne_zero' {k : Nat} (hk : 0 < k) : (k : F) ≠ 0 := by
  have := OrderedRing.pos_natCast_of_pos (R := F) k hk; grind

theorem div_pos' {a b : F} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [Field.div_eq_mul_inv]; exact OrderedRing.mul_pos ha (Field.IsOrdered.inv_pos_iff.mpr hb)

theorem mul_div_cancel' {d : F} (hd : 0 < d) (v : F) : d * (v / d) = v := by
  rw [Field.div_eq_mul_inv]
  have := Field.mul_inv_cancel (show d ≠ 0 by grind); grind

theorem mul_le_of_le_div {d l v : F} (hd : 0 < d) (h : l ≤ v / d) : d * l ≤ v := by
  have := OrderedRing.mul_le_mul_of_nonneg_left h (Std.le_of_lt hd)
  rw [mul_div_cancel' hd] at this; exact this

/-- Taylor expansion does not depend on a larger degree bound. -/
theorem tay_mono {m N : Nat} {p : PS F} (hp : IsPoly m p) (h : m ≤ N) (c : F) :
    tay N p c = tay m p c :=
  eq_of_eval_pos (isPoly_tay N p c) ((isPoly_tay m p c).mono h) fun z _ => by
    rw [eval_tay, eval_mono (isPoly_tay m p c) h, eval_tay, eval_mono hp h]

/-- `y² − a`. -/
def sqPoly (a : F) : PS F := ⟨fun i => if i = 0 then -a else if i = 2 then 1 else 0⟩

theorem isPoly_sqPoly (a : F) : IsPoly 2 (sqPoly a) := fun i hi => by
  show (if i = 0 then -a else if i = 2 then 1 else 0) = 0
  rw [if_neg (by omega), if_neg (by omega)]

theorem eval_sqPoly (a y : F) : eval 2 (sqPoly a) y = y * y - a := by
  have c0 : (sqPoly a).coeff 0 = -a := rfl
  have c1 : (sqPoly a).coeff 1 = 0 := rfl
  have c2 : (sqPoly a).coeff 2 = 1 := rfl
  unfold eval; show S (0 + 1 + 1 + 1) _ = _
  rw [S_succ, S_succ, S_succ, S_zero]; simp only [c0, c1, c2]; grind

/-- A nonzero square root is a simple root of `y² − a`. -/
theorem sqPoly_simple {r s : F} (hs : s * s = r) (hs0 : s ≠ 0) : IsOrd (tay 2 (sqPoly r) s) 1 := by
  constructor
  · intro i hi
    have : i = 0 := by omega
    subst this; rw [tay_coeff_zero, eval_sqPoly]; grind
  · have h := tay_coeff_ff (isPoly_sqPoly r) s 1
    have e1 : ((ff 0 1 : Nat) : F) = 1 := by rw [show ff 0 1 = 1 from rfl, Semiring.natCast_one]
    have e2 : eval 2 (derivN 1 (sqPoly r)) s = s + s := by
      show eval 2 (deriv (sqPoly r)) s = _
      have c1 : (sqPoly r).coeff 1 = 0 := rfl
      have c2 : (sqPoly r).coeff 2 = 1 := rfl
      have c3 : (sqPoly r).coeff 3 = 0 := rfl
      have n2 : ((2 : Nat) : F) = 1 + 1 := by
        rw [show (2 : Nat) = 1 + 1 from rfl, Semiring.natCast_add, Semiring.natCast_one]
      unfold eval; show S (0 + 1 + 1 + 1) _ = _
      rw [S_succ, S_succ, S_succ, S_zero]; simp only [coeff_deriv, c1, c2, c3, n2]; grind
    rw [e1, e2, Semiring.one_mul] at h
    rw [h]; grind

end Poly

theorem exists_min (P : Nat → Prop) (f : Nat → Rat) :
    ∀ m : Nat, (∃ j, j < m ∧ P j) → ∃ j, j < m ∧ P j ∧ ∀ i, i < m → P i → f j ≤ f i := by
  intro m
  induction m with
  | zero => intro ⟨j, hj, _⟩; omega
  | succ m ih =>
    intro ⟨j, hj, hPj⟩
    by_cases h : ∃ j, j < m ∧ P j
    · obtain ⟨k, hk, hPk, hmin⟩ := ih h
      by_cases hm : P m ∧ f m < f k
      · refine ⟨m, by omega, hm.1, fun i hi hPi => ?_⟩
        rcases (by omega : i < m ∨ i = m) with h' | h'
        · have := hmin i h' hPi; grind
        · rw [h']; exact Std.le_refl _
      · refine ⟨k, by omega, hPk, fun i hi hPi => ?_⟩
        rcases (by omega : i < m ∨ i = m) with h' | h'
        · exact hmin i h' hPi
        · rw [h'] at hPi ⊢; grind
    · have hjm : j = m := by
        apply Classical.byContradiction; intro hne; exact h ⟨j, by omega, hPj⟩
      refine ⟨j, by omega, hPj, fun i hi hPi => ?_⟩
      rcases (by omega : i < m ∨ i = m) with h' | h'
      · exact absurd ⟨i, h', hPi⟩ h
      · rw [h', ← hjm]; exact Std.le_refl _

namespace LCData

variable {R : Type u} {L : Type v}
  [Field R] [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
  [Field L] [LE L] [LT L] [Std.IsLinearOrder L] [Std.LawfulOrderLT L] [OrderedRing L]
  (D : LCData R L)

/-! ## Valuations -/

theorem exists_val {x : L} (hx : x ≠ 0) :
    ∃ q : Rat, D.Fin (x * D.e (-q)) ∧ D.st (x * D.e (-q)) ≠ 0 := by
  obtain ⟨r, q, δ, hr, hδ, hxe⟩ := D.lead' x hx
  have e : x * D.e (-q) = D.ι r * (1 + δ) := by
    rw [hxe, D.e_neg]; have := Field.mul_inv_cancel (D.e_ne_zero q); grind
  have h1 : D.Fin (1 + δ) := D.fin_add D.fin_one (D.fin_of_inf hδ)
  have hst : D.st (1 + δ) = 1 :=
    D.st_eq (by rw [D.ι_one, show 1 + δ - 1 = δ by grind]; exact hδ)
  refine ⟨q, by rw [e]; exact D.fin_mul (D.fin_ι r) h1, ?_⟩
  rw [e, D.st_mul (D.fin_ι r) h1, D.st_ι, hst]; grind

/-- A valuation: `x ε^{-v x}` is finite with nonzero standard part. -/
noncomputable def val (x : L) : Rat := if h : x ≠ 0 then Classical.choose (D.exists_val h) else 0

theorem val_spec {x : L} (hx : x ≠ 0) :
    D.Fin (x * D.e (-D.val x)) ∧ D.st (x * D.e (-D.val x)) ≠ 0 := by
  unfold val; rw [dif_pos hx]; exact Classical.choose_spec (D.exists_val hx)

theorem val_pos {x : L} (hx : x ≠ 0) (hinf : D.Inf x) : 0 < D.val x := by
  apply Classical.byContradiction; intro h
  have hs := D.val_spec hx
  exact hs.2 ((D.inf_iff_st hs.1).mp (D.inf_mul hinf (D.fin_e (by grind))))

theorem shift_e (x : L) (q t : Rat) : x * D.e t = x * D.e (-q) * D.e (q + t) := by
  rw [Semiring.mul_assoc, ← D.e_add]; congr 2; grind

theorem fin_coeff_scale {x : L} (hx : x ≠ 0) {t : Rat} (ht : 0 ≤ D.val x + t) :
    D.Fin (x * D.e t) := by
  rw [D.shift_e x (D.val x)]; exact D.fin_mul (D.val_spec hx).1 (D.fin_e ht)

theorem st_coeff_scale {x : L} (hx : x ≠ 0) {t : Rat} (ht : D.val x + t = 0) :
    D.st (x * D.e t) ≠ 0 := by
  rw [D.shift_e x (D.val x), ht, D.e_zero, Semiring.mul_one]; exact (D.val_spec hx).2

/-! ## Rescaling `w ↦ ε^λ w` -/

/-- Coefficients `Gⱼ ε^{(j−m)λ}`, so that `T(w) = ε^{−mλ} G(ε^λ w)`. -/
def sc (G : PS L) (lam : Rat) (m : Nat) : PS L :=
  ⟨fun j => G.coeff j * D.e (((j : Rat) - (m : Rat)) * lam)⟩

theorem isPoly_sc {N : Nat} {G : PS L} (hG : IsPoly N G) (lam : Rat) (m : Nat) :
    IsPoly N (D.sc G lam m) := fun i hi => by
  show G.coeff i * _ = 0; rw [hG i hi, Semiring.zero_mul]

theorem eval_sc (N : Nat) (G : PS L) (lam : Rat) (m : Nat) (w : L) :
    eval N (D.sc G lam m) w = D.e (-((m : Rat) * lam)) * eval N G (D.e lam * w) := by
  unfold eval; rw [← S_mul_left]
  refine S_congr fun j _ => ?_
  show G.coeff j * D.e (((j : Rat) - m) * lam) * w ^ j =
    D.e (-((m : Rat) * lam)) * (G.coeff j * (D.e lam * w) ^ j)
  rw [mul_pow', ← D.e_natMul, show ((j : Rat) - m) * lam = -((m : Rat) * lam) + (j : Rat) * lam by
    grind, D.e_add]
  grind

theorem root_of_sc {N : Nat} {G : PS L} {lam : Rat} {m : Nat} {w : L}
    (h : eval N (D.sc G lam m) w = 0) : eval N G (D.e lam * w) = 0 := by
  rw [D.eval_sc] at h
  apply Classical.byContradiction; intro hne
  exact mul_ne_zero' (D.e_ne_zero _) hne h

/-! ## The descent -/

theorem descent (hR : IVT R) (m : Nat) : (∃ k, m = 2 * k + 1) → ∀ (N : Nat) (P : PS L) (c : R),
    IsPoly N P → D.Integral P → IsOrd (tay N (D.stP P) c) m → ∃ r, eval N P r = 0 := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro hm N P c hN hI hord
  by_cases hm1 : m = 1
  · subst hm1; obtain ⟨r, -, hr⟩ := D.hensel hN hI hord; exact ⟨r, hr⟩
  have hm3 : 3 ≤ m := by obtain ⟨k, hk⟩ := hm; omega
  have hmN : m ≤ N := by
    apply Classical.byContradiction; intro h
    exact hord.2 (isPoly_tay N _ c m (by omega))
  -- a root of the `(m-1)`-th derivative
  have hQ := isPoly_derivN hN (m - 1)
  have hQI := D.integral_derivN hI (m - 1)
  have hPbar := D.isPoly_stP hN
  have hordQ : IsOrd (tay N (D.stP (derivN (m - 1) P)) c) 1 := by
    rw [D.stP_derivN hI]
    constructor
    · intro i hi
      have : i = 0 := by omega
      rw [this, tay_derivN_coeff hPbar, Nat.zero_add, hord.1 (m - 1) (by omega)]; grind
    · rw [tay_derivN_coeff hPbar, show 1 + (m - 1) = m by omega]
      exact mul_ne_zero' (natCast_ne_zero' (ff_pos 1 (m - 1))) hord.2
  obtain ⟨r0, hr0, hQr0⟩ := D.hensel hQ hQI hordQ
  have hr0f : D.Fin r0 := D.fin_of_inf_sub hr0
  have hr0st : D.st r0 = c := D.st_eq hr0
  -- expand at `r0`
  have hG := isPoly_tay N P r0
  have hGI := D.integral_tay hN hI hr0f
  have hGst' : ∀ j, D.st ((tay N P r0).coeff j) = (tay N (D.stP P) c).coeff j := fun j => by
    rw [← stP_coeff, D.stP_tay hN hI hr0f, hr0st]
  have hGm1 : (tay N P r0).coeff (m - 1) = 0 := by
    have h1 := tay_derivN_coeff hN r0 (m - 1) 0
    rw [tay_coeff_zero, hQr0, Nat.zero_add] at h1
    apply Classical.byContradiction; intro hne
    exact mul_ne_zero' (natCast_ne_zero' (ff_pos 0 (m - 1))) hne h1.symm
  have hroot : ∀ z, eval N (tay N P r0) z = 0 → eval N P (r0 + z) = 0 := fun z hz => by
    rw [eval_tay] at hz; exact hz
  obtain ⟨G, hGdef⟩ : ∃ G, G = tay N P r0 := ⟨_, rfl⟩
  rw [← hGdef] at hG hGI hGst' hGm1 hroot
  have hGinf : ∀ j, j < m → D.Inf (G.coeff j) := fun j hj =>
    (D.inf_iff_st (hGI j)).mpr (by rw [hGst']; exact hord.1 j hj)
  have hGm : D.st (G.coeff m) ≠ 0 := by rw [hGst']; exact hord.2
  by_cases hall : ∀ j, j < m → G.coeff j = 0
  · refine ⟨r0 + 0, hroot 0 ?_⟩
    rw [RCF.eval_at_zero]; exact hall 0 (by omega)
  have hex : ∃ j, j < m ∧ G.coeff j ≠ 0 := by
    apply Classical.byContradiction; intro h; apply hall; intro j hj
    apply Classical.byContradiction; intro h'; exact h ⟨j, hj, h'⟩
  obtain ⟨js, hjs, hjsne, hmin⟩ := exists_min (fun j => G.coeff j ≠ 0)
    (fun j => D.val (G.coeff j) / ((m : Rat) - (j : Rat))) m hex
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = D.val (G.coeff js) / ((m : Rat) - (js : Rat)) := ⟨_, rfl⟩
  have hdpos : ∀ j, j < m → 0 < (m : Rat) - (j : Rat) := fun j hj => by
    have := Rat.natCast_lt_natCast.mpr hj; grind
  have hlampos : 0 < lam := by
    rw [hlam]; exact div_pos' (D.val_pos hjsne (hGinf js hjs)) (hdpos js hjs)
  have hbound : ∀ j, j < m → G.coeff j ≠ 0 →
      0 ≤ D.val (G.coeff j) + ((j : Rat) - m) * lam := fun j hj hne => by
    have h1 := hmin j hj hne
    rw [← hlam] at h1
    have := mul_le_of_le_div (hdpos j hj) h1
    grind
  have hzero : D.val (G.coeff js) + ((js : Rat) - m) * lam = 0 := by
    rw [hlam]; have := mul_div_cancel' (hdpos js hjs) (D.val (G.coeff js)); grind
  -- the rescaled polynomial
  have hT := D.isPoly_sc hG lam m
  have hTI : D.Integral (D.sc G lam m) := fun j => by
    show D.Fin (G.coeff j * D.e (((j : Rat) - m) * lam))
    by_cases hj0 : G.coeff j = 0
    · rw [hj0, Semiring.zero_mul]; exact D.fin_of_inf D.inf_zero
    by_cases hjm : j < m
    · exact D.fin_coeff_scale hj0 (hbound j hjm hj0)
    · have := Rat.natCast_le_natCast.mpr (show m ≤ j by omega)
      exact D.fin_mul (hGI j) (D.fin_e (OrderedRing.mul_nonneg (by grind) (Std.le_of_lt hlampos)))
  obtain ⟨T, hTdef⟩ : ∃ T, T = D.stP (D.sc G lam m) := ⟨_, rfl⟩
  have hTc : ∀ j, T.coeff j = D.st (G.coeff j * D.e (((j : Rat) - m) * lam)) := fun j => by
    rw [hTdef]; rfl
  have hTdeg : IsPoly m T := fun j hj => by
    rw [hTc]
    apply (D.inf_iff_st (hTI j)).mp
    have := Rat.natCast_lt_natCast.mpr hj
    exact D.inf_mul' (hGI j) (D.inf_e (OrderedRing.mul_pos (by grind) hlampos))
  have hTm : T.coeff m ≠ 0 := by
    rw [hTc, show ((m : Rat) - m) * lam = 0 by grind, D.e_zero, Semiring.mul_one]; exact hGm
  have hTm1 : T.coeff (m - 1) = 0 := by
    rw [hTc, hGm1, Semiring.zero_mul, D.st_zero]
  have hTjs : T.coeff js ≠ 0 := by rw [hTc]; exact D.st_coeff_scale hjsne hzero
  obtain ⟨c', m', hm'odd, hord'⟩ :=
    RCF.odd_degree_odd_root hR hTdeg (by obtain ⟨k, hk⟩ := hm; omega) hTm
  have hm'' : ∃ k, m' = 2 * k + 1 := ⟨m' / 2, by omega⟩
  clear hm'odd
  have hm'le : m' ≤ m := by
    apply Classical.byContradiction; intro h
    exact hord'.2 (isPoly_tay m T c' m' (by omega))
  have hm'lt : m' < m := by
    apply Classical.byContradiction; intro h
    have hmm : m' = m := by omega
    rw [hmm] at hord'
    have h1 : (tay m T c').coeff (m - 1) = 0 := hord'.1 (m - 1) (by omega)
    have h2 := tay_derivN_coeff hTdeg c' (m - 1) 0
    rw [Nat.zero_add, h1, tay_coeff_zero] at h2
    have h3 : eval m (derivN (m - 1) T) c' = (ff 1 (m - 1) : R) * T.coeff m * c' := by
      unfold eval
      rw [S_eq_single (j := 1) (by omega) (fun i hi hi1 => by
        rw [coeff_derivN]
        rcases (by omega : i = 0 ∨ 2 ≤ i) with h | h
        · rw [h, Nat.zero_add, hTm1]; grind
        · rw [hTdeg (i + (m - 1)) (by omega)]; grind)]
      rw [coeff_derivN, show 1 + (m - 1) = m by omega]
      grind
    have hc' : c' = 0 := by
      rw [h3] at h2
      apply Classical.byContradiction; intro hne
      exact mul_ne_zero' (mul_ne_zero' (natCast_ne_zero' (ff_pos 1 (m - 1))) hTm) hne
        (by rw [h2]; grind)
    rw [hc', tay_zero hTdeg] at hord'
    exact hTjs (hord'.1 js hjs)
  obtain ⟨w, hw⟩ := ih m' hm'lt hm'' N (D.sc G lam m) c' hT hTI (by
    rw [← hTdef, tay_mono hTdeg hmN]; exact hord')
  exact ⟨r0 + D.e lam * w, hroot _ (D.root_of_sc hw)⟩

/-! ## Odd-degree polynomials -/

include D in
theorem odd_root (hR : IVT R) {n : Nat} {P : PS L} (hP : IsPoly n P) (hn : ∃ k, n = 2 * k + 1)
    (hlead : P.coeff n ≠ 0) : ∃ r, eval n P r = 0 := by
  obtain ⟨G, hGdef⟩ : ∃ G, G = smul (P.coeff n)⁻¹ P := ⟨_, rfl⟩
  have hG : IsPoly n G := by rw [hGdef]; exact isPoly_smul _ hP
  have hGn : G.coeff n = 1 := by rw [hGdef]; exact Field.inv_mul_cancel hlead
  have hroot : ∀ x, eval n G x = 0 → eval n P x = 0 := fun x hx => by
    rw [hGdef, eval_smul] at hx
    apply Classical.byContradiction; intro hne
    exact mul_ne_zero' (inv_ne_zero' hlead) hne hx
  have hn1 : 1 ≤ n := by obtain ⟨k, hk⟩ := hn; omega
  by_cases hall : ∀ j, j < n → G.coeff j = 0
  · exact ⟨0, hroot 0 (by rw [RCF.eval_at_zero]; exact hall 0 (by omega))⟩
  have hex : ∃ j, j < n ∧ G.coeff j ≠ 0 := by
    apply Classical.byContradiction; intro h; apply hall; intro j hj
    apply Classical.byContradiction; intro h'; exact h ⟨j, hj, h'⟩
  obtain ⟨js, hjs, hjsne, hmin⟩ := exists_min (fun j => G.coeff j ≠ 0)
    (fun j => D.val (G.coeff j) / ((n : Rat) - (j : Rat))) n hex
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = D.val (G.coeff js) / ((n : Rat) - (js : Rat)) := ⟨_, rfl⟩
  have hdpos : ∀ j, j < n → 0 < (n : Rat) - (j : Rat) := fun j hj => by
    have := Rat.natCast_lt_natCast.mpr hj; grind
  have hbound : ∀ j, j < n → G.coeff j ≠ 0 →
      0 ≤ D.val (G.coeff j) + ((j : Rat) - n) * lam := fun j hj hne => by
    have h1 := hmin j hj hne
    rw [← hlam] at h1
    have := mul_le_of_le_div (hdpos j hj) h1
    grind
  have hTI : D.Integral (D.sc G lam n) := fun j => by
    show D.Fin (G.coeff j * D.e (((j : Rat) - n) * lam))
    by_cases hj0 : G.coeff j = 0
    · rw [hj0, Semiring.zero_mul]; exact D.fin_of_inf D.inf_zero
    by_cases hjn : j < n
    · exact D.fin_coeff_scale hj0 (hbound j hjn hj0)
    · have hj : j = n := by
        apply Classical.byContradiction; intro h; exact hj0 (hG j (by omega))
      rw [hj, hGn, show ((n : Rat) - n) * lam = 0 by grind, D.e_zero, Semiring.mul_one]
      exact D.fin_one
  have hTdeg : IsPoly n (D.stP (D.sc G lam n)) := D.isPoly_stP (D.isPoly_sc hG lam n)
  have hTn : (D.stP (D.sc G lam n)).coeff n ≠ 0 := by
    show D.st (G.coeff n * D.e (((n : Rat) - n) * lam)) ≠ 0
    rw [hGn, show ((n : Rat) - n) * lam = 0 by grind, D.e_zero, Semiring.mul_one, D.st_one]
    grind
  obtain ⟨c', m', hm'odd, hord'⟩ :=
    RCF.odd_degree_odd_root hR hTdeg (by obtain ⟨k, hk⟩ := hn; omega) hTn
  obtain ⟨w, hw⟩ := D.descent hR m' ⟨m' / 2, by omega⟩ n (D.sc G lam n) c'
    (D.isPoly_sc hG lam n) hTI hord'
  exact ⟨_, hroot _ (D.root_of_sc hw)⟩

/-! ## Square roots -/

theorem exists_sqrt (hR : IVT R) {r : R} (hr : 0 < r) : ∃ s : R, 0 < s ∧ s * s = r := by
  have hrr := OrderedRing.mul_nonneg (Std.le_of_lt hr) (Std.le_of_lt hr)
  obtain ⟨s, hs0, -, hs⟩ := hR 2 (sqPoly r) 0 (r + 1) (by grind)
    (by rw [eval_sqPoly]; grind) (by rw [eval_sqPoly]; grind)
  rw [eval_sqPoly] at hs
  refine ⟨s, ?_, by grind⟩
  apply Classical.byContradiction; intro h
  have : s = 0 := by grind
  rw [this] at hs; grind

theorem stP_sqPoly {a : L} (ha : D.Fin a) : D.stP (sqPoly a) = sqPoly (D.st a) := by
  ext i
  rw [stP_coeff]
  show D.st (if i = 0 then -a else if i = 2 then 1 else 0) =
    (if i = 0 then -D.st a else if i = 2 then 1 else 0)
  by_cases h0 : i = 0
  · rw [if_pos h0, if_pos h0, D.st_neg ha]
  · rw [if_neg h0, if_neg h0]
    by_cases h2 : i = 2
    · rw [if_pos h2, if_pos h2, D.st_one]
    · rw [if_neg h2, if_neg h2, D.st_zero]

include D in
theorem exists_sq (hR : IVT R) {x : L} (hx : 0 < x) : ∃ y, y * y = x := by
  obtain ⟨r, q, δ, hr, hδ, hxe⟩ := D.lead' x (by grind)
  have hb := D.one_add_inf_bounds hδ
  have hr0 : 0 < r := by
    apply Classical.byContradiction; intro h
    have h1 : D.ι r < 0 := by have := D.ι_lt (show r < 0 by grind); rwa [D.ι_zero] at this
    have h2 := OrderedRing.mul_pos (D.e_pos q) (show 0 < 1 + δ by grind)
    have : D.ι r * (D.e q * (1 + δ)) < 0 := OrderedRing.mul_neg_of_neg_of_pos h1 h2
    rw [← Semiring.mul_assoc, ← hxe] at this; grind
  obtain ⟨s, hs0, hss⟩ := exists_sqrt hR hr0
  have haf : D.Fin (D.ι r * (1 + δ)) :=
    D.fin_mul (D.fin_ι r) (D.fin_add D.fin_one (D.fin_of_inf hδ))
  have hast : D.st (D.ι r * (1 + δ)) = r := D.st_eq (by
    rw [show D.ι r * (1 + δ) - D.ι r = D.ι r * δ by grind]; exact D.inf_mul' (D.fin_ι r) hδ)
  have hPI : D.Integral (sqPoly (D.ι r * (1 + δ))) := fun i => by
    show D.Fin (if i = 0 then -(D.ι r * (1 + δ)) else if i = 2 then 1 else 0)
    by_cases h0 : i = 0
    · rw [if_pos h0]; exact D.fin_neg haf
    · rw [if_neg h0]
      by_cases h2 : i = 2
      · rw [if_pos h2]; exact D.fin_one
      · rw [if_neg h2]; exact D.fin_of_inf D.inf_zero
  obtain ⟨y, -, hy⟩ := D.hensel (isPoly_sqPoly _) hPI (c := s)
    (by rw [D.stP_sqPoly haf, hast]; exact sqPoly_simple hss (by grind))
  rw [eval_sqPoly] at hy
  have he : D.e (q / 2) * D.e (q / 2) = D.e q := by rw [← D.e_add]; congr 1; grind
  refine ⟨y * D.e (q / 2), ?_⟩
  rw [hxe]
  have : y * D.e (q / 2) * (y * D.e (q / 2)) = (y * y) * (D.e (q / 2) * D.e (q / 2)) := by grind
  rw [this, he, show y * y = D.ι r * (1 + δ) by grind]; grind

include D in
/-- **The main theorem**: a Levi-Civita-like field over a coefficient field with the
polynomial IVT is real closed. -/
theorem isRealClosed (hR : IVT R) : IsRealClosed L :=
  ⟨fun _ hx => D.exists_sq hR hx,
   fun n _ hp hn hl => D.odd_root hR hp ⟨n / 2, by omega⟩ hl⟩

end LCData

end LeviCivita
