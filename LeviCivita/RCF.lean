import LeviCivita.Real

/-!
# Roots of odd multiplicity over a real closed field

Over an ordered field with the intermediate value property for polynomials
(`IVT F`), a polynomial that changes sign has a root of **odd multiplicity**
between the two points (`sign_change_odd_root`), and so does every polynomial of
odd degree (`odd_degree_odd_root`). The multiplicity of `c` as a root of `p` is
the order of the Taylor expansion `tay n p c` (`PS.IsOrd`).

The proof factors `p = (X − c)ᵐ · H` at a root `c` of even multiplicity `m`:
`H` changes sign like `p` does and has smaller degree, and roots `c' ≠ c` of `H`
have the same multiplicity in `p` (`tay_mul`).
-/

set_option linter.unusedSectionVars false

namespace LeviCivita.RCF

open Lean.Grind Series Series.PS Poly Limits Classical

attribute [local instance] Semiring.natCast Ring.intCast
attribute [local instance high] Semiring.ofNat

variable {F : Type u} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F]
  [OrderedRing F]

/-! ## Algebraic facts -/

/-- Drop the first `m` coefficients. -/
def shiftBy (m : Nat) (t : PS F) : PS F := ⟨fun j => t.coeff (j + m)⟩

theorem isPoly_shiftBy {n : Nat} {t : PS F} (ht : IsPoly n t) (m : Nat) :
    IsPoly (n - m) (shiftBy m t) := fun j hj => ht (j + m) (by omega)

theorem eval_at_zero (n : Nat) (p : PS F) : eval n p 0 = p.coeff 0 := by
  unfold eval; rw [S_succ_left, Semiring.pow_zero, S_eq_zero (fun i _ => by
    rw [Semiring.pow_succ]; grind)]; grind

/-- If the first `m` coefficients vanish, `t(z) = zᵐ · (shiftBy m t)(z)`. -/
theorem eval_split {n m : Nat} (hmn : m ≤ n) {t : PS F} (ht : ∀ i, i < m → t.coeff i = 0)
    (z : F) : eval n t z = z ^ m * eval (n - m) (shiftBy m t) z := by
  unfold eval
  rw [show n + 1 = m + (n - m + 1) by omega, PS.S_split,
    S_eq_zero (fun i hi => by rw [ht i hi]; grind), ← S_mul_left]
  have : S (n - m + 1) (fun i => t.coeff (m + i) * z ^ (m + i)) =
      S (n - m + 1) (fun i => z ^ m * ((shiftBy m t).coeff i * z ^ i)) :=
    S_congr fun i _ => by
      show _ = z ^ m * (t.coeff (i + m) * z ^ i)
      rw [Nat.add_comm m i, Semiring.pow_add]; grind
  rw [this]; grind

/-- Taylor expansion is multiplicative. -/
theorem tay_mul {a b : Nat} {p q : PS F} (hp : IsPoly a p) (hq : IsPoly b q) (c : F) :
    tay (a + b) (p * q) c = tay a p c * tay b q c :=
  eq_of_eval_pos (isPoly_tay _ _ _) (isPoly_mul (isPoly_tay a p c) (isPoly_tay b q c))
    (fun z _ => by
      rw [eval_tay, eval_mul hp hq, eval_mul (isPoly_tay a p c) (isPoly_tay b q c), eval_tay,
        eval_tay])

theorem tay_neg {n : Nat} {p : PS F} (_hp : IsPoly n p) (c : F) : tay n (-p) c = -tay n p c :=
  eq_of_eval_pos (isPoly_tay _ _ _) (isPoly_neg (isPoly_tay n p c)) (fun z _ => by
    rw [eval_tay, eval_neg, eval_neg, eval_tay])

theorem isOrd_neg {t : PS F} {m : Nat} (h : IsOrd t m) : IsOrd (-t) m :=
  ⟨fun i hi => by rw [coeff_neg, h.1 i hi]; grind, fun h0 => h.2 (by rw [coeff_neg] at h0; grind)⟩

/-- Orders add under multiplication. -/
theorem isOrd_mul {s t : PS F} {p q : Nat} (hs : IsOrd s p) (ht : IsOrd t q) :
    IsOrd (s * t) (p + q) := by
  obtain ⟨h0, h1⟩ := mul_low s t p q hs.1 ht.1
  refine ⟨h0, ?_⟩
  rw [h1]; intro h
  have hinv := Field.mul_inv_cancel ht.2
  apply hs.2
  calc s.coeff p = s.coeff p * t.coeff q * (t.coeff q)⁻¹ := by grind
    _ = 0 := by rw [h]; grind

theorem pow_even_pos {x : F} (hx : x ≠ 0) (k : Nat) : 0 < x ^ (2 * k) := by
  have hxx : 0 < x * x := by
    rcases (by grind : 0 < x ∨ x < 0) with h | h
    · exact OrderedRing.mul_pos h h
    · exact OrderedRing.mul_pos_of_neg_of_neg h h
  induction k with
  | zero => rw [Nat.mul_zero, Semiring.pow_zero]; exact OrderedRing.zero_lt_one
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, Semiring.pow_succ, Semiring.pow_succ,
      Semiring.mul_assoc]
    exact OrderedRing.mul_pos ih hxx

theorem pow_ne_zero {x : F} (hx : x ≠ 0) (k : Nat) : x ^ k ≠ 0 := by
  intro h; exact hx (Field.of_pow_eq_zero x k h)

theorem sub_ne_zero' {a b : F} (h : a ≠ b) : a - b ≠ 0 := fun h' => h (by grind)
theorem neg_add_self' (c : F) : -c + c = 0 := by grind
theorem neg_neg' (t : PS F) : - -t = t := by grind

/-! ## Sign changes give roots of odd multiplicity -/

theorem eval_linX (c y : F) : eval 1 (X - C c : PS F) y = y - c := by
  rw [eval_sub, eval_X (Nat.le_refl 1), eval_C]

theorem isPoly_linX (c : F) : IsPoly 1 (X - C c : PS F) :=
  isPoly_sub isPoly_X ((isPoly_C c).mono (by omega))

/-- **A sign change gives a root of odd multiplicity.** -/
theorem sign_change_odd_root (hF : IVT F) :
    ∀ N n (p : PS F) (lo hi : F), n ≤ N → IsPoly n p → lo < hi → eval n p lo < 0 →
      0 < eval n p hi → ∃ c m, lo < c ∧ c < hi ∧ m % 2 = 1 ∧ IsOrd (tay n p c) m := by
  intro N
  induction N with
  | zero =>
    intro n p lo hi hn hp hlh hlo hhi
    -- a constant cannot change sign
    have : n = 0 := by omega
    subst this
    have e : ∀ y, eval 0 p y = p.coeff 0 := fun y => by
      unfold eval; simp only [Nat.zero_add, S_one]; rw [Semiring.pow_zero]; grind
    rw [e] at hlo hhi; grind
  | succ N ih =>
    intro n p lo hi hn hp hlh hlo hhi
    obtain ⟨c, hc1, hc2, hc⟩ := hF n p lo hi (Std.le_of_lt hlh) (Std.le_of_lt hlo) (Std.le_of_lt hhi)
    have hclo : lo ≠ c := fun h => by rw [← h] at hc; grind
    have hchi : hi ≠ c := fun h => by rw [← h] at hc; grind
    let t := tay n p c
    have hevt : ∀ y, eval n p y = eval n t (y - c) := fun y => by
      show _ = eval n (tay n p c) _; rw [eval_tay]; congr 1; grind
    have ht0 : t ≠ 0 := fun h => by
      have := hevt lo; rw [h, eval_zero] at this; grind
    obtain ⟨m, hm0, hm⟩ := exists_ord t ht0
    have hmn : m ≤ n := Classical.byContradiction fun h => hm (isPoly_tay n p c m (by omega))
    have hm1 : m ≠ 0 := fun h => by
      subst h; apply hm; show (tay n p c).coeff 0 = 0; rw [tay_coeff_zero]; exact hc
    have hlc : lo < c := Std.lt_of_le_of_ne hc1 hclo
    have hch : c < hi := Std.lt_of_le_of_ne hc2 (fun h => hchi h.symm)
    by_cases hodd : m % 2 = 1
    · exact ⟨c, m, hlc, hch, hodd, hm0, hm⟩
    -- even multiplicity: factor out `(X − c)ᵐ`
    have hpow : ∀ y, y ≠ c → 0 < (y - c) ^ m := fun y hy => by
      rw [show m = 2 * (m / 2) by omega]; exact pow_even_pos (sub_ne_zero' hy) _
    clear hodd
    let H0 := shiftBy m t
    have hH0 : IsPoly (n - m) H0 := isPoly_shiftBy (isPoly_tay n p c) m
    let H := tay (n - m) H0 (-c)
    have hH : IsPoly (n - m) H := isPoly_tay _ _ _
    have key : ∀ y, eval n p y = (y - c) ^ m * eval (n - m) H y := fun y => by
      rw [hevt, eval_split hmn hm0]
      show _ = _ * eval (n - m) (tay (n - m) H0 (-c)) y
      rw [eval_tay]; congr 2; grind
    have hHlo : eval (n - m) H lo < 0 := by
      apply Classical.byContradiction; intro h
      have := OrderedRing.mul_nonneg (Std.le_of_lt (hpow lo hclo)) (by grind : 0 ≤ eval (n - m) H lo)
      rw [← key] at this; grind
    have hHhi : 0 < eval (n - m) H hi := by
      apply Classical.byContradiction; intro h
      have := OrderedRing.mul_nonneg (Std.le_of_lt (hpow hi hchi))
        (by grind : 0 ≤ -eval (n - m) H hi)
      have e := key hi
      grind
    obtain ⟨c', m', hc'1, hc'2, hm'odd, hm'⟩ :=
      ih (n - m) H lo hi (by omega) hH hlh hHlo hHhi
    -- `c' ≠ c`, since `H(c) = tₘ ≠ 0` but `H(c') = 0`
    have hHc : eval (n - m) H c ≠ 0 := by
      show eval (n - m) (tay (n - m) H0 (-c)) c ≠ 0
      rw [eval_tay, neg_add_self', eval_at_zero]
      show t.coeff (0 + m) ≠ 0; rw [Nat.zero_add]; exact hm
    have hHc' : eval (n - m) H c' = 0 := by
      rw [← tay_coeff_zero]; exact hm'.1 0 (by omega)
    have hcc' : c' ≠ c := fun h => by rw [h] at hHc'; exact hHc hHc'
    -- `p = (X − c)ᵐ · H`
    have hlin := isPoly_pow (isPoly_linX c) m
    rw [Nat.one_mul] at hlin
    have hfac : p = (X - C c) ^ m * H := by
      apply eq_of_eval_pos (n := n) hp
      · have := isPoly_mul hlin hH; rwa [Nat.add_sub_cancel' hmn] at this
      · intro y _
        rw [key, ← Nat.add_sub_cancel' hmn, eval_mul hlin hH, Nat.add_sub_cancel' hmn]
        congr 1
        have := eval_pow (isPoly_linX c) m y
        rw [Nat.one_mul] at this; rw [this, eval_linX]
    -- the multiplicity of `c'` in `p` is its multiplicity in `H`
    have hord0 : IsOrd (tay m ((X - C c) ^ m) c') 0 := ⟨fun i hi => by omega, by
      rw [tay_coeff_zero]
      have := eval_pow (isPoly_linX c) m c'
      rw [Nat.one_mul] at this; rw [this, eval_linX]
      exact pow_ne_zero (sub_ne_zero' hcc') m⟩
    refine ⟨c', m', hc'1, hc'2, hm'odd, ?_⟩
    have e : tay n p c' = tay m ((X - C c) ^ m) c' * tay (n - m) H c' := by
      rw [← tay_mul hlin hH, Nat.add_sub_cancel' hmn, ← hfac]
    rw [e]
    have := isOrd_mul hord0 hm'
    rwa [Nat.zero_add] at this

/-- The same with the signs reversed. -/
theorem sign_change_odd_root' (hF : IVT F) {n : Nat} {p : PS F} {lo hi : F} (hp : IsPoly n p)
    (hlh : lo < hi) (hlo : 0 < eval n p lo) (hhi : eval n p hi < 0) :
    ∃ c m, lo < c ∧ c < hi ∧ m % 2 = 1 ∧ IsOrd (tay n p c) m := by
  obtain ⟨c, m, h1, h2, h3, h4⟩ := sign_change_odd_root hF n n (-p) lo hi (Nat.le_refl _)
    (isPoly_neg hp) hlh (by rw [eval_neg]; grind) (by rw [eval_neg]; grind)
  refine ⟨c, m, h1, h2, h3, ?_⟩
  rw [tay_neg hp] at h4
  have := isOrd_neg h4; rwa [neg_neg'] at this

/-! ## Odd degree -/

theorem pow_le_pow_right {x : F} (hx : 1 ≤ x) {i j : Nat} (h : i ≤ j) : x ^ i ≤ x ^ j := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Std.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := ih (by omega)
      have hp : 0 ≤ x ^ j := pow_nonneg (by grind) j
      have : x ^ j * 1 ≤ x ^ j * x := OrderedRing.mul_le_mul_of_nonneg_left hx hp
      rw [Semiring.pow_succ]; grind
    · rw [h]; exact Std.le_refl _

/-- For `|y|` large, `p(y)` has the sign of its leading term `a yⁿ`. -/
theorem lead_dominates {n : Nat} {p : PS F} (_hp : IsPoly (n + 1) p) (_ha : 0 < p.coeff (n + 1))
    {y : F} (hy : 1 ≤ abs y)
    (hB : S (n + 1) (fun i => abs (p.coeff i)) < p.coeff (n + 1) * abs y) :
    abs (eval (n + 1) p y - p.coeff (n + 1) * y ^ (n + 1)) < p.coeff (n + 1) * abs y ^ (n + 1) := by
  have e : eval (n + 1) p y - p.coeff (n + 1) * y ^ (n + 1) = S (n + 1) (fun i => p.coeff i * y ^ i) := by
    unfold eval; rw [S_succ (n + 1)]; grind
  rw [e]
  refine Std.lt_of_le_of_lt (abs_S_le _ _) ?_
  have hyn : 0 < abs y ^ n := pow_pos (by grind) n
  have h1 : S (n + 1) (fun i => abs (p.coeff i * y ^ i)) ≤
      S (n + 1) (fun i => abs (p.coeff i) * abs y ^ n) := S_le fun i hi => by
    rw [abs_mul, abs_pow]
    exact OrderedRing.mul_le_mul_of_nonneg_left (pow_le_pow_right hy (by omega)) (abs_nonneg _)
  rw [S_mul_right] at h1
  have h2 := OrderedRing.mul_lt_mul_of_pos_right hB hyn
  rw [Semiring.pow_succ, show abs y ^ n * abs y = abs y * abs y ^ n by grind]
  grind

theorem pow_odd_neg_aux (x : F) (k : Nat) : (-x) ^ (2 * k + 1) = -(x ^ (2 * k + 1)) := by
  induction k with
  | zero => simp only [Nat.mul_zero, Nat.zero_add]; rw [Semiring.pow_one, Semiring.pow_one]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by omega, Semiring.pow_succ, Semiring.pow_succ, ih,
      Semiring.pow_succ x, Semiring.pow_succ x]; grind

theorem pow_odd_neg (x : F) {n : Nat} (hn : n % 2 = 1) : (-x) ^ n = -(x ^ n) := by
  rw [show n = 2 * (n / 2) + 1 by omega]; exact pow_odd_neg_aux x _

/-- **Odd degree polynomials have a root of odd multiplicity.** -/
theorem odd_degree_odd_root (hF : IVT F) {n : Nat} {p : PS F} (hp : IsPoly n p)
    (hn : n % 2 = 1) (ha : p.coeff n ≠ 0) : ∃ c m, m % 2 = 1 ∧ IsOrd (tay n p c) m := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hodd : ∀ y : F, (-y) ^ (n + 1) = -(y ^ (n + 1)) := fun y => pow_odd_neg y hn
  clear hn
  -- reduce to a positive leading coefficient
  suffices h : ∀ q : PS F, IsPoly (n + 1) q → 0 < q.coeff (n + 1) →
      ∃ lo hi, lo < hi ∧ eval (n + 1) q lo < 0 ∧ 0 < eval (n + 1) q hi by
    rcases (by grind : 0 < p.coeff (n + 1) ∨ p.coeff (n + 1) < 0) with hpos | hneg
    · obtain ⟨lo, hi, h1, h2, h3⟩ := h p hp hpos
      obtain ⟨c, m, _, _, h4, h5⟩ := sign_change_odd_root hF _ _ p lo hi (Nat.le_refl _) hp h1 h2 h3
      exact ⟨c, m, h4, h5⟩
    · obtain ⟨lo, hi, h1, h2, h3⟩ := h (-p) (isPoly_neg hp) (by rw [coeff_neg]; grind)
      rw [eval_neg] at h2 h3
      obtain ⟨c, m, _, _, h4, h5⟩ := sign_change_odd_root' hF hp h1 (by grind) (by grind)
      exact ⟨c, m, h4, h5⟩
  intro q hq ha
  let B := S (n + 1) (fun i => abs (q.coeff i))
  have hB0 : 0 ≤ B := S_nonneg fun i _ => abs_nonneg _
  let M := 1 + B * (q.coeff (n + 1))⁻¹
  have hinv := Field.IsOrdered.inv_pos_iff.mpr ha
  have hM1 : 1 ≤ M := by
    have := OrderedRing.mul_nonneg hB0 (Std.le_of_lt hinv); grind
  have hMpos : 0 < M := by grind
  have hBM : B < q.coeff (n + 1) * M := by
    have : q.coeff (n + 1) * M = q.coeff (n + 1) + B := by
      show q.coeff (n + 1) * (1 + B * (q.coeff (n + 1))⁻¹) = _
      have := Field.mul_inv_cancel (show q.coeff (n + 1) ≠ 0 by grind); grind
    grind
  have hMn : 0 < M ^ (n + 1) := pow_pos hMpos _
  have hlead : 0 < q.coeff (n + 1) * M ^ (n + 1) := OrderedRing.mul_pos ha hMn
  have hM : abs M = M := abs_of_nonneg (Std.le_of_lt hMpos)
  have hnM : abs (-M) = M := by rw [abs_neg]; exact hM
  refine ⟨-M, M, by grind, ?_, ?_⟩
  · have := lead_dominates hq ha (y := -M) (by rw [hnM]; exact hM1) (by rw [hnM]; exact hBM)
    rw [hnM, hodd M, abs_lt_iff] at this
    grind
  · have := lead_dominates hq ha (y := M) (by rw [hM]; exact hM1) (by rw [hM]; exact hBM)
    rw [hM, abs_lt_iff] at this
    grind

end LeviCivita.RCF
