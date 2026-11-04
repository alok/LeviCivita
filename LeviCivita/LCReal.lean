import LeviCivita.RealClosed

/-!
# The Levi-Civita field over a real-closed-like coefficient field is real closed

We build `LCData K (LeviCivitaFieldOver K)` for any ordered field `K`:

* `ι = ofK`, the constants;
* `e q = ε^q`, defined from the roots `ε^{1/N}`: `e (a/N) = (ε^{1/N})^a`;
* leading terms, computed in the Laurent field (`laurent_lead`), transported to the
  Puiseux field along `x ↦ x(ε^{1/N})` (`puiseux_lead`), and to the completion by
  approximating `x` within `|x| ε` (`lead`);
* completeness of the completion.

With `IVT ℝ` this gives **`LeviCivitaFieldOver.real_isRealClosed`**: the Levi-Civita
field over `ℝ = Completion ℚ` is real closed.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita

open Lean.Grind Series Series.PS Frac Poly Limits Classical

attribute [local instance] Semiring.natCast Ring.intCast
attribute [local instance high] Semiring.ofNat

universe u v

/-! ## Generic facts -/

section Generic

variable {A : Type u} [Field A] [LE A] [LT A] [Std.IsLinearOrder A] [Std.LawfulOrderLT A]
  [OrderedRing A]
variable {B : Type v} [Field B] [LE B] [LT B] [Std.IsLinearOrder B] [Std.LawfulOrderLT B]
  [OrderedRing B]

/-- Ordered embeddings commute with `abs`. -/
theorem abs_hom (φ : A → B) (h0 : φ 0 = 0) (hneg : ∀ x, φ (-x) = -φ x)
    (hlt : ∀ x y, x < y → φ x < φ y) (x : A) : abs (φ x) = φ (abs x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]; apply abs_of_nonneg
    rcases (by grind : x = 0 ∨ 0 < x) with h | h
    · rw [h, h0]; exact Std.le_refl _
    · have := hlt 0 x h; rw [h0] at this; exact Std.le_of_lt this
  · rw [abs_of_neg (x := x) (by grind), hneg]; apply abs_of_neg
    have := hlt x 0 (by grind); rw [h0] at this; exact this

theorem pos_mul_inv {a b : A} (h : 0 < a * b) (hb : b ≠ 0) : 0 < a * b⁻¹ := by
  have hb' : b⁻¹ ≠ 0 := inv_ne_zero' hb
  have hsq : 0 < b⁻¹ * b⁻¹ := by
    rcases (by grind : 0 < b⁻¹ ∨ b⁻¹ < 0) with h | h
    · exact OrderedRing.mul_pos h h
    · exact OrderedRing.mul_pos_of_neg_of_neg h h
  have := OrderedRing.mul_pos h hsq
  have e : a * b * (b⁻¹ * b⁻¹) = a * b⁻¹ := by
    have := Field.mul_inv_cancel hb; grind
  rwa [e] at this

theorem pow_mul'' (a : A) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, Semiring.pow_zero, Semiring.pow_zero]
  | succ n ih => rw [Nat.mul_succ, Semiring.pow_add, ih, Semiring.pow_succ]

end Generic

/-! ## Laurent series -/

section Laurent

variable {K : Type u} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

theorem ofRing_pow' (a : PS K) (n : Nat) : (ofRing a : Laurent K) ^ n = ofRing (a ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ofRing a ^ n * ofRing a = ofRing (a ^ n * a)
    rw [ih, ← ofRing_mul]

theorem ofRing_neg' (a : PS K) : (ofRing (-a) : Laurent K) = -ofRing a := by
  have := ofRing_add (R := PS K) a (-a)
  rw [show a + -a = 0 by grind, ofRing_zero] at this; grind

theorem ofRing_ne_zero' {a : PS K} (h : a ≠ 0) : (ofRing a : Laurent K) ≠ 0 :=
  fun h' => h (ofRing_injective (by rw [h']; rfl))

theorem ps_pos_of_coeff {p : PS K} (h : 0 < p.coeff 0) : 0 < p := by
  rw [PS.lt_def, show p - 0 = p by grind]
  exact ⟨0, fun m hm => absurd hm (Nat.not_lt_zero _), h⟩

theorem coeff_mul_zero (a b : PS K) : (a * b).coeff 0 = a.coeff 0 * b.coeff 0 := by
  rw [coeff_mul, S_succ, S_zero]; show 0 + a.coeff 0 * b.coeff 0 = _; grind

/-- `f / g` with `f(0) = 0` and `g(0) ≠ 0` is infinitesimal. -/
theorem laurent_small {f g : PS K} (hf : f.coeff 0 = 0) (hg : g.coeff 0 ≠ 0) {s : K}
    (hs : 0 < s) : abs (ofRing f * (ofRing g)⁻¹ : Laurent K) < Laurent.ofK s := by
  have hg' := ofRing_ne_zero' (show g ≠ 0 from fun h => hg (by rw [h]; rfl))
  have hgg : 0 < g.coeff 0 * g.coeff 0 := by
    rcases (by grind : 0 < g.coeff 0 ∨ g.coeff 0 < 0) with h | h
    · exact OrderedRing.mul_pos h h
    · exact OrderedRing.mul_pos_of_neg_of_neg h h
  have hsgg := OrderedRing.mul_pos hs hgg
  have key : ∀ p : PS K, p.coeff 0 = s * g.coeff 0 →
      0 < (ofRing p : Laurent K) * (ofRing g)⁻¹ := fun p hp => by
    apply pos_mul_inv _ hg'
    rw [← ofRing_mul, ← ofRing_zero]
    apply ofRing_lt.mpr; apply ps_pos_of_coeff
    rw [coeff_mul_zero, hp]; grind
  rw [abs_lt_iff]
  constructor
  · have h1 := key (C s * g - f) (by
      show (C s * g).coeff 0 + -f.coeff 0 = _; rw [C_mul, hf]; show s * g.coeff 0 + -0 = _; grind)
    rw [show (C s * g - f : PS K) = C s * g + -f from rfl, ofRing_add, ofRing_neg', ofRing_mul] at h1
    unfold Laurent.ofK
    have := Field.mul_inv_cancel hg'
    clear key
    have e : (ofRing (C s) * ofRing g + -ofRing f) * (ofRing g)⁻¹ =
        (ofRing (C s) : Laurent K) - ofRing f * (ofRing g)⁻¹ := by grind
    rw [e] at h1
    grind
  · have h1 := key (C s * g + f) (by
      show (C s * g).coeff 0 + f.coeff 0 = _; rw [C_mul, hf]; show s * g.coeff 0 + 0 = _; grind)
    rw [ofRing_add, ofRing_mul] at h1
    unfold Laurent.ofK
    have := Field.mul_inv_cancel hg'
    clear key
    have e : (ofRing (C s) * ofRing g + ofRing f) * (ofRing g)⁻¹ =
        (ofRing (C s) : Laurent K) + ofRing f * (ofRing g)⁻¹ := by grind
    rw [e] at h1
    grind

theorem ps_shift (a : PS K) (i : Nat) (h : ∀ m, m < i → a.coeff m = 0) :
    a = (X : PS K) ^ i * ⟨fun n => a.coeff (n + i)⟩ := by
  ext n
  rw [coeff_mul]
  by_cases hn : i ≤ n
  · rw [S_eq_single (j := i) (by omega) (fun k _ hki => by rw [X_pow_coeff, if_neg hki]; grind)]
    rw [X_pow_coeff, if_pos rfl]
    show a.coeff n = 1 * a.coeff (n - i + i)
    rw [Nat.sub_add_cancel hn]; grind
  · rw [S_eq_zero (fun k hk => by rw [X_pow_coeff, if_neg (by omega)]; grind)]
    exact h n (by omega)

theorem frac_mk_eq (a b : PS K) (hb : b ≠ 0) :
    (Frac.mk a b hb : Laurent K) = ofRing a * (ofRing b)⁻¹ := by
  have hb' := ofRing_ne_zero' hb
  have h : (Frac.mk a b hb : Laurent K) * ofRing b = ofRing a := by
    unfold ofRing; rw [Frac.mk_mul, Frac.mk_eq]; grind
  have := Field.mul_inv_cancel hb'
  rw [← h]; grind

/-- **Leading terms of Laurent series**: `x = r ε^n ε^{-m} (1 + δ)`, `δ` infinitesimal. -/
theorem laurent_lead (x : Laurent K) (hx : x ≠ 0) : ∃ (r : K) (n m : Nat) (δ : Laurent K),
    r ≠ 0 ∧ (∀ s : K, 0 < s → abs δ < Laurent.ofK s) ∧
    x = Laurent.ofK r * Laurent.eps ^ n * (Laurent.eps ^ m)⁻¹ * (1 + δ) := by
  induction x using Frac.ind with
  | h a b hb =>
  have ha : a ≠ 0 := fun h => hx ((Frac.mk_eq_zero a b hb).mpr h)
  obtain ⟨i, hi⟩ := exists_ord a ha
  obtain ⟨j, hj⟩ := exists_ord b hb
  obtain ⟨a', ha'⟩ : ∃ a' : PS K, a' = ⟨fun n => a.coeff (n + i)⟩ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : PS K, b' = ⟨fun n => b.coeff (n + j)⟩ := ⟨_, rfl⟩
  have hA : a = (X : PS K) ^ i * a' := by rw [ha']; exact ps_shift a i hi.1
  have hB : b = (X : PS K) ^ j * b' := by rw [hb']; exact ps_shift b j hj.1
  have ha0 : a'.coeff 0 ≠ 0 := by rw [ha']; show a.coeff (0 + i) ≠ 0; rw [Nat.zero_add]; exact hi.2
  have hb0 : b'.coeff 0 ≠ 0 := by rw [hb']; show b.coeff (0 + j) ≠ 0; rw [Nat.zero_add]; exact hj.2
  have hr : a'.coeff 0 * (b'.coeff 0)⁻¹ ≠ 0 := mul_ne_zero' ha0 (inv_ne_zero' hb0)
  obtain ⟨r, hrdef⟩ : ∃ r, r = a'.coeff 0 * (b'.coeff 0)⁻¹ := ⟨_, rfl⟩
  rw [← hrdef] at hr
  have hrb : r * b'.coeff 0 = a'.coeff 0 := by
    rw [hrdef]; have := Field.inv_mul_cancel hb0; grind
  refine ⟨r, i, j, ofRing (a' - C r * b') * (ofRing (C r * b'))⁻¹, hr, fun s hs => ?_, ?_⟩
  · apply laurent_small _ _ hs
    · rw [coeff_sub, C_mul]; show a'.coeff 0 - r * b'.coeff 0 = 0; grind
    · rw [C_mul]; show r * b'.coeff 0 ≠ 0; rw [hrb]; exact ha0
  · have hb'0 : b' ≠ 0 := fun h => hb0 (by rw [h]; rfl)
    have hCr : (C r : PS K) ≠ 0 := fun h => hr (by
      have := congrArg (fun p => PS.coeff p 0) h; simpa using this)
    have i1 := Field.mul_inv_cancel (ofRing_ne_zero' hb'0)
    have i2 := Field.mul_inv_cancel (ofRing_ne_zero' hCr)
    have i3 := Field.mul_inv_cancel (RCF.pow_ne_zero (F := Laurent K) Laurent.eps_ne_zero j)
    rw [frac_mk_eq, hA, hB, ofRing_mul, ofRing_mul, ← ofRing_pow', ← ofRing_pow',
      show (a' - C r * b' : PS K) = a' + -(C r * b') from rfl, ofRing_add, ofRing_neg',
      ofRing_mul, Field.inv_mul, Field.inv_mul]
    unfold Laurent.ofK Laurent.eps
    grind

end Laurent

/-! ## Puiseux series -/

section Puiseux

variable {K : Type u} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

open Puiseux in
theorem puiseux_lead (z : Puiseux K) (hz : z ≠ 0) : ∃ (r : K) (N : Nat) (hN : 0 < N) (n m : Nat)
    (δ : Puiseux K), r ≠ 0 ∧ (∀ s : K, 0 < s → abs δ < Puiseux.ofK s) ∧
    z = Puiseux.ofK r * Puiseux.root N hN ^ n * (Puiseux.root N hN ^ m)⁻¹ * (1 + δ) := by
  induction z using Puiseux.ind with
  | h N hN x =>
  have hx : x ≠ 0 := fun h => hz (by rw [h, mk_zero'])
  obtain ⟨r, n, m, δ, hr, hδ, hxe⟩ := laurent_lead x hx
  refine ⟨r, N, hN, n, m, mk N hN δ, hr, fun s hs => ?_, ?_⟩
  · rw [abs_hom (mk N hN) (mk_zero' N hN) (fun _ => rfl) (fun _ _ h => mk_lt.mpr h),
      ← mk_ofK N hN s]
    exact mk_lt.mpr (hδ s hs)
  · rw [hxe, mk_mul_same, mk_mul_same, mk_mul_same, mk_ofK, mk_pow, ← Puiseux.mk_inv, mk_pow,
      mk_add_same, mk_one']
    rfl

end Puiseux

/-! ## The completion -/

namespace LeviCivitaFieldOver

open Completion

variable {K : Type u} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

noncomputable section

theorem const_zero' : (const 0 : LeviCivitaFieldOver K) = 0 := rfl
theorem const_one' : (const 1 : LeviCivitaFieldOver K) = 1 := rfl

theorem const_inv' (a : Puiseux K) : (const a⁻¹ : LeviCivitaFieldOver K) = (const a)⁻¹ := by
  by_cases ha : a = 0
  · rw [ha, Field.inv_zero, const_zero', Field.inv_zero]
  · apply Field.eq_inv_of_mul_eq_one
    rw [← const_mul, Field.inv_mul_cancel ha]; rfl

theorem abs_const (a : Puiseux K) : abs (const a : LeviCivitaFieldOver K) = const (abs a) :=
  abs_hom const rfl (fun x => (const_neg x)) (fun _ _ h => const_lt.mpr h) a

theorem ofK_add' (a b : K) : (ofK (a + b) : LeviCivitaFieldOver K) = ofK a + ofK b := by
  unfold ofK; rw [Puiseux.ofK_add, const_add]

theorem ofK_mul' (a b : K) : (ofK (a * b) : LeviCivitaFieldOver K) = ofK a * ofK b := by
  unfold ofK Puiseux.ofK Laurent.ofK; rw [C_mul', ofRing_mul, Puiseux.ofL_mul, const_mul]

theorem ofK_one' : (ofK 1 : LeviCivitaFieldOver K) = 1 := rfl

theorem ofK_lt' {a b : K} (h : a < b) : (ofK a : LeviCivitaFieldOver K) < ofK b :=
  const_lt.mpr (Puiseux.ofK_lt h)

theorem root_ne (N : Nat) (hN : 0 < N) : (root N hN : LeviCivitaFieldOver K) ≠ 0 := by
  have := root_pos (K := K) N hN; grind

/-! ### Rational powers of `ε` -/

/-- `(ε^{1/N})^a`. -/
def Ecore (a : Int) (N : Nat) : LeviCivitaFieldOver K :=
  if h : 0 < N then root N h ^ a.toNat * (root N h ^ (-a).toNat)⁻¹ else 1

/-- `ε^q`. -/
def epow (q : Rat) : LeviCivitaFieldOver K := Ecore q.num q.den

theorem Ecore_nat {N : Nat} (h : 0 < N) (n m : Nat) :
    (Ecore ((n : Int) - m) N : LeviCivitaFieldOver K) = root N h ^ n * (root N h ^ m)⁻¹ := by
  unfold Ecore; rw [dite_eq_left h]
  have e : ((n : Int) - m).toNat + m = n + (-((n : Int) - m)).toNat := by omega
  have e1 : (root N h : LeviCivitaFieldOver K) ^ ((n : Int) - m).toNat * root N h ^ m =
      root N h ^ n * root N h ^ (-((n : Int) - m)).toNat := by
    rw [← Semiring.pow_add, ← Semiring.pow_add, e]
  have i1 := Field.mul_inv_cancel (RCF.pow_ne_zero (root_ne (K := K) N h) m)
  have i2 := Field.mul_inv_cancel
    (RCF.pow_ne_zero (root_ne (K := K) N h) (-((n : Int) - m)).toNat)
  grind

theorem Ecore_int {N : Nat} (h : 0 < N) (a : Int) :
    (Ecore a N : LeviCivitaFieldOver K) = root N h ^ a.toNat * (root N h ^ (-a).toNat)⁻¹ := by
  unfold Ecore; rw [dif_pos h]

theorem Ecore_pos (a : Int) (N : Nat) : 0 < (Ecore a N : LeviCivitaFieldOver K) := by
  unfold Ecore
  split
  · next h =>
    exact OrderedRing.mul_pos (Limits.pow_pos (root_pos N h) _)
      (Field.IsOrdered.inv_pos_iff.mpr (Limits.pow_pos (root_pos N h) _))
  · exact OrderedRing.zero_lt_one

theorem Ecore_scale (a : Int) {N M : Nat} (hN : 0 < N) (hM : 0 < M) :
    (Ecore (a * (M : Int)) (N * M) : LeviCivitaFieldOver K) = Ecore a N := by
  have e : a * (M : Int) = ((a.toNat * M : Nat) : Int) - (((-a).toNat * M : Nat) : Int) := by
    have := Int.toNat_sub_toNat_neg a
    simp only [Int.natCast_mul]; grind
  rw [e, Ecore_nat (Nat.mul_pos hN hM), Ecore_int hN, Nat.mul_comm a.toNat, Nat.mul_comm (-a).toNat,
    pow_mul'', pow_mul'']
  have := Puiseux.root_mul_pow (K := K) N M hN hM
  have hr : (root (N * M) (Nat.mul_pos hN hM) : LeviCivitaFieldOver K) ^ M = root N hN := by
    unfold root; rw [const_pow, this]
  rw [hr]

theorem Ecore_wd {a b : Int} {N M : Nat} (hN : 0 < N) (hM : 0 < M) (h : a * M = b * N) :
    (Ecore a N : LeviCivitaFieldOver K) = Ecore b M := by
  rw [← Ecore_scale a hN hM, h, Nat.mul_comm N M, Ecore_scale b hM hN]

theorem Ecore_add {N : Nat} (h : 0 < N) (a b : Int) :
    (Ecore (a + b) N : LeviCivitaFieldOver K) = Ecore a N * Ecore b N := by
  have e : a + b = ((a.toNat + b.toNat : Nat) : Int) - (((-a).toNat + (-b).toNat : Nat) : Int) := by
    have := Int.toNat_sub_toNat_neg a; have := Int.toNat_sub_toNat_neg b
    simp only [Int.natCast_add]; omega
  rw [e, Ecore_nat h, Ecore_int h a, Ecore_int h b, Semiring.pow_add, Semiring.pow_add,
    Field.inv_mul]
  grind

theorem epow_eq {q : Rat} {a : Int} {N : Nat} (hN : 0 < N) (h : q = mkRat a N) :
    (epow q : LeviCivitaFieldOver K) = Ecore a N := by
  unfold epow
  apply Ecore_wd q.den_pos hN
  have := (Rat.mkRat_eq_iff q.den_nz (show N ≠ 0 by omega)).mp (by rw [Rat.mkRat_self]; exact h)
  exact this

theorem epow_add (p q : Rat) :
    (epow (p + q) : LeviCivitaFieldOver K) = epow p * epow q := by
  rw [epow_eq (Nat.mul_pos p.den_pos q.den_pos) (Rat.add_def' p q),
    Ecore_add (Nat.mul_pos p.den_pos q.den_pos), Ecore_scale _ p.den_pos q.den_pos,
    Nat.mul_comm p.den q.den, Ecore_scale _ q.den_pos p.den_pos]
  rfl

theorem epow_pos (q : Rat) : 0 < (epow q : LeviCivitaFieldOver K) := Ecore_pos _ _

theorem root_le_one (N : Nat) (hN : 0 < N) : (root N hN : LeviCivitaFieldOver K) ≤ 1 := by
  have := root_lt_ofK (K := K) N hN (q := 1) OrderedRing.zero_lt_one
  rw [ofK_one'] at this; exact Std.le_of_lt this

theorem epow_small {q : Rat} (hq : 0 < q) {r : K} (hr : 0 < r) :
    (epow q : LeviCivitaFieldOver K) < ofK r := by
  have hnum : 0 < q.num := by
    have h1 := Rat.num_nonneg.mpr (Std.le_of_lt hq)
    have h2 : q.num ≠ 0 := fun h => by rw [Rat.num_eq_zero] at h; rw [h] at hq; exact (Rat.lt_irrefl hq)
    omega
  unfold epow
  rw [show q.num = ((q.num.toNat : Nat) : Int) - ((0 : Nat) : Int) by omega, Ecore_nat q.den_pos,
    Semiring.pow_zero, Field.inv_one, Semiring.mul_one]
  have h1 := Poly.pow_anti (Std.le_of_lt (root_pos (K := K) q.den q.den_pos))
    (root_le_one q.den q.den_pos) (show 1 ≤ q.num.toNat by omega)
  rw [show (root q.den q.den_pos : LeviCivitaFieldOver K) ^ 1 = root q.den q.den_pos by
    rw [show (1 : Nat) = 0 + 1 from rfl, Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul]] at h1
  exact Std.lt_of_le_of_lt h1 (root_lt_ofK q.den q.den_pos hr)

/-- The embedding and `ε`-powers. -/
def pre : LCPre K (LeviCivitaFieldOver K) where
  ι := ofK
  ι_add := ofK_add'
  ι_mul := ofK_mul'
  ι_one := ofK_one'
  ι_lt := ofK_lt'
  e := epow
  e_add := epow_add
  e_pos := epow_pos
  e_small := fun _ hq _ hr => epow_small hq hr

theorem pre_ι (r : K) : (pre : LCPre K (LeviCivitaFieldOver K)).ι r = ofK r := rfl
theorem pre_e (q : Rat) : (pre : LCPre K (LeviCivitaFieldOver K)).e q = epow q := rfl

/-! ### Leading terms in the completion -/

theorem const_root_pow (N : Nat) (hN : 0 < N) (n m : Nat) :
    (const (Puiseux.root N hN ^ n * (Puiseux.root N hN ^ m)⁻¹) : LeviCivitaFieldOver K) =
      epow (mkRat ((n : Int) - m) N) := by
  rw [epow_eq hN rfl, Ecore_nat hN, const_mul, const_inv', ← const_pow, ← const_pow]; rfl

theorem inf_const {δ : Puiseux K} (h : ∀ s : K, 0 < s → abs δ < Puiseux.ofK s) :
    (pre : LCPre K (LeviCivitaFieldOver K)).Inf (const δ) := fun s hs => by
  rw [pre_ι, abs_const]; exact const_lt.mpr (h s hs)

theorem eps_inf : (pre : LCPre K (LeviCivitaFieldOver K)).Inf eps := fun s hs => by
  rw [pre_ι, abs_of_nonneg (Std.le_of_lt eps_pos)]
  exact const_lt.mpr (Puiseux.ofL_lt.mpr (Laurent.eps_lt_ofK hs))

theorem lead (x : LeviCivitaFieldOver K) (hx : x ≠ 0) : ∃ (r : K) (q : Rat)
    (δ : LeviCivitaFieldOver K), r ≠ 0 ∧ (∀ s : K, 0 < s → abs δ < ofK s) ∧
    x = ofK r * epow q * (1 + δ) := by
  have P := (pre : LCPre K (LeviCivitaFieldOver K))
  have hax := abs_pos hx
  obtain ⟨d, hd, hdx⟩ := pos_bound hax
  obtain ⟨c, hc⟩ := dense x (OrderedRing.mul_pos hd Puiseux.eps_pos)
  rw [const_mul] at hc
  have hnear : abs (x - const c) < const d * eps := near_iff.mp hc
  -- `ε ≤ 1/2`
  have he2 : eps + eps ≤ (1 : LeviCivitaFieldOver K) := by
    have := eps_inf (K := K) (2⁻¹) (Field.IsOrdered.inv_pos_iff.mpr (by grind))
    rw [abs_of_nonneg (Std.le_of_lt eps_pos), pre_ι] at this
    have h2 : (ofK (2⁻¹ : K) : LeviCivitaFieldOver K) + ofK 2⁻¹ = 1 := by
      rw [← ofK_add', ← ofK_one']; congr 1
      have := Field.mul_inv_cancel (show (2 : K) ≠ 0 by grind); grind
    grind
  have hde : const d * eps ≤ abs x * eps :=
    OrderedRing.mul_le_mul_of_nonneg_right (Std.le_of_lt hdx) (Std.le_of_lt eps_pos)
  -- `|c| ≥ |x| / 2`
  have htri := abs_add_le (x - const c) (const c)
  rw [show x - const c + const c = x by grind] at htri
  have hxe : abs x * eps + abs x * eps ≤ abs x := by
    have := OrderedRing.mul_le_mul_of_nonneg_left he2 (abs_nonneg x); grind
  have hc0 : (const c : LeviCivitaFieldOver K) ≠ 0 := by
    intro h; rw [h, abs_zero] at htri
    have := OrderedRing.mul_pos hax eps_pos; grind
  have hcbig : abs x ≤ abs (const c : LeviCivitaFieldOver K) + abs (const c) := by grind
  -- `δ' = (x - c)/c`, `|δ'| ≤ 2 ε`
  obtain ⟨δ', hδ'⟩ : ∃ δ', δ' = (x - const c) * (const c)⁻¹ := ⟨_, rfl⟩
  have hxc : x = const c * (1 + δ') := by
    rw [hδ']; have := Field.mul_inv_cancel hc0; grind
  have hδ'inf : (pre : LCPre K (LeviCivitaFieldOver K)).Inf δ' := by
    have hci := Field.IsOrdered.inv_pos_iff.mpr (abs_pos hc0)
    have habs : abs δ' = abs (x - const c) * (abs (const c))⁻¹ := by
      rw [hδ', abs_mul]; congr 1
      apply Field.eq_inv_of_mul_eq_one
      rw [← abs_mul, Field.inv_mul_cancel hc0, abs_of_nonneg OrderedRing.zero_le_one]
    have hb : abs δ' ≤ eps + eps := by
      rw [habs]
      have h1 := OrderedRing.mul_le_mul_of_nonneg_right
        (Std.le_of_lt (Std.lt_of_lt_of_le hnear hde)) (Std.le_of_lt hci)
      have h2 := OrderedRing.mul_le_mul_of_nonneg_right
        (OrderedRing.mul_le_mul_of_nonneg_right hcbig (Std.le_of_lt eps_pos)) (Std.le_of_lt hci)
      have := Field.mul_inv_cancel (show abs (const c : LeviCivitaFieldOver K) ≠ 0 by grind)
      have e1 : (abs (const c) + abs (const c)) * eps * (abs (const c))⁻¹ =
          (eps + eps : LeviCivitaFieldOver K) := by grind
      rw [e1] at h2
      exact Std.le_trans h1 h2
    intro s hs
    have := pre.inf_add eps_inf eps_inf s hs
    rw [abs_of_nonneg (by have := eps_pos (K := K); grind)] at this
    exact Std.lt_of_le_of_lt hb this
  -- the leading term of `c`
  obtain ⟨r, N, hN, n, m, δ, hr, hδ, hce⟩ := puiseux_lead c (fun h => hc0 (by rw [h]; rfl))
  refine ⟨r, mkRat ((n : Int) - m) N, const δ + δ' + const δ * δ', hr, ?_, ?_⟩
  · have hi := pre.inf_add (pre.inf_add (inf_const hδ) hδ'inf)
      (pre.inf_mul (inf_const hδ) (pre.fin_of_inf hδ'inf))
    exact fun s hs => by have := hi s hs; rwa [pre_ι] at this
  · rw [hxc, hce, ← const_root_pow N hN n m]
    unfold ofK
    simp only [const_mul, const_add, const_one']
    grind

/-- **Levi-Civita data** for the Levi-Civita field over `K`. -/
def lcData : LCData K (LeviCivitaFieldOver K) where
  toLCPre := pre
  lead := lead
  complete := fun s hs => by
    obtain ⟨x, hx⟩ := complete s hs
    exact ⟨x, tendsto_of_near hx⟩

/-- **The Levi-Civita field over an ordered field with the polynomial intermediate value
property is real closed.** -/
theorem isRealClosed (hK : IVT K) : IsRealClosed (LeviCivitaFieldOver K) :=
  lcData.isRealClosed hK

end

/-- **The Levi-Civita field over `ℝ` is real closed.** -/
theorem real_isRealClosed : IsRealClosed (LeviCivitaFieldOver Real) :=
  isRealClosed Real.ivt

end LeviCivitaFieldOver

end LeviCivita
