import LeviCivita.Series

/-!
# Puiseux series: rational exponents

The Laurent field `K((ε))` only has integer exponents. Puiseux series allow
every rational exponent with a bounded denominator: an element is a Laurent
series in `ε^{1/N}` for some `N ≥ 1`. We build them by gluing the copies
`K((ε^{1/N}))` along the substitutions `ε^{1/N} ↦ (ε^{1/NM})^M`.

* `PS.sub k`: the substitution `ε ↦ εᵏ` on power series. It is an injective
  ring map that preserves the order.
* `Frac.map`: any such map extends to the fields of fractions, so `subL k` acts
  on `Laurent K`.
* `Puiseux K`: pairs `(N, x)` meaning `x(ε^{1/N})`, with `(N, x) ~ (M, y)` iff
  `x(ε^{M}) = y(ε^{N})`. An ordered field (`Lean.Grind.Field`,
  `Lean.Grind.OrderedRing`).
* `Puiseux.root N`, the series `ε^{1/N}`, satisfies `root N ^ N = ε`, and it is a
  positive infinitesimal.

`Puiseux K` is the subfield of the Levi-Civita field made of the series whose
exponents have bounded denominators. The full Levi-Civita field also allows
exponent sequences such as `1 − 1/n` with growing denominators.
-/

set_option linter.unusedSectionVars false

namespace LeviCivita.Series

open Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast
attribute [local instance high] Semiring.ofNat

variable {K : Type u} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

namespace PS

/-! ## Substitution `ε ↦ εᵏ` -/

/-- `(sub k a)(ε) = a(εᵏ)`. -/
def sub (k : Nat) (a : PS K) : PS K := ⟨fun n => if n % k = 0 then a.coeff (n / k) else 0⟩

theorem sub_coeff_mul {k : Nat} (hk : 0 < k) (a : PS K) (m : Nat) :
    (sub k a).coeff (k * m) = a.coeff m := by
  simp [sub, Nat.mul_mod_right, Nat.mul_div_cancel_left m hk]

theorem sub_coeff_ne {k : Nat} (a : PS K) {n : Nat} (h : n % k ≠ 0) : (sub k a).coeff n = 0 := by
  simp [sub, h]

theorem sub_add (k : Nat) (a b : PS K) : sub k (a + b) = sub k a + sub k b := by
  ext n; simp only [sub, coeff_add]; split <;> grind

theorem sub_neg (k : Nat) (a : PS K) : sub k (-a) = -sub k a := by
  ext n; simp only [sub, coeff_neg]; split <;> grind

theorem sub_C {k : Nat} (_hk : 0 < k) (c : K) : sub k (C c) = C c := by
  ext n; simp only [sub, coeff_C]
  by_cases h : n % k = 0
  · simp only [h, ↓reduceIte]
    have e := Nat.mod_add_div n k
    by_cases hn : n = 0
    · subst hn; simp
    · have : n / k ≠ 0 := by
        intro h0; rw [h, h0, Nat.mul_zero] at e; omega
      simp [this, hn]
  · simp only [h, ↓reduceIte]
    have : n ≠ 0 := by intro h0; subst h0; simp at h
    simp [this]

theorem sub_one {k : Nat} (hk : 0 < k) : sub k (1 : PS K) = 1 := sub_C hk 1
theorem sub_zero' {k : Nat} (hk : 0 < k) : sub k (0 : PS K) = 0 := sub_C hk 0

/-- Split a sum into a prefix and a block. -/
theorem S_split (a b : Nat) (f : Nat → K) : S (a + b) f = S a f + S b (fun i => f (a + i)) := by
  induction b with
  | zero => simp <;> grind
  | succ b ih => rw [← Nat.add_assoc, S_succ, ih, S_succ]; grind

/-- A sum supported on multiples of `k`. -/
theorem S_sparse {k : Nat} (hk : 0 < k) (m : Nat) (f : Nat → K)
    (hf : ∀ j, j % k ≠ 0 → f j = 0) : S (k * m + 1) f = S (m + 1) (fun i => f (k * i)) := by
  induction m with
  | zero => simp [S_succ]
  | succ m ih =>
    rw [show k * (m + 1) + 1 = (k * m + 1) + k by simp only [Nat.mul_add, Nat.mul_one]; omega, S_split, ih, S_succ]
    congr 1
    rw [S_eq_single (j := k - 1) (by omega)]
    · congr 1; rw [Nat.mul_succ]; omega
    · intro i hi hij
      apply hf
      rw [show k * m + 1 + i = k * m + (i + 1) by omega, Nat.mul_add_mod,
        Nat.mod_eq_of_lt (by omega)]
      omega

theorem S_sparse' {k : Nat} (hk : 0 < k) (n : Nat) (f : Nat → K)
    (hf : ∀ j, j % k ≠ 0 → f j = 0) : S (n + 1) f = S (n / k + 1) (fun i => f (k * i)) := by
  have e := Nat.mod_add_div n k
  have hr := Nat.mod_lt n hk
  rw [show n + 1 = (k * (n / k) + 1) + n % k by omega, S_split, S_sparse hk _ f hf]
  rw [S_eq_zero (n := n % k) (f := fun i => f (k * (n / k) + 1 + i)) (fun i hi => hf _ (by
    rw [show k * (n / k) + 1 + i = k * (n / k) + (i + 1) by omega, Nat.mul_add_mod,
      Nat.mod_eq_of_lt (by omega)]; omega))]
  grind

private theorem sub_mod {k j n : Nat} (hjn : j ≤ n) (hj : j % k = 0) : (n - j) % k = n % k := by
  have e := Nat.mod_add_div j k
  rw [hj, Nat.zero_add] at e
  conv => rhs; rw [show n = (n - j) + k * (j / k) by omega]
  rw [Nat.add_comm, Nat.mul_add_mod]

theorem sub_mul {k : Nat} (hk : 0 < k) (a b : PS K) : sub k (a * b) = sub k a * sub k b := by
  ext n
  rw [coeff_mul]
  by_cases hn : n % k = 0
  · have e := Nat.mod_add_div n k
    rw [hn, Nat.zero_add] at e
    rw [← e, sub_coeff_mul hk, coeff_mul]
    rw [S_sparse' hk (k * (n / k)) _ (fun j hj => by rw [sub_coeff_ne a hj]; grind)]
    rw [Nat.mul_div_cancel_left _ hk]
    apply S_congr; intro i hi
    rw [sub_coeff_mul hk, ← Nat.mul_sub, sub_coeff_mul hk]
  · rw [sub_coeff_ne _ hn]
    symm; apply S_eq_zero; intro j hj
    by_cases hjk : j % k = 0
    · rw [sub_coeff_ne b (n := n - j) (by rw [sub_mod (by omega) hjk]; exact hn)]; grind
    · rw [sub_coeff_ne a hjk]; grind

theorem sub_sub {a b : Nat} (ha : 0 < a) (hb : 0 < b) (x : PS K) :
    sub a (sub b x) = sub (a * b) x := by
  ext n
  by_cases h : n % (a * b) = 0
  · have e := Nat.mod_add_div n (a * b)
    rw [h, Nat.zero_add] at e
    rw [← e, sub_coeff_mul (Nat.mul_pos ha hb), Nat.mul_assoc, sub_coeff_mul ha, sub_coeff_mul hb]
  · rw [sub_coeff_ne _ h]
    by_cases h1 : n % a = 0
    · have e := Nat.mod_add_div n a
      rw [h1, Nat.zero_add] at e
      rw [← e, sub_coeff_mul ha]
      apply sub_coeff_ne
      intro h2; apply h
      have e2 := Nat.mod_add_div (n / a) b
      rw [h2, Nat.zero_add] at e2
      rw [← e, ← e2, ← Nat.mul_assoc, Nat.mul_mod_right]
    · exact sub_coeff_ne _ h1

theorem sub_inj {k : Nat} (hk : 0 < k) {a b : PS K} (h : sub k a = sub k b) : a = b := by
  ext m; rw [← sub_coeff_mul hk a, ← sub_coeff_mul hk b, h]

theorem sub_isPos {k : Nat} (hk : 0 < k) (a : PS K) : IsPos (sub k a) ↔ IsPos a := by
  constructor
  · rintro ⟨p, hp0, hp⟩
    have hpk : p % k = 0 := Classical.byContradiction fun h => by rw [sub_coeff_ne a h] at hp; grind
    have e := Nat.mod_add_div p k
    rw [hpk, Nat.zero_add] at e
    refine ⟨p / k, fun m hm => ?_, ?_⟩
    · rw [← sub_coeff_mul hk]; apply hp0
      have : k * m < k * (p / k) := Nat.mul_lt_mul_of_pos_left hm hk
      omega
    · rw [← sub_coeff_mul hk, e]; exact hp
  · rintro ⟨p, hp0, hp⟩
    refine ⟨k * p, fun m hm => ?_, by rw [sub_coeff_mul hk]; exact hp⟩
    by_cases h : m % k = 0
    · have e := Nat.mod_add_div m k
      rw [h, Nat.zero_add] at e
      rw [← e, sub_coeff_mul hk]; apply hp0
      apply Classical.byContradiction; intro h'
      have : k * p ≤ k * (m / k) := Nat.mul_le_mul_left k (by omega)
      omega
    · exact sub_coeff_ne a h

theorem sub_lt {k : Nat} (hk : 0 < k) {a b : PS K} : sub k a < sub k b ↔ a < b := by
  have : sub k (b - a) = sub k b - sub k a := by
    show sub k (b + -a) = sub k b + -sub k a; rw [sub_add, sub_neg]
  rw [lt_def, lt_def, ← this, sub_isPos hk]

theorem X_pow_coeff (N n : Nat) : ((X : PS K) ^ N).coeff n = if n = N then 1 else 0 := by
  induction N generalizing n with
  | zero => show (C (1 : K)).coeff n = _; simp
  | succ N ih =>
    show ((X : PS K) ^ N * X).coeff n = _
    rw [PS.mul_comm, coeff_mul]
    cases n with
    | zero => simp [S_succ] <;> grind
    | succ n =>
      rw [S_eq_single (j := 1) (by omega) (fun i hi hi1 => by simp [hi1]; grind)]
      simp [ih]; split <;> grind

theorem sub_X {k : Nat} (hk : 0 < k) : sub k (X : PS K) = (X : PS K) ^ k := by
  ext n; rw [X_pow_coeff]
  by_cases h : n % k = 0
  · have e := Nat.mod_add_div n k
    rw [h, Nat.zero_add] at e
    rw [← e, sub_coeff_mul hk, coeff_X]
    by_cases h1 : n / k = 1
    · rw [h1]; simp
    · simp only [h1, ↓reduceIte]
      have : k * (n / k) ≠ k := fun h2 => h1 (by
        have := Nat.mul_div_cancel_left (n / k) hk; rw [h2, Nat.div_self hk] at this; omega)
      simp [this]
  · rw [sub_coeff_ne _ h]
    have : n ≠ k := by intro h2; subst h2; simp at h
    simp [this]

theorem sub_one_id (a : PS K) : sub 1 a = a := by
  ext n; simp [sub, Nat.mod_one]

end PS

end LeviCivita.Series

/-! ## Extending a ring embedding to fractions -/

namespace LeviCivita.Frac

open Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast
attribute [local instance high] Semiring.ofNat

/-- An injective ring map. -/
structure Emb (R : Type u) (R' : Type v) [CommRing R] [CommRing R'] where
  f : R → R'
  map_add : ∀ a b, f (a + b) = f a + f b
  map_mul : ∀ a b, f (a * b) = f a * f b
  map_neg : ∀ a, f (-a) = -f a
  map_one : f 1 = 1
  map_zero : f 0 = 0
  inj : ∀ a, f a = 0 → a = 0

variable {R : Type u} {R' : Type v} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

omit [IsDomain R] [IsDomain R'] in
private theorem Emb.ne (e : Emb R R') {b : R} (hb : b ≠ 0) : e.f b ≠ 0 := fun h => hb (e.inj b h)

private theorem map_congr (e : Emb R R') (x y : Pair R) (h : x ≈ y) :
    mk (e.f x.val.1) (e.f x.val.2) (e.ne x.property) =
      mk (e.f y.val.1) (e.f y.val.2) (e.ne y.property) := by
  obtain ⟨⟨a, b⟩, hb⟩ := x; obtain ⟨⟨c, d⟩, hd⟩ := y
  have h : a * d = c * b := h
  rw [mk_eq, ← e.map_mul, ← e.map_mul, h]

/-- The induced map `a / b ↦ f a / f b`. -/
def map (e : Emb R R') : Frac R → Frac R' :=
  Quotient.lift (fun p => mk (e.f p.val.1) (e.f p.val.2) (e.ne p.property)) (map_congr e)

theorem map_mk (e : Emb R R') (a b : R) (hb : b ≠ 0) :
    map e (mk a b hb) = mk (e.f a) (e.f b) (e.ne hb) := rfl

theorem map_add (e : Emb R R') (x y : Frac R) : map e (x + y) = map e x + map e y := by
  induction x using ind with | h a b hb =>
  induction y using ind with | h c d hd =>
  rw [mk_add, map_mk, map_mk, map_mk, mk_add, mk_eq]
  simp only [e.map_add, e.map_mul]

theorem map_mul (e : Emb R R') (x y : Frac R) : map e (x * y) = map e x * map e y := by
  induction x using ind with | h a b hb =>
  induction y using ind with | h c d hd =>
  rw [mk_mul, map_mk, map_mk, map_mk, mk_mul, mk_eq]
  simp only [e.map_mul]

theorem map_neg (e : Emb R R') (x : Frac R) : map e (-x) = -map e x := by
  induction x using ind with | h a b hb =>
  rw [mk_neg, map_mk, map_mk, mk_neg, e.map_neg]

theorem map_one (e : Emb R R') : map e 1 = 1 := by
  rw [one_def, map_mk, one_def, mk_eq]; simp only [e.map_one]

theorem map_zero (e : Emb R R') : map e 0 = 0 := by
  rw [zero_def, map_mk, zero_def, mk_eq]; simp only [e.map_one, e.map_zero]

theorem map_eq_zero (e : Emb R R') {x : Frac R} (h : map e x = 0) : x = 0 := by
  induction x using ind with | h a b hb =>
  rw [map_mk, mk_eq_zero] at h
  rw [mk_eq_zero]; exact e.inj a h

theorem map_inj (e : Emb R R') {x y : Frac R} (h : map e x = map e y) : x = y := by
  have : map e (x - y) = 0 := by
    show map e (x + -y) = 0; rw [map_add, map_neg, h]; grind
  have := map_eq_zero e this; grind

theorem map_inv [DecidableEq R] [DecidableEq R'] (e : Emb R R') (x : Frac R) :
    map e x⁻¹ = (map e x)⁻¹ := by
  induction x using ind with | h a b hb =>
  by_cases ha : a = 0
  · subst ha; rw [mk_inv_zero, map_zero, map_mk, e.map_zero, mk_inv_zero]
  · rw [mk_inv a b hb ha, map_mk, map_mk, mk_inv _ _ _ (e.ne ha)]

section Order
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R] [OrderedRing R]
variable [LE R'] [LT R'] [Std.IsLinearOrder R'] [Std.LawfulOrderLT R'] [OrderedRing R']

theorem map_lt (e : Emb R R') (hpos : ∀ a : R, 0 < e.f a ↔ 0 < a) {x y : Frac R} :
    map e x < map e y ↔ x < y := by
  rw [lt_def, lt_def]
  have : map e y - map e x = map e (y - x) := by
    show map e y + -map e x = map e (y + -x); rw [map_add, map_neg]
  rw [this]
  generalize y - x = z
  induction z using ind with | h a b hb =>
  rw [map_mk, isPos_mk, isPos_mk, ← e.map_mul, hpos]

end Order

end LeviCivita.Frac

/-! ## Substitution on Laurent series -/

namespace LeviCivita.Series

open PS Frac Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast
attribute [local instance high] Semiring.ofNat

variable {K : Type u} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

/-- `ε ↦ εᵏ` as an embedding of power series, for `k > 0`. -/
def subEmb (k : Nat) (hk : 0 < k) : Emb (PS K) (PS K) where
  f := sub k
  map_add := sub_add k
  map_mul := sub_mul hk
  map_neg := sub_neg k
  map_one := sub_one hk
  map_zero := sub_zero' hk
  inj a h := sub_inj hk (by rw [h, sub_zero' hk])

/-- `(subL k x)(ε) = x(εᵏ)` on Laurent series. For `k = 0` it is the identity
(a junk value that keeps the ring-map laws unconditional). -/
def subL (k : Nat) (x : Laurent K) : Laurent K := if hk : 0 < k then map (subEmb k hk) x else x

theorem subL_add (k : Nat) (x y : Laurent K) : subL k (x + y) = subL k x + subL k y := by
  unfold subL; split
  · exact map_add _ x y
  · rfl
theorem subL_mul (k : Nat) (x y : Laurent K) : subL k (x * y) = subL k x * subL k y := by
  unfold subL; split
  · exact map_mul _ x y
  · rfl
theorem subL_neg (k : Nat) (x : Laurent K) : subL k (-x) = -subL k x := by
  unfold subL; split
  · exact map_neg _ x
  · rfl
theorem subL_inv (k : Nat) (x : Laurent K) : subL k x⁻¹ = (subL k x)⁻¹ := by
  unfold subL; split
  · exact map_inv _ x
  · rfl
theorem subL_one (k : Nat) : subL k (1 : Laurent K) = 1 := by
  unfold subL; split
  · exact map_one _
  · rfl
theorem subL_zero (k : Nat) : subL k (0 : Laurent K) = 0 := by
  unfold subL; split
  · exact map_zero _
  · rfl
theorem subL_sub (k : Nat) (x y : Laurent K) : subL k (x - y) = subL k x - subL k y := by
  show subL k (x + -y) = subL k x + -subL k y; rw [subL_add, subL_neg]

theorem subL_ofRing (k : Nat) (hk : 0 < k) (a : PS K) : subL k (ofRing a) = ofRing (sub k a) := by
  unfold subL; simp only [hk, ↓reduceDIte]
  unfold ofRing; rw [map_mk, mk_eq]; simp only [subEmb, sub_one hk]

theorem subL_subL {a b : Nat} (ha : 0 < a) (hb : 0 < b) (x : Laurent K) :
    subL a (subL b x) = subL (a * b) x := by
  have hab := Nat.mul_pos ha hb
  unfold subL; simp only [ha, hb, hab, ↓reduceDIte]
  induction x using ind with | h p q hq =>
  rw [map_mk, map_mk, map_mk]; simp only [subEmb, sub_sub ha hb]

theorem subL_one_id (x : Laurent K) : subL 1 x = x := by
  have h1 : 0 < 1 := by decide
  unfold subL; simp only [h1, ↓reduceDIte]
  induction x using ind with | h p q hq =>
  rw [map_mk]; simp only [subEmb, sub_one_id]

theorem subL_inj {k : Nat} (hk : 0 < k) {x y : Laurent K} (h : subL k x = subL k y) : x = y := by
  unfold subL at h; simp only [hk, ↓reduceDIte] at h; exact map_inj _ h

theorem subL_lt {k : Nat} (hk : 0 < k) {x y : Laurent K} : subL k x < subL k y ↔ x < y := by
  unfold subL; simp only [hk, ↓reduceDIte]
  exact map_lt _ (fun a => by
    have := sub_lt hk (a := 0) (b := a)
    rw [sub_zero' hk] at this; exact this)

theorem subL_pos {k : Nat} (hk : 0 < k) {x : Laurent K} : 0 < subL k x ↔ 0 < x := by
  have := subL_lt hk (x := 0) (y := x); rw [subL_zero] at this; exact this

/-- Combine nested substitutions after reassociating the levels. -/
theorem subL_subL' {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (h : a * b = c) (x : Laurent K) :
    subL a (subL b x) = subL c x := by rw [subL_subL ha hb, h]

end LeviCivita.Series

/-! ## The Puiseux field -/

namespace LeviCivita.Series

open PS Frac Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast
attribute [local instance high] Semiring.ofNat

variable {K : Type u} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

/-- Positivity of products of positive levels. -/
macro "npos" : tactic => `(tactic| (repeat (first | assumption | decide | apply Nat.mul_pos)))

/-- `(N, x)` stands for `x(ε^{1/N})`. -/
def PPair (K : Type u) [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
    [OrderedRing K] := { p : Nat × Laurent K // 0 < p.1 }

/-- `x(ε^{1/N}) = y(ε^{1/M})` iff `x(ε^M) = y(ε^N)`. -/
def PRel (p q : PPair K) : Prop := subL q.val.1 p.val.2 = subL p.val.1 q.val.2

theorem prel_equiv : Equivalence (PRel (K := K)) where
  refl _ := rfl
  symm h := h.symm
  trans {p q r} h1 h2 := by
    obtain ⟨⟨N, x⟩, hN⟩ := p; obtain ⟨⟨M, y⟩, hM⟩ := q; obtain ⟨⟨K, z⟩, hK⟩ := r
    have h1 : subL M x = subL N y := h1
    have h2 : subL K y = subL M z := h2
    show subL K x = subL N z
    apply subL_inj hM
    rw [subL_subL hM hK, Nat.mul_comm M K, ← subL_subL hK hM, h1, subL_subL hK hN,
      Nat.mul_comm K N, ← subL_subL hN hK, h2, subL_subL hN hM, Nat.mul_comm N M,
      ← subL_subL hM hN]

instance psetoid : Setoid (PPair K) := ⟨PRel, prel_equiv⟩

/-- Puiseux series: Laurent series in `ε^{1/N}` for some `N ≥ 1`. -/
def Puiseux (K : Type u) [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
    [OrderedRing K] := Quotient (psetoid (K := K))

namespace Puiseux

noncomputable section

/-- `x(ε^{1/N})`. -/
def mk (N : Nat) (hN : 0 < N) (x : Laurent K) : Puiseux K := Quotient.mk _ ⟨(N, x), hN⟩

theorem mk_eq {N M : Nat} {hN : 0 < N} {hM : 0 < M} {x y : Laurent K} :
    mk N hN x = mk M hM y ↔ subL M x = subL N y :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

theorem ind {P : Puiseux K → Prop} (h : ∀ N hN x, P (mk N hN x)) (z : Puiseux K) : P z :=
  Quotient.ind (fun ⟨⟨N, x⟩, hN⟩ => h N hN x) z

/-- Rescale one side of a relation `subL N' x = subL N x'`. -/
theorem scale {N N' : Nat} (hN : 0 < N) (hN' : 0 < N') {x x' : Laurent K}
    (h : subL N' x = subL N x') {c d e : Nat} (he : 0 < e) (hc : c = e * N') (hd : d = e * N) :
    subL c x = subL d x' := by
  subst hc hd; rw [← subL_subL he hN', h, subL_subL he hN]

private theorem add_congr (p q p' q' : PPair K) (h1 : p ≈ p') (h2 : q ≈ q') :
    mk (p.val.1 * q.val.1) (Nat.mul_pos p.property q.property)
        (subL q.val.1 p.val.2 + subL p.val.1 q.val.2) =
      mk (p'.val.1 * q'.val.1) (Nat.mul_pos p'.property q'.property)
        (subL q'.val.1 p'.val.2 + subL p'.val.1 q'.val.2) := by
  obtain ⟨⟨N, x⟩, hN⟩ := p; obtain ⟨⟨M, y⟩, hM⟩ := q
  obtain ⟨⟨N', x'⟩, hN'⟩ := p'; obtain ⟨⟨M', y'⟩, hM'⟩ := q'
  have h1 : subL N' x = subL N x' := h1
  have h2 : subL M' y = subL M y' := h2
  rw [mk_eq]
  simp only [subL_add]
  rw [subL_subL (by npos) hM, subL_subL (by npos) hN, subL_subL (by npos) hM',
    subL_subL (by npos) hN']
  rw [scale hN hN' h1 (e := M' * M) (by npos) (by grind) (by grind : N * M * M' = M' * M * N),
    scale hM hM' h2 (e := N' * N) (by npos) (by grind) (by grind : N * M * N' = N' * N * M)]

private theorem mul_congr (p q p' q' : PPair K) (h1 : p ≈ p') (h2 : q ≈ q') :
    mk (p.val.1 * q.val.1) (Nat.mul_pos p.property q.property)
        (subL q.val.1 p.val.2 * subL p.val.1 q.val.2) =
      mk (p'.val.1 * q'.val.1) (Nat.mul_pos p'.property q'.property)
        (subL q'.val.1 p'.val.2 * subL p'.val.1 q'.val.2) := by
  obtain ⟨⟨N, x⟩, hN⟩ := p; obtain ⟨⟨M, y⟩, hM⟩ := q
  obtain ⟨⟨N', x'⟩, hN'⟩ := p'; obtain ⟨⟨M', y'⟩, hM'⟩ := q'
  have h1 : subL N' x = subL N x' := h1
  have h2 : subL M' y = subL M y' := h2
  rw [mk_eq]
  simp only [subL_mul]
  rw [subL_subL (by npos) hM, subL_subL (by npos) hN, subL_subL (by npos) hM',
    subL_subL (by npos) hN']
  rw [scale hN hN' h1 (e := M' * M) (by npos) (by grind) (by grind : N * M * M' = M' * M * N),
    scale hM hM' h2 (e := N' * N) (by npos) (by grind) (by grind : N * M * N' = N' * N * M)]

private theorem neg_congr (p p' : PPair K) (h : p ≈ p') :
    mk p.val.1 p.property (-p.val.2) = mk p'.val.1 p'.property (-p'.val.2) := by
  obtain ⟨⟨N, x⟩, hN⟩ := p; obtain ⟨⟨N', x'⟩, hN'⟩ := p'
  have h : subL N' x = subL N x' := h
  rw [mk_eq, subL_neg, subL_neg, h]

private theorem inv_congr (p p' : PPair K) (h : p ≈ p') :
    mk p.val.1 p.property (p.val.2)⁻¹ = mk p'.val.1 p'.property (p'.val.2)⁻¹ := by
  obtain ⟨⟨N, x⟩, hN⟩ := p; obtain ⟨⟨N', x'⟩, hN'⟩ := p'
  have h : subL N' x = subL N x' := h
  rw [mk_eq, subL_inv, subL_inv, h]

private theorem one_pos : 0 < 1 := by decide

instance : Add (Puiseux K) := ⟨Quotient.lift₂ (fun p q => mk (p.val.1 * q.val.1)
  (Nat.mul_pos p.property q.property) (subL q.val.1 p.val.2 + subL p.val.1 q.val.2)) add_congr⟩
instance : Mul (Puiseux K) := ⟨Quotient.lift₂ (fun p q => mk (p.val.1 * q.val.1)
  (Nat.mul_pos p.property q.property) (subL q.val.1 p.val.2 * subL p.val.1 q.val.2)) mul_congr⟩
instance : Neg (Puiseux K) := ⟨Quotient.lift (fun p => mk p.val.1 p.property (-p.val.2)) neg_congr⟩
instance : Inv (Puiseux K) := ⟨Quotient.lift (fun p => mk p.val.1 p.property (p.val.2)⁻¹) inv_congr⟩
instance : Sub (Puiseux K) := ⟨fun x y => x + -y⟩
instance : Div (Puiseux K) := ⟨fun x y => x * y⁻¹⟩

/-- The embedding of Laurent series (`N = 1`). -/
def ofL (x : Laurent K) : Puiseux K := mk 1 one_pos x

instance : Zero (Puiseux K) := ⟨ofL 0⟩
instance : One (Puiseux K) := ⟨ofL 1⟩
instance : NatCast (Puiseux K) := ⟨fun n => ofL n⟩
instance : IntCast (Puiseux K) := ⟨fun i => ofL i⟩
instance : OfNat (Puiseux K) n := ⟨ofL (OfNat.ofNat n)⟩
instance : SMul Nat (Puiseux K) := ⟨fun n x => (n : Puiseux K) * x⟩
instance : SMul Int (Puiseux K) := ⟨fun i x => (i : Puiseux K) * x⟩

/-- Natural powers by repeated multiplication. -/
def npow (x : Puiseux K) : Nat → Puiseux K
  | 0 => 1
  | n + 1 => npow x n * x

instance : HPow (Puiseux K) Nat (Puiseux K) := ⟨npow⟩

/-- Integer powers. -/
def zpow (x : Puiseux K) : Int → Puiseux K
  | .ofNat n => x ^ n
  | .negSucc n => (x ^ (n + 1))⁻¹

instance : HPow (Puiseux K) Int (Puiseux K) := ⟨zpow⟩

@[simp] theorem mk_add (N M : Nat) (hN : 0 < N) (hM : 0 < M) (x y : Laurent K) :
    mk N hN x + mk M hM y = mk (N * M) (Nat.mul_pos hN hM) (subL M x + subL N y) := rfl
@[simp] theorem mk_mul (N M : Nat) (hN : 0 < N) (hM : 0 < M) (x y : Laurent K) :
    mk N hN x * mk M hM y = mk (N * M) (Nat.mul_pos hN hM) (subL M x * subL N y) := rfl
@[simp] theorem mk_neg (N : Nat) (hN : 0 < N) (x : Laurent K) : -mk N hN x = mk N hN (-x) := rfl
@[simp] theorem mk_inv (N : Nat) (hN : 0 < N) (x : Laurent K) : (mk N hN x)⁻¹ = mk N hN x⁻¹ := rfl
theorem zero_def : (0 : Puiseux K) = mk 1 one_pos 0 := rfl
theorem one_def : (1 : Puiseux K) = mk 1 one_pos 1 := rfl

/-- Push substitutions inward, then identify the levels. -/
macro "pnorm" : tactic => `(tactic| (
  rw [mk_eq]
  try simp (disch := npos) only [subL_add, subL_mul, subL_neg, subL_inv, subL_one, subL_zero,
    subL_one_id, subL_subL]
  try simp only [Nat.mul_one, Nat.one_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  try simp only [subL_one_id]))

theorem mk_eq_zero {N : Nat} {hN : 0 < N} {x : Laurent K} : mk N hN x = 0 ↔ x = 0 := by
  rw [zero_def, mk_eq, subL_one_id, subL_zero]

instance : CommRing (Puiseux K) where
  add_zero := ind fun N hN x => by rw [zero_def, mk_add]; pnorm; grind
  add_comm := ind fun N hN x => ind fun M hM y => by simp only [mk_add]; pnorm; grind
  add_assoc := ind fun N hN x => ind fun M hM y => ind fun K hK z => by
    simp only [mk_add]; pnorm; grind
  mul_assoc := ind fun N hN x => ind fun M hM y => ind fun K hK z => by
    simp only [mk_mul]; pnorm; grind
  mul_one := ind fun N hN x => by rw [one_def, mk_mul]; pnorm; grind
  one_mul := ind fun N hN x => by rw [one_def, mk_mul]; pnorm; grind
  left_distrib := ind fun N hN x => ind fun M hM y => ind fun K hK z => by
    simp only [mk_add, mk_mul]; pnorm; grind
  right_distrib := ind fun N hN x => ind fun M hM y => ind fun K hK z => by
    simp only [mk_add, mk_mul]; pnorm; grind
  zero_mul := ind fun N hN x => by rw [zero_def, mk_mul]; pnorm; grind
  mul_zero := ind fun N hN x => by rw [zero_def, mk_mul]; pnorm; grind
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := by
    show mk 1 one_pos _ = mk 1 one_pos _ + mk 1 one_pos 1
    rw [mk_add, mk_eq]; simp only [subL_one_id, Nat.mul_one]
    exact Semiring.ofNat_succ n
  ofNat_eq_natCast n := congrArg ofL (Semiring.ofNat_eq_natCast n)
  nsmul_eq_natCast_mul _ _ := rfl
  neg_add_cancel := ind fun N hN x => by rw [mk_neg, mk_add, zero_def]; pnorm; grind
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i := ind fun N hN x => by
    show ofL _ * mk N hN x = -(ofL _ * mk N hN x)
    rw [Ring.intCast_neg]; unfold ofL; simp only [mk_mul, mk_neg]; pnorm; grind
  zsmul_natCast_eq_nsmul n x := by
    show ofL _ * x = ofL _ * x
    rw [Ring.intCast_natCast]
  intCast_ofNat n := congrArg ofL (Ring.intCast_ofNat n)
  intCast_neg i := by
    show ofL _ = -ofL _
    unfold ofL; rw [mk_neg, Ring.intCast_neg]
  mul_comm := ind fun N hN x => ind fun M hM y => by simp only [mk_mul]; pnorm; grind

instance : Field (Puiseux K) where
  div_eq_mul_inv _ _ := rfl
  zero_ne_one h := by
    rw [zero_def, one_def, mk_eq, subL_one_id, subL_one_id] at h
    exact Field.zero_ne_one h
  inv_zero := by rw [zero_def, mk_inv, Field.inv_zero]
  mul_inv_cancel {z} := by
    induction z using ind with
    | h N hN x =>
      intro hz
      have hx : x ≠ 0 := fun h => hz (mk_eq_zero.mpr h)
      have hsx : subL N x ≠ 0 := fun h => hx (subL_inj hN (by rw [h, subL_zero]))
      rw [mk_inv, mk_mul, one_def, mk_eq, subL_one_id, subL_one, subL_inv,
        Field.mul_inv_cancel hsx]
  zpow_zero _ := rfl
  zpow_succ _ _ := rfl
  zpow_neg x n := by
    match n with
    | .ofNat 0 =>
      show (1 : Puiseux K) = 1⁻¹
      rw [one_def, mk_inv, Field.inv_one]
    | .ofNat (k + 1) => rfl
    | .negSucc k =>
      show x ^ (k + 1) = ((x ^ (k + 1))⁻¹)⁻¹
      induction x ^ (k + 1) using ind with
      | h N hN y => rw [mk_inv, mk_inv, Field.inv_inv]

/-! ### The order -/

private theorem pos_congr (p q : PPair K) (h : p ≈ q) : (0 < p.val.2) = (0 < q.val.2) := by
  obtain ⟨⟨N, x⟩, hN⟩ := p; obtain ⟨⟨M, y⟩, hM⟩ := q
  have h : subL M x = subL N y := h
  apply propext
  show 0 < x ↔ 0 < y
  rw [← subL_pos hM, h, subL_pos hN]

/-- Positivity: the Laurent series at any level is positive. -/
def IsPos (z : Puiseux K) : Prop := Quotient.liftOn z (fun p => 0 < p.val.2) pos_congr

theorem isPos_mk (N : Nat) (hN : 0 < N) (x : Laurent K) : IsPos (mk N hN x) ↔ 0 < x := Iff.rfl

private theorem lmul_pos {a b : Laurent K} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have := OrderedRing.mul_lt_mul_of_pos_left hb ha; grind

private theorem isPos_add {x y : Puiseux K} (hx : IsPos x) (hy : IsPos y) : IsPos (x + y) := by
  induction x using ind with | h N hN a =>
  induction y using ind with | h M hM b =>
  rw [isPos_mk] at hx hy; rw [mk_add, isPos_mk]
  have := (subL_pos hM).mpr hx; have := (subL_pos hN).mpr hy; grind

private theorem isPos_mul {x y : Puiseux K} (hx : IsPos x) (hy : IsPos y) : IsPos (x * y) := by
  induction x using ind with | h N hN a =>
  induction y using ind with | h M hM b =>
  rw [isPos_mk] at hx hy; rw [mk_mul, isPos_mk]
  exact lmul_pos ((subL_pos hM).mpr hx) ((subL_pos hN).mpr hy)

private theorem not_isPos_both (x : Puiseux K) (h1 : IsPos x) (h2 : IsPos (-x)) : False := by
  induction x using ind with | h N hN a =>
  rw [isPos_mk] at h1; rw [mk_neg, isPos_mk] at h2; grind

private theorem isPos_tri (x : Puiseux K) : x = 0 ∨ IsPos x ∨ IsPos (-x) := by
  induction x using ind with | h N hN a =>
  rw [mk_neg, isPos_mk, isPos_mk, mk_eq_zero]
  have : a < 0 ∨ a = 0 ∨ 0 < a := by grind
  rcases this with h | h | h
  · right; right; grind
  · left; exact h
  · right; left; exact h

private theorem not_isPos_zero : ¬ IsPos (0 : Puiseux K) := by
  rw [zero_def, isPos_mk]; grind

instance : LT (Puiseux K) := ⟨fun x y => IsPos (y - x)⟩
instance : LE (Puiseux K) := ⟨fun x y => x = y ∨ x < y⟩

theorem lt_def (x y : Puiseux K) : x < y ↔ IsPos (y - x) := Iff.rfl

theorem lt_irrefl (x : Puiseux K) : ¬ x < x := by
  rw [lt_def]; have : x - x = 0 := by grind
  rw [this]; exact not_isPos_zero

theorem lt_trans {x y z : Puiseux K} (h1 : x < y) (h2 : y < z) : x < z := by
  rw [lt_def] at *; have : z - x = (z - y) + (y - x) := by grind
  rw [this]; exact isPos_add h2 h1

theorem lt_asymm {x y : Puiseux K} (h1 : x < y) (h2 : y < x) : False := by
  rw [lt_def] at *; have : x - y = -(y - x) := by grind
  rw [this] at h2; exact not_isPos_both _ h1 h2

theorem lt_trichotomy (x y : Puiseux K) : x < y ∨ x = y ∨ y < x := by
  rcases isPos_tri (y - x) with h | h | h
  · exact Or.inr (Or.inl (by grind))
  · exact Or.inl h
  · right; right; rw [lt_def]; have : x - y = -(y - x) := by grind
    rw [this]; exact h

instance : Std.IsLinearOrder (Puiseux K) where
  le_refl _ := Or.inl rfl
  le_trans _ _ _ h1 h2 := by
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · exact Or.inl rfl
    · exact Or.inr h2
    · exact Or.inr h1
    · exact Or.inr (lt_trans h1 h2)
  le_antisymm _ _ h1 h2 := by
    rcases h1 with h1 | h1
    · exact h1
    · rcases h2 with h2 | h2
      · exact h2.symm
      · exact (lt_asymm h1 h2).elim
  le_total x y := by
    rcases lt_trichotomy x y with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)

instance : Std.LawfulOrderLT (Puiseux K) where
  lt_iff x y := by
    constructor
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (h' | h')
      · subst h'; exact lt_irrefl _ h
      · exact lt_asymm h h'
    · rintro ⟨h1 | h1, h2⟩
      · subst h1; exact (h2 (Or.inl rfl)).elim
      · exact h1

instance : OrderedAdd (Puiseux K) where
  add_le_left_iff {a b} c := by
    have key : b + c - (a + c) = b - a := by grind
    constructor
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr (by rw [lt_def, key]; exact h)
    · rintro (h | h)
      · left; have : a = a + c - c := by grind
        rw [this, h]; grind
      · exact Or.inr (by rw [lt_def, ← key]; exact h)

instance : OrderedRing (Puiseux K) where
  zero_lt_one := by
    rw [lt_def]; have : (1 : Puiseux K) - 0 = 1 := by grind
    rw [this, one_def, isPos_mk]
    exact OrderedRing.zero_lt_one
  mul_lt_mul_of_pos_left {a b c} h hc := by
    rw [lt_def] at *; have : c * b - c * a = (c - 0) * (b - a) := by grind
    rw [this]; exact isPos_mul hc h
  mul_lt_mul_of_pos_right {a b c} h hc := by
    rw [lt_def] at *; have : b * c - a * c = (b - a) * (c - 0) := by grind
    rw [this]; exact isPos_mul h hc

/-! ### Laurent series embed, and `ε` has every root -/

theorem ofL_add (x y : Laurent K) : ofL (x + y) = ofL x + ofL y := by
  unfold ofL; rw [mk_add]; pnorm
theorem ofL_mul (x y : Laurent K) : ofL (x * y) = ofL x * ofL y := by
  unfold ofL; rw [mk_mul]; pnorm
theorem ofL_neg (x : Laurent K) : ofL (-x) = -ofL x := rfl

theorem ofL_lt {x y : Laurent K} : ofL x < ofL y ↔ x < y := by
  have : ofL y - ofL x = ofL (y - x) := by
    show ofL y + -ofL x = ofL (y + -x); rw [ofL_add, ofL_neg]
  rw [lt_def, this]; unfold ofL; rw [isPos_mk]
  constructor <;> intro h <;> grind

/-- `x ↦ x(ε^{1/N})` is a ring map. -/
private theorem mk_mul_same (N : Nat) (hN : 0 < N) (x y : Laurent K) :
    mk N hN (x * y) = mk N hN x * mk N hN y := by rw [mk_mul]; pnorm

theorem mk_pow (N : Nat) (hN : 0 < N) (x : Laurent K) (n : Nat) :
    mk N hN (x ^ n) = mk N hN x ^ n := by
  induction n with
  | zero => show mk N hN 1 = mk 1 one_pos 1; pnorm
  | succ n ih =>
    show mk N hN (x ^ n * x) = mk N hN x ^ n * mk N hN x
    rw [mk_mul_same, ih]

/-- The infinitesimal `ε`. -/
def eps : Puiseux K := ofL Laurent.eps
/-- A coefficient, as a constant series. -/
def ofK (q : K) : Puiseux K := ofL (Laurent.ofK q)

/-- `ε^{1/N}`. -/
def root (N : Nat) (hN : 0 < N) : Puiseux K := mk N hN Laurent.eps

private theorem ofRing_pow (a : PS K) (n : Nat) : (ofRing a : Laurent K) ^ n = ofRing (a ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ofRing a ^ n * ofRing a = ofRing (a ^ n * a)
    rw [ih, ← ofRing_mul]

/-- `(ε^{1/N})^N = ε`. -/
theorem root_pow (N : Nat) (hN : 0 < N) : (root N hN : Puiseux K) ^ N = eps := by
  unfold root eps ofL
  rw [← mk_pow, mk_eq, subL_one_id]
  unfold Laurent.eps
  rw [ofRing_pow, subL_ofRing N hN, sub_X hN]

theorem root_pos (N : Nat) (hN : 0 < N) : 0 < (root N hN : Puiseux K) := by
  rw [lt_def]; have : (root N hN : Puiseux K) - 0 = root N hN := by grind
  rw [this]; unfold root; rw [isPos_mk]; exact Laurent.eps_pos

/-- `ε^{1/N}` is infinitesimal: below every positive element of `K`. -/
theorem root_lt_ofK (N : Nat) (hN : 0 < N) {q : K} (hq : 0 < q) : root N hN < ofK q := by
  rw [lt_def]
  show IsPos (mk 1 one_pos (Laurent.ofK q) + -mk N hN Laurent.eps)
  rw [mk_neg, mk_add, isPos_mk, subL_one_id]
  have hc : subL N (Laurent.ofK q) = Laurent.ofK q := by
    unfold Laurent.ofK; rw [subL_ofRing N hN, sub_C hN]
  rw [hc]
  have := Laurent.eps_lt_ofK hq
  grind

theorem eps_pos : 0 < (eps : Puiseux K) := ofL_lt.mpr Laurent.eps_pos

/-- `grind` reasons in the Puiseux field. -/
example (x : Puiseux K) (hx : x ≠ 0) : x * x⁻¹ = 1 := by grind
example (N : Nat) (hN : 0 < N) : (root N hN : Puiseux K)⁻¹ * root N hN = 1 := by
  have := root_pos (K := K) N hN; grind

end

end Puiseux

end LeviCivita.Series
