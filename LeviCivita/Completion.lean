import LeviCivita.Puiseux

/-!
# The Cauchy completion of an ordered field, and the Levi-Civita field

`Completion F` is the field of Cauchy sequences in a linearly ordered field `F`
modulo null sequences, where "Cauchy" is measured by the order of `F` itself:
`∀ δ > 0` in `F`, eventually `|sₘ − sₙ| < δ`. It is again a linearly ordered
field, and `F` embeds in it as an ordered subfield. Everything is generic and
proved without `sorry`.

Applied to the Puiseux field, this gives `LeviCivitaFieldOver K := Completion (Puiseux K)`
(and `LeviCivitaField := LeviCivitaFieldOver ℚ`).
In the Puiseux field the order topology is the valuation topology (the powers
`εⁿ` are cofinal among positive elements), and the Puiseux series are dense in
the Levi-Civita field (truncations converge). So this completion is the
Levi-Civita field over `K`: series `Σ aᵢ ε^{qᵢ}` with left-finite rational
support, unbounded denominators allowed.

The Levi-Civita field is real closed only when its coefficient field is. With
rational coefficients it is not: `x² = 2` has no solution. Real-closedness
would need real (or real-algebraic) coefficients.
-/

namespace LeviCivita.Cauchy

open Lean.Grind Classical

variable {F : Type u} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F]
  [OrderedRing F]

/-- `|a − b| < d`. -/
def Near (a b d : F) : Prop := a - b < d ∧ b - a < d

omit [LE F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F] in
theorem near_symm {a b d : F} (h : Near a b d) : Near b a d := ⟨h.2, h.1⟩

theorem near_trans {a b c d e : F} (h1 : Near a b d) (h2 : Near b c e) : Near a c (d + e) := by
  obtain ⟨h1, h1'⟩ := h1; obtain ⟨h2, h2'⟩ := h2; constructor <;> grind

theorem near_mono {a b d e : F} (h : Near a b d) (hde : d ≤ e) : Near a b e := by
  obtain ⟨h1, h2⟩ := h; constructor <;> grind

theorem near_add {a b c d δ η : F} (h1 : Near a b δ) (h2 : Near c d η) :
    Near (a + c) (b + d) (δ + η) := by
  obtain ⟨h1, h1'⟩ := h1; obtain ⟨h2, h2'⟩ := h2; constructor <;> grind

/-- `|x| < A`, `|y| < B` ⇒ `|xy| < AB`. -/
theorem near_mul {x y A B : F} (hx : Near x 0 A) (hy : Near y 0 B) : Near (x * y) 0 (A * B) := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  have hA : 0 < A := by grind
  have hB : 0 < B := by grind
  -- reduce to `0 ≤ x' < A`, `0 ≤ y' < B` with `xy = ±x'y'`
  have key : ∀ x' y' : F, 0 ≤ x' → x' < A → 0 ≤ y' → y' < B → x' * y' < A * B := by
    intro x' y' h1 h2 h3 h4
    have : x' * y' ≤ x' * B := OrderedRing.mul_le_mul_of_nonneg_left (by grind) h1
    have : x' * B < A * B := OrderedRing.mul_lt_mul_of_pos_right h2 hB
    grind
  have hxy : 0 ≤ x * y ∨ x * y ≤ 0 := by grind
  have sx : 0 ≤ x ∨ x < 0 := by grind
  have sy : 0 ≤ y ∨ y < 0 := by grind
  have k1 := key x y; have k2 := key (-x) y; have k3 := key x (-y); have k4 := key (-x) (-y)
  have e2 : -x * y = -(x * y) := by grind
  have e3 : x * -y = -(x * y) := by grind
  have e4 : -x * -y = x * y := by grind
  have p1 : 0 ≤ x → 0 ≤ y → 0 ≤ x * y := fun a b => OrderedRing.mul_nonneg a b
  have p2 : x < 0 → y < 0 → 0 ≤ x * y := fun a b => by
    have := OrderedRing.mul_pos_of_neg_of_neg a b; grind
  have p3 : 0 ≤ x → y < 0 → x * y ≤ 0 := fun a b => OrderedRing.mul_nonpos_of_nonneg_of_nonpos a (by grind)
  have p4 : x < 0 → 0 ≤ y → x * y ≤ 0 := fun a b => OrderedRing.mul_nonpos_of_nonpos_of_nonneg (by grind) b
  constructor <;> rcases sx with sx | sx <;> rcases sy with sy | sy <;> grind

/-- For `d, B > 0` there is `h > 0` with `B · h < d`. -/
theorem exists_mul_lt {d B : F} (hd : 0 < d) (hB : 0 < B) : ∃ h, 0 < h ∧ B * h < d := by
  have hB1 : 0 < B + 1 := by grind
  refine ⟨d * (B + 1)⁻¹, OrderedRing.mul_pos hd (Field.IsOrdered.inv_pos_iff.mpr hB1), ?_⟩
  have : B * (d * (B + 1)⁻¹) = (B * d) * (B + 1)⁻¹ := by grind
  rw [this, Field.IsOrdered.mul_inv_lt_iff_lt_mul _ _ hB1]
  grind

/-! ## Cauchy sequences -/

def IsCauchy (s : Nat → F) : Prop :=
  ∀ d, 0 < d → ∃ N, ∀ m n, N ≤ m → N ≤ n → Near (s m) (s n) d

/-- Sequences that agree in the limit. -/
def Equiv (s t : Nat → F) : Prop := ∀ d, 0 < d → ∃ N, ∀ n, N ≤ n → Near (s n) (t n) d

theorem equiv_refl (s : Nat → F) : Equiv s s := fun d hd => ⟨0, fun n _ => by
  constructor <;> grind⟩

omit [LE F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F] [OrderedRing F] in
theorem equiv_symm {s t : Nat → F} (h : Equiv s t) : Equiv t s := fun d hd => by
  obtain ⟨N, hN⟩ := h d hd; exact ⟨N, fun n hn => near_symm (hN n hn)⟩

theorem equiv_trans {s t u : Nat → F} (h1 : Equiv s t) (h2 : Equiv t u) : Equiv s u := fun d hd => by
  obtain ⟨N1, h1⟩ := h1 (d / 2) (by grind)
  obtain ⟨N2, h2⟩ := h2 (d / 2) (by grind)
  exact ⟨max N1 N2, fun n hn => near_mono (near_trans (h1 n (by omega)) (h2 n (by omega)))
    (by grind)⟩

theorem cauchy_const (c : F) : IsCauchy (fun _ => c) := fun d hd => ⟨0, fun _ _ _ _ => by
  constructor <;> grind⟩

theorem cauchy_add {s t : Nat → F} (hs : IsCauchy s) (ht : IsCauchy t) :
    IsCauchy (fun n => s n + t n) := fun d hd => by
  obtain ⟨N1, h1⟩ := hs (d / 2) (by grind)
  obtain ⟨N2, h2⟩ := ht (d / 2) (by grind)
  exact ⟨max N1 N2, fun m n hm hn => near_mono
    (near_add (h1 m n (by omega) (by omega)) (h2 m n (by omega) (by omega))) (by grind)⟩

theorem cauchy_neg {s : Nat → F} (hs : IsCauchy s) : IsCauchy (fun n => -s n) := fun d hd => by
  obtain ⟨N, h⟩ := hs d hd
  exact ⟨N, fun m n hm hn => by obtain ⟨a, b⟩ := h m n hm hn; constructor <;> grind⟩

/-- Cauchy sequences are bounded. -/
theorem cauchy_bounded {s : Nat → F} (hs : IsCauchy s) : ∃ B, 0 < B ∧ ∀ n, Near (s n) 0 B := by
  obtain ⟨N, hN⟩ := hs 1 OrderedRing.zero_lt_one
  -- a bound for the first `N + 1` terms, by recursion
  have : ∀ K, ∃ B, 0 < B ∧ ∀ n, n ≤ K → Near (s n) 0 B := by
    intro K
    induction K with
    | zero =>
      refine ⟨(if s 0 < 0 then -s 0 else s 0) + 1, by split <;> grind, fun n hn => ?_⟩
      have : n = 0 := by omega
      subst this; constructor <;> split <;> grind
    | succ K ih =>
      obtain ⟨B, hB, hb⟩ := ih
      let c := (if s (K + 1) < 0 then -s (K + 1) else s (K + 1)) + 1
      have hc : Near (s (K + 1)) 0 c := by constructor <;> simp only [c] <;> split <;> grind
      refine ⟨B + c, by simp only [c]; split <;> grind, fun n hn => ?_⟩
      rcases Nat.lt_or_ge n (K + 1) with h | h
      · exact near_mono (hb n (by omega)) (by simp only [c]; split <;> grind)
      · have : n = K + 1 := by omega
        subst this; exact near_mono hc (by grind)
  obtain ⟨B, hB, hb⟩ := this N
  refine ⟨B + 1, by grind, fun n => ?_⟩
  rcases Nat.lt_or_ge n N with h | h
  · exact near_mono (hb n (by omega)) (by grind)
  · have := near_trans (hN n N h (Nat.le_refl _)) (hb N (Nat.le_refl _))
    exact near_mono this (by grind)

theorem cauchy_mul {s t : Nat → F} (hs : IsCauchy s) (ht : IsCauchy t) :
    IsCauchy (fun n => s n * t n) := fun d hd => by
  obtain ⟨A, hA, hAs⟩ := cauchy_bounded hs
  obtain ⟨B, hB, hBt⟩ := cauchy_bounded ht
  obtain ⟨h, hh, hlt⟩ := exists_mul_lt hd (by grind : 0 < A + B)
  obtain ⟨N1, h1⟩ := hs h hh
  obtain ⟨N2, h2⟩ := ht h hh
  refine ⟨max N1 N2, fun m n hm hn => ?_⟩
  -- sₘtₘ − sₙtₙ = sₘ(tₘ − tₙ) + tₙ(sₘ − sₙ)
  have a1 : Near (t m - t n) 0 h := by
    obtain ⟨u, v⟩ := h2 m n (by omega) (by omega); constructor <;> grind
  have a2 : Near (s m - s n) 0 h := by
    obtain ⟨u, v⟩ := h1 m n (by omega) (by omega); constructor <;> grind
  have b1 := near_mul (hAs m) a1
  have b2 := near_mul (hBt n) a2
  have := near_add b1 b2
  have e : s m * (t m - t n) + t n * (s m - s n) = s m * t m - s n * t n := by grind
  obtain ⟨u, v⟩ := this
  constructor <;> grind

theorem equiv_add {s t s' t' : Nat → F} (h1 : Equiv s s') (h2 : Equiv t t') :
    Equiv (fun n => s n + t n) (fun n => s' n + t' n) := fun d hd => by
  obtain ⟨N1, h1⟩ := h1 (d / 2) (by grind)
  obtain ⟨N2, h2⟩ := h2 (d / 2) (by grind)
  exact ⟨max N1 N2, fun n hn => near_mono (near_add (h1 n (by omega)) (h2 n (by omega)))
    (by grind)⟩

theorem equiv_neg {s s' : Nat → F} (h : Equiv s s') : Equiv (fun n => -s n) (fun n => -s' n) :=
  fun d hd => by
    obtain ⟨N, h⟩ := h d hd
    exact ⟨N, fun n hn => by obtain ⟨a, b⟩ := h n hn; constructor <;> grind⟩

theorem equiv_mul {s t s' t' : Nat → F} (hs : IsCauchy s) (ht' : IsCauchy t')
    (h1 : Equiv s s') (h2 : Equiv t t') :
    Equiv (fun n => s n * t n) (fun n => s' n * t' n) := fun d hd => by
  obtain ⟨A, hA, hAs⟩ := cauchy_bounded hs
  obtain ⟨B, hB, hBt⟩ := cauchy_bounded ht'
  obtain ⟨h, hh, hlt⟩ := exists_mul_lt hd (by grind : 0 < A + B)
  obtain ⟨N1, h1⟩ := h1 h hh
  obtain ⟨N2, h2⟩ := h2 h hh
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have a1 : Near (t n - t' n) 0 h := by
    obtain ⟨u, v⟩ := h2 n (by omega); constructor <;> grind
  have a2 : Near (s n - s' n) 0 h := by
    obtain ⟨u, v⟩ := h1 n (by omega); constructor <;> grind
  have := near_add (near_mul (hAs n) a1) (near_mul (hBt n) a2)
  have e : s n * (t n - t' n) + t' n * (s n - s' n) = s n * t n - s' n * t' n := by grind
  obtain ⟨u, v⟩ := this
  constructor <;> grind

/-! ### Bounded away from zero -/

/-- A Cauchy sequence that is not null is eventually beyond `±η`. -/
theorem away {s : Nat → F} (hs : IsCauchy s) (h : ¬ Equiv s (fun _ => 0)) :
    ∃ η, 0 < η ∧ ∃ N, (∀ n, N ≤ n → η < s n) ∨ (∀ n, N ≤ n → s n < -η) := by
  have : ∃ d, 0 < d ∧ ∀ N, ∃ n, N ≤ n ∧ ¬ Near (s n) 0 d := by
    apply Classical.byContradiction; intro hc
    apply h; intro d hd
    apply Classical.byContradiction; intro hN
    apply hc; refine ⟨d, hd, fun N => ?_⟩
    apply Classical.byContradiction; intro hn
    exact hN ⟨N, fun n hNn => Classical.byContradiction fun h' => hn ⟨n, hNn, h'⟩⟩
  obtain ⟨d, hd, hfar⟩ := this
  obtain ⟨N, hN⟩ := hs (d / 2) (by grind)
  obtain ⟨n0, hn0, hfar0⟩ := hfar N
  refine ⟨d / 2, by grind, N, ?_⟩
  simp only [Near] at hfar0
  have : d ≤ s n0 ∨ s n0 ≤ -d := by grind
  rcases this with hp | hn
  · left; intro n hn; obtain ⟨u, v⟩ := hN n n0 hn hn0; grind
  · right; intro n hn; obtain ⟨u, v⟩ := hN n n0 hn hn0; grind

/-- The inverse sequence, for one bounded away from zero on the positive side. -/
theorem cauchy_inv_pos {s : Nat → F} (hs : IsCauchy s) {η : F} (hη : 0 < η) {N : Nat}
    (hN : ∀ n, N ≤ n → η < s n) : IsCauchy (fun n => (s n)⁻¹) := fun d hd => by
  have hη2 : 0 < η * η := OrderedRing.mul_pos hη hη
  obtain ⟨M, hM⟩ := hs (d * (η * η)) (OrderedRing.mul_pos hd hη2)
  refine ⟨max N M, fun m n hm hn => ?_⟩
  have hsm := hN m (by omega); have hsn := hN n (by omega)
  have hm0 : s m ≠ 0 := by grind
  have hn0 : s n ≠ 0 := by grind
  have hP : η * η < s m * s n := by
    have : η * η < s m * η := OrderedRing.mul_lt_mul_of_pos_right hsm hη
    have : s m * η < s m * s n := OrderedRing.mul_lt_mul_of_pos_left hsn (by grind)
    grind
  have hP0 : 0 < s m * s n := by grind
  have e1 : (s m)⁻¹ - (s n)⁻¹ = (s n - s m) * (s m * s n)⁻¹ := by grind
  have e2 : (s n)⁻¹ - (s m)⁻¹ = (s m - s n) * (s m * s n)⁻¹ := by grind
  obtain ⟨u, v⟩ := hM m n (by omega) (by omega)
  have hdP : d * (η * η) < d * (s m * s n) := OrderedRing.mul_lt_mul_of_pos_left hP hd
  constructor
  · rw [e1, Field.IsOrdered.mul_inv_lt_iff_lt_mul _ _ hP0]; grind
  · rw [e2, Field.IsOrdered.mul_inv_lt_iff_lt_mul _ _ hP0]; grind

theorem cauchy_inv {s : Nat → F} (hs : IsCauchy s) (h : ¬ Equiv s (fun _ => 0)) :
    IsCauchy (fun n => (s n)⁻¹) := by
  obtain ⟨η, hη, N, hpos | hneg⟩ := away hs h
  · exact cauchy_inv_pos hs hη hpos
  · have := cauchy_inv_pos (cauchy_neg hs) hη (N := N) (fun n hn => by have := hneg n hn; grind)
    have := cauchy_neg this
    intro d hd; obtain ⟨K, hK⟩ := this d hd
    exact ⟨K, fun m n hm hn => by
      have e : ∀ k, -(-s k)⁻¹ = (s k)⁻¹ := fun k => by rw [Field.inv_neg]; grind
      have := hK m n hm hn; simp only [e] at this; exact this⟩

theorem equiv_zero_iff {s t : Nat → F} (h : Equiv s t) :
    Equiv s (fun _ => 0) ↔ Equiv t (fun _ => 0) :=
  ⟨fun hs => equiv_trans (equiv_symm h) hs, fun ht => equiv_trans h ht⟩

theorem equiv_inv {s t : Nat → F} (hs : IsCauchy s) (ht : IsCauchy t) (h : Equiv s t)
    (h0 : ¬ Equiv s (fun _ => 0)) : Equiv (fun n => (s n)⁻¹) (fun n => (t n)⁻¹) := by
  have h0' : ¬ Equiv t (fun _ => 0) := fun h' => h0 ((equiv_zero_iff h).mpr h')
  -- `1/s − 1/t = (t − s) · (1/s) · (1/t)`, and `1/s`, `1/t` are bounded
  obtain ⟨A, hA, hAs⟩ := cauchy_bounded (cauchy_inv hs h0)
  obtain ⟨B, hB, hBt⟩ := cauchy_bounded (cauchy_inv ht h0')
  obtain ⟨η, hη, N, hsign⟩ := away hs h0
  intro d hd
  obtain ⟨k, hk, hlt⟩ := exists_mul_lt hd (OrderedRing.mul_pos hA hB)
  obtain ⟨M, hM⟩ := h k hk
  obtain ⟨η', hη', N', hsign'⟩ := away ht h0'
  refine ⟨max (max N N') M, fun n hn => ?_⟩
  have hs0 : s n ≠ 0 := by rcases hsign with p | p <;> have := p n (by omega) <;> grind
  have ht0 : t n ≠ 0 := by rcases hsign' with p | p <;> have := p n (by omega) <;> grind
  have e : (s n)⁻¹ - (t n)⁻¹ = (t n - s n) * ((s n)⁻¹ * (t n)⁻¹) := by grind
  have a : Near (t n - s n) 0 k := by obtain ⟨u, v⟩ := hM n (by omega); constructor <;> grind
  have := near_mul a (near_mul (hAs n) (hBt n))
  obtain ⟨u, v⟩ := this
  have : k * (A * B) = A * B * k := by grind
  constructor <;> grind

/-! ## The completion -/

/-- Cauchy sequences. -/
def CSeq (F : Type u) [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F]
    [OrderedRing F] := { s : Nat → F // IsCauchy s }

instance cauchySetoid (F : Type u) [Field F] [LE F] [LT F] [Std.IsLinearOrder F]
    [Std.LawfulOrderLT F] [OrderedRing F] : Setoid (CSeq F) :=
  ⟨fun s t => Equiv s.val t.val, ⟨fun s => equiv_refl s.val, equiv_symm, equiv_trans⟩⟩

end Cauchy

open Cauchy in
/-- The Cauchy completion of an ordered field. -/
def Completion (F : Type u) [Lean.Grind.Field F] [LE F] [LT F] [Std.IsLinearOrder F]
    [Std.LawfulOrderLT F] [Lean.Grind.OrderedRing F] := Quotient (cauchySetoid F)

namespace Completion

open Cauchy Lean.Grind Classical

attribute [local instance] Semiring.natCast Ring.intCast

variable {F : Type u} [Field F] [LE F] [LT F] [Std.IsLinearOrder F] [Std.LawfulOrderLT F]
  [OrderedRing F]

/-- The class of a Cauchy sequence. -/
def mk (s : Nat → F) (hs : IsCauchy s) : Completion F := Quotient.mk _ ⟨s, hs⟩

theorem mk_eq {s t : Nat → F} {hs : IsCauchy s} {ht : IsCauchy t} :
    mk s hs = mk t ht ↔ Equiv s t := ⟨Quotient.exact, fun h => Quotient.sound h⟩

theorem ind {P : Completion F → Prop} (h : ∀ s hs, P (mk s hs)) (x : Completion F) : P x :=
  Quotient.ind (fun ⟨s, hs⟩ => h s hs) x

/-- The constant sequence: the embedding `F → Completion F`. -/
def const (c : F) : Completion F := mk (fun _ => c) (cauchy_const c)


instance : Add (Completion F) := ⟨Quotient.lift₂
  (fun s t => mk (fun n => s.val n + t.val n) (cauchy_add s.property t.property))
  (fun _ _ _ _ h1 h2 => Quotient.sound (equiv_add h1 h2))⟩

instance : Neg (Completion F) := ⟨Quotient.lift
  (fun s => mk (fun n => -s.val n) (cauchy_neg s.property))
  (fun _ _ h => Quotient.sound (equiv_neg h))⟩

instance : Mul (Completion F) := ⟨Quotient.lift₂
  (fun s t => mk (fun n => s.val n * t.val n) (cauchy_mul s.property t.property))
  (fun s _ _ t' h1 h2 => Quotient.sound (equiv_mul s.property t'.property h1 h2))⟩

private noncomputable def invSeq (s : CSeq F) : CSeq F :=
  if h : Equiv s.val (fun _ => 0) then ⟨fun _ => 0, cauchy_const 0⟩
  else ⟨fun n => (s.val n)⁻¹, cauchy_inv s.property h⟩

private theorem invSeq_congr (s t : CSeq F) (h : s ≈ t) :
    (Quotient.mk _ (invSeq s) : Completion F) = Quotient.mk _ (invSeq t) := by
  have h : Equiv s.val t.val := h
  apply Quotient.sound
  unfold invSeq
  by_cases hs : Equiv s.val (fun _ => 0)
  · have ht := (equiv_zero_iff h).mp hs
    simp only [hs, ht, ↓reduceDIte]; exact equiv_refl _
  · have ht : ¬ Equiv t.val (fun _ => 0) := fun ht => hs ((equiv_zero_iff h).mpr ht)
    simp only [hs, ht, ↓reduceDIte]
    exact equiv_inv s.property t.property h hs

noncomputable instance : Inv (Completion F) := ⟨Quotient.lift
  (fun s => Quotient.mk _ (invSeq s)) invSeq_congr⟩

instance : Sub (Completion F) := ⟨fun x y => x + -y⟩
noncomputable instance : Div (Completion F) := ⟨fun x y => x * y⁻¹⟩
instance : OfNat (Completion F) n := ⟨const (OfNat.ofNat n)⟩
instance : NatCast (Completion F) := ⟨fun n => const n⟩
instance : IntCast (Completion F) := ⟨fun i => const i⟩
instance : SMul Nat (Completion F) := ⟨fun n x => (n : Completion F) * x⟩
instance : SMul Int (Completion F) := ⟨fun i x => (i : Completion F) * x⟩

/-- Natural powers. -/
def npow (x : Completion F) : Nat → Completion F
  | 0 => 1
  | n + 1 => npow x n * x

instance : HPow (Completion F) Nat (Completion F) := ⟨npow⟩

/-- Integer powers. -/
noncomputable def zpow (x : Completion F) : Int → Completion F
  | .ofNat n => x ^ n
  | .negSucc n => (x ^ (n + 1))⁻¹

noncomputable instance : HPow (Completion F) Int (Completion F) := ⟨zpow⟩

@[simp] theorem mk_add (s t : Nat → F) (hs : IsCauchy s) (ht : IsCauchy t) :
    mk s hs + mk t ht = mk (fun n => s n + t n) (cauchy_add hs ht) := rfl
@[simp] theorem mk_mul (s t : Nat → F) (hs : IsCauchy s) (ht : IsCauchy t) :
    mk s hs * mk t ht = mk (fun n => s n * t n) (cauchy_mul hs ht) := rfl
@[simp] theorem mk_neg (s : Nat → F) (hs : IsCauchy s) :
    -mk s hs = mk (fun n => -s n) (cauchy_neg hs) := rfl
theorem zero_def : (0 : Completion F) = const 0 := rfl
theorem one_def : (1 : Completion F) = const 1 := rfl

/-- Pointwise equal sequences are equal in the completion. -/
theorem mk_congr {s t : Nat → F} {hs : IsCauchy s} {ht : IsCauchy t} (h : ∀ n, s n = t n) :
    mk s hs = mk t ht := by
  have : s = t := funext h
  subst this; rfl

macro "cpoint" : tactic => `(tactic| (apply mk_congr; intro n; grind))

theorem const_add (a b : F) : const (a + b) = const a + const b := by
  unfold const; rw [mk_add]
theorem const_mul (a b : F) : const (a * b) = const a * const b := by
  unfold const; rw [mk_mul]
theorem const_neg (a : F) : const (-a) = -const a := by
  unfold const; rw [mk_neg]

instance : CommRing (Completion F) where
  add_zero := ind fun s hs => by rw [zero_def, const, mk_add]; cpoint
  add_comm := ind fun s hs => ind fun t ht => by simp only [mk_add]; cpoint
  add_assoc := ind fun s hs => ind fun t ht => ind fun u hu => by simp only [mk_add]; cpoint
  mul_assoc := ind fun s hs => ind fun t ht => ind fun u hu => by simp only [mk_mul]; cpoint
  mul_one := ind fun s hs => by rw [one_def, const, mk_mul]; cpoint
  one_mul := ind fun s hs => by rw [one_def, const, mk_mul]; cpoint
  left_distrib := ind fun s hs => ind fun t ht => ind fun u hu => by
    simp only [mk_add, mk_mul]; cpoint
  right_distrib := ind fun s hs => ind fun t ht => ind fun u hu => by
    simp only [mk_add, mk_mul]; cpoint
  zero_mul := ind fun s hs => by rw [zero_def, const, mk_mul]; cpoint
  mul_zero := ind fun s hs => by rw [zero_def, const, mk_mul]; cpoint
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := by
    show const _ = const _ + const 1
    rw [← const_add, Semiring.ofNat_succ]
  ofNat_eq_natCast n := congrArg const (Semiring.ofNat_eq_natCast n)
  nsmul_eq_natCast_mul _ _ := rfl
  neg_add_cancel := ind fun s hs => by rw [mk_neg, mk_add, zero_def, const]; cpoint
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i := ind fun s hs => by
    show const _ * mk s hs = -(const _ * mk s hs)
    rw [Ring.intCast_neg]; unfold const; simp only [mk_mul, mk_neg]; cpoint
  zsmul_natCast_eq_nsmul n x := by
    show const _ * x = const _ * x
    rw [Ring.intCast_natCast]
  intCast_ofNat n := congrArg const (Ring.intCast_ofNat n)
  intCast_neg i := by
    show const _ = -const _
    rw [Ring.intCast_neg, const_neg]
  mul_comm := ind fun s hs => ind fun t ht => by simp only [mk_mul]; cpoint

theorem mk_eq_zero {s : Nat → F} {hs : IsCauchy s} : mk s hs = 0 ↔ Equiv s (fun _ => 0) := by
  rw [zero_def, const, mk_eq]

theorem mk_inv_of_not {s : Nat → F} {hs : IsCauchy s} (h : ¬ Equiv s (fun _ => 0)) :
    (mk s hs)⁻¹ = mk (fun n => (s n)⁻¹) (cauchy_inv hs h) := by
  show Quotient.mk _ (invSeq ⟨s, hs⟩) = _
  unfold invSeq; simp only [h, ↓reduceDIte]; rfl

theorem mk_inv_of_null {s : Nat → F} {hs : IsCauchy s} (h : Equiv s (fun _ => 0)) :
    (mk s hs)⁻¹ = 0 := by
  show Quotient.mk _ (invSeq ⟨s, hs⟩) = _
  unfold invSeq; simp only [h, ↓reduceDIte]; rfl

private theorem not_null_one : ¬ Equiv (fun _ => (1 : F)) (fun _ => 0) := fun h => by
  obtain ⟨N, hN⟩ := h 1 OrderedRing.zero_lt_one
  obtain ⟨u, v⟩ := hN N (Nat.le_refl _); grind

theorem zero_ne_one' : (0 : Completion F) ≠ 1 := fun h => by
  rw [zero_def, one_def, const, const, mk_eq] at h
  exact not_null_one (equiv_symm h)

theorem inv_zero' : (0 : Completion F)⁻¹ = 0 := by
  rw [zero_def, const, mk_inv_of_null (equiv_refl _)]; rfl

theorem mul_inv_cancel' {x : Completion F} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  induction x using ind with
  | h s hs =>
    have h0 : ¬ Equiv s (fun _ => 0) := fun h => hx (mk_eq_zero.mpr h)
    rw [mk_inv_of_not h0, mk_mul, one_def, const, mk_eq]
    obtain ⟨η, hη, N, hsign⟩ := away hs h0
    intro d hd
    refine ⟨N, fun n hn => ?_⟩
    have : s n ≠ 0 := by rcases hsign with p | p <;> have := p n hn <;> grind
    have e : s n * (s n)⁻¹ = 1 := Field.mul_inv_cancel this
    simp only [Near, e]; constructor <;> grind

theorem inv_one' : (1 : Completion F)⁻¹ = 1 := by
  rw [one_def, const, mk_inv_of_not not_null_one]
  apply mk_congr; intro n; rw [Field.inv_one]

theorem inv_inv' (x : Completion F) : x⁻¹⁻¹ = x := by
  by_cases hx : x = 0
  · subst hx; rw [inv_zero', inv_zero']
  · have h1 := mul_inv_cancel' hx
    have hx' : x⁻¹ ≠ 0 := fun h => by
      rw [h] at h1; exact zero_ne_one' (F := F) (by rw [← h1]; grind)
    have h2 := mul_inv_cancel' hx'
    calc x⁻¹⁻¹ = (x * x⁻¹) * x⁻¹⁻¹ := by rw [h1]; grind
      _ = x * (x⁻¹ * x⁻¹⁻¹) := by grind
      _ = x := by rw [h2]; grind

noncomputable instance : Field (Completion F) where
  div_eq_mul_inv _ _ := rfl
  zero_ne_one := zero_ne_one'
  inv_zero := inv_zero'
  mul_inv_cancel := mul_inv_cancel'
  zpow_zero _ := rfl
  zpow_succ _ _ := rfl
  zpow_neg x n := by
    match n with
    | .ofNat 0 => exact inv_one'.symm
    | .ofNat (k + 1) => rfl
    | .negSucc k => exact (inv_inv' _).symm

/-! ### The order -/

/-- Eventually above a positive bound. -/
def PosSeq (s : Nat → F) : Prop := ∃ η, 0 < η ∧ ∃ N, ∀ n, N ≤ n → η < s n

private theorem posSeq_congr {s t : Nat → F} (h : Equiv s t) (hs : PosSeq s) : PosSeq t := by
  obtain ⟨η, hη, N, hN⟩ := hs
  obtain ⟨M, hM⟩ := h (η / 2) (by grind)
  exact ⟨η / 2, by grind, max N M, fun n hn => by
    have := hN n (by omega); obtain ⟨u, v⟩ := hM n (by omega); grind⟩

/-- Positivity in the completion. -/
def IsPos (x : Completion F) : Prop :=
  Quotient.liftOn x (fun s => PosSeq s.val) (fun _ _ h =>
    propext ⟨posSeq_congr h, posSeq_congr (equiv_symm h)⟩)

theorem isPos_mk (s : Nat → F) (hs : IsCauchy s) : IsPos (mk s hs) ↔ PosSeq s := Iff.rfl

private theorem isPos_add {x y : Completion F} (hx : IsPos x) (hy : IsPos y) : IsPos (x + y) := by
  induction x using ind with | h s hs =>
  induction y using ind with | h t ht =>
  rw [isPos_mk] at hx hy; rw [mk_add, isPos_mk]
  obtain ⟨a, ha, N, hN⟩ := hx; obtain ⟨b, hb, M, hM⟩ := hy
  exact ⟨a + b, by grind, max N M, fun n hn => by
    have := hN n (by omega); have := hM n (by omega); grind⟩

private theorem isPos_mul {x y : Completion F} (hx : IsPos x) (hy : IsPos y) : IsPos (x * y) := by
  induction x using ind with | h s hs =>
  induction y using ind with | h t ht =>
  rw [isPos_mk] at hx hy; rw [mk_mul, isPos_mk]
  obtain ⟨a, ha, N, hN⟩ := hx; obtain ⟨b, hb, M, hM⟩ := hy
  refine ⟨a * b, OrderedRing.mul_pos ha hb, max N M, fun n hn => ?_⟩
  have h1 := hN n (by omega); have h2 := hM n (by omega)
  have : a * b < s n * b := OrderedRing.mul_lt_mul_of_pos_right h1 hb
  have : s n * b < s n * t n := OrderedRing.mul_lt_mul_of_pos_left h2 (by grind)
  grind

private theorem not_isPos_both (x : Completion F) (h1 : IsPos x) (h2 : IsPos (-x)) : False := by
  induction x using ind with | h s hs =>
  rw [isPos_mk] at h1; rw [mk_neg, isPos_mk] at h2
  obtain ⟨a, ha, N, hN⟩ := h1; obtain ⟨b, hb, M, hM⟩ := h2
  have := hN (max N M) (by omega); have := hM (max N M) (by omega); grind

private theorem isPos_tri (x : Completion F) : x = 0 ∨ IsPos x ∨ IsPos (-x) := by
  induction x using ind with | h s hs =>
  rw [mk_neg, isPos_mk, isPos_mk, mk_eq_zero]
  by_cases h0 : Equiv s (fun _ => 0)
  · exact Or.inl h0
  · obtain ⟨η, hη, N, hp | hn⟩ := away hs h0
    · exact Or.inr (Or.inl ⟨η, hη, N, hp⟩)
    · exact Or.inr (Or.inr ⟨η, hη, N, fun n h => by have := hn n h; grind⟩)

private theorem not_isPos_zero : ¬ IsPos (0 : Completion F) := by
  rw [zero_def, const, isPos_mk]
  rintro ⟨η, hη, N, hN⟩; have := hN N (Nat.le_refl _); grind

instance : LT (Completion F) := ⟨fun x y => IsPos (y - x)⟩
instance : LE (Completion F) := ⟨fun x y => x = y ∨ x < y⟩

theorem lt_def (x y : Completion F) : x < y ↔ IsPos (y - x) := Iff.rfl

theorem lt_irrefl (x : Completion F) : ¬ x < x := by
  rw [lt_def]; have : x - x = 0 := by grind
  rw [this]; exact not_isPos_zero

theorem lt_trans {x y z : Completion F} (h1 : x < y) (h2 : y < z) : x < z := by
  rw [lt_def] at *; have : z - x = (z - y) + (y - x) := by grind
  rw [this]; exact isPos_add h2 h1

theorem lt_asymm {x y : Completion F} (h1 : x < y) (h2 : y < x) : False := by
  rw [lt_def] at *; have : x - y = -(y - x) := by grind
  rw [this] at h2; exact not_isPos_both _ h1 h2

theorem lt_trichotomy (x y : Completion F) : x < y ∨ x = y ∨ y < x := by
  rcases isPos_tri (y - x) with h | h | h
  · exact Or.inr (Or.inl (by grind))
  · exact Or.inl h
  · right; right; rw [lt_def]; have : x - y = -(y - x) := by grind
    rw [this]; exact h

instance : Std.IsLinearOrder (Completion F) where
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

instance : Std.LawfulOrderLT (Completion F) where
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

instance : OrderedAdd (Completion F) where
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

instance : OrderedRing (Completion F) where
  zero_lt_one := by
    rw [lt_def]; have : (1 : Completion F) - 0 = 1 := by grind
    rw [this, one_def, const, isPos_mk]
    exact ⟨1 / 2, by have := OrderedRing.zero_lt_one (R := F); grind, 0, fun n _ => by
      have := OrderedRing.zero_lt_one (R := F); grind⟩
  mul_lt_mul_of_pos_left {a b c} h hc := by
    rw [lt_def] at *; have : c * b - c * a = (c - 0) * (b - a) := by grind
    rw [this]; exact isPos_mul hc h
  mul_lt_mul_of_pos_right {a b c} h hc := by
    rw [lt_def] at *; have : b * c - a * c = (b - a) * (c - 0) := by grind
    rw [this]; exact isPos_mul h hc

/-- `F` sits inside its completion as an ordered subfield. -/
theorem const_lt {a b : F} : const a < const b ↔ a < b := by
  rw [lt_def]
  have : const b - const a = const (b - a) := by
    rw [Ring.sub_eq_add_neg b a, const_add, const_neg]; rfl
  rw [this, const, isPos_mk]
  constructor
  · rintro ⟨η, hη, N, hN⟩; have := hN N (Nat.le_refl _); grind
  · intro h; exact ⟨(b - a) / 2, by grind, 0, fun n _ => by grind⟩

/-- `F` is dense: the class of a Cauchy sequence is the limit of its terms,
`|s n − [s]| < δ` eventually, for every `δ > 0` in `F`. -/
theorem tendsto_mk (s : Nat → F) (hs : IsCauchy s) {δ : F} (hδ : 0 < δ) :
    ∃ N, ∀ n, N ≤ n → const (s n) - mk s hs < const δ ∧ mk s hs - const (s n) < const δ := by
  obtain ⟨N, hN⟩ := hs (δ / 2) (by grind)
  refine ⟨N, fun n hn => ⟨?_, ?_⟩⟩
  · rw [lt_def]
    show IsPos (mk _ _ + -(mk _ _ + -mk s hs))
    simp only [mk_neg, mk_add, isPos_mk]
    exact ⟨δ / 2, by grind, N, fun m hm => by obtain ⟨u, v⟩ := hN n m hn hm; grind⟩
  · rw [lt_def]
    show IsPos (mk _ _ + -(mk s hs + -mk _ _))
    simp only [mk_neg, mk_add, isPos_mk]
    exact ⟨δ / 2, by grind, N, fun m hm => by obtain ⟨u, v⟩ := hN n m hn hm; grind⟩

theorem const_inj {a b : F} (h : const a = const b) : a = b := by
  rcases (by grind : a < b ∨ a = b ∨ b < a) with h' | h' | h'
  · have := const_lt.mpr h'; rw [h] at this; exact (lt_irrefl _ this).elim
  · exact h'
  · have := const_lt.mpr h'; rw [h] at this; exact (lt_irrefl _ this).elim

/-! ### Completeness -/

theorem const_sub (a b : F) : const (a - b) = const a - const b := by
  rw [Ring.sub_eq_add_neg a b, const_add, const_neg]; rfl

theorem const_near {a b d : F} : Near (const a) (const b) (const d) ↔ Near a b d := by
  simp only [Near, ← const_sub, const_lt]

/-- Every element is approximated by elements of `F`. -/
theorem dense (y : Completion F) {δ : F} (hδ : 0 < δ) : ∃ c, Near y (const c) (const δ) := by
  induction y using ind with | h s hs =>
  obtain ⟨N, hN⟩ := tendsto_mk s hs hδ
  obtain ⟨u, v⟩ := hN N (Nat.le_refl _)
  exact ⟨s N, v, u⟩

/-- Every positive element is above a positive element of `F`. -/
theorem pos_bound {D : Completion F} (hD : 0 < D) : ∃ δ, 0 < δ ∧ const δ < D := by
  induction D using ind with | h s hs =>
  rw [lt_def] at hD
  have : mk s hs - 0 = mk s hs := by grind
  rw [this, isPos_mk] at hD
  obtain ⟨η, hη, N, hN⟩ := hD
  refine ⟨η / 2, by grind, ?_⟩
  rw [lt_def]
  show IsPos (mk s hs + -mk _ _)
  rw [mk_neg, mk_add, isPos_mk]
  exact ⟨η / 2, by grind, N, fun n hn => by have := hN n hn; grind⟩

/-- `F` has a sequence of positive elements that eventually drops below any `d > 0`.
(True in the Puiseux field with `εᵏ`; false in fields of uncountable cofinality.) -/
def HasNullSeq (F : Type u) [Field F] [LE F] [LT F] : Prop :=
  ∃ δ : Nat → F, (∀ k, 0 < δ k) ∧ ∀ d, 0 < d → ∃ K, ∀ k, K ≤ k → δ k < d

/-- **The completion is Cauchy-complete**: every Cauchy sequence in it converges. -/
theorem complete (hF : HasNullSeq F) (x : Nat → Completion F) (hx : IsCauchy x) :
    ∃ L, ∀ D, 0 < D → ∃ N, ∀ n, N ≤ n → Near (x n) L D := by
  obtain ⟨δ, hδpos, hδ⟩ := hF
  -- approximate each `x k` within `δ k`
  have happrox : ∀ k, ∃ c, Near (x k) (const c) (const (δ k)) := fun k => dense (x k) (hδpos k)
  let c : Nat → F := fun k => Classical.choose (happrox k)
  have hc : ∀ k, Near (x k) (const (c k)) (const (δ k)) := fun k => Classical.choose_spec (happrox k)
  -- `c` is Cauchy in `F`
  have hcC : IsCauchy c := by
    intro d hd
    obtain ⟨K, hK⟩ := hδ (d / 3) (by grind)
    obtain ⟨N, hN⟩ := hx (const (d / 3)) (const_lt.mpr (by grind : (0 : F) < d / 3))
    refine ⟨max K N, fun m n hm hn => ?_⟩
    have h1 := near_symm (hc m)
    have h2 := hN m n (by omega) (by omega)
    have h3 := hc n
    have := near_trans (near_trans h1 h2) h3
    have hb : const (δ m) + const (d / 3) + const (δ n) ≤ const d := by
      rw [← const_add, ← const_add]
      have := hK m (by omega); have := hK n (by omega)
      exact Or.inr (const_lt.mpr (by grind))
    exact const_near.mp (near_mono this hb)
  refine ⟨mk c hcC, fun D hD => ?_⟩
  obtain ⟨e, he, heD⟩ := pos_bound hD
  obtain ⟨K, hK⟩ := hδ (e / 2) (by grind)
  obtain ⟨M, hM⟩ := tendsto_mk c hcC (by grind : (0 : F) < e / 2)
  refine ⟨max K M, fun n hn => ?_⟩
  have h1 := hc n
  obtain ⟨u, v⟩ := hM n (by omega)
  have h2 : Near (const (c n)) (mk c hcC) (const (e / 2)) := ⟨u, v⟩
  have := near_trans h1 h2
  apply near_mono this
  have : const (δ n) + const (e / 2) < D := by
    rw [← const_add]
    have : δ n + e / 2 < e := by have := hK n (by omega); grind
    exact lt_trans (const_lt.mpr this) heD
  exact Or.inr this

end Completion

/-! ## `εᵏ` is a null sequence in the Puiseux field -/

namespace NullSeq

open Series Series.PS Frac Lean.Grind

attribute [local instance] Semiring.natCast Ring.intCast
attribute [local instance high] Semiring.ofNat

variable {K : Type u} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

private theorem laurent_eps_pow (n : Nat) : (Laurent.eps : Laurent K) ^ n = ofRing ((X : PS K) ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (Laurent.eps : Laurent K) ^ n * Laurent.eps = ofRing ((X : PS K) ^ n * X)
    rw [ih, ofRing_mul]; rfl

/-- In `K((ε))`, every positive element exceeds some power of `ε`. -/
theorem laurent_eps_pow_lt {x : Laurent K} (hx : 0 < x) : ∃ j : Nat, Laurent.eps ^ j < x := by
  induction x using Frac.ind with
  | h a b hb =>
  have hab : PS.IsPos (a * b) := by
    have e : mk a b hb - 0 = mk a b hb := by grind
    rw [Frac.lt_def, e, isPos_mk, PS.lt_def] at hx
    have e2 : a * b - 0 = a * b := by grind
    rwa [e2] at hx
  obtain ⟨p, hz, hp⟩ := hab
  refine ⟨p + 1, ?_⟩
  rw [laurent_eps_pow, Frac.lt_def]
  unfold ofRing; show Frac.IsPos (Frac.mk a b hb + -Frac.mk (X ^ (p + 1)) 1 _)
  rw [Frac.mk_neg, Frac.mk_add, isPos_mk, PS.lt_def]
  have e : (a * 1 + -(X : PS K) ^ (p + 1) * b) * (b * 1) - 0 = a * b - (X : PS K) ^ (p + 1) * (b * b) := by grind
  rw [e]
  have hX : ∀ m, m < p + 1 → ((X : PS K) ^ (p + 1)).coeff m = 0 := fun m hm => by
    rw [X_pow_coeff]; simp only [show m ≠ p + 1 by omega, ↓reduceIte]
  have hlow := (mul_low (X ^ (p + 1)) (b * b) (p + 1) 0 hX (fun _ h => absurd h (Nat.not_lt_zero _))).1
  refine ⟨p, fun m hm => ?_, ?_⟩
  · rw [coeff_sub, hz m hm, hlow m (by omega)]; grind
  · rw [coeff_sub, hlow p (by omega)]; grind

private theorem pow_pos' {F : Type u} [Field F] [LE F] [LT F] [Std.IsLinearOrder F]
    [Std.LawfulOrderLT F] [OrderedRing F] {e : F} (he : 0 < e) (n : Nat) : 0 < e ^ n := by
  induction n with
  | zero => rw [Semiring.pow_zero]; exact OrderedRing.zero_lt_one
  | succ n ih =>
    rw [Semiring.pow_succ]
    have := OrderedRing.mul_lt_mul_of_pos_left he ih; grind

/-- Powers of `0 < e < 1` decrease. -/
private theorem pow_le_pow' {F : Type u} [Field F] [LE F] [LT F] [Std.IsLinearOrder F]
    [Std.LawfulOrderLT F] [OrderedRing F] {e : F} (he : 0 < e) (he1 : e < 1) {j k : Nat}
    (hjk : j ≤ k) : e ^ k ≤ e ^ j := by
  induction k with
  | zero => have : j = 0 := by omega
            subst this; exact Std.le_refl _
  | succ k ih =>
    by_cases h : j = k + 1
    · subst h; exact Std.le_refl _
    · have ih := ih (by omega)
      have hp := pow_pos' he k
      have : e ^ k * e < e ^ k * 1 := OrderedRing.mul_lt_mul_of_pos_left he1 hp
      rw [Semiring.pow_succ]; grind

private theorem pow_mul' {F : Type u} [CommRing F] (a : F) (m n : Nat) :
    (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero => rw [Semiring.pow_zero, Nat.mul_zero, Semiring.pow_zero]
  | succ n ih => rw [Semiring.pow_succ, ih, Nat.mul_succ, Semiring.pow_add]

private theorem eps_lt_one : (Puiseux.eps : Puiseux K) < 1 := by
  have := Puiseux.root_lt_ofK (K := K) 1 (by decide) (q := 1) OrderedRing.zero_lt_one
  have e1 : (Puiseux.root 1 (by decide) : Puiseux K) = Puiseux.eps := by
    have := Puiseux.root_pow (K := K) 1 (by decide); rwa [Semiring.pow_one] at this
  have e2 : (Puiseux.ofK 1 : Puiseux K) = 1 := rfl
  rwa [e1, e2] at this

/-- **`εᵏ → 0` in the Puiseux field**: every positive element exceeds some `εᵏ`. -/
theorem puiseux_eps_pow_lt {z : Puiseux K} (hz : 0 < z) : ∃ j : Nat, Puiseux.eps ^ j < z := by
  induction z using Puiseux.ind with
  | h N hN x =>
  have hx : 0 < x := by
    have e : Puiseux.mk N hN x - 0 = Puiseux.mk N hN x := by grind
    rw [Puiseux.lt_def, e, Puiseux.isPos_mk] at hz; exact hz
  obtain ⟨j, hj⟩ := laurent_eps_pow_lt hx
  refine ⟨j, ?_⟩
  -- `εʲ = (ε^{1/N})^{N j} ≤ (ε^{1/N})ʲ < z`
  have hr : (Puiseux.root N hN : Puiseux K) ^ j < Puiseux.mk N hN x := by
    unfold Puiseux.root; rw [← Puiseux.mk_pow, Puiseux.lt_def]
    show Puiseux.IsPos (Puiseux.mk N hN x + -Puiseux.mk N hN (Laurent.eps ^ j))
    rw [Puiseux.mk_neg, Puiseux.mk_add, Puiseux.isPos_mk]
    have := (subL_pos hN).mpr (show 0 < x - Laurent.eps ^ j by grind)
    rw [subL_sub] at this; rw [subL_neg]; grind
  have hle : (Puiseux.eps : Puiseux K) ^ j ≤ Puiseux.root N hN ^ j := by
    rw [← Puiseux.root_pow N hN, pow_mul']
    exact pow_le_pow' (Puiseux.root_pos N hN)
      (by have := Puiseux.root_lt_ofK (K := K) N hN (q := 1) OrderedRing.zero_lt_one; exact this)
      (Nat.le_mul_of_pos_left j hN)
  grind

theorem puiseux_hasNullSeq : Completion.HasNullSeq (Puiseux K) := by
  refine ⟨fun k => Puiseux.eps ^ k, fun k => pow_pos' (Puiseux.eps_pos (K := K)) k, fun d hd => ?_⟩
  obtain ⟨j, hj⟩ := puiseux_eps_pow_lt hd
  exact ⟨j, fun k hk => by
    have := pow_le_pow' (Puiseux.eps_pos (K := K)) eps_lt_one hk; grind⟩

end NullSeq

/-! ## The Levi-Civita field -/

open Series

/-- The Levi-Civita field over an ordered coefficient field `K`: the completion of
the Puiseux field `K{{ε}}`. Its elements are the series `Σ aᵢ ε^{qᵢ}` with `aᵢ ∈ K`
and left-finite rational support. -/
abbrev LeviCivitaFieldOver (K : Type u) [Lean.Grind.Field K] [LE K] [LT K]
    [Std.IsLinearOrder K] [Std.LawfulOrderLT K] [Lean.Grind.OrderedRing K] :=
  Completion (Puiseux K)

/-- The Levi-Civita field over `ℚ`. -/
abbrev LeviCivitaField := LeviCivitaFieldOver Rat

namespace LeviCivitaFieldOver

open Completion Lean.Grind

variable {K : Type u} [Field K] [LE K] [LT K] [Std.IsLinearOrder K] [Std.LawfulOrderLT K]
  [OrderedRing K]

noncomputable section

/-- The infinitesimal `ε`. -/
def eps : LeviCivitaFieldOver K := const Puiseux.eps
/-- `ε^{1/N}`. -/
def root (N : Nat) (hN : 0 < N) : LeviCivitaFieldOver K := const (Puiseux.root N hN)
/-- A coefficient. -/
def ofK (q : K) : LeviCivitaFieldOver K := const (Puiseux.ofK q)

theorem const_pow (a : Puiseux K) (n : Nat) :
    (const a : LeviCivitaFieldOver K) ^ n = const (a ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show const a ^ n * const a = const (a ^ n * a)
    rw [ih, ← const_mul]

theorem eps_pos : 0 < (eps : LeviCivitaFieldOver K) := const_lt.mpr Puiseux.eps_pos
theorem root_pow (N : Nat) (hN : 0 < N) : (root N hN : LeviCivitaFieldOver K) ^ N = eps := by
  unfold root eps; rw [const_pow, Puiseux.root_pow]
theorem root_pos (N : Nat) (hN : 0 < N) : 0 < (root N hN : LeviCivitaFieldOver K) :=
  const_lt.mpr (Puiseux.root_pos N hN)
theorem root_lt_ofK (N : Nat) (hN : 0 < N) {q : K} (hq : 0 < q) :
    (root N hN : LeviCivitaFieldOver K) < ofK q :=
  const_lt.mpr (Puiseux.root_lt_ofK N hN hq)

/-- **The Levi-Civita field is Cauchy-complete**: every Cauchy sequence converges. -/
theorem complete (x : Nat → LeviCivitaFieldOver K) (hx : Cauchy.IsCauchy x) :
    ∃ L, ∀ D, 0 < D → ∃ N, ∀ n, N ≤ n → Cauchy.Near (x n) L D :=
  Completion.complete NullSeq.puiseux_hasNullSeq x hx

end

end LeviCivitaFieldOver

namespace LeviCivitaField

open Completion

noncomputable section

/-- The infinitesimal `ε`. -/
abbrev eps : LeviCivitaField := LeviCivitaFieldOver.eps
/-- `ε^{1/N}`. -/
abbrev root (N : Nat) (hN : 0 < N) : LeviCivitaField := LeviCivitaFieldOver.root N hN
/-- A rational number. -/
abbrev ofRat (q : Rat) : LeviCivitaField := LeviCivitaFieldOver.ofK q

theorem eps_pos : 0 < eps := LeviCivitaFieldOver.eps_pos
theorem root_pow (N : Nat) (hN : 0 < N) : root N hN ^ N = eps := LeviCivitaFieldOver.root_pow N hN
theorem root_pos (N : Nat) (hN : 0 < N) : 0 < root N hN := LeviCivitaFieldOver.root_pos N hN
theorem root_lt_ofRat (N : Nat) (hN : 0 < N) {q : Rat} (hq : 0 < q) : root N hN < ofRat q :=
  LeviCivitaFieldOver.root_lt_ofK N hN hq

/-- **The Levi-Civita field is Cauchy-complete**: every Cauchy sequence converges. -/
theorem complete (x : Nat → LeviCivitaField) (hx : Cauchy.IsCauchy x) :
    ∃ L, ∀ D, 0 < D → ∃ N, ∀ n, N ≤ n → Cauchy.Near (x n) L D :=
  LeviCivitaFieldOver.complete x hx

/-- `grind` reasons in the Levi-Civita field. -/
example (x : LeviCivitaField) (h : 0 < x) : 0 < x + eps := by have := eps_pos; grind
example : eps * eps⁻¹ = 1 := by have := eps_pos; grind

end

end LeviCivitaField

end LeviCivita
