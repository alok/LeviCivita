/-!
# Levi-Civita Tensor/Symbol

The Levi-Civita symbol (or antisymmetric tensor) from differential geometry.
This is distinct from the Levi-Civita field, which is in Field.lean.

`symbol space [i₀, …, iₙ₋₁]` is `volumeScale · sgn σ` when the indices are a
permutation `σ` of `0, …, n − 1` (`n = space.dimension`), and `0` otherwise. The
sign is `(−1)^(number of inversions)`. The main theorem, `symbol_swap`, is the
alternating law: exchanging two adjacent indices flips the sign.
-/

namespace LeviCivita.Tensor

/-- Basic metadata about an oriented space used when forming Levi-Civita tensors. -/
structure Orientation where
  /-- The dimension of the oriented space. -/
  dimension : Nat
  /-- The scaling factor for the volume form (typically ±1 for orientation). -/
  volumeScale : Int
deriving Repr

/-- Number of inversions: pairs `i < j` with `l[i] > l[j]`. -/
def inversions : List Nat → Nat
  | [] => 0
  | a :: l => l.countP (· < a) + inversions l

/-- The indices are a permutation of `0, …, n − 1`. -/
def IsPerm (n : Nat) (l : List Nat) : Prop := l.length = n ∧ l.Nodup ∧ ∀ i ∈ l, i < n

instance (n : Nat) (l : List Nat) : Decidable (IsPerm n l) := by
  unfold IsPerm; exact inferInstance

/-- The Levi-Civita symbol `ε_{i₀ … iₙ₋₁}`, scaled by the orientation. -/
def symbol (space : Orientation) (indices : List Nat) : Int :=
  if IsPerm space.dimension indices then
    if inversions indices % 2 = 0 then space.volumeScale else -space.volumeScale
  else 0

/-- A higher-order tensor assembled from the Levi-Civita symbol. -/
def tensor (space : Orientation) (order : Nat) : List (List Int) :=
  List.replicate order (List.replicate space.dimension 0)

/-- Swapping two adjacent entries changes the number of inversions by exactly one. -/
theorem inversions_swap (p : List Nat) (a b : Nat) (l : List Nat) (hab : a ≠ b) :
    (inversions (p ++ a :: b :: l) + inversions (p ++ b :: a :: l)) % 2 = 1 := by
  induction p with
  | nil =>
    simp only [List.nil_append, inversions, List.countP_cons]
    by_cases h : b < a
    · have : ¬ a < b := by omega
      simp [h, this]; omega
    · have : a < b := by omega
      simp [h, this]; omega
  | cons x p ih =>
    have hperm : (p ++ a :: b :: l).Perm (p ++ b :: a :: l) :=
      List.Perm.append_left p (List.Perm.swap b a l)
    simp only [List.cons_append, inversions, hperm.countP_eq]
    omega

/-- Swapping two adjacent entries keeps the indices a permutation (or not). -/
theorem isPerm_swap (n : Nat) (p : List Nat) (a b : Nat) (l : List Nat) :
    IsPerm n (p ++ a :: b :: l) ↔ IsPerm n (p ++ b :: a :: l) := by
  have hperm : (p ++ a :: b :: l).Perm (p ++ b :: a :: l) :=
    List.Perm.append_left p (List.Perm.swap b a l)
  unfold IsPerm
  rw [hperm.length_eq, hperm.nodup_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun i hi => h3 i (hperm.mem_iff.mpr hi)⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun i hi => h3 i (hperm.mem_iff.mp hi)⟩

/-- The Levi-Civita symbol is alternating: exchanging two adjacent indices
negates it. (If the two indices are equal, both sides are `0`.) -/
theorem symbol_swap (space : Orientation) (p : List Nat) (a b : Nat) (l : List Nat) :
    symbol space (p ++ a :: b :: l) = -symbol space (p ++ b :: a :: l) := by
  unfold symbol
  by_cases hp : IsPerm space.dimension (p ++ b :: a :: l)
  · have hp' := (isPerm_swap space.dimension p a b l).mpr hp
    simp only [hp, hp', ↓reduceIte]
    by_cases hab : a = b
    · subst hab
      exfalso
      have hnd := hp.2.1
      simp [List.nodup_append, List.nodup_cons] at hnd
    · have := inversions_swap p a b l hab
      by_cases h1 : inversions (p ++ a :: b :: l) % 2 = 0
      · have h2 : ¬ inversions (p ++ b :: a :: l) % 2 = 0 := by omega
        simp [h1, h2]
      · have h2 : inversions (p ++ b :: a :: l) % 2 = 0 := by omega
        simp [h1, h2]
  · have hp' : ¬ IsPerm space.dimension (p ++ a :: b :: l) :=
      fun h => hp ((isPerm_swap space.dimension p a b l).mp h)
    simp [hp, hp']

/-- A repeated index gives `0`. -/
theorem symbol_repeat (space : Orientation) (p : List Nat) (a : Nat) (l : List Nat) :
    symbol space (p ++ a :: a :: l) = 0 := by
  have := symbol_swap space p a a l
  omega

/-- The identity permutation has symbol `volumeScale`. -/
theorem symbol_range (space : Orientation) :
    symbol space (List.range space.dimension) = space.volumeScale := by
  have hinv : ∀ n, inversions (List.range' 0 n) = 0 := by
    suffices h : ∀ s n, inversions (List.range' s n) = 0 from fun n => h 0 n
    intro s n
    induction n generalizing s with
    | zero => rfl
    | succ n ih =>
      simp only [List.range'_succ, inversions, ih, Nat.add_zero]
      rw [List.countP_eq_zero]
      intro x hx
      rw [List.mem_range'_1] at hx
      simp only [decide_eq_true_eq]
      omega
  unfold symbol IsPerm
  simp [List.range_eq_range', hinv, List.nodup_range']

/-- Contracting the Levi-Civita tensor with itself yields a metric volume factor. -/
theorem tensor_self_contracts
    (space : Orientation) :
    (tensor space space.dimension).length = space.dimension := by
  simp [tensor]

example : symbol ⟨3, 1⟩ [0, 1, 2] = 1 := by decide
example : symbol ⟨3, 1⟩ [1, 0, 2] = -1 := by decide
example : symbol ⟨3, 1⟩ [2, 0, 1] = 1 := by decide
example : symbol ⟨3, 1⟩ [0, 0, 1] = 0 := by decide

end LeviCivita.Tensor
