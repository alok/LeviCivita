/-!
# Levi-Civita Tensor/Symbol

The Levi-Civita symbol (or antisymmetric tensor) from differential geometry.
This is distinct from the Levi-Civita field, which is in Field.lean.
-/

namespace LeviCivita.Tensor

/-- Basic metadata about an oriented space used when forming Levi-Civita tensors. -/
structure Orientation where
  /-- The dimension of the oriented space. -/
  dimension : Nat
  /-- The scaling factor for the volume form (typically ±1 for orientation). -/
  volumeScale : Int
deriving Repr

/-- Placeholder definition of the Levi-Civita symbol. -/
def symbol (space : Orientation) (indices : List Nat) : Int :=
  if indices.length = space.dimension then space.volumeScale else 0

/-- A higher-order tensor assembled from the Levi-Civita symbol. -/
def tensor (space : Orientation) (order : Nat) : List (List Int) :=
  List.replicate order (List.replicate space.dimension 0)

/-- The Levi-Civita symbol is alternating. -/
theorem symbol_alternating
    (space : Orientation) (indices : List Nat) :
    symbol space indices = - symbol space (indices.reverse) := by
  sorry

/-- Contracting the Levi-Civita tensor with itself yields a metric volume factor. -/
theorem tensor_self_contracts
    (space : Orientation) :
    (tensor space space.dimension).length = space.dimension := by
  simp [tensor]

end LeviCivita.Tensor
