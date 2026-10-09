/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Computable lexicographic order on finite tuples

This file defines `FinLex k α`, the type of `k`-tuples `Fin k → α` with the lexicographic order
(the first index where two tuples differ decides), as a one-field structure whose `LinearOrder`
is **computable**: `<`, `≤`, `=`, `min`, `max` and `compare` are all decided by a structurally
recursive comparison `Fin.lexCmp`, so `decide` reduces closed comparisons both in the kernel and
in the elaborator, and `#eval` works.

## Main definitions

* `Fin.lexCmp f g : Ordering`: lexicographic comparison of `f g : Fin k → α`, by structural
  recursion on `k`. `Fin.lexCmp_eq_lt_iff` identifies it with `Pi.Lex (· < ·) (· < ·)`.
  Compiled code uses the linear loop `Fin.lexCmpFast` instead (`@[csimp]`).
* `FinLex k α`: one-field structure around `Fin k → α`, with constructor `toFinLex` and
  projection `ofFinLex` (coerced to a function).
* `FinLex.instLinearOrder`: computable linear order, with `compare = Fin.lexCmp`.
* Pointwise `AddCommMonoid`/`AddCommGroup` and `IsOrderedCancelAddMonoid`.
* `FinLex.toLexOrderAddIso : FinLex k α ≃+o Lex (Fin k → α)`: the transfer to Mathlib's
  lexicographic order on `Lex (Fin k → α)`.
* `FinLex.single i a`: the tuple with `a` at `i` and `0` elsewhere.
* `Pi.Lex.decidableLTFin`, `Pi.Lex.linearOrderFin`: a computable decision procedure for `<` on
  Mathlib's own `Lex (Fin k → α)`, and a computable `LinearOrder` on it which is *equal* to
  Mathlib's `Pi.Lex.linearOrder` (`Pi.Lex.linearOrderFin_eq`).
* `Pi.Lex.decidableLTOfFintype`, `Pi.Lex.linearOrderOfFintype`: the same for any finite
  linearly ordered index type and dependent values (`Pi.Lex.linearOrderOfFintype_eq`).

## Implementation notes

**Why Mathlib's order is noncomputable.** `Pi.Lex.linearOrder` (in `Mathlib/Order/PiLex.lean`)
is declared for every `[LinearOrder ι] [WellFoundedLT ι]` as
`@linearOrderOfSTO (Πₗ i, β i) (· < ·) _ (Classical.decRel _)`.
A well-founded index type can be infinite (`ι = ℕ`), where `<` on `Πₗ i, β i` is genuinely
undecidable, so the instance takes its `DecidableLE`/`DecidableLT`/`DecidableEq` fields (and
hence `min`, `max`, `compare`) from `Classical.decRel`. For `ι = Fin k` the relation is
decidable, but the instance does not know that. Any computation that branches on `<` through
a `LinearOrder (Lex (Fin k → α))` argument is then stuck: `decide` does not reduce and `#eval`
fails with "depends on `Classical.choice`".

**Why a structure.** We use a one-field structure rather than a type synonym (`def`) for
`Fin k → α` or for `Lex (Fin k → α)`:
* A synonym of `Lex (Fin k → α)` unfolds (at `instances` transparency, or whenever someone
  `unfold`s it) to a type that already carries Mathlib's noncomputable `LinearOrder`, so two
  non-defeq `LinearOrder` instances would be reachable for the same type.
  A synonym of `Fin k → α` similarly exposes the *pointwise* `Preorder` of Pi types.
  A structure has no instances except the ones declared here, so there is no overlap.
* The algebraic instances (`+`, `0`, `-`, `•`) are pointwise and defined by `ofFinLex`, so the
  simp-normal form is always `⇑(x + y) = ⇑x + ⇑y` etc., without defeq abuse.
* The transfer to Mathlib is the bundled isomorphism `toLexOrderAddIso`, whose underlying maps
  are `fun x => toLex ⇑x` and `fun f => toFinLex (ofLex f)`.

For upstreaming, the more useful contribution is probably not a new type but a computable
decision procedure for Mathlib's existing `Lex (Fin k → α)`; that is `Pi.Lex.decidableLTFin`
and `Pi.Lex.linearOrderFin` at the end of this file. See `UPSTREAM.md` in this repository.

**Why structural recursion on `k`.** `Fin.lexCmp` peels off index `0` and recurses on
`Fin.tail`. This is plain structural recursion on a `Nat`, so it reduces in the kernel and in
`whnf` (unlike well-founded recursion), and on a closed tuple such as `![1, 0]` each step
reduces by `Matrix.vecCons`/`Fin.cons` computation. Searching for the first differing index
through `Fintype` (`∃ i, …` over `Finset.univ`) would also be computable, but goes through
`Multiset` quotients and is much slower to reduce. Compiled code does not run this recursion:
evaluating `Fin.tail (Fin.tail …)` re-enters nested closures, which is quadratic in `k`. The
`@[csimp]` lemma `Fin.lexCmp_eq_lexCmpFast` replaces it by a linear loop over the indices
(`Fin.lexCmpLoop`). `Ordering.then` is `@[macro_inline]`, so the compiled comparison stops at
the first difference.

The value type `α` is arbitrary: `[LinearOrder α]` for the order, `[AddCommMonoid α]`,
`[AddCommGroup α]` and `[IsOrderedCancelAddMonoid α]` for the algebra.
-/

namespace Fin

variable {α : Type*}

/-- Lexicographic comparison of two `k`-tuples: compare at index `0`, and on a tie compare the
tails. Structural recursion on `k`, so it reduces in the kernel and in the elaborator. -/
def lexCmp [LinearOrder α] : {k : ℕ} → (Fin k → α) → (Fin k → α) → Ordering
  | 0, _, _ => .eq
  | _ + 1, f, g => (compare (f 0) (g 0)).then (lexCmp (Fin.tail f) (Fin.tail g))

variable [LinearOrder α]

@[simp]
theorem lexCmp_zero (f g : Fin 0 → α) : lexCmp f g = .eq := rfl

theorem lexCmp_succ {k : ℕ} (f g : Fin (k + 1) → α) :
    lexCmp f g = (compare (f 0) (g 0)).then (lexCmp (Fin.tail f) (Fin.tail g)) := rfl

/-- `lexCmp` returns `eq` exactly on equal tuples. -/
@[simp]
theorem lexCmp_eq_eq_iff {k : ℕ} {f g : Fin k → α} : lexCmp f g = .eq ↔ f = g := by
  induction k with
  | zero => simpa [lexCmp] using Subsingleton.elim f g
  | succ k ih =>
    rw [lexCmp_succ, Ordering.then_eq_eq, compare_eq_iff_eq, ih]
    constructor
    · rintro ⟨h0, ht⟩
      ext i
      refine Fin.cases h0 (fun j => ?_) i
      exact congrFun ht j
    · rintro rfl; exact ⟨rfl, rfl⟩

/-- `lexCmp` returns `lt` exactly when the first differing entry of `f` is smaller, i.e. on
`Pi.Lex (· < ·) (· < ·)`, the strict order of Mathlib's `Lex (Fin k → α)`. -/
theorem lexCmp_eq_lt_iff {k : ℕ} {f g : Fin k → α} :
    lexCmp f g = .lt ↔ ∃ i, (∀ j < i, f j = g j) ∧ f i < g i := by
  induction k with
  | zero => simp [lexCmp]
  | succ k ih =>
    rw [lexCmp_succ, Ordering.then_eq_lt, compare_lt_iff_lt, compare_eq_iff_eq, ih,
      Fin.exists_fin_succ]
    simp only [Fin.tail]
    constructor
    · rintro (h | ⟨h0, i, hi, hlt⟩)
      · exact Or.inl ⟨fun j hj => absurd hj (Fin.not_lt_zero j), h⟩
      · refine Or.inr ⟨i, fun j hj => ?_, hlt⟩
        refine Fin.cases (fun _ => h0) (fun j hj => hi j (Fin.succ_lt_succ_iff.1 hj)) j hj
    · rintro (⟨_, h⟩ | ⟨i, hi, hlt⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hi 0 (Fin.succ_pos i), i,
          fun j hj => hi j.succ (Fin.succ_lt_succ_iff.2 hj), hlt⟩

/-- Swapping the arguments of `lexCmp` swaps the result. -/
theorem lexCmp_swap {k : ℕ} (f g : Fin k → α) : (lexCmp f g).swap = lexCmp g f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lexCmp_succ, lexCmp_succ, Ordering.swap_then, ih, Std.OrientedOrd.eq_swap (a := f 0),
      Ordering.swap_swap]

/-- Loop form of `lexCmp` for compiled code: compares the last `r` indices `k - r, …, k - 1`
in order, without building `Fin.tail` closures (which make `lexCmp` quadratic in `k` when
run). Connected to `lexCmp` by the `@[csimp]` lemma `lexCmp_eq_lexCmpLoop`. -/
def lexCmpLoop {k : ℕ} (f g : Fin k → α) : (r : ℕ) → r ≤ k → Ordering
  | 0, _ => .eq
  | r + 1, h => (compare (f ⟨k - (r + 1), by omega⟩) (g ⟨k - (r + 1), by omega⟩)).then
      (lexCmpLoop f g r (by omega))

theorem lexCmpLoop_eq {k : ℕ} (f g : Fin k → α) (r : ℕ) (h : r ≤ k) :
    lexCmpLoop f g r h =
      lexCmp (fun j : Fin r => f ⟨k - r + j, by omega⟩) (fun j : Fin r => g ⟨k - r + j, by omega⟩) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [lexCmpLoop, lexCmp_succ, ih (by omega)]
    congr 2
    · funext j; simp only [Fin.tail, Fin.val_succ]; congr 2; omega
    · funext j; simp only [Fin.tail, Fin.val_succ]; congr 2; omega

/-- `lexCmp` as a single linear-time loop over all indices (the compiled implementation). -/
def lexCmpFast {k : ℕ} (f g : Fin k → α) : Ordering := lexCmpLoop f g k le_rfl

/-- Compiled code runs `lexCmp` as the linear-time loop `lexCmpFast`. -/
@[csimp]
theorem lexCmp_eq_lexCmpFast : @lexCmp = @lexCmpFast := by
  funext α _ k f g
  rw [lexCmpFast, lexCmpLoop_eq]
  simp

end Fin

/-- `k`-tuples with values in `α`, ordered lexicographically (the first index where two tuples
differ decides) by a computable `LinearOrder`. Order-isomorphic to Mathlib's `Lex (Fin k → α)`
via `FinLex.toLexOrderAddIso`. -/
structure FinLex (k : ℕ) (α : Type*) where
  /-- Regard a tuple as an element of `FinLex k α`. -/
  toFinLex ::
  /-- The underlying tuple of an element of `FinLex k α`. -/
  ofFinLex : Fin k → α

namespace FinLex

variable {k : ℕ} {α : Type*}

/-- Elements of `FinLex k α` are functions `Fin k → α`. -/
instance instFunLike : FunLike (FinLex k α) (Fin k) α where
  coe := ofFinLex
  coe_injective := fun ⟨_⟩ ⟨_⟩ h => congrArg toFinLex h

@[simp] theorem ofFinLex_eq_coe (x : FinLex k α) : x.ofFinLex = ⇑x := rfl

@[simp] theorem coe_toFinLex (f : Fin k → α) : ⇑(toFinLex f) = f := rfl

@[simp] theorem toFinLex_coe (x : FinLex k α) : toFinLex ⇑x = x := rfl

theorem toFinLex_apply (f : Fin k → α) (i : Fin k) : toFinLex f i = f i := rfl

theorem coe_injective : Function.Injective (fun x : FinLex k α => (⇑x : Fin k → α)) :=
  DFunLike.coe_injective

@[ext]
theorem ext {x y : FinLex k α} (h : ∀ i, x i = y i) : x = y := DFunLike.ext _ _ h

@[simp] theorem toFinLex_inj {f g : Fin k → α} : toFinLex f = toFinLex g ↔ f = g :=
  ⟨congrArg ofFinLex, congrArg toFinLex⟩

/-- `toFinLex` as an equivalence. -/
@[simps]
def equivFun : (Fin k → α) ≃ FinLex k α where
  toFun := toFinLex
  invFun := ofFinLex
  left_inv _ := rfl
  right_inv _ := rfl

instance [Inhabited α] : Inhabited (FinLex k α) := ⟨toFinLex default⟩

instance [Nonempty α] : Nonempty (FinLex k α) := ⟨toFinLex fun _ => Classical.ofNonempty⟩

/-- Prints `x : FinLex k α` as the vector `![x 0, …, x (k-1)]`. -/
instance [Repr α] : Repr (FinLex k α) where
  reprPrec x _ := "![" ++ Std.Format.joinSep ((List.finRange k).map fun i => repr (x i)) ", " ++
    "]"

/-! ### Order -/

section Order

/-- The lexicographic partial order, pulled back from Mathlib's `Lex (Fin k → α)`. This carries
no decidability data, so pulling it back is computable. -/
instance instPartialOrder [PartialOrder α] : PartialOrder (FinLex k α) :=
  PartialOrder.lift (fun x => toLex (⇑x : Fin k → α)) fun x y h => coe_injective (by exact h)

section PartialOrder

variable [PartialOrder α] {x y : FinLex k α}

/-- `<` on `FinLex` is Mathlib's `<` on `Lex (Fin k → α)`. -/
theorem lt_iff_toLex_lt : x < y ↔ toLex (⇑x : Fin k → α) < toLex ⇑y := Iff.rfl

/-- `≤` on `FinLex` is Mathlib's `≤` on `Lex (Fin k → α)`. -/
theorem le_iff_toLex_le : x ≤ y ↔ toLex (⇑x : Fin k → α) ≤ toLex ⇑y := Iff.rfl

/-- The explicit lexicographic characterization of `<`. -/
theorem lt_iff_exists : x < y ↔ ∃ i, (∀ j < i, x j = y j) ∧ x i < y i := Iff.rfl

theorem le_iff_eq_or_lt : x ≤ y ↔ x = y ∨ x < y := _root_.le_iff_eq_or_lt

end PartialOrder

variable [LinearOrder α] {x y : FinLex k α}

@[simp] theorem lexCmp_eq_lt_iff : Fin.lexCmp ⇑x ⇑y = .lt ↔ x < y := Fin.lexCmp_eq_lt_iff

@[simp] theorem lexCmp_eq_eq_iff : Fin.lexCmp ⇑x ⇑y = .eq ↔ x = y :=
  Fin.lexCmp_eq_eq_iff.trans coe_injective.eq_iff

theorem lexCmp_ne_gt_iff : Fin.lexCmp ⇑x ⇑y ≠ .gt ↔ x ≤ y := by
  rw [le_iff_eq_or_lt, ← lexCmp_eq_lt_iff, ← lexCmp_eq_eq_iff]
  cases Fin.lexCmp ⇑x ⇑y <;> simp

theorem lt_trichotomy' (x y : FinLex k α) : x < y ∨ x = y ∨ y < x := by
  have h := Fin.lexCmp_swap ⇑x ⇑y
  rw [← lexCmp_eq_lt_iff, ← lexCmp_eq_eq_iff, ← lexCmp_eq_lt_iff (x := y), ← h]
  cases Fin.lexCmp ⇑x ⇑y <;> simp

/-- Computable decision procedure for `≤`, by `Fin.lexCmp`. -/
instance decidableLE : DecidableLE (FinLex k α) := fun _ _ =>
  decidable_of_iff _ lexCmp_ne_gt_iff

/-- Computable decision procedure for `<`, by `Fin.lexCmp`. -/
instance decidableLT : DecidableLT (FinLex k α) := fun _ _ =>
  decidable_of_iff _ lexCmp_eq_lt_iff

/-- Computable decision procedure for `=`, by `Fin.lexCmp`. -/
instance decidableEq : DecidableEq (FinLex k α) := fun _ _ =>
  decidable_of_iff _ lexCmp_eq_eq_iff

/-- The lexicographic linear order. All data (`≤`, `<`, `=` decisions, `min`, `max`, `compare`)
is computable, and `compare x y = Fin.lexCmp ⇑x ⇑y`. -/
instance instLinearOrder : LinearOrder (FinLex k α) where
  le_total x y := by
    rcases lt_trichotomy' x y with h | rfl | h
    exacts [Or.inl h.le, Or.inl le_rfl, Or.inr h.le]
  toDecidableLE := decidableLE
  toDecidableLT := decidableLT
  toDecidableEq := decidableEq
  compare x y := Fin.lexCmp ⇑x ⇑y
  compare_eq_compareOfLessAndEq x y := by
    rw [compareOfLessAndEq]
    split_ifs with hlt heq
    · exact lexCmp_eq_lt_iff.2 hlt
    · exact lexCmp_eq_eq_iff.2 heq
    · have h1 := mt lexCmp_eq_lt_iff.1 hlt
      have h2 := mt lexCmp_eq_eq_iff.1 heq
      revert h1 h2; cases Fin.lexCmp ⇑x ⇑y <;> simp

@[simp] theorem compare_eq_lexCmp (x y : FinLex k α) : compare x y = Fin.lexCmp ⇑x ⇑y := rfl

/-- Strict monotonicity of the transfer map is definitional. -/
theorem toLex_strictMono : StrictMono (fun x : FinLex k α => toLex (⇑x : Fin k → α)) :=
  fun _ _ h => h

end Order

/-! ### Algebra (pointwise) -/

section Algebra

/-- `tabulate f = toFinLex f`. It exists for compiled code only: the `@[csimp]` lemma
`tabulate_eq_tabulateImpl` makes it store `f` as an `Array`, computed once. Without it,
iterated pointwise operations build nested closures, and every comparison re-evaluates the
whole closure tree. In the kernel and in `decide`, `tabulate` unfolds to `toFinLex`, so all
the `coe_*` lemmas below stay `rfl`. (The result type is the structure, not a function type,
so the compiler does not eta-expand the implementation and recompute the array per call.) -/
def tabulate (f : Fin k → α) : FinLex k α := toFinLex f

@[simp] theorem tabulate_eq (f : Fin k → α) : tabulate f = toFinLex f := rfl

/-- Index into a tabulated tuple. -/
@[noinline]
def tabulateGet (a : Array α) (h : a.size = k) : Fin k → α := fun i => a[i.1]'(h ▸ i.2)

/-- Compiled implementation of `tabulate`: tabulate once, then index. -/
def tabulateImpl (f : Fin k → α) : FinLex k α :=
  toFinLex (tabulateGet (Array.ofFn f) Array.size_ofFn)

@[csimp]
theorem tabulate_eq_tabulateImpl : @tabulate = @tabulateImpl := by
  funext k α f
  simp only [tabulate, tabulateImpl, toFinLex.injEq]
  funext i
  simp [tabulateGet]

/-! The operations are top-level definitions, and the instances refer to them by name. An
instance written as a lambda `⟨fun x y => tabulate …⟩` would be eta-expanded by the compiler
(`FinLex` is erased to its function field), which moves the tabulation under the index binder
and recomputes it on every read. -/

/-- Pointwise addition. -/
protected def add [Add α] (x y : FinLex k α) : FinLex k α := tabulate (⇑x + ⇑y)
/-- Pointwise negation. -/
protected def neg [Neg α] (x : FinLex k α) : FinLex k α := tabulate (-⇑x)
/-- Pointwise subtraction. -/
protected def sub [Sub α] (x y : FinLex k α) : FinLex k α := tabulate (⇑x - ⇑y)
/-- Pointwise scalar multiplication. -/
protected def smul {M : Type*} [SMul M α] (c : M) (x : FinLex k α) : FinLex k α :=
  tabulate (c • ⇑x)

instance [Zero α] : Zero (FinLex k α) := ⟨toFinLex 0⟩
instance [Add α] : Add (FinLex k α) := ⟨FinLex.add⟩
instance [Neg α] : Neg (FinLex k α) := ⟨FinLex.neg⟩
instance [Sub α] : Sub (FinLex k α) := ⟨FinLex.sub⟩
instance {M : Type*} [SMul M α] : SMul M (FinLex k α) := ⟨FinLex.smul⟩

@[simp] theorem coe_zero [Zero α] : ⇑(0 : FinLex k α) = 0 := rfl
@[simp] theorem coe_add [Add α] (x y : FinLex k α) : ⇑(x + y) = ⇑x + ⇑y := rfl
@[simp] theorem coe_neg [Neg α] (x : FinLex k α) : ⇑(-x) = -⇑x := rfl
@[simp] theorem coe_sub [Sub α] (x y : FinLex k α) : ⇑(x - y) = ⇑x - ⇑y := rfl
@[simp] theorem coe_smul {M : Type*} [SMul M α] (c : M) (x : FinLex k α) : ⇑(c • x) = c • ⇑x :=
  rfl

theorem zero_apply [Zero α] (i : Fin k) : (0 : FinLex k α) i = 0 := rfl
theorem add_apply [Add α] (x y : FinLex k α) (i : Fin k) : (x + y) i = x i + y i := rfl
theorem neg_apply [Neg α] (x : FinLex k α) (i : Fin k) : (-x) i = -x i := rfl
theorem sub_apply [Sub α] (x y : FinLex k α) (i : Fin k) : (x - y) i = x i - y i := rfl
theorem smul_apply {M : Type*} [SMul M α] (c : M) (x : FinLex k α) (i : Fin k) :
    (c • x) i = c • x i := rfl

@[simp] theorem toFinLex_zero [Zero α] : toFinLex (0 : Fin k → α) = 0 := rfl
@[simp] theorem toFinLex_add [Add α] (f g : Fin k → α) :
    toFinLex (f + g) = toFinLex f + toFinLex g := rfl
@[simp] theorem toFinLex_neg [Neg α] (f : Fin k → α) : toFinLex (-f) = -toFinLex f := rfl
@[simp] theorem toFinLex_sub [Sub α] (f g : Fin k → α) :
    toFinLex (f - g) = toFinLex f - toFinLex g := rfl

instance [AddMonoid α] : AddMonoid (FinLex k α) :=
  Function.Injective.addMonoid _ coe_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)

instance [AddCommMonoid α] : AddCommMonoid (FinLex k α) :=
  Function.Injective.addCommMonoid _ coe_injective rfl (fun _ _ => rfl) (fun _ _ => rfl)

instance [AddGroup α] : AddGroup (FinLex k α) :=
  Function.Injective.addGroup _ coe_injective rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance [AddCommGroup α] : AddCommGroup (FinLex k α) :=
  Function.Injective.addCommGroup _ coe_injective rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Evaluation at an index, as an additive monoid hom. -/
@[simps]
def evalAddMonoidHom [AddMonoid α] (i : Fin k) : FinLex k α →+ α where
  toFun x := x i
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The lexicographic order is compatible with pointwise addition (via Mathlib's
`Pi.Lex.isOrderedCancelAddMonoid`). -/
instance [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] :
    IsOrderedCancelAddMonoid (FinLex k α) :=
  Function.Injective.isOrderedCancelAddMonoid (fun x : FinLex k α => toLex (⇑x : Fin k → α))
    (fun _ _ => rfl) Iff.rfl

/-- `FinLex k α` is an ordered additive monoid (this also follows from
`IsOrderedCancelAddMonoid`; stated for discoverability). -/
instance [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] :
    IsOrderedAddMonoid (FinLex k α) := inferInstance

/-! ### Basis vectors -/

/-- The tuple with `a` at index `i` and `0` elsewhere. -/
def single [Zero α] (i : Fin k) (a : α) : FinLex k α := tabulate (Pi.single i a)

@[simp] theorem coe_single [Zero α] (i : Fin k) (a : α) : ⇑(single i a) = Pi.single i a := rfl

theorem single_apply [Zero α] (i j : Fin k) (a : α) :
    single i a j = if j = i then a else 0 := Pi.single_apply i a j

@[simp] theorem single_apply_self [Zero α] (i : Fin k) (a : α) : single i a i = a := by
  simp [single]

theorem single_apply_of_ne [Zero α] {i j : Fin k} (h : j ≠ i) (a : α) : single i a j = 0 := by
  simp [single, h]

theorem single_injective [Zero α] (i : Fin k) : Function.Injective (single (α := α) i) :=
  fun _ _ h => by simpa using congrFun (congrArg DFunLike.coe h) i

theorem single_add [AddZeroClass α] (i : Fin k) (a b : α) :
    single i (a + b) = single i a + single i b :=
  ext fun j => by by_cases h : j = i <;> simp [single_apply, h]

/-- For a positive `a`, `single i a` is positive, and a basis vector at a *later* index is
smaller: `single j a < single i a` for `i < j` (the first index decides). -/
theorem single_lt_single [AddCommMonoid α] [PartialOrder α] {i j : Fin k} (hij : i < j)
    {a : α} (ha : 0 < a) : single j a < single i a :=
  lt_iff_exists.2 ⟨i, fun l hl => by
    rw [single_apply_of_ne hl.ne, single_apply_of_ne (hl.trans hij).ne],
    by rw [single_apply_of_ne hij.ne, single_apply_self]; exact ha⟩

theorem single_pos [AddCommMonoid α] [PartialOrder α] (i : Fin k) {a : α} (ha : 0 < a) :
    0 < single i a :=
  lt_iff_exists.2 ⟨i, fun l hl => by rw [single_apply_of_ne hl.ne]; rfl,
    by rw [single_apply_self]; exact ha⟩

end Algebra

/-! ### Transfer to Mathlib's `Lex (Fin k → α)` -/

section Transfer

variable [Add α] [PartialOrder α]

/-- `FinLex k α` and Mathlib's `Lex (Fin k → α)` are isomorphic as ordered additive monoids
(here: as types with `+` and `≤`). Both underlying maps are the identity on tuples. -/
def toLexOrderAddIso : FinLex k α ≃+o Lex (Fin k → α) where
  toFun x := toLex ⇑x
  invFun f := toFinLex (ofLex f)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_le_map_iff' := Iff.rfl

@[simp] theorem toLexOrderAddIso_apply (x : FinLex k α) : toLexOrderAddIso x = toLex ⇑x := rfl

@[simp] theorem toLexOrderAddIso_symm_apply (f : Lex (Fin k → α)) :
    toLexOrderAddIso.symm f = toFinLex (ofLex f) := rfl

/-- The underlying order isomorphism. -/
def toLexOrderIso : FinLex k α ≃o Lex (Fin k → α) := toLexOrderAddIso.toOrderIso

@[simp] theorem toLexOrderIso_apply (x : FinLex k α) : toLexOrderIso x = toLex ⇑x := rfl

end Transfer

end FinLex

/-! ### A computable order on Mathlib's `Lex (Fin k → α)`

The key lemma for an upstream change: Mathlib's `<` on `Lex (Fin k → α)` is decided by
`Fin.lexCmp`, and the resulting computable linear order *equals* `Pi.Lex.linearOrder`. Nothing
here is an instance, so the behaviour of Mathlib's type is unchanged in this project. -/

namespace Pi.Lex

variable {k : ℕ} {α : Type*} [LinearOrder α]

/-- Computable decision procedure for `<` on Mathlib's `Lex (Fin k → α)`. -/
@[instance_reducible]
def decidableLTFin : DecidableLT (Lex (Fin k → α)) := fun f g =>
  decidable_of_iff _ (Fin.lexCmp_eq_lt_iff (f := ofLex f) (g := ofLex g))

/-- A computable `LinearOrder` on Mathlib's `Lex (Fin k → α)`: the same construction as
`Pi.Lex.linearOrder` (`linearOrderOfSTO`), with `Classical.decRel` replaced by
`decidableLTFin`. Its `PartialOrder` is definitionally Mathlib's. -/
abbrev linearOrderFin : LinearOrder (Lex (Fin k → α)) :=
  @linearOrderOfSTO (Lex (Fin k → α)) (· < ·) { trichotomous := (Pi.trichotomous_lex _ _).1 }
    decidableLTFin

/-- The computable order is equal to Mathlib's (as a structure; the decidability fields agree
because `Decidable` is a subsingleton). -/
theorem linearOrderFin_eq : linearOrderFin = (Pi.Lex.linearOrder : LinearOrder (Lex (Fin k → α))) :=
  LinearOrder.ext fun _ _ => Iff.rfl

/-- The partial orders agree definitionally. -/
example : (linearOrderFin : LinearOrder (Lex (Fin k → α))).toPartialOrder =
    (Pi.Lex.linearOrder : LinearOrder (Lex (Fin k → α))).toPartialOrder := rfl

section Fintype

variable {ι : Type*} {β : ι → Type*} [Fintype ι] [LinearOrder ι]

/-- Computable decision procedure for `<` on `Lex (∀ i, β i)` for any finite linearly ordered
index type, by `Fintype` search for the first index where the arguments differ. This is the
general form an upstream instance would take; `decidableLTFin` is a faster special case for
`Fin k` with a constant value type. -/
@[instance_reducible]
def decidableLTOfFintype [∀ i, DecidableEq (β i)] [∀ i, LT (β i)] [∀ i, DecidableLT (β i)] :
    DecidableLT (Lex (∀ i, β i)) := fun x y =>
  inferInstanceAs (Decidable (∃ i, (∀ j, j < i → ofLex x j = ofLex y j) ∧ ofLex x i < ofLex y i))

/-- A computable `LinearOrder` on `Lex (∀ i, β i)` for finite `ι`: `Pi.Lex.linearOrder` with
`Classical.decRel` replaced by `decidableLTOfFintype`. -/
abbrev linearOrderOfFintype [∀ i, LinearOrder (β i)] : LinearOrder (Lex (∀ i, β i)) :=
  @linearOrderOfSTO (Lex (∀ i, β i)) (· < ·) { trichotomous := (Pi.trichotomous_lex _ _).1 }
    decidableLTOfFintype

/-- For finite `ι` the computable order equals Mathlib's `Pi.Lex.linearOrder` (whose
`WellFoundedLT ι` argument is found from `Finite ι`). -/
theorem linearOrderOfFintype_eq [∀ i, LinearOrder (β i)] :
    linearOrderOfFintype = (Pi.Lex.linearOrder : LinearOrder (Lex (∀ i, β i))) :=
  LinearOrder.ext fun _ _ => Iff.rfl

end Fintype

end Pi.Lex
