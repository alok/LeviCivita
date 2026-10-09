# Upstreaming the computable lexicographic order (M5)

This note covers what a Mathlib PR coming out of `LeviCivita/ForMathlib/Order/FinLex.lean` would
look like. Everything below was checked against the Mathlib checkout this project builds with
(`.lake/packages/mathlib`, master at `49fd9de`, 2026-10-08). Nothing has been opened or posted
upstream.

## The problem

`Mathlib/Order/PiLex.lean`:

```lean
/-- `Lex (∀ i, α i)` is a linear order if the original order has well-founded `<`. -/
noncomputable instance Lex.linearOrder [LinearOrder ι] [WellFoundedLT ι]
    [∀ a, LinearOrder (β a)] : LinearOrder (Lex (∀ i, β i)) :=
  @linearOrderOfSTO (Πₗ i, β i) (· < ·)
    { trichotomous := (trichotomous_lex _ _).1 } (Classical.decRel _)
```

The `DecidableLT` argument of `linearOrderOfSTO` is `Classical.decRel`, and everything else is
derived from it: `toDecidableLE`, `toDecidableEq`, `min`, `max`, `compare`. The instance covers
infinite well-ordered index types such as `ℕ`, where lexicographic `<` really is undecidable,
so it can't do better. But that makes the order on `Lex (Fin n → α)` noncomputable too, even
though it's decidable there. The consequences:

- any definition that branches on `<` through a `LinearOrder (Lex (Fin n → α))` argument (for
  us, `Poly`'s `insertTerm`) can't be `#eval`ed: it depends on `Classical.choice`;
- `decide` can't reduce it in the kernel or the elaborator.

`Pi.Colex.linearOrder` is defined as `Lex.linearOrder (ι := ιᵒᵈ)` and inherits the same problem.

There is precedent for fixing this. `DFinsupp.Lex.linearOrder` (`Mathlib/Data/DFinsupp/Lex.lean`)
and `Finsupp.Lex.linearOrder` (`Mathlib/Data/Finsupp/Lex.lean`) are computable. They decide `<`
using the finite set where the two arguments differ, and
`Mathlib/Data/Finsupp/MonomialOrder.lean` proves `toLex (single 1 1) < toLex (single 0 1)` with
`decide`. Pi types over a `Fintype` index have no such instance.

## How much of Mathlib depends on the instance

Scan (script reproduced below): we loaded all of `import Mathlib` and computed the
transitive closure of declarations whose type or value uses `Pi.Lex.linearOrder` or
`Pi.Colex.linearOrder`. Ignoring auxiliary `_proof_` constants, it contains **6 public
declarations and 2 private lemmas**, all in two files:

```
Pi.Lex.linearOrder                         Mathlib/Order/PiLex.lean
Pi.Colex.linearOrder                       Mathlib/Order/PiLex.lean
Pi.Lex.completeLattice                     Mathlib/Order/CompleteLattice/PiLex.lean
Pi.Lex.instCompleteLinearOrderLexForall    Mathlib/Order/CompleteLattice/PiLex.lean
Pi.Colex.completeLattice                   Mathlib/Order/CompleteLattice/PiLex.lean
Pi.Colex.instCompleteLinearOrderColexForall Mathlib/Order/CompleteLattice/PiLex.lean
Pi.Lex.isLUB_sSup, Pi.Lex.isGLB_sInf       Mathlib/Order/CompleteLattice/PiLex.lean (private)
```

Outside `Mathlib/Order/CompleteLattice/PiLex.lean`, no theorem in Mathlib mentions the
instance. No `decide`-based proof depends on it, and none could, since `Classical.decRel`
doesn't reduce. So changing the decidability data can't break any existing proof through
definitional unfolding. The only places to adapt are the `CompleteLattice/PiLex` instances and
the two private lemmas next to them, which would pick up the new instance argument from a
section `variable`.

```lean
import Mathlib
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut ts : NameSet := ([``Pi.Lex.linearOrder, ``Pi.Colex.linearOrder] : List Name).foldl
    (·.insert ·) {}
  let mut changed := true
  while changed do
    changed := false
    for (n, ci) in env.constants.toList do
      if !ts.contains n && ci.getUsedConstantsAsSet.any (ts.contains ·) then
        ts := ts.insert n; changed := true
  logInfo m!"{ts.toList}"
```

## Proposed change (recommended: decidability as an instance argument)

### 1. `Mathlib/Order/PiLex.lean`

Thread the decidability through as an instance argument instead of choosing it classically:

```lean
/-- `Lex (∀ i, α i)` is a linear order if the original order has well-founded `<`.
The decidability of `<` is an argument: it is computable for finite `ι`
(`Pi.Lex.decidableLT`); for infinite `ι` use `Classical.decRel`. -/
instance Lex.linearOrder [LinearOrder ι] [WellFoundedLT ι] [∀ a, LinearOrder (β a)]
    [DecidableLT (Lex (∀ i, β i))] : LinearOrder (Lex (∀ i, β i)) :=
  @linearOrderOfSTO (Πₗ i, β i) (· < ·) { trichotomous := (trichotomous_lex _ _).1 } inferInstance
```

`Colex.linearOrder` changes the same way, taking `[DecidableLT (Lex (∀ i : ιᵒᵈ, β i))]`, or
better, its own `[DecidableLT (Colex (∀ i, β i))]` with a one-line coercion.

This is the same convention Mathlib uses for `[DecidableEq α]` in `Finset` lemmas. The data
comes from whatever instance the caller has, so a generic lemma can be specialized without a
decidability diamond.

### 2. A computable `DecidableLT` for finite index types

`PiLex.lean` stays light (`assert_not_exists Monoid`, no `Fintype`). The instance would go
somewhere that already sees both `Fintype` and `Pi.Lex`, e.g. `Mathlib/Data/Fintype/Order.lean`
or a new `Mathlib/Order/PiLex/Fintype.lean`:

```lean
instance Pi.Lex.decidableLT [Fintype ι] [LinearOrder ι] [∀ i, DecidableEq (β i)]
    [∀ i, LT (β i)] [∀ i, DecidableLT (β i)] : DecidableLT (Lex (∀ i, β i)) := fun x y =>
  inferInstanceAs (Decidable (∃ i, (∀ j, j < i → ofLex x j = ofLex y j) ∧ ofLex x i < ofLex y i))
```

This is `Pi.Lex.decidableLTOfFintype` in our file, word for word. Our file also proves the
fact the PR depends on:

```lean
theorem Pi.Lex.linearOrderOfFintype_eq [∀ i, LinearOrder (β i)] :
    linearOrderOfFintype = (Pi.Lex.linearOrder : LinearOrder (Lex (∀ i, β i))) :=
  LinearOrder.ext fun _ _ => Iff.rfl
```

So the computable order equals today's, as a structure, for every finite `ι`. The proof is one
line because the partial orders are definitionally equal (both are `partialOrderOfSO (· < ·)`),
and `LinearOrder.ext` only needs `≤` to agree. `Pi.Lex.linearOrderFin_eq` is the same statement
for the faster `Fin`-specific procedure.

### 3. `Mathlib/Order/CompleteLattice/PiLex.lean`

The two `CompleteLinearOrder` instances (`__ := linearOrder`) need either the same
`[DecidableLT (Lex (∀ i, β i))]` argument or a local `Classical.decRel`. The instance argument
is better: with a local `Classical.decRel`, `CompleteLinearOrder.toLinearOrder` would differ
from the computable instance for finite `ι`, which is exactly a non-defeq data diamond. The
`completeLattice` instances themselves stay `noncomputable` (because of `sInf`). Only the
order they extend changes.

### Evidence that this works

We simulated the PR in a scratch file:
1. `attribute [-instance] Pi.Lex.linearOrder`;
2. installed the instance-argument version of `Lex.linearOrder` and `Pi.Lex.decidableLTOfFintype`
   as an instance;
3. re-ran the M2 tests on Mathlib's own `Γ = Lex (Fin 2 → ℤ)`, with no `FinLex` and no local
   `LinearOrder` instance.

All of them passed: `#eval` of `decide (ε₁ < ε₂)` etc., `ε₁ < ε₂`, `ε₁ * ε₂ < ε₁` and
`ε₁ < ε₂ ^ 5` with `decide +kernel` over `ℚ`, and the `ℤ`-coefficient tests with plain `decide`.
`(inferInstance : LinearOrder G2) = Pi.Lex.linearOrder` also holds by `LinearOrder.ext`. The
simulation is kept as `LeviCivita/TestM5.lean`, section "Upstream simulation".

### Why it's safe

- **Proofs:** no Mathlib theorem outside `CompleteLattice/PiLex.lean` depends on the instance
  (scan above). A theorem that used the
  instance could only see a different `Decidable` proof, and `Decidable` is a subsingleton.
- **Defeq:** the `PartialOrder`, and therefore `≤`, `<`, `Monotone`, `StrictMono`,
  `OrderIso` and `Pi.Lex.isOrderedCancelAddMonoid`, is unchanged definitionally. Only
  `toDecidableLE/LT/Eq`, `min`, `max` and `compare` change, and for those the old values were
  opaque (`Classical.decRel`). Nothing could have depended on how they reduce.
- **Infinite `ι`:** instance search no longer finds a `LinearOrder (Lex (ℕ → α))` without
  `open scoped Classical` (or an explicit `Classical.decRel` argument). This is the only
  breaking aspect. Inside Mathlib it affects nothing beyond the `CompleteLattice/PiLex`
  instances. Downstream projects using `Lex (ℕ → α)` as a linear order would need
  `open scoped Classical`. That is a deprecation-cycle-free change, but it should be called out
  in the PR description.

### Alternative considered: a second instance for finite `ι`

Adding `instance Pi.Lex.linearOrderOfFintype [Fintype ι] …` next to the existing noncomputable
one avoids the breaking change, but for `ι = Fin n` both instances apply. They are
propositionally equal (`linearOrderOfFintype_eq`) but **not definitionally**, because the
`Decidable` fields differ. That is a data diamond, and Mathlib policy rejects those: lemmas
proven with one instance won't `rw` or `simp` against goals elaborated with the other. Not
recommended.

## What would be upstreamed from `FinLex.lean`, and what would be dropped

| Our declaration | Upstream? |
|---|---|
| `Pi.Lex.decidableLTOfFintype` | **yes**: it *is* the new instance (`Pi.Lex.decidableLT`) |
| `Pi.Lex.linearOrderOfFintype`, `_eq` | dropped: after the PR, `Pi.Lex.linearOrder` is that order; `_eq` becomes `rfl` |
| `Fin.lexCmp`, `Fin.lexCmp_eq_lt_iff`, `Fin.lexCmp_eq_eq_iff`, `Fin.lexCmp_swap` | optional follow-up for `Mathlib/Order/Fin/Tuple.lean` (which already imports `PiLex` and `Fin.tail`). It could be the faster compiled `compare` (`@[csimp]` against the generic one) or a `Fin`-specific `DecidableLT` instance. Not both instances (decidability diamond). |
| `Pi.Lex.decidableLTFin`, `linearOrderFin`, `_eq` | same as `Fin.lexCmp` (follow-up, or dropped) |
| `FinLex` structure and all its instances, `toLexOrderAddIso`, `single`, `Repr` | **dropped**. Once Mathlib's `Lex (Fin n → α)` is computable, the extra type isn't needed upstream. We keep it in LeviCivita because it is independent of Mathlib's instance resolution, prints with `Repr`, and has `single`/`Repr` API that Mathlib's `Lex` lacks |
| `MultiEps`, `epsI` | LeviCivita-only (not in the ForMathlib file) |

Mathlib-style fixes before submission: add `module` / `public import` (Mathlib is on the module
system; our files aren't, hence the "designed for use with the module system" build warnings),
add `@[expose]` where needed, and add an author line.

## Draft PR

**Title:** `feat(Order/PiLex): computable lexicographic linear order for finite index types`

**Description:**

> `Pi.Lex.linearOrder` takes its decidability from `Classical.decRel`, which makes
> `Lex (Fin n → α)` noncomputable: one can't `#eval` or `decide` anything that branches on its
> `<`, `min`, `max` or `compare`. (`DFinsupp.Lex.linearOrder` and `Finsupp.Lex.linearOrder` are
> already computable.)
>
> This PR
> * makes `Pi.Lex.linearOrder` and `Pi.Colex.linearOrder` take `[DecidableLT (Lex (∀ i, β i))]`
>   as an instance argument instead of using `Classical.decRel`;
> * adds `Pi.Lex.decidableLT` for `[Fintype ι] [LinearOrder ι]` with decidable `=` and `<` on
>   each `β i`, by searching for the first index where the arguments differ;
> * threads the argument through `Mathlib/Order/CompleteLattice/PiLex.lean`.
>
> The partial order is unchanged definitionally. Only the decidability data, `min`, `max` and
> `compare` change. Before this PR those were classical, so no proof could depend on how they
> reduce. A scan of all of Mathlib finds that the only dependents are the `CompleteLattice` /
> `CompleteLinearOrder` instances (and two private lemmas) in `CompleteLattice/PiLex.lean`.
>
> Breaking: for infinite index types (e.g. `Lex (ℕ → α)`), `LinearOrder` now needs
> `open scoped Classical` or an explicit `Classical.decRel`.
>
> Example (now works):
> ```lean
> example : toLex ![0, 5] < (toLex ![1, 0] : Lex (Fin 2 → ℤ)) := by decide
> ```

