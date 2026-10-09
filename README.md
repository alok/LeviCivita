# LeviCivita

Exact, verified arithmetic with infinitesimals in Lean 4. The specification is
Mathlib's lexicographically ordered Hahn series `Lex R⟦Γ⟧`.

## Status: rewrite in progress (branch `grokbot/hahn-rewrite`)

This branch rewrites the library on top of current Mathlib (Lean `v4.35.0-rc4`, Mathlib master).
The design: a small **computable** type `Poly Γ R` with an **injective ring hom**
`toHahn : Poly Γ R →+* R⟦Γ⟧`. Every algebraic and order law is *transported* from Mathlib,
none is proved by hand.

**Milestone M1 (done):** zero `sorry`, zero `native_decide`, no `implemented_by`, no custom axioms.

- `LeviCivita.Poly.Basic`: `Poly Γ R` is a list of `(exponent, coeff)` terms with strictly
  ascending exponents and nonzero coefficients, and both invariants are fields of the structure.
  It has computable `0 1 + - * •`, `npow`, casts, `single`, `C`, `ε`, `H`, `sign`.
- `LeviCivita.Poly.Hahn`: `toHahn`, `toHahn_injective`, and `CommRing (Poly Γ R)` via
  `Function.Injective.commRing` (data fields are the computable ones).
- `LeviCivita.Poly.Order`: the computable `sign` agrees with `Lex R⟦Γ⟧`
  (`sign_eq_one_iff`, `sign_eq_neg_one_iff`, `sign_eq_zero_iff`). Also a `LinearOrder` whose
  `<`/`≤` *mean* the Hahn order but are *decided* by `sign`, and `IsStrictOrderedRing` by transport.
- `LeviCivita.Test`: `#eval` and `decide` tests, e.g.
  `example : (ε : Poly ℤ ℚ) < C (1/1000) := by decide +kernel`.
- `LeviCivita.AxiomAudit`: `#assert_axioms` fails the build if any key declaration depends
  on anything beyond `propext`, `Classical.choice`, `Quot.sound`.

**Milestone M2 (done, branch `grokbot/hahn-m2`):** same guarantees (zero `sorry`, no
`native_decide`, no custom axioms).

- `LeviCivita.Poly.Algebra`: `Algebra R (Poly Γ R)` (computable `•` and `algebraMap = C`),
  `toHahnAlg : Poly Γ R →ₐ[R] R⟦Γ⟧`, `toLexHahnHom : Poly Γ R →+*o Lex R⟦Γ⟧`, `toLexHahnEmb`.
- `LeviCivita.Poly.Std`: computable `coeff`, `leadExp`, `std`, decidable `IsFinite` and
  `IsInfinitesimal`, each proved equal to its Hahn-series meaning. Also `finiteSubring`,
  `stdPart : finiteSubring →+* R` (kernel = infinitesimals), and the order characterizations
  `isFinite_iff_exists_abs_le` and `isInfinitesimal_iff_forall_abs_lt`.
- `LeviCivita.Poly.Deriv`: the coefficient of `ε^n` in `f (a + ε)` is the `n`-th Hasse derivative
  of `f` at `a`. The `n = 1` case is ε-AD: `(aeval (C a + ε) f).coeff 1 = f.derivative.eval a`.
  Computable `dualDeriv`.
- `LeviCivita.TestM2`: tests, including two independent infinitesimals with `Γ = Lex (Fin 2 → ℤ)`.

See `NOTES-M2.md`.

**Milestone M3 (done, branch `grokbot/hahn-m3`):** same guarantees.

- `LeviCivita.Geometry.Predicates`: `orient2d`, `orient3d`, `incircle`, `insphere` as explicit
  polynomials (one definition runs on `ℤ`, `ℚ`, `Poly`, `Float`), each proved equal to the
  standard `Matrix.det`. Antisymmetry, translation invariance, naturality along ring homs.
- `LeviCivita.Geometry.SoS`: Simulation of Simplicity. Coordinate `j` of point `i` becomes
  `x i j + ε^(b^(j + d i))` in `Poly ℤ R`. For **any** input (collinear, coincident, …) the
  perturbed predicate is never `0` for distinct point indices (`orient2dSoS_ne_zero`, …,
  `insphereSoS_ne_zero`), and its sign is the exact sign whenever that is nonzero
  (`orient2dSoS_sign`, …). `b = 4` serves all four predicates.
- `LeviCivita.Geometry.LazySign`: `Poly.truncLT`/`mulTrunc` (specs: `HahnSeries.truncLT`), an
  expression evaluator with truncation, `lazySign_sound`/`lazySign_complete`, and lazy SoS
  `orient2dLazy`/`incircleLazy`.
- `bench/Bench.lean`: Float vs exact vs SoS timings (`lake env lean --run bench/Bench.lean`).

See `NOTES-M3.md`.

Convention: smaller exponent = larger magnitude (Mathlib's Hahn convention). `ε = ε^1` is a
positive infinitesimal and `H = ε^(-1)`. See `NOTES-M1.md` for details and what remains.

```lean
import LeviCivita
open LeviCivita Poly

#eval ((1 : Poly ℤ ℚ) + ε) * (1 - ε)               -- 1 ε^0 + -1 ε^2
example : (10 : Poly ℤ ℚ) ^ 9 < H := by decide +kernel
#eval dualDeriv (fun x : Poly ℤ ℚ => x ^ 3 + 2 * x) 2   -- 14
example : (ε : Poly ℤ ℚ).IsInfinitesimal := by decide +kernel

open Geometry LazySign
def pts : Fin 3 → Fin 2 → ℤ := ![![0, 0], ![1, 1], ![2, 2]]   -- collinear
example : (orient2dSoS 4 pts 0 1 2).sign = -1 := by decide   -- definite SoS sign
example : orient2dLazy 4 pts 0 1 2 = some (-1) := by decide
```

Build: `lake exe cache get && lake build` (this also builds the tests and the axiom audit).

## Legacy code

The previous implementation (Float variants, transcendental functions, NN demos, ...) is kept in
`Legacy/`. It is **not built and not audited**. Its proofs rely on `sorry`s, some of them false
as stated (see the design plan). Treat it as a source of ideas, not as verified code.

## License

Apache 2.0
