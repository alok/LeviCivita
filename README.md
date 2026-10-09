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

Convention: smaller exponent = larger magnitude (Mathlib's Hahn convention). `ε = ε^1` is a
positive infinitesimal and `H = ε^(-1)`. See `NOTES-M1.md` for details and what remains.

```lean
import LeviCivita
open LeviCivita Poly

#eval ((1 : Poly ℤ ℚ) + ε) * (1 - ε)               -- 1 ε^0 + -1 ε^2
example : (10 : Poly ℤ ℚ) ^ 9 < H := by decide +kernel
```

Build: `lake exe cache get && lake build` (this also builds the tests and the axiom audit).

## Legacy code

The previous implementation (Float variants, transcendental functions, NN demos, ...) is kept in
`Legacy/`. It is **not built and not audited**. Its proofs rely on `sorry`s, some of them false
as stated (see the design plan). Treat it as a source of ideas, not as verified code.

## License

Apache 2.0
