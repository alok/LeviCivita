# M1 notes: `Poly Γ R` on Mathlib Hahn series

Branch `grokbot/hahn-rewrite`. Toolchain `leanprover/lean4:v4.35.0-rc4`, Mathlib master (pinned in
`lake-manifest.json`). Status: **all M1 deliverables done**. The build has zero `sorry`, zero
`native_decide`, no `implemented_by`/`extern`, and no new `axiom`.

## Layout

| File | Contents |
|---|---|
| `LeviCivita/Poly/Basic.lean` | `insertTerm` (structural recursion), `structure Poly` (invariants in the type), `insert`, `insertMap`, `0 1 + - * •(R,ℕ,ℤ) ^`, casts, `single`, `C`, `ε`, `H`, `leadCoeff`, `sign`, `Repr`, `DecidableEq` |
| `LeviCivita/Poly/Hahn.lean` | `hahnL`/`toHahnFun` denotation, injectivity, hom lemmas, transported `CommRing`, bundled `toHahn : Poly Γ R →+* R⟦Γ⟧` |
| `LeviCivita/Poly/Order.lean` | sign theorems, `LT`/`LE` pulled back from `Lex R⟦Γ⟧`, computable `DecidableLT/LE`, `LinearOrder`, `IsStrictOrderedRing` by transport |
| `LeviCivita/Test.lean` | `#guard_msgs` `#eval` tests and named `decide` theorems |
| `LeviCivita/Util/AssertAxioms.lean` | `#assert_axioms` command (allow-list `propext`, `Classical.choice`, `Quot.sound`) |
| `LeviCivita/AxiomAudit.lean` | audit of all key declarations and the tests. It is a root of the default target, so `lake build` fails on a bad axiom |
| `.github/workflows/ci.yml` | elan, `lake exe cache get`, `lake build` (includes tests and audit), grep for `declaration uses 'sorry'` and forbidden constructs |

## Design decisions

- **List representation.** Every operation is a fold of `insertTerm`, which uses structural
  recursion on a list. This gives proofs by plain list induction, and the kernel can reduce every
  operation, so `decide` works. Complexity is `O(n·m)` for `+` and `O(n·m·|result|)` for `*`.
  Faster `Array`/merge versions are for M7 via `@[csimp]`.
- **Raw-list denotation.** `hahnL l = ∑ single e c` holds for *any* list, sorted or not. The hom
  lemma for `insertTerm` therefore needs no invariant. The invariants are used in exactly one
  place: `eq_of_hahnL_eq`, which gives injectivity.
- **Computable transported instances.** `Function.Injective.commRing` and
  `Function.Injective.linearOrder` take the noncomputable map (and, for the order, the
  noncomputable order on `Lex R⟦Γ⟧`) as an argument, so the compiler rejects the result. The fix:
  build `commRingAux`/`linearOrderAux` noncomputably, then define `instCommRing`/`instLinearOrder`
  with every **data** field written out as the computable operation. Every **proof** field is
  copied from the aux structure. No law is proved by hand.
- **Order.** `p < q` is *defined* as `toLex (toHahn p) < toLex (toHahn q)`. The order hypotheses
  of the transport lemmas are therefore `Iff.rfl`. `DecidableLT` is
  `decidable_of_iff ((q - p).sign = 1) lt_iff_sign.symm`, so `decide` computes signs, while the
  proposition being decided is the Hahn-series one.
- Generic in `Γ` (`AddCommMonoid Γ`, `LinearOrder Γ`, `IsOrderedCancelAddMonoid Γ`) and `R`
  (`CommRing R`, `DecidableEq R`, plus `LinearOrder R`, `IsStrictOrderedRing R` for the order).
  Tested with `Γ = ℤ` (`R = ℚ` and `R = ℤ`) and `Γ = ℚ` (`√ε = single (1/2) 1`).

## Proven (theorem names, namespace `LeviCivita.Poly`)

- Invariants: `insertTerm_sorted`, `insertTerm_nz`, `mem_insertTerm`.
- Denotation: `hahnL_insertTerm`, `toHahnFun_insert`, `toHahnFun_insertMap`, `toHahnFun_single`,
  `toHahnFun_zero/one/C/add/neg/sub/mul/smul/nsmul/zsmul/pow/natCast/intCast`.
- Injectivity: `eq_of_hahnL_eq`, `toHahnFun_injective`, `toHahn_injective`.
- Bundled hom: `toHahn : Poly Γ R →+* R⟦Γ⟧`, `toHahn_apply`, `toHahn_single`, `toHahn_C`,
  `toHahn_smul`, `toHahn_ε`, `toHahn_H`.
- Leading term: `leadingCoeff_toHahnFun` (`(toHahn p).leadingCoeff = p.leadCoeff`),
  `toHahnFun_eq_zero_iff`, `leadCoeff_eq_zero_iff`.
- Instances: `instCommRing` (aux `commRingAux`), `instLinearOrder` (aux `linearOrderAux`),
  `decidableLT`, `decidableLE`, `instIsStrictOrderedRing`.
- Sign/order: `sign_eq_one_iff : p.sign = 1 ↔ 0 < toLex (toHahn p)`,
  `sign_eq_neg_one_iff : p.sign = -1 ↔ toLex (toHahn p) < 0`, `sign_eq_zero_iff : p.sign = 0 ↔ p = 0`,
  `sign_trichotomy`, `lt_def`, `le_def`, `lt_iff_sign`, `le_iff_sign`, `pos_iff_sign`,
  `toLexHahn_injective`, `toLexHahn_strictMono`, `toLexHahn_le_iff`, `toLexHahn_lt_iff`.
- Tests (`LeviCivita.Test`, all `Poly ℤ ℚ` unless noted):
  - `decide +kernel`: `eps_lt_one_thousandth` (`ε < C (1/1000)`), `eps_pos`, `eps_sq_lt_eps`,
    `ten_pow_nine_lt_H`, `eps_mul_H`, `one_add_eps_mul_one_sub_eps`, `H_sq_gt`,
    `neg_eps_lt_zero`, `eps_le_eps`, `not_H_le_eps`.
  - Γ = ℚ: `sqrt_eps_sq`, `eps_lt_sqrt_eps`.
  - plain `decide`: the primed versions `eps_lt_one_thousandth'` … `one_add_eps_mul_one_sub_eps'`
    under `attribute [local semireducible] Rat.add Rat.mul Rat.sub Rat.inv`.
  - plain `decide` with no attribute changes (`Poly ℤ ℤ`): `int_eps_mul_H`, `int_ten_pow_nine_lt_H`,
    `int_eps_pos`.
  - via the transported structure: `eps_sq_pos` (`pow_pos`), `toHahn_eps`.

### About plain `decide` over ℚ

Core marks `Rat.add`, `Rat.mul`, `Rat.sub` and `Rat.inv` `@[irreducible]`. The elaborator's
`decide` therefore cannot evaluate even `(1 : ℚ) + 1 = 2`, and this has nothing to do with
`Poly`. `decide +kernel` works as is. Plain `decide` works after the local `semireducible`
attribute; that attribute only affects elaboration and changes nothing the kernel accepts.
Over `R = ℤ`, plain `decide` works with no changes.

## `#print axioms` (exact output)

```
'LeviCivita.Poly.toHahn_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.instCommRing' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.sign_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.instLinearOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.instIsStrictOrderedRing' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Test.eps_lt_one_thousandth' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Test.int_eps_mul_H' depends on axioms: [propext, Quot.sound]
```

`lake build` prints the same information for every audited declaration, from `#assert_axioms`
in `LeviCivita/AxiomAudit.lean`. A negative test (a scratch file, not committed) confirmed that
`#assert_axioms` errors on `sorryAx`, on the auxiliary axiom `native_decide` now generates
(`foo._native.native_decide.ax_1_1`), and on a user `axiom`.

## Clean build time

`rm -rf .lake/build && time LAKE_ARTIFACT_CACHE=false lake build` (Mathlib from cache, only this
package rebuilt; `LAKE_ARTIFACT_CACHE=false` is needed because this machine's Lake artifact cache
otherwise *reuses* the outputs and the "clean" build takes 1 s):

```
Build completed successfully (1356 jobs).
LAKE_ARTIFACT_CACHE=false lake build  8.28s user 6.02s system 142% cpu 10.058 total
```

Each of the 8 package modules builds in under 2 s.

## Remaining / caveats

- **Performance (M7):** the list operations are quadratic. Plan: `Array` two-pointer merge and
  sort-then-combine multiplication, linked to the list spec by `@[csimp]` equality theorems.
  Binary `npow` too; `npow` is currently repeated multiplication, by structural recursion so the
  kernel can reduce it.
- `Repr` prints `Rat` coefficients as `(7 : Rat)/2`. Cosmetic.
- `Module R (Poly Γ R)` / `Algebra R (Poly Γ R)` are not yet declared. `SMul R` exists with
  `toHahn_smul`, so this is a short transport for M2. An `OrderRingHom` bundling of `toLexHahn` is
  also not declared yet.
- The files use the classic (non-`module`) header, so Lake warns that Mathlib "is designed for use
  with the module system". The warnings are harmless; converting is optional.
- CI was written but not run (nothing was pushed). The local equivalent (`lake build` plus the
  grep checks) passes.
- Not started (later milestones): accessors/standard part (M2), predicates (M3), `Approx`/truncation
  (M4), and the rest of plan §6.
