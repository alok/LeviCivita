# M2 notes: algebra structure, accessors, standard part, ε-AD

Branch `grokbot/hahn-m2`, stacked on `grokbot/hahn-rewrite` (M1). Same toolchain
(`leanprover/lean4:v4.35.0-rc4`, Mathlib master). Status: **all M2 deliverables done**.
The build has zero `sorry`, zero `native_decide`, no `implemented_by`/`extern`, and no new `axiom`.

## New files

| File | Contents |
|---|---|
| `LeviCivita/Poly/Algebra.lean` | `C_zero/one/add/mul`, `CHom : R →+* Poly Γ R`, `smul_eq_C_mul`, `instAlgebra : Algebra R (Poly Γ R)`, `toHahnAlg : Poly Γ R →ₐ[R] R⟦Γ⟧`, `toLexHahnHom : Poly Γ R →+*o Lex R⟦Γ⟧`, `toLexHahnEmb : Poly Γ R ↪o Lex R⟦Γ⟧`, `toLexHahn_abs` |
| `LeviCivita/Poly/Std.lean` | `coeff`, `leadExp`, `std`, `IsInfinitesimal`, `IsFinite` (decidable), closure lemmas, `finiteSubring`, `stdPart`, `infinitesimalIdeal`, order characterizations |
| `LeviCivita/Poly/Deriv.lean` | `toHahn_aeval`, Taylor/Hasse coefficients of `f (a + ε)`, ε-AD theorem, `dualDeriv` |
| `LeviCivita/TestM2.lean` | `#guard_msgs` evals and `decide` theorems, including `Γ = Lex (Fin 2 → ℤ)` (a new root of the default target) |

`LeviCivita/Poly.lean` imports the three new modules. `AxiomAudit.lean` imports `TestM2` and
audits every declaration listed below.

## Proven (namespace `LeviCivita.Poly` unless noted)

**Loose ends from M1**
- `C_zero`, `C_one`, `C_add`, `C_mul`, and `CHom` (with `CHom_apply`).
- `smul_eq_C_mul : r • p = C r * p`.
- `instAlgebra : Algebra R (Poly Γ R)`, with `algebraMap_apply : algebraMap R _ r = C r` (`rfl`).
  `Module R (Poly Γ R)` is `Algebra.toModule`, and its `•` is the computable one from M1.
- `toHahnAlg : Poly Γ R →ₐ[R] R⟦Γ⟧`, `toHahnAlg_apply`, `toHahnAlg_injective`.
- `toLexHahnHom : Poly Γ R →+*o Lex R⟦Γ⟧` (Mathlib's `OrderRingHom`), `toLexHahnHom_apply`,
  `toLexHahnHom_strictMono`, `toLexHahnHom_injective`.
- `toLexHahnEmb : Poly Γ R ↪o Lex R⟦Γ⟧` (`OrderEmbedding.ofStrictMono`). Mathlib has no bundled
  "ordered ring embedding" type, so the order embedding and the ordered ring hom are given separately.
- `toLexHahn_neg`, `toLexHahn_abs` (via `map_abs`).

**Accessors**
- `coeff_hahnL`, `coeff_eq : p.coeff g = (toHahn p).coeff g`, `coeff_injective`.
- `leadExp_eq_orderTop : p.leadExp = (toHahn p).orderTop`.
- `leadCoeff_eq_leadingCoeff : p.leadCoeff = (toHahn p).leadingCoeff`. This restates M1's
  `leadingCoeff_toHahnFun`.
- `coeff_zero/add/neg/sub/smul/single/C`, `leadExp_zero`, `leadExp_eq_top_iff`, `leadExp_single`,
  `coeff_eq_zero_of_lt_leadExp`, `coeff_leadExp` (coefficient at `leadExp` = `leadCoeff`),
  `lt_leadExp_of_coeff_eq_zero`.
- `HahnSeries.lt_orderTop_of_coeff_eq_zero` (small general Hahn lemma).
- `std_zero/add/neg/sub/C/one`, `std_ε`, `leadExp_ε`, `isInfinitesimal_ε` (given `0 < 1` in `Γ`).

**Finite and infinitesimal elements**
- `isInfinitesimal_iff_orderTop`, `isFinite_iff_orderTop`, `IsInfinitesimal.isFinite`.
- Closure:
  - `isInfinitesimal_zero`, `isFinite_zero`, `isFinite_one`, `isFinite_C`.
  - `IsInfinitesimal.add/neg/sub/mul`, `isInfinitesimal_neg`.
  - `IsInfinitesimal.mul_left` (finite × infinitesimal) and `IsInfinitesimal.mul_right`.
  - `IsFinite.add/neg/sub/mul`, `isFinite_neg`.
- `IsInfinitesimal.std_eq_zero`, `IsFinite.isInfinitesimal_sub_C_std` (`p - C p.std` is infinitesimal),
  `IsFinite.isInfinitesimal_iff_std_eq_zero`.
- `std_mul (hp : p.IsFinite) (hq : q.IsFinite) : (p * q).std = p.std * q.std`.
- `finiteSubring : Subring (Poly Γ R)`, `mem_finiteSubring`, decidable membership.
- `stdPart : finiteSubring →+* R` (computable), `stdPart_apply`, `stdPart_C`,
  `isInfinitesimal_sub_C_stdPart`, `mem_ker_stdPart : p ∈ RingHom.ker stdPart ↔ p.1.IsInfinitesimal`,
  `infinitesimalIdeal := RingHom.ker stdPart`, `mem_infinitesimalIdeal`.
- Order (`[LinearOrder R] [IsStrictOrderedRing R]`):
  - `lt_iff_exists_coeff`: `p < q` iff `p.coeff` is less than `q.coeff` at the first exponent where they differ.
  - `leadCoeff_pos_iff`, `leadExp_abs`, `isFinite_abs`, `isInfinitesimal_abs`.
  - `isFinite_iff_exists_abs_le : p.IsFinite ↔ ∃ r : R, |p| ≤ C r`.
  - `isInfinitesimal_iff_forall_abs_lt [DenselyOrdered R] : p.IsInfinitesimal ↔ ∀ r : R, 0 < r → |p| < C r`.

**ε-AD** (`Γ` any ordered cancel monoid with `One Γ` and hypothesis `h : (0 : Γ) < 1`; `R` any
`CommRing` with `DecidableEq`)
- `toHahn_aeval : toHahn (aeval x f) = aeval (toHahn x) f`.
- `HahnSeries.coeff_aeval_C_add_single_one`: in `R⟦Γ⟧`, the coefficient of `ε^(n•1)` in
  `f (C a + single 1 1)` is `(taylor a f).coeff n`.
- `coeff_aeval_C_add_ε : (aeval (C a + ε) f).coeff (n • 1) = (hasseDeriv n f).eval a`.
- `coeff_zero_aeval_C_add_ε : … .coeff 0 = f.eval a`, `std_aeval_C_add_ε`.
- **`coeff_one_aeval_C_add_ε : (aeval (C a + ε : Poly Γ R) f).coeff 1 = f.derivative.eval a`**.
- `dualDeriv f a := (f (C a + ε)).coeff 1` (computable), `dualDeriv_aeval`, and
  `dualDeriv_aeval_int` (`Γ = ℤ`, no side condition).

**Tests** (`LeviCivita.TestM2`, `P = Poly ℤ ℚ`)
- `decide +kernel`: `std_example`, `coeff_example`, `leadExp_example`, `isInfinitesimal_eps`,
  `not_isInfinitesimal_one`, `not_isFinite_H`, `isFinite_three_add_eps`,
  `not_isInfinitesimal_three_add_eps`, `isInfinitesimal_eps_sub_eps_sq`, `stdPart_three_add_eps`,
  `ad_example_kernel` (`dualDeriv (x³+2x) 2 = 14`), `cube_expansion`.
- plain `decide` (`Poly ℤ ℤ`): `int_isInfinitesimal_eps`, `int_not_isFinite_H`.
- via theorems: `stdPart_mul_example` (uses `map_mul`), `abs_eps_lt`, `one_sub_eps_bounded`,
  `ad_example_theorem` (via `dualDeriv_aeval_int` and `simp`/`norm_num`, no `Poly` evaluation),
  `aeval_eq_direct`.
- `Γ = Lex (Fin 2 → ℤ)`, `ε₁ = single (toLex ![1,0]) 1`, `ε₂ = single (toLex ![0,1]) 1`:
  - `decide +kernel`: `eps1_lt_eps2`, `eps1_pos`, `eps1_mul_eps2_pos`, `eps1_mul_eps2_lt_eps1`,
    `eps1_lt_eps2_pow` (`ε₁ < ε₂^5`), `eps2_lt_one_thousandth`, `eps1_isInfinitesimal`.
  - plain `decide` with `ℤ` coefficients: `int_eps1_lt_eps2`, `int_eps1_mul_eps2_pos`.
  - `#eval` checks of the same.

## Design decisions / open questions

1. **`coeff` sums all matching entries.** `coeffL g ((e,c)::l) = (if g = e then c else 0) + coeffL g l`.
   It doesn't stop at the first match or use sortedness. This makes `(hahnL l).coeff g = coeffL g l`
   true for *every* raw list, by a two-line induction, which is the same "invariant-free denotation"
   trick M1 uses. It costs a full list traversal. An early-exit version can be attached later
   with `@[csimp]`.
2. **`IsInfinitesimal` characterization needs `DenselyOrdered R`.** The statement asked for
   (`p` infinitesimal ↔ `∀ r > 0, |p| < C r`) is **false** for `R = ℤ`. Counterexample:
   `1 - ε : Poly ℤ ℤ` is not infinitesimal, but `|1 - ε| = 1 - ε < C r` for every integer `r ≥ 1`.
   The theorem therefore assumes `[DenselyOrdered R]`, which every ordered field satisfies.
   The `→` direction holds without it.
3. **`IsFinite` characterization needs no extra hypothesis:**
   `IsFinite p ↔ ∃ r, |p| ≤ C r` holds over any strictly ordered ring (witness `r = std |p| + 1`).
4. **Finite/infinitesimal and `stdPart` do not need an order on `R`.** They are defined by
   `leadExp`, and `finiteSubring`/`stdPart`/`std_mul` hold for any `CommRing R`. Only the
   `|p| ≤ C r` characterizations need `LinearOrder R`. `Γ` only needs to be an ordered cancel
   additive monoid (`0 ≤ leadExp` makes sense with `WithTop Γ`), so `ℤ`, `ℚ` and
   `Lex (Fin k → ℤ)` all work.
5. **`std_mul` proof.** It writes `pq - C(ab) = (p - C a) q + C a (q - C b)` and uses the ideal
   property of infinitesimals. There's no convolution argument at the coefficient level.
6. **ε-AD in full generality.** `Polynomial.taylor` turns `f (a + ε)` into `∑ (taylor a f).coeff i • ε^i`.
   Since `n ↦ n • 1` is injective when `0 < 1`, the coefficient of `ε^(n•1)` is exactly the
   `n`-th Taylor (Hasse-derivative) coefficient. So the theorem covers all `n`, not just `0`
   and `1`, for any `Γ` with `0 < 1`. The hypothesis is explicit (`h : (0 : Γ) < 1`), not a
   typeclass, so exponent groups like `Lex (Fin 2 → ℤ)` with an unusual `1` aren't forced
   through a class.
7. **`dualDeriv` is generic in `Γ`** (not only `ℤ`). The `ℤ` correctness theorem is
   `dualDeriv_aeval_int`.
8. **`Lex (Fin k → ℤ)` needs a computable `LinearOrder`.** Mathlib's `Pi.Lex.linearOrder` is
   `noncomputable`: its decidability is `Classical.decRel`. With it, `Poly (Lex (Fin 2 → ℤ)) R`
   can't be `#eval`ed or `decide`d, since `insertTerm` branches on `e < e'`. `TestM2` installs
   `lexLinearOrder` (priority high), built with `linearOrderOfSTO` from the same strict order,
   deciding `<` by `Fintype` search. Its `PartialOrder` is definitionally Mathlib's, so Mathlib's
   `Pi.Lex.isOrderedAddCancelMonoid` is found unchanged. With it, `decide +kernel` works (and
   plain `decide` with `ℤ` coefficients). It's currently a test-local instance. If multi-ε becomes a
   library feature, it should move into the library, ideally as a type synonym (e.g.
   `MultiEps k := Lex (Fin k → ℤ)`) to avoid instance overlap, or upstream as a computable
   `Pi.Lex` order for `Fintype` index types.
9. **No `Repr` for `Lex (Fin 2 → ℤ)`**, so `Poly G2 ℚ` values are inspected through `coeff`/`decide` in
   `#eval` rather than printed.
10. **Not done (optional):** relating `IsInfinitesimal` to Mathlib's `ArchimedeanClass` on
    `Lex R⟦Γ⟧` (`p` infinitesimal ↔ `ArchimedeanClass.mk 1 < ArchimedeanClass.mk p`). That needs
    `R` Archimedean and is left for M3. `stdPart` isn't extended to a partial function on all of
    `Poly` (e.g. `Option R`); `std` is the raw total accessor.

## `#print axioms` (exact output)

```
'LeviCivita.Poly.instAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.toHahnAlg' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.toLexHahnHom' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.leadExp_eq_orderTop' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.coeff_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.std_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.stdPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.mem_ker_stdPart' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.isFinite_iff_exists_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.isInfinitesimal_iff_forall_abs_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.coeff_aeval_C_add_ε' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.coeff_one_aeval_C_add_ε' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.dualDeriv' depends on axioms: [propext, Quot.sound]
'LeviCivita.TestM2.ad_example_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.TestM2.eps1_mul_eps2_lt_eps1' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.TestM2.int_eps1_lt_eps2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake build` prints the same line for every declaration in `AxiomAudit.lean`, about 120 in total.
`#assert_axioms` would fail the build on anything outside `{propext, Classical.choice, Quot.sound}`.

## `lake build` (clean)

`rm -rf .lake/build && time LAKE_ARTIFACT_CACHE=false lake build` (Mathlib from cache):

```
✔ [1478/1490] Built LeviCivita.Util.AssertAxioms (737ms)
⚠ [1479/1490] Built LeviCivita.Poly.Basic (1.5s)
✔ [1480/1490] Built LeviCivita.Poly.Hahn (1.7s)
⚠ [1481/1490] Built LeviCivita.Poly.Order (1.6s)
⚠ [1482/1490] Built LeviCivita.Poly.Algebra (1.5s)
⚠ [1483/1490] Built LeviCivita.Poly.Std (1.9s)
⚠ [1484/1490] Built LeviCivita.Poly.Deriv (1.5s)
✔ [1485/1490] Built LeviCivita.Poly (1.3s)
✔ [1486/1490] Built LeviCivita (1.5s)
✔ [1487/1490] Built LeviCivita.Test (1.8s)
⚠ [1488/1490] Built LeviCivita.TestM2 (2.1s)
ℹ [1489/1490] Built LeviCivita.AxiomAudit (1.5s)
Build completed successfully (1490 jobs).
LAKE_ARTIFACT_CACHE=false lake build  14.52s user 8.89s system 146% cpu 15.996 total
```

All `⚠` warnings are the module-system notice ("imports … from package `mathlib`, which is
designed for use with the module system"). There are no other warnings. Checks on the log:
`declaration uses 'sorry'` has 0 matches, and the CI forbidden-construct grep (`axiom`,
`implemented_by`, `extern`, `native_decide`) finds nothing in `LeviCivita/`.
