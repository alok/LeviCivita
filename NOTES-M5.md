# M5 notes: a computable multi-index exponent type, several independent infinitesimals

Branch `grokbot/hahn-m5-multieps`, stacked on `grokbot/hahn-m4`. Same toolchain
(`leanprover/lean4:v4.35.0-rc4`, Mathlib master `49fd9de`). Status: **all M5 deliverables
done**. That includes the optional SoS variant: all four predicates are covered, with sign
agreement for `orient2d`/`incircle`. The build has zero `sorry`, zero `native_decide`, no
`implemented_by`/`extern`, and no new `axiom`.

## New files

| File | Contents |
|---|---|
| `LeviCivita/ForMathlib/Order/FinLex.lean` | imports only Mathlib. `Fin.lexCmp` and its specs; `FinLex k α` with computable `LinearOrder`, algebra, `Repr`, `single`; `toLexOrderAddIso : FinLex k α ≃+o Lex (Fin k → α)`; computable orders on Mathlib's own `Lex (Fin k → α)` and `Lex (∀ i, β i)` (finite `ι`), proved equal to `Pi.Lex.linearOrder` |
| `LeviCivita/Poly/MultiEps.lean` | `MultiEps k := FinLex k ℤ`, `epsI i`, `epsI_pos`, `epsI_lt_epsI`, `isInfinitesimal_epsI` |
| `LeviCivita/Geometry/SoSMulti.lean` | SoS with one infinitesimal per coordinate: key lemma without a degree bound, nonvanishing for `orient2d/3d`, `incircle`, `insphere`, sign agreement |
| `LeviCivita/TestM5.lean` | `#guard_msgs` evals, `decide` tests, and the **upstream simulation** (new root of the default target) |
| `UPSTREAM.md` | the proposed Mathlib PR |

Changed: `TestM2` (now uses `MultiEps 2`; local `lexLinearOrder` removed), `SoS.lean`
(`sign_of_isFinite_of_std_ne_zero` and `sign_eq_signOf_leadCoeff` generalized from `Poly ℤ R`
to any `Γ`, with no change at call sites), `AxiomAudit`, `bench/Bench.lean`, root imports,
`lakefile.lean` (root `TestM5`), README.

## Proven / defined

### `FinLex.lean` (namespaces `Fin`, `FinLex`, `Pi.Lex`)

- `Fin.lexCmp : (Fin k → α) → (Fin k → α) → Ordering` (structural recursion on `k`), with
  `lexCmp_zero`, `lexCmp_succ`, **`lexCmp_eq_eq_iff`** (`= .eq ↔ f = g`),
  **`lexCmp_eq_lt_iff`** (`= .lt ↔ ∃ i, (∀ j < i, f j = g j) ∧ f i < g i`) and `lexCmp_swap`.
- Compiled-code support, all proved: `Fin.lexCmpLoop`, `lexCmpLoop_eq`, `lexCmpFast`, and
  `@[csimp] lexCmp_eq_lexCmpFast`, which gives a linear loop instead of `Fin.tail` recursion.
  Also `FinLex.tabulate`, `tabulateImpl`, and `@[csimp] tabulate_eq_tabulateImpl`, which stores
  results of `+ - •` as an `Array`. See design decision 4.
- `structure FinLex (k) (α) where toFinLex :: ofFinLex : Fin k → α`, with `FunLike`, `ext`,
  `coe_toFinLex`, `toFinLex_coe`, `toFinLex_inj`, `equivFun`, `Inhabited`, `Nonempty`, and
  `Repr` (prints `![1, 0]`).
- Order:
  - `instPartialOrder`: pulled back from Mathlib's `Lex (Fin k → α)` (`[PartialOrder α]`);
  - **`lt_iff_toLex_lt`**, **`le_iff_toLex_le`**, **`lt_iff_exists`** (all `Iff.rfl`), and
    `le_iff_eq_or_lt`;
  - `lexCmp_eq_lt_iff`, `lexCmp_eq_eq_iff`, `lexCmp_ne_gt_iff`, `lt_trichotomy'`;
  - computable **`decidableLE`, `decidableLT`, `decidableEq`** and **`instLinearOrder`**
    (`[LinearOrder α]`), with `compare_eq_lexCmp : compare x y = Fin.lexCmp ⇑x ⇑y` (`rfl`);
  - `toLex_strictMono`.
- Algebra (pointwise, all `rfl` lemmas):
  - `Zero/Add/Neg/Sub/SMul` with `coe_*`, `*_apply` and `toFinLex_*` simp lemmas;
  - `AddMonoid`, `AddCommMonoid`, `AddGroup`, `AddCommGroup` (`Function.Injective.*`);
  - `IsOrderedCancelAddMonoid` and `IsOrderedAddMonoid` (`[AddCommMonoid α] [PartialOrder α]
    [IsOrderedCancelAddMonoid α]`);
  - `evalAddMonoidHom`.
- Basis: `single i a`, `coe_single`, `single_apply`, `single_apply_self`,
  `single_apply_of_ne`, `single_injective`, `single_add`, `single_pos`, and **`single_lt_single`**
  (`i < j → 0 < a → single j a < single i a`).
- Transfer: **`toLexOrderAddIso : FinLex k α ≃+o Lex (Fin k → α)`** (Mathlib's
  `OrderAddMonoidIso`; both maps are the identity on tuples), `toLexOrderIso`, and the apply
  lemmas.
- For upstream, on Mathlib's own types:
  - `Pi.Lex.decidableLTFin`;
  - `Pi.Lex.linearOrderFin` with **`linearOrderFin_eq : linearOrderFin = Pi.Lex.linearOrder`**;
  - the general `Pi.Lex.decidableLTOfFintype` (`[Fintype ι] [LinearOrder ι]`, dependent
    `β`) and `linearOrderOfFintype` with **`linearOrderOfFintype_eq`**.

### `MultiEps`

`epsI i := single (FinLex.single i 1) 1`. Then `epsI_pos`, `isInfinitesimal_epsI`, and
**`epsI_lt_epsI : i < j → epsI i < epsI j`**. So `epsI 0` is the smallest; in M2 notation,
`ε₁ = epsI 0` is infinitely smaller than `ε₂ = epsI 1`.

### SoS with independent infinitesimals (`LeviCivita.Geometry`)

Coordinate `(i, j)` is perturbed by `epsI (finProdFinEquiv (i, j))` in
`Poly (MultiEps (n * d)) R` (`multiPoint`).

- `multiSubst w : MvPolynomial σ R →ₐ[R] Poly (MultiEps N) R`, sending `X k ↦ epsI (w k)`.
  `multiExpo w m = ∑ mₖ • e_{w k}`. `toHahn_multiSubst` (proved via `prod_single_pow_gen`, a
  `Γ`-generic version of M3's lemma) computes its image.
- `multiExpo_apply`: `multiExpo w m (w k) = m k`. **`multiExpo_injective`** follows for any
  degrees.
- **`multiSubst_ne_zero (hw : Injective w) (hD : D ≠ 0) : multiSubst w D ≠ 0`**. Unlike M3's
  `sosSubst_ne_zero`, there is no degree hypothesis.
- **`orient2dSoSMulti_ne_zero`, `orient3dSoSMulti_ne_zero`** (any nontrivial `R`, distinct
  indices) and **`incircleSoSMulti_ne_zero`, `insphereSoSMulti_ne_zero`** (`(2 : R) ≠ 0`).
  There is no base `b`, so no `b ≥ 4`.
- `isFinite_multiPoint`, `std_multiPoint`, `orient2dSoSMulti_std`, `incircleSoSMulti_std`, and
  **`orient2dSoSMulti_sign`**, **`incircleSoSMulti_sign`**: on nondegenerate input the SoS sign
  is the exact sign.
- `orient2dSoSMulti_swap₁₂`, `orient2dSoSMulti_sign_ne_zero`.

### Tests

- `TestM2`, switched to `MultiEps 2` with the **same theorem names**: `eps1_lt_eps2`,
  `eps1_pos`, `eps1_mul_eps2_pos`, `eps1_mul_eps2_lt_eps1`, `eps1_lt_eps2_pow`,
  `eps2_lt_one_thousandth`, `eps1_isInfinitesimal` (`decide +kernel`, `ℚ`), and
  `int_eps1_lt_eps2`, `int_eps1_mul_eps2_pos` (plain `decide`, `ℤ`).
  New: `eps1_eq_epsI`, `int_eps1_lt_eps2_pow` (plain `decide`), `eps1_lt_eps2'` (via
  `epsI_lt_epsI`), and a `Repr` check: `#eval ε₁ + ε₂ + 2 * ε₁ * ε₂` prints
  `1 ε^![0, 1] + 1 ε^![1, 0] + 2 ε^![1, 1]`.
- `TestM5`:
  - `FinLex` evals and plain-`decide` tests (`finLex_lt`, `finLex_le`, `finLex_ne`,
    `finLex_single_lt`, `finLex_min`), `finLex_transfer` (via `toLexOrderIso`), and a compiled
    `k = 2000` comparison;
  - multi-ε SoS by `decide +kernel`: `multi_collinear`, `multi_collinear_swap`,
    `multi_coincident`, `multi_generic`, `multi_cocircular`;
  - via theorems: `multi_generic'`, `multi_ne_zero`, `multi_sign_ne_zero`,
    `multi_incircle_ne_zero`;
  - evals for `orient3d`/`insphere`;
  - **upstream simulation**: `attribute [-instance] Pi.Lex.linearOrder`, then the proposed
    instance-argument `simLinearOrder` and `Pi.Lex.decidableLTOfFintype` as a local instance.
    The M2 tests pass on Mathlib's own `Lex (Fin 2 → ℤ)`: `sim_eps1_lt_eps2`,
    `sim_eps1_lt_eps2_pow` (`decide +kernel`), `sim_int_eps1_lt_eps2`, `sim_lex_lt` (plain
    `decide`), and `sim_linearOrder_eq`.

## Design decisions / open questions

1. **A one-field structure, not a type synonym.** A synonym of `Lex (Fin k → α)` unfolds to a
   type that already has Mathlib's noncomputable `LinearOrder`. A synonym of `Fin k → α` exposes
   the pointwise Pi order. Either way, two non-defeq instances would be reachable. The structure
   has only our instances, and the transfer is the bundled `≃+o`. Upstreaming the *type* isn't
   the plan anyway (`UPSTREAM.md`): the Mathlib PR fixes `Pi.Lex.linearOrder` itself, and
   `FinLex` stays a LeviCivita convenience.
2. **`FinLex` is generic in `α`; `MultiEps k := FinLex k ℤ` lives on the LeviCivita side**
   (`Poly/MultiEps.lean`), since it doesn't belong in Mathlib.
3. **Order defined by pullback, decided by `lexCmp`.** `<`/`≤` *are* Mathlib's (so the order
   lemmas and the iso are `Iff.rfl`). Decidability, `min`, `max` and `compare` come from
   `Fin.lexCmp`. `Fin.lexCmp` uses structural recursion on `k` (peel off index `0`, recurse on
   `Fin.tail`), so `decide` reduces in the kernel and in `whnf`. Plain `decide` works for
   `ℤ`-valued tuples and for `Poly (MultiEps 2) ℤ`.
4. **Two `@[csimp]` lemmas for compiled code.** Both are proved, so they're not
   `implemented_by`.
   - `lexCmp` on `Fin.tail` closures is quadratic in `k` when run, so the compiler uses the
     index loop `lexCmpFast`.
   - Pointwise `+` on closures builds closure trees that every comparison re-evaluates.
     `tabulate` (identity on `toFinLex` for the kernel) stores results in an `Array` in
     compiled code. **Pitfall found while doing this:** `FinLex` is a *trivial structure*, so the
     compiler erases it to its function field and **eta-expands lambdas that return a
     `FinLex`**. With `instance : Add := ⟨fun x y => tabulate …⟩`, the tabulation moved under
     the index binder and was recomputed on every read. That is exponential in the nesting depth:
     a chain of 6 additions of 15-vectors took over 40 s. The instances therefore point to
     top-level defs (`⟨FinLex.add⟩`), whose code returns the closure built by `tabulateImpl`. A
     user lambda returning a `FinLex` could still trigger the same eta-expansion. The robust fix
     is a non-trivial (array-backed) representation; see future work.
5. **Axioms.** `FinLex.instLinearOrder`, `decidableLT` etc. list `Classical.choice`. It occurs
   only in the *proof* components (`decidable_of_iff _ lexCmp_eq_lt_iff`, through Mathlib
   lemmas used by `simp`/`omega`), never in the data: `#eval` and `decide` work. As a
   consequence, `orient2dSoSMulti` lists `Classical.choice`, while M3's `orient2dSoS` lists only
   `[propext, Quot.sound]`.
6. **`MultiEps (n * d)`, not `MultiEps N` with an arbitrary injection.** The index map is
   `finProdFinEquiv`, so `idx (i, j) = j + d i`, as in M3. Any injective `w` works for the key
   lemma.
7. **The multi-ε scheme is a different perturbation from M3's, so degenerate signs can differ.**
   In M3, `ε^(4^idx)` puts the largest perturbation at index `0`. Here `epsI 0` is the
   *smallest* (`epsI_lt_epsI`). On the M3 test configuration `pts` (collinear `0,1,2`), M3 gives
   `-1` and multi-ε gives `+1`. Both are consistent SoS schemes: antisymmetric, nonzero, and
   equal to the exact sign when that is nonzero. To make them agree, use
   `idx' = Fin.rev ∘ finProdFinEquiv`. That changes only the exponent map, not the proofs; we
   kept the natural order.
8. **`(2 : R) ≠ 0` remains for `incircle`/`insphere`.** It comes from the evaluation certificate
   (M3 note 4), not from the perturbation.
9. **Sign agreement** is proved for `orient2d` and `incircle`. `orient3d`/`insphere` would be
   the same five lines (`*_isFinite`, `*_std`, `*_sign`) and are not written out. No lazy
   multi-ε variant: `LazySign`'s truncation threshold and step function are tied to `Γ = ℤ`'s
   `sqStep`, so it isn't trivial.
10. **Mathlib-readiness of `FinLex.lean`:** `autoImplicit false`, docstrings on every public
    declaration, and no `set_option`. It is not yet a `module` file (none of this project is),
    hence the "designed for use with the module system" warnings. See `UPSTREAM.md`.

## Benchmark

Run with `lake env lean --run bench/Bench.lean <points> <queries> <grid> <multiQueries>` on an
Apple M4 Max, in the Lean interpreter (as in M3). The multi-ε predicates are slow, so they run
on the first `multiQueries` queries only. On that same subset the `b`-power SoS (`b = 4`) is
re-timed, and sign agreement between the two schemes is counted. µs per query:

| | n = 100, run 1 (coords < 10⁶) | n = 100, run 2 (16×16 grid) | n = 1000, run 1 | n = 1000, run 2 |
|---|---|---|---|---|
| `orient2d` exact `ℤ` | 1.76 | 1.46 | 1.76 | 1.46 |
| `orient2d` SoS `b`-power, `Poly ℤ ℤ` | 45 (subset: 50) | 45 (subset: 46) | 49 (subset: 57) | 47 (subset: 53) |
| `orient2d` lazy SoS | 23 | 24 | 23 | 28 |
| **`orient2d` SoS multi-ε, `Poly (MultiEps 2n) ℤ`** | **5 333** | **4 885** | **56 198** | **51 775** |
| `incircle` exact `ℤ` | 4.0 | 2.4 | 4.2 | 2.3 |
| `incircle` SoS `b`-power | 3 984 (subset: 4 021) | 3 622 (subset: 3 330) | 3 977 (subset: 4 150) | 3 711 (subset: 3 609) |
| `incircle` lazy SoS | 112 | 124 | 108 | 139 |
| **`incircle` SoS multi-ε** | **534 956** | **456 599** | **8 016 049** | **7 173 045** |
| multi-ε subset size; sign agreement | 20; 20/20, 20/20 | 20; 20/20, 20/20 | 5; 5/5, 5/5 | 5; 5/5, 5/5 |

Degenerate queries in the full runs (out of 1000): `n = 100` grid has 23 `orient2d` and 23
`incircle`; `n = 1000` grid has 26 and 19. The small multi-ε subsets happened to contain no
degenerate query, so their 100% agreement only shows agreement with the exact sign. On
degenerate input the two schemes can differ (design decision 7, e.g. `TestM5.multi_collinear`).

Honest reading:
- **Multi-ε is about 100× slower than the `b`-power version at `n = 100`, and about 1000×
  (`orient2d`) to 2000× (`incircle`) slower at `n = 1000`.** The cost grows linearly with
  `N = 2n`: each comparison or addition of exponents touches all `N` entries, while the
  `b`-power version handles one big integer. At `n = 1000` that integer has at most ~4000 bits,
  i.e. about 60 machine words, against 2000 `Int`s here. The `b`-power cost is flat in `n` at
  these sizes, and the multi-ε cost goes up 10× from `n = 100` to `n = 1000`.
- Before `tabulate`/`lexCmpFast` (design decision 4) it was much worse: a single `insphere` on 5
  points took 10 s. A first, eta-expanded `tabulate` was exponential.
- The multi-ε scheme's *proof* advantage (no degree bound, no base `b`) is real. Its runtime
  needs a sparse exponent representation: every exponent here has at most `deg ≤ 4` nonzero
  entries. That is future work, as requested; it was not attempted.
- Run `n = 10⁴` (M3's size) was not run for multi-ε: with `N = 2·10⁴`, one `incircle` query
  would take about 80 s.

## `#print axioms` (exact output, from `lake build`)

```
'Fin.lexCmp_eq_lt_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fin.lexCmp_eq_lexCmpFast' depends on axioms: [propext, Quot.sound]
'FinLex.ext' depends on axioms: [Quot.sound]
'FinLex.lt_iff_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'FinLex.decidableLT' depends on axioms: [propext, Classical.choice, Quot.sound]
'FinLex.instLinearOrder' depends on axioms: [propext, Classical.choice, Quot.sound]
'FinLex.instAddCommGroup' depends on axioms: [propext, Quot.sound]
'FinLex.instIsOrderedCancelAddMonoid' depends on axioms: [propext, Classical.choice, Quot.sound]
'FinLex.toLexOrderAddIso' depends on axioms: [propext, Classical.choice, Quot.sound]
'FinLex.tabulate_eq_tabulateImpl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Pi.Lex.linearOrderFin_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Pi.Lex.decidableLTOfFintype' depends on axioms: [propext, Classical.choice, Quot.sound]
'Pi.Lex.linearOrderOfFintype_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.epsI_lt_epsI' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.multiExpo_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.multiSubst_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.orient2dSoSMulti' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.orient2dSoSMulti_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.incircleSoSMulti_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.insphereSoSMulti_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.orient2dSoSMulti_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.incircleSoSMulti_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.TestM2.eps1_lt_eps2' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.TestM2.int_eps1_lt_eps2' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.TestM5.multi_collinear' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.TestM5.multi_cocircular' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.TestM5.sim_eps1_lt_eps2' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.TestM5.sim_int_eps1_lt_eps2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All M5 declarations (instances, the iso, the `lt_iff` lemmas, the `@[csimp]` lemmas, the SoS
theorems, the tests) are listed in `AxiomAudit.lean`'s M5 section. `#assert_axioms` fails the
build on anything outside `{propext, Classical.choice, Quot.sound}`. The ForMathlib file does
not import `AssertAxioms`; it is audited from `AxiomAudit.lean`.

## `lake build` (clean)

`rm -rf .lake/build && time LAKE_ARTIFACT_CACHE=false lake build` (Mathlib from cache):

```
⚠ [1696/1720] Built LeviCivita.ForMathlib.Order.FinLex (1.3s)
✔ [1704/1720] Built LeviCivita.Poly.MultiEps (1.3s)
✔ [1708/1720] Built LeviCivita.Geometry.SoSMulti (1.7s)
✔ [1711/1720] Built LeviCivita.TestM2 (1.9s)
✔ [1718/1720] Built LeviCivita.TestM5 (7.0s)
ℹ [1719/1720] Built LeviCivita.AxiomAudit (1.4s)
Build completed successfully (1720 jobs).
LAKE_ARTIFACT_CACHE=false lake build  44.76s user 16.81s system 246% cpu 25.003 total
```

`TestM5`'s 7 s is mostly the compiled multi-ε `insphere` `#eval` (≈ 1.9 s) and the kernel
`decide`s on `MultiEps 10`. The only warnings are the module-system notices. Checks:
- `declaration uses 'sorry'` has 0 matches;
- the CI forbidden-construct grep (`axiom`, `implemented_by`, `extern`, `native_decide`) is
  clean on `LeviCivita/`, `LeviCivita.lean` and `bench/`;
- `lake env lean bench/Bench.lean` elaborates.

## Future work

- **Sparse exponents.** A dense `2n`-vector per exponent makes every comparison and addition
  `O(n)`; see the benchmark. A sparse `FinLex` (sorted list of nonzero `(index, value)` pairs,
  ordered by the first differing index) would make both cost proportional to the support, which
  is at most the degree of the monomial. An array-backed (non-trivial-structure) representation
  would also remove the eta-expansion pitfall of note 4.
- The Mathlib PR from `UPSTREAM.md`.
- Sign agreement for `orient3dSoSMulti`/`insphereSoSMulti`, and a lazy multi-ε variant.
