# M3 notes: exact geometric predicates, Simulation of Simplicity, lazy sign

Branch `grokbot/hahn-m3`, stacked on `grokbot/hahn-m2`. Same toolchain
(`leanprover/lean4:v4.35.0-rc4`, Mathlib master). Status: **all M3 deliverables done**,
including the optional ones (SoS for `orient3d`, `incircle`, `insphere`; lazy `incircle`).
The build has zero `sorry`, zero `native_decide`, no `implemented_by`/`extern`, and no new
`axiom`.

## New files

| File | Contents |
|---|---|
| `LeviCivita/Geometry/Predicates.lean` | `det3`, `det4`, `orient2d`, `orient3d`, `incircle`, `insphere`; determinant specs; antisymmetry; translation invariance; naturality along ring homs |
| `LeviCivita/Geometry/SoS.lean` | base-`b` digit lemmas, the key lemma `sosSubst_ne_zero`, degree bookkeeping (`DegLe`, `DegBd`), `sosPoint`, the four `…SoS` predicates, nonvanishing, sign agreement, relabeling |
| `LeviCivita/Geometry/LazySign.lean` | `Poly.truncLT`, `Poly.mulTrunc` and their Hahn specs, `truncLT_mul`, `LazySign.Expr`, `evalTrunc`, `lazySign`, the driver `lazySignIter`, `orient2dLazy`, `incircleLazy` |
| `LeviCivita/Geometry.lean` | imports the three modules; `LeviCivita.lean` imports it |
| `LeviCivita/TestM3.lean` | `#guard_msgs` evals and `decide` theorems (new root of the default target) |
| `bench/Bench.lean` | benchmark script, not part of `lake build` (CI only elaborates it) |

## Proven

### Predicates (`LeviCivita.Geometry`)

The formulas are Shewchuk's, written relative to the last point:
`orient2d a b c = (a₀-c₀)(b₁-c₁) - (a₁-c₁)(b₀-c₀)`, `orient3d a b c d = det3 (a-d; b-d; c-d)`,
`incircle` and `insphere` with the lifted column `|p - last|²`. They are defined for any type
with `+ - *` (`[Add K] [Sub K] [Mul K]`), so one definition runs on `ℤ`, `ℚ`, `Poly Γ R`,
`Float` (benchmark) and on expression trees (`LazySign.Expr`). Everything below is for a
commutative ring `K`.

- Determinant specs: `orient2d_eq_det` (3×3), `orient3d_eq_det` (4×4), `incircle_eq_det` (4×4),
  `insphere_eq_det` (5×5). Each says the formula equals `Matrix.det` of the standard matrix,
  rows `(p, 1)` or `(p, |p|², 1)`. All four are proved with `det_succ_row_zero` + `simp` + `ring`.
- Antisymmetry: `orient2d_swap₁₂`, `orient2d_swap₂₃`, `orient2d_swap₁₃`, `orient2d_rotate`,
  `orient3d_swap₁₂`, `orient3d_swap₂₃`, `orient3d_swap₃₄`, `incircle_swap₁₂`, `incircle_swap₃₄`,
  `insphere_swap₁₂`, `insphere_swap₄₅`.
- Translation invariance: `orient2d_add_const`, `orient3d_add_const`, `incircle_add_const`,
  `insphere_add_const`.
- Naturality, for any `RingHomClass` map `f`: `map_det3`, `map_det4`, `map_orient2d`,
  `map_orient3d`, `map_incircle`, `map_insphere`. For example
  `f (orient2d a b c) = orient2d (f ∘ a) (f ∘ b) (f ∘ c)`.
  SoS uses these along three maps: `MvPolynomial.aeval` (the substitution), `MvPolynomial.eval`
  (the nonvanishing certificate) and `stdPart` / `Subring.subtype` (sign agreement).

### SoS (`LeviCivita.Geometry`)

Perturbation: `sosPoint b x i j = C (x i j) + single (b ^ (j + d·i)) 1 : Poly ℤ R`, so
coordinate `j` of point `i` gets `ε^(b^(j + d i))`. `sosIdx (i, j) = j + d·i` is
`finProdFinEquiv`, so it is injective (`sosIdx_injective`). The predicates are
`orient2dSoS b x i k l`, `orient3dSoS b x i k l m`, `incircleSoS b x i k l m`,
`insphereSoS b x i k l m o`. All are computable.

- **Key lemma** `sosSubst_ne_zero`: if `w` is injective, `D ≠ 0`, and every monomial of `D`
  has all exponents `< b`, then `aeval (X k ↦ ε^(b^(w k))) D ≠ 0`.
  - `toHahn_sosSubst` writes the image as `∑ₘ single (sosExpo b w m) (D.coeff m)`.
  - `sosExpo_injOn` shows distinct monomials have distinct exponents. It is base-`b` digit
    uniqueness: `digit_sum_lt` and `digit_extract`, where
    `(∑ dᵢ bʷ⁽ⁱ⁾) / bʷ⁽ᵏ⁾ % b = d_k`.
- **Nonvanishing** (any input, even degenerate; pairwise distinct indices; `R` nontrivial):
  - `orient2dSoS_ne_zero (hb : 2 ≤ b)`,
  - `orient3dSoS_ne_zero (hb : 2 ≤ b)`,
  - `incircleSoS_ne_zero (hb : 4 ≤ b) (h2 : (2 : R) ≠ 0)`,
  - `insphereSoS_ne_zero (hb : 4 ≤ b) (h2 : (2 : R) ≠ 0)`.

  Signs: `orient2dSoS_sign_ne_zero` and `orient3dSoS_sign_ne_zero` (`sign ≠ 0`).

  The proof has three steps, with `D` the predicate on symbolic points `C (x i j) + X (i, j)`:

  1. `D ≠ 0`. Evaluating at `X (i,j) := t i j - x i j` gives the predicate at points `t`. For
     `orient2d`/`orient3d`, `t` is the standard simplex and the value is `1`. For
     `incircle`/`insphere` the value is `2`.
  2. Degree bound, via `DegLe`/`DegBd`. Column `j` of the matrix only involves the variables of
     coordinate `j`, so the determinant is multilinear in them: degree `≤ 1` for `orient`. A
     lifted column adds `2`, giving degree `≤ 3` for `incircle`/`insphere`.
  3. The key lemma, applied through `map_orient2d` etc. (`sosSubst_mvPoint`).
- **Sign agreement** (no distinctness needed; `0 < b`). If the unperturbed value is nonzero,
  the SoS sign equals its sign:
  - `orient2dSoS_sign`, `orient3dSoS_sign`, `incircleSoS_sign`, `insphereSoS_sign`. For example,
    `orient2d (x i) (x k) (x l) ≠ 0 → (orient2dSoS b x i k l).sign = signOf (orient2d …)`,
    and `signOf_int : signOf r = r.sign`.
  - Proof: the perturbed points lie in `finiteSubring` (`isFinite_sosPoint`), and
    `std_sosPoint` says their standard parts are the inputs. Naturality along `stdPart` gives
    `orient2dSoS_std : (orient2dSoS b x i k l).std = orient2d (x i) (x k) (x l)`.
  - `sign_of_isFinite_of_std_ne_zero`: a finite element with nonzero standard part has it as
    its leading coefficient.
- **Relabeling**: `orient2dSoS_swap₁₂`, `orient2dSoS_swap₂₃`, `orient3dSoS_swap₁₂`. Also
  `sign_neg : (-p).sign = -p.sign` and `orient2dSoS_sign_swap₁₂` (swapping two points flips the
  SoS sign).

### Truncation and lazy sign (`LeviCivita.Poly`, `LeviCivita.LazySign`)

- `truncLT c p` keeps the terms with exponent `< c` (a list filter).
  - `toHahn_truncLT : toHahn (p.truncLT c) = HahnSeries.truncLT c (toHahn p)`. Mathlib master
    has `HahnSeries.truncLT`, so the spec is the Mathlib notion.
  - `coeff_truncLT`, `truncLT_add`, `truncLT_neg`, `truncLT_sub`, `truncLT_eq_self`,
    `isFinite_truncLT`.
- `mulTrunc c p q` multiplies only the pairs with `a + b < c`.
  `mulTrunc_eq : mulTrunc c p q = (p * q).truncLT c` holds with **no** hypothesis.
- `truncLT_mul (hp : p.IsFinite) (hq : q.IsFinite) :
  (p * q).truncLT c = (p.truncLT c * q.truncLT c).truncLT c`, via `mulTrunc_truncLT`.
- `leadCoeff_truncLT`, `sign_truncLT`: a nonzero truncation has the same leading term, hence the
  same sign.
- `Expr` is a tree of `leaf | add | sub | neg | mul` (with `+ - * -` instances), with `eval`
  (exact) and `evalTrunc c` (truncate at every node).
  - `evalTrunc_eq (h : e.LeavesFinite) : e.evalTrunc c = e.eval.truncLT c`.
- `lazySign c e := if e.evalTrunc c = 0 then none else some (e.evalTrunc c).sign`.
  - **`lazySign_sound`**: `e.LeavesFinite → lazySign c e = some s → e.eval.sign = s`.
  - **`lazySign_complete`**: if every exponent of `e.eval` is `< c`, then
    `lazySign c e = if e.eval = 0 then none else some e.eval.sign`.
  - `lazySign_complete_of_ne_zero`.
- Driver `lazySignIter e next fuel c` tries `c, next c, …`.
  - `lazySignIter_sound` holds for any `next`.
  - `lazySignIter_complete` holds if `next c ≥ 2c` and `2^fuel · c` exceeds every exponent.
  - The SoS drivers use `sqStep c = c² + 1` (`sqStep_ge`).
- Lazy SoS:
  - `orient2dExpr`/`incircleExpr` are the generic formulas instantiated at `K = Expr`, with
    `eval_orient2dExpr : … .eval = orient2dSoS …`.
  - `orient2dLazy`, `orient2dLazy_sound`, `orient2dLazy_complete` (with distinct indices it
    returns `some` of the SoS sign once the fuel is large enough).
  - `incircleLazy`, `incircleLazy_sound`.

### Tests (`LeviCivita.TestM3`)

- Predicates on `ℤ`/`ℚ` (`#eval`): `orient2d_ccw`, `incircle_inside` (`decide`) and
  `orient2d_rat` (via `orient2d_eq_det`).
- SoS, `decide` (plain, `ℤ` coefficients):
  - `sos_collinear`, `sos_collinear_swap` (collinear points get a definite sign, and a swap
    flips it),
  - `sos_coincident`, `sos_coincident_swap` (two identical points),
  - `sos_generic` (nondegenerate input gives the classical sign),
  - `sos3_coplanar`, `sos3_coplanar_swap`,
  - `sos_cocircular` (`decide +kernel`; plain `decide` hits the elaborator's recursion limit).
- SoS via theorems: `sos_ne_zero` (any input `Fin 5 → Fin 2 → ℤ`), `sos_sign_ne_zero` (any
  `ℚ` input), `sos_generic'` (via `orient2dSoS_sign`), `sos_incircle_ne_zero`.
- Lazy: `lazy_collinear`, `lazy_agrees`, `lazy_cocircular`, `lazy_sound_example`,
  `truncLT_example`, `mulTrunc_example`, and `#eval`s showing that `lazySign 1` (unperturbed)
  returns `none` on collinear input and `some` on generic input.

## Design decisions / open questions

1. **Perturbation scheme: `ε^(b^(j + d i))` in `Γ = ℤ`.** This is one infinitesimal with
   exponents that are powers of `b`, not a separate infinitesimal per coordinate. `Γ = ℤ` keeps
   everything computable with the existing `Repr`/`decide` support. The alternative,
   `Γ = Lex (Fin N → ℤ)`, would make injectivity trivial, but M2 noted that Mathlib's `Pi.Lex`
   order is noncomputable, and comparisons cost `O(N)`. The cost of powers of `b` is that
   exponents are big integers (`b^(2n)` for `n` points). See the benchmark.
2. **The nonvanishing proof goes through `MvPolynomial`**, not through a coefficient chase in
   `Poly`. Naturality turns "perturbed value" into "substitution applied to a symbolic
   determinant". So the predicate-specific work is only (1) one evaluation and (2) a degree
   bound, and both are short. This is why `orient3d`, `incircle` and `insphere` came almost for
   free after `orient2d`.
3. **Base `b`.** The key lemma needs every variable degree `< b`.
   - `orient2d`/`orient3d` are multilinear in the perturbations, so `b ≥ 2` is enough. This is
     the classical binary choice: products of distinct `ε^(2^k)` have distinct exponents.
   - In `incircle`/`insphere`, the variables of the last point occur in every row: once in a
     linear column and squared in the lifted column, so their degree is up to `3`. That needs
     `b ≥ 4`.
   - **`b = 4` is one global perturbation valid for all four predicates.** A Delaunay-style
     algorithm that mixes predicates should use the same `b` everywhere so that the perturbed
     configuration is the same. The tests use `b = 4`.
4. **`(2 : R) ≠ 0` for `incircle`/`insphere`** is an artifact of the proof. The certificate
   evaluation has value `2`. No `{0, ±1}`-valued evaluation can do better in characteristic 2,
   since `x² ≡ x` mod 2 makes the lifted column a sum of the others. The statement is presumably
   still true in characteristic 2: the symbolic determinant has `±1` coefficients, e.g. on
   `X(a,0)·X(b,1)·X(c,0)²`. Proving it would need a coefficient computation in `MvPolynomial`.
   The hypothesis holds for `ℤ`, `ℚ` and every ordered ring.
5. **Sign agreement needs no distinctness**, only `0 < b`. It is true for any input whose
   unperturbed value is nonzero, because the standard part of the perturbed value is the
   unperturbed value.
6. **Which SoS sign is chosen on degenerate input.** The sign is that of the lowest-exponent
   (dominant) nonzero term in the Hahn order. This is consistent: it depends only on the
   perturbed points, it is antisymmetric under relabeling, and it agrees with the exact sign
   whenever that is nonzero. It is **not** literally the Edelsbrunner–Mücke sequence of
   minors, which is defined by their ordering of `ε^(2^(i d - j))`. Matching their convention
   exactly would only change the exponent map `sosIdx`. The proofs never use a specific map
   beyond injectivity.
7. **`truncLT_mul` needs finiteness of both factors.** Counterexample without it:
   `(ε² · ε⁻¹).truncLT 2 = ε`, but `(ε²).truncLT 2 = 0`. `mulTrunc_eq` needs nothing. The
   lazy evaluator therefore assumes `LeavesFinite`, which SoS leaves satisfy
   (`isFinite_sosPoint`).
8. **`lazySign` returns `none` both for "value is 0" and for "needs more precision"**. They
   can't be told apart at finite precision. `lazySign_complete` gives the exact behavior once
   `c` is above all exponents.
9. **Driver step.** The plan said "double `c`". With SoS exponents `b^(j + d i)`, doubling from
   `c = 1` needs `≈ 2 d n log₂ b` passes, which is thousands for `n = 1000`. With `fuel = 64`
   the first benchmark version returned `none` on degenerate queries: sound, but useless. The
   driver therefore takes the step function as a parameter.
   - Soundness holds for any step.
   - Completeness is proved for any step with `next c ≥ 2c`.
   - The SoS drivers use `c ↦ c² + 1`, which reaches `2^(2^k)` in `k + 1` steps.
   - The first pass (`c = 1`) is exactly the unperturbed exact computation.
10. **Predicates are defined with `[Add K] [Sub K] [Mul K]`**, not `[CommRing K]`, so that the
    same definitions run on `Float` and on `Expr`. All theorems assume `[CommRing K]`.
11. Plain `decide` works for every SoS/lazy test except `incircle` with 4 points, which exceeds
    the elaborator's `maxRecDepth`. That one uses `decide +kernel` (still no `native_decide`).

## Left out / future work

- Lazy versions of `orient3d`/`insphere` (`orient3dExpr` etc.). They would be the same three
  lines as `orient2dExpr` and `incircleExpr`.
- A Float/interval filter in front of the exact path (Shewchuk-style), and fraction-free (Bareiss)
  evaluation. Both are M7. Today the lazy evaluator's first pass *is* the exact unperturbed
  computation, but it still builds the perturbed leaves (see the benchmark).
- Smaller SoS exponents. Any injective `sosIdx` works, and a `Γ = Lex (Fin k → ℤ)` variant
  would avoid big exponents, but needs a library-level computable lex order (M2 note 8).
- `incircle`/`insphere` SoS in characteristic 2 (note 4).

## `#print axioms` (exact output, from `lake build`)

```
'LeviCivita.Geometry.orient2d_eq_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.insphere_eq_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.map_orient2d' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.digit_extract' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.sosSubst_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.orient2dSoS' depends on axioms: [propext, Quot.sound]
'LeviCivita.Geometry.orient2dSoS_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.orient3dSoS_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.incircleSoS_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.insphereSoS_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.orient2dSoS_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Geometry.incircleSoS_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.toHahn_truncLT' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.mulTrunc_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Poly.truncLT_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.LazySign.lazySign_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.LazySign.lazySign_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.LazySign.lazySignIter_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.LazySign.lazySignIter_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.LazySign.orient2dLazy' depends on axioms: [propext, Quot.sound]
'LeviCivita.LazySign.orient2dLazy_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.TestM3.sos_collinear' depends on axioms: [propext, Quot.sound]
'LeviCivita.TestM3.sos_cocircular' depends on axioms: [propext, Quot.sound]
'LeviCivita.TestM3.lazy_collinear' depends on axioms: [propext, Quot.sound]
```

`AxiomAudit.lean` audits every M3 declaration listed above, plus the helpers and tests.
`#assert_axioms` fails the build on anything outside `{propext, Classical.choice, Quot.sound}`.

## Benchmark

The command is `lake env lean --run bench/Bench.lean <points> <queries> <grid>`, run on an Apple
M4 Max. The script runs in the Lean **interpreter**: a native `lean_exe` would have to compile
every imported Mathlib module to C, so it was not used. Each query is a random triple
(`orient2d`) or quadruple (`incircle`) of distinct indices into `10⁴` random integer points.
The checksum is order-sensitive and is printed so that methods can be compared. Run 2 uses a
16×16 grid to force degenerate queries.

| 10⁴ points, 10⁴ queries | run 1: coordinates in `[0, 10⁶)`, 0 degenerate | run 2: 16×16 grid, 243 / 309 degenerate |
|---|---|---|
| `orient2d` Float | 2.36 µs | 2.26 µs |
| `orient2d` exact `ℤ` | 2.17 µs | 1.59 µs |
| `orient2d` SoS `Poly ℤ ℤ` (full) | 63.3 µs | 59.5 µs |
| `orient2d` lazy SoS | 26.9 µs | 29.2 µs |
| `incircle` Float | 3.46 µs | 3.48 µs |
| `incircle` exact `ℤ` | 4.04 µs | 2.32 µs |
| `incircle` SoS `Poly ℤ ℤ` (full) | 4834 µs | 4321 µs |
| `incircle` lazy SoS | 116 µs | 179 µs |

Per query. Checksums:
- In run 1, all methods agree.
- In run 2, Float agrees with exact `ℤ`, because small integers are exact in Float, and full SoS
  agrees with lazy SoS. The two pairs differ from each other because the exact sign is `0` on
  degenerate queries.

Honest reading:
- **The lazy evaluator pays off**: 40× on `incircle` (4.8 ms → 0.12 ms) and 2.4× on `orient2d`.
- **It is still 10–30× slower than plain exact `ℤ`** on nondegenerate input, even though its first
  pass is the same computation. Two reasons:
  1. It builds the perturbed leaves `C x + ε^(4^(j + 2i))` first. With `n = 10⁴` these exponents
     are integers of up to 40 000 bits. They are computed by `Nat` pow and then filtered away.
  2. It runs on M1's quadratic list `Poly` operations instead of on `ℤ`.

  Fixes for M7: start the lazy evaluation from the unperturbed `ℤ` values (and a Float filter),
  build the perturbation terms only on demand, and give `sosIdx` smaller exponents.
- The full SoS `incircle` is slow because the perturbed determinant has hundreds of terms, each a
  product of several big-exponent monomials, multiplied with the `O(n·m·|result|)` list
  multiplication.
- Float numbers are given only for scale. Float has no correctness guarantee, and the
  interpreter dominates at this size.

## `lake build` (clean)

`rm -rf .lake/build && time LAKE_ARTIFACT_CACHE=false lake build` (Mathlib from cache):

```
Built LeviCivita.Geometry.Predicates (3.7s)
Built LeviCivita.Geometry.SoS (1.0s)
Built LeviCivita.Geometry.LazySign (1.9s)
Built LeviCivita.Geometry (1.3s)
Built LeviCivita.TestM3 (2.7s)
Built LeviCivita.AxiomAudit (1.4s)
Build completed successfully (1711 jobs).
LAKE_ARTIFACT_CACHE=false lake build  29.03s user 12.46s system 229% cpu 18.098 total
```

The only warnings are the module-system notices. Checks on the log:
- `declaration uses 'sorry'` has 0 matches;
- the CI forbidden-construct grep (`axiom`, `implemented_by`, `extern`, `native_decide`) finds
  nothing in `LeviCivita/` or `bench/`;
- `lake env lean bench/Bench.lean` elaborates. CI now checks this too.
