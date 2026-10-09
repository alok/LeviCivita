# M4 notes: precision-tracked approximations

Branch `grokbot/hahn-m4`, stacked on `grokbot/hahn-m3`. Same toolchain
(`leanprover/lean4:v4.35.0-rc4`, Mathlib master). Status: **all M4 deliverables done**. That
covers `Represents` and the truncation API, our `truncLT_mul`, sound `+ - *`, the certified sign
with verdicts, and a certified inverse.

The build has zero `sorry`, zero `native_decide`, no `implemented_by`/`extern`, and no new
`axiom`.

## New files

| File | Contents |
|---|---|
| `LeviCivita/Approx/Basic.lean` | Hahn-series agreement lemmas and our `truncLT_mul`; `Poly.truncTop`/`mulTruncTop`; `Approx`, `Represents`, truncation API; `add/neg/sub/mul`; `sign?`, `Verdict`, `decidePos?`; `newtonInv`, `invPrec`, `invCore`, `inv?` |
| `LeviCivita/Approx.lean` | root import; `LeviCivita.lean` imports it |
| `LeviCivita/TestM4.lean` | `#guard_msgs` evals and `decide +kernel` theorems (new root of the default target) |

## Definitions

- `structure Approx (Γ R) where val : Poly Γ R; prec : WithTop Γ`. `⊤` means exact. It has
  `Repr` (`1 ε^0 + -1 ε^1 + O(ε^2)`) and `DecidableEq`.
- `Represents a x := ∀ g : Γ, (g : WithTop Γ) < a.prec → x.coeff g = (toHahn a.val).coeff g`.
- `ord a := min a.val.leadExp a.prec`. This is a lower bound for the order of every represented
  series.
- `Certified a := a.val.leadExp < a.prec`. The leading term is below the precision. This is
  decidable.
- `exact p = ⟨p, ⊤⟩`, `ofPoly p c = ⟨p.truncTop c, c⟩`,
  `withPrec c a = ⟨a.val.truncTop (min c a.prec), min c a.prec⟩`.
- `Poly.truncTop : WithTop Γ → Poly → Poly` is M3's `truncLT`, with `⊤` meaning no truncation.
  `Poly.mulTruncTop` is M3's `mulTrunc` (and `*` at `⊤`).
- Arithmetic (also available as the instances `+ - - *`):
  - `add`/`sub`: precision `min pa pb`, then truncate;
  - `neg`: same precision;
  - `mul`: `mulPrec a b = min (pa + ord b) (pb + ord a)` in `WithTop Γ`. The product is computed
    by `mulTruncTop`, so only the terms below that precision are formed.
- `sign? a := if a.prec = ⊤ ∨ a.Certified then some a.val.sign else none`.
- `Verdict = accept | reject | unresolved`. `decidePos?` maps `some 1` to `accept`, any other
  `some _` to `reject` (`x ≤ 0`), and `none` to `unresolved`.
- Inverse (`[Field R]`, `Γ` an ordered additive group):
  - `newtonInv q u n`: `n` Newton steps `y ↦ y (2 - u y)` from `1`, truncated at `q`.
  - `invCore n a e r`:
    1. normalize `u = val · r⁻¹ ε^(-e)` at relative precision `q = prec - e`;
    2. take `y = r⁻¹ ε^(-e) · newtonInv q u n`;
    3. set the precision to `invPrec a e y`.
  - `invPrec a e y = min (ord (1 - val·y)) P + (-e)`, with `P = prec + ord y`. Here `val·y` is
    computed by `mulTruncTop P`.
  - `inv? n a` reads `(e, r)` off the head of `a.val.terms`. It returns `some (invCore n a e r)`
    when `e < prec`, and `none` otherwise (empty `val` or uncertified leading term).

## Proven

### Hahn series (namespace `LeviCivita.HahnSeries`)

- `agree_iff_le_orderTop`: `x` and `y` agree below `c` iff `c ≤ (x - y).orderTop`.
- `le_orderTop_add_of_coeff`: if `z.coeff g = 0` whenever `g + o < c`, then `c ≤ ord z + o`.
- **`coeff_mul_eq_of_agree`** (our `truncLT_mul`, valuation form, any ordered cancel monoid `Γ`).
  - Hypotheses: `ox ≤ ord x'`, `oy ≤ ord y`, `x` agrees with `x'` at every `g` with `g + oy < c`,
    and `y` agrees with `y'` at every `g` with `g + ox < c`.
  - Conclusion: `x * y` and `x' * y'` agree below `c`.
- **`coeff_mul_eq_of_agree_sub`**: the group form, with `g < c - oy` and `g < c - ox`.
  `Γ = ℤ` and `Γ = ℚ` instantiate it (`[AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]`).
- **`truncLT_mul_of_orderTop`**: if `ox ≤ ord x` and `oy ≤ ord y`, then
  `truncLT c (x*y) = truncLT c (truncLT (c - oy) x * truncLT (c - ox) y)`.
  M3's `truncLT_mul` for finite elements is the case `ox = oy = 0`.
- `orderTop_le_orderTop_truncLT`.

### Truncation API (`LeviCivita.Poly`, `LeviCivita.Approx`)

- `Poly.truncLT_truncLT : (p.truncLT a).truncLT b = p.truncLT (min a b)`, `Poly.truncTop_truncTop`,
  `Poly.coeff_truncTop`, `Poly.mulTruncTop_eq : mulTruncTop c p q = (p * q).truncTop c`.
- `represents_iff_le_orderTop : a.Represents x ↔ a.prec ≤ (x - toHahn a.val).orderTop`.
- `represents_iff_truncLT (hc : a.prec = c)`:
  `a.Represents x ↔ HahnSeries.truncLT c x = HahnSeries.truncLT c (toHahn a.val)`.
  This uses Mathlib master's `HahnSeries.truncLT`.
- `represents_iff_truncLT_eq`: if `val` has no terms `≥ c`, `Represents ↔ truncLT c x = toHahn val`.
  This is the plan's formulation.
- **`represents_top_iff`**: `⟨p, ⊤⟩.Represents x ↔ x = toHahn p`. Also `represents_exact` and
  `represents_exact_iff`.
- **`Represents.mono`**: lowering the precision preserves `Represents`.
- `represents_truncTop_iff`: dropping terms at or above some `c ≥ prec` changes nothing.
- `represents_ofPoly`, `Represents.withPrec`.
- `Represents.ord_le : a.ord ≤ x.orderTop`.
- Certified approximations:
  - `Represents.orderTop_eq (hc : a.Certified) : x.orderTop = a.val.leadExp`;
  - `Represents.leadingCoeff_eq : x.leadingCoeff = a.val.leadCoeff`;
  - `Represents.ne_zero`.

### Sound arithmetic

- `Represents.add`, `Represents.neg`, `Represents.sub`, `Represents.mul`. Each has the form
  `a.Represents x → b.Represents y → (a ⊙ b).Represents (x ⊙ y)`.
- `represents_mul_val`: the untruncated product rule. Its proof is the identity
  `xy - va·vb = (x - va)·y + va·(y - vb)` combined with
  `ord u + ord v ≤ ord (u v)` (Mathlib's `orderTop_add_le_mul`).
- `Represents.mul_exact`: an exact factor `q` gives precision `pa + ord q`.

### Certified sign

- `sign?_exact : (exact p).sign? = some p.sign`. This includes `p = 0`.
- `sign?_of_certified`.
- `sign?_eq_none_iff : a.sign? = none ↔ a.prec ≠ ⊤ ∧ ¬a.Certified`.
- `Represents.leadingCoeff_eq_of_sign?`.
- **`sign?_sound`**: `a.sign? = some s → a.Represents x → (s = 1 ↔ 0 < toLex x) ∧
  (s = -1 ↔ toLex x < 0) ∧ (s = 0 ↔ x = 0)`.
- **`decidePos?_accept`** (`accept → 0 < toLex x`), **`decidePos?_reject`**
  (`reject → toLex x ≤ 0`), `decidePos?_exact_ne` (an exact approximation is never unresolved).

### Inverse

- `orderTop_inv : x.orderTop = e → x⁻¹.orderTop = -e`. It uses Mathlib's `HahnSeries.instField`.
- **`Represents.inv_of_residual`**: for **any** candidate `y : Poly Γ R`, if `a.Represents x`,
  `a.val.leadExp = e` and `a.Certified`, then `⟨y, invPrec a e y⟩.Represents x⁻¹`.
- `Represents.invCore`.
- **`Represents.inv?`**: `a.Represents x → a.inv? n = some b → b.Represents x⁻¹`.
- `inv?_isSome`: a certified approximation always gets an answer.
- **`exists_inv?_represents`**: `a.Represents x → a.Certified → x ≠ 0 ∧ ∃ b, a.inv? n = some b ∧
  b.Represents x⁻¹`. This is the requested statement; `x ≠ 0` is a consequence of
  certification, not a hypothesis.

### Tests (`LeviCivita.TestM4`, `Γ = ℤ`, `R = ℚ` unless noted)

- `#guard_msgs` evals:
  - `a := (exact (1+ε)).withPrec 5` and `a.inv? 3 = 1 - ε + ε² - ε³ + ε⁴ + O(ε⁵)`.
  - Newton's doubling: with 1, 2, 3 steps the results are `O(ε²)`, `O(ε⁴)`, `O(ε⁵)`.
  - `(a.inv? 3) * a = 1 + O(ε⁵)`.
  - The exact `1+ε` with 3 steps gives `O(ε⁸)`.
  - `(2ε + 3ε² + O(ε⁴))⁻¹ = ½ε⁻¹ - ¾ + (9/8)ε + O(ε²)`, and its product with the input is
    `1 + O(ε³)`.
  - `Γ = ℚ`: `(1 + √ε + O(ε²))⁻¹ = 1 - √ε + ε - ε^{3/2} + O(ε²)`.
  - Precision rules: `(ε + O(ε³))(1 + O(ε²)) = ε + O(ε³)` and `O(ε²) · 1 = O(ε²)`.
  - `sign?` gives `none`/`some 1`, and `decidePos?` gives `reject`/`unresolved`.
- `decide +kernel`: `inv_one_add_eps`, `inv_mul_self_val`, `inv_b_prec`, `mul_prec_example`,
  `mul_unknown_order`, `sign_unresolved`, `sign_resolved`, `sign_exact_zero`, `accept_example`.
- Via the soundness theorems:
  - `inv_mul_self_represents`: every `b = a.inv? 3` satisfies `(b * a).Represents 1`.
  - `pos_of_approx`: every `x = ε + O(ε²)` is positive.
  - `inv_pos_example`: every `x = 1 + ε + O(ε⁵)` has `0 < x⁻¹`.

## Design decisions / open questions

1. **No "exponents < prec" invariant in the structure.** `Represents` ignores the terms of `val`
   at or above `prec`, so the invariant would carry no meaning and would cost a proof in every
   constructor. Instead, every operation truncates its output (`truncTop`), so in practice
   `val` satisfies the invariant. `represents_iff_truncLT_eq` gives the plan's
   `truncLT c x = toHahn val` reading whenever it holds.
2. **The valuation form is the working definition.** `Represents ↔ prec ≤ ord (x - val)`
   (`represents_iff_le_orderTop`) turns every soundness proof into a short estimate. The
   estimates use Mathlib's `min_orderTop_le_orderTop_add`, `orderTop_add_le_mul` and (for
   fields) `orderTop_mul`. There is no coefficient convolution anywhere.
3. **`ord a = min (leadExp val) prec`** is the conservative order bound. If `val = 0` and
   `prec = c`, the true `x` can have any order `≥ c`, so `ord = c`. If `prec = ⊤`, then
   `ord = leadExp val` exactly. In the precision rule `min (pa + ord b) (pb + ord a)`, `⊤`
   absorbs in `WithTop` addition. Two consequences:
   - exact × exact is exact;
   - exact `0` × anything is exact `0`.
   Both are correct.
4. **Our `truncLT_mul` needs order bounds on only one side of each pair.** The hypotheses are
   `ox ≤ ord x'` and `oy ≤ ord y`, from `xy - x'y' = (x - x')y + x'(y - y')`. The general
   statement uses `g + o < c`, so it holds for ordered cancel monoids; the group form with
   `c - o` is a corollary. M3's finiteness counterexample (`ε² · ε⁻¹`) is excluded by the order
   bounds.
5. **The inverse is certified a posteriori, and soundness does not depend on Newton.** Proving
   Newton's quadratic convergence on truncated `Poly`s would have meant tracking
   `ord (1 - u yₖ) ≥ min (q, 2ᵏ ord δ)` through truncations. Instead, the precision is
   *computed* from the residual: `x⁻¹ - y = x⁻¹ (1 - x y)`, so
   `ord (x⁻¹ - y) = -e + ord (1 - x y) ≥ -e + ord(approximation of 1 - x y)`. This is the
   "solver finds, Lean checks" pattern of plan §5.7 in miniature. It is sound for any candidate,
   and it is as tight as the candidate is good: on the tests it gives the optimal precision
   `pa - 2e` (absolute; relative precision `pa - e`). Cost: one extra truncated multiplication.
   The fallback geometric series is not needed.
6. **`inv?` returns `Option`.** Without a certified leading term, `x` might be `0` and its order
   is unknown. `WithTop Γ` has no bottom precision, so there is no vacuous approximation to
   return. A total `inv` with a certification hypothesis would compute garbage silently.
7. **`sign?` answers for every exact approximation, including `0`.** This follows
   `sign?_exact` as requested. An inexact approximation with `val = 0`, or with a leading term at
   or above `prec`, is `unresolved`, even if the true `x` is `0`. At finite precision `0` can't
   be told apart from a tiny nonzero tail; this is the same situation as M3 note 8.
8. **`reject` means `toLex x ≤ 0`**, so it includes `x = 0`. Use `sign?` for the three-way answer.
9. **Exact inputs to `inv?`** run Newton without truncation (`q = ⊤`). The term count can double
   at each step. Use `withPrec` first; the tests do so, except for the one exact demonstration.
10. **Axioms of definitions.** `sign?`, `withPrec`, `mul`, `inv?` and others list
    `Classical.choice` in `#print axioms`. The source is proof fields of instances they use, for
    example `LinearOrder (WithTop Γ)` inside `min`. Computation is unaffected: all `#eval`s run
    compiled code, and every `decide +kernel` test reduces in the kernel. `newtonInv`,
    `exact` and `ofPoly` don't mention it.
11. **Plain `decide`** does not work on the `ℚ` tests, for the reason explained in M1 (`Rat.add`
    etc. are `@[irreducible]`), so they use `decide +kernel`. The inverse needs a field, so
    switching to `ℤ` coefficients is not an option there.

## Left out / future work

- **A tightness theorem for `inv?`.** For example: after `⌈log₂ (q / ord δ)⌉` steps,
  `invPrec = prec - 2e`. Soundness is complete; only optimality of the certified precision is
  unproved. The tests show it.
- `Approx.refine` (re-run a thunk at higher precision, plan §5.4) and a precision-raising driver
  around `decidePos?`. This is the M3 `lazySignIter` pattern; it would be a few lines on top of
  `sign?_sound`.
- `sqrt` (`Γ = ℚ`) and transcendentals on infinitesimals belong to M6. The residual-certificate
  technique of `inv_of_residual` should carry over to `sqrt` (`x - y²`).
- No algebraic structure on `Approx`. Precision is not associative under the rules, so `Approx` is
  not a ring. The operations are plain functions with instances only for `+ - *` notation.
- Lazy `Stream`-based series (plan §5.4, optional).

## `#print axioms` (exact output, from `lake build`)

```
'LeviCivita.Approx.Represents.mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Approx.sign?_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Approx.Represents.inv?' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.HahnSeries.coeff_mul_eq_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.TestM4.inv_one_add_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Approx.sign?' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Approx.decidePos?' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Approx.inv?' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.Approx.newtonInv' depends on axioms: [propext, Quot.sound]
'LeviCivita.Approx.exact' depends on axioms: [propext]
'LeviCivita.TestM4.inv_mul_self_represents' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeviCivita.TestM4.inv_pos_example' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`AxiomAudit.lean` runs `#assert_axioms` on every M4 declaration listed above, plus the helpers and
all M4 tests.

## `lake build` (clean)

`rm -rf .lake/build && time LAKE_ARTIFACT_CACHE=false lake build` (Mathlib from cache):

```
Built LeviCivita.Approx (1.4s)
Built LeviCivita.TestM4 (2.1s)
Built LeviCivita.AxiomAudit (1.5s)
Build completed successfully (1716 jobs).
LAKE_ARTIFACT_CACHE=false lake build  35.90s user 15.29s system 244% cpu 20.908 total
```

The only warnings are the module-system notices; there are none from `Approx` or `TestM4`
otherwise. Checks on the log:
- `declaration uses 'sorry'` has 0 matches;
- the CI forbidden-construct grep (`axiom`, `implemented_by`, `extern`, `native_decide`) finds
  nothing.
