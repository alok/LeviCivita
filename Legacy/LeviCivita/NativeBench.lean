import Std
import LeviCivita.Fast
import LeviCivita.UltraFast
import LeviCivita.CompactLC
import LeviCivita.PackedLC

/-!
# Native Benchmark for LC Implementations

Run with: lake exe nativebench

Tests:
1. Large polynomial multiplication (10+ terms)
2. Batch derivative computation
3. Deep power operations
-/

set_option linter.missingDocs false

namespace LeviCivita.NativeBench

-- Timing helper
def benchMs (name : String) (iters : Nat) (f : Unit → α) : IO Unit := do
  -- Warmup
  for _ in [:100] do
    let _ := f ()

  let start ← IO.monoMsNow
  for _ in [:iters] do
    let _ := f ()
  let elapsed := (← IO.monoMsNow) - start

  let msPerOp := elapsed.toFloat / iters.toFloat
  let opsPerSec := if msPerOp > 0.0 then 1000.0 / msPerOp else 0.0

  if elapsed > 0 then
    IO.println s!"{name}: {elapsed}ms / {iters} = {(opsPerSec / 1_000_000.0)} M ops/sec"
  else
    IO.println s!"{name}: <1ms for {iters} iters (very fast)"

-- Build a FastLC polynomial with n terms
def buildFastPoly (n : Nat) : LeviCivita.Fast.FastLC.LC := Id.run do
  let mut result : LeviCivita.Fast.FastLC.LC := 0
  for i in [:n] do
    let exp := i.toFloat - (n.toFloat / 2.0)
    let coeff := (i.toFloat + 1.0) * 0.1
    result := result + { terms := #[⟨exp, coeff⟩] }
  result

-- Build an UltraFast polynomial with n terms
def buildUltraPoly (n : Nat) : LeviCivita.UltraFast.LC := Id.run do
  let mut result : LeviCivita.UltraFast.LC := 0
  for i in [:n] do
    let exp := i.toFloat - (n.toFloat / 2.0)
    let coeff := (i.toFloat + 1.0) * 0.1
    result := result + { terms := #[⟨exp, coeff⟩] }
  result

end LeviCivita.NativeBench

open LeviCivita.NativeBench in
def main : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║     Native Compiled LC Benchmarks                            ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- ═══════════════════════════════════════════════════════════════════
  -- Test 1: Small polynomials (baseline)
  -- ═══════════════════════════════════════════════════════════════════
  IO.println "═══ Test 1: Small Polynomials (2 terms) ═══"
  IO.println ""

  let fast2a := LeviCivita.Fast.FastLC.ofFloat 1.0 + LeviCivita.Fast.FastLC.epsilon
  let fast2b := LeviCivita.Fast.FastLC.ofFloat 2.0 + LeviCivita.Fast.FastLC.H
  let ultra2a := LeviCivita.UltraFast.LC.ofFloat 1.0 + LeviCivita.UltraFast.LC.epsilon
  let ultra2b := LeviCivita.UltraFast.LC.ofFloat 2.0 + LeviCivita.UltraFast.LC.H
  let compact2a := LeviCivita.Compact.LC.ofFloat 1.0 + LeviCivita.Compact.LC.epsilon
  let compact2b := LeviCivita.Compact.LC.ofFloat 2.0 + LeviCivita.Compact.LC.H
  let packed2a := LeviCivita.Packed.LC.ofFloat 1.0 + LeviCivita.Packed.LC.epsilon
  let packed2b := LeviCivita.Packed.LC.ofFloat 2.0 + LeviCivita.Packed.LC.H

  benchMs "FastLC    mul (2-term)" 10000000 fun _ => fast2a * fast2b
  benchMs "UltraFast mul (2-term)" 10000000 fun _ => ultra2a * ultra2b
  benchMs "CompactLC mul (2-term)" 10000000 fun _ => compact2a * compact2b
  benchMs "PackedLC  mul (2-term)" 10000000 fun _ => packed2a * packed2b
  IO.println ""

  -- ═══════════════════════════════════════════════════════════════════
  -- Test 2: Medium polynomials (5 terms)
  -- ═══════════════════════════════════════════════════════════════════
  IO.println "═══ Test 2: Medium Polynomials (5 terms) ═══"
  IO.println ""

  let fast5 := buildFastPoly 5
  let ultra5 := buildUltraPoly 5

  benchMs "FastLC    mul (5-term)" 2000000 fun _ => fast5 * fast5
  benchMs "UltraFast mul (5-term)" 2000000 fun _ => ultra5 * ultra5
  IO.println ""

  -- ═══════════════════════════════════════════════════════════════════
  -- Test 3: Large polynomials (10 terms)
  -- ═══════════════════════════════════════════════════════════════════
  IO.println "═══ Test 3: Large Polynomials (10 terms) ═══"
  IO.println ""

  let fast10 := buildFastPoly 10
  let ultra10 := buildUltraPoly 10

  benchMs "FastLC    mul (10-term)" 2000000 fun _ => fast10 * fast10
  benchMs "UltraFast mul (10-term)" 2000000 fun _ => ultra10 * ultra10
  IO.println ""

  -- ═══════════════════════════════════════════════════════════════════
  -- Test 4: Very large polynomials (20 terms)
  -- ═══════════════════════════════════════════════════════════════════
  IO.println "═══ Test 4: Very Large Polynomials (20 terms) ═══"
  IO.println ""

  let fast20 := buildFastPoly 20
  let ultra20 := buildUltraPoly 20

  benchMs "FastLC    mul (20-term)" 2000000 fun _ => fast20 * fast20
  benchMs "UltraFast mul (20-term)" 2000000 fun _ => ultra20 * ultra20
  IO.println ""

  -- ═══════════════════════════════════════════════════════════════════
  -- Test 5: Deep power operations
  -- ═══════════════════════════════════════════════════════════════════
  IO.println "═══ Test 5: Deep Power Operations ═══"
  IO.println ""

  benchMs "FastLC    (1+ε)^10" 2000000 fun _ => fast2a ^ 10
  benchMs "UltraFast (1+ε)^10" 2000000 fun _ => ultra2a ^ 10
  benchMs "CompactLC (1+ε)^10" 2000000 fun _ => compact2a ^ 10
  benchMs "PackedLC  (1+ε)^10" 2000000 fun _ => packed2a ^ 10
  IO.println ""

  benchMs "FastLC    (1+ε)^20" 1000000 fun _ => fast2a ^ 20
  benchMs "UltraFast (1+ε)^20" 1000000 fun _ => ultra2a ^ 20
  benchMs "CompactLC (1+ε)^20" 1000000 fun _ => compact2a ^ 20
  benchMs "PackedLC  (1+ε)^20" 1000000 fun _ => packed2a ^ 20
  IO.println ""

  -- ═══════════════════════════════════════════════════════════════════
  -- Test 6: Batch derivative computation
  -- ═══════════════════════════════════════════════════════════════════
  IO.println "═══ Test 6: Batch Derivatives ═══"
  IO.println ""

  -- Compute derivatives at 100 different points
  let f_fast := fun (x : LeviCivita.Fast.FastLC.LC) => x * x * x * x * x  -- x^5
  let f_ultra := fun (x : LeviCivita.UltraFast.LC) => x * x * x * x * x
  let f_compact := fun (x : LeviCivita.Compact.LC) => x * x * x * x * x
  let f_packed := fun (x : LeviCivita.Packed.LC) => x * x * x * x * x

  benchMs "FastLC    100 derivs of x^5" 1000000 fun _ => Id.run do
    let mut sum := 0.0
    for i in [:100] do
      let pt := LeviCivita.Fast.FastLC.ofFloat (i.toFloat * 0.1)
      sum := sum + LeviCivita.Fast.FastLC.derivative f_fast pt
    sum

  benchMs "UltraFast 100 derivs of x^5" 1000000 fun _ => Id.run do
    let mut sum := 0.0
    for i in [:100] do
      let pt := LeviCivita.UltraFast.LC.ofFloat (i.toFloat * 0.1)
      sum := sum + LeviCivita.UltraFast.LC.derivative f_ultra pt
    sum

  benchMs "CompactLC 100 derivs of x^5" 1000000 fun _ => Id.run do
    let mut sum := 0.0
    for i in [:100] do
      let pt := LeviCivita.Compact.LC.ofFloat (i.toFloat * 0.1)
      sum := sum + LeviCivita.Compact.LC.derivative f_compact pt
    sum

  benchMs "PackedLC  100 derivs of x^5" 1000000 fun _ => Id.run do
    let mut sum := 0.0
    for i in [:100] do
      let pt := LeviCivita.Packed.LC.ofFloat (i.toFloat * 0.1)
      sum := sum + LeviCivita.Packed.LC.derivative f_packed pt
    sum
  IO.println ""

  -- ═══════════════════════════════════════════════════════════════════
  -- Test 7: Complex expression evaluation
  -- ═══════════════════════════════════════════════════════════════════
  IO.println "═══ Test 7: Complex Expression (x³ + 2x² + 3x + 4) ═══"
  IO.println ""

  let evalFast := fun (x : LeviCivita.Fast.FastLC.LC) =>
    x * x * x + LeviCivita.Fast.FastLC.ofFloat 2.0 * x * x +
    LeviCivita.Fast.FastLC.ofFloat 3.0 * x + LeviCivita.Fast.FastLC.ofFloat 4.0

  let evalUltra := fun (x : LeviCivita.UltraFast.LC) =>
    x * x * x + LeviCivita.UltraFast.LC.ofFloat 2.0 * x * x +
    LeviCivita.UltraFast.LC.ofFloat 3.0 * x + LeviCivita.UltraFast.LC.ofFloat 4.0

  let evalCompact := fun (x : LeviCivita.Compact.LC) =>
    x * x * x + LeviCivita.Compact.LC.ofFloat 2.0 * x * x +
    LeviCivita.Compact.LC.ofFloat 3.0 * x + LeviCivita.Compact.LC.ofFloat 4.0

  let evalPacked := fun (x : LeviCivita.Packed.LC) =>
    x * x * x + LeviCivita.Packed.LC.ofFloat 2.0 * x * x +
    LeviCivita.Packed.LC.ofFloat 3.0 * x + LeviCivita.Packed.LC.ofFloat 4.0

  let pt_fast := LeviCivita.Fast.FastLC.ofFloat 2.0 + LeviCivita.Fast.FastLC.epsilon
  let pt_ultra := LeviCivita.UltraFast.LC.ofFloat 2.0 + LeviCivita.UltraFast.LC.epsilon
  let pt_compact := LeviCivita.Compact.LC.ofFloat 2.0 + LeviCivita.Compact.LC.epsilon
  let pt_packed := LeviCivita.Packed.LC.ofFloat 2.0 + LeviCivita.Packed.LC.epsilon

  benchMs "FastLC    eval polynomial" 5000000 fun _ => evalFast pt_fast
  benchMs "UltraFast eval polynomial" 5000000 fun _ => evalUltra pt_ultra
  benchMs "CompactLC eval polynomial" 5000000 fun _ => evalCompact pt_compact
  benchMs "PackedLC  eval polynomial" 5000000 fun _ => evalPacked pt_packed
  IO.println ""

  -- Verify correctness
  IO.println "═══ Correctness Check ═══"
  let result_fast := evalFast pt_fast
  let result_compact := evalCompact pt_compact
  -- At x=2: f(x) = 8 + 8 + 6 + 4 = 26, f'(x) = 12 + 8 + 3 = 23
  IO.println s!"FastLC:    value={LeviCivita.Fast.FastLC.std result_fast}, deriv={LeviCivita.Fast.FastLC.getCoeff result_fast (-1.0)}"
  IO.println s!"CompactLC: value={result_compact.std}, deriv={result_compact.getCoeff (-1)}"
  IO.println s!"Expected:  value=26.0, deriv=23.0"
