import LeviCivita.Core
import LeviCivita.Field
import LeviCivita.Fast

/-!
# Comprehensive Levi-Civita Benchmarks

Compares all implementations:
- Core: Sorted array with Rat coefficients (baseline)
- Field: HashMap with Rat coefficients
- FastLC: Sorted array with Float coefficients (fastest arithmetic)
- BinaryLC: Sorted array with binary search lookups (same as Core but with binary search)
-/

set_option linter.missingDocs false

namespace BenchAll

-- Type aliases
abbrev CLC := LeviCivita.Core.LC
abbrev FLC := LeviCivita.Field.LC
abbrev FastLC := LeviCivita.Fast.FastLC.LC
abbrev BinaryLC := LeviCivita.Fast.BinaryLC.LC

/-- Prevent DCE by checking condition. -/
@[noinline] def blackhole (b : Bool) : IO Unit :=
  if b then IO.println "unexpected" else pure ()

/-! ## Addition Benchmarks -/

section Addition

def benchAddCore (n : Nat) : IO Unit := do
  let x : CLC := (1 : CLC) + LeviCivita.Core.LC.epsilon + LeviCivita.Core.LC.epsilon * LeviCivita.Core.LC.epsilon
  let mut acc : CLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    acc := acc + x
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (acc.terms.size > 1000000)
  IO.println s!"Core.add ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def benchAddField (n : Nat) : IO Unit := do
  let x : FLC := (1 : FLC) + LeviCivita.Field.LC.epsilon + LeviCivita.Field.LC.epsilon * LeviCivita.Field.LC.epsilon
  let mut acc : FLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    acc := acc + x
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (acc.coeffs.size > 1000000)
  IO.println s!"Field.add ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def benchAddFast (n : Nat) : IO Unit := do
  let x : FastLC := (1 : FastLC) + LeviCivita.Fast.FastLC.epsilon + LeviCivita.Fast.FastLC.epsilon * LeviCivita.Fast.FastLC.epsilon
  let mut acc : FastLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    acc := acc + x
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (acc.terms.size > 1000000)
  IO.println s!"FastLC.add ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def benchAddBinary (n : Nat) : IO Unit := do
  let x : BinaryLC := (1 : BinaryLC) + LeviCivita.Fast.BinaryLC.epsilon + LeviCivita.Fast.BinaryLC.epsilon * LeviCivita.Fast.BinaryLC.epsilon
  let mut acc : BinaryLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    acc := acc + x
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (acc.terms.size > 1000000)
  IO.println s!"BinaryLC.add ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

end Addition

/-! ## Multiplication Benchmarks -/

section Multiplication

def benchMulCore (n : Nat) : IO Unit := do
  let x : CLC := (1 : CLC) + LeviCivita.Core.LC.epsilon + LeviCivita.Core.LC.epsilon * LeviCivita.Core.LC.epsilon
  let y : CLC := (2 : CLC) + LeviCivita.Core.LC.epsilon
  let mut result : CLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := x * y
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (result.terms.size > 1000000)
  IO.println s!"Core.mul ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def benchMulField (n : Nat) : IO Unit := do
  let x : FLC := (1 : FLC) + LeviCivita.Field.LC.epsilon + LeviCivita.Field.LC.epsilon * LeviCivita.Field.LC.epsilon
  let y : FLC := (2 : FLC) + LeviCivita.Field.LC.epsilon
  let mut result : FLC := LeviCivita.Field.LC.zero
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := x * y
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (result.coeffs.size > 1000000)
  IO.println s!"Field.mul ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def benchMulFast (n : Nat) : IO Unit := do
  let x : FastLC := (1 : FastLC) + LeviCivita.Fast.FastLC.epsilon + LeviCivita.Fast.FastLC.epsilon * LeviCivita.Fast.FastLC.epsilon
  let y : FastLC := (2 : FastLC) + LeviCivita.Fast.FastLC.epsilon
  let mut result : FastLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := x * y
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (result.terms.size > 1000000)
  IO.println s!"FastLC.mul ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def benchMulBinary (n : Nat) : IO Unit := do
  let x : BinaryLC := (1 : BinaryLC) + LeviCivita.Fast.BinaryLC.epsilon + LeviCivita.Fast.BinaryLC.epsilon * LeviCivita.Fast.BinaryLC.epsilon
  let y : BinaryLC := (2 : BinaryLC) + LeviCivita.Fast.BinaryLC.epsilon
  let mut result : BinaryLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := x * y
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (result.terms.size > 1000000)
  IO.println s!"BinaryLC.mul ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

end Multiplication

/-! ## Power Benchmarks -/

section Power

def benchPowCore (n : Nat) (exp : Nat) : IO Unit := do
  let x : CLC := (1 : CLC) + LeviCivita.Core.LC.epsilon
  let mut result : CLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := x ^ exp
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (result.terms.size > 1000000)
  IO.println s!"Core.pow^{exp} ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def benchPowFast (n : Nat) (exp : Nat) : IO Unit := do
  let x : FastLC := (1 : FastLC) + LeviCivita.Fast.FastLC.epsilon
  let mut result : FastLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := x ^ exp
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (result.terms.size > 1000000)
  IO.println s!"FastLC.pow^{exp} ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def benchPowBinary (n : Nat) (exp : Nat) : IO Unit := do
  let x : BinaryLC := (1 : BinaryLC) + LeviCivita.Fast.BinaryLC.epsilon
  let mut result : BinaryLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := x ^ exp
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (result.terms.size > 1000000)
  IO.println s!"BinaryLC.pow^{exp} ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

end Power

/-! ## Derivative Benchmarks -/

section Derivative

def benchDerivCore (n : Nat) : IO Unit := do
  let f := fun (x : CLC) => x * x * x  -- x³
  let pt : CLC := 3
  let mut result : Rat := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := LeviCivita.Core.LC.derivative f pt
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (result > 1000000)
  IO.println s!"Core.derivative ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def benchDerivFast (n : Nat) : IO Unit := do
  let f := fun (x : FastLC) => x * x * x  -- x³
  let pt : FastLC := 3
  let mut result : Float := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := LeviCivita.Fast.FastLC.derivative f pt
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (result > 1000000)
  IO.println s!"FastLC.derivative ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def benchDerivBinary (n : Nat) : IO Unit := do
  let f := fun (x : BinaryLC) => x * x * x  -- x³
  let pt : BinaryLC := 3
  let mut result : Rat := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := LeviCivita.Fast.BinaryLC.derivative f pt
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (result > 1000000)
  IO.println s!"BinaryLC.derivative ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

end Derivative

/-! ## Inversion Benchmarks -/

section Inversion

def benchInvertCore (n : Nat) : IO Unit := do
  let x : CLC := (2 : CLC) + LeviCivita.Core.LC.epsilon
  let mut result : Option CLC := none
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := LeviCivita.Core.LC.invert x 10
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (result.isSome && result.get!.terms.size > 1000000)
  IO.println s!"Core.invert ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def benchInvertFast (n : Nat) : IO Unit := do
  let x : FastLC := (2 : FastLC) + LeviCivita.Fast.FastLC.epsilon
  let mut result : Option FastLC := none
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := LeviCivita.Fast.FastLC.invert x 10
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (result.isSome && result.get!.terms.size > 1000000)
  IO.println s!"FastLC.invert ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def benchInvertBinary (n : Nat) : IO Unit := do
  let x : BinaryLC := (2 : BinaryLC) + LeviCivita.Fast.BinaryLC.epsilon
  let mut result : Option BinaryLC := none
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := LeviCivita.Fast.BinaryLC.invert x 10
  let elapsed := (← IO.monoNanosNow) - start
  blackhole (result.isSome && result.get!.terms.size > 1000000)
  IO.println s!"BinaryLC.invert ({n}): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

end Inversion

end BenchAll

/-- Main benchmark runner. -/
def main : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════════╗"
  IO.println "║         Levi-Civita Comprehensive Benchmarks                 ║"
  IO.println "╠══════════════════════════════════════════════════════════════╣"
  IO.println "║  Core    = Sorted Array, Rat coefficients (baseline)         ║"
  IO.println "║  Field   = HashMap, Rat coefficients                         ║"
  IO.println "║  FastLC  = Sorted Array, Float coefficients (speed focus)    ║"
  IO.println "║  BinaryLC= Sorted Array w/ binary search, Rat coefficients   ║"
  IO.println "╚══════════════════════════════════════════════════════════════╝"
  IO.println ""

  IO.println "━━━ ADDITION (accumulating, 10000 ops) ━━━"
  BenchAll.benchAddCore 10000
  BenchAll.benchAddField 10000
  BenchAll.benchAddFast 10000
  BenchAll.benchAddBinary 10000
  IO.println ""

  IO.println "━━━ MULTIPLICATION (single operation, 10000 ops) ━━━"
  BenchAll.benchMulCore 10000
  BenchAll.benchMulField 10000
  BenchAll.benchMulFast 10000
  BenchAll.benchMulBinary 10000
  IO.println ""

  IO.println "━━━ POWER x^10 (10000 ops) ━━━"
  BenchAll.benchPowCore 10000 10
  BenchAll.benchPowFast 10000 10
  BenchAll.benchPowBinary 10000 10
  IO.println ""

  IO.println "━━━ DERIVATIVE of x³ (10000 ops) ━━━"
  BenchAll.benchDerivCore 10000
  BenchAll.benchDerivFast 10000
  BenchAll.benchDerivBinary 10000
  IO.println ""

  IO.println "━━━ INVERSION (10 terms, 1000 ops) ━━━"
  BenchAll.benchInvertCore 1000
  BenchAll.benchInvertFast 1000
  BenchAll.benchInvertBinary 1000
  IO.println ""

  IO.println "━━━ POWER x^20 (large coefficients, 1000 ops) ━━━"
  BenchAll.benchPowCore 1000 20
  BenchAll.benchPowFast 1000 20
  BenchAll.benchPowBinary 1000 20
  IO.println ""

  IO.println "Done. FastLC uses Float arithmetic - expect 2-10x speedup."
