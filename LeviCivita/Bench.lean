import LeviCivita.Core
import LeviCivita.Field

/-!
# Levi-Civita Benchmarks

Performance benchmarks comparing Core (sorted array) vs Field (HashMap) implementations.
-/

namespace Bench

-- Type aliases to avoid ambiguity
private abbrev CLC := LeviCivita.Core.LC
private abbrev FLC := LeviCivita.Field.LC

namespace Core

private def eps : CLC := LeviCivita.Core.LC.epsilon

/-- Benchmark addition -/
def benchAdd (n : Nat) : IO Unit := do
  let x : CLC := (1 : CLC) + eps + eps * eps
  let mut acc : CLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    acc := acc + x
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"Core.add ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

/-- Benchmark multiplication -/
def benchMul (n : Nat) : IO Unit := do
  let x : CLC := (1 : CLC) + eps
  let mut acc : CLC := 1
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    acc := acc * x
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"Core.mul ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

/-- Benchmark power -/
@[noinline] def benchPow (n : Nat) (exp : Nat) : IO Unit := do
  let x : CLC := (1 : CLC) + eps
  let mut result : CLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := x ^ exp
  let elapsed := (← IO.monoNanosNow) - start
  if result.terms.size > 1000000 then IO.println "unexpected"
  IO.println s!"Core.pow^{exp} ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

/-- Benchmark derivative computation -/
@[noinline] def benchDerivative (n : Nat) : IO Unit := do
  let f := fun (x : CLC) => x * x * x  -- x³
  let pt : CLC := 3  -- evaluate at x=3
  let mut result : Rat := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := LeviCivita.Core.LC.derivative f pt
  let elapsed := (← IO.monoNanosNow) - start
  if result > 1000000 then IO.println "unexpected"
  IO.println s!"Core.derivative ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

/-- Benchmark inversion -/
@[noinline] def benchInvert (n : Nat) : IO Unit := do
  let x : CLC := (2 : CLC) + eps
  let mut result : Option CLC := none
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := LeviCivita.Core.LC.invert x 10
  let elapsed := (← IO.monoNanosNow) - start
  if result.isSome && result.get!.terms.size > 1000000 then IO.println "unexpected"
  IO.println s!"Core.invert ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

end Core

namespace Field

private def eps : FLC := LeviCivita.Field.LC.epsilon

/-- Benchmark addition -/
def benchAdd (n : Nat) : IO Unit := do
  let x : FLC := (1 : FLC) + eps + eps * eps
  let mut acc : FLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    acc := acc + x
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"Field.add ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

/-- Benchmark multiplication -/
def benchMul (n : Nat) : IO Unit := do
  let x : FLC := (1 : FLC) + eps
  let mut acc : FLC := 1
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    acc := acc * x
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"Field.mul ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

/-- Benchmark power -/
@[noinline] def benchPow (n : Nat) (exp : Nat) : IO Unit := do
  let x : FLC := (1 : FLC) + eps
  let mut result : FLC := LeviCivita.Field.LC.zero
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := x ^ exp
  let elapsed := (← IO.monoNanosNow) - start
  if result.coeffs.size > 1000000 then IO.println "unexpected"
  IO.println s!"Field.pow^{exp} ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

/-- Benchmark exp function -/
@[noinline] def benchExp (n : Nat) (terms : Nat) : IO Unit := do
  let mut result : FLC := LeviCivita.Field.LC.zero
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := LeviCivita.Field.LC.exp eps terms
  let elapsed := (← IO.monoNanosNow) - start
  if result.coeffs.size > 1000000 then IO.println "unexpected"
  IO.println s!"Field.exp({terms} terms) ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

/-- Benchmark derivative computation -/
@[noinline] def benchDerivative (n : Nat) : IO Unit := do
  let f := fun (x : FLC) => x * x * x  -- x³
  let pt : FLC := 3  -- evaluate at x=3
  let mut result : Rat := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := LeviCivita.Field.LC.derivative f pt
  let elapsed := (← IO.monoNanosNow) - start
  if result > 1000000 then IO.println "unexpected"
  IO.println s!"Field.derivative ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

/-- Benchmark inversion -/
@[noinline] def benchInvert (n : Nat) : IO Unit := do
  let x : FLC := (2 : FLC) + eps
  let mut result : Option FLC := none
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := LeviCivita.Field.LC.invert x 10
  let elapsed := (← IO.monoNanosNow) - start
  if result.isSome && result.get!.coeffs.size > 1000000 then IO.println "unexpected"
  IO.println s!"Field.invert ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

end Field

end Bench

/-- Non-accumulating mul benchmark -/
@[noinline] def benchMulSingle (n : Nat) : IO Unit := do
  let x : Bench.CLC := (1 : Bench.CLC) + Bench.Core.eps + Bench.Core.eps * Bench.Core.eps
  let y : Bench.CLC := (2 : Bench.CLC) + Bench.Core.eps
  let mut result : Bench.CLC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := x * y
  let elapsed := (← IO.monoNanosNow) - start
  -- Force use of result to prevent DCE
  if result.terms.size > 1000000 then IO.println "unexpected"
  IO.println s!"Core.mul_single ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

/-- Non-accumulating mul benchmark -/
@[noinline] def benchMulSingleField (n : Nat) : IO Unit := do
  let x : Bench.FLC := (1 : Bench.FLC) + Bench.Field.eps + Bench.Field.eps * Bench.Field.eps
  let y : Bench.FLC := (2 : Bench.FLC) + Bench.Field.eps
  let mut result : Bench.FLC := LeviCivita.Field.LC.zero
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    result := x * y
  let elapsed := (← IO.monoNanosNow) - start
  -- Force use of result to prevent DCE
  if result.coeffs.size > 1000000 then IO.println "unexpected"
  IO.println s!"Field.mul_single ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

/-- Run all benchmarks -/
def main : IO Unit := do
  IO.println "=== Levi-Civita Benchmarks ==="
  IO.println ""

  IO.println "--- Addition (accumulating) ---"
  Bench.Core.benchAdd 10000
  Bench.Field.benchAdd 10000
  IO.println ""

  IO.println "--- Multiplication (single, non-accumulating) ---"
  benchMulSingle 10000
  benchMulSingleField 10000
  IO.println ""

  IO.println "--- Multiplication (accumulating - gets slow) ---"
  Bench.Core.benchMul 100
  Bench.Field.benchMul 100
  IO.println ""

  IO.println "--- Power (x^10) ---"
  Bench.Core.benchPow 10000 10
  Bench.Field.benchPow 10000 10
  IO.println ""

  IO.println "--- Derivative ---"
  Bench.Core.benchDerivative 10000
  Bench.Field.benchDerivative 10000
  IO.println ""

  IO.println "--- Inversion ---"
  Bench.Core.benchInvert 1000
  Bench.Field.benchInvert 1000
  IO.println ""

  IO.println "--- Transcendentals (Field only) ---"
  Bench.Field.benchExp 1000 5
  Bench.Field.benchExp 1000 10
  Bench.Field.benchExp 100 20

  IO.println ""
  IO.println "Done."
