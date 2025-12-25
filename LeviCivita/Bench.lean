import LeviCivita.Core
import LeviCivita.Field
import LeviCivita.Fast
import LeviCivita.UltraFast
import LeviCivita.PackedLC

/-!
# Levi-Civita Benchmarks

Comprehensive benchmarks comparing different implementations.
-/

namespace Bench

open LeviCivita.Core
open LeviCivita.Fast
open LeviCivita.UltraFast
open LeviCivita.Packed

def benchAddCore (n : Nat) : IO Unit := do
  let eps := LeviCivita.Core.LC.epsilon
  let x : LeviCivita.Core.LC := (1 : LeviCivita.Core.LC) + eps + eps * eps
  let mut acc : LeviCivita.Core.LC := 0
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    acc := acc + x
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"Core.add ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def benchMulCore (n : Nat) : IO Unit := do
  let eps := LeviCivita.Core.LC.epsilon
  let x : LeviCivita.Core.LC := (1 : LeviCivita.Core.LC) + eps
  let mut acc : LeviCivita.Core.LC := 1
  let start ← IO.monoNanosNow
  for _ in [0:n] do
    acc := acc * x
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"Core.mul ({n} ops): {elapsed / 1000000}ms ({elapsed / n}ns/op)"

def main : IO Unit := do
  IO.println "=== Levi-Civita Benchmarks ==="
  IO.println ""

  IO.println "--- Addition (10000 ops) ---"
  benchAddCore 10000
  IO.println ""

  IO.println "--- Multiplication (1000 ops) ---"
  benchMulCore 1000
  IO.println ""

  IO.println "Done."

end Bench