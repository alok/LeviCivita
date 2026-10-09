/-
Benchmark (not part of `lake build`): Float vs exact predicates vs SoS over `Poly ℤ ℤ`.

Run: `lake env lean --run bench/Bench.lean [nPoints] [nQueries] [gridSize]`

This runs in the Lean *interpreter* (a native `lean_exe` would have to compile every imported
Mathlib module to C), so absolute numbers are pessimistic; ratios are what matter.
-/
import LeviCivita.Geometry

open LeviCivita LeviCivita.Geometry LeviCivita.LazySign

/-- 64-bit LCG (Knuth's MMIX constants). -/
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- `n` pseudo-random points with integer coordinates in `[0, grid)`, and `m` index triples
(pairwise distinct). Returns the coordinates and the triples. -/
def mkInput (n m grid : Nat) : Array (Array Int) × Array (Nat × Nat × Nat × Nat) := Id.run do
  let mut s : UInt64 := 42
  let mut pts : Array (Array Int) := #[]
  for _ in [0:n] do
    s := lcg s; let a := (s >>> 33).toNat % grid
    s := lcg s; let b := (s >>> 33).toNat % grid
    pts := pts.push #[(a : Int), (b : Int)]
  let mut qs : Array (Nat × Nat × Nat × Nat) := #[]
  while qs.size < m do
    s := lcg s; let i := (s >>> 33).toNat % n
    s := lcg s; let k := (s >>> 33).toNat % n
    s := lcg s; let l := (s >>> 33).toNat % n
    s := lcg s; let o := (s >>> 33).toNat % n
    if i != k && i != l && k != l && o != i && o != k && o != l then
      qs := qs.push (i, k, l, o)
  return (pts, qs)

/-- Order-sensitive checksum of a sign sequence. -/
def mix (acc s : Int) : Int := (acc * 3 + (s + 1)) % 1000000007

def timeIt (label : String) (m : Nat) (act : Unit → IO Int) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← act ()
  let t1 ← IO.monoNanosNow
  let ms := (t1 - t0).toFloat / 1e6
  IO.println s!"{label}: {ms} ms total, {ms * 1000 / m.toFloat} µs/query (checksum {r})"

def bench (n : Nat) (hn : 0 < n) (m grid : Nat) : IO Unit := do
  let (pts, qs) := mkInput n m grid
  IO.println s!"n = {n} points, m = {m} queries, coordinates in [0, {grid})"
  let xi : Fin n → Fin 2 → Int := fun i j => (pts[i.1]!)[j.1]!
  let xf : Fin n → Fin 2 → Float := fun i j => Float.ofInt ((pts[i.1]!)[j.1]!)
  let fin (a : Nat) : Fin n := ⟨a % n, Nat.mod_lt _ hn⟩
  -- with tiny grids, many queries are degenerate and exercise the perturbation
  let zeroCount := qs.foldl (fun (acc : Int) (i, k, l, _) =>
    if orient2d (xi (fin i)) (xi (fin k)) (xi (fin l)) == 0 then acc + 1 else acc) 0
  let zeroCountC := qs.foldl (fun (acc : Int) (i, k, l, o) =>
    if incircle (xi (fin i)) (xi (fin k)) (xi (fin l)) (xi (fin o)) == 0 then acc + 1 else acc) 0
  IO.println s!"degenerate queries: orient2d {zeroCount}, incircle {zeroCountC}"
  let sgnF (x : Float) : Int := if x > 0 then 1 else if x < 0 then -1 else 0
  timeIt "orient2d  Float          " m fun _ => pure <| qs.foldl (fun (acc : Int) (i, k, l, _) =>
    mix acc <| sgnF (orient2d (xf (fin i)) (xf (fin k)) (xf (fin l)))) 0
  timeIt "orient2d  exact ℤ        " m fun _ => pure <| qs.foldl (fun (acc : Int) (i, k, l, _) =>
    mix acc <| (orient2d (xi (fin i)) (xi (fin k)) (xi (fin l))).sign) 0
  timeIt "orient2d  SoS Poly ℤ ℤ   " m fun _ => pure <| qs.foldl (fun (acc : Int) (i, k, l, _) =>
    mix acc <| (orient2dSoS 4 xi (fin i) (fin k) (fin l)).sign) 0
  timeIt "orient2d  lazy SoS       " m fun _ => pure <| qs.foldl (fun (acc : Int) (i, k, l, _) =>
    mix acc <| ((orient2dLazy 4 xi (fin i) (fin k) (fin l)).getD 0)) 0
  timeIt "incircle  Float          " m fun _ => pure <| qs.foldl (fun (acc : Int) (i, k, l, o) =>
    mix acc <| sgnF (incircle (xf (fin i)) (xf (fin k)) (xf (fin l)) (xf (fin o)))) 0
  timeIt "incircle  exact ℤ        " m fun _ => pure <| qs.foldl (fun (acc : Int) (i, k, l, o) =>
    mix acc <| (incircle (xi (fin i)) (xi (fin k)) (xi (fin l)) (xi (fin o))).sign) 0
  timeIt "incircle  SoS Poly ℤ ℤ   " m fun _ => pure <| qs.foldl (fun (acc : Int) (i, k, l, o) =>
    mix acc <| (incircleSoS 4 xi (fin i) (fin k) (fin l) (fin o)).sign) 0
  timeIt "incircle  lazy SoS       " m fun _ => pure <| qs.foldl (fun (acc : Int) (i, k, l, o) =>
    mix acc <| ((incircleLazy 4 xi (fin i) (fin k) (fin l) (fin o)).getD 0)) 0

def main (args : List String) : IO Unit := do
  let n := (args[0]? >>= String.toNat?).getD 10000
  let m := (args[1]? >>= String.toNat?).getD 10000
  let grid := (args[2]? >>= String.toNat?).getD 1000000
  if h : 4 ≤ n then bench n (by omega) m grid else IO.println "need at least 4 points"
