import LeviCivita.Analysis

/-!
# `lake test`: analysis checks

Every check compares against a closed-form value. Exit code 1 on any failure.
-/

open LeviCivita.Fast FastLC

structure Check where
  name : String
  ok : Bool
  detail : String

def approx (a b : Float) (tol : Float := 1e-9) : Bool := (a - b).abs ≤ tol * (1.0 + b.abs)

def check (name : String) (got want : Float) (tol : Float := 1e-9) : Check :=
  { name, ok := approx got want tol, detail := s!"got {got}, want {want}" }

def checkSmall (name : String) (got : Float) (tol : Float := 1e-9) : Check :=
  { name, ok := got.abs ≤ tol, detail := s!"|·| = {got}" }

def analysisChecks : List Check :=
  let a := 0.7
  let sx := sin (ofFloat a + epsilon)
  let ex := exp (ofFloat a + epsilon)
  let lx := log (ofFloat a + epsilon)
  let px := rpow (ofFloat a + epsilon) 2.5
  [ check "sin jet ε¹" (epsCoeff sx 1) (Float.cos a),
    check "sin jet ε² = −sin/2" (epsCoeff sx 2) (-(Float.sin a) / 2),
    check "sin jet ε³ = −cos/6" (epsCoeff sx 3) (-(Float.cos a) / 6),
    check "exp jet ε²" (epsCoeff ex 2) (Float.exp a / 2),
    check "log jet ε² = −1/(2a²)" (epsCoeff lx 2) (-1 / (2 * a * a)),
    check "rpow jet ε² = p(p−1)a^(p−2)/2" (epsCoeff px 2) (2.5 * 1.5 * Float.pow a 0.5 / 2),
    check "sin² + cos² = 1 through ε⁴"
      (let s := sin (ofFloat a + epsilon); let c := cos (ofFloat a + epsilon)
       (List.range 5).foldl (fun m k => m + (epsCoeff (s * s + c * c) k - if k == 0 then 1 else 0).abs) 0)
      0 1e-12,
    check "exp ∘ log = id (ε² coefficient)" (epsCoeff (exp (log (ofFloat a + epsilon))) 2) 0 1e-12 ]

def main : IO UInt32 := do
  let all := analysisChecks
  let mut failed := 0
  for c in all do
    if c.ok then IO.println s!"  ok    {c.name}"
    else
      failed := failed + 1
      IO.println s!"  FAIL  {c.name}: {c.detail}"
  IO.println s!"{all.length - failed}/{all.length} passed"
  return if failed == 0 then 0 else 1
