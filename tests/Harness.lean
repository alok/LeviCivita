import LeviCivita.Analysis

/-! Shared helpers for `lake test`. -/

open LeviCivita.Fast FastLC

/-- One named check and what to print when it fails. -/
structure Check where
  name : String
  ok : Bool
  detail : String

/-- Relative closeness. -/
def approx (a b : Float) (tol : Float := 1e-9) : Bool := (a - b).abs ≤ tol * (1.0 + b.abs)

def check (name : String) (got want : Float) (tol : Float := 1e-9) : Check :=
  { name, ok := approx got want tol, detail := s!"got {got}, want {want}" }

def checkB (name : String) (ok : Bool) (detail : String := "") : Check := { name, ok, detail }

def checkOpt (name : String) (got : Option Float) (want : Float) (tol : Float := 1e-9) : Check :=
  { name, ok := (got.map fun g => approx g want tol).getD false, detail := s!"got {got}, want {want}" }

/-- Largest coefficient of `x − y` among terms of exponent `> −prec` (valuation `< prec`). -/
def diffBelow (x y : LC) (prec : Float) : Float :=
  ((x - y).terms.filter (·.exp > -prec)).foldl (fun m t => max m t.coeff.abs) 0
