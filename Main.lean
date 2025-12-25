import LeviCivita.Core
open LeviCivita.Core LC

def main : IO Unit := do
  let x : LC := 1 + ε
  let y : LC := 1 - ε
  let z := x * y
  IO.println s!"x = {x}"
  IO.println s!"y = {y}"
  IO.println s!"x * y = {z}"
  
  if x > y then
    IO.println "x > y holds"
  else
    IO.println "x > y fails"

  let w := (2 : LC) * epsilon
  IO.println s!"2 * ε = {w}"
  
  let h_sq := H * H
  IO.println s!"H * H = {h_sq}"