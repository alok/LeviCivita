import LeviCivita.Core

namespace LeviCivita.Field

open LeviCivita.Core

/-- Taylor series based exponential function for the rational-based Levi-Civita field. -/
def exp (x : LC) (terms : Nat := 10) : LC := Id.run do
  let mut result : LC := 1
  let mut power : LC := 1
  let mut fact : Rat := 1
  for n in [1:terms] do
    power := power * x
    fact := fact * n
    result := result + (LC.ofCoeff (1/fact)) * power
  result

/-- Taylor series based sine function. -/
def sin (x : LC) (terms : Nat := 10) : LC := Id.run do
  let mut result : LC := 0
  let mut power : LC := x
  let mut fact : Rat := 1
  for n in [1:terms] do
    if n % 2 == 1 then
      let sign : Rat := if (n / 2) % 2 == 0 then 1 else -1
      result := result + (LC.ofCoeff (sign / fact)) * power
    power := power * x
    fact := fact * (n + 1)
  result

/-- Taylor series based cosine function. -/
def cos (x : LC) (terms : Nat := 10) : LC := Id.run do
  let mut result : LC := 1
  let mut power : LC := 1
  let mut fact : Rat := 1
  for n in [1:terms] do
    power := power * x
    fact := fact * n
    if n % 2 == 0 then
      let sign : Rat := if (n / 2) % 2 == 0 then 1 else -1
      result := result + (LC.ofCoeff (sign / fact)) * power
  result

end LeviCivita.Field
