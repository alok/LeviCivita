import LeviCivita.Core
import Mathlib.RingTheory.HahnSeries.Basic

namespace LeviCivita.GrindTest

open LeviCivita.Core
open LeviCivita.Core.LC

-- Mark injectivity for grind
theorem toHahnSeries_injective' : Function.Injective toHahnSeries := sorry
attribute [grind inj] toHahnSeries_injective'

-- Mark homomorphism for grind
theorem toHahnSeries_add' (x y : LC) : toHahnSeries (x + y) = toHahnSeries x + toHahnSeries y := sorry
attribute [grind =] toHahnSeries_add'

theorem eq_iff_toHahnSeries_eq (x y : LC) : x = y ↔ toHahnSeries x = toHahnSeries y :=
  toHahnSeries_injective'.eq_iff.symm

-- Instead of marking ↔ with [grind =], let's try to use it as a parameter if needed
-- or just rely on [grind inj]

-- Now let's see if grind can prove commutativity of addition for LC
theorem add_comm_lc (x y : LC) : x + y = y + x := by
  apply toHahnSeries_injective'
  grind (config := { ring := false, linarith := false }) [_root_.add_comm]

end LeviCivita.GrindTest