/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# `#assert_axioms`: fail the build on non-standard axioms

`#assert_axioms c₁ c₂ …` collects the axioms each constant depends on (transitively, like
`#print axioms`) and throws an error unless every axiom is in the allow-list
`propext`, `Classical.choice`, `Quot.sound`.
So `sorryAx`, `Lean.ofReduceBool` (from `native_decide`), `Lean.trustCompiler` and any
user-declared `axiom` all fail it. On success it logs the axioms, matching `#print axioms`.
-/

namespace LeviCivita

open Lean Elab Command

/-- The only axioms a verified declaration may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#assert_axioms c₁ c₂ …` errors if any `cᵢ` depends on an axiom outside `allowedAxioms`. -/
elab "#assert_axioms " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter (· ∉ allowedAxioms)
    if bad.isEmpty then
      logInfoAt id m!"'{n}' depends on axioms: {axs.toList}"
    else
      logErrorAt id m!"'{n}' depends on forbidden axioms {bad.toList} (all axioms: {axs.toList})"

end LeviCivita
