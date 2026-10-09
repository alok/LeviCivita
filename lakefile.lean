import Lake
open Lake DSL

package LeviCivita where
  version := v!"0.2.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib LeviCivita where
  roots := #[`LeviCivita, `LeviCivita.Test, `LeviCivita.TestM2, `LeviCivita.AxiomAudit]
