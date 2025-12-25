import Lake
open Lake DSL

package LeviCivita where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0-rc1"

@[default_target]
lean_lib LeviCivita where
  globs := #[.submodules `LeviCivita]

-- Benchmark executables
lean_exe lcbench where
  root := `LeviCivita.Bench

lean_exe nativebench where
  root := `LeviCivita.NativeBench

lean_exe computable_test where
  root := `Main
