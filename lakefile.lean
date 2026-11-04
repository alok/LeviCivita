import Lake
open Lake DSL

package LeviCivita where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib LeviCivita where
  globs := #[.submodules `LeviCivita]

-- Benchmark executables
lean_exe lcbench where
  root := `LeviCivita.Bench

lean_exe nativebench where
  root := `LeviCivita.NativeBench

/-- Modules shared by the test driver: helpers and the randomized properties. -/
lean_lib TestSupport where
  roots := #[`tests.Harness, `tests.Properties]

@[test_driver]
lean_exe tests where
  root := `tests.Main
