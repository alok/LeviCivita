/-
Copyright (c) 2024-2025. All rights reserved.
Released under MIT license.
-/
import Lake
open Lake DSL
open System (FilePath)

require verso from git "https://github.com/leanprover/verso.git"@"v4.25.0"

package "levicivita-manual" where
  moreLeancArgs := #["-O0"]
  moreLinkArgs :=
    if System.Platform.isOSX then
      #["-Wl,-ignore_optimization_hints"]
    else #[]

@[default_target]
lean_lib Manual where

@[default_target]
lean_exe "generate-manual" where
  root := `Main
