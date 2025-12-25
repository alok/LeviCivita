/-
Copyright (c) 2024-2025. All rights reserved.
Released under MIT license.
-/
import VersoManual
import Manual

open Verso.Genre Manual

def config : Config where
  emitTeX := false
  emitHtmlSingle := true
  emitHtmlMulti := true
  extraFiles := [("static", "static")]
  sourceLink := some "https://github.com/alok/LeviCivita"
  issueLink := some "https://github.com/alok/LeviCivita/issues"

def main := manualMain (%doc Manual) (config := config)
