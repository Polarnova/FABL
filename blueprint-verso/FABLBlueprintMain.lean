/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABLBlueprint.Site
import VersoBlueprint.PreviewManifest
import FABLBlueprint.Blueprint

def main (args : List String) : IO UInt32 := do
  let profile ← BlueprintSite.readProfile
  let fablRevision ← BlueprintSite.sourceRevision "FABL_SOURCE_REVISION" "main"
  let probabilityRevision ←
    BlueprintSite.sourceRevision "PROBABILITY_APPROXIMATION_SOURCE_REVISION" "v0.9.6"
  let mathlibRevision ← BlueprintSite.sourceRevision "MATHLIB_SOURCE_REVISION" "v4.32.0"
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc FABLBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (config := BlueprintSite.renderConfig profile #[
      .github "FABL/" "Polarnova/FABL" fablRevision,
      .github "ProbabilityApproximation/" "Polarnova/ProbabilityApproximation" probabilityRevision,
      .github "Mathlib/" "leanprover-community/mathlib4" mathlibRevision
    ])
