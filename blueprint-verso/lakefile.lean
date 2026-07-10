import Lake

open Lake DSL

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint" @ "v4.30.0"
require FABL from ".."

package FABLBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib FABLBlueprint where

lean_exe «blueprint-gen» where
  root := `FABLBlueprintMain
