import Lake
open Lake DSL

package «lean-yo» where
  -- Add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

-- require proofwidgets from git
--   "https://github.com/leanprover-community/ProofWidgets4.git" @ "v0.0.36"

@[default_target]
lean_lib «LeanYo» where
  -- Add library configuration options here
  globs := #[.submodules `LeanYo]

-- Test targets removed - using library tests instead
