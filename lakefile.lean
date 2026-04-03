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
  globs := #[.submodules `LeanYo]

/-- Optional: `lake exe leanyo-benchmarks` runs IO smoke timing (see module docstring). -/
lean_exe «leanyo-benchmarks» where
  root := `LeanYo.Tests.Benchmarks
