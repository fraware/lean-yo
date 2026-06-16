import Lake
open Lake DSL

package «lean-yo» where
  -- Add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

-- require proofwidgets from git
--   "https://github.com/leanprover-community/ProofWidgets4.git" @ "v0.0.36"

@[default_target]
lean_lib «LeanYo» where
  roots := #[`LeanYo, `LeanYo.Examples]

/-- Tactic regression tests (`Manual` + `Tactic` sections in `LeanYo.Tests.*`). -/
lean_lib «LeanYoTests» where
  globs := #[.submodules `LeanYo.Tests]

/-- Optional: `lake exe leanyo-benchmarks` runs IO smoke timing (see module docstring). -/
lean_exe «leanyo-benchmarks» where
  root := `LeanYo.Tests.Benchmarks
