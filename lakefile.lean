import Lake
open Lake DSL

package «lean-yo» where
  -- Add package configuration options here

-- Audit baseline: Mathlib master on 2026-08-24.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "dc84fcbe9e049439c1c36d6db290cc0565f77788"

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
