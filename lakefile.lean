import Lake
open Lake DSL

package «lean-yo» where
  -- Add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

@[default_target]
lean_lib «LeanYo» where
  -- Add library configuration options here

-- Test targets
lean_exe testMinimal where
  root := `test_minimal

lean_exe testProduction where
  root := `test_production_readiness
