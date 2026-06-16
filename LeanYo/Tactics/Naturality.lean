import Lean
import Lean.Elab.Tactic
import LeanYo.Tactics.Common
import LeanYo.Tactics.Scripts
import LeanYo.Utils

namespace LeanYo

open Lean Elab Tactic

private def recordNaturalityTelemetry (tacticName : String) (action : TacticM (List String)) : TacticM (List String) := do
  let startTime ← IO.monoMsNow
  let rewrites ← action
  let endTime ← IO.monoMsNow
  liftM (m := IO) (recordTelemetry {
    tacticName := tacticName
    startTime := startTime
    endTime := endTime
    rewriteCount := rewrites.length
    success := true
    failureReason := none
  })
  return rewrites

elab "naturality!" : tactic => do
  let _ ← recordNaturalityTelemetry "naturality!" runNaturalityScripts

elab "naturality?" : tactic => do
  let rewrites ← recordNaturalityTelemetry "naturality?" runNaturalityScripts
  logInfo m!"naturality! tactic applied: {rewrites}"

elab "naturality.maxSteps" " := " steps:num : tactic => do
  liftM (m := IO) (setNaturalityMaxStepsIO steps.getNat)

elab "naturality.timeout" " := " timeout:num "ms" : tactic => do
  liftM (m := IO) (setNaturalityTimeoutIO timeout.getNat)

end LeanYo
