import Lean
import Lean.Elab.Tactic
import LeanYo.Tactics.Common
import LeanYo.Tactics.Scripts
import LeanYo.Utils

namespace LeanYo

open Lean Elab Tactic

private def recordYoTelemetry (tacticName : String) (action : TacticM (List String)) : TacticM (List String) := do
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

elab "yo" : tactic => do
  let _ ← recordYoTelemetry "yo" runYoScripts

elab "yo" "at" h:ident : tactic => do
  let _ ← getFVarId h
  let _ ← recordYoTelemetry "yo" (runYoAt h)

elab "yo?" : tactic => do
  let rewrites ← recordYoTelemetry "yo?" runYoScripts
  logInfo m!"yo tactic applied: {rewrites}"

elab "yo.direction" " := " dir:ident : tactic => do
  let direction ← match dir.getId.toString with
    | "covariant" => pure YoDirection.covariant
    | "contravariant" => pure YoDirection.contravariant
    | "auto" => pure YoDirection.auto
    | _ => throwError "Invalid direction: {dir.getId}"
  liftM (m := IO) (setYoDirectionIO direction)

end LeanYo
