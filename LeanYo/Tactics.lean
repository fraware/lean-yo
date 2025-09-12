import Lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NaturalTransformation
import LeanYo.Options
import LeanYo.RewriteKernel
import LeanYo.Utils
import LeanYo.SimpSets

namespace LeanYo

-- Global options state
def globalOptions : IO.Ref Options := unsafePerformIO (IO.mkRef {})

-- Get current options
def getOptions : IO Options := globalOptions.get

-- Set options
def setOptions (opts : Options) : IO Unit := globalOptions.set opts

-- Update yo direction
def setYoDirection (dir : YoDirection) : IO Unit := do
  let opts ← getOptions
  setOptions (setYoDirection opts dir)

-- Update naturality max steps
def setNaturalityMaxSteps (steps : Nat) : IO Unit := do
  let opts ← getOptions
  setOptions (setNaturalityMaxSteps opts steps)

-- Update naturality timeout
def setNaturalityTimeout (timeout : Nat) : IO Unit := do
  let opts ← getOptions
  setOptions (setNaturalityTimeout opts timeout)

-- Core yo tactic implementation
def yoTactic (goal : Expr) : MetaM (Option Expr) := do
  let opts ← liftM (m := IO) getOptions

  -- Check if this is a candidate for yo rewriting
  if !(← isCandidateForRewriting goal) then
    return none

  -- Apply smart simp first
  match ← smartSimp goal with
  | some newGoal => return some newGoal
  | none => pure ()

  -- Apply rewrite kernel
  match ← rewriteKernel goal opts with
  | some newGoal => return some newGoal
  | none => return none

-- Core naturality! tactic implementation
def naturalityTactic (goal : Expr) : MetaM (Option Expr) := do
  let opts ← liftM (m := IO) getOptions

  -- Check if this is a naturality square
  if !(isNaturalitySquare goal) then
    return none

  -- Apply naturality simp first
  match ← applyNaturalitySimp goal with
  | some newGoal => return some newGoal
  | none => pure ()

  -- Apply naturality step with timeout
  let timeoutMs := getNaturalityTimeout opts
  match ← withTimeout timeoutMs (naturalityStep goal) with
  | some newGoal => return some newGoal
  | none => return none

-- Debug version that prints the exact rewrites used
def yoDebugTactic (goal : Expr) : MetaM (Option (Expr × List String)) := do
  let opts ← liftM (m := IO) getOptions
  let mut rewrites : List String := []

  -- Check if this is a candidate for yo rewriting
  if !(← isCandidateForRewriting goal) then
    return none

  -- Apply smart simp with debug info
  match ← smartSimp goal with
  | some newGoal =>
    rewrites := rewrites ++ ["Applied smart simp"]
    let goal := newGoal
  | none => pure ()

  -- Apply rewrite kernel with debug info
  match ← rewriteKernel goal opts with
  | some newGoal =>
    rewrites := rewrites ++ ["Applied Yoneda isomorphism", "Applied naturality rewrites"]
    return some (newGoal, rewrites)
  | none => return none

-- Debug version for naturality!
def naturalityDebugTactic (goal : Expr) : MetaM (Option (Expr × List String)) := do
  let opts ← liftM (m := IO) getOptions
  let mut rewrites : List String := []

  -- Check if this is a naturality square
  if !(isNaturalitySquare goal) then
    return none

  -- Apply naturality simp with debug info
  match ← applyNaturalitySimp goal with
  | some newGoal =>
    rewrites := rewrites ++ ["Applied naturality simp"]
    let goal := newGoal
  | none => pure ()

  -- Apply naturality step with debug info
  let timeoutMs := getNaturalityTimeout opts
  match ← withTimeout timeoutMs (naturalityStep goal) with
  | some newGoal =>
    rewrites := rewrites ++ ["Applied naturality square rewrite"]
    return some (newGoal, rewrites)
  | none => return none

-- Tactic implementations for Lean 4
open Lean Elab Tactic

-- yo tactic
elab "yo" : tactic => do
  let goal ← getMainTarget
  let opts ← liftM (m := IO) getOptions

  -- Measure performance
  let (result, metrics) ← measurePerformance "yo" do
    yoTactic goal

  -- Record telemetry
  liftM (m := IO) (recordTelemetry metrics)

  match result with
  | some newGoal =>
    replaceMainTarget newGoal
  | none =>
    throwError "yo tactic failed to rewrite the goal"

-- yo at h tactic
elab "yo" "at" h:ident : tactic => do
  let fvarId ← getFVarId h
  let goal ← getLocalDecl fvarId
  let opts ← liftM (m := IO) getOptions

  -- Measure performance
  let (result, metrics) ← measurePerformance "yo" do
    yoTactic goal.type

  -- Record telemetry
  liftM (m := IO) (recordTelemetry metrics)

  match result with
  | some newType =>
    let newGoal ← mkEq goal.type newType
    let proof ← mkEqRefl goal.type
    replaceLocalDecl fvarId newType proof
  | none =>
    throwError "yo tactic failed to rewrite the hypothesis"

-- naturality! tactic
elab "naturality!" : tactic => do
  let goal ← getMainTarget
  let opts ← liftM (m := IO) getOptions

  -- Measure performance
  let (result, metrics) ← measurePerformance "naturality!" do
    naturalityTactic goal

  -- Record telemetry
  liftM (m := IO) (recordTelemetry metrics)

  match result with
  | some newGoal =>
    replaceMainTarget newGoal
  | none =>
    throwError "naturality! tactic failed to solve the naturality square"

-- yo? debug tactic
elab "yo?" : tactic => do
  let goal ← getMainTarget
  let opts ← liftM (m := IO) getOptions

  -- Measure performance
  let (result, metrics) ← measurePerformance "yo?" do
    yoDebugTactic goal

  -- Record telemetry
  liftM (m := IO) (recordTelemetry metrics)

  match result with
  | some (newGoal, rewrites) =>
    logInfo m!"yo tactic applied rewrites: {rewrites}"
    replaceMainTarget newGoal
  | none =>
    throwError "yo? tactic failed to rewrite the goal"

-- naturality? debug tactic
elab "naturality?" : tactic => do
  let goal ← getMainTarget
  let opts ← liftM (m := IO) getOptions

  -- Measure performance
  let (result, metrics) ← measurePerformance "naturality?" do
    naturalityDebugTactic goal

  -- Record telemetry
  liftM (m := IO) (recordTelemetry metrics)

  match result with
  | some (newGoal, rewrites) =>
    logInfo m!"naturality! tactic applied rewrites: {rewrites}"
    replaceMainTarget newGoal
  | none =>
    throwError "naturality? tactic failed to solve the naturality square"

-- Option setting tactics
elab "yo.direction" " := " dir:ident : tactic => do
  let direction := match dir.getId.toString with
    | "covariant" => YoDirection.covariant
    | "contravariant" => YoDirection.contravariant
    | "auto" => YoDirection.auto
    | _ => throwError "Invalid direction: {dir.getId}"
  liftM (m := IO) (setYoDirection direction)

elab "naturality.maxSteps" " := " steps:num : tactic => do
  liftM (m := IO) (setNaturalityMaxSteps steps.getNat)

elab "naturality.timeout" " := " timeout:num "ms" : tactic => do
  liftM (m := IO) (setNaturalityTimeout timeout.getNat)

end LeanYo
