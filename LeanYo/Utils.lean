import Lean
import Lean.Meta.Basic
import LeanYo.Core.Options

namespace LeanYo

open Lean Meta

structure PerformanceMetrics where
  tacticName : String
  startTime : Nat
  endTime : Nat
  rewriteCount : Nat
  success : Bool
  failureReason : Option String

structure TelemetryData where
  tacticInvocations : Nat := 0
  totalTime : Nat := 0
  totalRewrites : Nat := 0
  failureCount : Nat := 0
  failureReasons : List String := []
  deriving Inhabited

def isCandidateGoal (goal : Expr) : MetaM Bool := do
  let goalStr := (← ppExpr goal).pretty
  return goalStr.contains "Category.comp" ||
         goalStr.contains "Functor.map" ||
         goalStr.contains "NatTrans.app"

def extractFunctor (expr : Expr) : Option Expr :=
  match expr with
  | .app (.const `Functor.map _) f => some f
  | _ => none

def extractNaturalTransformation (expr : Expr) : Option Expr :=
  match expr with
  | .app (.const `NatTrans.app _) η => some η
  | _ => none

def isCompositionChain (expr : Expr) : Bool :=
  match expr with
  | .app (.app (.const `Category.comp _) _) _ => true
  | _ => false

def inferYoDirection (_goal : Expr) : MetaM YoDirection := do
  return .auto

def withTimeout (_timeoutMs : Nat) (action : MetaM (Option α)) : MetaM (Option α) :=
  action

def withTimeout' (timeoutMs : Nat) (action : MetaM (Option α)) : MetaM (Option α) :=
  withTimeout timeoutMs action

def measurePerformance {α} (tacticName : String) (action : MetaM α) : MetaM (α × PerformanceMetrics) := do
  let startTime ← IO.monoMsNow
  let rewriteCount := 0
  let mut success := false
  let mut failureReason : Option String := none
  let result ← try
    let res ← action
    success := true
    pure res
  catch e =>
    failureReason := some (← e.toMessageData.toString)
    throw e
  let endTime ← IO.monoMsNow
  let metrics : PerformanceMetrics := {
    tacticName := tacticName
    startTime := startTime
    endTime := endTime
    rewriteCount := rewriteCount
    success := success
    failureReason := failureReason
  }
  return (result, metrics)

initialize telemetryDataRef : IO.Ref TelemetryData ← IO.mkRef {}

def recordTelemetry (metrics : PerformanceMetrics) : IO Unit := do
  let data ← telemetryDataRef.get
  let newData := {
    tacticInvocations := data.tacticInvocations + 1
    totalTime := data.totalTime + (metrics.endTime - metrics.startTime)
    totalRewrites := data.totalRewrites + metrics.rewriteCount
    failureCount := if metrics.success then data.failureCount else data.failureCount + 1
    failureReasons := match metrics.failureReason with
      | none => data.failureReasons
      | some reason => reason :: data.failureReasons
  }
  telemetryDataRef.set newData

def getTelemetry : IO TelemetryData := telemetryDataRef.get

def resetTelemetry : IO Unit := telemetryDataRef.set {}

end LeanYo
