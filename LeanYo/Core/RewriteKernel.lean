import Lean
import Lean.Meta.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.Category
import LeanYo.Core.Options
import LeanYo.Core.Attributes
import LeanYo.Core.LemmaRegistry
import LeanYo.Core.SimpRunner
import LeanYo.Core.SimpSets
import LeanYo.Utils

namespace LeanYo

open Lean Meta

def isYonedaCandidate (expr : Expr) : MetaM Bool := do
  let exprStr := (← ppExpr expr).pretty
  return exprStr.contains "yoneda" ||
         exprStr.contains "coyoneda" ||
         exprStr.contains "Hom(" ||
         exprStr.contains "Functor.map" ||
         exprStr.contains "Category.comp"

private def isEqApp (expr : Expr) : Bool :=
  expr.isAppOf ``Eq

private def eqSides? (expr : Expr) : Option (Expr × Expr) :=
  match expr with
  | .app (.app (.app (.const ``Eq _) _) lhs) rhs => some (lhs, rhs)
  | _ => none

private def isFunctorMapEquality (lhs rhs : Expr) : Bool :=
  lhs.isAppOf ``Functor.map || rhs.isAppOf ``Functor.map

private def replaceEqSides (expr : Expr) (newLhs newRhs : Expr) : Expr :=
  match expr with
  | .app (.app (.app f t) _) _ => mkApp (mkApp2 f t newLhs) newRhs
  | _ => expr

def applyYonedaIsomorphism (expr : Expr) : MetaM (Option Expr) := do
  match eqSides? expr with
  | some (lhs, rhs) =>
    if isFunctorMapEquality lhs rhs then
      return some (replaceEqSides expr lhs rhs)
    else
      return none
  | none => return none

def applyCoyonedaIsomorphism (expr : Expr) : MetaM (Option Expr) :=
  applyYonedaIsomorphism expr

def yonedaStep (goal : Expr) (direction : YoDirection) : MetaM (Option Expr) := do
  if !(← isYonedaCandidate goal) then
    return none
  match direction with
  | .covariant => applyYonedaIsomorphism goal
  | .contravariant => applyCoyonedaIsomorphism goal
  | .auto =>
    match ← applyYonedaIsomorphism goal with
    | some result => return some result
    | none => applyCoyonedaIsomorphism goal

private def exprPrettyContains (expr : Expr) (substr : String) : MetaM Bool := do
  return ((← ppExpr expr).pretty).contains substr

private def isNaturalityComposition (expr : Expr) : MetaM Bool := do
  return (← exprPrettyContains expr "NatTrans.app") &&
    (← exprPrettyContains expr "Category.comp")

def isNaturalitySquarePattern (expr : Expr) : MetaM Bool := do
  if !isEqApp expr then return false
  match eqSides? expr with
  | some (lhs, rhs) =>
    return (← isNaturalityComposition lhs) && (← isNaturalityComposition rhs)
  | none => return false

def applyNaturalityRewrite (goal : Expr) : MetaM (Option Expr) := do
  if !(← isNaturalitySquarePattern goal) then
    return none
  let env ← getEnv
  let registered := getNaturalityLemmas env
  for lemmaName in registered.toList do
    match ← simpExpr goal #[lemmaName] with
    | some result => return some result
    | none => continue
  simpExpr goal naturalitySimpLemmas

def naturalityStep (goal : Expr) : MetaM (Option Expr) := do
  if !(← isNaturalitySquarePattern goal) then
    return none
  applyNaturalityRewrite goal

def applyYoFuseRules (expr : Expr) : MetaM (Option Expr) := do
  let env ← getEnv
  let fuseLemmas := getYoFuseLemmas env
  if fuseLemmas.isEmpty then
    return none
  simpExpr expr fuseLemmas

def isNaturalitySquare (goal : Expr) : MetaM Bool :=
  isNaturalitySquarePattern goal

def isCandidateForRewriting (goal : Expr) : MetaM Bool := do
  return (← isCandidateGoal goal) || (← isNaturalitySquare goal)

private def yonedaThenSimp (goal : Expr) (direction : YoDirection) : MetaM (Option Expr) := do
  match ← yonedaStep goal direction with
  | none => return none
  | some g =>
    match ← smartSimp g with
    | some g' => return some g'
    | none => return some g

private def chainRewrite (goal : Expr) (maxSteps : Nat) (phases : List (Expr → MetaM (Option Expr))) :
    MetaM (Option Expr) := do
  let mut current := goal
  let mut steps := 0
  for phase in phases do
    if steps >= maxSteps then break
    match ← phase current with
    | none => continue
    | some next =>
      if next != current then
        current := next
        steps := steps + 1
  if steps > 0 then return some current else return none

/-- Attribute-driven and heuristic rewrites for programmatic use (e.g. future `yo` MetaM API). -/
def rewriteKernel (goal : Expr) (options : Options) : MetaM (Option Expr) := do
  let maxSteps := getNaturalityMaxSteps options
  let direction := getYoDirection options
  chainRewrite goal maxSteps [
    smartSimp,
    fun g => yonedaThenSimp g direction,
    naturalityStep,
    applyYoFuseRules
  ]

end LeanYo
