import Lean
import Lean.Meta.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Yoneda
import LeanYo.Core.LemmaRegistry
import LeanYo.Core.SimpRunner

namespace LeanYo

open Lean Meta

/-- Simp set for functoriality (map_id, map_comp) -/
def functorialitySimpSet : Array Name := functorialityLemmas

/-- Simp set for natural transformation naturality -/
def naturalitySimpSet : Array Name := naturalityLemmas

/-- Simp set for whiskering and horizontal composition -/
def whiskeringSimpSet : Array Name := whiskeringLemmas

/-- Simp set for Yoneda isomorphisms -/
def yonedaSimpSet : Array Name := yonedaLemmas

/-- Combined simp set for all category theory operations -/
def categoryTheorySimpSet : Array Name := categoryTheoryLemmas

def applySimpSet (goal : Expr) (simpSet : Array Name) : MetaM (Option Expr) :=
  simpExpr goal simpSet

def applyFunctorialitySimp (goal : Expr) : MetaM (Option Expr) :=
  applySimpSet goal functorialitySimpSet

def applyNaturalitySimp (goal : Expr) : MetaM (Option Expr) :=
  applySimpSet goal naturalitySimpSet

def applyWhiskeringSimp (goal : Expr) : MetaM (Option Expr) :=
  applySimpSet goal whiskeringSimpSet

def applyYonedaSimp (goal : Expr) : MetaM (Option Expr) :=
  applySimpSet goal yonedaSimpSet

def applyCategoryTheorySimp (goal : Expr) : MetaM (Option Expr) :=
  applySimpSet goal categoryTheorySimpSet

private def goalContains (goal : Expr) (substr : String) : MetaM Bool := do
  return ((← ppExpr goal).pretty).contains substr

def isFunctorialityGoal (goal : Expr) : MetaM Bool := do
  return (← goalContains goal "Functor.map") &&
    ((← goalContains goal "map_id") || (← goalContains goal "map_comp"))

def isNaturalityGoal (goal : Expr) : MetaM Bool := do
  return (← goalContains goal "NatTrans.app") && (← goalContains goal "Category.comp")

def isWhiskeringGoal (goal : Expr) : MetaM Bool := do
  return (← goalContains goal "whisker") ||
    ((← goalContains goal "◫") || (← goalContains goal "≫"))

def isYonedaGoal (goal : Expr) : MetaM Bool := do
  return (← goalContains goal "yoneda") || (← goalContains goal "coyoneda")

def smartSimp (goal : Expr) : MetaM (Option Expr) := do
  if ← isFunctorialityGoal goal then
    applyFunctorialitySimp goal
  else if ← isNaturalityGoal goal then
    applyNaturalitySimp goal
  else if ← isWhiskeringGoal goal then
    applyWhiskeringSimp goal
  else if ← isYonedaGoal goal then
    applyYonedaSimp goal
  else
    applyCategoryTheorySimp goal

end LeanYo
