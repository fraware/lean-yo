import Lean
import Lean.Elab.Tactic
import Mathlib.Tactic.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Yoneda
import LeanYo.Core.LemmaRegistry
import LeanYo.Tactics.SimpSyntax

namespace LeanYo

open Lean Elab Tactic

/-- Try a tactic script; restore goal state on failure. -/
private def tryScript (label : String) (script : TacticM Unit) : TacticM (Option String) := do
  let s ← saveState
  try
    withMainContext script
    return some label
  catch _ =>
    restoreState s
    return none

private def yoFunctoriality : TacticM Unit :=
  simpOnlyNames yoFunctorialityLemmas

private def yoYoneda : TacticM Unit :=
  simpOnlyNames yoYonedaLemmas

/-- Functoriality / Yoneda simp scripts in priority order. -/
def runYoScripts : TacticM (List String) := do
  if let some label ← tryScript "rfl" (evalTactic (← `(tactic| rfl))) then
    return [label]
  if let some label ← tryScript "functoriality_simp" yoFunctoriality then
    return [label]
  if let some label ← tryScript "yoneda_simp" yoYoneda then
    return [label]
  throwError "yo tactic failed: tried rfl, functoriality simp, and Yoneda simp"

def runYoAt (h : TSyntax `ident) : TacticM (List String) := do
  if let some label ← tryScript "simp_at" (simpOnlyNamesAt yoYonedaLemmas h) then
    return [label]
  throwError "yo tactic failed at hypothesis: tried functoriality/Yoneda simp"

private def naturalityRw : TacticM Unit := do
  evalTactic (← `(tactic| rw [← CategoryTheory.NatTrans.naturality]))

private def naturalityRwId : TacticM Unit := do
  evalTactic (← `(tactic|
    rw [← CategoryTheory.NatTrans.naturality,
      CategoryTheory.Functor.map_id, CategoryTheory.Category.comp_id,
      CategoryTheory.Category.comp_id]))

private def naturalitySimp : TacticM Unit :=
  simpOnlyNames naturalitySimpLemmas

private def naturalitySimpAggressive : TacticM Unit :=
  simpNames (naturalityLemmas ++ whiskeringLemmas)

/-- Naturality square scripts in priority order. -/
def runNaturalityScripts : TacticM (List String) := do
  if let some label ← tryScript "naturality_rw" naturalityRw then
    return [label]
  if let some label ← tryScript "naturality_rw_id" naturalityRwId then
    return [label]
  if let some label ← tryScript "naturality_simp" naturalitySimp then
    return [label]
  if let some label ← tryScript "naturality_simp!" naturalitySimpAggressive then
    return [label]
  throwError "naturality! tactic failed: tried rw, id-rw, simp only, and simp"

end LeanYo
