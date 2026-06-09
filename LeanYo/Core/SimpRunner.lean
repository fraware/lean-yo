import Lean
import Lean.Meta.Basic
import Lean.Meta.Tactic.Simp.Main
import LeanYo.Core.LemmaRegistry

namespace LeanYo

open Lean Meta

/-- Build a `simp only` context from an explicit lemma name list. -/
def mkLemmaSimpContext (lemmas : Array Name) : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for name in lemmas do
    thms ← thms.addConst name
  Simp.mkContext (config := {}) (simpTheorems := #[thms])

/-- Simplify a proposition or type expression with an explicit lemma set. -/
def simpExpr (e : Expr) (lemmas : Array Name) : MetaM (Option Expr) := do
  if lemmas.isEmpty then return none
  let ctx ← mkLemmaSimpContext lemmas
  let (result, _) ← Meta.simp e ctx
  let newE := result.expr
  if newE != e then return some newE else return none

end LeanYo
