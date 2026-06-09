import Lean
import Lean.Elab.Tactic
import Lean.Elab.Term

namespace LeanYo

open Lean Elab Tactic Term

private def lemmaSyntax (name : Name) : TacticM (TSyntax `term) := do
  let id := mkIdentFrom (← getRef) name
  let _ ← realizeGlobalConstNoOverloadWithInfo id
  return id

/-- Elaborate `simp only […]` from an explicit global lemma name list. -/
def simpOnlyNames (lemmas : Array Name) : TacticM Unit := do
  if lemmas.isEmpty then
    throwError "simpOnlyNames: empty lemma list"
  let args ← lemmas.mapM fun name => do
    let t ← lemmaSyntax name
    `(Parser.Tactic.simpLemma| $t:term)
  evalTactic (← `(tactic| simp only [$args,*]))

/-- Elaborate `simp only […] at h` for a hypothesis identifier. -/
def simpOnlyNamesAt (lemmas : Array Name) (h : TSyntax `ident) : TacticM Unit := do
  if lemmas.isEmpty then
    throwError "simpOnlyNamesAt: empty lemma list"
  let args ← lemmas.mapM fun name => do
    let t ← lemmaSyntax name
    `(Parser.Tactic.simpLemma| $t:term)
  evalTactic (← `(tactic| simp only [$args,*] at $h:ident))

/-- Elaborate `simp […]` (non-`only`) from an explicit global lemma name list. -/
def simpNames (lemmas : Array Name) : TacticM Unit := do
  if lemmas.isEmpty then
    throwError "simpNames: empty lemma list"
  let args ← lemmas.mapM fun name => do
    let t ← lemmaSyntax name
    `(Parser.Tactic.simpLemma| $t:term)
  evalTactic (← `(tactic| simp [$args,*]))

end LeanYo
