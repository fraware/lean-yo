import Lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Yoneda

namespace LeanYo

/-!
Single source of truth for Mathlib lemma names used by `SimpSets`, `RewriteKernel`,
and tactic scripts. Keep arrays small and goal-directed; extend via `@[naturality]`
and `@[yo.fuse]` for project-local rules.
-/

/-- `map_id` / `map_comp` for functoriality goals. -/
def functorialityLemmas : Array Lean.Name := #[
  ``CategoryTheory.Functor.map_id,
  ``CategoryTheory.Functor.map_comp,
  ``CategoryTheory.Functor.map_comp_assoc
]

/-- Core naturality and vertical-composition simp lemmas. -/
def naturalityLemmas : Array Lean.Name := #[
  ``CategoryTheory.NatTrans.naturality,
  ``CategoryTheory.NatTrans.comp_app
]

/-- Whiskering and horizontal composition component lemmas. -/
def whiskeringLemmas : Array Lean.Name := #[
  ``CategoryTheory.NatTrans.hcomp_id_app,
  ``CategoryTheory.NatTrans.id_hcomp_app,
  ``CategoryTheory.Functor.whiskerRight_app,
  ``CategoryTheory.Functor.whiskerLeft_app
]

/-- Yoneda functor map simp lemmas (Mathlib 4.31 `@[simps]` names). -/
def yonedaLemmas : Array Lean.Name := #[
  ``CategoryTheory.yoneda_obj_map,
  ``CategoryTheory.yoneda_map_app
]

/-- Full structured naturality script (after `rw [← naturality]`). -/
def naturalitySimpLemmas : Array Lean.Name :=
  naturalityLemmas ++ whiskeringLemmas ++ #[
    ``CategoryTheory.Functor.map_id,
    ``CategoryTheory.Functor.map_comp,
    ``CategoryTheory.Functor.map_comp_assoc,
    ``CategoryTheory.NatTrans.naturality_app
  ]

/-- `yo` functoriality pass. -/
def yoFunctorialityLemmas : Array Lean.Name := functorialityLemmas

/-- `yo` Yoneda pass. -/
def yoYonedaLemmas : Array Lean.Name := yonedaLemmas ++ functorialityLemmas

/-- Union used by heuristic `smartSimp` fallback. -/
def categoryTheoryLemmas : Array Lean.Name :=
  yoYonedaLemmas ++ naturalitySimpLemmas

end LeanYo
