import LeanYo
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Yoneda

open CategoryTheory Opposite

namespace LeanYo.Tests.P2

/-! ### Manual proofs (Yoneda API on Mathlib 4.31) -/

section Manual

example {C : Type} [Category C] (X : C) :
    (yoneda.obj X).map (𝟙 (op X)) = 𝟙 _ := by
  simp only [Functor.map_id]

example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
    (F ⋙ yoneda).obj X = yoneda.obj (F.obj X) := by
  rfl

end Manual

/-! ### Tactic regression -/

section Tactic

example {C : Type} [Category C] (X : C) :
    (yoneda.obj X).map (𝟙 (op X)) = 𝟙 _ := by
  yo

example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
    (F ⋙ yoneda).obj X = yoneda.obj (F.obj X) := by
  yo

end Tactic

end LeanYo.Tests.P2
