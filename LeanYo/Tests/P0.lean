import LeanYo
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans

open CategoryTheory

namespace LeanYo.Tests.P0

/-! ### Manual proofs (extraction targets; must always build) -/

section Manual

example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
    F.map (𝟙 X) = 𝟙 (F.obj X) := by
  simp

example {C D : Type} [Category C] [Category D] (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by
  simp

example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  rw [← NatTrans.naturality]

example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X : C) :
    η.app X ≫ G.map (𝟙 X) = F.map (𝟙 X) ≫ η.app X := by
  rw [← NatTrans.naturality]

example {C D E : Type} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E) (X : C) :
    (F ⋙ G).map (𝟙 X) = 𝟙 ((F ⋙ G).obj X) := by
  simp only [Functor.map_id]

example {C D E : Type} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := by
  rfl

end Manual

/-! ### Tactic regression (`yo`, `naturality!`) -/

section Tactic

example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
    F.map (𝟙 X) = 𝟙 (F.obj X) := by
  yo

example {C D : Type} [Category C] [Category D] (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by
  yo

example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  naturality!

example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X : C) :
    η.app X ≫ G.map (𝟙 X) = F.map (𝟙 X) ≫ η.app X := by
  naturality!

example {C D E : Type} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E) (X : C) :
    (F ⋙ G).map (𝟙 X) = 𝟙 ((F ⋙ G).obj X) := by
  yo

example {C D E : Type} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := by
  yo

end Tactic

end LeanYo.Tests.P0
