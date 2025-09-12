import LeanYo
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans

-- P0 Test Suite: functoriality (map_id, map_comp) + simple NT squares

namespace LeanYo.Tests.P0

-- Test functoriality with map_id
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := by
  -- This should be solved by yo tactic
  yo

-- Test functoriality with map_comp
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map (f ≫ g) = F.map f ≫ F.map g := by
  -- This should be solved by yo tactic
  yo

-- Test simple natural transformation square
example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  -- This should be solved by naturality! tactic
  naturality!

-- Test naturality with identity morphism
example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X : C) :
  η.app X ≫ G.map (𝟙 X) = F.map (𝟙 X) ≫ η.app X := by
  -- This should be solved by naturality! tactic
  naturality!

-- Test composition of functors
example {C D E : Type} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E) (X : C) :
  (F ⋙ G).map (𝟙 X) = 𝟙 ((F ⋙ G).obj X) := by
  -- This should be solved by yo tactic
  yo

-- Test composition of functors with morphisms
example {C D E : Type} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E) (X Y : C) (f : X ⟶ Y) :
  (F ⋙ G).map f = G.map (F.map f) := by
  -- This should be solved by yo tactic
  yo

end LeanYo.Tests.P0
