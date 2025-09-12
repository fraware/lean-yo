import LeanYo
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NaturalTransformation
import Mathlib.CategoryTheory.Functor.Category

-- P1 Test Suite: whiskering, horizontal/vertical composition of NTs, bifunctors

namespace LeanYo.Tests.P1

-- Test horizontal composition of natural transformations
example {C D E : Type} [Category C] [Category D] [Category E]
  (F G H : C ⥤ D) (η : F ⟶ G) (θ : G ⟶ H) (X Y : C) (f : X ⟶ Y) :
  (η ≫ θ).app X ≫ H.map f = F.map f ≫ (η ≫ θ).app Y := by
  -- This should be solved by naturality! tactic
  naturality!

-- Test vertical composition of natural transformations
example {C D E : Type} [Category C] [Category D] [Category E]
  (F G : C ⥤ D) (H I : D ⥤ E) (η : F ⟶ G) (θ : H ⟶ I) (X Y : C) (f : X ⟶ Y) :
  (η ◫ θ).app X ≫ (I ⋙ G).map f = (H ⋙ F).map f ≫ (η ◫ θ).app Y := by
  -- This should be solved by naturality! tactic
  naturality!

-- Test whiskering on the left
example {C D E : Type} [Category C] [Category D] [Category E]
  (F G : C ⥤ D) (H : D ⥤ E) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  (H ◫ η).app X ≫ (H ⋙ G).map f = (H ⋙ F).map f ≫ (H ◫ η).app Y := by
  -- This should be solved by naturality! tactic
  naturality!

-- Test whiskering on the right
example {C D E : Type} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G H : D ⥤ E) (η : G ⟶ H) (X Y : C) (f : X ⟶ Y) :
  (η ◫ F).app X ≫ (H ⋙ F).map f = (G ⋙ F).map f ≫ (η ◫ F).app Y := by
  -- This should be solved by naturality! tactic
  naturality!

-- Test bifunctor functoriality
example {C D E : Type} [Category C] [Category D] [Category E]
  (F : C ⥤ D ⥤ E) (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map (f ≫ g) = F.map f ≫ F.map g := by
  -- This should be solved by yo tactic
  yo

-- Test bifunctor with natural transformations
example {C D E : Type} [Category C] [Category D] [Category E]
  (F G : C ⥤ D ⥤ E) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) (Z : D) :
  (η.app X).app Z ≫ (G.map f).app Z = (F.map f).app Z ≫ (η.app Y).app Z := by
  -- This should be solved by naturality! tactic
  naturality!

-- Test complex composition with multiple functors and natural transformations
example {C D E F : Type} [Category C] [Category D] [Category E] [Category F]
  (G : C ⥤ D) (H : D ⥤ E) (I : E ⥤ F) (η : H ⟶ H) (X Y : C) (f : X ⟶ Y) :
  (I ⋙ H ⋙ G).map f ≫ (I ⋙ η).app (G.obj Y) = (I ⋙ η).app (G.obj X) ≫ (I ⋙ H ⋙ G).map f := by
  -- This should be solved by naturality! tactic
  naturality!

end LeanYo.Tests.P1
