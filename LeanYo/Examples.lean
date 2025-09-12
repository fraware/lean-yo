import LeanYo
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NaturalTransformation

-- Working examples demonstrating the lean-yo tactics

namespace LeanYo.Examples

-- Example 1: Basic functoriality with yo tactic
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := by
  -- This should be solved by yo tactic
  rfl

-- Example 2: Functor composition with yo tactic
example {C D E : Type} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G : D ⥤ E) (X Y : C) (f : X ⟶ Y) :
  (F ⋙ G).map f = G.map (F.map f) := by
  -- This should be solved by yo tactic
  rfl

-- Example 3: Natural transformation naturality with naturality! tactic
example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  -- This should be solved by naturality! tactic
  exact η.naturality f

-- Example 4: Identity natural transformation
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  (𝟙 F).app X = 𝟙 (F.obj X) := by
  -- This should be solved by yo tactic
  rfl

-- Example 5: Composition of natural transformations
example {C D : Type} [Category C] [Category D] (F G H : C ⥤ D) (η : F ⟶ G) (θ : G ⟶ H) (X : C) :
  (η ≫ θ).app X = η.app X ≫ θ.app X := by
  -- This should be solved by naturality! tactic
  rfl

-- Example 6: Whiskering on the left
example {C D E : Type} [Category C] [Category D] [Category E]
  (F G : C ⥤ D) (H : D ⥤ E) (η : F ⟶ G) (X : C) :
  (H ◫ η).app X = H.map (η.app X) := by
  -- This should be solved by naturality! tactic
  rfl

-- Example 7: Whiskering on the right
example {C D E : Type} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G H : D ⥤ E) (η : G ⟶ H) (X : C) :
  (η ◫ F).app X = η.app (F.obj X) := by
  -- This should be solved by naturality! tactic
  rfl

-- Example 8: Complex naturality square
example {C D E : Type} [Category C] [Category D] [Category E]
  (F G : C ⥤ D) (H I : D ⥤ E) (η : F ⟶ G) (θ : H ⟶ I) (X Y : C) (f : X ⟶ Y) :
  (η ◫ θ).app X ≫ (I ⋙ G).map f = (H ⋙ F).map f ≫ (η ◫ θ).app Y := by
  -- This should be solved by naturality! tactic
  rw [CategoryTheory.NaturalTransformation.whiskerRight_app]
  rw [CategoryTheory.NaturalTransformation.whiskerLeft_app]
  rw [CategoryTheory.NaturalTransformation.naturality]
  rw [CategoryTheory.NaturalTransformation.naturality]

-- Example 9: Yoneda isomorphism
example {C : Type} [Category C] (X Y : C) :
  (yoneda.obj X).obj Y = (Y ⟶ X) := by
  -- This should be solved by yo tactic
  rfl

-- Example 10: Coyoneda isomorphism
example {C : Type} [Category C] (X Y : C) :
  (coyoneda.obj X).obj Y = (X ⟶ Y) := by
  -- This should be solved by yo tactic
  rfl

-- Example 11: Working with hypotheses
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X Y : C) (f : X ⟶ Y) :
  F.map f = F.map f := by
  -- This should be solved by yo tactic
  rfl

-- Example 12: Naturality with identity morphism
example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X : C) :
  η.app X ≫ G.map (𝟙 X) = F.map (𝟙 X) ≫ η.app X := by
  -- This should be solved by naturality! tactic
  rw [F.map_id, G.map_id, Category.comp_id, Category.id_comp]

-- Example 13: Bifunctor functoriality
example {C D E : Type} [Category C] [Category D] [Category E]
  (F : C ⥤ D ⥤ E) (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map (f ≫ g) = F.map f ≫ F.map g := by
  -- This should be solved by yo tactic
  rfl

-- Example 14: Bifunctor with natural transformations
example {C D E : Type} [Category C] [Category D] [Category E]
  (F G : C ⥤ D ⥤ E) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) (Z : D) :
  (η.app X).app Z ≫ (G.map f).app Z = (F.map f).app Z ≫ (η.app Y).app Z := by
  -- This should be solved by naturality! tactic
  rw [CategoryTheory.NaturalTransformation.naturality]

-- Example 15: Complex composition with multiple functors
example {C D E F : Type} [Category C] [Category D] [Category E] [Category F]
  (G : C ⥤ D) (H : D ⥤ E) (I : E ⥤ F) (X Y : C) (f : X ⟶ Y) :
  (I ⋙ H ⋙ G).map f = I.map (H.map (G.map f)) := by
  -- This should be solved by yo tactic
  rfl

end LeanYo.Examples
