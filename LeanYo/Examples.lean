import LeanYo
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.Category

-- Examples demonstrating lean-yo tactics

namespace LeanYo.Examples

-- Example 1: Basic functoriality
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := by
  yo

-- Example 2: Functor composition
example {C D E : Type} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G : D ⥤ E) (X Y : C) (f : X ⟶ Y) :
  (F ⋙ G).map f = G.map (F.map f) := by
  yo

-- Example 3: Natural transformation naturality
example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  naturality!

-- Example 4: Horizontal composition of natural transformations
example {C D E : Type} [Category C] [Category D] [Category E]
  (F G H : C ⥤ D) (η : F ⟶ G) (θ : G ⟶ H) (X Y : C) (f : X ⟶ Y) :
  (η ≫ θ).app X ≫ H.map f = F.map f ≫ (η ≫ θ).app Y := by
  naturality!

-- Example 5: Vertical composition of natural transformations
example {C D E : Type} [Category C] [Category D] [Category E]
  (F G : C ⥤ D) (H I : D ⥤ E) (η : F ⟶ G) (θ : H ⟶ I) (X Y : C) (f : X ⟶ Y) :
  (η ◫ θ).app X ≫ (I ⋙ G).map f = (H ⋙ F).map f ≫ (η ◫ θ).app Y := by
  naturality!

-- Example 6: Whiskering on the left
example {C D E : Type} [Category C] [Category D] [Category E]
  (F G : C ⥤ D) (H : D ⥤ E) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  (H ◫ η).app X ≫ (H ⋙ G).map f = (H ⋙ F).map f ≫ (H ◫ η).app Y := by
  naturality!

-- Example 7: Whiskering on the right
example {C D E : Type} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G H : D ⥤ E) (η : G ⟶ H) (X Y : C) (f : X ⟶ Y) :
  (η ◫ F).app X ≫ (H ⋙ F).map f = (G ⋙ F).map f ≫ (η ◫ F).app Y := by
  naturality!

-- Example 8: Yoneda isomorphism
example {C : Type} [Category C] (X Y : C) (f : X ⟶ Y) :
  (yoneda.obj X).map f = (coyoneda.obj X).map f := by
  yo

-- Example 9: Complex composition with multiple functors
example {C D E F : Type} [Category C] [Category D] [Category E] [Category F]
  (G : C ⥤ D) (H : D ⥤ E) (I : E ⥤ F) (X Y : C) (f : X ⟶ Y) :
  (I ⋙ H ⋙ G).map f = I.map (H.map (G.map f)) := by
  yo

-- Example 10: Bifunctor with natural transformations
example {C D E : Type} [Category C] [Category D] [Category E]
  (F G : C ⥤ D ⥤ E) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) (Z : D) :
  (η.app X).app Z ≫ (G.map f).app Z = (F.map f).app Z ≫ (η.app Y).app Z := by
  naturality!

-- Example 11: Using yo at hypothesis
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X Y : C) (f : X ⟶ Y) :
  F.map f = F.map f := by
  have h : F.map f = F.map f := by rfl
  yo at h
  exact h

-- Example 12: Using debug tactics
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := by
  yo? -- This will print the rewrites used

-- Example 13: Using naturality debug
example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  naturality? -- This will print the rewrites used

-- Example 14: Setting options
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := by
  yo.direction := covariant
  yo

-- Example 15: Complex naturality with multiple steps
example {C D E F : Type} [Category C] [Category D] [Category E] [Category F]
  (G : C ⥤ D) (H : D ⥤ E) (I : E ⥤ F) (η : H ⟶ H) (X Y : C) (f : X ⟶ Y) :
  (I ⋙ H ⋙ G).map f ≫ (I ⋙ η).app (G.obj Y) = (I ⋙ η).app (G.obj X) ≫ (I ⋙ H ⋙ G).map f := by
  naturality.maxSteps := 128
  naturality.timeout := 2000
  naturality!

end LeanYo.Examples
