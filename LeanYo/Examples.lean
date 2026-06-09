import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Yoneda

open CategoryTheory Functor Opposite

namespace LeanYo.Examples

/-!
Manual Mathlib proofs for extraction targets. These do not use `yo` or `naturality!`.
Tactic-driven mirrors live in `LeanYo.Tests.*`.
-/

-- P0: functoriality and basic naturality

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

example {C D E : Type} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := by
  rfl

-- P1: vertical/horizontal composition and whiskering

example {C D E : Type} [Category C] [Category D] [Category E]
    (F G H : C ⥤ D) (η : F ⟶ G) (θ : G ⟶ H) {X Y : C} (f : X ⟶ Y) :
    (η ≫ θ).app X ≫ H.map f = F.map f ≫ (η ≫ θ).app Y := by
  simp [NatTrans.comp_app, NatTrans.naturality]

example {C D E : Type} [Category C] [Category D] [Category E]
    (F G : C ⥤ D) (H I : D ⥤ E) (η : F ⟶ G) (θ : H ⟶ I) {X Y : C} (f : X ⟶ Y) :
    (η ◫ θ).app X ≫ (G ⋙ I).map f = (F ⋙ H).map f ≫ (η ◫ θ).app Y := by
  rw [← NatTrans.naturality]

example {C D E : Type} [Category C] [Category D] [Category E]
    (F G : C ⥤ D) (H : D ⥤ E) (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    (whiskerRight η H).app X ≫ (G ⋙ H).map f = (F ⋙ H).map f ≫ (whiskerRight η H).app Y := by
  rw [← NatTrans.naturality]

example {C D E : Type} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G H : D ⥤ E) (η : G ⟶ H) {X Y : C} (f : X ⟶ Y) :
    (whiskerLeft F η).app X ≫ (F ⋙ H).map f = (F ⋙ G).map f ≫ (whiskerLeft F η).app Y := by
  rw [← NatTrans.naturality]

example {C D E : Type} [Category C] [Category D] [Category E]
    (F G : C ⥤ D ⥤ E) (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) (Z : D) :
    (η.app X).app Z ≫ (G.map f).app Z = (F.map f).app Z ≫ (η.app Y).app Z := by
  simp [NatTrans.naturality_app]

example {C D E : Type} [Category C] [Category D] [Category E]
    (F G : C ⥤ D) (H : D ⥤ E) (η : F ⟶ G) (X : C) :
    (whiskerRight η H).app X = H.map (η.app X) := by
  simp [whiskerRight_app]

example {C D E : Type} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G H : D ⥤ E) (η : G ⟶ H) (X : C) :
    (whiskerLeft F η).app X = η.app (F.obj X) := by
  simp [whiskerLeft_app]

example {C D E F : Type} [Category C] [Category D] [Category E] [Category F]
    (G : C ⥤ D) (H : D ⥤ E) (I : E ⥤ F) (η : H ⟶ H) {X Y : C} (f : X ⟶ Y) :
    (whiskerRight η I).app (G.obj X) ≫ (H ⋙ I).map (G.map f) =
      (H ⋙ I).map (G.map f) ≫ (whiskerRight η I).app (G.obj Y) := by
  rw [← NatTrans.naturality]

-- P2: Yoneda

example {C : Type} [Category C] (X : C) :
    (yoneda.obj X).map (𝟙 (op X)) = 𝟙 _ := by
  simp only [Functor.map_id]

example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
    (F ⋙ yoneda).obj X = yoneda.obj (F.obj X) := by
  rfl

end LeanYo.Examples
