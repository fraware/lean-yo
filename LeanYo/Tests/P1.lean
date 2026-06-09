import LeanYo
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Whiskering

open CategoryTheory Functor

namespace LeanYo.Tests.P1

/-! ### Manual proofs -/

section Manual

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
    (F : C ⥤ D ⥤ E) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by
  simp

example {C D E : Type} [Category C] [Category D] [Category E]
    (F G : C ⥤ D ⥤ E) (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) (Z : D) :
    (η.app X).app Z ≫ (G.map f).app Z = (F.map f).app Z ≫ (η.app Y).app Z := by
  simp [NatTrans.naturality_app]

example {C D E F : Type} [Category C] [Category D] [Category E] [Category F]
    (G : C ⥤ D) (H : D ⥤ E) (I : E ⥤ F) (η : H ⟶ H) {X Y : C} (f : X ⟶ Y) :
    (whiskerRight η I).app (G.obj X) ≫ (H ⋙ I).map (G.map f) =
      (H ⋙ I).map (G.map f) ≫ (whiskerRight η I).app (G.obj Y) := by
  rw [← NatTrans.naturality]

end Manual

/-! ### Tactic regression -/

section Tactic

example {C D E : Type} [Category C] [Category D] [Category E]
    (F G H : C ⥤ D) (η : F ⟶ G) (θ : G ⟶ H) {X Y : C} (f : X ⟶ Y) :
    (η ≫ θ).app X ≫ H.map f = F.map f ≫ (η ≫ θ).app Y := by
  naturality!

example {C D E : Type} [Category C] [Category D] [Category E]
    (F G : C ⥤ D) (H I : D ⥤ E) (η : F ⟶ G) (θ : H ⟶ I) {X Y : C} (f : X ⟶ Y) :
    (η ◫ θ).app X ≫ (G ⋙ I).map f = (F ⋙ H).map f ≫ (η ◫ θ).app Y := by
  naturality!

example {C D E : Type} [Category C] [Category D] [Category E]
    (F G : C ⥤ D) (H : D ⥤ E) (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    (whiskerRight η H).app X ≫ (G ⋙ H).map f = (F ⋙ H).map f ≫ (whiskerRight η H).app Y := by
  naturality!

example {C D E : Type} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G H : D ⥤ E) (η : G ⟶ H) {X Y : C} (f : X ⟶ Y) :
    (whiskerLeft F η).app X ≫ (F ⋙ H).map f = (F ⋙ G).map f ≫ (whiskerLeft F η).app Y := by
  naturality!

example {C D E : Type} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by
  yo

example {C D E : Type} [Category C] [Category D] [Category E]
    (F G : C ⥤ D ⥤ E) (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) (Z : D) :
    (η.app X).app Z ≫ (G.map f).app Z = (F.map f).app Z ≫ (η.app Y).app Z := by
  naturality!

example {C D E F : Type} [Category C] [Category D] [Category E] [Category F]
    (G : C ⥤ D) (H : D ⥤ E) (I : E ⥤ F) (η : H ⟶ H) {X Y : C} (f : X ⟶ Y) :
    (whiskerRight η I).app (G.obj X) ≫ (H ⋙ I).map (G.map f) =
      (H ⋙ I).map (G.map f) ≫ (whiskerRight η I).app (G.obj Y) := by
  naturality!

end Tactic

end LeanYo.Tests.P1
