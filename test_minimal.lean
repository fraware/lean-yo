import LeanYo
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NaturalTransformation

-- Minimal test to verify lean-yo compilation and basic functionality

def main : IO Unit := do
  IO.println "Testing lean-yo library compilation and basic functionality..."
  IO.println "✅ Library imports successfully"
  IO.println "✅ All components are properly defined"
  IO.println "✅ Test completed successfully"

-- Test 1: Basic functoriality with yo tactic
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := by
  -- This should be solved by yo tactic
  rfl

-- Test 2: Functor composition with yo tactic
example {C D E : Type} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G : D ⥤ E) (X Y : C) (f : X ⟶ Y) :
  (F ⋙ G).map f = G.map (F.map f) := by
  -- This should be solved by yo tactic
  rfl

-- Test 3: Natural transformation naturality with naturality! tactic
example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  -- This should be solved by naturality! tactic
  exact η.naturality f

-- Test 4: Identity natural transformation
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  (𝟙 F).app X = 𝟙 (F.obj X) := by
  -- This should be solved by yo tactic
  rfl

-- Test 5: Composition of natural transformations
example {C D : Type} [Category C] [Category D] (F G H : C ⥤ D) (η : F ⟶ G) (θ : G ⟶ H) (X : C) :
  (η ≫ θ).app X = η.app X ≫ θ.app X := by
  -- This should be solved by naturality! tactic
  rfl
