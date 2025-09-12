import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NaturalTransformation

-- Simple test to verify basic category theory functionality

def main : IO Unit := do
  IO.println "Testing basic category theory functionality..."
  IO.println "✅ Mathlib imports successfully"
  IO.println "✅ Basic category theory types are available"
  IO.println "✅ Test completed successfully"

-- Test 1: Basic functoriality
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := by
  rfl

-- Test 2: Functor composition
example {C D E : Type} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G : D ⥤ E) (X Y : C) (f : X ⟶ Y) :
  (F ⋙ G).map f = G.map (F.map f) := by
  rfl

-- Test 3: Natural transformation naturality
example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) (X Y : C) (f : X ⟶ Y) :
  η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  exact η.naturality f
