# Mathlib PR draft: naturality and whiskering examples

**Proposed title:** `CategoryTheory: add naturality and whiskering examples`

**Target Mathlib revision:** `v4.31.0` (or current `master` when aligned)

**Source:** manual proofs in `lean-yo` `LeanYo/Examples.lean` (P1 queue rows 1–12). This document is repo-local planning only.

---

## Summary (for GitHub PR description)

Add short `example` blocks to Mathlib's category-theory library showing canonical proof patterns for:

- functoriality (`map_id`, `map_comp`, composition of functors);
- the naturality square (`NatTrans.naturality`);
- whiskering definitions and a whiskered naturality square;
- bifunctor `map_comp`;
- basic Yoneda functoriality and composite-with-`yoneda` goals.

No new lemmas or imports — documentation examples only.

---

## File placement map

| Queue # | Mathlib file | Section / anchor | Topic |
|--------|--------------|------------------|-------|
| 1, 2, 9 | `Mathlib/CategoryTheory/Functor/Basic.lean` | near `map_id` / `map_comp` | functoriality examples |
| 3, 4 | `Mathlib/CategoryTheory/Functor/Basic.lean` or `Functor/Category.lean` | near composed-functor lemmas | `(F ⋙ G).map` examples |
| 5, (13–14 later) | `Mathlib/CategoryTheory/NatTrans.lean` | near `NatTrans.naturality` | naturality square example |
| 6, 7, 8 | `Mathlib/CategoryTheory/Whiskering.lean` | near `whiskerLeft` / `whiskerRight` | whiskering `app` and naturality |
| 10, 11, 12 | `Mathlib/CategoryTheory/Yoneda.lean` | near `yoneda` definition / functoriality | Yoneda examples |

Row 4 fits best in `Functor/Category.lean` next to composition lemmas; rows 1–3 and 9 fit `Functor/Basic.lean`.

---

## `Mathlib/CategoryTheory/Functor/Basic.lean`

Add inside `namespace CategoryTheory` (after existing `map_comp` lemmas):

```lean
example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
    F.map (𝟙 X) = 𝟙 (F.obj X) := by
  simp

example {C D : Type} [Category C] [Category D] (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by
  simp

example {C D E : Type} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by
  simp

example {C D E : Type} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E) (X : C) :
    (F ⋙ G).map (𝟙 X) = 𝟙 ((F ⋙ G).obj X) := by
  simp only [Functor.map_id]
```

---

## `Mathlib/CategoryTheory/Functor/Category.lean`

Add near functor-composition lemmas:

```lean
example {C D E : Type} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (F ⋙ G).map f = G.map (F.map f) := by
  rfl
```

---

## `Mathlib/CategoryTheory/NatTrans.lean`

Add near `NatTrans.naturality`:

```lean
example {C D : Type} [Category C] [Category D] (F G : C ⥤ D) (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    η.app X ≫ G.map f = F.map f ≫ η.app Y := by
  rw [← NatTrans.naturality]
```

---

## `Mathlib/CategoryTheory/Whiskering.lean`

Add after `whiskerLeft` / `whiskerRight` simp lemmas:

```lean
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
```

---

## `Mathlib/CategoryTheory/Yoneda.lean`

Add in the Yoneda namespace block (imports already present in that file):

```lean
open Opposite

example {C : Type} [Category C] (X : C) :
    (yoneda.obj X).map (𝟙 (op X)) = 𝟙 _ := by
  simp only [Functor.map_id]

example {C D : Type} [Category C] [Category D] (F : C ⥤ D) (X : C) :
    (F ⋙ yoneda).obj X = yoneda.obj (F.obj X) := by
  rfl

example {C D : Type} [Category C] [Category D] (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    ((F ⋙ yoneda).map f).app (op (F.obj Y)) = (yoneda.map (F.map f)).app (op (F.obj Y)) := by
  simp
```

---

## Test plan (for GitHub PR description)

```markdown
## Test plan

- [ ] `lake build Mathlib.CategoryTheory.Functor.Basic`
- [ ] `lake build Mathlib.CategoryTheory.Functor.Category`
- [ ] `lake build Mathlib.CategoryTheory.NatTrans`
- [ ] `lake build Mathlib.CategoryTheory.Whiskering`
- [ ] `lake build Mathlib.CategoryTheory.Yoneda`
- [ ] No new `import` lines; examples use lemmas already in scope
- [ ] `lake exe lintStyle` (if run locally) on touched files
```

---

## Out of scope for this PR

- P2 reassoc lemmas (queue rows 13–18)
- P3 one-shot `@[simp]` bundles (rows 19–23)
- Row 24 whiskering/`hcomp` research (ill-typed as `(η ◫ yoneda)`; see queue)
- Any tactic or automation from external repositories

Follow-up PRs: see [MATHLIB_NATURALITY_PR_QUEUE.md](MATHLIB_NATURALITY_PR_QUEUE.md).
