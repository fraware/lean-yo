# Mathlib PR draft: reassociated naturality lemmas

**Proposed title:** `feat(CategoryTheory): add reassociated naturality lemmas`

**Target Mathlib revision:** `v4.31.0` (or current `master` when aligned; **open only after P1 merges**)

**Prerequisite:** [mathlib4#40707](https://github.com/leanprover-community/mathlib4/pull/40707) (P1 examples, queue rows 1–12)

**Queue rows:** 13–18 only (P2 band). P3 `@[simp]` bundles (rows 19–23) are a separate follow-up.

---

## Summary (for GitHub PR description)

Add named lemmas for naturality goals that today require `rw [← NatTrans.naturality]` followed by `Functor.map_id`, `Category.id_comp`, `comp_app`, or whiskering `app` lemmas. These are reassociation normal forms — not new mathematical content beyond existing `NatTrans.naturality`.

No new imports beyond what each file already uses.

---

## File placement map

| Queue # | Mathlib file | Topic |
|--------|--------------|-------|
| 13, 14 | `Mathlib/CategoryTheory/NatTrans.lean` | naturality with identity morphism on the right |
| 15, 16 | `Mathlib/CategoryTheory/Functor/Category.lean` | vertical and horizontal composition naturality |
| 17, 18 | `Mathlib/CategoryTheory/Whiskering.lean` | whiskerLeft / whiskerRight naturality squares |

---

## `Mathlib/CategoryTheory/NatTrans.lean`

Add near `NatTrans.naturality` (after P1 example from #40707):

```lean
/-- Naturality at an identity morphism, right-hand side reassociated. -/
theorem NatTrans.naturality_app_id (F G : C ⥤ D) (η : F ⟶ G) (X : C) :
    η.app X ≫ G.map (𝟙 X) = F.map (𝟙 X) ≫ η.app X := by
  rw [← NatTrans.naturality]

/-- Naturality at an identity morphism, simplified right-hand side. -/
@[simp]
theorem NatTrans.naturality_app_comp_id (F G : C ⥤ D) (η : F ⟶ G) (X : C) :
    η.app X ≫ G.map (𝟙 X) = η.app X := by
  rw [← NatTrans.naturality, Functor.map_id, Category.id_comp]
```

**Risk:** low — direct consequences of `NatTrans.naturality` and functoriality. Row 14 is a good `@[simp]` candidate; confirm with Mathlib reviewers whether both rows 13 and 14 are wanted or only the simp normal form.

---

## `Mathlib/CategoryTheory/Functor/Category.lean`

Add near vertical / horizontal composition lemmas:

```lean
/-- Naturality for vertically composed natural transformations. -/
theorem NatTrans.naturality_comp {C D E : Type} [Category C] [Category D] [Category E]
    (F G H : C ⥤ D) (η : F ⟶ G) (θ : G ⟶ H) {X Y : C} (f : X ⟶ Y) :
    (η ≫ θ).app X ≫ H.map f = F.map f ≫ (η ≫ θ).app Y := by
  rw [← NatTrans.naturality]
  simp only [NatTrans.comp_app, NatTrans.naturality]

/-- Naturality for horizontally composed natural transformations (`hcomp`). -/
theorem NatTrans.naturality_hcomp {C D E : Type} [Category C] [Category D] [Category E]
    (F G : C ⥤ D) (H I : D ⥤ E) (η : F ⟶ G) (θ : H ⟶ I) {X Y : C} (f : X ⟶ Y) :
    (η ◫ θ).app X ≫ (G ⋙ I).map f = (F ⋙ H).map f ≫ (η ◫ θ).app Y := by
  rw [← NatTrans.naturality]
```

**Risk:** medium — row 15 proof uses `simp only [NatTrans.comp_app, NatTrans.naturality]` (one-shot today). The P2 lemma packages that script; P3 may add `@[simp]` on the same statement (row 19). Coordinate naming with reviewers to avoid duplicate attributes.

---

## `Mathlib/CategoryTheory/Whiskering.lean`

Add after `whiskerLeft` / `whiskerRight` `app` lemmas:

```lean
/-- Naturality square for right whiskering. -/
theorem whiskerRight_naturality {C D E : Type} [Category C] [Category D] [Category E]
    (F G : C ⥤ D) (H : D ⥤ E) (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    (whiskerRight η H).app X ≫ (G ⋙ H).map f = (F ⋙ H).map f ≫ (whiskerRight η H).app Y := by
  rw [← NatTrans.naturality]

/-- Naturality square for left whiskering. -/
theorem whiskerLeft_naturality {C D E : Type} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G H : D ⥤ E) (η : G ⟶ H) {X Y : C} (f : X ⟶ Y) :
    (whiskerLeft F η).app X ≫ (F ⋙ H).map f = (F ⋙ G).map f ≫ (whiskerLeft F η).app Y := by
  rw [← NatTrans.naturality]
```

**Risk:** medium — same goals as P3 rows 21–22; P2 ships named theorems without `@[simp]` first.

---

## Test plan (for GitHub PR description)

```markdown
## Test plan

- [ ] `lake build Mathlib.CategoryTheory.NatTrans`
- [ ] `lake build Mathlib.CategoryTheory.Functor.Category`
- [ ] `lake build Mathlib.CategoryTheory.Whiskering`
- [ ] No new `import` lines
- [ ] `lake exe lintStyle` on touched files (if run locally)
- [ ] Confirm lemma names do not clash with existing `simp` lemmas in 4.31
```

---

## Out of scope for this PR

- P1 documentation examples (submitted as #40707)
- P3 one-shot `@[simp]` bundles (queue rows 19–23)
- Row 24 whiskering / `yoneda` research (blocked)
- Bifunctor `naturality_app` simp bundle (row 23; separate P3 PR)

Follow-up: [MATHLIB_NATURALITY_PR_QUEUE.md](MATHLIB_NATURALITY_PR_QUEUE.md) rows 19–23.
