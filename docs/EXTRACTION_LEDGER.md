# Extraction ledger (Lean 4.31 / Mathlib `v4.31.0-rc1`)

This ledger records Mathlib upstream candidates discovered while modernizing `lean-yo`. The first upstream outputs are **lemmas and examples**, not the `yo` / `naturality!` tactics.

Toolchain: `leanprover/lean4:v4.31.0-rc1` · Mathlib: `v4.31.0-rc1`

## Coverage index (required extraction categories)

| Category | Ledger row(s) | Manual example | Mathlib path (4.31) |
|----------|---------------|----------------|---------------------|
| Naturality square | naturality square | `LeanYo/Examples.lean` (P0) | `Mathlib/CategoryTheory/NatTrans.lean` |
| Reassociated naturality square | reassociated naturality square | `LeanYo/Examples.lean` (P0, id on morphism) | `Mathlib/CategoryTheory/NatTrans.lean` |
| Left whiskering naturality | left whiskering naturality | `LeanYo/Examples.lean` (P1) | `Mathlib/CategoryTheory/Whiskering.lean` |
| Right whiskering naturality | right whiskering naturality | `LeanYo/Examples.lean` (P1) | `Mathlib/CategoryTheory/Whiskering.lean` |
| Functor map over identity | functor map over identity | `LeanYo/Examples.lean` (P0) | `Mathlib/CategoryTheory/Functor/Basic.lean` |
| Functor map over composition | functor map over composition | `LeanYo/Examples.lean` (P0) | `Mathlib/CategoryTheory/Functor/Basic.lean` |
| Yoneda usage example | Yoneda usage | `LeanYo/Examples.lean` (P2) | `Mathlib/CategoryTheory/Yoneda.lean` |
| Mathlib paths after modernization | all rows below | — | see **Mathlib 4.31 module map** |

### Mathlib 4.31 module map (post-modernization)

| Area | Primary import / file |
|------|------------------------|
| Categories, morphisms, `comp_id` / `id_comp` | `Mathlib.CategoryTheory.Category.Basic` → `Mathlib/CategoryTheory/Category/Basic.lean` |
| Functors, `map_id`, `map_comp` | `Mathlib.CategoryTheory.Functor.Basic` → `Mathlib/CategoryTheory/Functor/Basic.lean` |
| Functor category, `hcomp`, vertical `≫` | `Mathlib.CategoryTheory.Functor.Category` → `Mathlib/CategoryTheory/Functor/Category.lean` |
| Natural transformations, `NatTrans.naturality` | `Mathlib.CategoryTheory.NatTrans` → `Mathlib/CategoryTheory/NatTrans.lean` |
| Whiskering (`whiskerLeft`, `whiskerRight`) | `Mathlib.CategoryTheory.Whiskering` → `Mathlib/CategoryTheory/Whiskering.lean` |
| Yoneda embedding | `Mathlib.CategoryTheory.Yoneda` → `Mathlib/CategoryTheory/Yoneda.lean` |

| Tactic | Input goal | Manual proof today | Missing lemma | Candidate theorem statement | Proposed Mathlib file | Risk | Status |
|--------|------------|-------------------|---------------|---------------------------|----------------------|------|--------|
| functor map over identity | `F.map (𝟙 X) = 𝟙 (F.obj X)` | `simp` | none (present) | `Functor.map_id` | `Mathlib/CategoryTheory/Functor/Basic.lean` | low | documented |
| functor map over composition | `F.map (f ≫ g) = F.map f ≫ F.map g` | `simp` | none (present) | `Functor.map_comp` | `Mathlib/CategoryTheory/Functor/Basic.lean` | low | documented |
| `yo` | `F.map (𝟙 X) = 𝟙 (F.obj X)` | `simp` | none | `@[simp]` bundle example in docs | `Mathlib/CategoryTheory/Functor/Basic.lean` | low | tactic + manual pass |
| `yo` | `(F ⋙ G).map f = G.map (F.map f)` | `rfl` | none | — | `Mathlib/CategoryTheory/Functor/Category.lean` | low | documented |
| naturality square | `η.app X ≫ G.map f = F.map f ≫ η.app Y` | `rw [← NatTrans.naturality]` | none (core lemma present) | `NatTrans.naturality` | `Mathlib/CategoryTheory/NatTrans.lean` | low | documented |
| reassociated naturality square | `η.app X ≫ G.map (𝟙 X) = F.map (𝟙 X) ≫ η.app X` | `rw [← NatTrans.naturality]` then `simp` | reassoc-oriented `simp` lemma | `η.app X ≫ G.map (𝟙 X) = η.app X` (simp normal form) | `Mathlib/CategoryTheory/NatTrans.lean` | low | tactic + manual pass |
| `naturality!` | `η.app X ≫ G.map f = F.map f ≫ η.app Y` | `rw [← NatTrans.naturality]` | reassoc-oriented `simp` lemma | `η.app X ≫ G.map f = F.map f ≫ η.app Y` (simp normal form doc) | `Mathlib/CategoryTheory/NatTrans.lean` | low | tactic + manual pass |
| `naturality!` | `(η ≫ θ).app X ≫ H.map f = F.map f ≫ (η ≫ θ).app Y` | `simp [NatTrans.comp_app, NatTrans.naturality]` | combined `simp` lemma | `@[simp]` lemma for vertical composition naturality | `Mathlib/CategoryTheory/Functor/Category.lean` | med | candidate |
| right whiskering naturality | `(whiskerRight η H).app X ≫ (G ⋙ H).map f = (F ⋙ H).map f ≫ (whiskerRight η H).app Y` | `rw [← NatTrans.naturality]` | one-shot whisker+naturality `simp` | whiskerRight naturality square | `Mathlib/CategoryTheory/Whiskering.lean` | med | tactic + manual pass |
| left whiskering naturality | `(whiskerLeft F η).app X ≫ (F ⋙ H).map f = (F ⋙ G).map f ≫ (whiskerLeft F η).app Y` | `rw [← NatTrans.naturality]` | one-shot whisker+naturality `simp` | whiskerLeft naturality square | `Mathlib/CategoryTheory/Whiskering.lean` | med | tactic + manual pass |
| `naturality!` | `(η ◫ θ).app X ≫ (G ⋙ I).map f = (F ⋙ H).map f ≫ (η ◫ θ).app Y` | `rw [← NatTrans.naturality]` | horizontal composition naturality `simp` | `@[simp]` lemma for `hcomp` naturality squares | `Mathlib/CategoryTheory/Functor/Category.lean` | med | tactic + manual pass |
| Yoneda usage | `(yoneda.obj X).map (𝟙 (op X)) = 𝟙 _` | `simp only [Functor.map_id]` | none | Yoneda functoriality on identity | `Mathlib/CategoryTheory/Yoneda.lean` | low | tactic + manual pass |
| Yoneda usage | `(F ⋙ yoneda).obj X = yoneda.obj (F.obj X)` | `rfl` | none | Yoneda composite object lemma | `Mathlib/CategoryTheory/Yoneda.lean` | low | tactic + manual pass |
| `naturality!` | `η.app X ≫ G.map (𝟙 X) = F.map (𝟙 X) ≫ η.app Y` | `rw [← NatTrans.naturality]` | fused id lemma | `η.app X ≫ G.map (𝟙 X) = η.app X` variant for `simp` | `Mathlib/CategoryTheory/NatTrans.lean` | low | tactic + manual pass |
| `yo` | bifunctor `F.map (f ≫ g) = F.map f ≫ F.map g` for `C ⥤ D ⥤ E` | `simp` | none | — | `Mathlib/CategoryTheory/Functor/Basic.lean` | low | documented |
| `naturality!` | `(η.app X).app Z ≫ (G.map f).app Z = (F.map f).app Z ≫ (η.app Y).app Z` | `simp [NatTrans.naturality_app]` | bifunctor naturality `simp` bundle | naturality for components of bundled NTs | `Mathlib/CategoryTheory/Functor/Category.lean` | med | tactic + manual pass |
| `yo` | `(F ⋙ yoneda).map (op f) = (yoneda.map (F.map f)).app (op Y)` | type-sensitive on 4.31 | Yoneda comp map lemma | example section in Yoneda docs | `Mathlib/CategoryTheory/Yoneda.lean` | med | research |
| `naturality!` | `(η ◫ yoneda).app X = (yoneda ◫ η).app X` | unknown | interchange lemma | document whiskering vs `hcomp` with `yoneda` | `Mathlib/CategoryTheory/Yoneda.lean` | high | research |
| (infra) | attribute `@[naturality]` registry | `registerLabelAttr` | none | — | repo-local | low | ported |
| (infra) | whiskering API (`whiskerRight η H`, not `H ◫ η`) | `Whiskering.lean` | none | update downstream docs | `Mathlib/CategoryTheory/Whiskering.lean` | low | fixed in repo |
| (infra) | `Functor.whiskerRight_app` / `Functor.whiskerLeft_app` simp names | present | none | — | `Mathlib/CategoryTheory/Whiskering.lean` | low | fixed in repo |

## Build certification (2026-06-16)

| Command | Result |
|---------|--------|
| `lake update` | pass |
| `lake build LeanYo` | pass (625 jobs) |
| `lake build LeanYo.Examples` | pass |
| `lake build LeanYoTests` | pass (`P0`–`P2`, Manual + Tactic sections) |
| `lake exe leanyo-benchmarks` | pass (smoke) |
| `scripts/production_test.py` | pass |
| `scripts/validate_lemmas.py` | pass |
| `scripts/ci_build.sh` / `make test` | equivalent steps run on Windows (bash not required) |

### Tactic implementation notes

- `LeanYo/Core/LemmaRegistry.lean` is the single source of truth for Mathlib lemma names used by tactics and the MetaM kernel.
- `yo` and `naturality!` delegate to `LeanYo/Tactics/Scripts.lean`: ordered `rfl` / `simp only` / `rw [← NatTrans.naturality]` scripts with goal-state rollback.
- `LeanYo/Core/SimpRunner.lean` runs real `Meta.simp` on expressions; `SimpSets.smartSimp` and `RewriteKernel` use it for programmatic rewrites and `@[naturality]` / `@[yo.fuse]` attributes.

## Upstream PR order (lemma-first; no tactics)

1. **`CategoryTheory: add naturality and whiskering examples`** — manual proofs from `LeanYo/Examples.lean` (naturality square, left/right whiskering naturality, functor map over identity/composition, Yoneda usage).
2. **`CategoryTheory: add reassociated naturality lemmas`** (if friction remains) — rows labeled *reassociated naturality square*, vertical/`hcomp` combined `simp` lemmas, and whiskering one-shot `simp` bundles.
3. Yoneda composite-map examples and research rows (`F ⋙ yoneda` map goals).
4. Tactic discussion only after ledger friction is lemma-level only.
