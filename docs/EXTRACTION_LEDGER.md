# Extraction ledger (Lean 4.31 / Mathlib `v4.31.0-rc1`)

This ledger records Mathlib upstream candidates discovered while modernizing `lean-yo`. The first upstream outputs are **lemmas and examples**, not the `yo` / `naturality!` tactics.

Toolchain: `leanprover/lean4:v4.31.0-rc1` · Mathlib: `v4.31.0-rc1`

| Tactic | Input goal | Manual proof today | Missing lemma | Candidate theorem statement | Proposed Mathlib file | Risk | Status |
|--------|------------|-------------------|---------------|---------------------------|----------------------|------|--------|
| (manual) | `F.map (𝟙 X) = 𝟙 (F.obj X)` | `simp` | none (present) | — | `Mathlib/CategoryTheory/Functor/Basic.lean` | low | documented |
| (manual) | `F.map (f ≫ g) = F.map f ≫ F.map g` | `simp` | none (present) | — | `Mathlib/CategoryTheory/Functor/Basic.lean` | low | documented |
| `yo` | `F.map (𝟙 X) = 𝟙 (F.obj X)` | `simp` | none | `@[simp]` bundle example in docs | `Mathlib/CategoryTheory/Functor/Basic.lean` | low | tactic + manual pass |
| `yo` | `(F ⋙ G).map f = G.map (F.map f)` | `rfl` | none | — | `Mathlib/CategoryTheory/Functor/Category.lean` | low | documented |
| `naturality!` | `η.app X ≫ G.map f = F.map f ≫ η.app Y` | `rw [← NatTrans.naturality]` | reassoc-oriented `simp` lemma | `η.app X ≫ G.map f = F.map f ≫ η.app Y` (simp normal form doc) | `Mathlib/CategoryTheory/NatTrans.lean` | low | tactic + manual pass |
| `naturality!` | `(η ≫ θ).app X ≫ H.map f = F.map f ≫ (η ≫ θ).app Y` | `simp [NatTrans.comp_app, NatTrans.naturality]` | combined `simp` lemma | `@[simp]` lemma for vertical composition naturality | `Mathlib/CategoryTheory/Functor/Category.lean` | med | candidate |
| `naturality!` | whiskered square for `whiskerRight η H` | `rw [← NatTrans.naturality]` | one-shot whisker+naturality `simp` | `(whiskerRight η H).app X ≫ (G ⋙ H).map f = (F ⋙ H).map f ≫ (whiskerRight η H).app Y` | `Mathlib/CategoryTheory/Whiskering.lean` | med | tactic + manual pass |
| `naturality!` | whiskered square for `whiskerLeft F η` | `rw [← NatTrans.naturality]` | one-shot whisker+naturality `simp` | `(whiskerLeft F η).app X ≫ (F ⋙ H).map f = (F ⋙ G).map f ≫ (whiskerLeft F η).app Y` | `Mathlib/CategoryTheory/Whiskering.lean` | med | tactic + manual pass |
| `naturality!` | `(η ◫ θ).app X ≫ (G ⋙ I).map f = (F ⋙ H).map f ≫ (η ◫ θ).app Y` | `rw [← NatTrans.naturality]` | horizontal composition naturality `simp` | `@[simp]` lemma for `hcomp` naturality squares | `Mathlib/CategoryTheory/Functor/Category.lean` | med | tactic + manual pass |
| `yo` | `(yoneda.obj X).map (𝟙 (op X)) = 𝟙 _` | `simp only [Functor.map_id]` | none | — | `Mathlib/CategoryTheory/Yoneda.lean` | low | tactic + manual pass |
| `yo` | `(F ⋙ yoneda).obj X = yoneda.obj (F.obj X)` | `rfl` | none | — | `Mathlib/CategoryTheory/Yoneda.lean` | low | tactic + manual pass |
| `naturality!` | `η.app X ≫ G.map (𝟙 X) = F.map (𝟙 X) ≫ η.app Y` | `rw [← NatTrans.naturality]` | fused id lemma | `η.app X ≫ G.map (𝟙 X) = η.app X` variant for `simp` | `Mathlib/CategoryTheory/NatTrans.lean` | low | tactic + manual pass |
| `yo` | bifunctor `F.map (f ≫ g) = F.map f ≫ F.map g` for `C ⥤ D ⥤ E` | `simp` | none | — | `Mathlib/CategoryTheory/Functor/Basic.lean` | low | documented |
| `naturality!` | `(η.app X).app Z ≫ (G.map f).app Z = (F.map f).app Z ≫ (η.app Y).app Z` | `simp [NatTrans.naturality_app]` | bifunctor naturality `simp` bundle | naturality for components of bundled NTs | `Mathlib/CategoryTheory/Functor/Category.lean` | med | tactic + manual pass |
| `yo` | `(F ⋙ yoneda).map (op f) = (yoneda.map (F.map f)).app (op Y)` | type-sensitive on 4.31 | Yoneda comp map lemma | example section in Yoneda docs | `Mathlib/CategoryTheory/Yoneda.lean` | med | research |
| `naturality!` | `(η ◫ yoneda).app X = (yoneda ◫ η).app X` | unknown | interchange lemma | document whiskering vs `hcomp` with `yoneda` | `Mathlib/CategoryTheory/Yoneda.lean` | high | research |
| (infra) | attribute `@[naturality]` registry | `registerLabelAttr` | none | — | repo-local | low | ported |
| (infra) | whiskering API (`whiskerRight η H`, not `H ◫ η`) | `Whiskering.lean` | none | update downstream docs | `Mathlib/CategoryTheory/Whiskering.lean` | low | fixed in repo |
| (infra) | `Functor.whiskerRight_app` / `Functor.whiskerLeft_app` simp names | present | none | — | `Mathlib/CategoryTheory/Whiskering.lean` | low | fixed in repo |

## Build certification (2026-06-09)

| Command | Result |
|---------|--------|
| `lake update` | pass |
| `lake build LeanYo` | pass (core + `LeanYo.Examples`) |
| `lake build LeanYoTests` | pass (`P0`–`P2`, Manual + Tactic sections) |
| `lake exe leanyo-benchmarks` | pass (smoke) |
| `scripts/ci_build.sh` | not run on Windows shell; run in CI/Linux |

### Tactic implementation notes

- `LeanYo/Core/LemmaRegistry.lean` is the single source of truth for Mathlib lemma names used by tactics and the MetaM kernel.
- `yo` and `naturality!` delegate to `LeanYo/Tactics/Scripts.lean`: ordered `rfl` / `simp only` / `rw [← NatTrans.naturality]` scripts with goal-state rollback.
- `LeanYo/Core/SimpRunner.lean` runs real `Meta.simp` on expressions; `SimpSets.smartSimp` and `RewriteKernel` use it for programmatic rewrites and `@[naturality]` / `@[yo.fuse]` attributes.

## Upstream PR order (unchanged)

1. Mathlib naturality `simp` / `reassoc` lemmas (rows with whiskering and `hcomp`).
2. Mathlib whiskering simplification lemmas (`Whiskering.lean`).
3. Mathlib examples for naturality proof patterns (`LeanYo/Examples.lean` manual proofs).
4. Mathlib Yoneda usage examples (including functor–Yoneda composite map goals).
5. Tactic discussion only after ledger friction is lemma-level only.
