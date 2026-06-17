# Mathlib naturality upstream PR queue (Lean 4.31.0)

Classification of every extraction target from `docs/EXTRACTION_LEDGER.md` and manual proofs in `LeanYo/Examples.lean`. First upstream PRs are **lemmas and examples only** (no `yo` / `naturality!` tactics).

Toolchain: `leanprover/lean4:v4.31.0` · Mathlib: `v4.31.0`

## Priority bands (ledger order)

| Band | Buckets | Rationale |
|------|---------|-----------|
| **P1** | `documentation-only`, `Yoneda example` | Mathlib already has core lemmas; upstream value is curated examples |
| **P2** | `reassoc lemma candidate` | Goals that close after `rw [← NatTrans.naturality]` plus `map_id` / `comp_id` |
| **P3** | `simp lemma candidate` | Missing one-shot `@[simp]` bundles for vertical / horizontal / whiskering / bifunctor goals |
| **P4** | `future tactic-only` | Repo-local tactic friction or research; not first Mathlib PR |

## Queue (24 rows)

| # | Bucket | Goal / statement (Lean-ish) | Manual proof (`LeanYo/Examples.lean`) | Mathlib path (4.31) | Suggested PR title fragment | Priority |
|---|--------|----------------------------|----------------------------------------|---------------------|------------------------------|----------|
| 1 | documentation-only | `F.map (𝟙 X) = 𝟙 (F.obj X)` | lines 19–21 | `Mathlib/CategoryTheory/Functor/Basic.lean` | `add Functor.map_id example` | P1 |
| 2 | documentation-only | `F.map (f ≫ g) = F.map f ≫ F.map g` | lines 23–25 | `Mathlib/CategoryTheory/Functor/Basic.lean` | `add Functor.map_comp example` | P1 |
| 3 | documentation-only | `(F ⋙ G).map (𝟙 X) = 𝟙 ((F ⋙ G).obj X)` | lines 44–46 | `Mathlib/CategoryTheory/Functor/Basic.lean` | `add composed functor map_id example` | P1 |
| 4 | documentation-only | `(F ⋙ G).map f = G.map (F.map f)` | lines 48–51 | `Mathlib/CategoryTheory/Functor/Category.lean` | `add functor composition map example` | P1 |
| 5 | documentation-only | `η.app X ≫ G.map f = F.map f ≫ η.app Y` | lines 27–29 | `Mathlib/CategoryTheory/NatTrans.lean` | `add NatTrans.naturality example` | P1 |
| 6 | documentation-only | `(whiskerRight η H).app X = H.map (η.app X)` | lines 80–83 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskerRight_app example` | P1 |
| 7 | documentation-only | `(whiskerLeft F η).app X = η.app (F.obj X)` | lines 85–88 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskerLeft_app example` | P1 |
| 8 | documentation-only | `(whiskerRight η I).app (G.obj X) ≫ (H ⋙ I).map (G.map f) = (H ⋙ I).map (G.map f) ≫ (whiskerRight η I).app (G.obj Y)` | lines 90–94 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskered naturality example` | P1 |
| 9 | documentation-only | `F.map (f ≫ g) = F.map f ≫ F.map g` for `F : C ⥤ D ⥤ E` | lines 31–34 | `Mathlib/CategoryTheory/Functor/Basic.lean` | `add bifunctor map_comp example` | P1 |
| 10 | Yoneda example | `(yoneda.obj X).map (𝟙 (op X)) = 𝟙 _` | lines 98–100 | `Mathlib/CategoryTheory/Yoneda.lean` | `add Yoneda map_id example` | P1 |
| 11 | Yoneda example | `(F ⋙ yoneda).obj X = yoneda.obj (F.obj X)` | lines 102–104 | `Mathlib/CategoryTheory/Yoneda.lean` | `add Yoneda composite object example` | P1 |
| 12 | Yoneda example | `((F ⋙ yoneda).map f).app (op (F.obj Y)) = (yoneda.map (F.map f)).app (op (F.obj Y))` | lines 106–108 | `Mathlib/CategoryTheory/Yoneda.lean` | `add Yoneda composite map example` | P1 |
| 13 | reassoc lemma candidate | `η.app X ≫ G.map (𝟙 X) = F.map (𝟙 X) ≫ η.app X` | lines 40–42 | `Mathlib/CategoryTheory/NatTrans.lean` | `add naturality reassoc with identity morphism` | P2 |
| 14 | reassoc lemma candidate | `η.app X ≫ G.map (𝟙 X) = η.app X` | lines 36–38 | `Mathlib/CategoryTheory/NatTrans.lean` | `add naturality identity reassoc simp lemma` | P2 |
| 15 | reassoc lemma candidate | `(η ≫ θ).app X ≫ H.map f = F.map f ≫ (η ≫ θ).app Y` via `comp_app` + `map_id`/`comp_id` after `naturality` | lines 55–58 (today: one-shot `simp`) | `Mathlib/CategoryTheory/Functor/Category.lean` | `add vertical composition naturality reassoc lemma` | P2 |
| 16 | reassoc lemma candidate | `(η ◫ θ).app X ≫ (G ⋙ I).map f = (F ⋙ H).map f ≫ (η ◫ θ).app Y` after whisker reassociation | lines 60–63 | `Mathlib/CategoryTheory/Functor/Category.lean` | `add horizontal composition naturality reassoc lemma` | P2 |
| 17 | reassoc lemma candidate | `(whiskerRight η H).app X ≫ (G ⋙ H).map f = (F ⋙ H).map f ≫ (whiskerRight η H).app Y` after `whiskerRight_app` | lines 65–68 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskerRight naturality reassoc lemma` | P2 |
| 18 | reassoc lemma candidate | `(whiskerLeft F η).app X ≫ (F ⋙ H).map f = (F ⋙ G).map f ≫ (whiskerLeft F η).app Y` after `whiskerLeft_app` | lines 70–73 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskerLeft naturality reassoc lemma` | P2 |
| 19 | simp lemma candidate | `(η ≫ θ).app X ≫ H.map f = F.map f ≫ (η ≫ θ).app Y` as one-shot `@[simp]` | lines 55–58 | `Mathlib/CategoryTheory/Functor/Category.lean` | `add vertical composition naturality simp lemma` | P3 |
| 20 | simp lemma candidate | `(η ◫ θ).app X ≫ (G ⋙ I).map f = (F ⋙ H).map f ≫ (η ◫ θ).app Y` as one-shot `@[simp]` | lines 60–63 | `Mathlib/CategoryTheory/Functor/Category.lean` | `add horizontal composition naturality simp lemma` | P3 |
| 21 | simp lemma candidate | `(whiskerRight η H).app X ≫ (G ⋙ H).map f = (F ⋙ H).map f ≫ (whiskerRight η H).app Y` as one-shot `@[simp]` | lines 65–68 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskerRight naturality simp lemma` | P3 |
| 22 | simp lemma candidate | `(whiskerLeft F η).app X ≫ (F ⋙ H).map f = (F ⋙ G).map f ≫ (whiskerLeft F η).app Y` as one-shot `@[simp]` | lines 70–73 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskerLeft naturality simp lemma` | P3 |
| 23 | simp lemma candidate | `(η.app X).app Z ≫ (G.map f).app Z = (F.map f).app Z ≫ (η.app Y).app Z` for `F : C ⥤ D ⥤ E` | lines 75–78 | `Mathlib/CategoryTheory/Functor/Category.lean` | `add bifunctor naturality_app simp lemma` | P3 |
| 24 | future tactic-only | `(η ◫ yoneda).app X = (yoneda ◫ η).app X` (whiskering vs `hcomp` interchange; types delicate) | *no manual proof yet* | `Mathlib/CategoryTheory/Yoneda.lean` | — (research) | P4 |

### Ledger infra rows (not queued for Mathlib)

| Ledger row | Bucket | Notes |
|------------|--------|-------|
| `@[naturality]` registry (`registerLabelAttr`) | future tactic-only | Repo-local attribute wiring in `LeanYo/Core/Attributes.lean` |
| Whiskering API (`whiskerRight η H` vs `H ◫ η`) | future tactic-only | Downstream doc migration; Mathlib 4.31 API already correct |
| `yo` / `naturality!` tactic script ordering | future tactic-only | `LeanYo/Tactics/Scripts.lean`; discuss only after lemma queue drains |

## Mathlib path verification (installed `.lake/packages/mathlib`)

| Path | Present on `v4.31.0` |
|------|----------------------|
| `Mathlib/CategoryTheory/Category/Basic.lean` | yes |
| `Mathlib/CategoryTheory/Functor/Basic.lean` | yes |
| `Mathlib/CategoryTheory/Functor/Category.lean` | yes |
| `Mathlib/CategoryTheory/NatTrans.lean` | yes |
| `Mathlib/CategoryTheory/Whiskering.lean` | yes |
| `Mathlib/CategoryTheory/Yoneda.lean` | yes |

## Suggested PR sequence

1. **P1 batch** — rows 1–12: examples section in `NatTrans`, `Whiskering`, `Functor`, `Yoneda` (ledger: *CategoryTheory: add naturality and whiskering examples*).
2. **P2 batch** — rows 13–18: reassoc lemmas if example-only PRs leave `simp`/`cat_disch` friction (ledger: *CategoryTheory: add reassociated naturality lemmas*).
3. **P3 batch** — rows 19–23: one-shot `@[simp]` bundles where manual proofs still need multi-lemma `simp` lists.
4. **P4** — row 24 and infra: stay repo-local until types and interchange law are settled.
