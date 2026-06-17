# Mathlib naturality upstream PR queue (Lean 4.31.0)

Classification of every extraction target from [`docs/EXTRACTION_LEDGER.md`](../EXTRACTION_LEDGER.md) and manual proofs in [`LeanYo/Examples.lean`](../../LeanYo/Examples.lean). First upstream PRs are **lemmas and examples only** (no `yo` / `naturality!` tactics).

**P1 draft:** [MATHLIB_PR_DRAFT_nat_examples.md](MATHLIB_PR_DRAFT_nat_examples.md) · **P2 draft:** [MATHLIB_PR_DRAFT_reassoc_lemmas.md](MATHLIB_PR_DRAFT_reassoc_lemmas.md) · **P1 status:** [MATHLIB_PR_40707_STATUS.md](MATHLIB_PR_40707_STATUS.md) · **Index:** [README.md](README.md)

Toolchain: `leanprover/lean4:v4.31.0` · Mathlib: `v4.31.0`

## Priority bands (ledger order)

| Band | Buckets | Rationale |
|------|---------|-----------|
| **P1** | `documentation-only`, `Yoneda example` | Mathlib already has core lemmas; upstream value is curated examples |
| **P2** | `reassoc lemma candidate` | Goals that close after `rw [← NatTrans.naturality]` plus `map_id` / `comp_id` |
| **P3** | `simp lemma candidate` | Missing one-shot `@[simp]` bundles for vertical / horizontal / whiskering / bifunctor goals |
| **P4** | `future tactic-only` | Repo-local tactic friction or research; not first Mathlib PR |

## Queue (24 rows)

| # | Bucket | Goal / statement (Lean-ish) | Manual proof (`LeanYo/Examples.lean`) | Mathlib path (4.31) | Suggested PR title fragment | Priority | Status |
|---|--------|----------------------------|----------------------------------------|---------------------|------------------------------|----------|--------|
| 1 | documentation-only | `F.map (𝟙 X) = 𝟙 (F.obj X)` | lines 19–21 | `Mathlib/CategoryTheory/Functor/Basic.lean` | `add Functor.map_id example` | P1 | submitted ([#40707](https://github.com/leanprover-community/mathlib4/pull/40707)) |
| 2 | documentation-only | `F.map (f ≫ g) = F.map f ≫ F.map g` | lines 23–25 | `Mathlib/CategoryTheory/Functor/Basic.lean` | `add Functor.map_comp example` | P1 | submitted ([#40707](https://github.com/leanprover-community/mathlib4/pull/40707)) |
| 3 | documentation-only | `(F ⋙ G).map (𝟙 X) = 𝟙 ((F ⋙ G).obj X)` | lines 44–46 | `Mathlib/CategoryTheory/Functor/Basic.lean` | `add composed functor map_id example` | P1 | submitted ([#40707](https://github.com/leanprover-community/mathlib4/pull/40707)) |
| 4 | documentation-only | `(F ⋙ G).map f = G.map (F.map f)` | lines 48–51 | `Mathlib/CategoryTheory/Functor/Category.lean` | `add functor composition map example` | P1 | submitted ([#40707](https://github.com/leanprover-community/mathlib4/pull/40707)) |
| 5 | documentation-only | `η.app X ≫ G.map f = F.map f ≫ η.app Y` | lines 27–29 | `Mathlib/CategoryTheory/NatTrans.lean` | `add NatTrans.naturality example` | P1 | submitted ([#40707](https://github.com/leanprover-community/mathlib4/pull/40707)) |
| 6 | documentation-only | `(whiskerRight η H).app X = H.map (η.app X)` | lines 80–83 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskerRight_app example` | P1 | submitted ([#40707](https://github.com/leanprover-community/mathlib4/pull/40707)) |
| 7 | documentation-only | `(whiskerLeft F η).app X = η.app (F.obj X)` | lines 85–88 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskerLeft_app example` | P1 | submitted ([#40707](https://github.com/leanprover-community/mathlib4/pull/40707)) |
| 8 | documentation-only | `(whiskerRight η I).app (G.obj X) ≫ (H ⋙ I).map (G.map f) = (H ⋙ I).map (G.map f) ≫ (whiskerRight η I).app (G.obj Y)` | lines 90–94 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskered naturality example` | P1 | submitted ([#40707](https://github.com/leanprover-community/mathlib4/pull/40707)) |
| 9 | documentation-only | `F.map (f ≫ g) = F.map f ≫ F.map g` for `F : C ⥤ D ⥤ E` | lines 31–34 | `Mathlib/CategoryTheory/Functor/Basic.lean` | `add bifunctor map_comp example` | P1 | submitted ([#40707](https://github.com/leanprover-community/mathlib4/pull/40707)) |
| 10 | Yoneda example | `(yoneda.obj X).map (𝟙 (op X)) = 𝟙 _` | lines 98–100 | `Mathlib/CategoryTheory/Yoneda.lean` | `add Yoneda map_id example` | P1 | submitted ([#40707](https://github.com/leanprover-community/mathlib4/pull/40707)) |
| 11 | Yoneda example | `(F ⋙ yoneda).obj X = yoneda.obj (F.obj X)` | lines 102–104 | `Mathlib/CategoryTheory/Yoneda.lean` | `add Yoneda composite object example` | P1 | submitted ([#40707](https://github.com/leanprover-community/mathlib4/pull/40707)) |
| 12 | Yoneda example | `((F ⋙ yoneda).map f).app (op (F.obj Y)) = (yoneda.map (F.map f)).app (op (F.obj Y))` | lines 106–108 | `Mathlib/CategoryTheory/Yoneda.lean` | `add Yoneda composite map example` | P1 | submitted ([#40707](https://github.com/leanprover-community/mathlib4/pull/40707)) |
| 13 | reassoc lemma candidate | `η.app X ≫ G.map (𝟙 X) = F.map (𝟙 X) ≫ η.app X` | lines 40–42 | `Mathlib/CategoryTheory/NatTrans.lean` | `add naturality reassoc with identity morphism` | P2 | draft ready |
| 14 | reassoc lemma candidate | `η.app X ≫ G.map (𝟙 X) = η.app X` | lines 36–38 | `Mathlib/CategoryTheory/NatTrans.lean` | `add naturality identity reassoc simp lemma` | P2 | draft ready |
| 15 | reassoc lemma candidate | `(η ≫ θ).app X ≫ H.map f = F.map f ≫ (η ≫ θ).app Y` via `comp_app` + `map_id`/`comp_id` after `naturality` | lines 55–58 (today: one-shot `simp`) | `Mathlib/CategoryTheory/Functor/Category.lean` | `add vertical composition naturality reassoc lemma` | P2 | draft ready |
| 16 | reassoc lemma candidate | `(η ◫ θ).app X ≫ (G ⋙ I).map f = (F ⋙ H).map f ≫ (η ◫ θ).app Y` after whisker reassociation | lines 60–63 | `Mathlib/CategoryTheory/Functor/Category.lean` | `add horizontal composition naturality reassoc lemma` | P2 | draft ready |
| 17 | reassoc lemma candidate | `(whiskerRight η H).app X ≫ (G ⋙ H).map f = (F ⋙ H).map f ≫ (whiskerRight η H).app Y` after `whiskerRight_app` | lines 65–68 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskerRight naturality reassoc lemma` | P2 | draft ready |
| 18 | reassoc lemma candidate | `(whiskerLeft F η).app X ≫ (F ⋙ H).map f = (F ⋙ G).map f ≫ (whiskerLeft F η).app Y` after `whiskerLeft_app` | lines 70–73 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskerLeft naturality reassoc lemma` | P2 | draft ready |
| 19 | simp lemma candidate | `(η ≫ θ).app X ≫ H.map f = F.map f ≫ (η ≫ θ).app Y` as one-shot `@[simp]` | lines 55–58 | `Mathlib/CategoryTheory/Functor/Category.lean` | `add vertical composition naturality simp lemma` | P3 | planned |
| 20 | simp lemma candidate | `(η ◫ θ).app X ≫ (G ⋙ I).map f = (F ⋙ H).map f ≫ (η ◫ θ).app Y` as one-shot `@[simp]` | lines 60–63 | `Mathlib/CategoryTheory/Functor/Category.lean` | `add horizontal composition naturality simp lemma` | P3 | planned |
| 21 | simp lemma candidate | `(whiskerRight η H).app X ≫ (G ⋙ H).map f = (F ⋙ H).map f ≫ (whiskerRight η H).app Y` as one-shot `@[simp]` | lines 65–68 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskerRight naturality simp lemma` | P3 | planned |
| 22 | simp lemma candidate | `(whiskerLeft F η).app X ≫ (F ⋙ H).map f = (F ⋙ G).map f ≫ (whiskerLeft F η).app Y` as one-shot `@[simp]` | lines 70–73 | `Mathlib/CategoryTheory/Whiskering.lean` | `add whiskerLeft naturality simp lemma` | P3 | planned |
| 23 | simp lemma candidate | `(η.app X).app Z ≫ (G.map f).app Z = (F.map f).app Z ≫ (η.app Y).app Z` for `F : C ⥤ D ⥤ E` | lines 75–78 | `Mathlib/CategoryTheory/Functor/Category.lean` | `add bifunctor naturality_app simp lemma` | P3 | planned |
| 24 | future tactic-only | `(η ◫ yoneda).app X = (yoneda ◫ η).app X` — **blocked (ill-typed)**; refined: `(η ◫ 𝟙 yoneda).app X = (whiskerRight η yoneda).app X` and `(𝟙 yoneda ◫ η).app X = (whiskerLeft yoneda η).app X` (η between functors `(Cᵒᵖ ⥤ Type) ⥤ E`) via `hcomp_id` / `id_hcomp` | lines 114–122 (refined); original goal does not typecheck | `Mathlib/CategoryTheory/Yoneda.lean` | — (blocked) | P4 | blocked |

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

1. **P1 batch** — rows 1–12: **submitted** as [mathlib4#40707](https://github.com/leanprover-community/mathlib4/pull/40707) (status: [MATHLIB_PR_40707_STATUS.md](MATHLIB_PR_40707_STATUS.md)).
2. **P2 batch** — rows 13–18: draft at [MATHLIB_PR_DRAFT_reassoc_lemmas.md](MATHLIB_PR_DRAFT_reassoc_lemmas.md); open after P1 merges.
3. **P3 batch** — rows 19–23: one-shot `@[simp]` bundles where manual proofs still need multi-lemma `simp` lists.
4. **P4** — row 24 (blocked as stated; refined whiskering examples in `Examples.lean`) and infra: stay repo-local.

### Row 24 typecheck note

Lean 4.31 rejects `(η ◫ yoneda)` because `yoneda : C ⥤ Cᵒᵖ ⥤ Type _` is a **functor**, while `◫` (`NatTrans.hcomp`) expects natural transformations. Mathlib already identifies whiskering with horizontal composition against identity natural transformations (`Functor.hcomp_id`, `Functor.id_hcomp`). The refined examples in `LeanYo/Examples.lean` (lines 114–122) use `𝟙 yoneda` on the correct side; the two refined goals are **not** comparable (different functor categories). There is no true symmetric lemma between the ill-typed sides of the original goal.
