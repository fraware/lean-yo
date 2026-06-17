# Mathlib upstream index

Repo-local planning for the first [Mathlib4](https://github.com/leanprover-community/mathlib4) contributions from `lean-yo`. Nothing here opens a PR by itself — use these files to prepare copy-paste-ready Mathlib changes.

**Toolchain:** `leanprover/lean4:v4.31.0` · **Mathlib:** `v4.31.0`

## Files

| Document | Purpose |
|----------|---------|
| [MATHLIB_NATURALITY_PR_QUEUE.md](MATHLIB_NATURALITY_PR_QUEUE.md) | 24-row priority queue (P1–P4) with Mathlib paths, manual proof line refs, and suggested PR titles |
| [MATHLIB_PR_DRAFT_nat_examples.md](MATHLIB_PR_DRAFT_nat_examples.md) | Copy-paste draft for P1 examples (rows 1–12) |
| [MATHLIB_PR_DRAFT_reassoc_lemmas.md](MATHLIB_PR_DRAFT_reassoc_lemmas.md) | Copy-paste draft for **P2** reassoc lemmas (rows 13–18; open after P1 merges) |
| [MATHLIB_PR_40707_STATUS.md](MATHLIB_PR_40707_STATUS.md) | Live CI and review status for submitted P1 PR |
| [../EXTRACTION_LEDGER.md](../EXTRACTION_LEDGER.md) | Full friction ledger (tactic goals, risk, status) — source of queue rows |
| [../MODERNIZATION_EXTRACTION_SPRINT.md](../MODERNIZATION_EXTRACTION_SPRINT.md) | Sprint gates, architecture, and certification history |

## Submitted upstream

| PR | Queue | Status |
|----|-------|--------|
| [mathlib4#40707](https://github.com/leanprover-community/mathlib4/pull/40707) | P1 rows 1–12 | submitted — see [MATHLIB_PR_40707_STATUS.md](MATHLIB_PR_40707_STATUS.md) |

## How to open the first Mathlib PR

1. **Read the queue** — [MATHLIB_NATURALITY_PR_QUEUE.md](MATHLIB_NATURALITY_PR_QUEUE.md), rows **1–12** (P1 band). These are documentation examples; Mathlib already has the core lemmas.
2. **Verify manual proofs** — each P1 row maps to a compiling `example` in [`LeanYo/Examples.lean`](../../LeanYo/Examples.lean). Build with `lake build LeanYo.Examples`.
3. **Use the draft** — [MATHLIB_PR_DRAFT_nat_examples.md](MATHLIB_PR_DRAFT_nat_examples.md) has Mathlib-ready `example` blocks, a file placement map (`NatTrans.lean`, `Whiskering.lean`, `Functor/*`, `Yoneda.lean`), and a PR description template. **Do not mention `lean-yo` tactics** in the Mathlib PR.
4. **Branch Mathlib** — fork `mathlib4`, branch from `v4.31.0` (or current `master` if aligned), paste examples into the mapped files under existing `example` / doc sections.
5. **Follow Mathlib style** — run `lake build` on touched modules; add no new imports beyond what each file already uses.
6. **After P1 merges** — use [MATHLIB_PR_DRAFT_reassoc_lemmas.md](MATHLIB_PR_DRAFT_reassoc_lemmas.md) for P2 (rows 13–18), then P3 (one-shot `@[simp]` bundles, rows 19–23). Row 24 and infra rows stay repo-local (see queue notes).

## Cross-references

- Queue row *n* ↔ ledger tactic rows ↔ `LeanYo/Examples.lean` line ranges (in queue table).
- P2/P3 rows share proofs with P1 where the goal is the same; the queue distinguishes **example** vs **reassoc lemma** vs **simp lemma** upstream packaging.
- Row **24** is **blocked** as originally stated (ill-typed `◫` with `yoneda`); refined whiskering identities are proved in `Examples.lean` and documented in the queue.

## Local verification before upstreaming

```bash
lake update
lake build LeanYo
lake build LeanYo.Examples
lake build LeanYoTests
lake exe leanyo-benchmarks
python scripts/production_test.py
python scripts/validate_lemmas.py
```

On Linux/macOS: `bash scripts/ci_build.sh` or `make test`. On Windows: `powershell -File scripts/ci_build.ps1` or `make test` (Makefile selects the script).
