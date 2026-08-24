# lean-yo current-upstream audit — 2026-08-24

This document supersedes the June 2026 upstream queue **for current Mathlib contribution decisions**. The older extraction ledger remains a historical record of the 4.31 proof corpus and modernization work.

## Audit baseline

- Lean: `leanprover/lean4:v4.34.0-rc2`
- Mathlib: `dc84fcbe9e049439c1c36d6db290cc0565f77788` (master, 2026-08-24)
- Current-baseline build status: **pending CI** until the audit branch workflow completes successfully.

The previous 4.31 build certification is historical and must not be represented as current compatibility evidence.

## Current upstream state

Mathlib PR #40707 (`CategoryTheory: add naturality and whiskering examples`) remains open and unmerged.

The key review signal from the June submission was substantive: a category-theory maintainer stated that the PR did not appear to add anything useful to Mathlib and asked about AI use. That feedback invalidates the original assumption that example-only PRs were a low-risk way to establish upstream value.

Current Mathlib has also moved materially since the June ledger:

- `NatTrans.naturality` is installed as a reassociated simp theorem;
- category-theory core files use category-specific `grind` support;
- current `NatTrans.lean` itself includes a nontrivial multi-arrow naturality example discharged by `grind`.

Therefore the old queue of naturality/whiskering examples, reassociated naturality helper lemmas, and speculative simp bundles must be rebenchmarked from scratch.

## Strategic decision

`lean-yo` remains useful as a **naturality proof-friction and regression laboratory**. It is not currently evidence for upstreaming the `yo` / `naturality!` tactics or an example-only documentation series.

Each benchmark should now answer:

1. does current `simp` solve the goal?
2. does current reassociated naturality solve it directly?
3. does `cat_disch` solve it?
4. does category `grind` solve it?
5. if not, what exact primitive theorem/attribute is missing?
6. does the same gap recur in real category-theory developments?

Only after those questions should the local tactic be compared.

## Decision table

| June stream | Current decision |
|---|---|
| Naturality/whiskering examples (#40707) | Retire as a technical direction; keep proof cases as local fixtures |
| Reassociated naturality lemmas | Re-audit against current `[reassoc (attr := simp)] NatTrans.naturality` |
| Vertical/horizontal composition simp bundles | Rebenchmark; no presumption of a gap |
| Yoneda composite-map examples | Research only if a current real proof exposes discoverability/API friction |
| `yo` tactic | Keep local |
| `naturality!` tactic | Keep local |
| Lemma registry / tactic infrastructure | Repository-local implementation detail |

## Benchmark matrix

For every representative goal, record whether it is solved cleanly by:

| Method | Required result |
|---|---|
| `rfl` | definitional equality only |
| `simp` | current global simp set |
| `simp only` | stable explicit theorem set |
| `rw` / named theorem | direct discoverable API |
| `cat_disch` | current category discharge mechanism |
| `grind` | current category-theory grind support |
| `yo` / `naturality!` | local comparison only |

A local tactic win is not automatically an upstream gap. The diagnostic question is what primitive fact or normalization principle the standard stack lacks.

## Real-proof requirement

A candidate theorem/attribute should normally be supported by at least three independent real proof sites, or by one substantial proof where the missing API is clearly the dominant friction.

Synthetic goals remain valuable as regression fixtures, but they do not by themselves justify Mathlib surface growth.

## AI-policy constraint

Mathlib's current contribution policy is a first-order project constraint:

- AI use affecting a PR must be accurately disclosed;
- the contributor must understand and be able to justify every submitted declaration/proof;
- GitHub/Zulip discussion must be written by the contributor in their own words rather than generated for copy/paste.

Accordingly, this repository may be used for code archaeology, experiments, proof drafts, benchmarks, and internal reasoning. Maintainer-facing discussion must remain the contributor's own communication.

## Acceptance gate for any Yo-derived Mathlib PR

A candidate may move to `PR_READY` only when:

1. the current 4.34/Mathlib baseline builds;
2. current master and open PRs do not already solve the goal cleanly;
3. `simp`, `cat_disch`, `grind`, and the current named API have been benchmarked;
4. the gap is demonstrated in real downstream proof sites;
5. the candidate is a primitive theorem/attribute/API improvement rather than a tactic-specific artifact;
6. no `sorry`, `admit`, custom axiom, or local tactic is needed in the submitted proof;
7. the PR remains useful to Mathlib users who have never seen `lean-yo`.

## Immediate work queue

1. Obtain CI evidence on the current baseline.
2. Re-run the naturality corpus against current `simp`, `cat_disch`, and `grind`.
3. Mark every old ledger row `EXISTS_UPSTREAM`, `SOLVED_BY_AUTOMATION`, `RESEARCH`, or `CANDIDATE`.
4. Mine current real category-theory files for repeated manual naturality rearrangements.
5. Only prepare a new Mathlib candidate if a primitive recurring gap survives that audit.
