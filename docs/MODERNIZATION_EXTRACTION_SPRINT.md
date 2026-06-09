# Modernization and extraction sprint

This document records the first modernization and extraction plan for `lean-yo` as part of the broader category-theory contribution program targeting Mathlib and CSLib.

## Current repository position

`lean-yo` implements category-theory proof automation around Yoneda-style rewrites, functoriality, naturality squares, whiskering, rewrite kernels, tuned simp sets, attributes, and options.

The repository is valuable primarily as a Mathlib proof-friction detector. The most important upstream product is not the tactic itself. The first product is a ledger of missing simp lemmas, naturality variants, reassociation lemmas, and documentation examples found by the tactic.

Current constraints:

- Current toolchain in `lean-toolchain`: `leanprover/lean4:v4.8.0`.
- `lakefile.lean` pins Mathlib at `v4.8.0`.
- The public top-level module imports tactics, attributes, options, rewrite kernel, utilities, and simp sets.
- The README presents `yo`, `yo?`, `naturality!`, and `naturality?` as the main user-facing commands.

## Sprint objective

The objective is to port the repository to the Lean 4.31 / current-Mathlib line and use it to extract a first sequence of Mathlib PR candidates around naturality, functoriality, whiskering, and Yoneda-style examples.

The first upstream outputs should be lemmas and examples. The tactic should remain external until current-Mathlib compatibility, predictability, and test coverage are established.

## Modernization gates

### Gate 1: port to current Mathlib

Required commands:

```bash
lake update
lake build LeanYo
lake exe leanyo-benchmarks
make test
```

Expected first failures to check:

- moved Mathlib category-theory imports;
- Lean tactic elaborator API drift;
- changes in simp extension APIs;
- attribute implementation changes;
- notation changes around functors, natural transformations, whiskering, and Yoneda.

### Gate 2: separate stable components

Recommended target layout:

```text
LeanYo/Core/RewriteKernel.lean
LeanYo/Core/SimpSets.lean
LeanYo/Core/Options.lean
LeanYo/Core/Attributes.lean
LeanYo/Tactics/Yo.lean
LeanYo/Tactics/Naturality.lean
LeanYo/Examples.lean
LeanYo.lean
```

The top-level import should remain convenient for users, but extraction work must be able to import the kernel without loading every tactic command.

### Gate 3: build the Mathlib extraction ledger

Every time `yo` or `naturality!` solves a proof, record whether the proof indicates missing Mathlib API.

Required ledger columns:

- tactic used;
- input goal;
- proof shape generated or intended;
- existing Mathlib theorem used;
- missing theorem, if any;
- proposed statement;
- proposed Mathlib file path;
- expected maintainability risk.

## Extraction targets

### Target A: naturality lemmas

Candidate Mathlib outputs:

- naturality variants oriented for `simp`;
- reassociated naturality lemmas;
- lemmas for natural transformations composed with functor maps;
- examples showing canonical proof patterns without custom tactics.

### Target B: whiskering API

Candidate Mathlib outputs:

- left- and right-whiskering simplification lemmas;
- composition lemmas for whiskered natural transformations;
- examples that reduce proof boilerplate in functor-category work.

### Target C: Yoneda examples

Yoneda material should be introduced carefully. The first upstream contribution should likely be documentation examples or small helper lemmas, not a rewrite tactic.

### Target D: tactic hardening

A later tactic proposal is possible only after:

- the package builds on current Mathlib;
- the tactic has narrow, predictable scope;
- failure messages are clear;
- the test suite uses real current-Mathlib examples;
- the extraction ledger shows that the remaining friction cannot be solved by ordinary lemmas.

## Non-upstream material for now

The following should remain repository-local during this sprint:

- `yo` tactic;
- `yo?` debug tactic;
- `naturality!` tactic;
- `naturality?` debug tactic;
- custom rewrite kernel;
- registration attributes;
- benchmark executable;
- Docker packaging.

## First PR candidates generated from this repo

1. Local modernization PR: port to Lean 4.31 and current Mathlib.
2. Local architecture PR: separate rewrite kernel, simp sets, attributes, and tactic frontends.
3. Local audit PR: create a naturality and whiskering extraction ledger.
4. Mathlib candidate PR: add missing naturality simp or reassociation lemmas discovered by the ledger.
5. Mathlib candidate PR: add whiskering examples and helper lemmas.
6. Mathlib candidate PR: add Yoneda usage examples if they fill a confirmed documentation gap.

## Build certification status

This document is a planning and extraction artifact. It does not certify that the repository has been built on Lean 4.31 yet. Certification requires a successful local or CI run of the commands in Gate 1.
