# Contributing to LeanYo

## Prerequisites

- **Lean and Lake** matching [`lean-toolchain`](lean-toolchain).
- **Git**. On Windows, use an environment where `make` and a Unix shell work (for example Git Bash or WSL), or run the equivalent `lake` commands by hand.
- **Python 3.12+** if you run the helper scripts under `scripts/`.

## Mathlib and Lean versions

The library depends on a specific Mathlib revision recorded in [`lakefile.lean`](lakefile.lean) and [`lake-manifest.json`](lake-manifest.json). Avoid editing the manifest by hand unless you are comfortable with Lake.

**To bump dependencies:**

1. Run `lake update` (and change `lean-toolchain` if the new Mathlib needs a newer Lean).
2. Run `make test` and fix any failures.
3. Commit manifest and toolchain changes together with any code fixes.

Maintainers may use automation in the repository to open pull requests after a successful dependency update.

## Documentation

When you change user-visible behavior, keep these in sync:

| Document | Purpose |
|----------|---------|
| [`README.md`](README.md) | Install, quickstart, compatibility |
| [`docs/USAGE_GUIDE.md`](docs/USAGE_GUIDE.md) | When to use which tactic |
| [`docs/API_REFERENCE.md`](docs/API_REFERENCE.md) | Syntax, options, helpers |
| [`docs/DEVELOPER_GUIDE.md`](docs/DEVELOPER_GUIDE.md) | Architecture and tests |
| [`docs/GOVERNANCE.md`](docs/GOVERNANCE.md) | Lemma and review expectations |

If you change how the project is built, tested, or released, update [`README.md`](README.md) and this file as needed.

## Before you open a pull request

1. Add or extend `example` proofs in `LeanYo.Tests.P0`, `P1`, or `P2` when behavior changes.
2. Run `make test`.
3. Update `README.md` or `docs/` when tactics, options, or attributes change.

## Pull requests

Use the PR template. Prefer small, focused changes.

## Code style

- Match surrounding Lean style and naming.
- Prefer clear tactic messages and bounded search (timeouts and step limits) for new automation.
- Briefly document non-obvious `unsafe` code or global `IO.Ref` usage (see `LeanYo.Tactics` and `LeanYo.Utils`).
