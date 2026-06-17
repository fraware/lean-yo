# Mathlib PR #40707 status

**PR:** [leanprover-community/mathlib4#40707](https://github.com/leanprover-community/mathlib4/pull/40707)  
**Title (current):** `CategoryTheory: add naturality and whiskering reference examples`  
**State:** open (as of 2026-06-17)  
**Lean-yo queue:** P1 rows 1–12

---

## CI summary

| Check | Result | Notes |
|-------|--------|-------|
| `check_title` | **failure** | Title must follow Mathlib commit style |
| `ci (fork) / Build` | **failure** | Branch predates cache storage-layout migration |
| `ci (fork) / Lint style` | success | |
| `Lint and suggest` | success | |
| Other automation | success / neutral | welcome bot, labels, PR summary |

No human maintainer reviews yet.

---

## Actionable fixes (on the Mathlib fork / PR)

### 1. Retitle the PR (required)

Mathlib expects:

```text
doc(CategoryTheory): add naturality and whiskering reference examples
```

Allowed kinds include `doc`, `feat`, `chore`, etc. Scope `CategoryTheory` is optional but recommended. Subject: imperative, lowercase, no trailing period.

### 2. Merge current `master` into the PR branch (required for build)

Fork CI failed with:

```text
Your branch predates the cache storage-layout migration; merge master so 'lake exe cache get' can read your branch's artifacts.
```

**Fix:** on the Mathlib fork branch, merge or rebase onto current `leanprover-community/mathlib4` `master`, then push. This is infrastructure (PR #40035), not a proof error.

### 3. After green CI

- Post on [Lean Zulip](https://leanprover.zulipchat.com/) if not already done (welcome bot reminder).
- Watch [queueboard entry for #40707](https://leanprover-community.github.io/queueboard/on_the_queue.html?search=40707).

---

## Repo-local next steps

- **Do not open P2** until #40707 merges — draft ready at [MATHLIB_PR_DRAFT_reassoc_lemmas.md](MATHLIB_PR_DRAFT_reassoc_lemmas.md).
- No Mathlib fork changes from lean-yo unless applying the two fixes above on the contributor's fork.
