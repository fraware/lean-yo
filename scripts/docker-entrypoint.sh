#!/usr/bin/env bash
set -euo pipefail

if [[ "${1:-}" == "--help" || "${1:-}" == "-h" || $# -eq 0 ]]; then
  cat <<'EOF'
LeanYo — Lean 4 tactic library for category theory (Yoneda / naturality helpers)

Usage:
  lean-yo --help          This message
  lean-yo --version       Toolchain and Lean versions
  lean-yo --examples      Typecheck example module (lake build LeanYo.Examples)
  lean-yo --test          Build library, tests, and run Python checks
  lean-yo --validate      Run lemma validation script
  lean-yo <file.lean>     Typecheck a Lean file in the Lake environment (lake env lean)

Interactive:
  docker run -it --rm -v "$(pwd):/workspace" ghcr.io/fraware/lean-yo:latest bash

Docs: https://github.com/fraware/lean-yo/tree/main/docs
EOF
  exit 0
fi

case "$1" in
  --version)
    echo "LeanYo (pinned Lean from lean-toolchain): $(cut -d: -f2 lean-toolchain)"
    lean --version
    ;;
  --examples)
    echo "Typechecking LeanYo.Examples..."
    lake build LeanYo.Examples
    ;;
  --test)
    echo "Building library and tests..."
    lake build
    lake build LeanYo.Tests.P0 LeanYo.Tests.P1 LeanYo.Tests.P2 LeanYo.Tests.Benchmarks
    if [[ -f scripts/production_test.py ]]; then
      python3 scripts/production_test.py
    fi
    ;;
  --validate)
    if [[ -f scripts/validate_lemmas.py ]]; then
      python3 scripts/validate_lemmas.py
    else
      echo "Validation script not found" >&2
      exit 1
    fi
    ;;
  *.lean)
    echo "Typechecking Lean file: $1"
    lake env lean "$1"
    ;;
  *)
    echo "Unknown option: $1" >&2
    echo "Run lean-yo --help" >&2
    exit 1
    ;;
esac
