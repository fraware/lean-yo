#!/usr/bin/env bash
# Single entry point for CI and local verification: sync deps, build library, examples, tests.
set -euo pipefail
cd "$(dirname "$0")/.."

lake update
lake build LeanYo
lake build LeanYo.Examples
lake build LeanYoTests
echo "LeanYoTests: pass"
