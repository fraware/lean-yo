#!/usr/bin/env bash
# Single entry point for CI and local verification: sync deps, build library, examples, and test modules.
set -euo pipefail
cd "$(dirname "$0")/.."

lake update
lake build
lake build LeanYo.Examples
lake build LeanYo.Tests.P0 LeanYo.Tests.P1 LeanYo.Tests.P2 LeanYo.Tests.Benchmarks
