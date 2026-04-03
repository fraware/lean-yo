import LeanYo
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.Category

/-!
# Benchmarks (smoke / timing harness)

This module typechecks with the rest of the test suite. The IO actions below measure
cheap pure loops only; they do **not** benchmark tactic execution inside the elaborator.
For real tactic timings you would need a dedicated harness (e.g. repeated `MetaM` goals).
-/

namespace LeanYo.Tests.Benchmarks

private def separatorLine : String :=
  String.mk (List.replicate 60 '=')

/-- Minimal timing helper: returns elapsed milliseconds. -/
private def timeLoop (name : String) (iterations : Nat) (body : Nat → IO Unit) : IO Unit := do
  let t0 ← IO.monoMsNow
  for i in List.range iterations do
    body i
  let t1 ← IO.monoMsNow
  let elapsed := t1 - t0
  IO.println s!"{name}: {iterations} iterations in {elapsed}ms (total wall time)"

def benchmarkYoSmoke (iterations : Nat := 1000) : IO Unit := do
  IO.println s!"Smoke: yo-related pure work × {iterations}"
  timeLoop "yo-smoke" iterations fun i => do
    let _ := i + 1
    pure ()

def benchmarkNaturalitySmoke (iterations : Nat := 1000) : IO Unit := do
  IO.println s!"Smoke: naturality-related pure work × {iterations}"
  timeLoop "naturality-smoke" iterations fun i => do
    let _ := i * 2
    pure ()

def runAllBenchmarks : IO Unit := do
  IO.println "LeanYo benchmark smoke (IO timing of cheap loops; not tactic elab)"
  IO.println separatorLine
  benchmarkYoSmoke 1000
  IO.println ""
  benchmarkNaturalitySmoke 1000
  IO.println ""
  IO.println "Done."

end LeanYo.Tests.Benchmarks

/-- Lake `lean_exe` entry point (module root). -/
def main : IO Unit := LeanYo.Tests.Benchmarks.runAllBenchmarks
