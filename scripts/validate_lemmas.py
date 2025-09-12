#!/usr/bin/env python3
"""
Lean-Yo Lemma Validation Script

This script validates lemmas in the lean-yo database to ensure they meet
governance requirements including loop detection, performance validation,
and quality checks.
"""

import os
import re
import time
import subprocess
import json
from typing import List, Dict, Any, Optional
from dataclasses import dataclass
from pathlib import Path


@dataclass
class LemmaInfo:
    """Information about a lemma in the database."""

    name: str
    file_path: str
    line_number: int
    attribute: str  # '@[naturality]' or '@[yo.fuse]'
    type_signature: str
    proof: str
    documentation: str
    performance_metrics: Dict[str, float]


@dataclass
class ValidationResult:
    """Result of lemma validation."""

    lemma: LemmaInfo
    passed: bool
    errors: List[str]
    warnings: List[str]
    performance_score: float
    loop_detection_passed: bool


class LemmaValidator:
    """Validates lemmas according to lean-yo governance requirements."""

    def __init__(self, project_root: Path):
        self.project_root = project_root
        self.lemmas: List[LemmaInfo] = []
        self.validation_results: List[ValidationResult] = []

    def discover_lemmas(self) -> List[LemmaInfo]:
        """Discover all lemmas with @[naturality] or @[yo.fuse] attributes."""
        lemmas = []

        # Search for .lean files
        for lean_file in self.project_root.rglob("*.lean"):
            if self._should_skip_file(lean_file):
                continue

            file_lemmas = self._extract_lemmas_from_file(lean_file)
            lemmas.extend(file_lemmas)

        return lemmas

    def _should_skip_file(self, file_path: Path) -> bool:
        """Check if file should be skipped during lemma discovery."""
        skip_patterns = [
            "lake-packages",
            ".lake",
            "build",
            "Tests/",  # Skip test files
            "Examples.lean",  # Skip example files
        ]

        return any(pattern in str(file_path) for pattern in skip_patterns)

    def _extract_lemmas_from_file(self, file_path: Path) -> List[LemmaInfo]:
        """Extract lemmas from a single .lean file."""
        lemmas = []

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Find lemmas with @[naturality] or @[yo.fuse] attributes
            lines = content.split("\n")
            for i, line in enumerate(lines):
                if "@[naturality]" in line or "@[yo.fuse]" in line:
                    lemma_info = self._parse_lemma(lines, i, file_path)
                    if lemma_info:
                        lemmas.append(lemma_info)

        except Exception as e:
            print(f"Error reading file {file_path}: {e}")

        return lemmas

    def _parse_lemma(
        self, lines: List[str], start_line: int, file_path: Path
    ) -> Optional[LemmaInfo]:
        """Parse a single lemma from lines starting at start_line."""
        try:
            # Extract attribute
            attr_line = lines[start_line]
            if "@[naturality]" in attr_line:
                attribute = "@[naturality]"
            elif "@[yo.fuse]" in attr_line:
                attribute = "@[yo.fuse]"
            else:
                return None

            # Find the theorem/lemma declaration
            theorem_line = None
            for i in range(start_line + 1, min(start_line + 10, len(lines))):
                if lines[i].strip().startswith(("theorem ", "lemma ", "def ")):
                    theorem_line = i
                    break

            if theorem_line is None:
                return None

            # Extract name and signature
            theorem_text = lines[theorem_line].strip()
            name_match = re.search(
                r"(theorem|lemma|def)\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*[:(]", theorem_text
            )
            if not name_match:
                return None

            name = name_match.group(2)

            # Extract documentation (comments before the lemma)
            documentation = ""
            for i in range(max(0, start_line - 10), start_line):
                if lines[i].strip().startswith("--"):
                    documentation += lines[i].strip() + "\n"

            return LemmaInfo(
                name=name,
                file_path=str(file_path),
                line_number=theorem_line + 1,
                attribute=attribute,
                type_signature=theorem_text,
                proof="",  # Would need more sophisticated parsing
                documentation=documentation,
                performance_metrics={},
            )

        except Exception as e:
            print(f"Error parsing lemma at line {start_line} in {file_path}: {e}")
            return None

    def validate_lemma(self, lemma: LemmaInfo) -> ValidationResult:
        """Validate a single lemma according to governance requirements."""
        errors = []
        warnings = []

        # Check documentation
        if not lemma.documentation.strip():
            errors.append("Missing documentation")
        elif len(lemma.documentation) < 50:
            warnings.append("Documentation is too brief")

        # Check type signature
        if not self._validate_type_signature(lemma):
            errors.append("Invalid type signature for attribute")

        # Check for loop patterns
        loop_detection_passed = self._check_loop_patterns(lemma)
        if not loop_detection_passed:
            errors.append("Potential loop detected")

        # Performance validation
        performance_score = self._validate_performance(lemma)
        if performance_score < 0.8:
            warnings.append(f"Performance score below threshold: {performance_score}")

        # Check naming conventions
        if not self._validate_naming(lemma):
            warnings.append("Naming convention not followed")

        passed = len(errors) == 0

        return ValidationResult(
            lemma=lemma,
            passed=passed,
            errors=errors,
            warnings=warnings,
            performance_score=performance_score,
            loop_detection_passed=loop_detection_passed,
        )

    def _validate_type_signature(self, lemma: LemmaInfo) -> bool:
        """Validate that the type signature matches the attribute."""
        signature = lemma.type_signature.lower()

        if lemma.attribute == "@[naturality]":
            # Should contain naturality patterns
            return (
                "naturality" in signature or "app" in signature and "map" in signature
            )
        elif lemma.attribute == "@[yo.fuse]":
            # Should contain fusion patterns
            return "map" in signature or "comp" in signature

        return True

    def _check_loop_patterns(self, lemma: LemmaInfo) -> bool:
        """Check for potential loop patterns in the lemma."""
        # Simple loop detection - in practice, this would be more sophisticated
        signature = lemma.type_signature.lower()

        # Check for self-referential patterns
        if lemma.name.lower() in signature:
            return False

        # Check for circular dependencies
        if "naturality" in lemma.name.lower() and lemma.attribute == "@[yo.fuse]":
            return False
        if "fuse" in lemma.name.lower() and lemma.attribute == "@[naturality]":
            return False

        return True

    def _validate_performance(self, lemma: LemmaInfo) -> float:
        """Validate lemma performance (placeholder implementation)."""
        # In practice, this would run actual performance tests
        # For now, return a score based on heuristic analysis

        score = 1.0

        # Penalize very long type signatures
        if len(lemma.type_signature) > 200:
            score -= 0.1

        # Penalize complex patterns
        complex_patterns = ["⊗", "⊕", "⨁", "⨂"]
        for pattern in complex_patterns:
            if pattern in lemma.type_signature:
                score -= 0.05

        return max(0.0, score)

    def _validate_naming(self, lemma: LemmaInfo) -> bool:
        """Validate lemma naming conventions."""
        name = lemma.name.lower()

        if lemma.attribute == "@[naturality]":
            return "naturality" in name or "nat" in name
        elif lemma.attribute == "@[yo.fuse]":
            return "fuse" in name or "comp" in name or "map" in name

        return True

    def run_validation(self) -> Dict[str, Any]:
        """Run complete validation of all lemmas."""
        print("Discovering lemmas...")
        self.lemmas = self.discover_lemmas()
        print(f"Found {len(self.lemmas)} lemmas")

        print("Validating lemmas...")
        for lemma in self.lemmas:
            result = self.validate_lemma(lemma)
            self.validation_results.append(result)

        return self._generate_report()

    def _generate_report(self) -> Dict[str, Any]:
        """Generate validation report."""
        total_lemmas = len(self.validation_results)
        passed_lemmas = sum(1 for r in self.validation_results if r.passed)
        failed_lemmas = total_lemmas - passed_lemmas

        total_warnings = sum(len(r.warnings) for r in self.validation_results)
        total_errors = sum(len(r.errors) for r in self.validation_results)

        avg_performance = (
            sum(r.performance_score for r in self.validation_results) / total_lemmas
            if total_lemmas > 0
            else 0
        )

        report = {
            "summary": {
                "total_lemmas": total_lemmas,
                "passed": passed_lemmas,
                "failed": failed_lemmas,
                "success_rate": passed_lemmas / total_lemmas if total_lemmas > 0 else 0,
                "total_warnings": total_warnings,
                "total_errors": total_errors,
                "average_performance_score": avg_performance,
            },
            "detailed_results": [
                {
                    "name": r.lemma.name,
                    "file": r.lemma.file_path,
                    "attribute": r.lemma.attribute,
                    "passed": r.passed,
                    "errors": r.errors,
                    "warnings": r.warnings,
                    "performance_score": r.performance_score,
                    "loop_detection_passed": r.loop_detection_passed,
                }
                for r in self.validation_results
            ],
        }

        return report

    def print_report(self, report: Dict[str, Any]):
        """Print validation report to console."""
        summary = report["summary"]

        print("\n" + "=" * 60)
        print("LEAN-YO LEMMA VALIDATION REPORT")
        print("=" * 60)

        print(f"Total Lemmas: {summary['total_lemmas']}")
        print(f"Passed: {summary['passed']}")
        print(f"Failed: {summary['failed']}")
        print(f"Success Rate: {summary['success_rate']:.1%}")
        print(f"Total Warnings: {summary['total_warnings']}")
        print(f"Total Errors: {summary['total_errors']}")
        print(f"Average Performance Score: {summary['average_performance_score']:.2f}")

        print("\nDETAILED RESULTS:")
        print("-" * 60)

        for result in report["detailed_results"]:
            status = "✅ PASS" if result["passed"] else "❌ FAIL"
            print(f"{status} {result['name']} ({result['attribute']})")
            print(f"    File: {result['file']}")
            print(f"    Performance Score: {result['performance_score']:.2f}")
            print(
                f"    Loop Detection: {'✅' if result['loop_detection_passed'] else '❌'}"
            )

            if result["errors"]:
                print(f"    Errors: {', '.join(result['errors'])}")
            if result["warnings"]:
                print(f"    Warnings: {', '.join(result['warnings'])}")
            print()


def main():
    """Main entry point for the validation script."""
    import argparse

    parser = argparse.ArgumentParser(description="Validate lean-yo lemmas")
    parser.add_argument(
        "--project-root",
        type=Path,
        default=Path.cwd(),
        help="Root directory of the lean-yo project",
    )
    parser.add_argument("--output", type=str, help="Output file for JSON report")
    parser.add_argument("--verbose", action="store_true", help="Verbose output")

    args = parser.parse_args()

    validator = LemmaValidator(args.project_root)

    start_time = time.time()
    report = validator.run_validation()
    end_time = time.time()

    validator.print_report(report)

    if args.output:
        with open(args.output, "w") as f:
            json.dump(report, f, indent=2)
        print(f"\nReport saved to {args.output}")

    print(f"\nValidation completed in {end_time - start_time:.2f} seconds")

    # Exit with error code if any lemmas failed
    if report["summary"]["failed"] > 0:
        exit(1)


if __name__ == "__main__":
    main()
