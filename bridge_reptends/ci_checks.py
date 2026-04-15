"""
Focused CI checks for the current published surfaces.

This intentionally mirrors the targeted pytest-backed suite used during
iteration. It keeps CI lightweight while still covering:

- published atlas/data snapshots
- Lean umbrella/theorem-surface hygiene for both `QRTour` and `GeometricStack`
  without `sorry` or public-target `#eval` noise
- theorem-witness and worked-example surface hygiene
- theorem-guide open-claim boundary/order hygiene
- registry-doc sync command surface
- generated note synchronization
- selector/transducer regression checks
- registry/doc drift checks
"""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path

from .registry import load_lean_module_index
from .sync_registry_docs import check_registry_docs


ROOT = Path(__file__).resolve().parent.parent
LAKE = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
PYTHON = sys.executable


def _public_lean_targets() -> tuple[str, ...]:
    """Return the focused Lean build surface for public Lean modules and umbrellas."""
    module_index = load_lean_module_index()
    qr_tour_public_modules = [
        record.id
        for record in module_index
        if record.path.startswith("lean/QRTour/")
        and record.path.endswith(".lean")
        and record.promotion_decision.startswith("keep as public ")
    ]
    geometric_stack_public_modules = [
        record.id
        for record in module_index
        if record.path.startswith("lean/GeometricStack/")
        and record.path.endswith(".lean")
        and record.promotion_decision.startswith("keep as public ")
    ]
    return (
        *qr_tour_public_modules,
        "QRTour",
        *geometric_stack_public_modules,
        "GeometricStack",
    )


LEAN_TARGETS = _public_lean_targets()
CORE_TESTS = (
    "test_carry_transducer.py",
    "test_visibility.py",
    "test_composite_crt.py",
    "test_search_datasets.py",
    "test_api_normalization.py",
    "test_expository_note.py",
)
SURFACE_TEST_PATTERNS = (
    "test_*surface*.py",
    "test_theorem_guide_*.py",
    "test_registry.py",
    "test_theorem_witnesses.py",
    "test_doc_drift.py",
)


def _targeted_pytest_files(root: Path | None = None) -> tuple[str, ...]:
    """Return the focused pytest surface with core checks explicit and surface tests discovered."""
    repo_root = ROOT if root is None else root
    tests_dir = repo_root / "tests"
    missing_core = [name for name in CORE_TESTS if not (tests_dir / name).exists()]
    if missing_core:
        raise FileNotFoundError(
            "missing focused core pytest files: " + ", ".join(missing_core)
        )

    surface_tests = {
        path.name
        for pattern in SURFACE_TEST_PATTERNS
        for path in tests_dir.glob(pattern)
        if path.is_file()
    }
    return (*CORE_TESTS, *sorted(surface_tests - set(CORE_TESTS)))


TESTS = _targeted_pytest_files()


def _lean_target_paths() -> tuple[Path, ...]:
    """Return filesystem paths for the focused Lean build targets."""
    paths_by_id = {record.id: ROOT / record.path for record in load_lean_module_index()}
    return tuple(paths_by_id[target] for target in LEAN_TARGETS)


def _run_checked(command: list[str], *, cwd: Path, label: str) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            command,
            cwd=cwd,
            check=True,
            capture_output=True,
            text=True,
        )
    except subprocess.CalledProcessError as exc:
        details = "\n".join(
            line
            for line in (
                exc.stdout.strip() if exc.stdout else "",
                exc.stderr.strip() if exc.stderr else "",
            )
            if line
        )
        message = f"{label} failed with exit code {exc.returncode}"
        if details:
            message = f"{message}:\n{details}"
        raise RuntimeError(message) from exc


def _lean_sorry_matches(scan_root: Path | None = None) -> list[str]:
    lean_dir = ROOT / "lean" if scan_root is None else scan_root
    rg = shutil.which("rg")
    if rg is not None:
        result = subprocess.run(
            [rg, "-n", "--glob", "*.lean", r"\bsorry\b", str(lean_dir)],
            check=False,
            capture_output=True,
            text=True,
        )
        if result.returncode == 0:
            return [line for line in result.stdout.splitlines() if line.strip()]
        if result.returncode == 1:
            return []
        raise RuntimeError(result.stderr.strip() or "rg failed while scanning Lean sources")

    matches: list[str] = []
    pattern = re.compile(r"\bsorry\b")
    for path in sorted(lean_dir.rglob("*.lean")):
        for line_number, line in enumerate(path.read_text().splitlines(), start=1):
            if pattern.search(line):
                matches.append(f"{path}:{line_number}:{line.strip()}")
    return matches


def _public_lean_eval_matches(paths: tuple[Path, ...] | None = None) -> list[str]:
    """Return `#eval` directives that would emit output in focused public Lean builds."""
    scan_paths = _lean_target_paths() if paths is None else paths
    pattern = re.compile(r"^\s*#eval\b")
    matches: list[str] = []
    for path in scan_paths:
        for line_number, line in enumerate(path.read_text().splitlines(), start=1):
            if pattern.search(line):
                matches.append(f"{path}:{line_number}:{line.strip()}")
    return matches


def check_lean_surface() -> None:
    matches = _lean_sorry_matches()
    if matches:
        formatted = "\n".join(matches)
        raise AssertionError(f"Lean sources still contain `sorry`:\n{formatted}")
    print("PASS lean::no_sorry")
    eval_matches = _public_lean_eval_matches()
    if eval_matches:
        formatted = "\n".join(eval_matches)
        raise AssertionError(
            "Focused public Lean build targets still contain `#eval` directives:\n"
            f"{formatted}"
        )
    print("PASS lean::no_eval")


def check_registry_doc_surface() -> None:
    check_registry_docs()


def check_lean_targets() -> None:
    lean_dir = ROOT / "lean"
    _run_checked(
        [LAKE, "build", *LEAN_TARGETS],
        cwd=lean_dir,
        label="Lean target build",
    )
    for target in LEAN_TARGETS:
        print(f"PASS lean::build::{target}")


def check_python_tests() -> None:
    tests_dir = ROOT / "tests"
    _run_checked(
        [PYTHON, "-m", "pytest", "-q", *(str(tests_dir / filename) for filename in TESTS)],
        cwd=ROOT,
        label="Targeted pytest suite",
    )
    print("PASS pytest::targeted_suite")


def run_ci_checks() -> int:
    check_lean_surface()
    check_registry_doc_surface()
    check_lean_targets()
    check_python_tests()
    print(f"TOTAL {len(TESTS)} modules")
    return len(TESTS)


def main() -> None:
    run_ci_checks()


if __name__ == "__main__":
    main()
