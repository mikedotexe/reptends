"""
Focused CI checks for the current published surfaces.

This intentionally mirrors the targeted direct-harness suite used during
iteration. It keeps CI lightweight while still covering:

- published atlas/data snapshots
- generated note synchronization
- selector/transducer regression checks
- registry/doc drift checks
"""

from __future__ import annotations

import importlib.util
import re
import shutil
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
TESTS = (
    "test_carry_transducer.py",
    "test_search_datasets.py",
    "test_api_normalization.py",
    "test_expository_note.py",
    "test_registry.py",
    "test_doc_drift.py",
)


def _lean_sorry_matches() -> list[str]:
    lean_dir = ROOT / "lean"
    rg = shutil.which("rg")
    if rg is not None:
        result = subprocess.run(
            [rg, "-n", r"\bsorry\b", str(lean_dir)],
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


def check_lean_surface() -> None:
    matches = _lean_sorry_matches()
    if matches:
        formatted = "\n".join(matches)
        raise AssertionError(f"Lean sources still contain `sorry`:\n{formatted}")
    print("PASS lean::no_sorry")


def run_ci_checks() -> int:
    check_lean_surface()
    tests_dir = ROOT / "tests"
    total = 0
    for filename in TESTS:
        path = tests_dir / filename
        spec = importlib.util.spec_from_file_location(path.stem, path)
        if spec is None or spec.loader is None:
            raise RuntimeError(f"Unable to load test module {path}")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        for name in sorted(dir(module)):
            if not name.startswith("test_"):
                continue
            test = getattr(module, name)
            if not callable(test):
                continue
            test()
            total += 1
            print(f"PASS {filename}::{name}")
    print(f"TOTAL {total}")
    return total


def main() -> None:
    run_ci_checks()


if __name__ == "__main__":
    main()
