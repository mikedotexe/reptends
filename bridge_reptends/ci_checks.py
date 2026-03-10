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


def run_ci_checks() -> int:
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
