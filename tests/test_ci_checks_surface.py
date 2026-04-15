import subprocess
from pathlib import Path
from unittest.mock import patch

import pytest

from bridge_reptends import load_lean_module_index
from bridge_reptends.ci_checks import (
    CORE_TESTS,
    LAKE,
    LEAN_TARGETS,
    PYTHON,
    ROOT,
    SURFACE_TEST_PATTERNS,
    TESTS,
    _lean_sorry_matches,
    _public_lean_eval_matches,
    _targeted_pytest_files,
    check_registry_doc_surface,
    check_lean_surface,
    check_lean_targets,
    check_python_tests,
    run_ci_checks,
)


def test_ci_checks_builds_public_example_surface() -> None:
    assert "QRTour" in LEAN_TARGETS
    assert "QRTour.Examples" in LEAN_TARGETS
    assert "GeometricStack" in LEAN_TARGETS


def test_ci_checks_lean_targets_follow_public_lean_surface() -> None:
    qr_tour_expected = tuple(
        module.id
        for module in load_lean_module_index()
        if module.path.startswith("lean/QRTour/")
        and module.path.endswith(".lean")
        and module.promotion_decision.startswith("keep as public ")
    )
    geometric_stack_expected = tuple(
        module.id
        for module in load_lean_module_index()
        if module.path.startswith("lean/GeometricStack/")
        and module.path.endswith(".lean")
        and module.promotion_decision.startswith("keep as public ")
    )
    expected = (*qr_tour_expected, "QRTour", *geometric_stack_expected, "GeometricStack")

    assert LEAN_TARGETS == expected


def test_ci_checks_runs_theorem_surface_hygiene_suite() -> None:
    expected_surface = sorted(
        {
            path.name
            for pattern in SURFACE_TEST_PATTERNS
            for path in (ROOT / "tests").glob(pattern)
            if path.is_file()
        }
        - set(CORE_TESTS)
    )

    assert TESTS == (*CORE_TESTS, *expected_surface)


def test_ci_checks_auto_discovers_surface_tests_by_filename(tmp_path: Path) -> None:
    tests_dir = tmp_path / "tests"
    tests_dir.mkdir()
    for filename in CORE_TESTS:
        (tests_dir / filename).write_text("")

    (tests_dir / "test_future_surface_guard.py").write_text("")
    (tests_dir / "test_theorem_guide_future_order.py").write_text("")
    (tests_dir / "test_unrelated.py").write_text("")

    assert _targeted_pytest_files(tmp_path) == (
        *CORE_TESTS,
        "test_future_surface_guard.py",
        "test_theorem_guide_future_order.py",
    )


def test_ci_checks_no_sorry_guard_stays_clean() -> None:
    assert _lean_sorry_matches() == []


def test_ci_checks_public_lean_eval_guard_stays_clean() -> None:
    assert _public_lean_eval_matches() == []


def test_ci_checks_no_sorry_guard_ignores_non_lean_files_in_fallback_scan(tmp_path: Path) -> None:
    (tmp_path / "Example.lean").write_text("theorem no_sorry_here : True := by trivial\n")
    (tmp_path / "notes.txt").write_text("this file says sorry but is not Lean source\n")

    with patch("bridge_reptends.ci_checks.shutil.which", return_value=None):
        assert _lean_sorry_matches(tmp_path) == []


def test_ci_checks_no_sorry_guard_limits_rg_scan_to_lean_sources(tmp_path: Path) -> None:
    with (
        patch("bridge_reptends.ci_checks.shutil.which", return_value="/usr/bin/rg"),
        patch("bridge_reptends.ci_checks.subprocess.run") as run,
    ):
        run.return_value = subprocess.CompletedProcess(
            args=[],
            returncode=1,
            stdout="",
            stderr="",
        )
        assert _lean_sorry_matches(tmp_path) == []

    run.assert_called_once_with(
        ["/usr/bin/rg", "-n", "--glob", "*.lean", r"\bsorry\b", str(tmp_path)],
        check=False,
        capture_output=True,
        text=True,
    )


def test_ci_checks_public_lean_eval_guard_reports_noisy_targets(tmp_path: Path) -> None:
    clean = tmp_path / "Clean.lean"
    noisy = tmp_path / "Noisy.lean"
    clean.write_text("theorem clean_surface : True := by trivial\n")
    noisy.write_text("#eval [1, 4, 2, 8, 5, 7]\n")

    assert _public_lean_eval_matches((clean, noisy)) == [
        f"{noisy}:1:#eval [1, 4, 2, 8, 5, 7]"
    ]


def test_ci_checks_surface_hygiene_reports_eval_noise() -> None:
    with (
        patch("bridge_reptends.ci_checks._lean_sorry_matches", return_value=[]),
        patch(
            "bridge_reptends.ci_checks._public_lean_eval_matches",
            return_value=["lean/GeometricStack/OrbitBufferDuality.lean:202:#eval 1"],
        ),
    ):
        with pytest.raises(
            AssertionError,
            match="Focused public Lean build targets still contain `#eval` directives",
        ) as exc_info:
            check_lean_surface()

    assert "#eval 1" in str(exc_info.value)


def test_ci_checks_runs_registry_doc_sync_guard() -> None:
    with patch("bridge_reptends.ci_checks.check_registry_docs") as check:
        check_registry_doc_surface()

    check.assert_called_once_with()


def test_ci_checks_batches_public_lean_build_targets() -> None:
    with patch("bridge_reptends.ci_checks.subprocess.run") as run:
        check_lean_targets()

    run.assert_called_once_with(
        [LAKE, "build", *LEAN_TARGETS],
        cwd=Path(ROOT / "lean"),
        check=True,
        capture_output=True,
        text=True,
    )


def test_ci_checks_runs_targeted_pytest_suite_via_python_module() -> None:
    with patch("bridge_reptends.ci_checks.subprocess.run") as run:
        check_python_tests()

    run.assert_called_once_with(
        [PYTHON, "-m", "pytest", "-q", *(str(ROOT / "tests" / filename) for filename in TESTS)],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )


def test_ci_checks_surfaces_pytest_failure_output() -> None:
    failure = subprocess.CalledProcessError(
        1,
        [PYTHON, "-m", "pytest", "-q"],
        output="failed test output",
        stderr="stderr details",
    )

    with patch("bridge_reptends.ci_checks.subprocess.run", side_effect=failure):
        with pytest.raises(RuntimeError, match="Targeted pytest suite failed with exit code 1") as exc_info:
            check_python_tests()

    message = str(exc_info.value)
    assert "failed test output" in message
    assert "stderr details" in message


def test_ci_checks_runs_registry_sync_before_build_and_pytest() -> None:
    with (
        patch("bridge_reptends.ci_checks.check_lean_surface") as lean_surface,
        patch("bridge_reptends.ci_checks.check_registry_doc_surface") as registry_docs,
        patch("bridge_reptends.ci_checks.check_lean_targets") as lean_targets,
        patch("bridge_reptends.ci_checks.check_python_tests") as python_tests,
    ):
        total = run_ci_checks()

    assert total == len(TESTS)
    lean_surface.assert_called_once_with()
    registry_docs.assert_called_once_with()
    lean_targets.assert_called_once_with()
    python_tests.assert_called_once_with()
