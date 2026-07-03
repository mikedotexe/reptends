import re
from pathlib import Path

import pytest

import bridge_reptends.sync_registry_docs as sync_registry_docs_module


ROOT = Path(__file__).resolve().parent.parent
MARKER_PATTERN = re.compile(r"<!-- ([A-Z0-9_]+)_START -->")
SYNC_TARGETS = tuple(
    path.relative_to(ROOT).as_posix()
    for path in sync_registry_docs_module.registry_doc_updates()
)


def _copy_sync_targets(tmp_path: Path) -> None:
    for relative in SYNC_TARGETS:
        destination = tmp_path / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text((ROOT / relative).read_text())


def _replace_block(text: str, start_marker: str, end_marker: str, body: str) -> str:
    start = text.index(start_marker) + len(start_marker)
    end = text.index(end_marker)
    return text[:start] + f"\n{body}\n" + text[end:]


def _marker_backed_doc_paths() -> set[Path]:
    candidates = [
        ROOT / "README.md",
        *sorted((ROOT / "docs").rglob("*.md")),
        *sorted((ROOT / "lean").rglob("*.md")),
        *sorted((ROOT / "lean").rglob("*.lean")),
    ]
    return {path for path in candidates if MARKER_PATTERN.search(path.read_text())}


def test_registry_doc_updates_cover_every_marker_backed_theorem_surface_doc() -> None:
    managed_paths = set(sync_registry_docs_module.registry_doc_updates())

    assert managed_paths == _marker_backed_doc_paths()


def test_sync_registry_docs_is_noop_when_docs_are_current(tmp_path: Path, monkeypatch) -> None:
    _copy_sync_targets(tmp_path)

    monkeypatch.setattr(sync_registry_docs_module, "ROOT", tmp_path)

    assert sync_registry_docs_module.sync_registry_docs() == ()
    assert sync_registry_docs_module.sync_registry_docs(check=True) == ()


def test_sync_registry_docs_check_mode_reports_drift_without_rewriting(tmp_path: Path, monkeypatch) -> None:
    _copy_sync_targets(tmp_path)

    theorem_guide = tmp_path / "lean" / "THEOREM_GUIDE.md"
    drifted = _replace_block(
        theorem_guide.read_text(),
        "<!-- THEOREM_GUIDE_CLAIM_CARRIERS_START -->",
        "<!-- THEOREM_GUIDE_CLAIM_CARRIERS_END -->",
        "| drifted | theorem guide | claim carriers |",
    )
    theorem_guide.write_text(drifted)

    monkeypatch.setattr(sync_registry_docs_module, "ROOT", tmp_path)

    touched = sync_registry_docs_module.sync_registry_docs(check=True)

    assert touched == (theorem_guide,)
    assert theorem_guide.read_text() == drifted


def test_sync_registry_docs_restores_examples_proof_legend(tmp_path: Path, monkeypatch) -> None:
    _copy_sync_targets(tmp_path)

    examples_surface = tmp_path / "lean" / "QRTour" / "Examples.lean"
    drifted = _replace_block(
        examples_surface.read_text(),
        "<!-- PROOF_SYSTEM_LEGEND_START -->",
        "<!-- PROOF_SYSTEM_LEGEND_END -->",
        "- drifted example legend",
    )
    examples_surface.write_text(drifted)

    monkeypatch.setattr(sync_registry_docs_module, "ROOT", tmp_path)

    touched = sync_registry_docs_module.sync_registry_docs(check=True)

    assert touched == (examples_surface,)
    restored = sync_registry_docs_module.sync_registry_docs()
    assert restored == (examples_surface,)
    assert "- drifted example legend" not in examples_surface.read_text()


def test_sync_registry_docs_restores_examples_open_boundary_note(tmp_path: Path, monkeypatch) -> None:
    _copy_sync_targets(tmp_path)

    examples_surface = tmp_path / "lean" / "QRTour" / "Examples.lean"
    drifted = _replace_block(
        examples_surface.read_text(),
        "<!-- EXAMPLES_OPEN_BOUNDARY_NOTE_START -->",
        "<!-- EXAMPLES_OPEN_BOUNDARY_NOTE_END -->",
        "- drifted example open-boundary note",
    )
    examples_surface.write_text(drifted)

    monkeypatch.setattr(sync_registry_docs_module, "ROOT", tmp_path)

    touched = sync_registry_docs_module.sync_registry_docs(check=True)

    assert touched == (examples_surface,)
    restored = sync_registry_docs_module.sync_registry_docs()
    assert restored == (examples_surface,)
    assert "- drifted example open-boundary note" not in examples_surface.read_text()


def test_sync_registry_docs_restores_theorem_surface_docs(tmp_path: Path, monkeypatch) -> None:
    _copy_sync_targets(tmp_path)
    relative_targets = [Path(relative) for relative in SYNC_TARGETS]
    originals = {relative: (ROOT / relative).read_text() for relative in relative_targets}

    for relative in relative_targets:
        drifted_text = (tmp_path / relative).read_text()
        for index, (start_marker, end_marker, _lines) in enumerate(
            sync_registry_docs_module.registry_doc_updates()[ROOT / relative]
        ):
            drifted_text = _replace_block(
                drifted_text,
                start_marker,
                end_marker,
                f"drifted {relative.as_posix()} block {index}",
            )
        (tmp_path / relative).write_text(drifted_text)

    monkeypatch.setattr(sync_registry_docs_module, "ROOT", tmp_path)

    touched = sync_registry_docs_module.sync_registry_docs()

    assert set(touched) == {tmp_path / relative for relative in relative_targets}
    for relative, original in originals.items():
        assert (tmp_path / relative).read_text() == original


def test_sync_registry_docs_main_check_exits_nonzero_on_drift(tmp_path: Path, monkeypatch, capsys) -> None:
    _copy_sync_targets(tmp_path)

    witness_atlas = tmp_path / "docs" / "THEOREM_WITNESS_ATLAS.md"
    drifted = _replace_block(
        witness_atlas.read_text(),
        "<!-- THEOREM_WITNESS_TABLE_START -->",
        "<!-- THEOREM_WITNESS_TABLE_END -->",
        "| drifted | witness | atlas |",
    )
    witness_atlas.write_text(drifted)

    monkeypatch.setattr(sync_registry_docs_module, "ROOT", tmp_path)

    with pytest.raises(SystemExit, match="1"):
        sync_registry_docs_module.main(["--check"])

    assert witness_atlas.read_text() == drifted
    assert capsys.readouterr().out.strip().splitlines() == ["docs/THEOREM_WITNESS_ATLAS.md"]
