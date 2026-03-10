from pathlib import Path

from bridge_reptends import load_claim_registry
from bridge_reptends.build_expository_note import render_expository_note_lines


ROOT = Path(__file__).resolve().parent.parent
NOTE_PATH = ROOT / "docs" / "EXPOSITORY_NOTE.md"


def test_expository_note_matches_generator() -> None:
    assert NOTE_PATH.exists()
    expected = "\n".join(render_expository_note_lines()) + "\n"
    assert NOTE_PATH.read_text() == expected


def test_expository_note_traces_claims_to_ids_and_evidence() -> None:
    note = NOTE_PATH.read_text()
    for claim in load_claim_registry():
        assert f"`{claim.id}`" in note
        for evidence_path in claim.evidence:
            assert Path(evidence_path).name in note
