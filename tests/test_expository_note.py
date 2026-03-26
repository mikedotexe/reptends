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
    assert "THEOREM_WITNESS_ATLAS.md" in note
    for witness_id in [
        "series_q_weighted_identity_prime97_stride2",
        "same_core_threshold_shift_interval_996_over_249",
        "small_k_visibility_threshold_target_97_249_996",
        "carry_dfa_factorization_target_21_97_996",
    ]:
        assert f"`{witness_id}`" in note
    for claim in load_claim_registry():
        assert f"`{claim.id}`" in note
        for evidence_path in claim.evidence:
            assert Path(evidence_path).name in note
