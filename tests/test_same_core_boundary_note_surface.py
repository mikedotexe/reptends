from dataclasses import replace

import pytest

from bridge_reptends import load_theorem_witnesses, render_same_core_boundary_note_lines


VISIBILITY_WITNESS_ID = "same_core_threshold_shift_interval_996_over_249"
CARRY_WITNESS_ID = "carry_dfa_factorization_target_249_498_996_same_core"


def _replace_witness(witness_id: str, **changes: str) -> list:
    return [
        replace(record, **changes) if record.id == witness_id else record
        for record in load_theorem_witnesses()
    ]


def test_same_core_boundary_note_keeps_exact_then_open_witness_roles() -> None:
    witness_map = {record.id: record for record in load_theorem_witnesses()}

    assert witness_map[VISIBILITY_WITNESS_ID].claim_id == "same_core_threshold_shift_interval"
    assert witness_map[VISIBILITY_WITNESS_ID].kind == "theorem-witness"
    assert witness_map[CARRY_WITNESS_ID].claim_id == "carry_dfa_factorization"
    assert witness_map[CARRY_WITNESS_ID].kind == "open-target"

    rendered = "\n".join(render_same_core_boundary_note_lines())
    assert f"`{VISIBILITY_WITNESS_ID}`" in rendered
    assert f"`{CARRY_WITNESS_ID}`" in rendered


def test_same_core_boundary_note_rejects_visibility_witness_claim_drift() -> None:
    with pytest.raises(
        ValueError,
        match=(
            "same-core boundary note expected witness "
            "same_core_threshold_shift_interval_996_over_249 to carry claim "
            "same_core_threshold_shift_interval, got small_k_visibility_threshold"
        ),
    ):
        render_same_core_boundary_note_lines(
            witnesses=_replace_witness(
                VISIBILITY_WITNESS_ID,
                claim_id="small_k_visibility_threshold",
            )
        )


def test_same_core_boundary_note_rejects_carry_witness_kind_drift() -> None:
    with pytest.raises(
        ValueError,
        match=(
            "same-core boundary note expected witness "
            "carry_dfa_factorization_target_249_498_996_same_core to have kind "
            "open-target, got theorem-witness"
        ),
    ):
        render_same_core_boundary_note_lines(
            witnesses=_replace_witness(
                CARRY_WITNESS_ID,
                kind="theorem-witness",
            )
        )
