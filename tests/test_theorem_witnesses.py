from bridge_reptends import (
    load_claim_registry,
    load_theorem_witnesses,
    render_same_core_boundary_note_lines,
    theorem_witnesses_by_claim,
)
from bridge_reptends.registry import claim_context_for_parameters


def test_every_claim_has_at_least_one_named_witness() -> None:
    claims = load_claim_registry()
    witnesses = theorem_witnesses_by_claim()

    for claim in claims:
        assert claim.id in witnesses, f"missing theorem witness for claim {claim.id}"


def test_witness_kinds_match_claim_status_boundaries() -> None:
    claims = {claim.id: claim for claim in load_claim_registry()}
    witnesses = load_theorem_witnesses()

    for witness in witnesses:
        status = claims[witness.claim_id].status
        if status == "open":
            assert witness.kind == "open-target"
        elif status == "empirical":
            assert witness.kind == "empirical-witness"
        else:
            assert witness.kind == "theorem-witness"


def test_open_claims_have_named_target_families() -> None:
    claims = {claim.id: claim for claim in load_claim_registry()}
    witnesses = theorem_witnesses_by_claim()

    for claim_id, claim in claims.items():
        if claim.status != "open":
            continue
        claim_witnesses = witnesses[claim_id]
        assert any(witness.kind == "open-target" for witness in claim_witnesses)
        assert any("family" in witness.tuple_display.lower() or "{" in witness.tuple_display for witness in claim_witnesses)


def test_same_core_carry_open_target_matches_actual_core_context() -> None:
    context = claim_context_for_parameters(
        ("carry_dfa_factorization",),
        base=10,
        actual=996,
        core=249,
        requested_blocks=8,
    )

    assert context["related_open_claim_ids"] == ["carry_dfa_factorization"]
    assert "carry_dfa_factorization_target_249_498_996_same_core" in context["matching_witness_ids"]


def test_same_core_boundary_note_separates_visibility_transport_from_carry_failure() -> None:
    rendered = "\n".join(render_same_core_boundary_note_lines())

    assert "same_core_threshold_shift_interval_996_over_249" in rendered
    assert "carry_dfa_factorization_target_249_498_996_same_core" in rendered
    assert "same_core_threshold_shift_interval" in rendered
    assert "carry_dfa_factorization" in rendered
    assert "`carryToRemainderFunctional` transport is not currently claimed" in rendered
