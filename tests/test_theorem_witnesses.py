from bridge_reptends import (
    load_claim_registry,
    load_theorem_witnesses,
    theorem_witnesses_by_claim,
)


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
