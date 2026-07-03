from bridge_reptends import (
    load_claim_registry,
    load_lean_worked_examples,
    load_theorem_witnesses,
    render_same_core_boundary_note_lines,
    render_theorem_witness_table_lines,
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


def test_same_core_visibility_context_matches_exact_and_open_boundary_witnesses() -> None:
    context = claim_context_for_parameters(
        ("same_core_threshold_shift_interval", "small_k_visibility_threshold"),
        base=10,
        actual=996,
        core=249,
        requested_blocks=8,
    )

    assert context["related_open_claim_ids"] == ["small_k_visibility_threshold"]
    assert context["matching_claim_ids"] == [
        "same_core_threshold_shift_interval",
        "small_k_visibility_threshold",
    ]
    assert context["matching_witness_ids"] == [
        "same_core_threshold_shift_interval_996_over_249",
        "small_k_visibility_threshold_target_97_249_996",
    ]


def test_carry_context_matches_exact_and_open_same_core_witnesses() -> None:
    context = claim_context_for_parameters(
        ("carry_window_transducer", "carry_dfa_factorization"),
        base=10,
        n=996,
    )

    assert context["related_open_claim_ids"] == ["carry_dfa_factorization"]
    assert context["matching_claim_ids"] == [
        "carry_dfa_factorization",
        "carry_window_transducer",
    ]
    assert "carry_dfa_factorization_target_21_97_996" in context["matching_witness_ids"]
    assert "carry_dfa_factorization_target_249_498_996_same_core" in context["matching_witness_ids"]
    assert "carry_window_transducer_same_core_996_window4" in context["matching_witness_ids"]


def test_positive_q_incoming_carry_context_matches_composite249_witnesses() -> None:
    context = claim_context_for_parameters(
        ("positive_q_good_modes", "incoming_carry_position_formula"),
        base=10,
        n=249,
    )

    assert context["matching_claim_ids"] == [
        "incoming_carry_position_formula",
        "positive_q_good_modes",
    ]
    assert context["matching_witness_ids"] == [
        "positive_q_good_modes_n249_stride3",
        "incoming_carry_position_formula_n249_stride3",
    ]


def test_positive_q_series_context_matches_composite249_witness() -> None:
    context = claim_context_for_parameters(
        ("series_q_weighted_identity",),
        base=10,
        n=249,
    )

    assert context["matching_claim_ids"] == ["series_q_weighted_identity"]
    assert context["matching_witness_ids"] == ["series_q_weighted_identity_n249_stride3"]


def test_positive_q_carry_context_matches_composite249_window_witness() -> None:
    context = claim_context_for_parameters(
        ("carry_window_transducer",),
        base=10,
        n=249,
        requested_blocks=3,
    )

    assert context["related_claim_ids"] == ["carry_window_transducer"]
    assert context["related_open_claim_ids"] == []
    assert context["matching_claim_ids"] == ["carry_window_transducer"]
    assert context["matching_witness_ids"] == ["carry_window_transducer_n249_window3"]


def test_digit_periodicity_context_matches_prime19_worked_example_witness() -> None:
    context = claim_context_for_parameters(
        ("digit_periodicity",),
        base=10,
        n=19,
    )

    assert context["matching_claim_ids"] == ["digit_periodicity"]
    assert context["matching_witness_ids"] == ["digit_periodicity_prime19_base10"]


def test_same_core_boundary_note_separates_visibility_transport_from_carry_failure() -> None:
    rendered = "\n".join(render_same_core_boundary_note_lines())

    assert "same_core_threshold_shift_interval_996_over_249" in rendered
    assert "carry_dfa_factorization_target_249_498_996_same_core" in rendered
    assert "same_core_threshold_shift_interval" in rendered
    assert "carry_dfa_factorization" in rendered
    assert "forward exact same-core carry-to-remainder transport fails" in rendered
    assert "one-block `1/0` window" in rendered
    assert "forward same-core `carryToRemainderFunctional` transport outside the current Lean claim surface" in rendered


def test_theorem_witness_table_includes_linked_lean_example_namespaces() -> None:
    rows = {}
    rendered_rows = render_theorem_witness_table_lines()

    assert rendered_rows[0] == (
        "| Witness ID | Claim ID | Claim Status | Kind | Canonical tuple or family | "
        "Why this witness | Lean example namespace(s) | Repo Evidence |"
    )

    for line in rendered_rows[2:]:
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        witness_id = cells[0].strip("`")
        rows[witness_id] = cells

    namespaces_by_witness_id: dict[str, list[str]] = {}
    for record in load_lean_worked_examples():
        for witness_id in record.witness_ids:
            namespaces_by_witness_id.setdefault(witness_id, []).append(record.namespace)

    for witness in load_theorem_witnesses():
        namespace_cell = rows[witness.id][6]
        expected_namespaces = namespaces_by_witness_id.get(witness.id, [])
        if expected_namespaces:
            assert "[QRTour/Examples.lean]" in namespace_cell
            for namespace in expected_namespaces:
                assert f"`{namespace}`" in namespace_cell
        else:
            assert namespace_cell == "-"
