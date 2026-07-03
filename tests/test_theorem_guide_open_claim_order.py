import re
from pathlib import Path

from bridge_reptends import load_claim_registry, load_lean_open_claim_boundaries


ROOT = Path(__file__).resolve().parent.parent
LEAN_GUIDE = ROOT / "lean" / "THEOREM_GUIDE.md"


def _extract_markdown_table_rows(text: str, heading: str) -> list[list[str]]:
    lines = text.splitlines()
    start = lines.index(heading) + 1
    while start < len(lines) and not lines[start].startswith("|"):
        start += 1

    table_lines: list[str] = []
    while start < len(lines) and lines[start].startswith("|"):
        table_lines.append(lines[start])
        start += 1

    return [
        [cell.strip() for cell in row.strip().strip("|").split("|")]
        for row in table_lines[2:]
    ]


def _extract_theorem_guide_support_order() -> dict[str, list[str]]:
    theorem_guide_text = LEAN_GUIDE.read_text()
    modules_by_claim: dict[str, list[str]] = {}
    for claim_id_cell, module_cell, _theorems, _role in _extract_markdown_table_rows(
        theorem_guide_text, "## Open-Claim Lean Support Crosswalk"
    ):
        claim_id = claim_id_cell.strip("`")
        matches = re.findall(r"\]\(([^)]+)\)", module_cell)
        assert len(matches) == 1, f"{claim_id} should list exactly one Lean module per support row"
        target = matches[0]
        relative = target.split("quadratic-residue-reptends/", 1)[1]
        modules_by_claim.setdefault(claim_id, []).append(relative)
    return modules_by_claim


def _extract_theorem_guide_support_rows() -> list[tuple[str, str, str, str]]:
    theorem_guide_text = LEAN_GUIDE.read_text()
    rows: list[tuple[str, str, str, str]] = []
    for claim_id_cell, module_cell, theorem_cell, role_cell in _extract_markdown_table_rows(
        theorem_guide_text, "## Open-Claim Lean Support Crosswalk"
    ):
        claim_id = claim_id_cell.strip("`")
        matches = re.findall(r"\]\(([^)]+)\)", module_cell)
        assert len(matches) == 1, f"{claim_id} should list exactly one Lean module per support row"
        relative = matches[0].split("quadratic-residue-reptends/", 1)[1]
        rows.append((claim_id, relative, theorem_cell, role_cell))
    return rows


def test_open_claim_support_order_matches_boundary_registry() -> None:
    support_order_by_claim = _extract_theorem_guide_support_order()
    boundary_order_by_claim = {
        record.claim_id: [path for segment in record.segments for path in segment.module_paths]
        for record in load_lean_open_claim_boundaries()
    }

    assert support_order_by_claim == boundary_order_by_claim


def test_open_claim_registry_support_order_matches_boundary_registry() -> None:
    boundary_order_by_claim = {
        record.claim_id: [path for segment in record.segments for path in segment.module_paths]
        for record in load_lean_open_claim_boundaries()
    }

    registry_order_by_claim = {
        claim.id: [item.module for item in claim.lean_support_items]
        for claim in load_claim_registry()
        if claim.status == "open"
    }

    assert registry_order_by_claim == boundary_order_by_claim


def test_small_k_visibility_support_crosswalk_lists_pointwise_same_core_wrappers() -> None:
    claim = next(
        claim
        for claim in load_claim_registry()
        if claim.id == "small_k_visibility_threshold"
    )
    item = next(
        item
        for item in claim.lean_support_items
        if item.module == "lean/QRTour/CarryComparison.lean"
    )

    assert item.theorems == (
        "actualCoordinate_visibleCarryWord_eq_emittedBlockWord_of_core_lookaheadCertificate_add_exact",
        "actualCoordinate_visibleCarryWord_eq_emittedBlockWord_of_core_remainderKPow_lt_modulus_add",
        "strippedCoordinate_visibleCarryWord_eq_emittedBlockWord_of_actual_lookaheadCertificate_add_exact",
        "strippedCoordinate_visibleCarryWord_eq_emittedBlockWord_of_actual_remainderKPow_lt_modulus_add",
        "actualCoordinate_visibleCarryPairs_output_agreement_pointwise_of_core_lookaheadCertificate_add_exact",
        "strippedCoordinate_visibleCarryPairs_output_agreement_pointwise_of_actual_lookaheadCertificate_add_exact",
        "actualCoordinate_stateAlignments_output_agreement_pointwise_of_core_lookaheadCertificate_add_exact",
        "strippedCoordinate_stateAlignments_output_agreement_pointwise_of_actual_lookaheadCertificate_add_exact",
    )
    assert "whole-window and pointwise levels" in item.role
    assert "lookahead certificate" in item.role
    assert "coarse shifted `k^(n+L) < modulus` visible-word corollaries" in item.role

    row = next(
        row
        for row in _extract_theorem_guide_support_rows()
        if row[0] == "small_k_visibility_threshold"
        and row[1] == "lean/QRTour/CarryComparison.lean"
    )
    theorem_cell = row[2]
    role_cell = row[3]

    for theorem_name in item.theorems:
        assert f"`{theorem_name}`" in theorem_cell
    assert "whole-window and pointwise levels" in role_cell
    assert "lookahead certificate" in role_cell
    assert "coarse shifted `k^(n+L) < modulus` visible-word corollaries" in role_cell


def test_small_k_visibility_support_crosswalk_lists_exact_tail_mass_implications() -> None:
    claim = next(
        claim
        for claim in load_claim_registry()
        if claim.id == "small_k_visibility_threshold"
    )
    item = next(
        item
        for item in claim.lean_support_items
        if item.module == "lean/QRTour/CompositeVisibility.lean"
    )

    assert item.theorems == (
        "sameCoreCompatible_firstVisibleMismatchPosition_shift_exact",
        "sameCoreCompatible_lookaheadCertificateHolds_iff_add_exact",
        "sameCoreCompatible_lookaheadCertificateHolds_of_core_remainderKPow_lt_modulus_add",
        "sameCoreCompatible_stripped_lookaheadCertificateHolds_of_actual_remainderKPow_lt_modulus_add",
        "sameCoreCompatible_tailMassLowerBound_iff_add_exact",
        "sameCoreCompatible_tailMassLowerBound_of_core_lookaheadCertificate_add_exact",
        "sameCoreCompatible_tailMassLowerBound_of_actual_lookaheadCertificate_add_exact",
    )
    assert "paired forward and reverse exact-certificate tail-mass implications" in item.role
    assert "raw tail-mass inequality" in item.role

    row = next(
        row
        for row in _extract_theorem_guide_support_rows()
        if row[0] == "small_k_visibility_threshold"
        and row[1] == "lean/QRTour/CompositeVisibility.lean"
    )
    theorem_cell = row[2]
    role_cell = row[3]

    for theorem_name in item.theorems:
        assert f"`{theorem_name}`" in theorem_cell
    assert "paired forward and reverse exact-certificate tail-mass implications" in role_cell
    assert "raw tail-mass inequality" in role_cell


def test_carry_dfa_support_crosswalk_lists_both_coarse_step_functional_wrappers() -> None:
    claim = next(
        claim
        for claim in load_claim_registry()
        if claim.id == "carry_dfa_factorization"
    )
    item = next(
        item
        for item in claim.lean_support_items
        if item.module == "lean/QRTour/CarryComparison.lean"
    )

    assert item.theorems == (
        "BlockCoordinate.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate",
        "BlockCoordinate.stateAlignments_remainderToCarryStepFunctional_of_functional_and_remainderK_pow_lt_modulus",
        "BlockCoordinate.stateAlignments_carryToRemainderStepFunctional_of_functional_and_remainderK_pow_lt_modulus",
        "actualCoordinate_stateAlignments_remainderToCarry_transition_compatible_of_core_remainderKPow_lt_modulus_add",
        "strippedCoordinate_stateAlignments_remainderToCarry_transition_compatible_of_actual_remainderKPow_lt_modulus_add",
        "actualCoordinate_stateAlignments_carryToRemainder_transition_compatible_of_core_remainderKPow_lt_modulus_add",
        "strippedCoordinate_stateAlignments_carryToRemainder_transition_compatible_of_actual_remainderKPow_lt_modulus_add",
        "BlockCoordinate.not_remainderToCarryFunctional_of_conflict",
        "BlockCoordinate.not_carryToRemainderFunctional_of_conflict",
        "composite996_sameCore_carryToRemainderTransport_counterexample",
    )
    assert "remainder-to-carry and carry-to-remainder step-functional" in item.role
    assert "forward same-core carry-to-remainder transport counterexample" in item.role

    row = next(
        row
        for row in _extract_theorem_guide_support_rows()
        if row[0] == "carry_dfa_factorization"
        and row[1] == "lean/QRTour/CarryComparison.lean"
    )
    theorem_cell = row[2]
    role_cell = row[3]

    for theorem_name in item.theorems:
        assert f"`{theorem_name}`" in theorem_cell
    assert "remainder-to-carry and carry-to-remainder step-functional" in role_cell
    assert "forward same-core carry-to-remainder transport counterexample" in role_cell
