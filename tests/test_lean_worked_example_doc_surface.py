import re
from pathlib import Path

from bridge_reptends import load_lean_worked_examples


ROOT = Path(__file__).resolve().parent.parent
EXAMPLES_SURFACE = ROOT / "lean" / "QRTour" / "Examples.lean"
PROOF_SYSTEM_LEGEND = (
    "- `Lean-formalized`: proved in the Lean tree and suitable for theorem-level citation in the current public surface.\n"
    "- `Agda-locally-proved`: discharged inside the Agda pedagogical companion surface without relying on Agda postulates.\n"
    "- `Agda-postulated but Lean-backed`: still explicit as an Agda postulate, but closed by Lean or an atlas-backed Lean-backed claim in this repo.\n"
    "- `empirical`: implemented and regression-tested here, but not promoted to theorem status.\n"
    "- `open`: tracked as an unresolved claim boundary or interface question, not an established result."
)
DECL_PATTERN = re.compile(
    r"^(?:@\[[^\n]+\]\s*)?"
    r"(?:(?:private|noncomputable|protected|partial|unsafe)\s+)*"
    r"(?:def|theorem|lemma|abbrev)\s+([A-Za-z0-9_'.]+)",
    re.MULTILINE,
)
DOC_NAME_PATTERN = re.compile(r"`(QRTour\.[A-Za-z0-9_.']+)`")
RESULT_SECTION_BOUNDS = (
    ("QRTour.Prime19", "## Prime 19 Results", "## Prime 97 Results"),
    ("QRTour.Prime97", "## Prime 97 Results", "## Composite 21 Results"),
    ("QRTour.Composite21", "## Composite 21 Results", "## Composite 249 Results"),
    ("QRTour.Composite249", "## Composite 249 Results", "## Same-Core 996 over 249 Results"),
    ("QRTour.Composite996", "## Same-Core 996 over 249 Results", None),
)


def _examples_intro() -> str:
    return EXAMPLES_SURFACE.read_text().split("namespace QRTour.Prime97", 1)[0]


def test_examples_doc_surface_carries_shared_proof_system_legend() -> None:
    intro = _examples_intro()

    assert "## Proof-System Framing" in intro
    assert "`Examples.lean` is a registry-backed worked-example surface" in intro
    assert "<!-- PROOF_SYSTEM_LEGEND_START -->" in intro
    assert PROOF_SYSTEM_LEGEND in intro


def test_examples_doc_surface_keeps_same_core_open_boundary_note() -> None:
    intro = _examples_intro()

    assert "## Same-Core Open Boundary Reminder" in intro
    assert "<!-- EXAMPLES_OPEN_BOUNDARY_NOTE_START -->" in intro
    assert "`small_k_visibility_threshold` remains `open`" in intro
    assert "`carry_dfa_factorization` remains `open`" in intro
    assert "`sameCore_firstVisibleMismatchPosition_shift_exact`" in intro
    assert "`sameCore_lookaheadCertificateHolds_iff_add_exact`" in intro
    assert "`core249_carryToRemainderFunctional_one_zero`" in intro
    assert "`actual996_carryToRemainder_conflict_two_zero`" in intro
    assert "`sameCore_carryToRemainderTransport_counterexample`" in intro
    assert "`actual996_not_carryToRemainderFunctional`" in intro
    assert "`core249_not_carryToRemainderFunctional`" in intro
    assert "do not claim a sharp minimal-lookahead or global visibility formula" in intro
    assert "explicitly refute forward same-core `carryToRemainderFunctional` transport" in intro
    assert "the exact `1/0 -> 2/0` pair" in intro
    assert "do not promote a global canonical factorization theorem" in intro


def _documented_names_by_namespace(intro: str) -> dict[str, list[str]]:
    grouped: dict[str, list[str]] = {}
    for full_name in DOC_NAME_PATTERN.findall(intro):
        namespace, theorem_name = full_name.rsplit(".", 1)
        grouped.setdefault(namespace, []).append(theorem_name)
    return grouped


def _result_sections_by_namespace(intro: str) -> dict[str, str]:
    sections: dict[str, str] = {}
    for namespace, start_heading, end_heading in RESULT_SECTION_BOUNDS:
        section = intro.split(start_heading, 1)[1]
        if end_heading is not None:
            section = section.split(end_heading, 1)[0]
        sections[namespace] = section
    return sections


def _ordered_occurrence_positions(section_names: list[str], expected_names: list[str]) -> list[int]:
    positions: list[int] = []
    start_index = 0
    for expected_name in expected_names:
        for index in range(start_index, len(section_names)):
            if section_names[index] == expected_name:
                positions.append(index)
                start_index = index + 1
                break
        else:
            raise AssertionError(
                f"missing documented theorem entry point {expected_name} in section {section_names}"
            )
    return positions


def test_examples_doc_surface_covers_registry_worked_example_entry_points() -> None:
    intro = _examples_intro()
    documented = _documented_names_by_namespace(intro)
    declarations = {match.group(1) for match in DECL_PATTERN.finditer(EXAMPLES_SURFACE.read_text())}

    for record in load_lean_worked_examples():
        assert record.namespace in documented, (
            f"{record.namespace} should appear in the Examples.lean top-level worked-example summary"
        )
        missing = [
            theorem_name
            for theorem_name in record.theorem_names
            if theorem_name not in documented[record.namespace]
        ]
        assert not missing, (
            f"{record.namespace} is missing registry theorem entry points in the "
            f"Examples.lean summary: {missing}"
        )

        unresolved = [
            theorem_name for theorem_name in record.theorem_names if theorem_name not in declarations
        ]
        assert not unresolved, (
            f"{record.namespace} registry theorem entry points do not resolve in Examples.lean: "
            f"{unresolved}"
        )

        positions = [documented[record.namespace].index(theorem_name) for theorem_name in record.theorem_names]
        assert positions == sorted(positions), (
            f"{record.namespace} should mention registry theorem entry points in registry order"
        )


def test_examples_result_sections_keep_registry_entry_points_in_namespace_order() -> None:
    intro = _examples_intro()
    sections = _result_sections_by_namespace(intro)

    assert list(sections) == [record.namespace for record in load_lean_worked_examples()]

    for record in load_lean_worked_examples():
        section_names = DOC_NAME_PATTERN.findall(sections[record.namespace])
        expected_full_names = [f"{record.namespace}.{theorem_name}" for theorem_name in record.theorem_names]

        assert section_names, f"{record.namespace} results section should document Lean entry points"
        assert all(
            full_name.startswith(f"{record.namespace}.") for full_name in section_names
        ), f"{record.namespace} results section should not mix entry points from other namespaces"

        positions = _ordered_occurrence_positions(section_names, expected_full_names)
        assert positions == sorted(positions), (
            f"{record.namespace} results section should keep registry entry points in registry order"
        )


def test_positive_q_worked_example_exports_incoming_carry_boundary_entry_points() -> None:
    records = {record.namespace: record for record in load_lean_worked_examples()}
    positive_q = records["QRTour.Composite249"]

    assert positive_q.claim_ids == (
        "positive_q_good_modes",
        "series_q_weighted_identity",
        "incoming_carry_position_formula",
        "carry_window_transducer",
    )
    assert "coordinate_positive_q_good_modes" in positive_q.theorem_names
    assert "coordinate_series_q_weighted_identity" in positive_q.theorem_names
    assert "coordinate_partialSumQ_four_eq_finite" in positive_q.theorem_names
    assert "coordinate_bodyTerm_four_eq_polynomial" in positive_q.theorem_names
    assert "coordinate_bodyTerm_five_recurrence" in positive_q.theorem_names
    assert "coordinate_firstIncomingCarryPosition" in positive_q.theorem_names
    assert "coordinate_incomingCarry_two_eq_zero" in positive_q.theorem_names
    assert "coordinate_incomingCarry_three_eq_one" in positive_q.theorem_names
    assert "coordinate_localOverflowBoundary" in positive_q.theorem_names
    assert "coordinate_lookaheadCertificate_three_zero" in positive_q.theorem_names
    assert "coordinate_visibleCarryWord_eq_emittedBlockWord_three_zero" in positive_q.theorem_names
    assert "coordinate_visibleCarryWord_three_zero_eq_blocks" in positive_q.theorem_names
    assert "coordinate_stateAlignments_output_agreement_three_zero" in positive_q.theorem_names
    assert "coordinate_stateAlignments_output_agreement_pointwise_three_zero" in positive_q.theorem_names
    assert positive_q.theorem_names.index("coordinate_positive_q_good_modes") < positive_q.theorem_names.index(
        "coordinate_series_q_weighted_identity"
    )
    assert positive_q.theorem_names.index(
        "coordinate_series_q_weighted_identity"
    ) < positive_q.theorem_names.index(
        "coordinate_partialSumQ_four_eq_finite"
    )
    assert positive_q.theorem_names.index(
        "coordinate_partialSumQ_four_eq_finite"
    ) < positive_q.theorem_names.index(
        "coordinate_bodyTerm_four_eq_polynomial"
    )
    assert positive_q.theorem_names.index("coordinate_bodyTerm_four_eq_polynomial") < positive_q.theorem_names.index(
        "coordinate_bodyTerm_five_recurrence"
    )
    assert positive_q.theorem_names.index("coordinate_bodyTerm_five_recurrence") < positive_q.theorem_names.index(
        "coordinate_firstIncomingCarryPosition"
    )
    assert positive_q.theorem_names.index("coordinate_firstIncomingCarryPosition") < positive_q.theorem_names.index(
        "coordinate_incomingCarry_two_eq_zero"
    )
    assert positive_q.theorem_names.index("coordinate_incomingCarry_two_eq_zero") < positive_q.theorem_names.index(
        "coordinate_incomingCarry_three_eq_one"
    )
    assert positive_q.theorem_names.index("coordinate_incomingCarry_three_eq_one") < positive_q.theorem_names.index(
        "coordinate_localOverflowBoundary"
    )
    assert positive_q.theorem_names.index("coordinate_localOverflowBoundary") < positive_q.theorem_names.index(
        "coordinate_lookaheadCertificate_three_zero"
    )
    assert positive_q.theorem_names.index("coordinate_lookaheadCertificate_three_zero") < positive_q.theorem_names.index(
        "coordinate_visibleCarryWord_eq_emittedBlockWord_three_zero"
    )
    assert positive_q.theorem_names.index(
        "coordinate_visibleCarryWord_eq_emittedBlockWord_three_zero"
    ) < positive_q.theorem_names.index("coordinate_visibleCarryWord_three_zero_eq_blocks")
    assert positive_q.theorem_names.index(
        "coordinate_visibleCarryWord_three_zero_eq_blocks"
    ) < positive_q.theorem_names.index("coordinate_stateAlignments_output_agreement_three_zero")
    assert positive_q.theorem_names.index(
        "coordinate_stateAlignments_output_agreement_three_zero"
    ) < positive_q.theorem_names.index("coordinate_stateAlignments_output_agreement_pointwise_three_zero")
    assert "good-mode positivity" in positive_q.current_role
    assert "q-weighted series" in positive_q.current_role
    assert "incoming-carry, and finite carry-window public statements" in positive_q.current_role
    assert "finite carry-window public statements" in positive_q.current_role
    assert "exact q-weighted series specialization" in positive_q.current_role
    assert "four-term finite partial-sum closed form" in positive_q.current_role
    assert "four-block body term" in positive_q.current_role
    assert "overflowing coefficient `1024`" in positive_q.current_role
    assert "zero carry just before that boundary" in positive_q.current_role
    assert "carry `1` at the boundary itself" in positive_q.current_role
    assert "whole-window and pointwise levels" in positive_q.current_role


def test_prime97_worked_example_exports_signed_bridge_and_block_value_entry_points() -> None:
    records = {record.namespace: record for record in load_lean_worked_examples()}
    prime97 = records["QRTour.Prime97"]

    assert prime97.claim_ids == (
        "qr_stride_classification",
        "signed_bridge_recurrence",
        "bridge_block_value_periodicity",
        "series_q_weighted_identity",
        "incoming_carry_position_formula",
        "carry_window_transducer",
    )
    assert "k_is_qr_generator" in prime97.theorem_names
    assert "signedBridge_remainder_k_step" in prime97.theorem_names
    assert "signedBridge_remainder_2k_step" in prime97.theorem_names
    assert "bridge_blockValue_eq_pow" in prime97.theorem_names
    assert "bridgeOrder_eq_forty_eight" in prime97.theorem_names
    assert "bridge_blockValue_periodic" in prime97.theorem_names
    assert "coordinate_series_q_weighted_identity" in prime97.theorem_names
    assert "coordinate_partialSumQ_four_eq_finite" in prime97.theorem_names
    assert "coordinate_bodyTerm_four_eq_polynomial" in prime97.theorem_names
    assert "coordinate_bodyTerm_five_recurrence" in prime97.theorem_names
    assert "coordinate_firstIncomingCarryPosition" in prime97.theorem_names
    assert "coordinate_isFirstIncomingCarryPosition_iff" in prime97.theorem_names
    assert "coordinate_incomingCarry_three_eq_zero" in prime97.theorem_names
    assert "coordinate_incomingCarry_four_eq_two" in prime97.theorem_names
    assert "coordinate_overflowQuotient_four_eq_zero" in prime97.theorem_names
    assert "coordinate_localOverflowBoundary" in prime97.theorem_names
    assert "coordinate_isLocalOverflowBoundary_iff" in prime97.theorem_names
    assert "coordinate_lookaheadCertificate_six_one" in prime97.theorem_names
    assert "coordinate_visibleCarryWord_eq_emittedBlockWord_six_one" in prime97.theorem_names
    assert "coordinate_lookaheadCertificate_six_three" in prime97.theorem_names
    assert "coordinate_visibleCarryWord_six_one_eq_six_three" in prime97.theorem_names
    assert "coordinate_visibleCarryWord_eq_emittedBlockWord_six_three" in prime97.theorem_names
    assert "coordinate_visibleCarryWord_six_three_eq_blocks" in prime97.theorem_names
    assert "coordinate_stateAlignments_output_agreement_six_three" in prime97.theorem_names
    assert "coordinate_stateAlignments_output_agreement_pointwise_six_three" in prime97.theorem_names
    assert prime97.theorem_names.index("k_is_qr_generator") < prime97.theorem_names.index(
        "signedBridge_remainder_k_step"
    )
    assert prime97.theorem_names.index("signedBridge_remainder_k_step") < prime97.theorem_names.index(
        "signedBridge_remainder_2k_step"
    )
    assert prime97.theorem_names.index("signedBridge_remainder_2k_step") < prime97.theorem_names.index(
        "bridge_blockValue_eq_pow"
    )
    assert prime97.theorem_names.index("bridge_blockValue_eq_pow") < prime97.theorem_names.index(
        "bridgeOrder_eq_forty_eight"
    )
    assert prime97.theorem_names.index("bridgeOrder_eq_forty_eight") < prime97.theorem_names.index(
        "bridge_blockValue_periodic"
    )
    assert prime97.theorem_names.index("bridge_blockValue_periodic") < prime97.theorem_names.index(
        "coordinate_series_q_weighted_identity"
    )
    assert prime97.theorem_names.index("coordinate_series_q_weighted_identity") < prime97.theorem_names.index(
        "coordinate_partialSumQ_four_eq_finite"
    )
    assert prime97.theorem_names.index("coordinate_partialSumQ_four_eq_finite") < prime97.theorem_names.index(
        "coordinate_bodyTerm_four_eq_polynomial"
    )
    assert prime97.theorem_names.index("coordinate_bodyTerm_four_eq_polynomial") < prime97.theorem_names.index(
        "coordinate_bodyTerm_five_recurrence"
    )
    assert prime97.theorem_names.index("coordinate_bodyTerm_five_recurrence") < prime97.theorem_names.index(
        "coordinate_firstIncomingCarryPosition"
    )
    assert prime97.theorem_names.index("coordinate_firstIncomingCarryPosition") < prime97.theorem_names.index(
        "coordinate_isFirstIncomingCarryPosition_iff"
    )
    assert prime97.theorem_names.index("coordinate_isFirstIncomingCarryPosition_iff") < prime97.theorem_names.index(
        "coordinate_incomingCarry_three_eq_zero"
    )
    assert prime97.theorem_names.index("coordinate_incomingCarry_three_eq_zero") < prime97.theorem_names.index(
        "coordinate_incomingCarry_four_eq_two"
    )
    assert prime97.theorem_names.index("coordinate_incomingCarry_four_eq_two") < prime97.theorem_names.index(
        "coordinate_overflowQuotient_four_eq_zero"
    )
    assert prime97.theorem_names.index("coordinate_overflowQuotient_four_eq_zero") < prime97.theorem_names.index(
        "coordinate_localOverflowBoundary"
    )
    assert prime97.theorem_names.index("coordinate_localOverflowBoundary") < prime97.theorem_names.index(
        "coordinate_isLocalOverflowBoundary_iff"
    )
    assert prime97.theorem_names.index("coordinate_isLocalOverflowBoundary_iff") < prime97.theorem_names.index(
        "coordinate_lookaheadCertificate_six_one"
    )
    assert prime97.theorem_names.index(
        "coordinate_lookaheadCertificate_six_one"
    ) < prime97.theorem_names.index("coordinate_visibleCarryWord_eq_emittedBlockWord_six_one")
    assert prime97.theorem_names.index(
        "coordinate_visibleCarryWord_eq_emittedBlockWord_six_one"
    ) < prime97.theorem_names.index(
        "coordinate_lookaheadCertificate_six_three"
    )
    assert prime97.theorem_names.index("coordinate_lookaheadCertificate_six_three") < prime97.theorem_names.index(
        "coordinate_visibleCarryWord_six_one_eq_six_three"
    )
    assert prime97.theorem_names.index(
        "coordinate_visibleCarryWord_six_one_eq_six_three"
    ) < prime97.theorem_names.index(
        "coordinate_visibleCarryWord_eq_emittedBlockWord_six_three"
    )
    assert prime97.theorem_names.index(
        "coordinate_visibleCarryWord_eq_emittedBlockWord_six_three"
    ) < prime97.theorem_names.index("coordinate_visibleCarryWord_six_three_eq_blocks")
    assert prime97.theorem_names.index("coordinate_visibleCarryWord_six_three_eq_blocks") < prime97.theorem_names.index(
        "coordinate_stateAlignments_output_agreement_six_three"
    )
    assert prime97.theorem_names.index(
        "coordinate_stateAlignments_output_agreement_six_three"
    ) < prime97.theorem_names.index("coordinate_stateAlignments_output_agreement_pointwise_six_three")
    assert "signed-bridge recurrence" in prime97.current_role
    assert "block-value periodicity" in prime97.current_role
    assert "minus-bridge recurrence" in prime97.current_role
    assert "block-value period `48`" in prime97.current_role
    assert "exact q-weighted series specialization" in prime97.current_role
    assert "four-term exact finite prefix identity" in prime97.current_role
    assert "four-block body term" in prime97.current_role
    assert "raw coefficients `1, 3, 9, 27`" in prime97.current_role
    assert "next raw coefficient `81`" in prime97.current_role
    assert "clean `q = 1` bridge case" in prime97.current_role
    assert "first incoming-carry boundary characterized exactly by `j = 4`" in prime97.current_role
    assert "zero carry just before that boundary" in prime97.current_role
    assert "carry `2` at the boundary itself" in prime97.current_role
    assert "pre-overflow quotient still vanishing at block `4`" in prime97.current_role
    assert "adjacent local-overflow boundary also characterized exactly by `j = 4`" in prime97.current_role
    assert "block `5` is the first raw overflow" in prime97.current_role
    assert "finite carry-window public statements" in prime97.current_role
    assert "one block of lookahead already certifies the six-block carried window" in prime97.current_role
    assert "larger `(requestedBlocks=6, lookahead=3)` witness preserves that same visible prefix" in prime97.current_role
    assert "stabilized six-block carried word `[1, 3, 9, 27, 83, 50]`" in prime97.current_role
    assert "whole-window and pointwise levels" in prime97.current_role


def test_composite21_worked_example_exports_crt_period_entry_points() -> None:
    records = {record.namespace: record for record in load_lean_worked_examples()}
    composite21 = records["QRTour.Composite21"]

    assert composite21.claim_ids == ("crt_period_lcm",)
    assert composite21.theorem_names == (
        "order_of_decimalUnitMod3",
        "order_of_decimalUnitMod7",
        "decimalUnit_order_eq_lcm_component_orders",
        "order_of_decimalUnitMod21",
    )
    assert composite21.current_role.startswith("Canonical small composite witness surface")
    assert "ord_3(base)=1" in composite21.current_role
    assert "ord_7(base)=6" in composite21.current_role
    assert "pairwise CRT least-common-multiple equation" in composite21.current_role
    assert "global decimal order to `6`" in composite21.current_role


def test_same_core_worked_example_exports_exact_shift_and_carry_agreement_entry_points() -> None:
    records = {record.namespace: record for record in load_lean_worked_examples()}
    same_core = records["QRTour.Composite996"]

    assert same_core.claim_ids == (
        "preperiod_from_base_factors",
        "same_core_threshold_shift_interval",
        "carry_window_transducer",
    )
    assert "preperiodSteps_eq_two" in same_core.theorem_names
    assert "basePrimeSupportFactor_eq_four" in same_core.theorem_names
    assert "strippedPeriodModulus_eq_249" in same_core.theorem_names
    assert "sameCore_remainderK_eq" in same_core.theorem_names
    assert "sameCore_basePrimeSupportFactor_eq_remainderK_pow_one" in same_core.theorem_names
    assert "sameCore_denominator_eq_249_mul_remainderK_pow_one" in same_core.theorem_names
    assert "sameCore_denominator_eq_249_mul_coreRemainderK_pow_one" in same_core.theorem_names
    assert "sameCore_quotientQ_scaling" in same_core.theorem_names
    assert "sameCore_quotientQ_scaling_eq_remainderK_pow_one" in same_core.theorem_names
    assert "sameCore_firstIncomingCarryPosition_shift_exact" in same_core.theorem_names
    assert "sameCore_localOverflowBoundary_shift_exact" in same_core.theorem_names
    assert "sameCore_localOverflowBoundary_via_overflowQuotient" in same_core.theorem_names
    assert "core249_firstVisibleMismatchPosition_eq_three" in same_core.theorem_names
    assert "actual996_firstVisibleMismatchPosition_eq_four" in same_core.theorem_names
    assert "sameCore_firstVisibleMismatchPosition_shift_exact" in same_core.theorem_names
    assert "sameCore_lookaheadCertificateHolds_iff_add_exact" in same_core.theorem_names
    assert "sameCore_tailMassLowerBound_iff_add_exact" in same_core.theorem_names
    assert "actual996_tailMassLowerBound_of_core_lookaheadCertificate_exact" in same_core.theorem_names
    assert "core249_tailMassLowerBound_of_actual_lookaheadCertificate_exact" in same_core.theorem_names
    assert "actual996_visibleCarryWord_eq_emittedBlockWord_of_core_lookaheadCertificate" in same_core.theorem_names
    assert "actual996_visibleCarryPairs_output_agreement_of_core_lookaheadCertificate" in same_core.theorem_names
    assert "actual996_visibleCarryPairs_output_agreement_pointwise_of_core_lookaheadCertificate" in same_core.theorem_names
    assert "actual996_visibleCarryPairs_carry_balance" in same_core.theorem_names
    assert "actual996_visibleCarryPairs_remainder_balance" in same_core.theorem_names
    assert "core249_visibleCarryWord_eq_emittedBlockWord_of_actual_lookaheadCertificate" in same_core.theorem_names
    assert "core249_visibleCarryPairs_output_agreement_of_actual_lookaheadCertificate" in same_core.theorem_names
    assert "core249_visibleCarryPairs_output_agreement_pointwise_of_actual_lookaheadCertificate" in same_core.theorem_names
    assert "core249_visibleCarryPairs_carry_balance" in same_core.theorem_names
    assert "core249_visibleCarryPairs_remainder_balance" in same_core.theorem_names
    assert "actual996_stateAlignments_output_agreement_of_core_lookaheadCertificate" in same_core.theorem_names
    assert "actual996_stateAlignments_output_agreement_pointwise_of_core_lookaheadCertificate" in same_core.theorem_names
    assert "core249_stateAlignments_output_agreement_of_actual_lookaheadCertificate" in same_core.theorem_names
    assert "core249_stateAlignments_output_agreement_pointwise_of_actual_lookaheadCertificate" in same_core.theorem_names
    assert "actual996_visibleCarryWord_eq_emittedBlockWord" in same_core.theorem_names
    assert "actual996_visibleCarryWord_four_zero_eq_blocks" in same_core.theorem_names
    assert "actual996_visibleCarryPairs_output_agreement" in same_core.theorem_names
    assert "actual996_visibleCarryPairs_output_agreement_pointwise" in same_core.theorem_names
    assert "actual996_stateAlignments_output_agreement" in same_core.theorem_names
    assert "actual996_stateAlignments_output_agreement_pointwise" in same_core.theorem_names
    assert "actual996_stateAlignments_coefficient_shift_exact" in same_core.theorem_names
    assert "actual996_stateAlignments_carryIn_shift_exact" in same_core.theorem_names
    assert "actual996_stateAlignments_carryOut_shift_exact" in same_core.theorem_names
    assert "actual996_stateAlignments_remainderIn_shift_exact" in same_core.theorem_names
    assert "actual996_stateAlignments_carryBlockValue_shift_exact" in same_core.theorem_names
    assert "actual996_stateAlignments_remainderBlockValue_shift_exact" in same_core.theorem_names
    assert "actual996_stateAlignments_remainderOut_shift_exact" in same_core.theorem_names
    assert "core249_visibleCarryWord_eq_emittedBlockWord" in same_core.theorem_names
    assert "core249_visibleCarryWord_three_zero_eq_blocks" in same_core.theorem_names
    assert "sameCore_visibleCarryWord_shift_exact" in same_core.theorem_names
    assert "core249_visibleCarryPairs_output_agreement" in same_core.theorem_names
    assert "core249_visibleCarryPairs_output_agreement_pointwise" in same_core.theorem_names
    assert "core249_stateAlignments_output_agreement" in same_core.theorem_names
    assert "core249_stateAlignments_output_agreement_pointwise" in same_core.theorem_names
    assert "actual996_stateAlignments_remainderToCarryStepFunctional" in same_core.theorem_names
    assert "core249_carryToRemainderFunctional_one_zero" in same_core.theorem_names
    assert "actual996_carryToRemainder_conflict_two_zero" in same_core.theorem_names
    assert "sameCore_carryToRemainderTransport_counterexample" in same_core.theorem_names
    assert "actual996_not_carryToRemainderFunctional" in same_core.theorem_names
    assert "actual996_stateAlignments_remainderToCarry_transition_compatible" in same_core.theorem_names
    assert "actual996_quotientOnly_profile" in same_core.theorem_names
    assert "core249_remainderToCarryFunctional" in same_core.theorem_names
    assert "core249_stateAlignments_remainderToCarry_transition_compatible" in same_core.theorem_names
    assert "core249_not_carryToRemainderFunctional" in same_core.theorem_names
    assert same_core.theorem_names.index("preperiodSteps_eq_two") < same_core.theorem_names.index(
        "basePrimeSupportFactor_eq_four"
    )
    assert same_core.theorem_names.index("basePrimeSupportFactor_eq_four") < same_core.theorem_names.index(
        "strippedPeriodModulus_eq_249"
    )
    assert same_core.theorem_names.index("strippedPeriodModulus_eq_249") < same_core.theorem_names.index(
        "sameCore_remainderK_eq"
    )
    assert same_core.theorem_names.index("sameCore_remainderK_eq") < same_core.theorem_names.index(
        "sameCore_basePrimeSupportFactor_eq_remainderK_pow_one"
    )
    assert same_core.theorem_names.index(
        "sameCore_basePrimeSupportFactor_eq_remainderK_pow_one"
    ) < same_core.theorem_names.index(
        "sameCore_denominator_eq_249_mul_remainderK_pow_one"
    )
    assert same_core.theorem_names.index(
        "sameCore_denominator_eq_249_mul_remainderK_pow_one"
    ) < same_core.theorem_names.index(
        "sameCore_denominator_eq_249_mul_coreRemainderK_pow_one"
    )
    assert same_core.theorem_names.index(
        "sameCore_denominator_eq_249_mul_coreRemainderK_pow_one"
    ) < same_core.theorem_names.index(
        "sameCore_quotientQ_scaling"
    )
    assert same_core.theorem_names.index("sameCore_quotientQ_scaling") < same_core.theorem_names.index(
        "sameCore_quotientQ_scaling_eq_remainderK_pow_one"
    )
    assert same_core.theorem_names.index("sameCore_quotientQ_scaling_eq_remainderK_pow_one") < same_core.theorem_names.index(
        "sameCore_firstIncomingCarryPosition_shift_exact"
    )
    assert same_core.theorem_names.index("sameCore_firstIncomingCarryPosition_shift_exact") < same_core.theorem_names.index(
        "sameCore_localOverflowBoundary_shift_exact"
    )
    assert same_core.theorem_names.index("sameCore_localOverflowBoundary_shift_exact") < same_core.theorem_names.index(
        "sameCore_localOverflowBoundary_via_overflowQuotient"
    )
    assert same_core.theorem_names.index(
        "sameCore_localOverflowBoundary_via_overflowQuotient"
    ) < same_core.theorem_names.index(
        "core249_firstVisibleMismatchPosition_eq_three"
    )
    assert same_core.theorem_names.index("core249_firstVisibleMismatchPosition_eq_three") < same_core.theorem_names.index(
        "actual996_firstVisibleMismatchPosition_eq_four"
    )
    assert same_core.theorem_names.index("actual996_firstVisibleMismatchPosition_eq_four") < same_core.theorem_names.index(
        "sameCore_firstVisibleMismatchPosition_shift_exact"
    )
    assert same_core.theorem_names.index("sameCore_firstVisibleMismatchPosition_shift_exact") < same_core.theorem_names.index(
        "sameCore_lookaheadCertificateHolds_iff_add_exact"
    )
    assert same_core.theorem_names.index("sameCore_lookaheadCertificateHolds_iff_add_exact") < same_core.theorem_names.index(
        "sameCore_tailMassLowerBound_iff_add_exact"
    )
    assert same_core.theorem_names.index(
        "sameCore_tailMassLowerBound_iff_add_exact"
    ) < same_core.theorem_names.index(
        "actual996_tailMassLowerBound_of_core_lookaheadCertificate_exact"
    )
    assert same_core.theorem_names.index(
        "actual996_tailMassLowerBound_of_core_lookaheadCertificate_exact"
    ) < same_core.theorem_names.index(
        "core249_tailMassLowerBound_of_actual_lookaheadCertificate_exact"
    )
    assert same_core.theorem_names.index(
        "core249_tailMassLowerBound_of_actual_lookaheadCertificate_exact"
    ) < same_core.theorem_names.index(
        "actual996_visibleCarryWord_eq_emittedBlockWord_of_core_lookaheadCertificate"
    )
    assert same_core.theorem_names.index(
        "actual996_visibleCarryWord_eq_emittedBlockWord_of_core_lookaheadCertificate"
    ) < same_core.theorem_names.index(
        "actual996_visibleCarryPairs_output_agreement_of_core_lookaheadCertificate"
    )
    assert same_core.theorem_names.index(
        "actual996_visibleCarryPairs_output_agreement_of_core_lookaheadCertificate"
    ) < same_core.theorem_names.index(
        "actual996_visibleCarryPairs_output_agreement_pointwise_of_core_lookaheadCertificate"
    )
    assert same_core.theorem_names.index(
        "actual996_visibleCarryPairs_output_agreement_pointwise_of_core_lookaheadCertificate"
    ) < same_core.theorem_names.index(
        "actual996_visibleCarryPairs_carry_balance"
    )
    assert same_core.theorem_names.index(
        "actual996_visibleCarryPairs_carry_balance"
    ) < same_core.theorem_names.index(
        "actual996_visibleCarryPairs_remainder_balance"
    )
    assert same_core.theorem_names.index(
        "actual996_visibleCarryPairs_remainder_balance"
    ) < same_core.theorem_names.index(
        "core249_visibleCarryWord_eq_emittedBlockWord_of_actual_lookaheadCertificate"
    )
    assert same_core.theorem_names.index(
        "core249_visibleCarryWord_eq_emittedBlockWord_of_actual_lookaheadCertificate"
    ) < same_core.theorem_names.index(
        "core249_visibleCarryPairs_output_agreement_of_actual_lookaheadCertificate"
    )
    assert same_core.theorem_names.index(
        "core249_visibleCarryPairs_output_agreement_of_actual_lookaheadCertificate"
    ) < same_core.theorem_names.index(
        "core249_visibleCarryPairs_output_agreement_pointwise_of_actual_lookaheadCertificate"
    )
    assert same_core.theorem_names.index(
        "core249_visibleCarryPairs_output_agreement_pointwise_of_actual_lookaheadCertificate"
    ) < same_core.theorem_names.index(
        "core249_visibleCarryPairs_carry_balance"
    )
    assert same_core.theorem_names.index(
        "core249_visibleCarryPairs_carry_balance"
    ) < same_core.theorem_names.index(
        "core249_visibleCarryPairs_remainder_balance"
    )
    assert same_core.theorem_names.index(
        "core249_visibleCarryPairs_remainder_balance"
    ) < same_core.theorem_names.index(
        "actual996_stateAlignments_output_agreement_of_core_lookaheadCertificate"
    )
    assert same_core.theorem_names.index(
        "actual996_stateAlignments_output_agreement_of_core_lookaheadCertificate"
    ) < same_core.theorem_names.index(
        "actual996_stateAlignments_output_agreement_pointwise_of_core_lookaheadCertificate"
    )
    assert same_core.theorem_names.index(
        "actual996_stateAlignments_output_agreement_pointwise_of_core_lookaheadCertificate"
    ) < same_core.theorem_names.index(
        "core249_stateAlignments_output_agreement_of_actual_lookaheadCertificate"
    )
    assert same_core.theorem_names.index(
        "core249_stateAlignments_output_agreement_of_actual_lookaheadCertificate"
    ) < same_core.theorem_names.index(
        "core249_stateAlignments_output_agreement_pointwise_of_actual_lookaheadCertificate"
    )
    assert same_core.theorem_names.index(
        "core249_stateAlignments_output_agreement_pointwise_of_actual_lookaheadCertificate"
    ) < same_core.theorem_names.index(
        "actual996_visibleCarryWord_eq_emittedBlockWord"
    )
    assert same_core.theorem_names.index("actual996_visibleCarryWord_eq_emittedBlockWord") < same_core.theorem_names.index(
        "actual996_visibleCarryWord_four_zero_eq_blocks"
    )
    assert same_core.theorem_names.index("actual996_visibleCarryWord_four_zero_eq_blocks") < same_core.theorem_names.index(
        "actual996_visibleCarryPairs_output_agreement"
    )
    assert same_core.theorem_names.index("actual996_visibleCarryPairs_output_agreement") < same_core.theorem_names.index(
        "actual996_visibleCarryPairs_output_agreement_pointwise"
    )
    assert same_core.theorem_names.index("actual996_visibleCarryPairs_output_agreement_pointwise") < same_core.theorem_names.index(
        "actual996_stateAlignments_output_agreement"
    )
    assert same_core.theorem_names.index("actual996_stateAlignments_output_agreement") < same_core.theorem_names.index(
        "actual996_stateAlignments_output_agreement_pointwise"
    )
    assert same_core.theorem_names.index("actual996_stateAlignments_output_agreement_pointwise") < same_core.theorem_names.index(
        "actual996_stateAlignments_coefficient_shift_exact"
    )
    assert same_core.theorem_names.index("actual996_stateAlignments_coefficient_shift_exact") < same_core.theorem_names.index(
        "actual996_stateAlignments_carryIn_shift_exact"
    )
    assert same_core.theorem_names.index("actual996_stateAlignments_carryIn_shift_exact") < same_core.theorem_names.index(
        "actual996_stateAlignments_carryOut_shift_exact"
    )
    assert same_core.theorem_names.index("actual996_stateAlignments_carryOut_shift_exact") < same_core.theorem_names.index(
        "actual996_stateAlignments_remainderIn_shift_exact"
    )
    assert same_core.theorem_names.index("actual996_stateAlignments_remainderIn_shift_exact") < same_core.theorem_names.index(
        "actual996_stateAlignments_carryBlockValue_shift_exact"
    )
    assert same_core.theorem_names.index("actual996_stateAlignments_carryBlockValue_shift_exact") < same_core.theorem_names.index(
        "actual996_stateAlignments_remainderBlockValue_shift_exact"
    )
    assert same_core.theorem_names.index("actual996_stateAlignments_remainderBlockValue_shift_exact") < same_core.theorem_names.index(
        "actual996_stateAlignments_remainderOut_shift_exact"
    )
    assert same_core.theorem_names.index("actual996_stateAlignments_remainderOut_shift_exact") < same_core.theorem_names.index(
        "core249_visibleCarryWord_eq_emittedBlockWord"
    )
    assert same_core.theorem_names.index("core249_visibleCarryWord_eq_emittedBlockWord") < same_core.theorem_names.index(
        "core249_visibleCarryWord_three_zero_eq_blocks"
    )
    assert same_core.theorem_names.index("core249_visibleCarryWord_three_zero_eq_blocks") < same_core.theorem_names.index(
        "sameCore_visibleCarryWord_shift_exact"
    )
    assert same_core.theorem_names.index("sameCore_visibleCarryWord_shift_exact") < same_core.theorem_names.index(
        "core249_visibleCarryPairs_output_agreement"
    )
    assert same_core.theorem_names.index("core249_visibleCarryPairs_output_agreement") < same_core.theorem_names.index(
        "core249_visibleCarryPairs_output_agreement_pointwise"
    )
    assert same_core.theorem_names.index("core249_visibleCarryPairs_output_agreement_pointwise") < same_core.theorem_names.index(
        "core249_stateAlignments_output_agreement"
    )
    assert same_core.theorem_names.index("core249_stateAlignments_output_agreement") < same_core.theorem_names.index(
        "core249_stateAlignments_output_agreement_pointwise"
    )
    assert same_core.theorem_names.index("core249_stateAlignments_output_agreement_pointwise") < same_core.theorem_names.index(
        "actual996_stateAlignments_remainderToCarryStepFunctional"
    )
    assert same_core.theorem_names.index("actual996_stateAlignments_remainderToCarryStepFunctional") < same_core.theorem_names.index(
        "core249_carryToRemainderFunctional_one_zero"
    )
    assert same_core.theorem_names.index("core249_carryToRemainderFunctional_one_zero") < same_core.theorem_names.index(
        "actual996_carryToRemainder_conflict_two_zero"
    )
    assert same_core.theorem_names.index("actual996_carryToRemainder_conflict_two_zero") < same_core.theorem_names.index(
        "sameCore_carryToRemainderTransport_counterexample"
    )
    assert same_core.theorem_names.index("sameCore_carryToRemainderTransport_counterexample") < same_core.theorem_names.index(
        "actual996_not_carryToRemainderFunctional"
    )
    assert same_core.theorem_names.index("actual996_not_carryToRemainderFunctional") < same_core.theorem_names.index(
        "actual996_stateAlignments_remainderToCarry_transition_compatible"
    )
    assert same_core.theorem_names.index("actual996_stateAlignments_remainderToCarry_transition_compatible") < same_core.theorem_names.index(
        "actual996_quotientOnly_profile"
    )
    assert same_core.theorem_names.index("actual996_quotientOnly_profile") < same_core.theorem_names.index(
        "core249_remainderToCarryFunctional"
    )
    assert same_core.theorem_names.index("core249_remainderToCarryFunctional") < same_core.theorem_names.index(
        "core249_stateAlignments_remainderToCarry_transition_compatible"
    )
    assert same_core.theorem_names.index(
        "core249_stateAlignments_remainderToCarry_transition_compatible"
    ) < same_core.theorem_names.index(
        "core249_not_carryToRemainderFunctional"
    )
    assert "first incoming-carry" in same_core.current_role
    assert "base-prime support factor identity `basePrimeSupportFactor 10 996 = 4`" in same_core.current_role
    assert "product decomposition `996 = 4 * 249`" in same_core.current_role
    assert "stripped periodic core identity `strippedPeriodModulus 10 996 = 249`" in same_core.current_role
    assert "shared remainder identity `k_core = k_actual = 4`" in same_core.current_role
    assert "exact `k^1` specialization `basePrimeSupportFactor 10 996 = k_actual^1 = k_core^1`" in same_core.current_role
    assert "exact same-core denominator identity `996 = 249 * k^1`" in same_core.current_role
    assert "`996 = 249 * k_actual^1`" in same_core.current_role
    assert "`996 = 249 * k_core^1`" in same_core.current_role
    assert "`q_core = q_actual * 4`" in same_core.current_role
    assert "`q_core = q_actual * k^1`" in same_core.current_role
    assert "quotient-scaling identities `q_core = q_actual * 4` and `q_core = q_actual * k^1`" in same_core.current_role
    assert "local-overflow" in same_core.current_role
    assert "overflow-quotient view of the same-core local-overflow boundary" in same_core.current_role
    assert "first visible-mismatch" in same_core.current_role
    assert "first visible-mismatch positions made explicit as `3` and `4`" in same_core.current_role
    assert "lookahead-certificate transport" in same_core.current_role
    assert "exact raw tail-mass lower-bound equivalence" in same_core.current_role
    assert "tail-mass lower-bound implications" in same_core.current_role
    assert "forward and reverse exact-certificate visible-word, pair-output, and aligned-output implications" in same_core.current_role
    assert "pair-output and aligned-output layers exposed at both whole-window and pointwise levels" in same_core.current_role
    assert "pointwise pair-balance arithmetic on both canonical windows" in same_core.current_role
    assert "canonical `3/0 -> 4/0` window pair" in same_core.current_role
    assert "forward visible carry, pair-output, and state-output agreement" in same_core.current_role
    assert "concrete stabilized visible word `[1, 4, 16, 64]`" in same_core.current_role
    assert "concrete stripped-core visible word `[4, 16, 64]`" in same_core.current_role
    assert "exact one-block visible-word shift `[1, 4, 16, 64] = 1 :: [4, 16, 64]`" in same_core.current_role
    assert "coarse whole-window and pointwise pair-output and state-alignment wrappers" in same_core.current_role
    assert (
        "exact one-block same-core shift of aligned raw coefficients, carry states, carried block values, carry outputs, "
        "remainder inputs, remainder block values, and next-step remainder states"
    ) in same_core.current_role
    assert "reverse visible, pair-output, and state-output agreement" in same_core.current_role
    assert "transported remainder-to-carry functionality" in same_core.current_role
    assert "reverse transition compatibility" in same_core.current_role
    assert "stripped-core carry-to-remainder failure" in same_core.current_role
    assert "stripped-core `1/0` carry-to-remainder functional witness" in same_core.current_role
    assert "shifted-actual `2/0` carry-to-remainder conflict" in same_core.current_role
    assert "one-block `1/0 -> 2/0` counterexample to forward same-core carry-to-remainder transport" in same_core.current_role
    assert "transition compatibility" in same_core.current_role
    assert "quotient-only profile" in same_core.current_role
