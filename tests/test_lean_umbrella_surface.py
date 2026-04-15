import re
from pathlib import Path

from bridge_reptends.registry import (
    render_proof_system_legend_lines,
    render_qr_tour_module_lines,
    render_qr_tour_open_boundary_lines,
    render_qr_tour_theorem_surface_lines,
)


ROOT = Path(__file__).resolve().parent.parent
QRT_SURFACE = ROOT / "lean" / "QRTour.lean"
EXAMPLES_SURFACE = ROOT / "lean" / "QRTour" / "Examples.lean"
EXAMPLE_DECL_PATTERN = re.compile(
    r"^(?:@\[[^\n]+\]\s*)?"
    r"(?:(?:private|noncomputable|protected|partial|unsafe)\s+)*"
    r"(?:def|theorem|lemma|abbrev)\s+([A-Za-z0-9_'.]+)",
    re.MULTILINE,
)


def _section(text: str, start_heading: str, end_heading: str) -> str:
    return text.split(start_heading, 1)[1].split(end_heading, 1)[0]


def _marked_block(text: str, start_marker: str, end_marker: str) -> str:
    return text.split(start_marker, 1)[1].split(end_marker, 1)[0].strip()


def test_qr_tour_umbrella_classifies_carry_surface_honestly() -> None:
    text = QRT_SURFACE.read_text()
    theorem_surface = _section(text, "## Current Theorem Surface", "## Exact/Open Boundary")
    boundary = _section(text, "## Exact/Open Boundary", "## Example: p = 97, base = 10, m = 2, B = 100")

    assert "`QRTour.CarryTransducer` together with `QRTour.CarryComparison`" in theorem_surface
    assert "`carry_window_transducer`" in theorem_surface
    assert "`carry_dfa_factorization` remains `open`" in boundary
    assert "`small_k_visibility_threshold` remains `open`" in boundary


def test_qr_tour_umbrella_example_uses_exact_block_coordinate_tuple() -> None:
    text = QRT_SURFACE.read_text()

    assert "## Example: p = 97, base = 10, m = 2, B = 100" in text
    assert "`B = 10^2 = 100` and `k = B mod 97 = 3`" in text
    assert "`ord_97(3) = 48 = (97 - 1) / 2`" in text
    assert "`3^0, 3^1, 3^2, ..., 3^47`" in text


def test_qr_tour_umbrella_marks_support_only_modules_as_unpromoted() -> None:
    text = QRT_SURFACE.read_text()
    theorem_surface = _section(text, "## Current Theorem Surface", "## Exact/Open Boundary")
    modules = _section(text, "## Modules", "## Notes On Agda Correspondence")

    assert "`QRTour.PrimitiveRoots` remains general generator infrastructure" in theorem_surface
    assert "bridge-quality support layer rather than an atlas-backed theorem" in theorem_surface
    assert "support-only infrastructure above the current atlas-backed QR" in modules
    assert "exploratory support only, not an atlas-backed theorem carrier" in modules


def test_qr_tour_umbrella_registry_backed_blocks_are_synchronized() -> None:
    text = QRT_SURFACE.read_text()

    assert _marked_block(text, "<!-- PROOF_SYSTEM_LEGEND_START -->", "<!-- PROOF_SYSTEM_LEGEND_END -->") == "\n".join(
        render_proof_system_legend_lines()
    )
    assert _marked_block(
        text,
        "<!-- QRT_SURFACE_THEOREM_SURFACE_START -->",
        "<!-- QRT_SURFACE_THEOREM_SURFACE_END -->",
    ) == "\n".join(render_qr_tour_theorem_surface_lines())
    assert _marked_block(
        text,
        "<!-- QRT_SURFACE_OPEN_BOUNDARY_START -->",
        "<!-- QRT_SURFACE_OPEN_BOUNDARY_END -->",
    ) == "\n".join(render_qr_tour_open_boundary_lines())
    assert _marked_block(text, "<!-- QRT_SURFACE_MODULES_START -->", "<!-- QRT_SURFACE_MODULES_END -->") == "\n".join(
        render_qr_tour_module_lines()
    )


def test_examples_surface_mentions_prime_and_composite_witnesses() -> None:
    umbrella_text = QRT_SURFACE.read_text()
    examples_text = EXAMPLES_SURFACE.read_text()

    assert (
        "`QRTour.Examples` - Worked prime, small composite, positive-q composite, and same-core composite examples"
        in umbrella_text
    )
    assert (
        "# Worked Examples: prime 19, prime 97, composite 21, composite 249, and same-core composite 996 over 249"
        in examples_text
    )
    assert "(base=10, p=19, ord_p(base)=18)" in examples_text
    assert "QRTour.Prime19.reptendPeriod_eq_eighteen" in examples_text
    assert "QRTour.Prime19.digit_remainder_step_zero" in examples_text
    assert "QRTour.Prime19.digit_periodic_decimal" in examples_text
    assert "(base=10, p=97, stride=2, B=100, q=1, k=3)" in examples_text
    assert "QRTour.Prime97.coordinate_partialSumQ_four_eq_finite" in examples_text
    assert "QRTour.Prime97.coordinate_stateAlignments_output_agreement_pointwise_six_three" in examples_text
    assert "(base=10, N=21=3·7, ord_3(base)=1, ord_7(base)=6)" in examples_text
    assert "QRTour.Composite21.order_of_decimalUnitMod3" in examples_text
    assert "QRTour.Composite21.decimalUnit_order_eq_lcm_component_orders" in examples_text
    assert "QRTour.Composite21.order_of_decimalUnitMod21" in examples_text
    assert "(base=10, N=249, stride=3, B=1000, q=4, k=4)" in examples_text
    assert "(base=10, N=996, core=249, stride=3," in examples_text
    assert "QRTour.Composite249.coordinate_goodMode" in examples_text
    assert "QRTour.Composite249.coordinate_quotientQ_eq_four" in examples_text
    assert "QRTour.Composite249.coordinate_remainderK_eq_four" in examples_text
    assert "QRTour.Composite249.coordinate_positive_q_good_modes" in examples_text
    assert "QRTour.Composite249.coordinate_series_q_weighted_identity" in examples_text
    assert "QRTour.Composite249.coordinate_partialSumQ_four_eq_finite" in examples_text
    assert "QRTour.Composite249.coordinate_firstIncomingCarryPosition" in examples_text
    assert "QRTour.Composite249.coordinate_localOverflowBoundary" in examples_text
    assert "QRTour.Composite249.coordinate_firstVisibleMismatchPosition_eq_three" in examples_text
    assert "QRTour.Composite249.coordinate_lookaheadCertificate_three_zero" in examples_text
    assert "QRTour.Composite249.coordinate_visibleCarryWord_eq_emittedBlockWord_three_zero" in examples_text
    assert "QRTour.Composite249.coordinate_visibleCarryWord_three_zero_eq_blocks" in examples_text
    assert "QRTour.Composite249.coordinate_stateAlignments_output_agreement_three_zero" in examples_text
    assert "QRTour.Composite249.coordinate_stateAlignments_output_agreement_pointwise_three_zero" in examples_text
    assert "QRTour.Composite996.preperiodSteps_eq_two" in examples_text
    assert "QRTour.Composite996.strippedPeriodModulus_eq_249" in examples_text
    assert "QRTour.Composite996.sameCore_remainderK_eq" in examples_text
    assert "QRTour.Composite996.sameCore_basePrimeSupportFactor_eq_remainderK_pow_one" in examples_text
    assert "QRTour.Composite996.sameCore_denominator_eq_249_mul_remainderK_pow_one" in examples_text
    assert "QRTour.Composite996.sameCore_denominator_eq_249_mul_coreRemainderK_pow_one" in examples_text
    assert "QRTour.Composite996.sameCore_quotientQ_scaling_eq_remainderK_pow_one" in examples_text
    assert "QRTour.Composite996.sameCore_firstIncomingCarryPosition_shift_exact" in examples_text
    assert "QRTour.Composite996.sameCore_localOverflowBoundary_shift_exact" in examples_text
    assert "QRTour.Composite996.sameCore_firstVisibleMismatchPosition_shift_exact" in examples_text
    assert "QRTour.Composite996.sameCore_lookaheadCertificateHolds_iff_add_exact" in examples_text
    assert "QRTour.Composite996.sameCore_tailMassLowerBound_iff_add_exact" in examples_text
    assert "QRTour.Composite996.actual996_tailMassLowerBound_of_core_lookaheadCertificate_exact" in examples_text
    assert "QRTour.Composite996.core249_tailMassLowerBound_of_actual_lookaheadCertificate_exact" in examples_text
    assert "QRTour.Composite996.actual996_stateAlignments_carryIn_shift_exact" in examples_text
    assert "QRTour.Composite996.actual996_stateAlignments_remainderIn_shift_exact" in examples_text
    assert "QRTour.Composite996.actual996_stateAlignments_remainderBlockValue_shift_exact" in examples_text
    assert "QRTour.Composite996.actual996_stateAlignments_remainderOut_shift_exact" in examples_text
    assert "QRTour.Composite996.actual996_stateAlignments_remainderToCarryStepFunctional" in examples_text
    assert "QRTour.Composite996.core249_carryToRemainderFunctional_one_zero" in examples_text
    assert "QRTour.Composite996.actual996_carryToRemainder_conflict_two_zero" in examples_text
    assert "QRTour.Composite996.sameCore_carryToRemainderTransport_counterexample" in examples_text
    assert "QRTour.Composite996.actual996_not_carryToRemainderFunctional" in examples_text
    assert "QRTour.Composite996.actual996_stateAlignments_remainderToCarry_transition_compatible" in examples_text
    assert "QRTour.Composite996.actual996_quotientOnly_profile" in examples_text
    assert "QRTour.Composite996.core249_remainderToCarryFunctional" in examples_text
    assert "QRTour.Composite996.core249_stateAlignments_remainderToCarry_transition_compatible" in examples_text
    assert "QRTour.Composite996.core249_not_carryToRemainderFunctional" in examples_text


def test_examples_surface_documented_entry_points_resolve_in_examples_module() -> None:
    examples_text = EXAMPLES_SURFACE.read_text()
    doc_section = examples_text.split("## Prime 97 Results", 1)[1].split("namespace QRTour.Prime97", 1)[0]
    documented_entry_points = re.findall(r"`(QRTour\.[A-Za-z0-9_.']+)`", doc_section)
    declarations = {match.group(1) for match in EXAMPLE_DECL_PATTERN.finditer(examples_text)}

    assert documented_entry_points
    unresolved = [
        full_name
        for full_name in documented_entry_points
        if full_name.rsplit(".", 1)[1] not in declarations
    ]
    assert not unresolved, f"documented example entry points missing declarations: {unresolved}"
