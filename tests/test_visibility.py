from bridge_reptends import (
    canonical_visibility_case_studies,
    canonical_visibility_family_studies,
    carried_prefix_visibility_profile,
    certified_lookahead_blocks,
    chart_invariance_rows,
    incoming_carry_counterexample_rows,
    incoming_carry_value,
    instrument_atlas_rows,
    lookahead_certificate_holds,
    lookahead_gap_numerator,
    lookahead_tail_mass_lower_bound,
    predicted_first_incoming_carry_position,
    predicted_raw_prefix_agreement_length,
    select_same_core_prefer_m,
    same_core_visibility_comparison,
    same_core_visibility_rows,
    visibility_base_instrument_rows,
    visibility_optics_workbench_rows,
    visibility_profile_rows,
)


def test_visibility_profile_distinguishes_carry_intrusion_from_local_overflow() -> None:
    profile = carried_prefix_visibility_profile(97, prefer_m=2, n_blocks=8)

    assert profile.q == 1
    assert profile.k == 3
    assert profile.first_local_overflow_position == 5
    assert profile.first_incoming_carry_position == 4
    assert profile.predicted_first_incoming_carry_position == 4
    assert profile.raw_prefix_agreement_length == 4
    assert profile.predicted_raw_prefix_agreement_length == 4
    assert profile.lookahead_lower_bound == 2
    assert profile.certified_lookahead_blocks == 2
    assert profile.exact_gap_numerator == 4217
    assert profile.first_mismatch_position == 4
    assert profile.mismatch_regime == "incoming_carry_before_local_overflow"
    assert profile.incoming_carry_formula_holds is True
    assert profile.agreement_identity_holds is True
    assert profile.lookahead_certificate_matches is True


def test_visibility_optics_workbench_surfaces_ranked_signal_classes() -> None:
    rows = visibility_optics_workbench_rows(max_n=500, n_blocks=8, top=10)
    by_group: dict[str, list[dict[str, object]]] = {}
    for row in rows:
        by_group.setdefault(str(row["group"]), []).append(row)

    assert by_group["workbench_summary"][0]["open_claim_boundary"] == [
        "small_k_visibility_threshold",
        "carry_dfa_factorization",
    ]
    anchors = {row["n"]: row for row in by_group["canonical_anchor"]}
    assert {21, 97, 249, 996}.issubset(anchors)
    assert anchors[21]["signal_class"] == "transparent_window"
    assert {
        anchors[97]["signal_class"],
        anchors[996]["signal_class"],
    } & {"early_carry_intrusion"}
    assert any(
        row["signal_class"] in {
            "visible_state_compression",
            "hidden_graph_obstruction",
        }
        for row in by_group["ranked_case"]
    )
    assert any(
        "carry_dfa_factorization" in row["related_open_claim_ids"]
        for row in by_group["ranked_case"]
    )
    assert any(row["signal_class"] == "same_core_drift" for row in by_group["same_core_signal"])


def test_visibility_base_instrument_rows_compare_bases() -> None:
    rows = visibility_base_instrument_rows(max_n=120, bases=(10, 12, 30), n_blocks=8, top=5)
    by_group: dict[str, list[dict[str, object]]] = {}
    for row in rows:
        by_group.setdefault(str(row["group"]), []).append(row)

    summary = by_group["base_instrument_summary"][0]
    assert summary["bases"] == [10, 12, 30]
    assert summary["open_claim_boundary"] == [
        "small_k_visibility_threshold",
        "carry_dfa_factorization",
    ]
    assert {row["base"] for row in by_group["base_summary"]} == {10, 12, 30}

    cross_by_n = {row["n"]: row for row in by_group["cross_base_case"]}
    assert 97 in cross_by_n
    assert cross_by_n[97]["base_instrument_behavior"] in {
        "instrument_shift",
        "base30_absorption_shift",
    }
    assert "10:" in cross_by_n[97]["signal_class_path"]
    assert any(row["base"] == 30 for row in by_group["base_ranked_case"])


def test_instrument_atlas_rows_pressure_working_axioms() -> None:
    rows = instrument_atlas_rows(max_n=120, bases=(10, 12, 30), n_blocks=8, top=5)
    by_group: dict[str, list[dict[str, object]]] = {}
    for row in rows:
        by_group.setdefault(str(row["group"]), []).append(row)

    summary = by_group["instrument_atlas_summary"][0]
    assert summary["bases"] == [10, 12, 30]
    assert summary["open_claim_boundary"] == [
        "small_k_visibility_threshold",
        "carry_dfa_factorization",
    ]
    assert {row["base"] for row in by_group["instrument_profile"]} == {10, 12, 30}
    assert any(row["instrument_personality"] == "obstruction_revealer" for row in by_group["instrument_profile"])

    case_97 = next(row for row in by_group["instrument_case"] if row["n"] == 97)
    assert "10:visible_state_compression" in case_97["instrument_signature"]
    assert "30:hidden_graph_obstruction" in case_97["instrument_signature"]
    assert case_97["revealed_by_bases"] == [10]
    assert case_97["obstructed_by_bases"] == [30]
    assert "visible_trace_can_hide_state_obstruction" in case_97["working_axiom_pressure"]

    axiom_ids = {row["signal_id"] for row in by_group["working_axiom_signal"]}
    assert "recoverability_is_instrument_relative" in axiom_ids
    assert "factor_absorption_changes_periodic_core" in axiom_ids


def test_chart_invariance_rows_split_clean_distortion_from_absorption() -> None:
    rows = chart_invariance_rows(max_n=120, bases=(10, 12, 30), n_blocks=8, top=5)
    by_group: dict[str, list[dict[str, object]]] = {}
    for row in rows:
        by_group.setdefault(str(row["group"]), []).append(row)

    summary = by_group["chart_invariance_summary"][0]
    assert summary["bases"] == [10, 12, 30]
    assert summary["clean_chart_distortion_count"] >= 1
    assert summary["open_claim_boundary"] == [
        "small_k_visibility_threshold",
        "carry_dfa_factorization",
    ]

    pair_by_name = {row["base_pair"]: row for row in by_group["chart_pair_summary"]}
    assert pair_by_name["10/30"]["chart_relation_class"] == "clean_chart_distortion_pair"
    assert 97 in pair_by_name["10/30"]["clean_distortion_example_ns"]
    assert pair_by_name["10/30"]["reveal_hide_flip_count"] >= 1

    case_97 = next(row for row in by_group["chart_distortion_witness"] if row["n"] == 97)
    assert case_97["chart_invariance_class"] == "clean_chart_distortion"
    assert case_97["periodic_moduli_by_base"] == {"10": 97, "12": 97, "30": 97}
    assert "30:hidden_graph_obstruction" in case_97["chart_signature"]

    invariant_ns = {row["n"] for row in by_group["chart_invariant_case"]}
    assert {249, 996} <= invariant_ns


def test_visibility_profile_handles_fully_visible_positive_q_case() -> None:
    profile = carried_prefix_visibility_profile(37, prefer_m=3, n_blocks=6)

    assert profile.q == 27
    assert profile.k == 1
    assert profile.first_local_overflow_position is None
    assert profile.first_incoming_carry_position is None
    assert profile.predicted_first_incoming_carry_position is None
    assert profile.lookahead_lower_bound == 0
    assert profile.certified_lookahead_blocks == 0
    assert profile.raw_prefix_agreement_length == 6
    assert profile.full_window_visible is True
    assert profile.mismatch_regime == "fully_visible_window"


def test_visibility_profile_same_periodic_core_cases_separate_observables() -> None:
    profile_249 = carried_prefix_visibility_profile(249, prefer_m=3, n_blocks=8)
    profile_996 = carried_prefix_visibility_profile(996, prefer_m=3, n_blocks=8)

    assert profile_249.periodic_modulus == 249
    assert profile_996.periodic_modulus == 249
    assert profile_249.preperiod_digits == 0
    assert profile_996.preperiod_digits == 2
    assert profile_249.first_incoming_carry_position == 3
    assert profile_996.first_incoming_carry_position == 4
    assert profile_249.predicted_first_incoming_carry_position == 3
    assert profile_996.predicted_first_incoming_carry_position == 4
    assert profile_249.lookahead_lower_bound == 2
    assert profile_249.certified_lookahead_blocks == 2
    assert profile_996.lookahead_lower_bound == 1
    assert profile_996.certified_lookahead_blocks == 1
    assert profile_249.raw_prefix_agreement_length == 3
    assert profile_996.raw_prefix_agreement_length == 4


def test_canonical_visibility_cases_cover_track_16_families() -> None:
    cases = {case.n: case for case in canonical_visibility_case_studies()}
    families = {case.label: case for case in canonical_visibility_family_studies()}

    assert {21, 37, 97, 249, 996}.issubset(cases)
    assert cases[97].profile.mismatch_regime == "incoming_carry_before_local_overflow"
    assert "lookahead" in cases[249].theorem_candidate.lower()
    assert "naive visibility rules" in cases[996].counterexample_target.lower()

    assert "q = 1 carried-prefix family" in families
    assert families["q = 1 carried-prefix family"].members == (97, 996)
    assert "shared periodic core" in families["Shared periodic core with different preperiods"].label.lower()
    assert "Cross-base same-core exact law" in families
    assert families["Cross-base same-core exact law"].members == (8, 56)
    assert "Cross-base interval endpoints in one coordinate" in families
    assert 70 in families["Cross-base interval endpoints in one coordinate"].members


def test_visibility_profile_rows_export_exact_observables() -> None:
    rows = visibility_profile_rows(1000, n_blocks=8)
    by_n = {row["n"]: row for row in rows}

    assert 97 in by_n
    assert 249 in by_n
    assert 996 in by_n
    assert by_n[97]["mismatch_regime"] == "incoming_carry_before_local_overflow"
    assert by_n[97]["predicted_first_incoming_carry_position"] == 4
    assert by_n[97]["lookahead_lower_bound"] == 2
    assert by_n[97]["certified_lookahead_blocks"] == 2
    assert by_n[97]["incoming_carry_formula_holds"] is True
    assert by_n[97]["agreement_identity_holds"] is True
    assert by_n[97]["lookahead_certificate_matches"] is True
    assert "incoming_carry_position_formula" in by_n[97]["matching_claim_ids"]
    assert "small_k_visibility_threshold" in by_n[97]["related_open_claim_ids"]
    assert "incoming_carry_position_formula_prime97_stride2" in by_n[97]["matching_witness_ids"]
    assert "small_k_visibility_threshold_target_97_249_996" in by_n[97]["matching_witness_ids"]
    assert by_n[37]["mismatch_regime"] == "fully_visible_window"


def test_incoming_carry_formula_matches_values_and_counterexample_rows() -> None:
    profile = carried_prefix_visibility_profile(249, prefer_m=3, n_blocks=8)

    assert incoming_carry_value(profile.q, profile.k, profile.B, 2) == 0
    assert incoming_carry_value(profile.q, profile.k, profile.B, 3) == 1
    assert predicted_first_incoming_carry_position(profile.q, profile.k, profile.B, requested_blocks=8) == 3
    assert predicted_raw_prefix_agreement_length(profile.q, profile.k, profile.B, requested_blocks=8) == 3
    assert lookahead_tail_mass_lower_bound(profile.q, profile.k, profile.B, requested_blocks=8) == 2
    assert lookahead_gap_numerator(profile.q, profile.k, profile.B, requested_blocks=8, lookahead_blocks=2) == 807424
    assert lookahead_certificate_holds(profile.q, profile.k, profile.B, requested_blocks=8, lookahead_blocks=2) is True
    assert certified_lookahead_blocks(profile.q, profile.k, profile.B, requested_blocks=8) == 2

    rows = incoming_carry_counterexample_rows(1000, n_blocks=8)
    by_n = {row["n"]: row for row in rows}
    assert 97 in by_n
    assert 249 in by_n
    assert 996 in by_n


def test_same_core_visibility_comparison_captures_249_996_shift_law() -> None:
    comparison = same_core_visibility_comparison(996, prefer_m=3, n_blocks=8)

    assert comparison.actual_profile.n == 996
    assert comparison.core_profile.n == 249
    assert comparison.shared_bridge_defect == 996
    assert comparison.q_ratio == 4
    assert comparison.q_ratio_floor_log_k == 1
    assert comparison.q_ratio_k_exponent == 1
    assert comparison.shift_interval == (1, 1)
    assert comparison.incoming_carry_shift == 1
    assert comparison.local_overflow_shift == 1
    assert comparison.raw_prefix_shift == 1
    assert comparison.interval_family_law_holds is True
    assert comparison.incoming_carry_shift_matches is True
    assert comparison.local_overflow_shift_matches is True
    assert comparison.raw_prefix_shift_matches is True
    assert comparison.lookahead_shift == 1
    assert comparison.exact_shift_law_holds is True


def test_same_core_interval_law_covers_non_power_q_ratios() -> None:
    comparison = same_core_visibility_comparison(498, prefer_m=3, n_blocks=8)

    assert comparison.actual_profile.n == 498
    assert comparison.core_profile.n == 249
    assert comparison.q_ratio == 2
    assert comparison.q_ratio_floor_log_k == 0
    assert comparison.q_ratio_k_exponent is None
    assert comparison.shift_interval == (0, 1)
    assert comparison.incoming_carry_shift == 1
    assert comparison.local_overflow_shift == 1
    assert comparison.raw_prefix_shift == 1
    assert comparison.interval_family_law_holds is True
    assert comparison.exact_shift_law_holds is False


def test_same_core_mode_selector_prefers_informative_cross_base_coordinates() -> None:
    assert select_same_core_prefer_m(56, base=7, n_blocks=8) == 3
    assert select_same_core_prefer_m(10, base=12, n_blocks=8) == 2
    assert select_same_core_prefer_m(70, base=12, n_blocks=8) == 2


def test_same_core_visibility_rows_surface_cross_base_examples() -> None:
    by_actual_10 = {row["actual_n"]: row for row in same_core_visibility_rows(1000, base=10, n_blocks=8)}
    by_actual_7 = {row["actual_n"]: row for row in same_core_visibility_rows(100, base=7, n_blocks=8)}
    by_actual_12 = {row["actual_n"]: row for row in same_core_visibility_rows(200, base=12, n_blocks=8)}

    assert 996 in by_actual_10
    assert "same_core_threshold_shift_interval" in by_actual_10[996]["matching_claim_ids"]
    assert "small_k_visibility_threshold" in by_actual_10[996]["related_open_claim_ids"]
    assert "same_core_threshold_shift_interval_996_over_249" in by_actual_10[996]["matching_witness_ids"]
    assert "small_k_visibility_threshold_target_97_249_996" in by_actual_10[996]["matching_witness_ids"]

    assert 56 in by_actual_7
    assert by_actual_7[56]["core_n"] == 8
    assert by_actual_7[56]["family_law"] == "exact"
    assert by_actual_7[56]["threshold_shift_endpoint"] == "exact"

    assert 10 in by_actual_12
    assert 20 in by_actual_12
    assert 70 in by_actual_12
    assert by_actual_12[10]["core_n"] == 5
    assert by_actual_12[10]["family_law"] == "interval"
    assert by_actual_12[10]["threshold_shift_endpoint"] == "lower"
    assert by_actual_12[20]["family_law"] == "exact"
    assert by_actual_12[20]["threshold_shift_endpoint"] == "exact"
    assert by_actual_12[70]["core_n"] == 35
    assert by_actual_12[70]["family_law"] == "interval"
    assert by_actual_12[70]["threshold_shift_endpoint"] == "upper"
