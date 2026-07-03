from bridge_reptends import (
    canonical_visibility_case_studies,
    canonical_visibility_family_studies,
    certificate_lean_fixture_rows,
    certificate_workbench_rows,
    carry_remainder_comparison,
    carried_prefix_visibility_profile,
    certified_positive_lookahead_coefficient_conflict_atlas_rows,
    certified_positive_lookahead_coefficient_conflict_family_rows,
    certified_positive_lookahead_coefficient_conflict_rows,
    certified_positive_lookahead_state_window_rows,
    certified_lookahead_blocks,
    chart_invariance_rows,
    composite68_congruence_family_rows,
    composite68_cross_base_obstruction_sweep_rows,
    CoefficientConflictCertificate,
    incoming_carry_counterexample_rows,
    incoming_carry_value,
    LookaheadCertificate,
    instrument_atlas_rows,
    observability_atlas_rows,
    observability_instrument_comparison_rows,
    observability_mod_stable_carry_loss_rows,
    observability_next_source_shape_family_rows,
    observability_program_atlas_rows,
    observability_shape13_k4_mod_stable_carry_loss_rows,
    observability_shape187_k188_family_rows,
    observability_shape17_k4_family_rows,
    observability_target_signature_rows,
    observability_target_split_rows,
    lookahead_certificate_holds,
    lookahead_gap_numerator,
    lookahead_tail_mass_lower_bound,
    predicted_first_incoming_carry_position,
    predicted_raw_prefix_agreement_length,
    select_same_core_prefer_m,
    same_core_visibility_comparison,
    same_core_visibility_rows,
    StateMapCertificate,
    visibility_base_instrument_rows,
    visibility_optics_workbench_rows,
    visibility_profile_rows,
)
from bridge_reptends.certificates import POSITIVE_RECONSTRUCTION_SOURCE_PINNED_ANCHORS


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


def test_remainder_to_coefficient_map_distinguishes_frontier_from_counterexamples() -> None:
    prime97 = carry_remainder_comparison(97, base=10, n_blocks=8, prefer_m=2)
    composite996 = carry_remainder_comparison(996, base=10, n_blocks=8, prefer_m=3)
    obstruction68 = carry_remainder_comparison(68, base=10, n_blocks=8, prefer_m=4)

    assert prime97.remainder_to_coefficient_map.source_kind == "remainder state"
    assert prime97.remainder_to_coefficient_map.target_kind == "raw coefficient"
    assert prime97.coefficient_functional is True
    assert composite996.coefficient_functional is True
    assert obstruction68.coefficient_functional is False
    assert prime97.first_remainder_to_coefficient_conflict is None
    assert composite996.first_remainder_to_coefficient_conflict is None

    conflict = obstruction68.first_remainder_to_coefficient_conflict
    assert conflict is not None
    assert conflict.remainder_state == 4
    assert conflict.positions == (1, 5)
    assert conflict.coefficients == (588, 150528)
    assert conflict.carry_states == (0, 60)
    assert conflict.block_values == (588, 588)
    assert conflict.output_hidden is True
    assert conflict.position_gap == 4
    assert conflict.coefficient_delta == 149940


def test_certificate_objects_export_flat_fields_for_frontier_and_obstruction_rows() -> None:
    state_rows = certified_positive_lookahead_state_window_rows(
        max_n=1000,
        base=10,
        n_blocks=8,
    )
    by_n = {
        row["n"]: row
        for row in state_rows
        if row["group"] == "certified_positive_lookahead_case"
    }

    lookahead97 = LookaheadCertificate.from_row(by_n[97]).to_row()
    assert lookahead97 == {
        "requested_blocks": 8,
        "certified_lookahead_blocks": 2,
        "lookahead_lower_bound": 2,
        "exact_gap_numerator": 4217,
        "lookahead_certificate_matches": True,
    }

    comparison97 = carry_remainder_comparison(97, base=10, n_blocks=8, prefer_m=2)
    comparison996 = carry_remainder_comparison(996, base=10, n_blocks=8, prefer_m=3)
    state97 = StateMapCertificate.from_state_map(
        comparison97.remainder_to_coefficient_map
    ).to_row("remainder_to_coefficient")
    state996 = StateMapCertificate.from_state_map(
        comparison996.remainder_to_coefficient_map
    ).to_row("remainder_to_coefficient")
    assert state97["remainder_to_coefficient_functional"] is True
    assert state97["remainder_to_coefficient_ambiguity_signature"] == "functional"
    assert state996["remainder_to_coefficient_functional"] is True

    comparison68 = carry_remainder_comparison(68, base=10, n_blocks=8, prefer_m=4)
    conflict68 = comparison68.first_remainder_to_coefficient_conflict
    assert conflict68 is not None
    conflict_row = CoefficientConflictCertificate.from_witness(conflict68).to_row()
    assert conflict_row["conflict_remainder_state"] == 4
    assert conflict_row["conflict_positions"] == [1, 5]
    assert conflict_row["conflict_coefficients"] == [588, 150528]
    assert conflict_row["conflict_carry_states"] == [0, 60]
    assert conflict_row["conflict_block_values"] == [588, 588]
    assert conflict_row["conflict_output_hidden"] is True
    assert conflict_row["conflict_position_gap"] == 4
    assert conflict_row["conflict_coefficient_delta"] == 149940

    comparison68_base30 = carry_remainder_comparison(68, base=30, n_blocks=8, prefer_m=3)
    conflict68_base30 = comparison68_base30.first_remainder_to_coefficient_conflict
    assert conflict68_base30 is not None
    conflict_row_base30 = CoefficientConflictCertificate.from_witness(
        conflict68_base30
    ).to_row()
    assert conflict_row_base30["conflict_remainder_state"] == 4
    assert conflict_row_base30["conflict_positions"] == [1, 5]
    assert conflict_row_base30["conflict_coefficients"] == [1588, 406528]
    assert conflict_row_base30["conflict_carry_states"] == [0, 60]
    assert conflict_row_base30["conflict_block_values"] == [1588, 1588]
    assert conflict_row_base30["conflict_output_hidden"] is True


def test_certified_positive_lookahead_state_window_rows_surface_frontier_and_candidates() -> None:
    rows = certified_positive_lookahead_state_window_rows(max_n=1000, base=10, n_blocks=8)
    assert rows[0]["group"] == "certified_positive_lookahead_summary"

    summary = rows[0]
    case_rows = [row for row in rows if row["group"] == "certified_positive_lookahead_case"]
    by_n = {row["n"]: row for row in case_rows}

    assert summary["total_rows"] == len(case_rows)
    assert summary["gap_one_covered_rows"] == 0
    assert summary["empirical_coefficient_functional_frontier_rows"] > 0
    assert summary["coefficient_functionality_counterexample_candidates"] > 0
    assert summary["smallest_exact_gap_numerator"] == 44
    assert summary["next_theorem_direction"] == "refine_gap_criterion_or_search_counterexample"

    assert case_rows[0]["n"] == 98
    assert by_n[98]["m"] == 2
    assert by_n[98]["B"] == 100
    assert by_n[98]["q"] == 1
    assert by_n[98]["k"] == 2
    assert by_n[98]["certified_lookahead_blocks"] == 1
    assert by_n[98]["exact_gap_numerator"] == 44
    assert by_n[98]["theorem_frontier_status"] == "empirically_coefficient_functional_frontier"

    assert by_n[97]["theorem_frontier_status"] == "empirically_coefficient_functional_frontier"
    assert by_n[97]["remainder_to_coefficient_functional"] is True
    assert "remainder_to_coefficient_fiber_signature" in by_n[97]
    assert by_n[996]["theorem_frontier_status"] == "empirically_coefficient_functional_frontier"
    assert by_n[996]["remainder_to_coefficient_functional"] is True

    assert by_n[68]["m"] == 4
    assert by_n[68]["q"] == 147
    assert by_n[68]["k"] == 4
    assert by_n[68]["certified_lookahead_blocks"] == 1
    assert by_n[68]["exact_gap_numerator"] == 6208
    assert by_n[68]["theorem_frontier_status"] == "coefficient_functionality_counterexample_candidate"
    assert by_n[68]["remainder_to_coefficient_functional"] is False

    assert all(
        row["theorem_frontier_status"] != "covered_by_gap_one_bridge"
        for row in case_rows
        if row["base"] == 10
    )


def test_certified_positive_lookahead_coefficient_conflict_rows_surface_first_obstruction() -> None:
    rows = certified_positive_lookahead_coefficient_conflict_rows(
        max_n=1000,
        base=10,
        n_blocks=8,
        top=8,
    )
    assert rows[0]["group"] == "coefficient_conflict_summary"
    assert rows[0]["first_conflict_n"] == 68
    assert rows[0]["first_conflict_tuple"] == [10, 68, 4, 10000, 147, 4, 1, 6208]
    assert rows[0]["total_conflict_rows"] > 0
    assert rows[0]["output_hidden_conflict_rows"] == rows[0]["total_conflict_rows"]

    conflict_rows = [row for row in rows if row["group"] == "coefficient_conflict_witness"]
    assert conflict_rows[0]["n"] == 68
    assert conflict_rows[0]["conflict_remainder_state"] == 4
    assert conflict_rows[0]["conflict_positions"] == [1, 5]
    assert conflict_rows[0]["conflict_coefficients"] == [588, 150528]
    assert conflict_rows[0]["conflict_carry_states"] == [0, 60]
    assert conflict_rows[0]["conflict_block_values"] == [588, 588]
    assert conflict_rows[0]["conflict_output_hidden"] is True
    assert conflict_rows[0]["conflict_position_gap"] == 4
    assert conflict_rows[0]["conflict_coefficient_delta"] == 149940
    assert {row["n"] for row in conflict_rows}.isdisjoint({97, 996})


def test_certificate_workbench_rows_package_lean_ready_and_frontier_anchors() -> None:
    rows = certificate_workbench_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    assert rows[0]["group"] == "certificate_workbench_summary"
    assert rows[0]["requested_blocks"] == 8
    assert rows[0]["bases"] == [7, 10, 12, 30]
    assert rows[0]["first_lean_ready_tuple"] == [10, 68, 4, 10000, 147, 4, 1, 6208]
    assert rows[0]["recommended_next_lean_task"] == "reuse_composite68_family_certificate"

    case_rows = [row for row in rows if row["group"] == "certificate_workbench_case"]
    by_key = {(row["base"], row["n"]): row for row in case_rows}
    assert {(10, 68), (30, 68), (10, 97), (10, 996)} <= set(by_key)

    base10_68 = by_key[(10, 68)]
    assert base10_68["certificate_class"] == "lean_ready_hidden_conflict"
    assert base10_68["lean_readiness"] == "existing_composite68_family_theorem"
    assert base10_68["theorem_frontier_status"] == "coefficient_functionality_counterexample_candidate"
    assert base10_68["next_lean_task"] == "reuse_composite68_family_certificate"
    assert base10_68["conflict_positions"] == [1, 5]
    assert base10_68["conflict_coefficients"] == [588, 150528]
    assert base10_68["remainder_to_coefficient_functional"] is False
    assert base10_68["remainder_to_carry_functional"] is False
    assert "4->0,60" in base10_68["remainder_to_carry_ambiguity_signature"]
    assert base10_68["carry_to_remainder_functional"] is False
    assert "0->1,4,16" in base10_68["carry_to_remainder_ambiguity_signature"]

    base30_68 = by_key[(30, 68)]
    assert base30_68["certificate_class"] == "lean_ready_hidden_conflict"
    assert base30_68["conflict_coefficients"] == [1588, 406528]
    assert base30_68["conflict_block_values"] == [1588, 1588]

    assert by_key[(10, 97)]["certificate_class"] == "functional_frontier"
    assert by_key[(10, 97)]["remainder_to_coefficient_functional"] is True
    assert by_key[(10, 996)]["certificate_class"] == "functional_frontier"
    assert by_key[(10, 996)]["remainder_to_coefficient_functional"] is True


def test_certificate_workbench_ranking_prefers_lean_ready_over_smaller_conflicts() -> None:
    rows = certificate_workbench_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    case_rows = [row for row in rows if row["group"] == "certificate_workbench_case"]
    assert case_rows[0]["base"] == 10
    assert case_rows[0]["n"] == 68
    assert case_rows[0]["certificate_class"] == "lean_ready_hidden_conflict"
    assert case_rows[1]["base"] == 30
    assert case_rows[1]["n"] == 68
    assert case_rows[1]["certificate_class"] == "lean_ready_hidden_conflict"

    smaller_frontier_conflict = next(
        row for row in case_rows if row["base"] == 30 and row["n"] == 7
    )
    assert smaller_frontier_conflict["exact_gap_numerator"] < case_rows[0]["exact_gap_numerator"]
    assert case_rows.index(smaller_frontier_conflict) > case_rows.index(case_rows[0])


def test_observability_atlas_rows_classify_hidden_and_functional_anchors() -> None:
    rows = observability_atlas_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )

    assert rows[0]["group"] == "observability_summary"
    assert rows[0]["open_boundary_ids"] == [
        "small_k_visibility_threshold",
        "carry_dfa_factorization",
    ]
    assert rows[0]["observability_boundary_status"] == "empirical_open_boundary_tooling"
    assert rows[0]["finite_only_hidden_conflict_cases"] > 0

    case_rows = [row for row in rows if row["group"] != "observability_summary"]
    by_key = {(row["base"], row["n"]): row for row in case_rows}
    assert {(10, 68), (30, 68), (10, 97), (10, 996)} <= set(by_key)

    for key in [(10, 68), (30, 68)]:
        row = by_key[key]
        assert row["group"] == "hidden_coefficient_conflict"
        assert row["coefficient_observability_class"] == "hidden_coefficient_conflict"
        assert row["source_symmetry_visible"] is True
        assert row["coefficient_information_lost"] is True
        assert row["carry_output_hides_conflict"] is True
        assert row["open_boundary_ids"] == [
            "small_k_visibility_threshold",
            "carry_dfa_factorization",
        ]
        assert row["same_core_shift_support_status"] == "finite_only_hidden_conflict"
        assert row["observability_targets"] == [
            "raw_coefficient_nat",
            "coefficient_mod_block_base",
            "carried_block_value",
            "carry_state",
            "remainder_state",
            "displayed_prefix",
        ]
        assert row["raw_coefficient_nat_observability_status"] == "factor_through_obstructed"
        assert row["raw_coefficient_nat_functional"] is False
        assert row["coefficient_mod_block_base_observability_status"] == "factor_through_obstructed"
        assert row["coefficient_mod_block_base_functional"] is False
        assert row["carried_block_value_observability_status"] == (
            "functional_output_hides_raw_coefficient_conflict"
        )
        assert row["carried_block_value_functional"] is True
        assert row["carry_state_observability_status"] == "factor_through_obstructed"
        assert row["carry_state_functional"] is False
        assert row["remainder_state_observability_status"] == "identity_observation"
        assert row["displayed_prefix_observability_status"] == (
            "certified_window_output_agreement"
        )
        assert "raw_coefficient_nat:factor_through_obstructed" in row[
            "observability_target_summary_signature"
        ]

    for key in [(10, 97), (10, 996)]:
        row = by_key[key]
        assert row["group"] == "coefficient_functional_frontier"
        assert row["coefficient_observability_class"] == "coefficient_functional_frontier"
        assert row["source_symmetry_visible"] is False
        assert row["coefficient_information_lost"] is False
        assert row["carry_output_hides_conflict"] is False
        assert row["same_core_shift_support_status"] == "not_same_core_shift_case"
        assert row["raw_coefficient_nat_observability_status"] == "factor_through_candidate"
        assert row["raw_coefficient_nat_functional"] is True
        assert row["coefficient_mod_block_base_observability_status"] == "factor_through_candidate"
        assert row["coefficient_mod_block_base_functional"] is True

    forbidden_statuses = {
        "small_k_visibility_threshold_closed",
        "carry_dfa_factorization_closed",
    }
    assert all(
        row["observability_boundary_status"] not in forbidden_statuses
        for row in rows
    )


def test_observability_program_atlas_rows_rank_program_lanes_and_reconstruction() -> None:
    rows = observability_program_atlas_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=50,
    )

    assert rows[0]["group"] == "observability_program_summary"
    assert rows[0]["open_boundary_ids"] == [
        "small_k_visibility_threshold",
        "carry_dfa_factorization",
    ]
    assert rows[0]["observability_boundary_status"] == (
        "empirical_open_boundary_program_atlas_tooling"
    )
    assert rows[0]["target_signature_family_count"] >= 3
    assert rows[0]["hidden_source_shape_count"] > 0
    assert rows[0]["cross_base_shape_count"] > 0
    assert rows[0]["lean_ready_hidden_conflicts"] >= 2
    assert rows[0]["positive_functional_frontier_count"] > 0
    assert rows[0]["source_pinned_positive_reconstruction_cases"] == 26
    assert rows[0]["empirical_positive_reconstruction_candidates"] > 0
    assert rows[0]["positive_reconstruction_arithmetic_criterion_id"] == (
        "finite_remainder_state_injective_on_window"
    )
    assert rows[0]["positive_reconstruction_injective_window_criterion_cases"] == (
        rows[0]["emitted_positive_reconstruction_candidates"]
    )
    assert (
        rows[0]["source_pinned_positive_reconstruction_injective_window_cases"]
        == 26
    )
    assert rows[0]["positive_reconstruction_power_no_collision_criterion_id"] == (
        "finite_remainder_power_residue_no_collision"
    )
    assert rows[0]["positive_reconstruction_power_no_collision_criterion_cases"] == (
        rows[0]["emitted_positive_reconstruction_candidates"]
    )
    assert rows[0]["source_pinned_positive_reconstruction_power_no_collision_cases"] == 26
    assert rows[0]["positive_reconstruction_power_no_wrap_criterion_id"] == (
        "finite_remainder_power_residue_no_wrap"
    )
    assert rows[0]["positive_reconstruction_power_no_wrap_criterion_formula"] == (
        "1 < k and k^j < n for 0 <= j < requested_blocks"
    )
    assert rows[0]["positive_reconstruction_power_no_wrap_criterion_cases"] == 1
    assert rows[0]["source_pinned_positive_reconstruction_power_no_wrap_cases"] == 1
    assert rows[0]["first_unpinned_positive_reconstruction_tuple"] == [
        7,
        340,
        3,
        343,
        1,
        3,
        1,
        299,
    ]
    assert rows[0]["first_unpinned_positive_reconstruction_status"] == (
        "empirical_power_no_collision_sufficient_criterion_satisfied"
    )
    assert rows[0][
        "first_unpinned_positive_reconstruction_remainder_power_residue_window"
    ] == [1, 3, 9, 27, 81, 243, 49, 147]
    assert rows[0]["first_unpinned_positive_reconstruction_raw_coefficient_window"] == [
        1,
        3,
        9,
        27,
        81,
        243,
        729,
        2187,
    ]
    assert rows[0]["first_unpinned_positive_reconstruction_family_seed_tuples"] == [
        [7, 170, 3, 343, 2, 3, 1, 255]
    ]
    assert rows[0]["first_unpinned_positive_reconstruction_family_signal"] == (
        "same_base_block_remainder_as_source_pinned_candidate"
    )
    assert rows[0]["positive_reconstruction_family_criterion_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert rows[0]["positive_reconstruction_family_criterion_moduli"] == [
        17,
        34,
        68,
        85,
        170,
        340,
    ]
    assert rows[0]["positive_reconstruction_family_no_collision_theorem"] == (
        "QRTour.Base7K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem"
    )
    assert rows[0]["positive_reconstruction_family_functional_theorem"] == (
        "QRTour.Base7K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem"
    )
    assert rows[0]["positive_reconstruction_family_factor_through_theorem"] == (
        "QRTour.Base7K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert rows[0]["positive_reconstruction_family_pair_theorem"] == (
        "QRTour.Base7K3PositiveReconstruction.n170_n340_powerResidues_nodup_eight_pair"
    )
    assert rows[0]["recommended_positive_reconstruction_decision"] == (
        "use_lean_proved_family_criterion_before_source_pinning_more_examples"
    )
    assert rows[0]["recommended_positive_reconstruction_next_task"] == (
        "prove_or_reject_same_base_block_remainder_power_no_collision_family"
    )
    assert rows[0]["recommended_next_observability_task"] == (
        "prove_or_reject_same_base_block_remainder_power_no_collision_family"
    )
    assert rows[0]["first_uncovered_positive_reconstruction_tuple"] == [
        10,
        361,
        5,
        100000,
        277,
        3,
        1,
        82603,
    ]
    assert rows[0]["first_uncovered_positive_reconstruction_status"] == (
        "empirical_uncovered_power_no_collision_frontier"
    )
    assert rows[0][
        "first_uncovered_positive_reconstruction_remainder_power_residue_window"
    ] == [1, 3, 9, 27, 81, 243, 7, 21]
    assert rows[0]["first_uncovered_positive_reconstruction_raw_coefficient_window"] == [
        277,
        831,
        2493,
        7479,
        22437,
        67311,
        201933,
        605799,
    ]
    assert rows[0]["first_uncovered_positive_reconstruction_family_seed_tuples"] == [
        [10, 277, 5, 100000, 361, 3, 1, 31479]
    ]
    assert rows[0]["first_uncovered_positive_reconstruction_family_signal"] == (
        "same_base_block_remainder_as_source_pinned_candidate"
    )
    assert rows[0]["first_uncovered_positive_reconstruction_decision"] == (
        "pursue_family_criterion_before_source_pinning_more_examples"
    )
    assert rows[0]["first_uncovered_positive_reconstruction_next_task"] == (
        "prove_or_reject_same_base_block_remainder_power_no_collision_family"
    )
    n71_source_pin = POSITIVE_RECONSTRUCTION_SOURCE_PINNED_ANCHORS[(7, 71)]
    assert n71_source_pin["namespace"] == "QRTour.FutureBase7N71"
    assert n71_source_pin["functional_theorem_name"] == (
        "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
    )
    assert n71_source_pin["factor_through_theorem_name"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
    )
    n118_source_pin = POSITIVE_RECONSTRUCTION_SOURCE_PINNED_ANCHORS[(7, 118)]
    assert n118_source_pin["namespace"] == "QRTour.FutureBase7N118"
    assert n118_source_pin["functional_theorem_name"] == (
        "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
    )
    assert n118_source_pin["factor_through_theorem_name"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
    )
    n226_source_pin = POSITIVE_RECONSTRUCTION_SOURCE_PINNED_ANCHORS[(12, 226)]
    assert n226_source_pin["namespace"] == "QRTour.FutureBase12N226"
    assert n226_source_pin["functional_theorem_name"] == (
        "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
    )
    assert n226_source_pin["factor_through_theorem_name"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
    )
    n338_source_pin = POSITIVE_RECONSTRUCTION_SOURCE_PINNED_ANCHORS[(7, 338)]
    assert n338_source_pin["namespace"] == "QRTour.FutureBase7N338"
    assert n338_source_pin["functional_theorem_name"] == (
        "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two"
    )
    assert n338_source_pin["factor_through_theorem_name"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
    )
    n149_source_pin = POSITIVE_RECONSTRUCTION_SOURCE_PINNED_ANCHORS[(12, 149)]
    assert n149_source_pin["namespace"] == "QRTour.FutureBase12N149"
    assert n149_source_pin["functional_theorem_name"] == (
        "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one"
    )
    assert n149_source_pin["factor_through_theorem_name"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
    )
    assert rows[0]["source_pinned_positive_reconstruction_tuples"] == [
        [12, 142, 2, 144, 1, 2, 1, 32],
        [7, 47, 2, 49, 1, 2, 1, 38],
        [10, 98, 2, 100, 1, 2, 1, 44],
        [12, 71, 2, 144, 2, 2, 1, 64],
        [10, 49, 2, 100, 2, 2, 1, 88],
        [30, 299, 2, 900, 3, 3, 1, 117],
        [7, 170, 3, 343, 2, 3, 1, 255],
        [10, 997, 3, 1000, 1, 3, 1, 439],
        [10, 996, 3, 1000, 1, 4, 1, 464],
        [12, 575, 3, 1728, 3, 3, 1, 1053],
        [7, 1199, 4, 2401, 2, 3, 1, 1284],
        [10, 294, 4, 10000, 34, 4, 1, 1776],
        [7, 46, 2, 49, 1, 3, 2, 2171],
        [7, 141, 4, 2401, 17, 4, 1, 2353],
        [10, 97, 2, 100, 1, 3, 2, 4217],
        [12, 146, 4, 20736, 142, 4, 1, 4352],
        [10, 769, 4, 10000, 13, 3, 1, 4707],
        [7, 345, 6, 117649, 341, 4, 1, 5534],
        [7, 542, 5, 16807, 31, 5, 1, 8472],
        [12, 47, 2, 144, 3, 3, 2, 9639],
        [30, 794, 3, 27000, 34, 4, 1, 12776],
        [7, 113, 3, 343, 3, 4, 2, 13444],
        [12, 691, 4, 20736, 30, 6, 1, 20736],
        [10, 578, 5, 100000, 173, 6, 1, 26432],
        [10, 277, 5, 100000, 361, 3, 1, 31479],
        [7, 669, 7, 823543, 1231, 4, 1, 32398],
    ]

    lane_ids = [
        row["program_lane_id"]
        for row in rows
        if row["group"] == "observability_program_lane"
    ]
    assert lane_ids == [
        "composite68_shape17_obstruction_lane",
        "shape187_same_position_scaling_lane",
        "shape13_mod_stable_carry_loss_lane",
        "unresolved_hidden_conflict_lane",
        "positive_reconstruction_lane",
    ]
    positive_lane = next(
        row
        for row in rows
        if row["group"] == "observability_program_lane"
        and row["program_lane_id"] == "positive_reconstruction_lane"
    )
    assert positive_lane["proof_covered_count"] == 26
    assert positive_lane["source_pinned_positive_reconstruction_cases"] == 26
    assert positive_lane["empirical_positive_reconstruction_candidates"] > 0
    assert positive_lane["injective_window_criterion_cases"] == positive_lane["member_count"]
    assert positive_lane["source_pinned_injective_window_criterion_cases"] == 26
    assert positive_lane["recommended_next_observability_task"] == (
        "prove_or_reject_same_base_block_remainder_power_no_collision_family"
    )

    n340_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 7
        and row["n"] == 340
    )
    assert n340_case["positive_reconstruction_frontier_covered"] is True
    assert n340_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n340_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base7K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )

    base7_stride6_k4_moduli = [
        23,
        55,
        69,
        115,
        155,
        165,
        253,
        345,
        465,
        713,
        759,
        1265,
        1705,
        2139,
        3565,
        3795,
        5115,
        7843,
        10695,
        23529,
        39215,
        117645,
    ]
    n465_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 7
        and row["n"] == 465
    )
    assert n465_case["positive_reconstruction_source_pinned"] is False
    assert n465_case["positive_reconstruction_frontier_covered"] is True
    assert n465_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n465_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n465_case["positive_reconstruction_frontier_coverage_moduli"] == (
        base7_stride6_k4_moduli
    )
    assert n465_case["remainder_power_residue_window"] == [
        1,
        4,
        16,
        64,
        256,
        94,
        376,
        109,
    ]

    wide_rows = observability_program_atlas_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=80,
    )
    base7_stride6_k3_moduli = [59, 118, 997, 1994, 58823, 117646]
    n997_base7_case = next(
        row
        for row in wide_rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 7
        and row["m"] == 6
        and row["n"] == 997
    )
    assert n997_base7_case["positive_reconstruction_source_pinned"] is False
    assert n997_base7_case["positive_reconstruction_frontier_covered"] is True
    assert n997_base7_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n997_base7_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base7Stride6K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n997_base7_case["positive_reconstruction_frontier_coverage_moduli"] == (
        base7_stride6_k3_moduli
    )
    assert n997_base7_case["remainder_power_residue_window"] == [
        1,
        3,
        9,
        27,
        81,
        243,
        729,
        193,
    ]

    n59_case = next(
        row
        for row in wide_rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 7
        and row["m"] == 6
        and row["n"] == 59
    )
    assert n59_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base7Stride6K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n59_case["positive_reconstruction_frontier_coverage_moduli"] == (
        base7_stride6_k3_moduli
    )

    base10_stride5_k6_moduli = [
        17,
        34,
        173,
        289,
        346,
        578,
        2941,
        5882,
        49997,
        99994,
    ]
    n289_case = next(
        row
        for row in wide_rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 10
        and row["m"] == 5
        and row["n"] == 289
    )
    assert n289_case["positive_reconstruction_source_pinned"] is False
    assert n289_case["positive_reconstruction_frontier_covered"] is True
    assert n289_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n289_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base10Stride5K6PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n289_case["positive_reconstruction_frontier_coverage_moduli"] == (
        base10_stride5_k6_moduli
    )
    assert n289_case["remainder_power_residue_window"] == [
        1,
        6,
        36,
        216,
        140,
        262,
        127,
        184,
    ]

    n226_case = next(
        row
        for row in wide_rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 12
        and row["m"] == 5
        and row["n"] == 226
    )
    assert n226_case["positive_reconstruction_rank"] == 57
    assert n226_case["positive_reconstruction_source_pinned"] is True
    assert n226_case["positive_reconstruction_namespace"] == "QRTour.FutureBase12N226"
    assert n226_case["positive_reconstruction_frontier_covered"] is True
    assert n226_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n226_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
    )
    assert n226_case["remainder_power_residue_window"] == [
        1,
        6,
        36,
        216,
        166,
        92,
        100,
        148,
    ]
    assert n226_case["raw_coefficient_window"] == [
        1101,
        6606,
        39636,
        237816,
        1426896,
        8561376,
        51368256,
        308209536,
    ]

    n338_case = next(
        row
        for row in wide_rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 7
        and row["m"] == 3
        and row["n"] == 338
    )
    assert n338_case["positive_reconstruction_rank"] == 58
    assert n338_case["positive_reconstruction_source_pinned"] is True
    assert n338_case["positive_reconstruction_namespace"] == "QRTour.FutureBase7N338"
    assert n338_case["positive_reconstruction_frontier_covered"] is True
    assert n338_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n338_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
    )
    assert n338_case["remainder_power_residue_window"] == [
        1,
        5,
        25,
        125,
        287,
        83,
        77,
        47,
    ]
    assert n338_case["raw_coefficient_window"] == [
        1,
        5,
        25,
        125,
        625,
        3125,
        15625,
        78125,
    ]

    n149_case = next(
        row
        for row in wide_rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 12
        and row["m"] == 5
        and row["n"] == 149
    )
    assert n149_case["positive_reconstruction_rank"] == 59
    assert n149_case["positive_reconstruction_source_pinned"] is True
    assert n149_case["positive_reconstruction_namespace"] == "QRTour.FutureBase12N149"
    assert n149_case["positive_reconstruction_frontier_covered"] is True
    assert n149_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n149_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
    )
    assert n149_case["remainder_power_residue_window"] == [
        1,
        2,
        4,
        8,
        16,
        32,
        64,
        128,
    ]
    assert n149_case["remainder_power_unreduced_window"] == [
        1,
        2,
        4,
        8,
        16,
        32,
        64,
        128,
    ]
    assert n149_case["raw_coefficient_window"] == [
        1670,
        3340,
        6680,
        13360,
        26720,
        53440,
        106880,
        213760,
    ]
    assert n149_case["positive_reconstruction_hyp_remainder_power_residue_no_wrap"] is True
    assert n149_case["positive_reconstruction_power_no_wrap_criterion_status"] == (
        "source_pinned_power_no_wrap_sufficient_criterion_satisfied"
    )

    base12_stride5_k3_moduli = [
        17,
        41,
        51,
        119,
        123,
        287,
        289,
        357,
        697,
        861,
        867,
        2023,
        2091,
        4879,
        6069,
        11849,
        14637,
        35547,
        82943,
        248829,
    ]
    n289_base12_case = next(
        row
        for row in wide_rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 12
        and row["m"] == 5
        and row["n"] == 289
    )
    assert n289_base12_case["positive_reconstruction_rank"] == 60
    assert n289_base12_case["positive_reconstruction_source_pinned"] is False
    assert n289_base12_case["positive_reconstruction_frontier_covered"] is True
    assert n289_base12_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n289_base12_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base12Stride5K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n289_base12_case["positive_reconstruction_frontier_coverage_moduli"] == (
        base12_stride5_k3_moduli
    )
    assert n289_base12_case["remainder_power_residue_window"] == [
        1,
        3,
        9,
        27,
        81,
        243,
        151,
        164,
    ]
    assert n289_base12_case["raw_coefficient_window"] == [
        861,
        2583,
        7749,
        23247,
        69741,
        209223,
        627669,
        1883007,
    ]

    base10_stride5_k4_moduli = [
        641,
        1282,
        1923,
        2564,
        3846,
        7692,
        8333,
        16666,
        24999,
        33332,
        49998,
        99996,
    ]
    n641_case = next(
        row
        for row in wide_rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 10
        and row["m"] == 5
        and row["n"] == 641
    )
    assert n641_case["positive_reconstruction_rank"] == 61
    assert n641_case["positive_reconstruction_source_pinned"] is False
    assert n641_case["positive_reconstruction_frontier_covered"] is True
    assert n641_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n641_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base10Stride5K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n641_case["positive_reconstruction_frontier_coverage_moduli"] == (
        base10_stride5_k4_moduli
    )
    assert n641_case["remainder_power_residue_window"] == [
        1,
        4,
        16,
        64,
        256,
        383,
        250,
        359,
    ]
    assert n641_case["raw_coefficient_window"] == [
        156,
        624,
        2496,
        9984,
        39936,
        159744,
        638976,
        2555904,
    ]

    n997_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 10
        and row["n"] == 997
    )
    assert n997_case["positive_reconstruction_source_pinned"] is True
    assert n997_case["positive_reconstruction_namespace"] == "QRTour.FutureBase10N997"
    assert n997_case["positive_reconstruction_frontier_covered"] is True
    assert n997_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )

    n897_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 30
        and row["n"] == 897
    )
    assert n897_case["positive_reconstruction_source_pinned"] is False
    assert n897_case["positive_reconstruction_frontier_covered"] is True
    assert n897_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n897_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base30K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n897_case["positive_reconstruction_frontier_coverage_moduli"] == (
        [23, 69, 299, 897]
    )

    n498_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 10
        and row["n"] == 498
    )
    assert n498_case["positive_reconstruction_source_pinned"] is False
    assert n498_case["positive_reconstruction_frontier_covered"] is True
    assert n498_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n498_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n498_case["positive_reconstruction_frontier_coverage_moduli"] == (
        [83, 166, 249, 332, 498, 996]
    )

    n575_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 12
        and row["n"] == 575
    )
    assert n575_case["positive_reconstruction_source_pinned"] is True
    assert n575_case["positive_reconstruction_namespace"] == "QRTour.FutureBase12N575"
    assert n575_case["positive_reconstruction_frontier_covered"] is True
    assert n575_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )

    n1199_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 7
        and row["n"] == 1199
    )
    assert n1199_case["positive_reconstruction_source_pinned"] is True
    assert n1199_case["positive_reconstruction_namespace"] == "QRTour.FutureBase7N1199"
    assert n1199_case["positive_reconstruction_frontier_covered"] is True
    assert n1199_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n1199_case["remainder_power_residue_window"] == [
        1,
        3,
        9,
        27,
        81,
        243,
        729,
        988,
    ]

    n294_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 10
        and row["n"] == 294
    )
    assert n294_case["positive_reconstruction_source_pinned"] is True
    assert n294_case["positive_reconstruction_namespace"] == "QRTour.FutureBase10N294"
    assert n294_case["positive_reconstruction_frontier_covered"] is True
    assert n294_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n294_case["preperiod_digits"] == 1
    assert n294_case["periodic_modulus"] == 147
    assert n294_case["remainder_power_residue_window"] == [
        1,
        4,
        16,
        64,
        256,
        142,
        274,
        214,
    ]

    n714_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 10
        and row["n"] == 714
    )
    assert n714_case["positive_reconstruction_source_pinned"] is False
    assert n714_case["positive_reconstruction_frontier_covered"] is True
    assert n714_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n714_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base10Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n714_case["positive_reconstruction_frontier_coverage_moduli"] == (
        [49, 98, 119, 147, 196, 238, 294, 357, 476, 588, 714, 833]
    )

    n146_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 12
        and row["n"] == 146
    )
    assert n146_case["positive_reconstruction_source_pinned"] is True
    assert n146_case["positive_reconstruction_namespace"] == "QRTour.FutureBase12N146"
    assert n146_case["positive_reconstruction_frontier_covered"] is True
    assert n146_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n146_case["preperiod_digits"] == 1
    assert n146_case["periodic_modulus"] == 73
    assert n146_case["remainder_power_residue_window"] == [
        1,
        4,
        16,
        64,
        110,
        2,
        8,
        32,
    ]

    n769_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 10
        and row["n"] == 769
    )
    assert n769_case["positive_reconstruction_source_pinned"] is True
    assert n769_case["positive_reconstruction_namespace"] == "QRTour.FutureBase10N769"
    assert n769_case["positive_reconstruction_frontier_covered"] is True
    assert n769_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n769_case["preperiod_digits"] == 0
    assert n769_case["periodic_modulus"] == 769
    assert n769_case["remainder_power_residue_window"] == [
        1,
        3,
        9,
        27,
        81,
        243,
        729,
        649,
    ]

    n109_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 7
        and row["n"] == 109
    )
    assert n109_case["positive_reconstruction_source_pinned"] is False
    assert n109_case["positive_reconstruction_frontier_covered"] is True
    assert n109_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n109_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n109_case["positive_reconstruction_frontier_coverage_moduli"] == (
        [109, 218, 1199, 2398]
    )
    assert n109_case["remainder_power_residue_window"] == [
        1,
        3,
        9,
        27,
        81,
        25,
        75,
        7,
    ]

    n218_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 7
        and row["n"] == 218
    )
    assert n218_case["positive_reconstruction_source_pinned"] is False
    assert n218_case["positive_reconstruction_frontier_covered"] is True
    assert n218_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n218_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n218_case["positive_reconstruction_frontier_coverage_moduli"] == (
        [109, 218, 1199, 2398]
    )

    n46_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 7
        and row["n"] == 46
    )
    assert n46_case["positive_reconstruction_source_pinned"] is True
    assert n46_case["positive_reconstruction_namespace"] == "QRTour.FutureBase7N46"
    assert n46_case["positive_reconstruction_frontier_covered"] is True
    assert n46_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n46_case["remainder_power_residue_window"] == [
        1,
        3,
        9,
        27,
        35,
        13,
        39,
        25,
    ]

    n75_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 12
        and row["n"] == 75
    )
    assert n75_case["positive_reconstruction_source_pinned"] is False
    assert n75_case["positive_reconstruction_frontier_covered"] is True
    assert n75_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n75_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n75_case["positive_reconstruction_frontier_coverage_moduli"] == (
        [23, 25, 69, 75, 115, 345, 575, 1725]
    )

    n73_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 12
        and row["n"] == 73
    )
    assert n73_case["positive_reconstruction_source_pinned"] is False
    assert n73_case["positive_reconstruction_frontier_covered"] is True
    assert n73_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n73_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n73_case["positive_reconstruction_frontier_coverage_moduli"] == (
        [71, 73, 142, 146, 284, 292, 5183, 10366, 20732]
    )
    assert n73_case["remainder_power_residue_window"] == [
        1,
        4,
        16,
        64,
        37,
        2,
        8,
        32,
    ]
    assert n73_case["raw_coefficient_window"] == [
        284,
        1136,
        4544,
        18176,
        72704,
        290816,
        1163264,
        4653056,
    ]

    n47_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 12
        and row["n"] == 47
    )
    assert n47_case["positive_reconstruction_source_pinned"] is True
    assert n47_case["positive_reconstruction_namespace"] == "QRTour.FutureBase12N47"
    assert n47_case["positive_reconstruction_frontier_covered"] is True
    assert n47_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n47_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
    )
    assert n47_case["remainder_power_residue_window"] == [
        1,
        3,
        9,
        27,
        34,
        8,
        24,
        25,
    ]
    assert n47_case["raw_coefficient_window"] == [
        3,
        9,
        27,
        81,
        243,
        729,
        2187,
        6561,
    ]

    n141_base12_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 12
        and row["n"] == 141
    )
    assert n141_base12_case["positive_reconstruction_source_pinned"] is False
    assert n141_base12_case["positive_reconstruction_frontier_covered"] is True
    assert n141_base12_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n141_base12_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n141_base12_case["positive_reconstruction_frontier_coverage_moduli"] == (
        [47, 141]
    )
    assert n141_base12_case["remainder_power_residue_window"] == [
        1,
        3,
        9,
        27,
        81,
        102,
        24,
        72,
    ]
    assert n141_base12_case["raw_coefficient_window"] == [
        1,
        3,
        9,
        27,
        81,
        243,
        729,
        2187,
    ]

    n794_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 30
        and row["n"] == 794
    )
    assert n794_case["positive_reconstruction_source_pinned"] is True
    assert n794_case["positive_reconstruction_namespace"] == "QRTour.FutureBase30N794"
    assert n794_case["positive_reconstruction_frontier_covered"] is True
    assert n794_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n794_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
    )
    assert n794_case["remainder_power_residue_window"] == [
        1,
        4,
        16,
        64,
        256,
        230,
        126,
        504,
    ]
    assert n794_case["raw_coefficient_window"] == [
        34,
        136,
        544,
        2176,
        8704,
        34816,
        139264,
        557056,
    ]

    n113_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 7
        and row["n"] == 113
    )
    assert n113_case["positive_reconstruction_source_pinned"] is True
    assert n113_case["positive_reconstruction_namespace"] == "QRTour.FutureBase7N113"
    assert n113_case["positive_reconstruction_frontier_covered"] is True
    assert n113_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n113_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
    )
    assert n113_case["remainder_power_residue_window"] == [
        1,
        4,
        16,
        64,
        30,
        7,
        28,
        112,
    ]
    assert n113_case["raw_coefficient_window"] == [
        3,
        12,
        48,
        192,
        768,
        3072,
        12288,
        49152,
    ]

    n691_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 12
        and row["n"] == 691
    )
    assert n691_case["positive_reconstruction_source_pinned"] is True
    assert n691_case["positive_reconstruction_namespace"] == "QRTour.FutureBase12N691"
    assert n691_case["positive_reconstruction_frontier_covered"] is True
    assert n691_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n691_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
    )
    assert n691_case["remainder_power_residue_window"] == [
        1,
        6,
        36,
        216,
        605,
        175,
        359,
        81,
    ]
    assert n691_case["raw_coefficient_window"] == [
        30,
        180,
        1080,
        6480,
        38880,
        233280,
        1399680,
        8398080,
    ]

    n578_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 10
        and row["n"] == 578
    )
    assert n578_case["positive_reconstruction_source_pinned"] is True
    assert n578_case["positive_reconstruction_namespace"] == "QRTour.FutureBase10N578"
    assert n578_case["positive_reconstruction_frontier_covered"] is True
    assert n578_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n578_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
    )
    assert n578_case["remainder_power_residue_window"] == [
        1,
        6,
        36,
        216,
        140,
        262,
        416,
        184,
    ]
    assert n578_case["raw_coefficient_window"] == [
        173,
        1038,
        6228,
        37368,
        224208,
        1345248,
        8071488,
        48428928,
    ]

    n277_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 10
        and row["n"] == 277
    )
    assert n277_case["positive_reconstruction_source_pinned"] is True
    assert n277_case["positive_reconstruction_namespace"] == "QRTour.FutureBase10N277"
    assert n277_case["positive_reconstruction_frontier_covered"] is True
    assert n277_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n277_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
    )
    assert n277_case["remainder_power_residue_window"] == [
        1,
        3,
        9,
        27,
        81,
        243,
        175,
        248,
    ]
    assert n277_case["raw_coefficient_window"] == [
        361,
        1083,
        3249,
        9747,
        29241,
        87723,
        263169,
        789507,
    ]

    n669_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 7
        and row["n"] == 669
    )
    assert n669_case["positive_reconstruction_source_pinned"] is True
    assert n669_case["positive_reconstruction_namespace"] == "QRTour.FutureBase7N669"
    assert n669_case["positive_reconstruction_frontier_covered"] is True
    assert n669_case["positive_reconstruction_frontier_coverage_status"] == (
        "source_pinned_finite_factor_through_theorem"
    )
    assert n669_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
    )
    assert n669_case["remainder_power_residue_window"] == [
        1,
        4,
        16,
        64,
        256,
        355,
        82,
        328,
    ]
    assert n669_case["raw_coefficient_window"] == [
        1231,
        4924,
        19696,
        78784,
        315136,
        1260544,
        5042176,
        20168704,
    ]

    n397_case = next(
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
        and row["base"] == 30
        and row["n"] == 397
    )
    assert n397_case["positive_reconstruction_source_pinned"] is False
    assert n397_case["positive_reconstruction_frontier_covered"] is True
    assert n397_case["positive_reconstruction_frontier_coverage_status"] == (
        "lean_proved_explicit_divisor_family_criterion"
    )
    assert n397_case["positive_reconstruction_frontier_coverage_theorem"] == (
        "QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert n397_case["positive_reconstruction_frontier_coverage_moduli"] == (
        [397, 794, 1588, 6749, 13498, 26996]
    )
    assert n397_case["remainder_power_residue_window"] == [
        1,
        4,
        16,
        64,
        256,
        230,
        126,
        107,
    ]
    assert n397_case["raw_coefficient_window"] == [
        68,
        272,
        1088,
        4352,
        17408,
        69632,
        278528,
        1114112,
    ]

    family_ids = {
        row["program_family_id"]
        for row in rows
        if row["group"] == "observability_program_family"
    }
    assert {
        "shape17_k4_composite68_proof_backed_obstruction",
        "shape187_k188_same_position_scaling",
        "shape13_k4_mod_stable_carry_loss",
        "unresolved_hidden_conflict_source_family",
        "positive_functional_frontier_signature_family",
    } <= family_ids

    candidates = [
        row
        for row in rows
        if row["group"] == "observability_positive_reconstruction_candidate"
    ]
    by_key = {(row["base"], row["n"]): row for row in candidates}
    assert {
        (12, 142),
        (7, 47),
        (10, 98),
        (12, 71),
        (10, 49),
        (30, 299),
        (7, 170),
        (7, 340),
        (10, 498),
        (12, 75),
        (12, 575),
        (7, 1199),
        (10, 294),
        (7, 46),
        (7, 141),
        (10, 714),
        (12, 146),
        (10, 769),
        (7, 345),
        (7, 465),
        (7, 542),
        (12, 73),
        (12, 47),
        (12, 141),
        (30, 794),
        (7, 113),
        (12, 691),
        (10, 578),
        (10, 277),
        (7, 669),
        (30, 397),
        (7, 109),
        (7, 218),
        (10, 97),
        (10, 996),
    } <= set(by_key)
    assert any(
        row["positive_reconstruction_source_pinned"] is False
        for row in candidates
    )
    expected_source_pins = {
        (10, 97): (
            "QRTour.Prime97",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two",
            [1, 3, 9, 27, 81, 49, 50, 53],
            [1, 3, 9, 27, 81, 243, 729, 2187],
        ),
        (10, 98): (
            "QRTour.FutureBase10N98",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 2, 4, 8, 16, 32, 64, 30],
            [1, 2, 4, 8, 16, 32, 64, 128],
        ),
        (12, 142): (
            "QRTour.FutureBase12N142",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 2, 4, 8, 16, 32, 64, 128],
            [1, 2, 4, 8, 16, 32, 64, 128],
        ),
        (7, 47): (
            "QRTour.FutureBase7N47",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 2, 4, 8, 16, 32, 17, 34],
            [1, 2, 4, 8, 16, 32, 64, 128],
        ),
        (12, 71): (
            "QRTour.FutureBase12N71",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 2, 4, 8, 16, 32, 64, 57],
            [2, 4, 8, 16, 32, 64, 128, 256],
        ),
        (10, 49): (
            "QRTour.FutureBase10N49",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 2, 4, 8, 16, 32, 15, 30],
            [2, 4, 8, 16, 32, 64, 128, 256],
        ),
        (30, 299): (
            "QRTour.FutureBase30N299",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 3, 9, 27, 81, 243, 131, 94],
            [3, 9, 27, 81, 243, 729, 2187, 6561],
        ),
        (7, 170): (
            "QRTour.FutureBase7N170",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 3, 9, 27, 81, 73, 49, 147],
            [2, 6, 18, 54, 162, 486, 1458, 4374],
        ),
        (12, 575): (
            "QRTour.FutureBase12N575",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 3, 9, 27, 81, 243, 154, 462],
            [3, 9, 27, 81, 243, 729, 2187, 6561],
        ),
        (7, 1199): (
            "QRTour.FutureBase7N1199",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 3, 9, 27, 81, 243, 729, 988],
            [2, 6, 18, 54, 162, 486, 1458, 4374],
        ),
        (10, 294): (
            "QRTour.FutureBase10N294",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 4, 16, 64, 256, 142, 274, 214],
            [34, 136, 544, 2176, 8704, 34816, 139264, 557056],
        ),
        (7, 46): (
            "QRTour.FutureBase7N46",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two",
            [1, 3, 9, 27, 35, 13, 39, 25],
            [1, 3, 9, 27, 81, 243, 729, 2187],
        ),
        (7, 141): (
            "QRTour.FutureBase7N141",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 4, 16, 64, 115, 37, 7, 28],
            [17, 68, 272, 1088, 4352, 17408, 69632, 278528],
        ),
        (12, 146): (
            "QRTour.FutureBase12N146",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 4, 16, 64, 110, 2, 8, 32],
            [142, 568, 2272, 9088, 36352, 145408, 581632, 2326528],
        ),
        (10, 769): (
            "QRTour.FutureBase10N769",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 3, 9, 27, 81, 243, 729, 649],
            [13, 39, 117, 351, 1053, 3159, 9477, 28431],
        ),
        (7, 345): (
            "QRTour.FutureBase7N345",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 4, 16, 64, 256, 334, 301, 169],
            [341, 1364, 5456, 21824, 87296, 349184, 1396736, 5586944],
        ),
        (7, 542): (
            "QRTour.FutureBase7N542",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 5, 25, 125, 83, 415, 449, 77],
            [31, 155, 775, 3875, 19375, 96875, 484375, 2421875],
        ),
        (30, 794): (
            "QRTour.FutureBase30N794",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 4, 16, 64, 256, 230, 126, 504],
            [34, 136, 544, 2176, 8704, 34816, 139264, 557056],
        ),
        (7, 113): (
            "QRTour.FutureBase7N113",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two",
            [1, 4, 16, 64, 30, 7, 28, 112],
            [3, 12, 48, 192, 768, 3072, 12288, 49152],
        ),
        (12, 691): (
            "QRTour.FutureBase12N691",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 6, 36, 216, 605, 175, 359, 81],
            [30, 180, 1080, 6480, 38880, 233280, 1399680, 8398080],
        ),
        (10, 578): (
            "QRTour.FutureBase10N578",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 6, 36, 216, 140, 262, 416, 184],
            [173, 1038, 6228, 37368, 224208, 1345248, 8071488, 48428928],
        ),
        (10, 277): (
            "QRTour.FutureBase10N277",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 3, 9, 27, 81, 243, 175, 248],
            [361, 1083, 3249, 9747, 29241, 87723, 263169, 789507],
        ),
        (7, 669): (
            "QRTour.FutureBase7N669",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 4, 16, 64, 256, 355, 82, 328],
            [1231, 4924, 19696, 78784, 315136, 1260544, 5042176, 20168704],
        ),
        (12, 47): (
            "QRTour.FutureBase12N47",
            "coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two",
            "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two",
            [1, 3, 9, 27, 34, 8, 24, 25],
            [3, 9, 27, 81, 243, 729, 2187, 6561],
        ),
        (10, 996): (
            "QRTour.Composite996",
            "actual996_stateAlignments_remainderToCoefficientFunctional_eight_one",
            "actual996_stateAlignments_remainderToCoefficientFactorsThrough_eight_one",
            [1, 4, 16, 64, 256, 28, 112, 448],
            [1, 4, 16, 64, 256, 1024, 4096, 16384],
        ),
    }
    for (
        key,
        (
            namespace,
            functional_name,
            factor_through_name,
            remainder_window,
            coefficient_window,
        ),
    ) in expected_source_pins.items():
        row = by_key[key]
        assert row["positive_reconstruction_source_pinned"] is True
        assert row["positive_reconstruction_source_status"] == "source_pinned_existing_theorem"
        assert row["positive_reconstruction_lean_support_status"] == (
            "source_pinned_finite_factor_through_theorem"
        )
        assert row["positive_reconstruction_namespace"] == namespace
        assert row["positive_reconstruction_module_path"] == "lean/QRTour/Examples.lean"
        assert row["positive_reconstruction_functional_theorem"] == functional_name
        assert row["positive_reconstruction_factor_through_theorem"] == factor_through_name
        assert row["positive_reconstruction_qualified_theorem_names"] == [
            f"{namespace}.{functional_name}",
            f"{namespace}.{factor_through_name}",
        ]
        assert row["remainder_state_window"] == remainder_window
        assert row["raw_coefficient_window"] == coefficient_window
        assert row["remainder_power_residue_window"] == remainder_window
        assert row["remainder_state_window_injective"] is True
        assert row["positive_reconstruction_power_no_collision_criterion_id"] == (
            "finite_remainder_power_residue_no_collision"
        )
        assert row["positive_reconstruction_hyp_remainder_power_residue_window_injective"] is True
        assert row["positive_reconstruction_power_no_collision_criterion_status"] == (
            "source_pinned_power_no_collision_sufficient_criterion_satisfied"
        )
        assert row["positive_reconstruction_arithmetic_criterion_id"] == (
            "finite_remainder_state_injective_on_window"
        )
        assert row["positive_reconstruction_arithmetic_criterion_status"] == (
            "source_pinned_sufficient_criterion_satisfied"
        )
        assert row["positive_reconstruction_hyp_remainder_state_window_injective"] is True
        assert row["positive_reconstruction_criterion_failure_reason"] is None
    assert by_key[(7, 340)]["positive_reconstruction_source_pinned"] is False
    assert by_key[(7, 340)]["positive_reconstruction_power_no_collision_criterion_status"] == (
        "empirical_power_no_collision_sufficient_criterion_satisfied"
    )
    for row in candidates:
        assert row["coefficient_observability_class"] == "coefficient_functional_frontier"
        assert row["raw_coefficient_nat_functional"] is True
        assert row["coefficient_mod_block_base_functional"] is True
        assert row["carried_block_value_functional"] is True
        assert row["carry_state_functional"] is True
        assert row["positive_reconstruction_arithmetic_criterion_id"] == (
            "finite_remainder_state_injective_on_window"
        )
        assert row["positive_reconstruction_hyp_remainder_state_window_injective"] is True
        assert row["positive_reconstruction_power_no_collision_criterion_id"] == (
            "finite_remainder_power_residue_no_collision"
        )
        assert row["remainder_power_residue_window"] == row["remainder_state_window"]
        assert row["positive_reconstruction_hyp_remainder_power_residue_window_injective"] is True
        assert row["open_boundary_ids"] == [
            "small_k_visibility_threshold",
            "carry_dfa_factorization",
        ]

    hidden_keys = {
        (row.get("base"), row.get("n"))
        for row in rows
        if row.get("coefficient_observability_class") == "hidden_coefficient_conflict"
    }
    assert not hidden_keys & set(by_key)


def test_observability_target_split_rows_expand_target_matrix_for_anchors() -> None:
    rows = observability_target_split_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )

    assert rows[0]["group"] == "observability_target_split_summary"
    assert rows[0]["observability_targets"] == [
        "raw_coefficient_nat",
        "coefficient_mod_block_base",
        "carried_block_value",
        "carry_state",
        "remainder_state",
        "displayed_prefix",
    ]
    assert rows[0]["observability_boundary_status"] == (
        "empirical_open_boundary_target_split_tooling"
    )
    assert rows[0]["open_boundary_ids"] == [
        "small_k_visibility_threshold",
        "carry_dfa_factorization",
    ]

    case_rows = [
        row for row in rows if row["group"] == "observability_target_split_case"
    ]
    by_key = {
        (row["base"], row["n"], row["observability_target_id"]): row
        for row in case_rows
    }

    for key in [(10, 68), (30, 68)]:
        raw = by_key[(*key, "raw_coefficient_nat")]
        assert raw["target_observability_status"] == "factor_through_obstructed"
        assert raw["target_functional"] is False
        assert raw["factor_through_surface"] == "remainder_state_to_raw_coefficient_nat"
        assert raw["open_boundary_ids"] == [
            "small_k_visibility_threshold",
            "carry_dfa_factorization",
        ]

        carried = by_key[(*key, "carried_block_value")]
        assert carried["target_observability_status"] == (
            "functional_output_hides_raw_coefficient_conflict"
        )
        assert carried["target_functional"] is True
        assert carried["target_hides_raw_coefficient_conflict"] is True
        assert carried["next_target_task"] == "classify_hidden_output_normalization"

        displayed = by_key[(*key, "displayed_prefix")]
        assert displayed["target_observability_status"] == (
            "certified_window_output_agreement"
        )
        assert displayed["target_functional"] is None
        assert displayed["factor_through_surface"] == (
            "window_level_certificate_not_pointwise_factor_through"
        )

    for key in [(10, 97), (10, 996)]:
        raw = by_key[(*key, "raw_coefficient_nat")]
        coefficient_mod = by_key[(*key, "coefficient_mod_block_base")]
        assert raw["target_observability_status"] == "factor_through_candidate"
        assert raw["target_functional"] is True
        assert coefficient_mod["target_observability_status"] == "factor_through_candidate"
        assert coefficient_mod["target_functional"] is True


def test_observability_target_signature_rows_group_loss_profiles() -> None:
    rows = observability_target_signature_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )

    assert rows[0]["group"] == "observability_target_signature_summary"
    assert rows[0]["observability_boundary_status"] == (
        "empirical_open_boundary_target_signature_tooling"
    )
    assert rows[0]["hidden_output_signature_families"] >= 1
    assert rows[0]["functional_frontier_signature_families"] >= 1
    assert rows[0]["open_boundary_ids"] == [
        "small_k_visibility_threshold",
        "carry_dfa_factorization",
    ]

    families = [
        row
        for row in rows
        if row["group"] == "observability_target_signature_family"
    ]
    hidden = next(row for row in families if row["contains_base10_68"])
    assert hidden["contains_base30_68"] is True
    assert hidden["signature_family_class"] == (
        "raw_coefficient_obstructed_carried_output_hidden"
    )
    assert hidden["raw_coefficient_nat_status"] == "factor_through_obstructed"
    assert hidden["coefficient_mod_block_base_status"] == "factor_through_obstructed"
    assert hidden["carried_block_value_status"] == (
        "functional_output_hides_raw_coefficient_conflict"
    )
    assert hidden["carried_block_value_functional"] is True
    assert hidden["first_nonfunctional_pointwise_target"] == "raw_coefficient_nat"
    assert hidden["first_nonfunctional_pointwise_target_after_raw"] == (
        "coefficient_mod_block_base"
    )
    assert hidden["raw_coefficient_obstructed_cases"] == hidden["member_count"]
    assert hidden["carried_block_value_hidden_cases"] == hidden["member_count"]
    assert hidden["lean_ready_hidden_conflict_cases"] >= 2
    assert [10, 68, 4, 10000, 147, 4, 1, 6208] in hidden["member_tuple_sample"]

    functional = next(row for row in families if row["contains_base10_97"])
    assert functional["contains_base10_996"] is True
    assert functional["signature_family_class"] == (
        "all_pointwise_targets_functional_frontier"
    )
    assert functional["raw_coefficient_nat_status"] == "factor_through_candidate"
    assert functional["coefficient_mod_block_base_status"] == "factor_through_candidate"
    assert functional["carried_block_value_status"] == "factor_through_candidate"
    assert functional["carry_state_status"] == "factor_through_candidate"
    assert functional["first_nonfunctional_pointwise_target"] is None
    assert functional["functional_frontier_cases"] == functional["member_count"]


def test_observability_mod_stable_carry_loss_rows_mine_second_hidden_signature() -> None:
    rows = observability_mod_stable_carry_loss_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )

    assert rows[0]["group"] == "observability_mod_stable_carry_loss_summary"
    assert rows[0]["total_mod_stable_carry_loss_cases"] == 6
    assert rows[0]["bases_observed"] == [12, 30]
    assert rows[0]["first_mod_stable_carry_loss_tuple"] == [
        30,
        26,
        1,
        30,
        1,
        4,
        5,
        11927264,
    ]
    assert rows[0]["observability_boundary_status"] == (
        "empirical_open_boundary_mod_stable_carry_loss_tooling"
    )
    assert rows[0]["open_boundary_ids"] == [
        "small_k_visibility_threshold",
        "carry_dfa_factorization",
    ]

    case_rows = [
        row
        for row in rows
        if row["group"] == "observability_mod_stable_carry_loss_case"
    ]
    assert len(case_rows) == 6
    first = case_rows[0]
    assert first["base"] == 30
    assert first["n"] == 26
    assert first["mod_stable_carry_loss_rank"] == 1
    assert first["target_signature_family_class"] == "mod_stable_carry_state_loss"
    assert first["source_symmetry_signature"] == (
        "periodic_modulus=13;k=4;position_gap=6"
    )
    assert first["raw_coefficient_nat_observability_status"] == (
        "factor_through_obstructed"
    )
    assert first["coefficient_mod_block_base_observability_status"] == (
        "factor_through_candidate"
    )
    assert first["carried_block_value_observability_status"] == (
        "functional_output_hides_raw_coefficient_conflict"
    )
    assert first["carry_state_observability_status"] == "factor_through_obstructed"
    assert first["coefficient_mod_block_base_preserved"] is True
    assert first["raw_coefficient_information_lost"] is True
    assert first["carried_output_hides_raw_conflict"] is True
    assert first["carry_state_information_lost"] is True
    assert first["first_nonfunctional_pointwise_target_after_raw"] == "carry_state"
    assert first["conflict_remainder_state"] == 4
    assert first["conflict_positions"] == [1, 7]
    assert first["conflict_coefficients"] == [4, 16384]
    assert first["conflict_carry_states"] == [0, 2520]
    assert first["conflict_block_values"] == [4, 4]

    assert all(row["coefficient_mod_block_base_functional"] is True for row in case_rows)
    assert all(row["remainder_to_carry_functional"] is False for row in case_rows)
    assert not any(row["n"] in {68, 97, 996} for row in case_rows)


def test_observability_shape13_k4_mod_stable_carry_loss_classifies_pair() -> None:
    rows = observability_shape13_k4_mod_stable_carry_loss_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )

    assert rows[0]["group"] == (
        "observability_shape13_k4_mod_stable_carry_loss_summary"
    )
    assert rows[0]["source_symmetry_signature"] == (
        "periodic_modulus=13;k=4;position_gap=6"
    )
    assert rows[0]["family_class"] == "shape13_k4_mod_stable_carry_loss_shift"
    assert rows[0]["total_members"] == 2
    assert rows[0]["n_values"] == [13, 26]
    assert rows[0]["bases_observed"] == [30]
    assert rows[0]["source_core_present"] is True
    assert rows[0]["base30_n26_shift_present"] is True
    assert rows[0]["source_core_tuple"] == [30, 13, 1, 30, 2, 4, 5, 23854528]
    assert rows[0]["shifted_member_tuple"] == [30, 26, 1, 30, 1, 4, 5, 11927264]
    assert rows[0]["observed_position_windows"] == ["[0,6]", "[1,7]"]
    assert rows[0]["mod_stable_shift_proved_cases"] == 1
    assert rows[0]["mod_stable_shift_candidate_cases"] == 0
    assert rows[0]["finite_only_mod_stable_carry_loss_cases"] == 0
    assert rows[0]["shape13_k4_scale_two_hypothesis_ready_members"] == 1
    assert rows[0]["shape13_k4_scale_two_hypothesis_failed_members"] == 1
    assert rows[0]["shape13_k4_scale_two_unnamed_candidate_members"] == 0
    assert rows[0]["shape13_k4_scale_two_unnamed_candidate_tuples"] == []
    assert rows[0]["shape13_k4_scale_two_candidate_mining_status"] == (
        "no_unnamed_scale_two_ready_members_under_current_bounds"
    )
    assert rows[0]["shape13_k4_current_scan_status"] == (
        "only_base30_core_and_shift_pair_under_current_bounds"
    )
    assert rows[0]["shape13_k4_current_scan_stop_condition"] == (
        "do_not_add_new_shape13_k4_finite_package_until_wider_scan_emits_new_member"
    )
    assert "max_n=2000" in rows[0]["shape13_k4_wider_probe_note"]
    assert "7,10,12,30,32,64,66,72,98,100" in rows[0][
        "shape13_k4_wider_probe_note"
    ]
    assert "no unnamed scale-two-ready members" in rows[0][
        "shape13_k4_wider_scale_two_candidate_probe_note"
    ]
    assert rows[0]["recommended_next_observability_task"] == (
        "mine_wider_shape13_k4_members_or_generalize_scale_two_criterion"
    )
    assert rows[0]["all_members_coefficient_mod_block_base_preserved"] is True
    assert rows[0]["all_members_carried_output_hides_raw_conflict"] is True
    assert rows[0]["all_members_carry_state_information_lost"] is True
    assert rows[0]["open_boundary_ids"] == [
        "small_k_visibility_threshold",
        "carry_dfa_factorization",
    ]

    members = [
        row
        for row in rows
        if row["group"] == "observability_shape13_k4_mod_stable_carry_loss_member"
    ]
    by_n = {row["n"]: row for row in members}
    assert set(by_n) == {13, 26}

    core = by_n[13]
    assert core["family_member_rank"] == 1
    assert core["shape13_k4_family_role"] == "source_core_reference"
    assert core["shape13_k4_support_status"] == "source_core_reference"
    assert core["conflict_remainder_state"] == 1
    assert core["conflict_positions"] == [0, 6]
    assert core["conflict_coefficients"] == [2, 8192]
    assert core["conflict_carry_states"] == [0, 1260]
    assert core["conflict_block_values"] == [2, 2]
    assert core["shape13_k4_denominator_multiplier_from_core"] == 1
    assert core["shape13_k4_core_q"] == 2
    assert core["shape13_k4_q_times_denominator_multiplier_eq_core_q"] is True
    assert core["shape13_k4_scale_two_hypotheses_hold"] is False
    assert core["shape13_k4_scale_two_failure_reason"] == (
        "base_prime_support_times_two_ne_k"
    )
    assert core["shape13_k4_hyp_good_mode"] is True
    assert core["shape13_k4_hyp_same_core_compatible"] is True
    assert core["shape13_k4_hyp_base_prime_support_times_two_eq_k"] is False
    assert core["shape13_k4_hyp_scaled_quotient_remainders_lt_gap"] is True
    assert core["shape13_k4_hyp_scaled_block_remainders_lt_block_base"] is True
    assert core["shape13_k4_hyp_source_core_hidden_carry_block_value"] is True

    shifted = by_n[26]
    assert shifted["family_member_rank"] == 2
    assert shifted["shape13_k4_family_role"] == "base_supported_shift_member"
    assert shifted["shape13_k4_support_status"] == (
        "mod_stable_carry_loss_shift_proved_by_arithmetic_criterion"
    )
    assert shifted["shape13_k4_proof_surface"] == "lean_named_arithmetic_criterion"
    assert shifted["shape13_k4_failure_reason"] is None
    assert shifted["conflict_remainder_state"] == 4
    assert shifted["conflict_positions"] == [1, 7]
    assert shifted["conflict_coefficients"] == [4, 16384]
    assert shifted["conflict_carry_states"] == [0, 2520]
    assert shifted["conflict_block_values"] == [4, 4]
    assert shifted["shape13_k4_source_positions"] == [0, 6]
    assert shifted["shape13_k4_target_positions"] == [1, 7]
    assert shifted["shape13_k4_position_shift_from_core"] == 1
    assert shifted["shape13_k4_preperiod_shift_from_core"] == 1
    assert shifted["shape13_k4_denominator_multiplier_from_core"] == 2
    assert shifted["shape13_k4_q_times_denominator_multiplier_eq_core_q"] is True
    assert shifted["shape13_k4_shift_criterion_theorem"] == (
        "sameCoreCompatible_hiddenCarryBlockValue_shift_scale_two"
    )
    assert shifted["shape13_k4_named_instantiation"] == (
        "QRTour.Shape13K4.base30_n26_sameCore_scale_two_hiddenCarryBlockValue_shift"
    )
    assert shifted["shape13_k4_coefficient_mod_block_base_preserved"] is True
    assert shifted["shape13_k4_carried_output_hides_raw_conflict"] is True
    assert shifted["shape13_k4_carry_state_information_lost"] is True
    assert shifted["shape13_k4_scale_two_hypotheses_hold"] is True
    assert shifted["shape13_k4_scale_two_failure_reason"] is None
    assert shifted["shape13_k4_hyp_good_mode"] is True
    assert shifted["shape13_k4_hyp_same_core_compatible"] is True
    assert shifted["shape13_k4_hyp_base_prime_support_times_two_eq_k"] is True
    assert shifted["shape13_k4_hyp_left_scaled_quotient_remainder_lt_gap"] is True
    assert shifted["shape13_k4_hyp_right_scaled_quotient_remainder_lt_gap"] is True
    assert shifted["shape13_k4_hyp_scaled_quotient_remainders_lt_gap"] is True
    assert shifted["shape13_k4_hyp_left_scaled_block_remainder_lt_block_base"] is True
    assert shifted["shape13_k4_hyp_right_scaled_block_remainder_lt_block_base"] is True
    assert shifted["shape13_k4_hyp_scaled_block_remainders_lt_block_base"] is True
    assert shifted["shape13_k4_hyp_source_core_hidden_carry_block_value"] is True
    assert shifted["shape13_k4_next_lean_task"] == (
        "generalize_shape13_scale_two_criterion_beyond_base30_13_26"
    )
    assert shifted["next_observability_task"] == (
        "generalize_shape13_scale_two_criterion_beyond_base30_13_26"
    )


def test_observability_instrument_comparison_groups_hidden_source_shapes() -> None:
    rows = observability_instrument_comparison_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=5,
    )

    assert rows[0]["group"] == "observability_instrument_summary"
    assert rows[0]["first_source_symmetry_signature"] == (
        "periodic_modulus=17;k=4;position_gap=4"
    )
    assert rows[0]["cross_base_shape_count"] > 0
    assert rows[0]["shifted_shape_count"] > 0
    assert rows[0]["open_boundary_ids"] == [
        "small_k_visibility_threshold",
        "carry_dfa_factorization",
    ]

    shape_rows = [
        row for row in rows if row["group"] == "observability_source_symmetry_shape"
    ]
    first_shape = shape_rows[0]
    assert first_shape["source_symmetry_signature"] == (
        "periodic_modulus=17;k=4;position_gap=4"
    )
    assert first_shape["hidden_bases"] == [10, 30]
    assert first_shape["visible_bases"] == []
    assert first_shape["shifted_bases"] == [10]
    assert first_shape["source_symmetry_shift_observed"] is True
    assert first_shape["conflict_remainder_states"] == [1, 4]
    assert first_shape["exact_position_signatures"] == [
        "positions=[0,4]",
        "positions=[1,5]",
    ]

    members = [
        row
        for row in rows
        if row["group"] == "observability_instrument_member"
        and row["source_symmetry_signature"]
        == "periodic_modulus=17;k=4;position_gap=4"
    ]
    by_key = {(row["base"], row["n"]): row for row in members}
    assert {(10, 68), (30, 68), (10, 17)} <= set(by_key)
    assert by_key[(10, 68)]["instrument_observation_status"] == "hides_source_symmetry"
    assert by_key[(30, 68)]["instrument_observation_status"] == "hides_source_symmetry"
    assert by_key[(10, 17)]["source_symmetry_shift_status"] == "shifted_position_window"

    assert all(
        row["observability_boundary_status"]
        != "small_k_visibility_threshold_closed"
        for row in rows
        if "observability_boundary_status" in row
    )


def test_observability_shape17_k4_family_connects_shifted_core_to_composite68() -> None:
    rows = observability_shape17_k4_family_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )

    assert rows[0]["group"] == "observability_shape17_k4_family_summary"
    assert rows[0]["source_symmetry_signature"] == (
        "periodic_modulus=17;k=4;position_gap=4"
    )
    assert rows[0]["n_values"] == [17, 34, 68]
    assert rows[0]["same_core_multipliers"] == [1, 2, 4]
    assert rows[0]["shifted_member_count"] == 1
    assert rows[0]["composite68_style_member_count"] == 2
    assert rows[0]["lean_ready_member_count"] == 2
    assert rows[0]["same_core_shift_proved_cases"] == 4
    assert rows[0]["same_core_shift_candidate_cases"] == 0
    assert rows[0]["finite_only_hidden_conflict_cases"] == 0
    assert rows[0]["observability_boundary_status"] == (
        "empirical_open_boundary_shape17_k4_family_classifier"
    )

    members = [
        row
        for row in rows
        if row["group"] == "observability_shape17_k4_family_member"
    ]
    by_key = {(row["base"], row["n"]): row for row in members}
    assert {(10, 17), (10, 34), (30, 34), (10, 68), (30, 68)} == set(by_key)

    base10_17 = by_key[(10, 17)]
    assert base10_17["source_symmetry_family_role"] == "periodic_core_shifted_member"
    assert base10_17["same_core_multiplier"] == 1
    assert base10_17["conflict_positions"] == [0, 4]
    assert base10_17["position_shift_from_canonical"] == -1
    assert base10_17["base_local_coefficient_scale"] == 1
    assert base10_17["same_core_shift_support_status"] == "source_core_reference"
    assert base10_17["same_core_shift_source_positions"] == [0, 4]
    assert base10_17["same_core_shift_target_positions"] == [1, 5]

    row = by_key[(10, 34)]
    assert row["source_symmetry_family_role"] == "double_core_composite_style_member"
    assert row["same_core_multiplier"] == 2
    assert row["conflict_positions"] == [1, 5]
    assert row["position_shift_from_canonical"] == 0
    assert row["base_local_coefficient_scale"] == 2
    assert row["same_core_shift_support_status"] == (
        "same_core_shift_proved_by_arithmetic_criterion"
    )
    assert row["same_core_shift_scale"] == 2
    assert row["same_core_shift_source_positions"] == [0, 4]
    assert row["same_core_shift_target_positions"] == [1, 5]
    assert row["same_core_hyp_base_prime_support_times_scale_eq_k"] is True
    assert row["same_core_hyp_scaled_quotient_remainder_lt_gap"] is True
    assert row["same_core_hyp_scaled_block_remainder_lt_block_base"] is True
    assert row["same_core_shift_criterion_theorem"] == (
        "sameCoreCompatible_hiddenCarryBlockValue_shift_scaled_one"
    )
    assert row["same_core_shift_named_instantiation"] == (
        "QRTour.Shape17K4.base10_n34_sameCore_scale_two_hiddenCarryBlockValue_shift"
    )

    row = by_key[(30, 34)]
    assert row["source_symmetry_family_role"] == "double_core_composite_style_member"
    assert row["same_core_multiplier"] == 2
    assert row["conflict_positions"] == [1, 5]
    assert row["position_shift_from_canonical"] == 0
    assert row["base_local_coefficient_scale"] == 2
    assert row["same_core_shift_support_status"] == (
        "same_core_shift_proved_by_arithmetic_criterion"
    )
    assert row["same_core_shift_named_instantiation"] == (
        "QRTour.Shape17K4.base30_n34_sameCore_scale_two_hiddenCarryBlockValue_shift"
    )
    assert row["same_core_shift_failure_reason"] is None

    for key in [(10, 68), (30, 68)]:
        row = by_key[key]
        assert row["source_symmetry_family_role"] == "composite68_style_member"
        assert row["same_core_multiplier"] == 4
        assert row["conflict_positions"] == [1, 5]
        assert row["lean_readiness"] == "existing_composite68_family_theorem"
        assert row["open_boundary_ids"] == [
            "small_k_visibility_threshold",
            "carry_dfa_factorization",
        ]
        assert row["same_core_shift_source_positions"] == [0, 4]
        assert row["same_core_shift_target_positions"] == [1, 5]
        assert row["same_core_hyp_base_prime_support_times_scale_eq_k"] is True
        assert row["same_core_hyp_scaled_quotient_remainder_lt_gap"] is True
        assert row["same_core_hyp_scaled_block_remainder_lt_block_base"] is True

    assert by_key[(10, 68)]["same_core_shift_support_status"] == (
        "same_core_shift_proved_by_arithmetic_criterion"
    )
    assert by_key[(10, 68)]["same_core_shift_named_instantiation"] == (
        "QRTour.Shape17K4.base10_n68_sameCore_scale_one_hiddenCarryBlockValue_shift"
    )
    assert by_key[(30, 68)]["same_core_shift_support_status"] == (
        "same_core_shift_proved_by_arithmetic_criterion"
    )
    assert by_key[(30, 68)]["same_core_shift_named_instantiation"] == (
        "QRTour.Shape17K4.base30_n68_sameCore_scale_one_hiddenCarryBlockValue_shift"
    )


def test_observability_next_source_shape_family_mines_shape187_k188() -> None:
    rows = observability_next_source_shape_family_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )

    assert rows[0]["group"] == "observability_next_source_shape_family_summary"
    assert rows[0]["source_symmetry_signature"] == (
        "periodic_modulus=187;k=188;position_gap=6"
    )
    assert rows[0]["skipped_source_symmetry_signatures"] == [
        "periodic_modulus=17;k=4;position_gap=4"
    ]
    assert rows[0]["selected_shape_rank"] == 2
    assert rows[0]["n_values"] == [374, 748]
    assert rows[0]["same_core_multipliers"] == [2, 4]
    assert rows[0]["bases_observed"] == [10, 12, 30]
    assert rows[0]["hidden_bases"] == [10, 12, 30]
    assert rows[0]["shifted_bases"] == []
    assert rows[0]["canonical_conflict_positions"] == [1, 2]
    assert rows[0]["exact_position_signatures"] == ["positions=[1,2]"]
    assert rows[0]["lean_ready_member_count"] == 0
    assert rows[0]["same_core_shift_proved_cases"] == 0
    assert rows[0]["same_core_shift_candidate_cases"] == 0
    assert rows[0]["finite_only_hidden_conflict_cases"] == 6
    assert rows[0]["observability_boundary_status"] == (
        "empirical_open_boundary_next_source_shape_family_classifier"
    )

    members = [
        row
        for row in rows
        if row["group"] == "observability_next_source_shape_family_member"
    ]
    by_key = {(row["base"], row["n"]): row for row in members}
    assert {
        (10, 374),
        (10, 748),
        (12, 374),
        (12, 748),
        (30, 374),
        (30, 748),
    } == set(by_key)

    for key, expected_multiplier, expected_scale in [
        ((10, 374), 2, 2),
        ((12, 374), 2, 2),
        ((30, 374), 2, 2),
        ((10, 748), 4, 1),
        ((12, 748), 4, 1),
        ((30, 748), 4, 1),
    ]:
        row = by_key[key]
        assert row["source_symmetry_family_role"] == "same_position_scaled_member"
        assert row["same_core_multiplier"] == expected_multiplier
        assert row["position_shift_from_canonical"] == 0
        assert row["base_local_coefficient_scale"] == expected_scale
        assert row["same_core_shift_support_status"] == "finite_only_hidden_conflict"
        assert row["same_core_shift_failure_reason"] == (
            "outside_same_core_shift_classifier"
        )
        assert row["open_boundary_ids"] == [
            "small_k_visibility_threshold",
            "carry_dfa_factorization",
        ]


def test_observability_shape187_k188_family_classifies_same_position_scaling() -> None:
    rows = observability_shape187_k188_family_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )

    assert rows[0]["group"] == "observability_shape187_k188_family_summary"
    assert rows[0]["source_symmetry_signature"] == (
        "periodic_modulus=187;k=188;position_gap=6"
    )
    assert rows[0]["family_class"] == "shape187_k188_same_position_scaling"
    assert rows[0]["n_values"] == [374, 748]
    assert rows[0]["same_core_multipliers"] == [2, 4]
    assert rows[0]["bases_observed"] == [10, 12, 30]
    assert rows[0]["same_position_scaling_proved_cases"] == 4
    assert rows[0]["same_position_scaling_candidate_cases"] == 2
    assert rows[0]["finite_only_hidden_conflict_cases"] == 0
    assert rows[0]["all_members_idempotent_remainder"] is True
    assert rows[0]["all_members_hidden_output_formula_holds"] is True
    assert rows[0]["first_finite_package_tuple"] == [
        30,
        374,
        20,
        348678440100000000000000000000,
        932295294385026737967914438,
        188,
        1,
        173406924756399393953853079552,
    ]
    assert rows[0]["first_finite_package_namespace"] == "QRTour.FutureBase30N374"
    assert rows[0]["first_finite_package_theorem"] == (
        "coordinate_stateAlignments_one_two_certifiedConflict_eight_one"
    )
    assert rows[0]["same_position_scaling_suggested_lean_theorem"] == (
        "samePositionIdempotent_hiddenCarryBlockValue"
    )
    assert rows[0]["same_position_scaling_exported_hypothesis_record"] == (
        "BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses"
    )
    assert rows[0]["same_position_scaling_idempotent_remainder_projection"] == (
        "BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses.idempotent_remainder"
    )
    assert rows[0]["same_position_scaling_exported_hypothesis_adapter"] == (
        "BlockCoordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses"
    )

    members = [
        row
        for row in rows
        if row["group"] == "observability_shape187_k188_family_member"
    ]
    assert members[0]["base"] == 30
    assert members[0]["n"] == 374
    by_key = {(row["base"], row["n"]): row for row in members}
    assert {
        (10, 374),
        (10, 748),
        (12, 374),
        (12, 748),
        (30, 374),
        (30, 748),
    } == set(by_key)

    for (
        key,
        expected_multiplier,
        expected_role,
        expected_carry_states,
        expected_status,
        expected_failure_reason,
        expected_named_instantiation,
    ) in [
        (
            (10, 374),
            2,
            "double_core_same_position_member",
            [94, 17766],
            "same_position_scaling_proved_by_arithmetic_criterion",
            None,
            "QRTour.FutureBase10N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two",
        ),
        (
            (12, 374),
            2,
            "double_core_same_position_member",
            [94, 17766],
            "same_position_scaling_proved_by_arithmetic_criterion",
            None,
            "QRTour.FutureBase12N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two",
        ),
        (
            (30, 374),
            2,
            "double_core_same_position_member",
            [94, 17766],
            "same_position_scaling_proved_by_arithmetic_criterion",
            None,
            "QRTour.FutureBase30N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two",
        ),
        (
            (10, 748),
            4,
            "quadruple_core_same_position_member",
            [47, 8883],
            "same_position_scaling_criterion_candidate",
            "no_named_lean_instantiation",
            None,
        ),
        (
            (12, 748),
            4,
            "quadruple_core_same_position_member",
            [47, 8883],
            "same_position_scaling_criterion_candidate",
            "no_named_lean_instantiation",
            None,
        ),
        (
            (30, 748),
            4,
            "quadruple_core_same_position_member",
            [47, 8883],
            "same_position_scaling_proved_by_arithmetic_criterion",
            None,
            "QRTour.FutureBase30N748.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two",
        ),
    ]:
        row = by_key[key]
        assert row["source_symmetry_family_role"] == expected_role
        assert row["same_core_multiplier"] == expected_multiplier
        assert row["position_shift_from_canonical"] == 0
        assert row["same_position_scaling_support_status"] == expected_status
        assert row["same_position_scaling_idempotent_remainder"] is True
        assert row["same_position_hyp_k_eq_core_plus_one"] is True
        assert row["same_position_hyp_multiplier_divides_k"] is True
        assert row["same_position_hyp_coefficient_ratio_eq_k"] is True
        assert row["same_position_hyp_carry_states_match_floor_powers"] is True
        assert row["same_position_hyp_hidden_output_formula_holds"] is True
        assert row["same_position_scaling_coefficient_ratio"] == 188
        assert row["same_position_scaling_expected_carry_states"] == expected_carry_states
        assert row["same_position_scaling_failure_reason"] == expected_failure_reason
        assert row["same_position_scaling_suggested_lean_theorem"] == (
            "samePositionIdempotent_hiddenCarryBlockValue"
        )
        assert row["same_position_scaling_exported_hypothesis_record"] == (
            "BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses"
        )
        assert row["same_position_scaling_idempotent_remainder_projection"] == (
            "BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses.idempotent_remainder"
        )
        assert row["same_position_scaling_exported_hypothesis_adapter"] == (
            "BlockCoordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses"
        )
        assert row["same_position_scaling_intended_proof_path"] == [
            "BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses",
            "BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses.idempotent_remainder",
            "samePositionIdempotent_hiddenCarryBlockValue",
            "BlockCoordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses",
        ]
        if key == (10, 374):
            assert row["same_position_scaling_named_hypothesis_instantiation"] == (
                "QRTour.FutureBase10N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
            )
            assert row["same_position_scaling_named_finite_conflict_instantiation"] == (
                "QRTour.FutureBase10N374.coordinate_stateAlignments_one_two_certifiedConflict_eight_two"
            )
        elif key == (12, 374):
            assert row["same_position_scaling_named_hypothesis_instantiation"] == (
                "QRTour.FutureBase12N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
            )
            assert row["same_position_scaling_named_finite_conflict_instantiation"] is None
        elif key == (30, 374):
            assert row["same_position_scaling_named_hypothesis_instantiation"] == (
                "QRTour.FutureBase30N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
            )
            assert row["same_position_scaling_named_finite_conflict_instantiation"] == (
                "QRTour.FutureBase30N374.coordinate_stateAlignments_one_two_certifiedConflict_eight_one"
            )
        elif key == (30, 748):
            assert row["same_position_scaling_named_hypothesis_instantiation"] == (
                "QRTour.FutureBase30N748.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
            )
            assert row["same_position_scaling_named_finite_conflict_instantiation"] == (
                "QRTour.FutureBase30N748.coordinate_stateAlignments_one_two_certifiedConflict_eight_one"
            )
        else:
            assert row["same_position_scaling_named_hypothesis_instantiation"] is None
            assert row["same_position_scaling_named_finite_conflict_instantiation"] is None
        assert (
            row["same_position_scaling_named_instantiation"]
            == expected_named_instantiation
        )


def test_certificate_lean_fixture_rows_pin_composite68_theorem_surface() -> None:
    fixtures = certificate_lean_fixture_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )

    assert [fixture["namespace"] for fixture in fixtures] == [
        "QRTour.Composite68",
        "QRTour.Composite68Base30",
    ]
    assert [fixture["certificate_tuple"] for fixture in fixtures] == [
        [10, 68, 4, 10000, 147, 4, 1, 6208],
        [30, 68, 3, 27000, 397, 4, 1, 10208],
    ]
    assert {fixture["n"] for fixture in fixtures} == {68}
    assert {fixture["base"] for fixture in fixtures} == {10, 30}
    assert {fixture["namespace"] for fixture in fixtures}.isdisjoint(
        {"QRTour.Prime97", "QRTour.Composite996"}
    )
    assert all(fixture["fixture_status"] == "source_pinned_existing_theorem" for fixture in fixtures)
    assert all(
        fixture["open_boundary_ids"] == ["small_k_visibility_threshold", "carry_dfa_factorization"]
        for fixture in fixtures
    )
    assert all(
        fixture["proof_path_snippet"]
        == (
            "have hrecord := coordinate_stateAlignments_one_five_certifiedConflict_eight_one\n"
            "exact hrecord.not_remainderToCoefficientFunctional"
        )
        for fixture in fixtures
    )
    for fixture in fixtures:
        stub = fixture["copyable_lean_stub"]
        assert stub["kind"] == "not_remainder_to_coefficient_functional_projection"
        assert stub["record_theorem_name"] == (
            "coordinate_stateAlignments_one_five_certifiedConflict_eight_one"
        )
        assert stub["projection_accessor"] == "not_remainderToCoefficientFunctional"
        assert stub["recommended_theorem_name"] == (
            f"{fixture['certificate_id']}_not_remainderToCoefficientFunctional"
        )
        assert "certificate-lean-fixtures-v1" in stub["code"]
        assert f"theorem {stub['recommended_theorem_name']} :" in stub["code"]
        assert "have hrecord := coordinate_stateAlignments_one_five_certifiedConflict_eight_one" in stub["code"]
        assert "exact hrecord.not_remainderToCoefficientFunctional" in stub["code"]


def test_certified_positive_lookahead_coefficient_conflict_atlas_rows_cross_base_surface() -> None:
    rows = certified_positive_lookahead_coefficient_conflict_atlas_rows(
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=12,
    )
    assert rows[0]["group"] == "coefficient_conflict_atlas_summary"
    assert rows[0]["bases"] == [7, 10, 12, 30]
    assert rows[0]["bases_with_conflicts"] == 4
    assert rows[0]["first_base10_conflict_tuple"] == [10, 68, 4, 10000, 147, 4, 1, 6208]

    atlas_rows = [row for row in rows if row["group"] == "coefficient_conflict_atlas_case"]
    assert atlas_rows
    assert atlas_rows[0]["base"] == 30
    assert atlas_rows[0]["n"] == 7
    assert atlas_rows[0]["exact_gap_numerator"] == 532
    assert atlas_rows[0]["global_conflict_rank"] == 1

    base10_first = next(
        row for row in atlas_rows if row["base"] == 10 and row["base_conflict_rank"] == 1
    )
    assert base10_first["n"] == 68
    assert base10_first["conflict_remainder_state"] == 4
    assert base10_first["conflict_positions"] == [1, 5]
    assert base10_first["conflict_coefficients"] == [588, 150528]
    assert base10_first["base_total_conflict_rows"] > 0


def test_certified_positive_lookahead_coefficient_conflict_family_rows_mine_shapes() -> None:
    rows = certified_positive_lookahead_coefficient_conflict_family_rows(
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=12,
    )
    assert rows[0]["group"] == "coefficient_conflict_family_summary"
    assert rows[0]["cross_base_shape_families"] > 0
    assert rows[0]["composite68_cross_base_family_present"] is True
    assert rows[0]["recommended_family_signature"] == (
        "periodic_modulus=17;k=4;remainder_state=4;"
        "positions=[1, 5];carry_states=[0, 60];output_hidden=true"
    )
    assert rows[0]["next_lean_theorem_recommendation"] == (
        "classify_composite68_cross_base_hidden_output_conflict"
    )
    assert [10, 68, 4, 10000, 147, 4, 1, 6208] in rows[0]["recommended_family_member_tuples"]
    assert [30, 68, 3, 27000, 397, 4, 1, 10208] in rows[0]["recommended_family_member_tuples"]

    family_rows = [row for row in rows if row["group"] == "coefficient_conflict_family"]
    assert family_rows
    composite68_family = next(row for row in family_rows if row["contains_base10_68"])
    assert composite68_family["shape_periodic_modulus"] == 17
    assert composite68_family["shape_k"] == 4
    assert composite68_family["shape_conflict_remainder_state"] == 4
    assert composite68_family["shape_conflict_positions"] == [1, 5]
    assert composite68_family["shape_conflict_carry_states"] == [0, 60]
    assert composite68_family["shape_conflict_output_hidden"] is True
    assert composite68_family["bases"] == [10, 30]
    assert composite68_family["n_values"] == [68]
    assert composite68_family["theorem_candidate_kind"] == "composite68_cross_base_family_candidate"
    assert composite68_family["next_lean_theorem_recommendation"] == (
        "classify_composite68_cross_base_hidden_output_conflict"
    )


def test_composite68_cross_base_obstruction_sweep_rows_find_bounded_family_signal() -> None:
    rows = composite68_cross_base_obstruction_sweep_rows(
        max_base=120,
        n_blocks=8,
        top=0,
    )
    assert rows[0]["group"] == "composite68_cross_base_sweep_summary"
    assert rows[0]["target_shape_signature"] == (
        "periodic_modulus=17;k=4;remainder_state=4;"
        "positions=[1, 5];carry_states=[0, 60];output_hidden=true"
    )
    assert rows[0]["target_shape_bases"] == [10, 30, 32, 64, 66, 72, 98, 100]
    assert rows[0]["target_shape_rows"] == 8
    assert rows[0]["base10_anchor_tuple"] == [10, 68, 4, 10000, 147, 4, 1, 6208]
    assert rows[0]["base30_package_candidate_tuple"] == [30, 68, 3, 27000, 397, 4, 1, 10208]
    assert rows[0]["base30_target_present"] is True
    assert rows[0]["all_target_rows_have_B_mod_68_eq_4"] is True
    assert rows[0]["recommended_next_lean_task"] == (
        "add_composite68_base30_finite_package_then_cross_base_shape_lemma"
    )

    case_rows = [row for row in rows if row["group"] == "composite68_cross_base_sweep_case"]
    target_rows = [row for row in case_rows if row["composite68_hidden_output_shape_match"]]
    assert [row["base"] for row in target_rows] == [10, 30, 32, 64, 66, 72, 98, 100]
    base30 = next(row for row in target_rows if row["base"] == 30)
    assert base30["lean_package_role"] == "next_base30_package_candidate"
    assert base30["conflict_coefficients"] == [1588, 406528]
    assert base30["conflict_block_values"] == [1588, 1588]
    assert base30["selected_block_base_mod_68"] == 4


def test_composite68_congruence_family_rows_classify_bounded_family() -> None:
    rows = composite68_congruence_family_rows(max_base=120, max_m=8, n_blocks=8, top=0)
    assert rows[0]["group"] == "composite68_congruence_family_summary"
    assert rows[0]["all_congruence_rows_have_k_eq_4"] is True
    assert rows[0]["all_congruence_rows_have_B_mod_68_eq_4"] is True
    assert rows[0]["lean_obstruction_covered_rows"] == rows[0]["total_congruence_rows"]
    known_targets = {10, 30, 32, 64, 66, 72, 98, 100}
    assert known_targets <= set(rows[0]["hidden_output_shape_bases"])

    case_rows = [row for row in rows if row["group"] == "composite68_congruence_family_case"]
    assert case_rows
    assert all(row["selected_block_base_mod_68"] == 4 for row in case_rows)
    assert all(row["k"] == 4 for row in case_rows)
    assert all(row["lean_obstruction_covered"] is True for row in case_rows)

    matched_bases = {
        row["base"]
        for row in case_rows
        if row["composite68_hidden_output_shape_match"] is True
    }
    assert known_targets <= matched_bases

    base10 = next(row for row in case_rows if row["base"] == 10 and row["m"] == 4)
    assert base10["B"] == 10000
    assert base10["q"] == 147
    assert base10["certified_lookahead_blocks"] == 1
    assert base10["exact_gap_numerator"] == 6208
    assert base10["conflict_positions"] == [1, 5]
    assert base10["empirical_classifier_status"] == "certified_hidden_output_shape_match"


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
