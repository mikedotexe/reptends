from bridge_reptends import (
    CarryTransducer,
    carry_factorization_selector_profile,
    carry_selector_profile_rows,
    carry_selector_profile_class,
    canonical_carry_selector_case_studies,
    canonical_carry_selector_family_studies,
    canonical_carry_dfa_examples,
    carry_factorization_rows,
    carry_selector_research_rows,
    carry_remainder_comparison,
    carry_window_example,
    compare_carry_selector_profiles,
    non_k_one_state_relabeling_rows,
    same_core_selector_family_rows,
    select_carry_factorization_prefer_m,
)
from bridge_reptends.orbit_weave import apply_carry, skeleton_vs_actual


def test_transducer_matches_windowed_carry_normalization() -> None:
    for modulus, prefer_m, blocks in [(19, 2, 9), (37, 3, 6), (97, 2, 12)]:
        result = skeleton_vs_actual(modulus, n_blocks=blocks, prefer_m=prefer_m)
        run = CarryTransducer(result["B"]).run(result["raw"])
        assert run.render(result["m"]) == apply_carry(result["raw"], result["B"])
        assert run.render(result["m"]) == result["carried"]


def test_transducer_exposes_reachable_carry_states() -> None:
    result = skeleton_vs_actual(19, n_blocks=9, prefer_m=2)
    run = CarryTransducer(result["B"]).run(result["raw"])

    assert 0 in run.reachable_carries
    assert max(run.reachable_carries) > 0


def test_state_summary_and_dot_export_capture_first_nonzero_carry() -> None:
    example = carry_window_example(97, prefer_m=2, n_blocks=8)
    summary = example.run.state_summary()

    assert summary.reachable_states == (0, 2, 7, 22, 67, 196)
    assert summary.first_nonzero_position == 4
    assert summary.max_carry == 196

    dot = summary.to_dot()
    assert "digraph CarryTransducerStateGraph" in dot
    assert '"2" -> "0"' in dot


def test_carry_window_example_matches_long_division_and_layers() -> None:
    example = carry_window_example(996, prefer_m=3, n_blocks=8)

    assert example.matches_long_division is True
    assert example.raw_coefficients[:4] == (1, 4, 16, 64)
    assert example.carried_blocks[:4] == ("001", "004", "016", "064")
    assert example.actual_blocks[:4] == ("001", "004", "016", "064")


def test_k_one_examples_collapse_to_single_carry_state() -> None:
    example = carry_window_example(21, prefer_m=6, n_blocks=6)
    summary = example.run.state_summary()

    assert example.matches_long_division is True
    assert summary.reachable_states == (0,)
    assert summary.first_nonzero_position is None


def test_state_graph_and_minimization_interfaces_are_exposed() -> None:
    example = carry_window_example(97, prefer_m=2, n_blocks=8)
    graph = example.run.state_summary().graph()
    minimized = graph.minimize()

    assert graph.graph_kind == "CarryTransducer"
    assert graph.initial_state == 0
    assert graph.edge_count == len(graph.edges)
    assert minimized.graph_kind == "CarryTransducer"
    assert minimized.class_count <= len(graph.states)
    assert "digraph MinimizedCarryTransducerGraph" in minimized.to_dot()


def test_carry_remainder_comparison_keeps_objects_separate() -> None:
    comparison = carry_remainder_comparison(996, prefer_m=3, n_blocks=8)

    assert comparison.outputs_match is True
    assert comparison.carry_graph.graph_kind == "CarryTransducer"
    assert comparison.remainder_graph.graph_kind == "RemainderDFA"
    assert len(comparison.alignments) == 8
    assert "finite-window output agreement" in comparison.implemented_statement
    assert "not established here" in comparison.open_claim_boundary
    assert comparison.decision_report.remainder_to_carry_quotient_candidate is True
    assert comparison.decision_report.state_relabeling_candidate is False
    assert any("carry graph classes" in line for line in comparison.summary_lines())


def test_canonical_carry_dfa_examples_cover_named_cases() -> None:
    cases = {case.n: case for case in canonical_carry_dfa_examples()}

    assert {21, 97, 996}.issubset(cases)
    assert cases[21].comparison.outputs_match is True
    assert "functional criteria hold" in cases[21].distinctive_feature
    assert "trivial relabeling" in cases[21].distinctive_feature
    assert "preperiod" in cases[996].distinctive_feature


def test_factorization_decision_report_separates_relabeling_from_quotient_candidates() -> None:
    trivial = carry_remainder_comparison(21, prefer_m=6, n_blocks=8)
    prime = carry_remainder_comparison(97, prefer_m=2, n_blocks=8)
    composite = carry_remainder_comparison(996, prefer_m=3, n_blocks=8)

    assert trivial.decision_report.state_relabeling_candidate is True
    assert trivial.decision_report.remainder_to_carry_quotient_candidate is True
    assert trivial.decision_report.carry_to_remainder_lift_candidate is True
    assert trivial.decision_report.regime == "state_relabeling"

    assert prime.decision_report.state_relabeling_candidate is False
    assert prime.decision_report.remainder_to_carry_quotient_candidate is True
    assert prime.decision_report.carry_to_remainder_lift_candidate is False
    assert prime.decision_report.counterexample_to_state_relabeling is True
    assert prime.decision_report.regime == "quotient_candidate_only"

    assert composite.decision_report.state_relabeling_candidate is False
    assert composite.decision_report.remainder_to_carry_quotient_candidate is True
    assert composite.decision_report.carry_to_remainder_lift_candidate is False
    assert composite.decision_report.counterexample_to_state_relabeling is True
    assert composite.decision_report.regime == "quotient_candidate_only"


def test_carry_factorization_mode_selector_prefers_informative_track_17_coordinates() -> None:
    assert select_carry_factorization_prefer_m(21, base=10, n_blocks=8) == 6
    assert select_carry_factorization_prefer_m(97, base=10, n_blocks=8) == 2
    assert select_carry_factorization_prefer_m(996, base=10, n_blocks=8) == 3


def test_carry_factorization_selector_profiles_capture_nonmonotone_regime_transitions() -> None:
    profile_21 = carry_factorization_selector_profile(21, base=10, n_blocks=8, max_m=7)
    profile_249 = carry_factorization_selector_profile(249, base=10, n_blocks=8, max_m=7)
    profile_996 = carry_factorization_selector_profile(996, base=10, n_blocks=8, max_m=7)

    assert profile_21.transition_signature == ("finite_word_only", "state_relabeling", "finite_word_only")
    assert profile_21.relabeling_modes == (6,)
    assert profile_21.has_isolated_relabeling_window is True

    assert profile_249.transition_signature == (
        "quotient_candidate_only",
        "state_relabeling",
        "quotient_candidate_only",
    )
    assert profile_249.relabeling_modes == (6,)
    assert profile_249.quotient_modes == (3, 4, 5, 7)
    assert profile_249.has_isolated_relabeling_window is True

    assert profile_996.transition_signature == ("quotient_candidate_only",)
    assert profile_996.relabeling_modes == ()
    assert profile_996.quotient_modes == (3, 4, 5, 6, 7)
    assert profile_996.has_isolated_relabeling_window is False


def test_selector_profile_comparisons_capture_same_core_loss_and_multiple_shift() -> None:
    same_core_loss = compare_carry_selector_profiles(249, 996, base=10, n_blocks=8, max_m=7)
    doubled_shift = compare_carry_selector_profiles(17, 34, base=10, n_blocks=8, max_m=8)

    assert same_core_loss.shared_periodic_core == 249
    assert same_core_loss.relabeling_window_destroyed is True
    assert same_core_loss.left_only_relabeling_modes == (6,)
    assert same_core_loss.right_only_relabeling_modes == ()
    assert same_core_loss.transition_signature_changed is True

    assert doubled_shift.shared_periodic_core == 17
    assert doubled_shift.relabeling_window_destroyed is False
    assert doubled_shift.relabeling_window_shifted is True
    assert doubled_shift.common_relabeling_modes == (5,)
    assert doubled_shift.right_only_relabeling_modes == (7,)


def test_selector_profile_classifier_and_rows_surface_non_k_one_signal() -> None:
    profile_21 = carry_factorization_selector_profile(21, base=10, n_blocks=8, max_m=7)
    profile_249 = carry_factorization_selector_profile(249, base=10, n_blocks=8, max_m=7)
    rows = carry_selector_profile_rows(1000, base=10, n_blocks=8, max_m=8)
    by_n = {row["n"]: row for row in rows}
    non_k_one = {row["n"]: row for row in non_k_one_state_relabeling_rows(1000, base=10, n_blocks=8, max_m=8)}

    assert carry_selector_profile_class(profile_21) == "isolated_k_one_relabeling"
    assert carry_selector_profile_class(profile_249) == "isolated_non_k_one_relabeling"
    assert by_n[249]["profile_class"] == "isolated_non_k_one_relabeling"
    assert by_n[996]["profile_class"] == "quotient_only"
    assert 249 in non_k_one
    assert 17 in non_k_one
    assert 996 not in non_k_one


def test_same_core_selector_family_rows_capture_disagreement_beyond_249_996() -> None:
    rows = same_core_selector_family_rows(1200, base=10, n_blocks=8, max_m=8)
    by_core = {row["core_n"]: row for row in rows}

    assert 249 in by_core
    assert by_core[249]["members"] == [249, 498, 996]
    assert by_core[249]["selected_members"] == [249]
    assert by_core[249]["has_relabeling_disagreement"] is True
    assert by_core[249]["related_open_claim_ids"] == ["carry_dfa_factorization"]
    assert "carry_dfa_factorization_target_249_498_996_same_core" in by_core[249]["matching_witness_ids"]

    assert 17 in by_core
    assert by_core[17]["members"][:3] == [17, 34, 68]
    assert by_core[17]["selected_members"][:2] == [17, 34]
    assert by_core[17]["has_signature_disagreement"] is True
    assert by_core[17]["matching_witness_ids"] == []


def test_canonical_carry_selector_studies_capture_systematic_track_17_signal() -> None:
    cases = {case.n: case for case in canonical_carry_selector_case_studies()}
    families = {case.label: case for case in canonical_carry_selector_family_studies()}

    assert {21, 249, 996}.issubset(cases)
    assert cases[249].profile.selected_step is not None
    assert cases[249].profile.selected_step.k == 16
    assert "same-core" in cases[996].explanation.lower()

    assert "Non-k = 1 relabeling windows" in families
    assert "Same-core relabeling loss" in families
    assert "Small-multiple relabeling shift and enlargement" in families
    assert families["Same-core relabeling loss"].members == (249, 498, 996)
    assert families["Small-multiple relabeling shift and enlargement"].members == (17, 34, 68)


def test_carry_selector_research_rows_publish_cross_base_signal() -> None:
    rows = carry_selector_research_rows(120, bases=(7, 10, 12), n_blocks=8, max_m=8)
    by_base = {row["base"]: row for row in rows}

    assert by_base[7]["publication_decision"] == "published_research_layer"
    assert by_base[7]["non_k_one_count"] == 26
    assert by_base[7]["same_core_disagreement_count"] == 14
    assert by_base[7]["same_core_multi_member_count"] == 0

    assert by_base[10]["non_k_one_count"] == 21
    assert by_base[10]["same_core_disagreement_count"] == 19
    assert by_base[10]["same_core_multi_member_count"] == 5
    assert any("core 17" in sample for sample in by_base[10]["sample_same_core_families"])

    assert by_base[12]["non_k_one_count"] == 14
    assert by_base[12]["same_core_disagreement_count"] == 14
    assert by_base[12]["same_core_multi_member_count"] == 4
    assert any("N=37" in sample for sample in by_base[12]["sample_non_k_one_examples"])


def test_carry_factorization_rows_surface_canonical_track_17_regimes() -> None:
    rows = carry_factorization_rows(1000, base=10, n_blocks=8)
    by_n = {row["n"]: row for row in rows}

    assert by_n[21]["factorization_regime"] == "state_relabeling"
    assert by_n[21]["state_relabeling_candidate"] is True
    assert by_n[21]["transition_signature"] == [
        "finite_word_only",
        "state_relabeling",
        "finite_word_only",
    ]
    assert by_n[21]["has_isolated_relabeling_window"] is True
    assert by_n[97]["factorization_regime"] == "quotient_candidate_only"
    assert by_n[97]["counterexample_to_state_relabeling"] is True
    assert "carry_window_transducer" in by_n[97]["matching_claim_ids"]
    assert "carry_dfa_factorization" in by_n[97]["related_open_claim_ids"]
    assert "carry_window_transducer_prime97_window6" in by_n[97]["matching_witness_ids"]
    assert "carry_dfa_factorization_target_21_97_996" in by_n[97]["matching_witness_ids"]
    assert by_n[996]["factorization_regime"] == "quotient_candidate_only"
    assert by_n[996]["remainder_to_carry_quotient_candidate"] is True
    assert "carry_window_transducer_same_core_996_window4" in by_n[996]["matching_witness_ids"]
    assert "carry_dfa_factorization_target_21_97_996" in by_n[996]["matching_witness_ids"]
    assert by_n[249]["factorization_regime"] == "state_relabeling"
    assert by_n[249]["transition_signature"] == [
        "quotient_candidate_only",
        "state_relabeling",
        "quotient_candidate_only",
    ]
