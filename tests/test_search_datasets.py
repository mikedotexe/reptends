import ast
import json
from pathlib import Path
import subprocess
import sys

import pytest

from bridge_reptends import (
    build_claim_witness_rows,
    build_example_atlas,
    build_orbit_carry_frontier_groups,
    certificate_first_scaffold_mapping_lint_payload,
    certificate_fixture_mapping_lint_payload,
    certificate_lean_fixture_payload,
    certificate_lean_fixture_rows,
    certificate_lean_stub_payload,
    certificate_lean_stub_rows,
    certificate_workbench_rows,
    chart_invariance_rows,
    certified_positive_lookahead_coefficient_conflict_atlas_rows,
    certified_positive_lookahead_coefficient_conflict_family_rows,
    certified_positive_lookahead_coefficient_conflict_rows,
    certified_positive_lookahead_state_window_rows,
    composite68_congruence_family_rows,
    composite68_cross_base_obstruction_sweep_rows,
    composite_profile_rows,
    find_legacy_counterexamples,
    instrument_atlas_rows,
    load_lean_worked_examples,
    load_throughlines,
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
    orbit_carry_frontier_rows,
    orbit_carry_trace_rows,
    quotient_obstruction_family_rows,
    quotient_obstruction_rows,
    rank_bridge_candidates,
    rank_composite_highlights,
    rank_prime_qr_examples,
    rank_q_one_bridges,
    same_core_obstruction_correlate_rows,
    same_core_obstruction_phase_rows,
    state_merging_rows,
    state_merging_same_core_rows,
    visibility_base_instrument_rows,
    visibility_optics_workbench_rows,
)

ROOT = Path(__file__).resolve().parent.parent


def _lean_worked_example_row(namespace: str) -> dict[str, object]:
    record = next(record for record in load_lean_worked_examples() if record.namespace == namespace)
    return {
        "module_path": record.module_path,
        "namespace": record.namespace,
        "claim_ids": list(record.claim_ids),
        "theorem_names": list(record.theorem_names),
    }


def test_bridge_ranking_surfaces_good_q_weighted_examples() -> None:
    candidates = rank_bridge_candidates(1200, top=None, dedupe_periodic_modulus=False)
    by_n = {candidate.n: candidate for candidate in candidates}

    assert all(candidate.period > 1 for candidate in candidates[:20])
    assert by_n[97].q_is_one is True
    assert by_n[249].k == 4
    assert by_n[996].q_is_one is True
    assert "small-residue block coordinate" in by_n[97].explanation


def test_legacy_counterexample_search_finds_19_and_31() -> None:
    records = find_legacy_counterexamples(50, [10])
    pairs = {(record.p, record.base, record.reptend_type) for record in records}

    assert (19, 10, "full") in pairs
    assert (31, 10, "half") in pairs


def test_composite_profile_dataset_contains_crt_fields() -> None:
    rows = composite_profile_rows(30, base=10)
    row_21 = next(row for row in rows if row["n"] == 21)

    assert row_21["global_order"] == 6
    assert "3:ord=1:lambda=2" in row_21["components"]
    assert "7:ord=6:lambda=6" in row_21["components"]


def test_q_one_bridge_leaderboard_highlights_nontrivial_bridge_cases() -> None:
    candidates = rank_q_one_bridges(1500, top=10)
    by_n = {candidate.n: candidate for candidate in candidates}

    assert all(candidate.q_is_one for candidate in candidates)
    assert all(candidate.period > 1 for candidate in candidates)
    assert 97 in by_n
    assert 996 in by_n


def test_prime_qr_leaderboard_exposes_generator_examples() -> None:
    examples = rank_prime_qr_examples(200, top=10)
    primes = {example.p for example in examples}

    assert 19 in primes or 97 in primes
    assert all(example.primary_vocabulary_id == "qr_generator" for example in examples)
    assert all("generator of the QR subgroup" in example.explanation for example in examples)


def test_composite_highlights_surface_crt_and_preperiod_examples() -> None:
    examples = rank_composite_highlights(1200, top=20)
    by_n = {example.n: example for example in examples}

    assert 249 in by_n
    assert 996 in by_n
    assert "remainder orbit under multiplication by the base" in by_n[996].explanation


def test_example_atlas_contains_canonical_examples_and_leaderboards() -> None:
    atlas = build_example_atlas(max_n=1200, max_p=300, top=8)

    canonical_ns = {entry["n"] for entry in atlas["canonical_examples"]}
    assert {37, 97, 249, 996, 19}.issubset(canonical_ns)

    assert "bridge_q1" in atlas["leaderboards"]
    assert "bridge_nontrivial" in atlas["leaderboards"]
    assert "composite_crt" in atlas["leaderboards"]
    assert "prime_qr" in atlas["leaderboards"]
    assert atlas["schema_version"] == "2.16"
    assert atlas["dataset_kind"] == "published_example_atlas"
    assert atlas["manifest"]["publication_layer"] == "published"
    assert "data/lean_worked_examples.json" in atlas["manifest"]["source_files"]
    assert "data/theorem_witnesses.json" in atlas["manifest"]["source_files"]
    assert "data/throughlines.json" in atlas["manifest"]["source_files"]
    assert "throughlines" in atlas
    assert atlas["throughlines"]["featured_ids"] == ["orbit_plus_carry_factorization"]
    throughline = atlas["throughlines"]["rows"][0]
    assert throughline["kind"] == "research-thesis"
    assert "carry_dfa_factorization" in throughline["open_claim_ids"]
    assert "orbit_carry_frontier" in {entry["atlas_section_id"] for entry in throughline["featured_searches"]}
    assert "state_merging" in {entry["atlas_section_id"] for entry in throughline["featured_searches"]}
    assert "state_merging_same_core" in {entry["atlas_section_id"] for entry in throughline["featured_searches"]}
    assert "state_merging_research" in {entry["atlas_section_id"] for entry in throughline["featured_searches"]}
    assert "claim_witnesses" in atlas
    witness_rows = atlas["claim_witnesses"]["rows"]
    witness_ids = {row["witness_id"] for row in witness_rows}
    assert "series_q_weighted_identity_prime97_stride2" in witness_ids
    assert "small_k_visibility_threshold_target_97_249_996" in witness_ids
    witness_rows_by_id = {row["witness_id"]: row for row in witness_rows}
    assert witness_rows_by_id["series_q_weighted_identity_prime97_stride2"]["lean_example_namespaces"] == [
        "QRTour.Prime97"
    ]
    assert witness_rows_by_id["series_q_weighted_identity_prime97_stride2"]["lean_examples"] == [
        _lean_worked_example_row("QRTour.Prime97")
    ]
    assert witness_rows_by_id["same_core_threshold_shift_interval_996_over_249"]["lean_example_namespaces"] == [
        "QRTour.Composite996"
    ]
    assert witness_rows_by_id["same_core_threshold_shift_interval_996_over_249"]["lean_examples"][0][
        "namespace"
    ] == "QRTour.Composite996"
    assert "sameCore_firstVisibleMismatchPosition_shift_exact" in witness_rows_by_id[
        "same_core_threshold_shift_interval_996_over_249"
    ]["lean_examples"][0]["theorem_names"]
    assert witness_rows_by_id["small_k_visibility_threshold_target_97_249_996"]["lean_example_namespaces"] == []
    assert witness_rows_by_id["small_k_visibility_threshold_target_97_249_996"]["lean_examples"] == []
    featured_ids = set(atlas["claim_witnesses"]["featured_ids"])
    assert {
        "series_q_weighted_identity_prime97_stride2",
        "same_core_threshold_shift_interval_996_over_249",
        "small_k_visibility_threshold_target_97_249_996",
        "carry_dfa_factorization_target_21_97_996",
    } == featured_ids
    assert "case_studies" in atlas
    assert "research_layers" in atlas
    assert "orbit_carry_frontier" in atlas["case_studies"]
    assert "carry_dfa" in atlas["case_studies"]
    assert "carry_selector" in atlas["case_studies"]
    assert "carry_selector_families" in atlas["case_studies"]
    assert "state_merging" in atlas["case_studies"]
    assert "state_merging_families" in atlas["case_studies"]
    assert "visibility" in atlas["case_studies"]
    assert "visibility_families" in atlas["case_studies"]
    assert "composite_families" in atlas["case_studies"]
    visibility_by_n = {entry["n"]: entry for entry in atlas["case_studies"]["visibility"]}
    carry_by_n = {entry["n"]: entry for entry in atlas["case_studies"]["carry_dfa"]}
    assert "small_k_visibility_threshold" in visibility_by_n[97]["claim_context"]["related_open_claim_ids"]
    assert "incoming_carry_position_formula_prime97_stride2" in visibility_by_n[97]["claim_context"]["matching_witness_ids"]
    assert "carry_dfa_factorization" in carry_by_n[97]["claim_context"]["related_open_claim_ids"]
    assert "carry_window_transducer_prime97_window6" in carry_by_n[97]["claim_context"]["matching_witness_ids"]
    selector_labels = {entry["label"] for entry in atlas["case_studies"]["carry_selector_families"]}
    assert "Same-core relabeling loss" in selector_labels
    assert "Small-multiple relabeling shift and enlargement" in selector_labels
    state_merging_by_n = {entry["n"]: entry for entry in atlas["case_studies"]["state_merging"]}
    assert set(state_merging_by_n) == {21, 89, 97, 996}
    assert state_merging_by_n[89]["obstruction_class"] == "hidden_graph_obstruction"
    assert state_merging_by_n[89]["observed_alignment_bijection"] is True
    assert state_merging_by_n[97]["forward_profile"]["max_preimage_size"] == 4
    assert state_merging_by_n[97]["reverse_profile"]["is_functional"] is False
    merging_family_labels = {entry["label"] for entry in atlas["case_studies"]["state_merging_families"]}
    assert "Same-core visible compression" in merging_family_labels
    assert "Mixed obstruction family" in merging_family_labels
    same_core_merging = next(
        entry for entry in atlas["case_studies"]["state_merging_families"]
        if entry["label"] == "Same-core visible compression"
    )
    assert same_core_merging["family_row"]["members"] == [249, 498, 996]
    assert same_core_merging["family_row"]["has_state_merging_disagreement"] is True
    mixed_family = next(
        entry for entry in atlas["case_studies"]["state_merging_families"]
        if entry["label"] == "Mixed obstruction family"
    )
    assert mixed_family["family_row"]["members"][:4] == [17, 34, 68, 85]
    assert mixed_family["family_row"]["crosses_relabeling_hidden_visible_classes"] is True
    frontier = atlas["case_studies"]["orbit_carry_frontier"]
    assert {row["n"] for row in frontier["orbit_layer_examples"] if row["n"] is not None} >= {19, 97, 249, 996}
    assert {row["n"] for row in frontier["carry_layer_examples"] if row["n"] is not None} >= {21, 97, 996}
    frontier_target_ids = {row["witness_id"] for row in frontier["frontier_targets"]}
    assert {
        "small_k_visibility_threshold_target_97_249_996",
        "carry_dfa_factorization_target_21_97_996",
        "carry_dfa_factorization_target_249_498_996_same_core",
    } <= frontier_target_ids
    obstruction_ids = {row.get("counterexample_id") for row in frontier["obstruction_families"]}
    assert "carry_state_relabeling_failure_97" in obstruction_ids
    assert "carry_selector_core_invariance_failure_996" in obstruction_ids
    assert atlas["research_layers"]["carry_selector"]["publication_status"] == "published_research_layer"
    research_bases = {entry["base"]: entry for entry in atlas["research_layers"]["carry_selector"]["bases"]}
    assert {7, 10, 12}.issubset(research_bases)
    assert research_bases[10]["non_k_one_count"] == 21
    assert research_bases[10]["same_core_multi_member_count"] == 5
    assert atlas["research_layers"]["state_merging"]["publication_status"] == "published_research_layer"
    assert atlas["research_layers"]["state_merging_same_core"]["publication_status"] == "published_research_layer"
    assert atlas["research_layers"]["state_merging"]["visible_preimage_compression_count"] > 0
    assert atlas["research_layers"]["state_merging"]["hidden_graph_obstruction_count"] > 0
    assert {row["n"] for row in atlas["research_layers"]["state_merging"]["rows"]} >= {
        17,
        21,
        34,
        68,
        85,
        89,
        97,
        249,
        498,
        996,
    }
    assert {row["core_n"] for row in atlas["research_layers"]["state_merging_same_core"]["rows"]} == {
        17,
        249,
    }
    row_17 = next(
        row for row in atlas["research_layers"]["state_merging_same_core"]["rows"] if row["core_n"] == 17
    )
    assert row_17["has_nonmonotone_hidden_visible_switching"] is True
    assert row_17["hidden_visible_switch_count"] == 2
    family_labels = {entry["label"] for entry in atlas["case_studies"]["visibility_families"]}
    assert "Cross-base same-core exact law" in family_labels
    assert "Cross-base interval endpoints in one coordinate" in family_labels


def test_state_merging_search_surfaces_surface_canonical_rows_and_same_core_disagreement() -> None:
    rows = state_merging_rows(1000, base=10, n_blocks=8, max_m=8)
    by_n = {row["n"]: row for row in rows}
    same_core_rows = state_merging_same_core_rows(1200, base=10, n_blocks=8, max_m=8)
    by_core = {row["core_n"]: row for row in same_core_rows}

    assert {21, 89, 97, 996}.issubset(by_n)
    assert by_n[97]["forward_profile"]["is_functional"] is True
    assert by_n[97]["reverse_profile"]["is_functional"] is False
    assert by_n[89]["obstruction_class"] == "hidden_graph_obstruction"
    assert by_n[89]["observed_alignment_bijection"] is True
    assert by_n[996]["factorization_regime"] == "quotient_candidate_only"
    assert by_n[996]["forward_profile"]["max_preimage_size"] == 4

    assert 249 in by_core
    assert by_core[249]["members"] == [249, 498, 996]
    assert by_core[249]["has_state_merging_disagreement"] is True
    assert by_core[17]["has_rehidden_after_visible"] is True
    assert by_core[17]["visibility_behavior"] == "rehiding_visible"
    assert by_core[17]["phase_summary"].startswith("same-core path")


def test_quotient_obstruction_search_surfaces_include_visible_hidden_and_family_signal() -> None:
    rows = quotient_obstruction_rows(1000, base=10, n_blocks=8, max_m=8)
    visible = [row for row in rows if row.get("group") == "visible_preimage_compression"]
    hidden = [row for row in rows if row.get("group") == "hidden_graph_obstruction"]
    families = quotient_obstruction_family_rows(1200, base=10, n_blocks=8, max_m=8)
    by_core = {row["core_n"]: row for row in families}

    assert rows[0]["group"] == "census_summary"
    assert any(row["n"] == 97 for row in visible)
    assert any(row["n"] == 996 for row in visible)
    assert any(row["n"] == 89 for row in hidden)
    assert 17 in by_core
    assert 249 in by_core
    assert by_core[17]["crosses_relabeling_hidden_visible_classes"] is True
    assert by_core[249]["has_visible_preimage_compression_member"] is True


def test_same_core_obstruction_phase_surface_highlights_nonmonotone_families() -> None:
    rows = same_core_obstruction_phase_rows(1200, base=10, n_blocks=8, max_m=8)
    by_core = {row["core_n"]: row for row in rows}

    assert rows[0]["has_nonmonotone_hidden_visible_switching"] is True
    assert by_core[17]["has_nonmonotone_hidden_visible_switching"] is True
    assert by_core[17]["hidden_visible_switch_count"] == 2
    assert by_core[29]["hidden_visible_switch_count"] == 3
    assert by_core[249]["has_nonmonotone_hidden_visible_switching"] is False
    assert by_core[249]["has_rehidden_after_visible"] is False
    assert by_core[249]["visibility_behavior"] == "one_way_visible"


def test_same_core_obstruction_correlate_surface_summarizes_rehiding_vs_one_way_visibility() -> None:
    rows = same_core_obstruction_correlate_rows(2000, base=10, n_blocks=8, max_m=8)
    onset_rows = {
        row["onset_kind"]: row
        for row in rows
        if row["group"] == "onset_correlation"
    }
    hidden_multiplier_rows = {
        row["valuation_bucket"]: row
        for row in rows
        if row["group"] == "first_hidden_multiplier_correlation"
    }
    family_examples = {row["core_n"]: row for row in rows if row["group"] == "family_examples"}

    assert rows[0]["group"] == "behavior_census"
    assert rows[0]["rehiding_visible_count"] > rows[0]["one_way_visible_count"] > 0
    assert onset_rows["visible_without_hidden"]["rehiding_count"] == 0
    assert onset_rows["visible_first"]["one_way_visible_count"] == 0
    assert hidden_multiplier_rows["v2=1,v5=0"]["rehiding_count"] > hidden_multiplier_rows["v2=1,v5=0"]["one_way_visible_count"]
    assert 17 in family_examples
    assert 167 in family_examples


def test_claim_witness_rows_surface_all_registry_witnesses() -> None:
    rows = build_claim_witness_rows()
    by_id = {row["witness_id"]: row for row in rows}

    assert "same_core_threshold_shift_interval_996_over_249" in by_id
    assert by_id["same_core_threshold_shift_interval_996_over_249"]["claim_id"] == "same_core_threshold_shift_interval"
    assert by_id["digit_periodicity_prime19_base10"]["lean_example_namespaces"] == ["QRTour.Prime19"]
    assert by_id["series_q_weighted_identity_n249_stride3"]["lean_example_namespaces"] == [
        "QRTour.Composite249"
    ]
    assert by_id["positive_q_good_modes_n249_stride3"]["lean_example_namespaces"] == ["QRTour.Composite249"]
    assert by_id["carry_window_transducer_prime97_window6"]["lean_example_namespaces"] == ["QRTour.Prime97"]
    assert by_id["carry_window_transducer_n249_window3"]["lean_example_namespaces"] == ["QRTour.Composite249"]
    assert by_id["carry_window_transducer_same_core_996_window4"]["lean_example_namespaces"] == [
        "QRTour.Composite996"
    ]
    assert by_id["digit_periodicity_prime19_base10"]["lean_examples"] == [
        _lean_worked_example_row("QRTour.Prime19")
    ]
    assert by_id["carry_window_transducer_same_core_996_window4"]["lean_examples"][0]["module_path"] == (
        "lean/QRTour/Examples.lean"
    )
    assert by_id["small_k_visibility_threshold_target_97_249_996"]["claim_status"] == "open"
    assert by_id["small_k_visibility_heuristic_family_21_37_97_249_996"]["kind"] == "empirical-witness"
    assert by_id["small_k_visibility_threshold_target_97_249_996"]["lean_example_namespaces"] == []
    assert by_id["small_k_visibility_threshold_target_97_249_996"]["lean_examples"] == []


def test_claim_witness_rows_support_claim_kind_and_status_filters() -> None:
    carry_rows = build_claim_witness_rows(claim_id="carry_window_transducer")
    carry_ids = {row["witness_id"] for row in carry_rows}

    assert carry_ids == {
        "carry_window_transducer_prime97_window6",
        "carry_window_transducer_n249_window3",
        "carry_window_transducer_same_core_996_window4",
    }
    assert all(row["claim_status"] == "implemented-here" for row in carry_rows)

    open_rows = build_claim_witness_rows(status="open", kind="open-target")
    open_ids = {row["witness_id"] for row in open_rows}

    assert open_ids == {
        "small_k_visibility_threshold_target_97_249_996",
        "carry_dfa_factorization_target_21_97_996",
        "carry_dfa_factorization_target_249_498_996_same_core",
    }
    assert all(row["kind"] == "open-target" for row in open_rows)

    same_core_rows = build_claim_witness_rows(lean_example_namespace="QRTour.Composite996")
    same_core_ids = {row["witness_id"] for row in same_core_rows}

    assert same_core_ids == {
        "preperiod_from_base_factors_n996_base10",
        "same_core_threshold_shift_interval_996_over_249",
        "carry_window_transducer_same_core_996_window4",
    }
    assert all(row["lean_example_namespaces"] == ["QRTour.Composite996"] for row in same_core_rows)


def test_claim_witness_rows_surface_both_series_witnesses() -> None:
    series_rows = build_claim_witness_rows(claim_id="series_q_weighted_identity")
    series_ids = {row["witness_id"] for row in series_rows}

    assert series_ids == {
        "series_q_weighted_identity_prime97_stride2",
        "series_q_weighted_identity_n249_stride3",
    }
    assert all(row["claim_status"] == "reproved-here" for row in series_rows)


def test_claim_witness_rows_reject_unknown_filters() -> None:
    with pytest.raises(ValueError, match="unknown claim_id"):
        build_claim_witness_rows(claim_id="not_a_claim")

    with pytest.raises(ValueError, match="unknown claim status"):
        build_claim_witness_rows(status="lean-formalized")

    with pytest.raises(ValueError, match="unknown witness kind"):
        build_claim_witness_rows(kind="witness")

    with pytest.raises(ValueError, match="unknown lean example namespace"):
        build_claim_witness_rows(lean_example_namespace="QRTour.NotARealExample")


def test_orbit_carry_frontier_rows_surface_canonical_groups() -> None:
    rows = orbit_carry_frontier_rows(1200, base=10, n_blocks=8)

    assert rows
    by_group: dict[str, list[dict[str, object]]] = {}
    for row in rows:
        by_group.setdefault(str(row["group"]), []).append(row)

    assert {row["n"] for row in by_group["carry_layer_examples"] if row["n"] is not None} >= {21, 97, 996}
    assert {row["n"] for row in by_group["orbit_layer_examples"] if row["n"] is not None} >= {19, 249, 996}
    frontier_target_ids = {row["witness_id"] for row in by_group["frontier_targets"]}
    assert "carry_dfa_factorization_target_21_97_996" in frontier_target_ids
    assert "carry_dfa_factorization_target_249_498_996_same_core" in frontier_target_ids
    obstruction_labels = {str(row["label"]) for row in by_group["obstruction_families"]}
    assert "Same-core relabeling loss" in obstruction_labels


def test_orbit_carry_frontier_groups_align_with_throughline_search_surface() -> None:
    throughline = next(record for record in load_throughlines() if record.id == "orbit_plus_carry_factorization")
    surface_ids = {entry.id for entry in throughline.featured_searches}
    grouped = build_orbit_carry_frontier_groups(max_n=1200, base=10, n_blocks=8)

    assert "orbit_carry_frontier" in surface_ids
    assert "orbit_carry_trace" in surface_ids
    assert "visibility_optics_workbench" in surface_ids
    assert "visibility_base_compare" in surface_ids
    assert "quotient_obstructions" in surface_ids
    assert "quotient_obstruction_families" in surface_ids
    assert "same_core_obstruction_correlates" in surface_ids
    assert {row["n"] for row in grouped["carry_layer_examples"] if row["n"] is not None} >= {21, 97, 996}
    same_core_frontier = next(
        row for row in grouped["frontier_targets"]
        if row["witness_id"] == "carry_dfa_factorization_target_249_498_996_same_core"
    )
    assert same_core_frontier["members"] == [249, 498, 996]


def test_orbit_carry_frontier_cli_contains_canonical_rows() -> None:
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "orbit-carry-frontier",
            "--max",
            "1200",
            "--base",
            "10",
            "--blocks",
            "8",
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    by_group: dict[str, list[dict[str, object]]] = {}
    for row in rows:
        by_group.setdefault(str(row["group"]), []).append(row)

    assert any(row.get("n") == 21 for row in by_group["carry_layer_examples"])
    assert any(row.get("n") == 97 for row in by_group["carry_layer_examples"])
    assert any(row.get("n") == 996 for row in by_group["carry_layer_examples"])
    assert any(row.get("members") == [249, 498, 996] for row in by_group["frontier_targets"])


def test_orbit_carry_trace_rows_and_cli_contain_canonical_trace() -> None:
    rows = orbit_carry_trace_rows(base=10, n_blocks=8)
    assert any(
        row["group"] == "trace_step"
        and row["n"] == 97
        and row["position"] == 4
        and row["visibility_event"] == "incoming_carry_before_overflow"
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "orbit-carry-trace",
            "--base",
            "10",
            "--blocks",
            "8",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    by_group: dict[str, list[dict[str, object]]] = {}
    for row in cli_rows:
        by_group.setdefault(str(row["group"]), []).append(row)

    assert {row["n"] for row in by_group["case_summary"]} == {21, 97, 996}
    assert any(row["n"] == 996 and row["periodic_modulus"] == 249 for row in by_group["case_summary"])
    assert any(
        row["n"] == 996
        and row["position"] == 4
        and row["visibility_event"] == "incoming_carry_before_overflow"
        for row in by_group["trace_step"]
    )


def test_visibility_optics_workbench_rows_and_cli_rank_signal() -> None:
    rows = visibility_optics_workbench_rows(max_n=500, base=10, n_blocks=8, top=10)
    assert rows[0]["group"] == "workbench_summary"
    assert any(
        row["group"] == "canonical_anchor"
        and row["n"] == 21
        and row["signal_class"] == "transparent_window"
        for row in rows
    )
    assert any(
        row["group"] == "ranked_case"
        and row["signal_class"] == "hidden_graph_obstruction"
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "visibility-optics",
            "--max",
            "500",
            "--base",
            "10",
            "--blocks",
            "8",
            "--top",
            "10",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "workbench_summary"
    assert any(row.get("signal_class") == "same_core_drift" for row in cli_rows)


def test_certified_positive_lookahead_rows_and_cli_surface_frontier_summary() -> None:
    rows = certified_positive_lookahead_state_window_rows(max_n=1000, base=10, n_blocks=8)
    assert rows[0]["group"] == "certified_positive_lookahead_summary"
    assert rows[0]["smallest_exact_gap_numerator"] == 44
    assert any(
        row["group"] == "certified_positive_lookahead_case"
        and row["n"] == 97
        and row["theorem_frontier_status"] == "empirically_coefficient_functional_frontier"
        for row in rows
    )
    assert any(
        row["group"] == "certified_positive_lookahead_case"
        and row["n"] == 68
        and row["theorem_frontier_status"] == "coefficient_functionality_counterexample_candidate"
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "visibility-certified-lookahead",
            "--max",
            "1000",
            "--base",
            "10",
            "--blocks",
            "8",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "certified_positive_lookahead_summary"
    assert any(row.get("n") == 97 for row in cli_rows if row.get("group") == "certified_positive_lookahead_case")
    assert any(row.get("n") == 996 for row in cli_rows if row.get("group") == "certified_positive_lookahead_case")
    assert any(row.get("n") == 68 for row in cli_rows if row.get("group") == "certified_positive_lookahead_case")


def test_coefficient_conflict_rows_and_cli_surface_first_obstruction() -> None:
    rows = certified_positive_lookahead_coefficient_conflict_rows(
        max_n=1000,
        base=10,
        n_blocks=8,
        top=5,
    )
    assert rows[0]["group"] == "coefficient_conflict_summary"
    first = rows[1]
    assert first["group"] == "coefficient_conflict_witness"
    assert first["n"] == 68
    assert first["conflict_remainder_state"] == 4
    assert first["conflict_coefficients"] == [588, 150528]

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "visibility-coefficient-conflicts",
            "--max",
            "1000",
            "--base",
            "10",
            "--blocks",
            "8",
            "--top",
            "5",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "coefficient_conflict_summary"
    assert cli_rows[1]["n"] == 68
    assert cli_rows[1]["conflict_positions"] == [1, 5]
    assert cli_rows[1]["conflict_carry_states"] == [0, 60]


def test_coefficient_conflict_atlas_rows_and_cli_surface_cross_base() -> None:
    rows = certified_positive_lookahead_coefficient_conflict_atlas_rows(
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=12,
    )
    assert rows[0]["group"] == "coefficient_conflict_atlas_summary"
    assert rows[0]["first_base10_conflict_tuple"] == [10, 68, 4, 10000, 147, 4, 1, 6208]
    assert any(
        row["group"] == "coefficient_conflict_atlas_case"
        and row["base"] == 10
        and row["n"] == 68
        and row["base_conflict_rank"] == 1
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "visibility-coefficient-conflict-atlas",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--top",
            "20",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "coefficient_conflict_atlas_summary"
    assert cli_rows[0]["first_base10_conflict_tuple"] == [10, 68, 4, 10000, 147, 4, 1, 6208]
    assert any(
        row.get("group") == "coefficient_conflict_atlas_case"
        and row.get("base") == 10
        and row.get("n") == 68
        for row in cli_rows
    )


def test_coefficient_conflict_family_rows_and_cli_surface_recommends_composite68_family() -> None:
    rows = certified_positive_lookahead_coefficient_conflict_family_rows(
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=12,
    )
    assert rows[0]["group"] == "coefficient_conflict_family_summary"
    assert rows[0]["composite68_cross_base_family_present"] is True
    assert rows[0]["next_lean_theorem_recommendation"] == (
        "classify_composite68_cross_base_hidden_output_conflict"
    )
    assert [10, 68, 4, 10000, 147, 4, 1, 6208] in rows[0]["recommended_family_member_tuples"]

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "visibility-coefficient-conflict-families",
            "--max",
            "120",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--top",
            "12",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "coefficient_conflict_family_summary"
    assert cli_rows[0]["next_lean_theorem_recommendation"] == (
        "classify_composite68_cross_base_hidden_output_conflict"
    )
    assert any(
        row.get("group") == "coefficient_conflict_family"
        and row.get("contains_base10_68") is True
        and row.get("bases") == [10, 30]
        for row in cli_rows
    )


def test_composite68_base_sweep_rows_and_cli_surface_find_family_signal() -> None:
    rows = composite68_cross_base_obstruction_sweep_rows(max_base=120, n_blocks=8, top=0)
    assert rows[0]["group"] == "composite68_cross_base_sweep_summary"
    assert rows[0]["target_shape_bases"] == [10, 30, 32, 64, 66, 72, 98, 100]
    assert rows[0]["base30_package_candidate_tuple"] == [30, 68, 3, 27000, 397, 4, 1, 10208]
    assert rows[0]["recommended_next_lean_task"] == (
        "add_composite68_base30_finite_package_then_cross_base_shape_lemma"
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "visibility-composite68-base-sweep",
            "--max-base",
            "120",
            "--blocks",
            "8",
            "--top",
            "20",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "composite68_cross_base_sweep_summary"
    assert cli_rows[0]["target_shape_bases"] == [10, 30, 32, 64, 66, 72, 98, 100]
    assert any(
        row.get("group") == "composite68_cross_base_sweep_case"
        and row.get("base") == 30
        and row.get("lean_package_role") == "next_base30_package_candidate"
        and row.get("selected_block_base_mod_68") == 4
        for row in cli_rows
    )


def test_composite68_congruence_family_rows_and_cli_surface_classify_family() -> None:
    rows = composite68_congruence_family_rows(max_base=120, max_m=8, n_blocks=8, top=0)
    assert rows[0]["group"] == "composite68_congruence_family_summary"
    known_targets = {10, 30, 32, 64, 66, 72, 98, 100}
    assert known_targets <= set(rows[0]["hidden_output_shape_bases"])
    assert rows[0]["all_congruence_rows_have_k_eq_4"] is True
    assert rows[0]["all_congruence_rows_have_B_mod_68_eq_4"] is True
    assert rows[0]["lean_obstruction_covered_rows"] == rows[0]["total_congruence_rows"]

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "visibility-composite68-congruence-family",
            "--max-base",
            "120",
            "--max-m",
            "8",
            "--blocks",
            "8",
            "--top",
            "0",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "composite68_congruence_family_summary"
    assert known_targets <= set(cli_rows[0]["hidden_output_shape_bases"])
    assert any(
        row.get("group") == "composite68_congruence_family_case"
        and row.get("base") == 10
        and row.get("m") == 4
        and row.get("selected_block_base_mod_68") == 4
        and row.get("lean_obstruction_covered") is True
        for row in cli_rows
    )
    assert any(
        row.get("group") == "composite68_congruence_family_case"
        and row.get("base") == 30
        and row.get("m") == 3
        and row.get("composite68_hidden_output_shape_match") is True
        for row in cli_rows
    )


def test_certificate_workbench_rows_and_cli_surface_lean_ready_anchors() -> None:
    rows = certificate_workbench_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    assert rows[0]["group"] == "certificate_workbench_summary"
    assert rows[0]["first_lean_ready_tuple"] == [10, 68, 4, 10000, 147, 4, 1, 6208]
    assert any(
        row["group"] == "certificate_workbench_case"
        and row["base"] == 10
        and row["n"] == 68
        and row["certificate_class"] == "lean_ready_hidden_conflict"
        for row in rows
    )
    assert any(
        row["group"] == "certificate_workbench_case"
        and row["base"] == 30
        and row["n"] == 68
        and row["lean_readiness"] == "existing_composite68_family_theorem"
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "visibility-certificate-workbench",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--top",
            "20",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "certificate_workbench_summary"
    assert cli_rows[0]["recommended_next_lean_task"] == "reuse_composite68_family_certificate"
    assert any(
        row.get("group") == "certificate_workbench_case"
        and row.get("base") == 10
        and row.get("n") == 68
        and row.get("certificate_class") == "lean_ready_hidden_conflict"
        for row in cli_rows
    )
    assert any(
        row.get("group") == "certificate_workbench_case"
        and row.get("base") == 30
        and row.get("n") == 68
        and row.get("lean_readiness") == "existing_composite68_family_theorem"
        for row in cli_rows
    )


def test_observability_atlas_rows_and_cli_surface_anchors() -> None:
    rows = observability_atlas_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    assert rows[0]["group"] == "observability_summary"
    assert rows[0]["recommended_next_observability_task"] == (
        "develop_composite68_observability_flagship"
    )
    assert any(
        row["group"] == "hidden_coefficient_conflict"
        and row["base"] == 10
        and row["n"] == 68
        and row["certificate_class"] == "lean_ready_hidden_conflict"
        for row in rows
    )
    assert any(
        row["group"] == "hidden_coefficient_conflict"
        and row["base"] == 30
        and row["n"] == 68
        and row["lean_readiness"] == "existing_composite68_family_theorem"
        for row in rows
    )
    assert any(
        row["group"] == "coefficient_functional_frontier"
        and row["base"] == 10
        and row["n"] == 97
        for row in rows
    )
    assert any(
        row["group"] == "coefficient_functional_frontier"
        and row["base"] == 10
        and row["n"] == 996
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "observability-atlas",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--top",
            "20",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "observability_summary"
    assert any(
        row.get("group") == "hidden_coefficient_conflict"
        and row.get("base") == 10
        and row.get("n") == 68
        for row in cli_rows
    )
    assert any(
        row.get("group") == "hidden_coefficient_conflict"
        and row.get("base") == 30
        and row.get("n") == 68
        for row in cli_rows
    )
    assert any(
        row.get("group") == "coefficient_functional_frontier"
        and row.get("base") == 10
        and row.get("n") == 97
        for row in cli_rows
    )
    assert any(
        row.get("group") == "coefficient_functional_frontier"
        and row.get("base") == 10
        and row.get("n") == 996
        for row in cli_rows
    )


def test_observability_program_atlas_rows_and_cli_surface() -> None:
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
    assert rows[0]["source_pinned_positive_reconstruction_cases"] == 26
    assert rows[0]["empirical_positive_reconstruction_candidates"] > 0
    assert rows[0]["positive_reconstruction_arithmetic_criterion_id"] == (
        "finite_remainder_state_injective_on_window"
    )
    assert rows[0]["positive_reconstruction_injective_window_criterion_cases"] == (
        rows[0]["emitted_positive_reconstruction_candidates"]
    )
    assert rows[0]["positive_reconstruction_power_no_collision_criterion_id"] == (
        "finite_remainder_power_residue_no_collision"
    )
    assert rows[0]["positive_reconstruction_power_no_collision_criterion_cases"] == (
        rows[0]["emitted_positive_reconstruction_candidates"]
    )
    assert rows[0]["positive_reconstruction_power_no_wrap_criterion_id"] == (
        "finite_remainder_power_residue_no_wrap"
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
    assert rows[0]["first_unpinned_positive_reconstruction_family_seed_tuples"] == [
        [7, 170, 3, 343, 2, 3, 1, 255]
    ]
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
    assert rows[0]["positive_reconstruction_family_factor_through_theorem"] == (
        "QRTour.Base7K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
    )
    assert rows[0]["recommended_positive_reconstruction_decision"] == (
        "use_lean_proved_family_criterion_before_source_pinning_more_examples"
    )
    assert rows[0]["recommended_positive_reconstruction_next_task"] == (
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
    assert rows[0][
        "first_uncovered_positive_reconstruction_remainder_power_residue_window"
    ] == [1, 3, 9, 27, 81, 243, 7, 21]
    assert rows[0]["first_uncovered_positive_reconstruction_family_signal"] == (
        "same_base_block_remainder_as_source_pinned_candidate"
    )
    assert rows[0]["first_uncovered_positive_reconstruction_family_seed_tuples"] == [
        [10, 277, 5, 100000, 361, 3, 1, 31479]
    ]
    assert rows[0]["first_uncovered_positive_reconstruction_decision"] == (
        "pursue_family_criterion_before_source_pinning_more_examples"
    )
    assert rows[0]["first_uncovered_positive_reconstruction_next_task"] == (
        "prove_or_reject_same_base_block_remainder_power_no_collision_family"
    )
    assert any(
        row.get("group") == "observability_program_lane"
        and row.get("program_lane_id") == "composite68_shape17_obstruction_lane"
        for row in rows
    )
    assert any(
        row.get("group") == "observability_program_lane"
        and row.get("program_lane_id") == "positive_reconstruction_lane"
        for row in rows
    )
    assert any(
        row.get("group") == "observability_program_family"
        and row.get("program_family_id") == "shape187_k188_same_position_scaling"
        for row in rows
    )
    assert any(
        row.get("group") == "observability_program_family"
        and row.get("program_family_id") == "shape13_k4_mod_stable_carry_loss"
        for row in rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 10
        and row.get("n") == 97
        for row in rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 10
        and row.get("n") == 996
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_factor_through_theorem")
        == "actual996_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        and row.get("positive_reconstruction_arithmetic_criterion_status")
        == "source_pinned_sufficient_criterion_satisfied"
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "observability-program-atlas",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--top",
            "50",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "observability_program_summary"
    assert cli_rows[0]["first_unpinned_positive_reconstruction_tuple"] == [
        7,
        340,
        3,
        343,
        1,
        3,
        1,
        299,
    ]
    assert cli_rows[0][
        "first_unpinned_positive_reconstruction_remainder_power_residue_window"
    ] == [1, 3, 9, 27, 81, 243, 49, 147]
    assert cli_rows[0]["recommended_positive_reconstruction_next_task"] == (
        "prove_or_reject_same_base_block_remainder_power_no_collision_family"
    )
    assert cli_rows[0]["first_uncovered_positive_reconstruction_tuple"] == [
        10,
        361,
        5,
        100000,
        277,
        3,
        1,
        82603,
    ]
    assert cli_rows[0][
        "first_uncovered_positive_reconstruction_remainder_power_residue_window"
    ] == [1, 3, 9, 27, 81, 243, 7, 21]
    assert cli_rows[0]["first_uncovered_positive_reconstruction_family_seed_tuples"] == [
        [10, 277, 5, 100000, 361, 3, 1, 31479]
    ]
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 30
        and row.get("n") == 897
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "lean_proved_explicit_divisor_family_criterion"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base30K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 10
        and row.get("n") == 498
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "lean_proved_explicit_divisor_family_criterion"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 10
        and row.get("n") == 714
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "lean_proved_explicit_divisor_family_criterion"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base10Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 12
        and row.get("n") == 575
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase12N575"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("remainder_power_residue_window")
        == [1, 3, 9, 27, 81, 243, 154, 462]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 12
        and row.get("n") == 75
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "lean_proved_explicit_divisor_family_criterion"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        and row.get("positive_reconstruction_frontier_coverage_moduli")
        == [23, 25, 69, 75, 115, 345, 575, 1725]
        and row.get("remainder_power_residue_window")
        == [1, 3, 9, 27, 6, 18, 54, 12]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 10
        and row.get("n") == 997
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase10N997"
        and row.get("remainder_power_residue_window")
        == [1, 3, 9, 27, 81, 243, 729, 193]
        and row.get("positive_reconstruction_frontier_covered") is True
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("n") == 1199
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase7N1199"
        and row.get("remainder_power_residue_window")
        == [1, 3, 9, 27, 81, 243, 729, 988]
        and row.get("positive_reconstruction_frontier_covered") is True
        for row in cli_rows
    )
    wide_rows = observability_program_atlas_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=80,
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("m") == 6
        and row.get("n") == 997
        and row.get("positive_reconstruction_source_pinned") is False
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base7Stride6K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        and row.get("positive_reconstruction_frontier_coverage_moduli")
        == [59, 118, 997, 1994, 58823, 117646]
        for row in wide_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 10
        and row.get("m") == 5
        and row.get("n") == 289
        and row.get("positive_reconstruction_source_pinned") is False
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base10Stride5K6PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        and row.get("positive_reconstruction_frontier_coverage_moduli")
        == [17, 34, 173, 289, 346, 578, 2941, 5882, 49997, 99994]
        and row.get("remainder_power_residue_window")
        == [1, 6, 36, 216, 140, 262, 127, 184]
        for row in wide_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 12
        and row.get("m") == 5
        and row.get("n") == 289
        and row.get("positive_reconstruction_source_pinned") is False
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "lean_proved_explicit_divisor_family_criterion"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base12Stride5K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        and row.get("positive_reconstruction_frontier_coverage_moduli")
        == [
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
        and row.get("remainder_power_residue_window")
        == [1, 3, 9, 27, 81, 243, 151, 164]
        for row in wide_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 10
        and row.get("m") == 5
        and row.get("n") == 641
        and row.get("positive_reconstruction_source_pinned") is False
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "lean_proved_explicit_divisor_family_criterion"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base10Stride5K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        and row.get("positive_reconstruction_frontier_coverage_moduli")
        == [641, 1282, 1923, 2564, 3846, 7692, 8333, 16666, 24999, 33332, 49998, 99996]
        and row.get("remainder_power_residue_window")
        == [1, 4, 16, 64, 256, 383, 250, 359]
        for row in wide_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 12
        and row.get("m") == 5
        and row.get("n") == 149
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase12N149"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        and row.get("remainder_power_residue_window")
        == [1, 2, 4, 8, 16, 32, 64, 128]
        and row.get("remainder_power_unreduced_window")
        == [1, 2, 4, 8, 16, 32, 64, 128]
        and row.get("positive_reconstruction_hyp_remainder_power_residue_no_wrap")
        is True
        and row.get("positive_reconstruction_power_no_wrap_criterion_status")
        == "source_pinned_power_no_wrap_sufficient_criterion_satisfied"
        for row in wide_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 12
        and row.get("m") == 5
        and row.get("n") == 226
        and row.get("positive_reconstruction_rank") == 57
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase12N226"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        and row.get("remainder_power_residue_window")
        == [1, 6, 36, 216, 166, 92, 100, 148]
        and row.get("raw_coefficient_window")
        == [1101, 6606, 39636, 237816, 1426896, 8561376, 51368256, 308209536]
        for row in wide_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("m") == 3
        and row.get("n") == 338
        and row.get("positive_reconstruction_rank") == 58
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase7N338"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
        and row.get("remainder_power_residue_window")
        == [1, 5, 25, 125, 287, 83, 77, 47]
        and row.get("raw_coefficient_window")
        == [1, 5, 25, 125, 625, 3125, 15625, 78125]
        for row in wide_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 12
        and row.get("n") == 146
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase12N146"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("remainder_power_residue_window")
        == [1, 4, 16, 64, 110, 2, 8, 32]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 12
        and row.get("n") == 73
        and row.get("positive_reconstruction_source_pinned") is False
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "lean_proved_explicit_divisor_family_criterion"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        and row.get("positive_reconstruction_frontier_coverage_moduli")
        == [71, 73, 142, 146, 284, 292, 5183, 10366, 20732]
        and row.get("remainder_power_residue_window")
        == [1, 4, 16, 64, 37, 2, 8, 32]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 12
        and row.get("n") == 47
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase12N47"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("remainder_power_residue_window")
        == [1, 3, 9, 27, 34, 8, 24, 25]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 12
        and row.get("n") == 141
        and row.get("positive_reconstruction_source_pinned") is False
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "lean_proved_explicit_divisor_family_criterion"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        and row.get("positive_reconstruction_frontier_coverage_moduli")
        == [47, 141]
        and row.get("remainder_power_residue_window")
        == [1, 3, 9, 27, 81, 102, 24, 72]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 30
        and row.get("n") == 794
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase30N794"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("remainder_power_residue_window")
        == [1, 4, 16, 64, 256, 230, 126, 504]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("n") == 113
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase7N113"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two"
        and row.get("remainder_power_residue_window")
        == [1, 4, 16, 64, 30, 7, 28, 112]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 12
        and row.get("n") == 691
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase12N691"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        and row.get("remainder_power_residue_window")
        == [1, 6, 36, 216, 605, 175, 359, 81]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 10
        and row.get("n") == 578
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase10N578"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        and row.get("remainder_power_residue_window")
        == [1, 6, 36, 216, 140, 262, 416, 184]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 10
        and row.get("n") == 277
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase10N277"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        and row.get("remainder_power_residue_window")
        == [1, 3, 9, 27, 81, 243, 175, 248]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("n") == 669
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase7N669"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one"
        and row.get("remainder_power_residue_window")
        == [1, 4, 16, 64, 256, 355, 82, 328]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 30
        and row.get("n") == 397
        and row.get("positive_reconstruction_source_pinned") is False
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "lean_proved_explicit_divisor_family_criterion"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        and row.get("positive_reconstruction_frontier_coverage_moduli")
        == [397, 794, 1588, 6749, 13498, 26996]
        and row.get("remainder_power_residue_window")
        == [1, 4, 16, 64, 256, 230, 126, 107]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 10
        and row.get("n") == 769
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase10N769"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("remainder_power_residue_window")
        == [1, 3, 9, 27, 81, 243, 729, 649]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 10
        and row.get("n") == 294
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase10N294"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("remainder_power_residue_window")
        == [1, 4, 16, 64, 256, 142, 274, 214]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("n") == 109
        and row.get("positive_reconstruction_source_pinned") is False
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "lean_proved_explicit_divisor_family_criterion"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        and row.get("positive_reconstruction_frontier_coverage_moduli")
        == [109, 218, 1199, 2398]
        and row.get("remainder_power_residue_window")
        == [1, 3, 9, 27, 81, 25, 75, 7]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("n") == 218
        and row.get("positive_reconstruction_source_pinned") is False
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "lean_proved_explicit_divisor_family_criterion"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        and row.get("positive_reconstruction_frontier_coverage_moduli")
        == [109, 218, 1199, 2398]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("n") == 465
        and row.get("positive_reconstruction_source_pinned") is False
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "lean_proved_explicit_divisor_family_criterion"
        and row.get("positive_reconstruction_frontier_coverage_theorem")
        == "QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem"
        and row.get("positive_reconstruction_frontier_coverage_moduli")
        == [
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
        and row.get("remainder_power_residue_window")
        == [1, 4, 16, 64, 256, 94, 376, 109]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("n") == 542
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase7N542"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("remainder_power_residue_window")
        == [1, 5, 25, 125, 83, 415, 449, 77]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("n") == 46
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase7N46"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("remainder_power_residue_window")
        == [1, 3, 9, 27, 35, 13, 39, 25]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("n") == 141
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase7N141"
        and row.get("positive_reconstruction_frontier_covered") is True
        and row.get("positive_reconstruction_frontier_coverage_status")
        == "source_pinned_finite_factor_through_theorem"
        and row.get("remainder_power_residue_window")
        == [1, 4, 16, 64, 115, 37, 7, 28]
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 12
        and row.get("n") == 142
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase12N142"
        and row.get("remainder_state_window") == [1, 2, 4, 8, 16, 32, 64, 128]
        and row.get("positive_reconstruction_hyp_remainder_state_window_injective")
        is True
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("n") == 47
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase7N47"
        and row.get("remainder_state_window") == [1, 2, 4, 8, 16, 32, 17, 34]
        and row.get("positive_reconstruction_hyp_remainder_state_window_injective")
        is True
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 12
        and row.get("n") == 71
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase12N71"
        and row.get("remainder_state_window") == [1, 2, 4, 8, 16, 32, 64, 57]
        and row.get("positive_reconstruction_hyp_remainder_state_window_injective")
        is True
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 10
        and row.get("n") == 49
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase10N49"
        and row.get("remainder_state_window") == [1, 2, 4, 8, 16, 32, 15, 30]
        and row.get("positive_reconstruction_hyp_remainder_state_window_injective")
        is True
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 30
        and row.get("n") == 299
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase30N299"
        and row.get("remainder_state_window") == [1, 3, 9, 27, 81, 243, 131, 94]
        and row.get("remainder_power_residue_window")
        == [1, 3, 9, 27, 81, 243, 131, 94]
        and row.get("positive_reconstruction_hyp_remainder_state_window_injective")
        is True
        and row.get(
            "positive_reconstruction_hyp_remainder_power_residue_window_injective"
        )
        is True
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("n") == 170
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase7N170"
        and row.get("remainder_state_window") == [1, 3, 9, 27, 81, 73, 49, 147]
        and row.get("raw_coefficient_window") == [2, 6, 18, 54, 162, 486, 1458, 4374]
        and row.get("remainder_power_residue_window")
        == [1, 3, 9, 27, 81, 73, 49, 147]
        and row.get("positive_reconstruction_hyp_remainder_state_window_injective")
        is True
        and row.get(
            "positive_reconstruction_hyp_remainder_power_residue_window_injective"
        )
        is True
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 7
        and row.get("n") == 340
        and row.get("positive_reconstruction_source_pinned") is False
        and row.get("positive_reconstruction_power_no_collision_criterion_status")
        == "empirical_power_no_collision_sufficient_criterion_satisfied"
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_positive_reconstruction_candidate"
        and row.get("base") == 10
        and row.get("n") == 98
        and row.get("positive_reconstruction_source_pinned") is True
        and row.get("positive_reconstruction_namespace") == "QRTour.FutureBase10N98"
        and row.get("remainder_state_window") == [1, 2, 4, 8, 16, 32, 64, 30]
        and row.get("positive_reconstruction_hyp_remainder_state_window_injective")
        is True
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_program_next_task"
        and row.get("program_next_task_id")
        == "prove_or_reject_same_base_block_remainder_power_no_collision_family"
        for row in cli_rows
    )


def test_observability_target_split_rows_and_cli_surface_anchors() -> None:
    rows = observability_target_split_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    assert rows[0]["group"] == "observability_target_split_summary"
    assert "raw_coefficient_nat" in rows[0]["observability_targets"]
    assert "displayed_prefix" in rows[0]["observability_targets"]

    assert any(
        row["group"] == "observability_target_split_case"
        and row["base"] == 10
        and row["n"] == 68
        and row["observability_target_id"] == "carried_block_value"
        and row["target_hides_raw_coefficient_conflict"] is True
        for row in rows
    )
    assert any(
        row["group"] == "observability_target_split_case"
        and row["base"] == 30
        and row["n"] == 68
        and row["observability_target_id"] == "raw_coefficient_nat"
        and row["target_observability_status"] == "factor_through_obstructed"
        for row in rows
    )
    assert any(
        row["group"] == "observability_target_split_case"
        and row["base"] == 10
        and row["n"] == 97
        and row["observability_target_id"] == "coefficient_mod_block_base"
        and row["target_observability_status"] == "factor_through_candidate"
        for row in rows
    )
    assert any(
        row["group"] == "observability_target_split_case"
        and row["base"] == 10
        and row["n"] == 996
        and row["observability_target_id"] == "raw_coefficient_nat"
        and row["target_observability_status"] == "factor_through_candidate"
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "observability-target-split",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--top",
            "20",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "observability_target_split_summary"
    assert any(
        row.get("group") == "observability_target_split_case"
        and row.get("base") == 10
        and row.get("n") == 68
        and row.get("observability_target_id") == "carried_block_value"
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_target_split_case"
        and row.get("base") == 30
        and row.get("n") == 68
        for row in cli_rows
    )


def test_observability_target_signature_rows_and_cli_surface_families() -> None:
    rows = observability_target_signature_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    assert rows[0]["group"] == "observability_target_signature_summary"
    assert rows[0]["recommended_next_target_signature_task"] == (
        "classify_hidden_output_normalization_family"
    )

    family_rows = [
        row
        for row in rows
        if row["group"] == "observability_target_signature_family"
    ]
    assert any(
        row["signature_family_class"]
        == "raw_coefficient_obstructed_carried_output_hidden"
        and row["contains_base10_68"] is True
        and row["contains_base30_68"] is True
        and row["carried_block_value_hidden_cases"] == row["member_count"]
        for row in family_rows
    )
    assert any(
        row["signature_family_class"] == "all_pointwise_targets_functional_frontier"
        and row["contains_base10_97"] is True
        and row["contains_base10_996"] is True
        and row["first_nonfunctional_pointwise_target"] is None
        for row in family_rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "observability-target-signatures",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--top",
            "20",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "observability_target_signature_summary"
    assert any(
        row.get("group") == "observability_target_signature_family"
        and row.get("contains_base10_68") is True
        and row.get("contains_base30_68") is True
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_target_signature_family"
        and row.get("contains_base10_97") is True
        and row.get("contains_base10_996") is True
        for row in cli_rows
    )


def test_observability_mod_stable_carry_loss_rows_and_cli_surface() -> None:
    rows = observability_mod_stable_carry_loss_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    assert rows[0]["group"] == "observability_mod_stable_carry_loss_summary"
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
    assert any(
        row["group"] == "observability_mod_stable_carry_loss_case"
        and row["base"] == 30
        and row["n"] == 26
        and row["coefficient_mod_block_base_preserved"] is True
        and row["first_nonfunctional_pointwise_target_after_raw"] == "carry_state"
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "observability-mod-stable-carry-loss",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--top",
            "20",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "observability_mod_stable_carry_loss_summary"
    assert any(
        row.get("group") == "observability_mod_stable_carry_loss_case"
        and row.get("base") == 30
        and row.get("n") == 26
        and row.get("target_signature_family_class") == "mod_stable_carry_state_loss"
        for row in cli_rows
    )


def test_observability_shape13_k4_mod_stable_carry_loss_rows_and_cli_surface() -> None:
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
    assert rows[0]["source_core_tuple"] == [30, 13, 1, 30, 2, 4, 5, 23854528]
    assert rows[0]["shifted_member_tuple"] == [30, 26, 1, 30, 1, 4, 5, 11927264]
    assert rows[0]["mod_stable_shift_proved_cases"] == 1
    assert rows[0]["mod_stable_shift_candidate_cases"] == 0
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
    assert rows[0]["recommended_next_observability_task"] == (
        "mine_wider_shape13_k4_members_or_generalize_scale_two_criterion"
    )
    assert any(
        row["group"] == "observability_shape13_k4_mod_stable_carry_loss_member"
        and row["base"] == 30
        and row["n"] == 13
        and row["shape13_k4_family_role"] == "source_core_reference"
        for row in rows
    )
    assert any(
        row["group"] == "observability_shape13_k4_mod_stable_carry_loss_member"
        and row["base"] == 30
        and row["n"] == 26
        and row["shape13_k4_family_role"] == "base_supported_shift_member"
        and row["shape13_k4_position_shift_from_core"] == 1
        and row["shape13_k4_preperiod_shift_from_core"] == 1
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "observability-shape13-k4-mod-stable-carry-loss",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--top",
            "20",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == (
        "observability_shape13_k4_mod_stable_carry_loss_summary"
    )
    assert cli_rows[0]["shape13_k4_current_scan_stop_condition"] == (
        "do_not_add_new_shape13_k4_finite_package_until_wider_scan_emits_new_member"
    )
    assert cli_rows[0]["shape13_k4_scale_two_unnamed_candidate_members"] == 0
    assert cli_rows[0]["shape13_k4_scale_two_candidate_mining_status"] == (
        "no_unnamed_scale_two_ready_members_under_current_bounds"
    )
    assert any(
        row.get("group") == "observability_shape13_k4_mod_stable_carry_loss_member"
        and row.get("base") == 30
        and row.get("n") == 26
        and row.get("shape13_k4_support_status")
        == "mod_stable_carry_loss_shift_proved_by_arithmetic_criterion"
        and row.get("shape13_k4_named_instantiation")
        == "QRTour.Shape13K4.base30_n26_sameCore_scale_two_hiddenCarryBlockValue_shift"
        and row.get("shape13_k4_next_lean_task")
        == "generalize_shape13_scale_two_criterion_beyond_base30_13_26"
        and row.get("shape13_k4_scale_two_hypotheses_hold") is True
        and row.get("shape13_k4_hyp_base_prime_support_times_two_eq_k") is True
        for row in cli_rows
    )


def test_observability_instrument_comparison_rows_and_cli_surface_shapes() -> None:
    rows = observability_instrument_comparison_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=3,
    )
    assert rows[0]["group"] == "observability_instrument_summary"
    assert rows[0]["first_source_symmetry_signature"] == (
        "periodic_modulus=17;k=4;position_gap=4"
    )
    assert any(
        row["group"] == "observability_source_symmetry_shape"
        and row["source_symmetry_signature"]
        == "periodic_modulus=17;k=4;position_gap=4"
        and row["hidden_bases"] == [10, 30]
        and row["shifted_bases"] == [10]
        for row in rows
    )
    assert any(
        row["group"] == "observability_instrument_member"
        and row["base"] == 10
        and row["n"] == 68
        and row["instrument_observation_status"] == "hides_source_symmetry"
        for row in rows
    )
    assert any(
        row["group"] == "observability_instrument_member"
        and row["base"] == 30
        and row["n"] == 68
        and row["instrument_observation_status"] == "hides_source_symmetry"
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "observability-instrument-compare",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--top",
            "3",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "observability_instrument_summary"
    assert any(
        row.get("group") == "observability_source_symmetry_shape"
        and row.get("source_symmetry_signature")
        == "periodic_modulus=17;k=4;position_gap=4"
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_instrument_member"
        and row.get("base") == 30
        and row.get("n") == 68
        for row in cli_rows
    )


def test_observability_shape17_k4_family_rows_and_cli_surface() -> None:
    rows = observability_shape17_k4_family_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    assert rows[0]["group"] == "observability_shape17_k4_family_summary"
    assert rows[0]["n_values"] == [17, 34, 68]
    assert any(
        row["group"] == "observability_shape17_k4_family_member"
        and row["base"] == 10
        and row["n"] == 17
        and row["source_symmetry_family_role"] == "periodic_core_shifted_member"
        for row in rows
    )
    assert any(
        row["group"] == "observability_shape17_k4_family_member"
        and row["base"] == 10
        and row["n"] == 68
        and row["source_symmetry_family_role"] == "composite68_style_member"
        and row["same_core_shift_support_status"]
        == "same_core_shift_proved_by_arithmetic_criterion"
        for row in rows
    )
    assert any(
        row["group"] == "observability_shape17_k4_family_member"
        and row["base"] == 30
        and row["n"] == 68
        and row["lean_readiness"] == "existing_composite68_family_theorem"
        and row["same_core_shift_support_status"]
        == "same_core_shift_proved_by_arithmetic_criterion"
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "observability-shape17-k4-family",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--top",
            "20",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "observability_shape17_k4_family_summary"
    assert any(
        row.get("group") == "observability_shape17_k4_family_member"
        and row.get("base") == 10
        and row.get("n") == 17
        and row.get("position_shift_from_canonical") == -1
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_shape17_k4_family_member"
        and row.get("base") == 30
        and row.get("n") == 68
        and row.get("same_core_shift_support_status")
        == "same_core_shift_proved_by_arithmetic_criterion"
        and row.get("same_core_shift_named_instantiation")
        == "QRTour.Shape17K4.base30_n68_sameCore_scale_one_hiddenCarryBlockValue_shift"
        and "same_core_hyp_scaled_quotient_remainder_lt_gap" in row
        and "same_core_hyp_scaled_block_remainder_lt_block_base" in row
        for row in cli_rows
    )


def test_observability_next_source_shape_family_rows_and_cli_surface() -> None:
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
    assert rows[0]["selected_shape_rank"] == 2
    assert any(
        row["group"] == "observability_next_source_shape_family_member"
        and row["base"] == 30
        and row["n"] == 374
        and row["same_core_multiplier"] == 2
        and row["base_local_coefficient_scale"] == 2
        and row["same_core_shift_support_status"] == "finite_only_hidden_conflict"
        for row in rows
    )
    assert any(
        row["group"] == "observability_next_source_shape_family_member"
        and row["base"] == 10
        and row["n"] == 748
        and row["same_core_multiplier"] == 4
        and row["base_local_coefficient_scale"] == 1
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "observability-next-source-shape-family",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--top",
            "20",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "observability_next_source_shape_family_summary"
    assert cli_rows[0]["source_symmetry_signature"] == (
        "periodic_modulus=187;k=188;position_gap=6"
    )
    assert any(
        row.get("group") == "observability_next_source_shape_family_member"
        and row.get("base") == 30
        and row.get("n") == 374
        and row.get("same_core_shift_support_status") == "finite_only_hidden_conflict"
        for row in cli_rows
    )


def test_observability_shape187_k188_family_rows_and_cli_surface() -> None:
    rows = observability_shape187_k188_family_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    assert rows[0]["group"] == "observability_shape187_k188_family_summary"
    assert rows[0]["same_position_scaling_proved_cases"] == 4
    assert rows[0]["same_position_scaling_candidate_cases"] == 2
    assert rows[0]["first_finite_package_namespace"] == "QRTour.FutureBase30N374"
    assert rows[0]["recommended_next_observability_task"] == (
        "extend_same_position_idempotent_criterion_to_remaining_shape187_rows_or_add_next_finite_package"
    )
    assert rows[0]["same_position_scaling_exported_hypothesis_record"] == (
        "BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses"
    )
    assert rows[0]["same_position_scaling_exported_hypothesis_adapter"] == (
        "BlockCoordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses"
    )
    assert any(
        row["group"] == "observability_shape187_k188_family_member"
        and row["base"] == 10
        and row["n"] == 374
        and row["same_position_scaling_support_status"]
        == "same_position_scaling_proved_by_arithmetic_criterion"
        and row["same_position_scaling_named_instantiation"]
        == "QRTour.FutureBase10N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two"
        and row["same_position_scaling_named_hypothesis_instantiation"]
        == "QRTour.FutureBase10N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
        and row["same_position_scaling_named_finite_conflict_instantiation"]
        == "QRTour.FutureBase10N374.coordinate_stateAlignments_one_two_certifiedConflict_eight_two"
        and row["same_position_scaling_expected_carry_states"] == [94, 17766]
        for row in rows
    )
    assert any(
        row["group"] == "observability_shape187_k188_family_member"
        and row["base"] == 12
        and row["n"] == 374
        and row["same_position_scaling_support_status"]
        == "same_position_scaling_proved_by_arithmetic_criterion"
        and row["same_position_scaling_named_instantiation"]
        == "QRTour.FutureBase12N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two"
        and row["same_position_scaling_named_hypothesis_instantiation"]
        == "QRTour.FutureBase12N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
        and row["same_position_scaling_named_finite_conflict_instantiation"] is None
        and row["same_position_scaling_expected_carry_states"] == [94, 17766]
        for row in rows
    )
    assert any(
        row["group"] == "observability_shape187_k188_family_member"
        and row["base"] == 30
        and row["n"] == 374
        and row["same_position_scaling_support_status"]
        == "same_position_scaling_proved_by_arithmetic_criterion"
        and row["same_position_scaling_named_instantiation"]
        == "QRTour.FutureBase30N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two"
        and row["same_position_scaling_named_hypothesis_instantiation"]
        == "QRTour.FutureBase30N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
        and row["same_position_scaling_expected_carry_states"] == [94, 17766]
        for row in rows
    )
    assert any(
        row["group"] == "observability_shape187_k188_family_member"
        and row["base"] == 30
        and row["n"] == 748
        and row["same_position_scaling_support_status"]
        == "same_position_scaling_proved_by_arithmetic_criterion"
        and row["same_position_scaling_named_instantiation"]
        == "QRTour.FutureBase30N748.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two"
        and row["same_position_scaling_named_hypothesis_instantiation"]
        == "QRTour.FutureBase30N748.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
        and row["same_position_scaling_expected_carry_states"] == [47, 8883]
        for row in rows
    )
    assert any(
        row["group"] == "observability_shape187_k188_family_member"
        and row["base"] == 10
        and row["n"] == 748
        and row["same_position_scaling_support_status"]
        == "same_position_scaling_criterion_candidate"
        and row["same_position_scaling_named_hypothesis_instantiation"] is None
        and row["same_position_scaling_exported_hypothesis_adapter"]
        == "BlockCoordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses"
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "observability-shape187-k188-family",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--top",
            "20",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "observability_shape187_k188_family_summary"
    assert cli_rows[0]["source_symmetry_signature"] == (
        "periodic_modulus=187;k=188;position_gap=6"
    )
    assert cli_rows[0]["same_position_scaling_exported_hypothesis_record"] == (
        "BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses"
    )
    assert any(
        row.get("group") == "observability_shape187_k188_family_member"
        and row.get("base") == 10
        and row.get("n") == 374
        and row.get("same_position_scaling_support_status")
        == "same_position_scaling_proved_by_arithmetic_criterion"
        and row.get("same_position_scaling_named_instantiation")
        == "QRTour.FutureBase10N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two"
        and row.get("same_position_scaling_named_hypothesis_instantiation")
        == "QRTour.FutureBase10N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
        and row.get("same_position_scaling_named_finite_conflict_instantiation")
        == "QRTour.FutureBase10N374.coordinate_stateAlignments_one_two_certifiedConflict_eight_two"
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_shape187_k188_family_member"
        and row.get("base") == 12
        and row.get("n") == 374
        and row.get("same_position_scaling_support_status")
        == "same_position_scaling_proved_by_arithmetic_criterion"
        and row.get("same_position_scaling_named_instantiation")
        == "QRTour.FutureBase12N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two"
        and row.get("same_position_scaling_named_hypothesis_instantiation")
        == "QRTour.FutureBase12N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
        and row.get("same_position_scaling_named_finite_conflict_instantiation") is None
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_shape187_k188_family_member"
        and row.get("base") == 30
        and row.get("n") == 374
        and row.get("same_position_scaling_support_status")
        == "same_position_scaling_proved_by_arithmetic_criterion"
        and row.get("same_position_scaling_named_instantiation")
        == "QRTour.FutureBase30N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two"
        and row.get("same_position_scaling_named_hypothesis_instantiation")
        == "QRTour.FutureBase30N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_shape187_k188_family_member"
        and row.get("base") == 30
        and row.get("n") == 748
        and row.get("same_position_scaling_support_status")
        == "same_position_scaling_proved_by_arithmetic_criterion"
        and row.get("same_position_scaling_named_instantiation")
        == "QRTour.FutureBase30N748.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two"
        and row.get("same_position_scaling_named_hypothesis_instantiation")
        == "QRTour.FutureBase30N748.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses"
        for row in cli_rows
    )
    assert any(
        row.get("group") == "observability_shape187_k188_family_member"
        and row.get("base") == 10
        and row.get("n") == 748
        and row.get("same_position_scaling_support_status")
        == "same_position_scaling_criterion_candidate"
        and row.get("same_position_scaling_named_hypothesis_instantiation") is None
        and row.get("same_position_scaling_exported_hypothesis_adapter")
        == "BlockCoordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses"
        for row in cli_rows
    )


def test_certificate_lean_fixture_payload_and_cli_emit_source_pinned_json() -> None:
    payload = certificate_lean_fixture_payload(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    rows = certificate_lean_fixture_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    assert payload["schema"] == "certificate-lean-fixtures-v1"
    assert payload["fixtures"] == rows
    assert payload["summary"]["emitted_fixture_count"] == 2
    assert payload["summary"]["namespaces"] == [
        "QRTour.Composite68",
        "QRTour.Composite68Base30",
    ]
    assert payload["summary"]["first_tuple"] == [10, 68, 4, 10000, 147, 4, 1, 6208]
    assert payload["summary"]["open_boundary_ids"] == [
        "small_k_visibility_threshold",
        "carry_dfa_factorization",
    ]
    assert {
        fixture["copyable_lean_stub"]["projection_accessor"]
        for fixture in payload["fixtures"]
    } == {"not_remainderToCoefficientFunctional"}
    assert all(
        fixture["copyable_lean_stub"]["recommended_theorem_name"]
        == f"{fixture['certificate_id']}_not_remainderToCoefficientFunctional"
        for fixture in payload["fixtures"]
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "visibility-certificate-lean-fixtures",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_payload = json.loads(result.stdout)
    assert cli_payload["schema"] == "certificate-lean-fixtures-v1"
    assert cli_payload["summary"]["emitted_fixture_count"] == 2
    assert [fixture["namespace"] for fixture in cli_payload["fixtures"]] == [
        "QRTour.Composite68",
        "QRTour.Composite68Base30",
    ]
    assert [fixture["certificate_tuple"] for fixture in cli_payload["fixtures"]] == [
        [10, 68, 4, 10000, 147, 4, 1, 6208],
        [30, 68, 3, 27000, 397, 4, 1, 10208],
    ]
    assert all("copyable_lean_stub" in fixture for fixture in cli_payload["fixtures"])


def test_certificate_lean_stub_payload_and_cli_emit_linted_scaffold_json() -> None:
    payload = certificate_lean_stub_payload(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    rows = certificate_lean_stub_rows(
        max_n=1200,
        bases=(7, 10, 12, 30),
        n_blocks=8,
        top=20,
    )
    assert payload["schema"] == "certificate-lean-stubs-v1"
    assert payload["summary"]["source_schema"] == "certificate-lean-fixtures-v1"
    assert payload["summary"]["emitted_stub_count"] == 2
    assert payload["summary"]["lint_passed"] == 2
    assert payload["summary"]["lint_failed"] == 0
    assert payload["stubs"] == rows
    assert [stub["namespace"] for stub in rows] == [
        "QRTour.Composite68",
        "QRTour.Composite68Base30",
    ]
    assert [stub["certificate_tuple"] for stub in rows] == [
        [10, 68, 4, 10000, 147, 4, 1, 6208],
        [30, 68, 3, 27000, 397, 4, 1, 10208],
    ]
    assert {stub["stub_scaffold_status"] for stub in rows} == {
        "copyable_projection_stub"
    }
    assert {stub["lint_status"] for stub in rows} == {"passed"}
    assert all(not stub["lint_errors"] for stub in rows)
    assert all(
        stub["copyable_lean_code"].startswith("/-- Copyable fixture stub")
        for stub in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "visibility-certificate-lean-stubs",
            "--max",
            "1200",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_payload = json.loads(result.stdout)
    assert cli_payload["schema"] == "certificate-lean-stubs-v1"
    assert cli_payload["summary"]["lint_failed"] == 0
    assert [stub["stub_theorem_name"] for stub in cli_payload["stubs"]] == [
        "base10_n68_m4_blocks8_L1_not_remainderToCoefficientFunctional",
        "base30_n68_m3_blocks8_L1_not_remainderToCoefficientFunctional",
    ]


def test_certificate_fixture_mapping_lint_stages_future_namespace_without_promotion() -> None:
    source_ready_payload = certificate_fixture_mapping_lint_payload(
        candidate_base=10,
        candidate_n=68,
        namespace="QRTour.Composite68",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(10,),
        n_blocks=8,
    )
    assert source_ready_payload["schema"] == "certificate-fixture-mapping-lint-v1"
    assert source_ready_payload["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert source_ready_payload["summary"]["source_ready"] is True
    assert source_ready_payload["summary"]["promotes_claims"] is False
    assert source_ready_payload["candidate"]["certificate_tuple"] == [
        10,
        68,
        4,
        10000,
        147,
        4,
        1,
        6208,
    ]
    assert source_ready_payload["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert source_ready_payload["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "visibility-certificate-lean-stubs",
            "--max",
            "120",
            "--bases",
            "30",
            "--blocks",
            "8",
            "--candidate-base",
            "30",
            "--candidate-n",
            "7",
            "--namespace",
            "QRTour.FutureN7",
            "--module-path",
            "lean/QRTour/Examples.lean",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    staged_payload = json.loads(result.stdout)
    assert staged_payload["schema"] == "certificate-fixture-mapping-lint-v1"
    assert staged_payload["summary"]["mapping_lint_status"] == (
        "scaffold_ready_pending_lean_source"
    )
    assert staged_payload["summary"]["source_ready"] is False
    assert staged_payload["summary"]["scaffold_ready"] is True
    assert staged_payload["summary"]["promotes_claims"] is False
    assert staged_payload["candidate"]["certificate_tuple"][:2] == [30, 7]
    source_checks = staged_payload["proposed_mapping"]["source_checks"]
    assert source_checks["module_path_exists"] is True
    assert source_checks["namespace_found"] is False
    assert source_checks["missing_source_theorem_names"]
    assert source_checks["missing_theorem_guide_mentions"]
    assert staged_payload["proposed_mapping"]["stub_lint_status"] == "passed"
    recipe = staged_payload["proposed_mapping"]["source_pinning_recipe"]
    assert recipe["recipe_id"] == "source_pinning_recipe_v1"
    assert recipe["status_transition"] == [
        "scaffold_ready_pending_lean_source",
        "source_ready_existing_mapping",
    ]
    assert recipe["required_theorem_names"] == staged_payload["proposed_mapping"][
        "required_theorem_names"
    ]
    assert recipe["record_theorem_name"] == (
        "coordinate_stateAlignments_zero_three_certifiedConflict_eight_two"
    )
    assert recipe["projection_accessor"] == "not_remainderToCoefficientFunctional"
    assert recipe["copyable_stub_theorem_name"] == (
        "base30_n7_m1_blocks8_L2_not_remainderToCoefficientFunctional"
    )
    assert "proposed_mapping.copyable_lean_stub.code" == recipe[
        "copyable_stub_field"
    ]
    assert any("theorem-guide mentions" in step for step in recipe["steps"])
    assert "No registry IDs" in recipe["promotion_boundary"]

    n7_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=30,
        candidate_n=7,
        candidate_m=1,
        namespace="QRTour.FutureBase30N7",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert n7_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert n7_source_ready["summary"]["source_ready"] is True
    assert n7_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_zero_three_certifiedConflict_eight_two",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_two",
        "base30_n7_m1_blocks8_L2_not_remainderToCoefficientFunctional",
    ]
    assert n7_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert n7_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    n14_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=30,
        candidate_n=14,
        candidate_m=1,
        namespace="QRTour.FutureBase30N14",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert n14_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert n14_source_ready["summary"]["source_ready"] is True
    assert n14_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_one_four_certifiedConflict_eight_two",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_two",
        "base30_n14_m1_blocks8_L2_not_remainderToCoefficientFunctional",
    ]
    assert n14_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert n14_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    n28_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=30,
        candidate_n=28,
        candidate_m=1,
        namespace="QRTour.FutureBase30N28",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert n28_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert n28_source_ready["summary"]["source_ready"] is True
    assert n28_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_two_five_certifiedConflict_eight_two",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_two",
        "base30_n28_m1_blocks8_L2_not_remainderToCoefficientFunctional",
    ]
    assert n28_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert n28_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base12_n10_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=12,
        candidate_n=10,
        candidate_m=1,
        namespace="QRTour.FutureBase12N10",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base12_n10_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base12_n10_source_ready["summary"]["source_ready"] is True
    assert base12_n10_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_one_five_certifiedConflict_eight_three",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_three",
        "base12_n10_m1_blocks8_L3_not_remainderToCoefficientFunctional",
    ]
    assert base12_n10_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base12_n10_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base10_n102_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=10,
        candidate_n=102,
        candidate_m=4,
        namespace="QRTour.FutureBase10N102",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base10_n102_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base10_n102_source_ready["summary"]["source_ready"] is True
    assert base10_n102_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_one_five_certifiedConflict_eight_one",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one",
        "base10_n102_m4_blocks8_L1_not_remainderToCoefficientFunctional",
    ]
    assert base10_n102_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base10_n102_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base7_n5_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=7,
        candidate_n=5,
        candidate_m=1,
        namespace="QRTour.FutureBase7N5",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base7_n5_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base7_n5_source_ready["summary"]["source_ready"] is True
    assert base7_n5_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_zero_four_certifiedConflict_eight_five",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_five",
        "base7_n5_m1_blocks8_L5_not_remainderToCoefficientFunctional",
    ]
    assert base7_n5_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base7_n5_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base12_n5_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=12,
        candidate_n=5,
        candidate_m=1,
        namespace="QRTour.FutureBase12N5",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base12_n5_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base12_n5_source_ready["summary"]["source_ready"] is True
    assert base12_n5_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_zero_four_certifiedConflict_eight_four",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_four",
        "base12_n5_m1_blocks8_L4_not_remainderToCoefficientFunctional",
    ]
    assert base12_n5_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base12_n5_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base30_n34_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=30,
        candidate_n=34,
        candidate_m=3,
        namespace="QRTour.FutureBase30N34",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base30_n34_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base30_n34_source_ready["summary"]["source_ready"] is True
    assert base30_n34_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_one_five_certifiedConflict_eight_one",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one",
        "base30_n34_m3_blocks8_L1_not_remainderToCoefficientFunctional",
    ]
    assert base30_n34_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base30_n34_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base7_n93_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=7,
        candidate_n=93,
        candidate_m=6,
        namespace="QRTour.FutureBase7N93",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base7_n93_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base7_n93_source_ready["summary"]["source_ready"] is True
    assert base7_n93_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_zero_five_certifiedConflict_eight_one",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one",
        "base7_n93_m6_blocks8_L1_not_remainderToCoefficientFunctional",
    ]
    assert base7_n93_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base7_n93_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base10_n39_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=10,
        candidate_n=39,
        candidate_m=5,
        namespace="QRTour.FutureBase10N39",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base10_n39_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base10_n39_source_ready["summary"]["source_ready"] is True
    assert base10_n39_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_zero_six_certifiedConflict_eight_one",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one",
        "base10_n39_m5_blocks8_L1_not_remainderToCoefficientFunctional",
    ]
    assert base10_n39_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base10_n39_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base10_n78_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=10,
        candidate_n=78,
        candidate_m=5,
        namespace="QRTour.FutureBase10N78",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base10_n78_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base10_n78_source_ready["summary"]["source_ready"] is True
    assert base10_n78_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_one_seven_certifiedConflict_eight_one",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one",
        "base10_n78_m5_blocks8_L1_not_remainderToCoefficientFunctional",
    ]
    assert base10_n78_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base10_n78_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base10_n96_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=10,
        candidate_n=96,
        candidate_m=2,
        namespace="QRTour.FutureBase10N96",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base10_n96_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base10_n96_source_ready["summary"]["source_ready"] is True
    assert base10_n96_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_three_four_certifiedConflict_eight_three",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_three",
        "base10_n96_m2_blocks8_L3_not_remainderToCoefficientFunctional",
    ]
    assert base10_n96_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base10_n96_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base12_n35_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=12,
        candidate_n=35,
        candidate_m=2,
        namespace="QRTour.FutureBase12N35",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base12_n35_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base12_n35_source_ready["summary"]["source_ready"] is True
    assert base12_n35_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_zero_six_certifiedConflict_eight_three",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_three",
        "base12_n35_m2_blocks8_L3_not_remainderToCoefficientFunctional",
    ]
    assert base12_n35_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base12_n35_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    base12_n31_source_ready = certificate_fixture_mapping_lint_payload(
        candidate_base=12,
        candidate_n=31,
        candidate_m=6,
        namespace="QRTour.FutureBase12N31",
        module_path="lean/QRTour/Examples.lean",
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert base12_n31_source_ready["summary"]["mapping_lint_status"] == (
        "source_ready_existing_mapping"
    )
    assert base12_n31_source_ready["summary"]["source_ready"] is True
    assert base12_n31_source_ready["proposed_mapping"]["required_theorem_names"] == [
        "coordinate_stateAlignments_zero_five_certifiedConflict_eight_one",
        "coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one",
        "base12_n31_m6_blocks8_L1_not_remainderToCoefficientFunctional",
    ]
    assert base12_n31_source_ready["proposed_mapping"]["source_checks"][
        "missing_source_theorem_names"
    ] == []
    assert base12_n31_source_ready["proposed_mapping"]["source_checks"][
        "missing_theorem_guide_mentions"
    ] == []

    auto_payload = certificate_first_scaffold_mapping_lint_payload(
        max_n=120,
        bases=(7, 10, 12, 30),
        n_blocks=8,
    )
    assert auto_payload["schema"] == "certificate-fixture-mapping-lint-v1"
    assert auto_payload["summary"]["candidate_selection_mode"] == "first_scaffold_only"
    assert auto_payload["summary"]["auto_selected_candidate"] is True
    assert auto_payload["summary"]["namespace_auto_generated"] is True
    assert auto_payload["summary"]["skipped_source_pinned_candidates"] == 2
    assert auto_payload["summary"]["mapping_lint_status"] == (
        "scaffold_ready_pending_lean_source"
    )
    assert auto_payload["candidate"]["certificate_tuple"] == [
        12,
        70,
        2,
        144,
        2,
        4,
        3,
        2363392,
    ]
    assert auto_payload["proposed_mapping"]["namespace"] == "QRTour.FutureBase12N70"
    assert auto_payload["proposed_mapping"]["source_pinning_recipe"][
        "record_theorem_name"
    ] == "coordinate_stateAlignments_one_seven_certifiedConflict_eight_three"
    assert auto_payload["proposed_mapping"]["source_pinning_recipe"][
        "copyable_stub_theorem_name"
    ] == "base12_n70_m2_blocks8_L3_not_remainderToCoefficientFunctional"
    package_plan = auto_payload["proposed_mapping"]["lean_package_plan"]
    assert package_plan["plan_id"] == "lean_finite_package_plan_v1"
    assert package_plan["candidate_id"] == "base12_n70_m2_blocks8_L3"
    assert package_plan["worth_proving_next"] is True
    assert package_plan["decision"] == "prove_next_finite_obstruction_example"
    assert package_plan["recommended_namespace"] == "QRTour.FutureBase12N70"
    assert package_plan["record_theorem_name"] == (
        "coordinate_stateAlignments_one_seven_certifiedConflict_eight_three"
    )
    assert package_plan["conflict_shape"]["conflict_remainder_state"] == 4
    assert package_plan["conflict_shape"]["conflict_positions"] == [1, 7]
    assert package_plan["conflict_shape"]["conflict_coefficients"] == [8, 32768]
    assert package_plan["conflict_shape"]["conflict_carry_states"] == [0, 936]
    assert package_plan["conflict_shape"]["conflict_block_values"] == [8, 8]
    assert package_plan["stub_theorem_name"] == (
        "base12_n70_m2_blocks8_L3_not_remainderToCoefficientFunctional"
    )
    assert any(
        "source_ready_existing_mapping" in step for step in package_plan["checklist"]
    )

    auto_result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "visibility-certificate-lean-stubs",
            "--max",
            "120",
            "--bases",
            "7,10,12,30",
            "--blocks",
            "8",
            "--first-scaffold-only",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    auto_cli_payload = json.loads(auto_result.stdout)
    assert auto_cli_payload["summary"]["candidate_selection_mode"] == (
        "first_scaffold_only"
    )
    assert auto_cli_payload["candidate"]["certificate_tuple"] == [
        12,
        70,
        2,
        144,
        2,
        4,
        3,
        2363392,
    ]
    assert auto_cli_payload["proposed_mapping"]["namespace"] == (
        "QRTour.FutureBase12N70"
    )
    assert auto_cli_payload["proposed_mapping"]["lean_package_plan"][
        "worth_proving_next"
    ] is True


def test_visibility_base_compare_rows_and_cli_compare_instruments() -> None:
    rows = visibility_base_instrument_rows(max_n=120, bases=(10, 12, 30), n_blocks=8, top=5)
    assert rows[0]["group"] == "base_instrument_summary"
    assert rows[0]["bases"] == [10, 12, 30]
    assert any(
        row["group"] == "cross_base_case"
        and row["n"] == 97
        and row["base_instrument_behavior"] in {"instrument_shift", "base30_absorption_shift"}
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "visibility-base-compare",
            "--max",
            "120",
            "--bases",
            "10,12,30",
            "--blocks",
            "8",
            "--top",
            "5",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "base_instrument_summary"
    assert any(row.get("group") == "base_summary" and row.get("base") == 30 for row in cli_rows)


def test_instrument_atlas_rows_and_cli_surface_axiom_pressure() -> None:
    rows = instrument_atlas_rows(max_n=120, bases=(10, 12, 30), n_blocks=8, top=5)
    assert rows[0]["group"] == "instrument_atlas_summary"
    assert rows[0]["source_surface"] == "visibility-base-compare"
    assert any(
        row["group"] == "instrument_case"
        and row["n"] == 97
        and row["obstructed_by_bases"] == [30]
        for row in rows
    )
    assert any(
        row["group"] == "working_axiom_signal"
        and row["signal_id"] == "visible_trace_can_hide_state_obstruction"
        and row["evidence_count"] >= 1
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "instrument-atlas",
            "--max",
            "120",
            "--bases",
            "10,12,30",
            "--blocks",
            "8",
            "--top",
            "5",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "instrument_atlas_summary"
    assert any(row.get("group") == "instrument_profile" and row.get("base") == 30 for row in cli_rows)


def test_chart_invariance_rows_and_cli_find_clean_distortion() -> None:
    rows = chart_invariance_rows(max_n=120, bases=(10, 12, 30), n_blocks=8, top=5)
    assert rows[0]["group"] == "chart_invariance_summary"
    assert any(
        row["group"] == "chart_distortion_witness"
        and row["n"] == 97
        and row["chart_invariance_class"] == "clean_chart_distortion"
        for row in rows
    )
    assert any(
        row["group"] == "chart_pair_summary"
        and row["base_pair"] == "10/30"
        and 97 in row["clean_distortion_example_ns"]
        for row in rows
    )

    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "chart-invariance",
            "--max",
            "120",
            "--bases",
            "10,12,30",
            "--blocks",
            "8",
            "--top",
            "5",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    cli_rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    assert cli_rows[0]["group"] == "chart_invariance_summary"
    assert any(row.get("group") == "chart_pair_summary" for row in cli_rows)


def test_quotient_obstruction_cli_contains_visible_hidden_and_family_rows() -> None:
    visible_hidden = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "quotient-obstructions",
            "--max",
            "500",
            "--base",
            "10",
            "--blocks",
            "8",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    visible_hidden_rows = [ast.literal_eval(line) for line in visible_hidden.stdout.splitlines() if line.strip()]
    assert visible_hidden_rows[0]["group"] == "census_summary"
    assert any(row.get("n") == 97 for row in visible_hidden_rows if row.get("group") == "visible_preimage_compression")
    assert any(row.get("n") == 89 for row in visible_hidden_rows if row.get("group") == "hidden_graph_obstruction")

    families = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "quotient-obstruction-families",
            "--max",
            "1200",
            "--base",
            "10",
            "--blocks",
            "8",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    family_rows = [ast.literal_eval(line) for line in families.stdout.splitlines() if line.strip()]
    assert any(row.get("core_n") == 17 for row in family_rows)
    assert any(row.get("core_n") == 249 for row in family_rows)

    phases = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "same-core-obstruction-phases",
            "--max",
            "1200",
            "--base",
            "10",
            "--blocks",
            "8",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    phase_rows = [ast.literal_eval(line) for line in phases.stdout.splitlines() if line.strip()]
    assert any(row.get("core_n") == 17 and row.get("has_rehidden_after_visible") for row in phase_rows)
    assert any(
        row.get("core_n") == 29 and row.get("has_nonmonotone_hidden_visible_switching")
        for row in phase_rows
    )

    correlates = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "same-core-obstruction-correlates",
            "--max",
            "2000",
            "--base",
            "10",
            "--blocks",
            "8",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    correlate_rows = [ast.literal_eval(line) for line in correlates.stdout.splitlines() if line.strip()]
    assert correlate_rows[0]["group"] == "behavior_census"
    assert any(
        row.get("group") == "onset_correlation"
        and row.get("onset_kind") == "visible_without_hidden"
        and row.get("rehiding_count") == 0
        for row in correlate_rows
    )
    assert any(
        row.get("group") == "family_examples"
        and row.get("core_n") == 17
        and row.get("has_rehidden_after_visible")
        for row in correlate_rows
    )


def test_theorem_witness_cli_supports_lean_example_filter() -> None:
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "bridge_reptends.search",
            "theorem-witnesses",
            "--lean-example",
            "QRTour.Composite996",
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    rows = [ast.literal_eval(line) for line in result.stdout.splitlines() if line.strip()]
    witness_ids = {row["witness_id"] for row in rows}

    assert witness_ids == {
        "preperiod_from_base_factors_n996_base10",
        "same_core_threshold_shift_interval_996_over_249",
        "carry_window_transducer_same_core_996_window4",
    }
    assert all(row["lean_example_namespaces"] == ["QRTour.Composite996"] for row in rows)
    assert all(
        row["lean_examples"][0]["namespace"] == "QRTour.Composite996"
        and row["lean_examples"][0]["module_path"] == "lean/QRTour/Examples.lean"
        for row in rows
    )


def test_example_atlas_snapshot_matches_checked_in_data() -> None:
    atlas_path = ROOT / "data" / "example_atlas.json"
    expected = build_example_atlas(max_n=1200, max_p=1200, top=8)

    assert atlas_path.exists()
    assert json.loads(atlas_path.read_text()) == expected
