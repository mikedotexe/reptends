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
    composite_profile_rows,
    find_legacy_counterexamples,
    load_lean_worked_examples,
    load_throughlines,
    orbit_carry_frontier_rows,
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
