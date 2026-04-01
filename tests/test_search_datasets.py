import json
from pathlib import Path

import pytest

from bridge_reptends import (
    build_claim_witness_rows,
    build_example_atlas,
    composite_profile_rows,
    find_legacy_counterexamples,
    rank_bridge_candidates,
    rank_composite_highlights,
    rank_prime_qr_examples,
    rank_q_one_bridges,
)

ROOT = Path(__file__).resolve().parent.parent


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
    assert atlas["schema_version"] == "2.9"
    assert atlas["dataset_kind"] == "published_example_atlas"
    assert atlas["manifest"]["publication_layer"] == "published"
    assert "data/theorem_witnesses.json" in atlas["manifest"]["source_files"]
    assert "claim_witnesses" in atlas
    witness_rows = atlas["claim_witnesses"]["rows"]
    witness_ids = {row["witness_id"] for row in witness_rows}
    assert "series_q_weighted_identity_prime97_stride2" in witness_ids
    assert "small_k_visibility_threshold_target_97_249_996" in witness_ids
    featured_ids = set(atlas["claim_witnesses"]["featured_ids"])
    assert {
        "series_q_weighted_identity_prime97_stride2",
        "same_core_threshold_shift_interval_996_over_249",
        "small_k_visibility_threshold_target_97_249_996",
        "carry_dfa_factorization_target_21_97_996",
    } == featured_ids
    assert "case_studies" in atlas
    assert "research_layers" in atlas
    assert "carry_dfa" in atlas["case_studies"]
    assert "carry_selector" in atlas["case_studies"]
    assert "carry_selector_families" in atlas["case_studies"]
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
    assert atlas["research_layers"]["carry_selector"]["publication_status"] == "published_research_layer"
    research_bases = {entry["base"]: entry for entry in atlas["research_layers"]["carry_selector"]["bases"]}
    assert {7, 10, 12}.issubset(research_bases)
    assert research_bases[10]["non_k_one_count"] == 21
    assert research_bases[10]["same_core_multi_member_count"] == 5
    family_labels = {entry["label"] for entry in atlas["case_studies"]["visibility_families"]}
    assert "Cross-base same-core exact law" in family_labels
    assert "Cross-base interval endpoints in one coordinate" in family_labels


def test_claim_witness_rows_surface_all_registry_witnesses() -> None:
    rows = build_claim_witness_rows()
    by_id = {row["witness_id"]: row for row in rows}

    assert "same_core_threshold_shift_interval_996_over_249" in by_id
    assert by_id["same_core_threshold_shift_interval_996_over_249"]["claim_id"] == "same_core_threshold_shift_interval"
    assert by_id["small_k_visibility_threshold_target_97_249_996"]["claim_status"] == "open"
    assert by_id["small_k_visibility_heuristic_family_21_37_97_249_996"]["kind"] == "empirical-witness"


def test_claim_witness_rows_support_claim_kind_and_status_filters() -> None:
    carry_rows = build_claim_witness_rows(claim_id="carry_window_transducer")
    carry_ids = {row["witness_id"] for row in carry_rows}

    assert carry_ids == {
        "carry_window_transducer_prime97_window6",
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


def test_claim_witness_rows_reject_unknown_filters() -> None:
    with pytest.raises(ValueError, match="unknown claim_id"):
        build_claim_witness_rows(claim_id="not_a_claim")

    with pytest.raises(ValueError, match="unknown claim status"):
        build_claim_witness_rows(status="lean-formalized")

    with pytest.raises(ValueError, match="unknown witness kind"):
        build_claim_witness_rows(kind="witness")


def test_example_atlas_snapshot_matches_checked_in_data() -> None:
    atlas_path = ROOT / "data" / "example_atlas.json"
    expected = build_example_atlas(max_n=1200, max_p=1200, top=8)

    assert atlas_path.exists()
    assert json.loads(atlas_path.read_text()) == expected
