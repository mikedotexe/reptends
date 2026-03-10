from pathlib import Path

from bridge_reptends import (
    load_claim_registry,
    load_counterexamples,
    load_literature_map,
    load_vocabulary,
)


ROOT = Path(__file__).resolve().parent.parent


def test_claim_registry_cross_references_are_valid() -> None:
    claims = load_claim_registry()
    claim_ids = {claim.id for claim in claims}

    counterexamples = load_counterexamples()
    counterexample_ids = {record.id for record in counterexamples}

    sources = load_literature_map()
    source_ids = {source.id for source in sources}
    vocabulary = load_vocabulary()
    vocabulary_ids = {entry.id for entry in vocabulary}

    for claim in claims:
        assert all(source_id in source_ids for source_id in claim.source_ids)
        assert all(counterexample_id in counterexample_ids for counterexample_id in claim.counterexample_ids)
        assert all(vocabulary_id in vocabulary_ids for vocabulary_id in claim.vocabulary_ids)
        for evidence_path in claim.evidence:
            assert (ROOT / evidence_path).exists()

    for record in counterexamples:
        assert record.claim_id in claim_ids


def test_vocabulary_entries_have_preferred_labels_and_aliases() -> None:
    vocabulary = load_vocabulary()
    assert vocabulary
    for entry in vocabulary:
        assert entry.preferred_label
        assert entry.meaning
        assert entry.scope
        assert entry.repo_aliases


def test_claim_registry_includes_explicit_open_section() -> None:
    claims = load_claim_registry()
    open_claims = [claim for claim in claims if claim.status == "open"]

    assert open_claims
    assert {claim.id for claim in open_claims} == {
        "small_k_visibility_threshold",
        "carry_dfa_factorization",
    }
