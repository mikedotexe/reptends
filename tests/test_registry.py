from pathlib import Path

from bridge_reptends import (
    load_claim_registry,
    load_counterexamples,
    load_lean_claim_carriers,
    load_lean_frontier_lanes,
    load_lean_module_index,
    load_lean_open_claim_boundaries,
    load_literature_map,
    load_theorem_witnesses,
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
        for item in claim.lean_support_items:
            assert (ROOT / item.module).exists()
            assert item.theorems
            assert item.role

    for record in counterexamples:
        assert record.claim_id in claim_ids


def test_lean_module_index_and_theorem_witnesses_cross_references_are_valid() -> None:
    claims = load_claim_registry()
    claim_ids = {claim.id for claim in claims}
    claim_status = {claim.id: claim.status for claim in claims}

    modules = load_lean_module_index()
    assert modules
    assert len({module.id for module in modules}) == len(modules)
    module_paths = {module.path for module in modules}
    for module in modules:
        assert module.current_role
        assert module.promotion_decision
        assert module.rationale
        assert (ROOT / module.path).exists()
        assert all(claim_id in claim_ids for claim_id in module.claim_ids)

    carriers = load_lean_claim_carriers()
    assert carriers
    assert len({record.claim_id for record in carriers}) == len(carriers)
    for record in carriers:
        assert claim_status[record.claim_id] != "open"
        assert record.module_paths
        assert record.theorem_names
        assert all(module_path in module_paths for module_path in record.module_paths)

    boundaries = load_lean_open_claim_boundaries()
    assert boundaries
    assert len({record.claim_id for record in boundaries}) == len(boundaries)
    for record in boundaries:
        assert claim_status[record.claim_id] == "open"
        assert record.segments
        for segment in record.segments:
            assert segment.summary
            assert segment.module_paths
            assert all(module_path in module_paths for module_path in segment.module_paths)

    frontier_lanes = load_lean_frontier_lanes()
    assert frontier_lanes
    assert len({lane.label for lane in frontier_lanes}) == len(frontier_lanes)
    for lane in frontier_lanes:
        assert lane.label
        assert lane.summary

    witnesses = load_theorem_witnesses()
    assert witnesses
    assert len({witness.id for witness in witnesses}) == len(witnesses)
    theorem_witness_ids_by_claim: dict[str, list[str]] = {}
    for witness in witnesses:
        assert witness.claim_id in claim_ids
        assert witness.kind
        assert witness.label
        assert witness.tuple_display
        assert witness.summary
        assert witness.parameters
        if witness.kind == "theorem-witness":
            theorem_witness_ids_by_claim.setdefault(witness.claim_id, []).append(witness.id)
        for evidence_path in witness.evidence:
            assert (ROOT / evidence_path).exists()

    for record in carriers:
        assert theorem_witness_ids_by_claim.get(record.claim_id), (
            f"claim carrier {record.claim_id} should have at least one theorem witness"
        )


def test_lean_module_index_covers_tracked_lean_sources() -> None:
    indexed_paths = {module.path for module in load_lean_module_index()}
    tracked_paths = {
        path.relative_to(ROOT).as_posix()
        for path in (ROOT / "lean").rglob("*.lean")
        if path.name != "lakefile.lean" and ".lake" not in path.parts
    }

    missing = tracked_paths - indexed_paths
    extra = indexed_paths - tracked_paths
    assert not missing and not extra, f"missing={sorted(missing)}, extra={sorted(extra)}"


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
