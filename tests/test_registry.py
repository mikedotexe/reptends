from pathlib import Path

import pytest

import bridge_reptends.registry as registry_module
from bridge_reptends import (
    load_claim_registry,
    load_counterexamples,
    load_lean_claim_carriers,
    load_lean_frontier_lanes,
    load_lean_module_index,
    load_lean_open_claim_boundaries,
    load_lean_worked_examples,
    load_literature_map,
    load_throughlines,
    load_theorem_witnesses,
    load_vocabulary,
)
from bridge_reptends.registry import (
    render_lean_claim_carrier_lines,
    render_theorem_guide_next_frontier_lines,
    render_lean_worked_example_lines,
    render_open_claim_lean_support_lines,
    render_throughline_research_thesis_lines,
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
    theorem_witnesses = load_theorem_witnesses()
    witness_ids = {record.id for record in theorem_witnesses}

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

    throughlines = load_throughlines()
    assert throughlines
    assert len({record.id for record in throughlines}) == len(throughlines)
    for record in throughlines:
        assert record.kind == "research-thesis"
        assert record.title
        assert record.headline
        assert record.status_note
        assert set(record.open_claim_ids).issubset(record.claim_ids)
        assert all(claim_id in claim_ids for claim_id in record.claim_ids)
        assert all(claim_id in claim_ids for claim_id in record.open_claim_ids)
        assert all(witness_id in witness_ids for witness_id in record.witness_ids)
        assert all(counterexample_id in counterexample_ids for counterexample_id in record.counterexample_ids)
        assert record.featured_searches
        assert record.ladder
        for search in record.featured_searches:
            assert search.id
            assert search.label
            assert search.summary
            assert search.command.startswith("search-reptends ")
        for ladder in record.ladder:
            assert ladder.label
            assert ladder.summary
            assert ladder.claim_ids
            assert ladder.witness_ids


def test_claim_registry_loader_rejects_open_claim_support_module_claim_tag_drift(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "claim_registry.json"
        return [
            {
                "id": "small_k_visibility_threshold",
                "title": "Open visibility frontier",
                "statement": "fixture",
                "status": "open",
                "repo_status": "open",
                "proof_status": "fixture",
                "evidence": ["lean/QRTour/Visibility.lean"],
                "vocabulary_ids": [],
                "source_ids": [],
                "counterexample_ids": [],
                "lean_support_items": [
                    {
                        "module": "lean/QRTour/Visibility.lean",
                        "theorems": ["incomingCarry_formula"],
                        "role": "fixture support",
                    }
                ],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "load_lean_module_index",
        lambda: [
            registry_module.LeanModuleRecord(
                id="QRTour.Visibility",
                path="lean/QRTour/Visibility.lean",
                current_role="fixture",
                promotion_decision="fixture",
                claim_ids=("incoming_carry_position_formula",),
                rationale="fixture",
            )
        ],
    )

    with pytest.raises(
        ValueError,
        match="open claim support small_k_visibility_threshold lists modules without the corresponding claim tag",
    ):
        registry_module.load_claim_registry()


def test_claim_registry_loader_rejects_open_claim_support_unresolved_theorem_names(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "claim_registry.json"
        return [
            {
                "id": "carry_dfa_factorization",
                "title": "Open carry factorization frontier",
                "statement": "fixture",
                "status": "open",
                "repo_status": "open",
                "proof_status": "fixture",
                "evidence": ["lean/QRTour/CarryComparison.lean"],
                "vocabulary_ids": [],
                "source_ids": [],
                "counterexample_ids": [],
                "lean_support_items": [
                    {
                        "module": "lean/QRTour/CarryComparison.lean",
                        "theorems": ["missing_support_theorem"],
                        "role": "fixture support",
                    }
                ],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "load_lean_module_index",
        lambda: [
            registry_module.LeanModuleRecord(
                id="QRTour.CarryComparison",
                path="lean/QRTour/CarryComparison.lean",
                current_role="fixture",
                promotion_decision="fixture",
                claim_ids=("carry_dfa_factorization",),
                rationale="fixture",
            )
        ],
    )

    with pytest.raises(
        ValueError,
        match="open claim support carry_dfa_factorization references unresolved Lean declarations",
    ):
        registry_module.load_claim_registry()


def test_throughline_loader_rejects_unknown_witness_ids(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "throughlines.json"
        return [
            {
                "id": "fixture_throughline",
                "kind": "research-thesis",
                "title": "Fixture",
                "headline": "Fixture headline",
                "status_note": "Fixture status note mentioning `carry_dfa_factorization` as `open`.",
                "claim_ids": ["carry_window_transducer", "carry_dfa_factorization"],
                "open_claim_ids": ["carry_dfa_factorization"],
                "witness_ids": ["missing_witness"],
                "counterexample_ids": ["carry_state_relabeling_failure_97"],
                "featured_searches": [
                    {
                        "id": "fixture_search",
                        "label": "Fixture search",
                        "summary": "Fixture summary",
                        "command": "search-reptends orbit-carry-frontier --max 1200 --base 10 --blocks 8",
                        "atlas_section_id": "orbit_carry_frontier",
                    }
                ],
                "ladder": [
                    {
                        "id": "fixture_ladder",
                        "label": "Fixture ladder",
                        "claim_ids": ["carry_window_transducer"],
                        "witness_ids": ["missing_witness"],
                        "counterexample_ids": [],
                        "summary": "Fixture ladder summary",
                    }
                ],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "claim_lookup",
        lambda: {
            "carry_window_transducer": registry_module.ClaimRecord(
                id="carry_window_transducer",
                title="fixture",
                statement="fixture",
                status="implemented-here",
                repo_status="fixture",
                proof_status="fixture",
                evidence=(),
                vocabulary_ids=(),
                source_ids=(),
                counterexample_ids=(),
                lean_support_items=(),
            ),
            "carry_dfa_factorization": registry_module.ClaimRecord(
                id="carry_dfa_factorization",
                title="fixture open",
                statement="fixture",
                status="open",
                repo_status="fixture",
                proof_status="fixture",
                evidence=(),
                vocabulary_ids=(),
                source_ids=(),
                counterexample_ids=(),
                lean_support_items=(),
            ),
        },
    )
    monkeypatch.setattr(registry_module, "theorem_witness_lookup", lambda: {})
    monkeypatch.setattr(
        registry_module,
        "counterexample_lookup",
        lambda: {
            "carry_state_relabeling_failure_97": registry_module.CounterexampleRecord(
                id="carry_state_relabeling_failure_97",
                claim_id="carry_dfa_factorization",
                legacy_claim="fixture",
                parameters={},
                observed="fixture",
                replacement="fixture",
            )
        },
    )

    with pytest.raises(ValueError, match="references missing witness ids"):
        registry_module.load_throughlines()


def test_throughline_loader_rejects_unknown_search_surface(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "throughlines.json"
        return [
            {
                "id": "fixture_throughline",
                "kind": "research-thesis",
                "title": "Fixture",
                "headline": "Fixture headline",
                "status_note": "Fixture status note mentioning `carry_dfa_factorization` as `open`.",
                "claim_ids": ["carry_dfa_factorization"],
                "open_claim_ids": ["carry_dfa_factorization"],
                "witness_ids": ["carry_dfa_factorization_target_21_97_996"],
                "counterexample_ids": ["carry_state_relabeling_failure_97"],
                "featured_searches": [
                    {
                        "id": "fixture_search",
                        "label": "Fixture search",
                        "summary": "Fixture summary",
                        "command": "search-reptends not-a-real-surface --max 10",
                        "atlas_section_id": "orbit_carry_frontier",
                    }
                ],
                "ladder": [
                    {
                        "id": "fixture_ladder",
                        "label": "Fixture ladder",
                        "claim_ids": ["carry_dfa_factorization"],
                        "witness_ids": ["carry_dfa_factorization_target_21_97_996"],
                        "counterexample_ids": ["carry_state_relabeling_failure_97"],
                        "summary": "Fixture ladder summary",
                    }
                ],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "claim_lookup",
        lambda: {
            "carry_dfa_factorization": registry_module.ClaimRecord(
                id="carry_dfa_factorization",
                title="fixture open",
                statement="fixture",
                status="open",
                repo_status="fixture",
                proof_status="fixture",
                evidence=(),
                vocabulary_ids=(),
                source_ids=(),
                counterexample_ids=(),
                lean_support_items=(),
            )
        },
    )
    monkeypatch.setattr(
        registry_module,
        "theorem_witness_lookup",
        lambda: {
            "carry_dfa_factorization_target_21_97_996": registry_module.TheoremWitnessRecord(
                id="carry_dfa_factorization_target_21_97_996",
                claim_id="carry_dfa_factorization",
                kind="open-target",
                label="fixture witness",
                tuple_display="fixture tuple",
                parameters={"N": [21, 97, 996]},
                summary="fixture summary",
                evidence=("tests/test_registry.py",),
            )
        },
    )
    monkeypatch.setattr(
        registry_module,
        "counterexample_lookup",
        lambda: {
            "carry_state_relabeling_failure_97": registry_module.CounterexampleRecord(
                id="carry_state_relabeling_failure_97",
                claim_id="carry_dfa_factorization",
                legacy_claim="fixture",
                parameters={},
                observed="fixture",
                replacement="fixture",
            )
        },
    )

    with pytest.raises(ValueError, match="unknown search surface"):
        registry_module.load_throughlines()


def test_lean_module_index_and_theorem_witnesses_cross_references_are_valid() -> None:
    claims = load_claim_registry()
    claim_ids = {claim.id for claim in claims}
    claim_status = {claim.id: claim.status for claim in claims}

    modules = load_lean_module_index()
    assert modules
    assert len({module.id for module in modules}) == len(modules)
    module_paths = {module.path for module in modules}
    modules_by_path = {module.path: module for module in modules}
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
        assert all(
            record.claim_id in modules_by_path[module_path].claim_ids
            for module_path in record.module_paths
        ), f"claim carrier {record.claim_id} lists a module without that claim tag in lean_module_index.json"

    boundaries = load_lean_open_claim_boundaries()
    assert boundaries
    assert len({record.claim_id for record in boundaries}) == len(boundaries)
    boundaries_by_claim = {record.claim_id: record for record in boundaries}
    for record in boundaries:
        assert claim_status[record.claim_id] == "open"
        assert record.segments
        for segment in record.segments:
            assert segment.summary
            assert segment.module_paths
            assert all(module_path in module_paths for module_path in segment.module_paths)
            assert all(
                record.claim_id in modules_by_path[module_path].claim_ids
                for module_path in segment.module_paths
            ), (
                f"open claim boundary {record.claim_id} lists a module without that claim tag "
                "in lean_module_index.json"
            )

    for claim in claims:
        if claim.status != "open":
            assert not claim.lean_support_items, (
                f"non-open claim {claim.id} should not carry open-boundary lean_support_items"
            )
            continue

        support_modules = {item.module for item in claim.lean_support_items}
        boundary_modules = {
            module_path
            for segment in boundaries_by_claim[claim.id].segments
            for module_path in segment.module_paths
        }
        assert support_modules == boundary_modules, (
            f"open claim {claim.id} should keep claim_registry lean_support_items aligned "
            "with lean_open_claim_boundaries.json"
        )
        for item in claim.lean_support_items:
            assert item.module in module_paths
            assert claim.id in modules_by_path[item.module].claim_ids, (
                f"open claim support item {claim.id} -> {item.module} is missing the corresponding "
                "claim tag in lean_module_index.json"
            )

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

    witnesses_by_id = {witness.id: witness for witness in witnesses}
    worked_examples = load_lean_worked_examples()
    assert worked_examples
    assert len({record.namespace for record in worked_examples}) == len(worked_examples)
    example_surface_paths = {
        module.path for module in modules if "public example surface" in module.promotion_decision
    }
    worked_example_namespaces_by_witness_id: dict[str, list[str]] = {}
    for record in worked_examples:
        assert record.claim_ids
        assert record.theorem_names
        assert record.current_role
        assert "witness" in record.current_role.lower()
        assert "claim carrier" not in record.current_role.lower()
        assert "theorem carrier" not in record.current_role.lower()
        assert record.witness_ids
        assert record.module_path in module_paths
        assert record.module_path.endswith("QRTour/Examples.lean")
        module_record = modules_by_path[record.module_path]
        assert not module_record.claim_ids
        assert "public example surface" in module_record.promotion_decision
        assert all(claim_id in claim_ids for claim_id in record.claim_ids)
        witness_claim_ids = tuple(dict.fromkeys(witnesses_by_id[witness_id].claim_id for witness_id in record.witness_ids))
        assert record.claim_ids == witness_claim_ids, (
            f"worked example {record.namespace} should keep explicit claim ids aligned with witness ids"
        )
        for witness_id in record.witness_ids:
            assert witness_id in witnesses_by_id
            assert witnesses_by_id[witness_id].kind == "theorem-witness"
            assert record.module_path in witnesses_by_id[witness_id].evidence, (
                f"worked example {record.namespace} should point to theorem witnesses that cite "
                f"{record.module_path}"
            )
            worked_example_namespaces_by_witness_id.setdefault(witness_id, []).append(record.namespace)

    for witness in witnesses:
        if witness.kind != "theorem-witness":
            continue
        cited_example_surface_paths = [
            path for path in witness.evidence if path in example_surface_paths
        ]
        if not cited_example_surface_paths:
            continue
        namespaces = worked_example_namespaces_by_witness_id.get(witness.id, [])
        assert len(namespaces) == 1, (
            f"theorem witness {witness.id} should map to exactly one worked-example namespace, "
            f"got {namespaces}"
        )


def test_throughline_render_surface_keeps_open_boundary_explicit() -> None:
    rendered = "\n".join(render_throughline_research_thesis_lines())

    assert "research-thesis" in rendered
    assert "`orbit_plus_carry_factorization`" in rendered
    assert "`carry_dfa_factorization`" in rendered
    assert "`open`" in rendered


def test_theorem_witness_loader_rejects_unknown_claim_id(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "theorem_witnesses.json"
        return [
            {
                "id": "missing_claim_fixture",
                "claim_id": "missing_claim",
                "kind": "theorem-witness",
                "label": "Missing claim fixture",
                "tuple_display": "(fixture)",
                "parameters": {"base": 10},
                "summary": "Intentional missing-claim witness fixture.",
                "evidence": ["README.md"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(registry_module, "claim_lookup", lambda: {})
    monkeypatch.setattr(registry_module, "load_lean_module_index", lambda: [])

    with pytest.raises(
        ValueError,
        match="theorem witness missing_claim_fixture references unknown claim id missing_claim",
    ):
        registry_module.load_theorem_witnesses()


def test_theorem_witness_loader_rejects_kind_status_mismatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "theorem_witnesses.json"
        return [
            {
                "id": "open_claim_kind_fixture",
                "claim_id": "small_k_visibility_threshold",
                "kind": "theorem-witness",
                "label": "Wrong kind fixture",
                "tuple_display": "(fixture)",
                "parameters": {"base": 10},
                "summary": "Intentional witness-kind drift fixture.",
                "evidence": ["README.md"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "claim_lookup",
        lambda: {
            "small_k_visibility_threshold": registry_module.ClaimRecord(
                id="small_k_visibility_threshold",
                title="Open visibility frontier",
                statement="fixture",
                status="open",
                repo_status="open",
                proof_status="fixture",
                evidence=("README.md",),
                vocabulary_ids=(),
                source_ids=(),
                counterexample_ids=(),
                lean_support_items=(),
            )
        },
    )
    monkeypatch.setattr(registry_module, "load_lean_module_index", lambda: [])

    with pytest.raises(
        ValueError,
        match=(
            "theorem witness open_claim_kind_fixture expected witness kind open-target "
            "for claim status open, got theorem-witness"
        ),
    ):
        registry_module.load_theorem_witnesses()


def test_theorem_witness_loader_rejects_unindexed_lean_evidence_path(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "theorem_witnesses.json"
        return [
            {
                "id": "unindexed_lean_fixture",
                "claim_id": "carry_window_transducer",
                "kind": "theorem-witness",
                "label": "Unindexed Lean evidence fixture",
                "tuple_display": "(fixture)",
                "parameters": {"base": 10},
                "summary": "Intentional unindexed Lean evidence fixture.",
                "evidence": ["lean/lakefile.lean"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "claim_lookup",
        lambda: {
            "carry_window_transducer": registry_module.ClaimRecord(
                id="carry_window_transducer",
                title="Carry transducer",
                statement="fixture",
                status="implemented-here",
                repo_status="fixture",
                proof_status="fixture",
                evidence=("lean/lakefile.lean",),
                vocabulary_ids=(),
                source_ids=(),
                counterexample_ids=(),
                lean_support_items=(),
            )
        },
    )
    monkeypatch.setattr(registry_module, "load_lean_module_index", lambda: [])

    with pytest.raises(
        ValueError,
        match=(
            "theorem witness unindexed_lean_fixture references unindexed Lean module "
            r"paths \['lean/lakefile\.lean'\]"
        ),
    ):
        registry_module.load_theorem_witnesses()


def test_theorem_witness_loader_rejects_claim_evidence_overlap_drift(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "theorem_witnesses.json"
        return [
            {
                "id": "evidence_overlap_fixture",
                "claim_id": "series_q_weighted_identity",
                "kind": "theorem-witness",
                "label": "Evidence overlap fixture",
                "tuple_display": "(fixture)",
                "parameters": {"base": 10},
                "summary": "Intentional evidence-overlap drift fixture.",
                "evidence": ["tests/test_registry.py"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "claim_lookup",
        lambda: {
            "series_q_weighted_identity": registry_module.ClaimRecord(
                id="series_q_weighted_identity",
                title="q-weighted series",
                statement="fixture",
                status="reproved-here",
                repo_status="fixture",
                proof_status="fixture",
                evidence=("README.md",),
                vocabulary_ids=(),
                source_ids=(),
                counterexample_ids=(),
                lean_support_items=(),
            )
        },
    )
    monkeypatch.setattr(registry_module, "load_lean_module_index", lambda: [])

    with pytest.raises(
        ValueError,
        match=(
            "theorem witness evidence_overlap_fixture should share at least one evidence path "
            "with claim series_q_weighted_identity"
        ),
    ):
        registry_module.load_theorem_witnesses()


def test_theorem_witness_loader_rejects_duplicate_ids(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "theorem_witnesses.json"
        return [
            {
                "id": "duplicate_fixture",
                "claim_id": "series_q_weighted_identity",
                "kind": "theorem-witness",
                "label": "First duplicate witness",
                "tuple_display": "(fixture one)",
                "parameters": {"base": 10},
                "summary": "First duplicate fixture.",
                "evidence": ["README.md"],
            },
            {
                "id": "duplicate_fixture",
                "claim_id": "series_q_weighted_identity",
                "kind": "theorem-witness",
                "label": "Second duplicate witness",
                "tuple_display": "(fixture two)",
                "parameters": {"base": 10},
                "summary": "Second duplicate fixture.",
                "evidence": ["README.md"],
            },
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "claim_lookup",
        lambda: {
            "series_q_weighted_identity": registry_module.ClaimRecord(
                id="series_q_weighted_identity",
                title="q-weighted series",
                statement="fixture",
                status="reproved-here",
                repo_status="fixture",
                proof_status="fixture",
                evidence=("README.md",),
                vocabulary_ids=(),
                source_ids=(),
                counterexample_ids=(),
                lean_support_items=(),
            )
        },
    )
    monkeypatch.setattr(registry_module, "load_lean_module_index", lambda: [])

    with pytest.raises(
        ValueError,
        match="theorem witness duplicate_fixture uses duplicate witness id duplicate_fixture",
    ):
        registry_module.load_theorem_witnesses()


def test_registry_lean_surface_renderers_resolve_declared_theorem_names() -> None:
    assert render_lean_claim_carrier_lines()
    assert render_open_claim_lean_support_lines()
    assert render_lean_worked_example_lines()
    assert render_theorem_guide_next_frontier_lines()


def test_lean_frontier_lane_loader_rejects_duplicate_labels(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_frontier_lanes.json"
        return [
            {"label": "theorem frontier", "summary": "fixture summary one"},
            {"label": "theorem frontier", "summary": "fixture summary two"},
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)

    with pytest.raises(ValueError, match="Lean frontier lane labels must be unique"):
        registry_module.load_lean_frontier_lanes()


def test_lean_frontier_lane_loader_rejects_missing_summary(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_frontier_lanes.json"
        return [
            {"label": "theorem frontier", "summary": ""},
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)

    with pytest.raises(ValueError, match="Lean frontier lane 'theorem frontier' is missing a summary"):
        registry_module.load_lean_frontier_lanes()


def test_theorem_guide_next_frontier_renderer_uses_lane_registry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        registry_module,
        "load_lean_frontier_lanes",
        lambda: [
            registry_module.LeanFrontierLaneRecord(
                label="lane one",
                summary="fixture summary one",
            ),
            registry_module.LeanFrontierLaneRecord(
                label="lane two",
                summary="fixture summary two",
            ),
        ],
    )

    assert render_theorem_guide_next_frontier_lines() == (
        "- lane one: fixture summary one",
        "- lane two: fixture summary two",
    )


def test_lean_module_index_loader_rejects_module_id_path_drift(monkeypatch: pytest.MonkeyPatch) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_module_index.json"
        return [
            {
                "id": "QRTour.NotExamples",
                "path": "lean/QRTour/Examples.lean",
                "current_role": "bad test fixture",
                "promotion_decision": "keep as public support surface",
                "claim_ids": [],
                "rationale": "intentional drift fixture",
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)

    with pytest.raises(ValueError, match="uses Lean module id QRTour.NotExamples"):
        registry_module.load_lean_module_index()


def test_lean_claim_carrier_loader_rejects_module_claim_tag_drift(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_claim_carriers.json"
        return [
            {
                "claim_id": "qr_stride_classification",
                "module_paths": ["lean/QRTour/QuadraticResidues.lean"],
                "theorem_names": ["pow_isQRGenerator_iff"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "claim_lookup",
        lambda: {
            "qr_stride_classification": registry_module.ClaimRecord(
                id="qr_stride_classification",
                title="QR stride classification",
                statement="fixture",
                status="reproved-here",
                repo_status="reproved-here",
                proof_status="fixture",
                evidence=("lean/QRTour/QuadraticResidues.lean",),
                vocabulary_ids=(),
                source_ids=(),
                counterexample_ids=(),
                lean_support_items=(),
            )
        },
    )
    monkeypatch.setattr(
        registry_module,
        "load_lean_module_index",
        lambda: [
            registry_module.LeanModuleRecord(
                id="QRTour.QuadraticResidues",
                path="lean/QRTour/QuadraticResidues.lean",
                current_role="fixture",
                promotion_decision="fixture",
                claim_ids=(),
                rationale="fixture",
            )
        ],
    )
    monkeypatch.setattr(
        registry_module,
        "load_theorem_witnesses",
        lambda: [
            registry_module.TheoremWitnessRecord(
                id="qr_stride_classification_prime97_stride2",
                claim_id="qr_stride_classification",
                kind="theorem-witness",
                label="fixture witness",
                tuple_display="(base=10, p=97, stride=2, B=100, q=1, k=3)",
                parameters={"base": 10, "p": 97, "stride": 2},
                summary="fixture",
                evidence=("lean/QRTour/QuadraticResidues.lean",),
            )
        ],
    )

    with pytest.raises(
        ValueError,
        match="lists modules without the corresponding claim tag qr_stride_classification",
    ):
        registry_module.load_lean_claim_carriers()


def test_lean_claim_carrier_loader_rejects_missing_theorem_witness(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_claim_carriers.json"
        return [
            {
                "claim_id": "qr_stride_classification",
                "module_paths": ["lean/QRTour/QuadraticResidues.lean"],
                "theorem_names": ["pow_isQRGenerator_iff"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "claim_lookup",
        lambda: {
            "qr_stride_classification": registry_module.ClaimRecord(
                id="qr_stride_classification",
                title="QR stride classification",
                statement="fixture",
                status="reproved-here",
                repo_status="reproved-here",
                proof_status="fixture",
                evidence=("lean/QRTour/QuadraticResidues.lean",),
                vocabulary_ids=(),
                source_ids=(),
                counterexample_ids=(),
                lean_support_items=(),
            )
        },
    )
    monkeypatch.setattr(
        registry_module,
        "load_lean_module_index",
        lambda: [
            registry_module.LeanModuleRecord(
                id="QRTour.QuadraticResidues",
                path="lean/QRTour/QuadraticResidues.lean",
                current_role="fixture",
                promotion_decision="fixture",
                claim_ids=("qr_stride_classification",),
                rationale="fixture",
            )
        ],
    )
    monkeypatch.setattr(registry_module, "load_theorem_witnesses", lambda: [])

    with pytest.raises(ValueError, match="claim carrier qr_stride_classification is missing a theorem witness"):
        registry_module.load_lean_claim_carriers()


def test_lean_claim_carrier_loader_rejects_modules_without_named_theorem_coverage(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_claim_carriers.json"
        return [
            {
                "claim_id": "same_core_threshold_shift_interval",
                "module_paths": [
                    "lean/QRTour/Visibility.lean",
                    "lean/QRTour/CompositeVisibility.lean",
                ],
                "theorem_names": ["incomingCarry_formula"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "claim_lookup",
        lambda: {
            "same_core_threshold_shift_interval": registry_module.ClaimRecord(
                id="same_core_threshold_shift_interval",
                title="Same-core threshold shift interval",
                statement="fixture",
                status="reproved-here",
                repo_status="reproved-here",
                proof_status="fixture",
                evidence=(
                    "lean/QRTour/Visibility.lean",
                    "lean/QRTour/CompositeVisibility.lean",
                ),
                vocabulary_ids=(),
                source_ids=(),
                counterexample_ids=(),
                lean_support_items=(),
            )
        },
    )
    monkeypatch.setattr(
        registry_module,
        "load_lean_module_index",
        lambda: [
            registry_module.LeanModuleRecord(
                id="QRTour.Visibility",
                path="lean/QRTour/Visibility.lean",
                current_role="fixture",
                promotion_decision="fixture",
                claim_ids=("same_core_threshold_shift_interval",),
                rationale="fixture",
            ),
            registry_module.LeanModuleRecord(
                id="QRTour.CompositeVisibility",
                path="lean/QRTour/CompositeVisibility.lean",
                current_role="fixture",
                promotion_decision="fixture",
                claim_ids=("same_core_threshold_shift_interval",),
                rationale="fixture",
            ),
        ],
    )
    monkeypatch.setattr(
        registry_module,
        "load_theorem_witnesses",
        lambda: [
            registry_module.TheoremWitnessRecord(
                id="same_core_threshold_shift_interval_996_over_249",
                claim_id="same_core_threshold_shift_interval",
                kind="theorem-witness",
                label="fixture witness",
                tuple_display="(base=10, actual=996, core=249, stride=3, B=1000, q=1, k=4)",
                parameters={"base": 10, "actual": 996, "core": 249, "stride": 3},
                summary="fixture",
                evidence=(
                    "lean/QRTour/Visibility.lean",
                    "lean/QRTour/CompositeVisibility.lean",
                ),
            )
        ],
    )

    with pytest.raises(
        ValueError,
        match="claim carrier same_core_threshold_shift_interval lists Lean carrier modules without any named theorem coverage",
    ):
        registry_module.load_lean_claim_carriers()


def test_lean_claim_carrier_loader_rejects_modules_missing_from_claim_evidence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_claim_carriers.json"
        return [
            {
                "claim_id": "qr_stride_classification",
                "module_paths": ["lean/QRTour/QuadraticResidues.lean"],
                "theorem_names": ["pow_isQRGenerator_iff"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "claim_lookup",
        lambda: {
            "qr_stride_classification": registry_module.ClaimRecord(
                id="qr_stride_classification",
                title="QR stride classification",
                statement="fixture",
                status="reproved-here",
                repo_status="reproved-here",
                proof_status="fixture",
                evidence=("README.md",),
                vocabulary_ids=(),
                source_ids=(),
                counterexample_ids=(),
                lean_support_items=(),
            )
        },
    )
    monkeypatch.setattr(
        registry_module,
        "load_lean_module_index",
        lambda: [
            registry_module.LeanModuleRecord(
                id="QRTour.QuadraticResidues",
                path="lean/QRTour/QuadraticResidues.lean",
                current_role="fixture",
                promotion_decision="fixture",
                claim_ids=("qr_stride_classification",),
                rationale="fixture",
            )
        ],
    )
    monkeypatch.setattr(
        registry_module,
        "load_theorem_witnesses",
        lambda: [
            registry_module.TheoremWitnessRecord(
                id="qr_stride_classification_prime97_stride2",
                claim_id="qr_stride_classification",
                kind="theorem-witness",
                label="fixture witness",
                tuple_display="(base=10, p=97, stride=2, B=100, q=1, k=3)",
                parameters={"base": 10, "p": 97, "stride": 2},
                summary="fixture",
                evidence=("lean/QRTour/QuadraticResidues.lean",),
            )
        ],
    )

    with pytest.raises(
        ValueError,
        match="claim carrier qr_stride_classification lists Lean carrier modules outside claim_registry evidence",
    ):
        registry_module.load_lean_claim_carriers()


def test_lean_open_claim_boundary_loader_rejects_module_claim_tag_drift(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_open_claim_boundaries.json"
        return [
            {
                "claim_id": "small_k_visibility_threshold",
                "segments": [
                    {
                        "module_paths": ["lean/QRTour/Visibility.lean"],
                        "summary": "fixture boundary",
                    }
                ],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "claim_lookup",
        lambda: {
            "small_k_visibility_threshold": registry_module.ClaimRecord(
                id="small_k_visibility_threshold",
                title="Open visibility frontier",
                statement="fixture",
                status="open",
                repo_status="open",
                proof_status="fixture",
                evidence=("lean/QRTour/Visibility.lean",),
                vocabulary_ids=(),
                source_ids=(),
                counterexample_ids=(),
                lean_support_items=(
                    registry_module.LeanSupportItem(
                        module="lean/QRTour/Visibility.lean",
                        theorems=("incomingCarry_formula",),
                        role="fixture",
                    ),
                ),
            )
        },
    )
    monkeypatch.setattr(
        registry_module,
        "load_lean_module_index",
        lambda: [
            registry_module.LeanModuleRecord(
                id="QRTour.Visibility",
                path="lean/QRTour/Visibility.lean",
                current_role="fixture",
                promotion_decision="fixture",
                claim_ids=("incoming_carry_position_formula",),
                rationale="fixture",
            )
        ],
    )

    with pytest.raises(
        ValueError,
        match="lists modules without the corresponding claim tag small_k_visibility_threshold",
    ):
        registry_module.load_lean_open_claim_boundaries()


def test_lean_open_claim_boundary_loader_rejects_claim_registry_alignment_drift(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_open_claim_boundaries.json"
        return [
            {
                "claim_id": "small_k_visibility_threshold",
                "segments": [
                    {
                        "module_paths": ["lean/QRTour/CarryComparison.lean"],
                        "summary": "fixture boundary",
                    }
                ],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "claim_lookup",
        lambda: {
            "small_k_visibility_threshold": registry_module.ClaimRecord(
                id="small_k_visibility_threshold",
                title="Open visibility frontier",
                statement="fixture",
                status="open",
                repo_status="open",
                proof_status="fixture",
                evidence=("lean/QRTour/Visibility.lean",),
                vocabulary_ids=(),
                source_ids=(),
                counterexample_ids=(),
                lean_support_items=(
                    registry_module.LeanSupportItem(
                        module="lean/QRTour/Visibility.lean",
                        theorems=("incomingCarry_formula",),
                        role="fixture",
                    ),
                ),
            )
        },
    )
    monkeypatch.setattr(
        registry_module,
        "load_lean_module_index",
        lambda: [
            registry_module.LeanModuleRecord(
                id="QRTour.Visibility",
                path="lean/QRTour/Visibility.lean",
                current_role="fixture",
                promotion_decision="fixture",
                claim_ids=("small_k_visibility_threshold",),
                rationale="fixture",
            ),
            registry_module.LeanModuleRecord(
                id="QRTour.CarryComparison",
                path="lean/QRTour/CarryComparison.lean",
                current_role="fixture",
                promotion_decision="fixture",
                claim_ids=("small_k_visibility_threshold",),
                rationale="fixture",
            ),
        ],
    )

    with pytest.raises(
        ValueError,
        match="should stay aligned with claim_registry lean_support_items",
    ):
        registry_module.load_lean_open_claim_boundaries()


def test_lean_worked_example_loader_rejects_undeclared_namespace(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def example_module_records() -> list[registry_module.LeanModuleRecord]:
        return [
            registry_module.LeanModuleRecord(
                id="QRTour.Examples",
                path="lean/QRTour/Examples.lean",
                current_role="fixture",
                promotion_decision="keep as public example surface, not atlas-backed",
                claim_ids=(),
                rationale="fixture",
            )
        ]

    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_worked_examples.json"
        return [
            {
                "module_path": "lean/QRTour/Examples.lean",
                "namespace": "QRTour.MissingExample",
                "claim_ids": ["qr_stride_classification"],
                "theorem_names": ["k_is_qr_generator"],
                "current_role": "bad namespace witness fixture",
                "witness_ids": ["qr_stride_classification_prime97_stride2"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(registry_module, "load_lean_module_index", example_module_records)
    monkeypatch.setattr(
        registry_module,
        "load_theorem_witnesses",
        lambda: [
            registry_module.TheoremWitnessRecord(
                id="qr_stride_classification_prime97_stride2",
                claim_id="qr_stride_classification",
                kind="theorem-witness",
                label="namespace fixture witness",
                tuple_display="(base=10, p=97, stride=2, B=100, q=1, k=3)",
                parameters={"base": 10, "p": 97, "stride": 2},
                summary="Intentional namespace fixture.",
                evidence=("lean/QRTour/Examples.lean",),
            )
        ],
    )

    with pytest.raises(ValueError, match="undeclared Lean namespace QRTour.MissingExample"):
        registry_module.load_lean_worked_examples()


def test_lean_worked_example_loader_rejects_theorem_names_from_other_namespace(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def example_module_records() -> list[registry_module.LeanModuleRecord]:
        return [
            registry_module.LeanModuleRecord(
                id="QRTour.Examples",
                path="lean/QRTour/Examples.lean",
                current_role="fixture",
                promotion_decision="keep as public example surface, not atlas-backed",
                claim_ids=(),
                rationale="fixture",
            )
        ]

    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_worked_examples.json"
        return [
            {
                "module_path": "lean/QRTour/Examples.lean",
                "namespace": "QRTour.Prime97",
                "claim_ids": ["qr_stride_classification"],
                "theorem_names": ["coordinate_quotientQ_eq_four"],
                "current_role": "cross-namespace theorem witness fixture",
                "witness_ids": ["qr_stride_classification_prime97_stride2"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(registry_module, "load_lean_module_index", example_module_records)
    monkeypatch.setattr(
        registry_module,
        "load_theorem_witnesses",
        lambda: [
            registry_module.TheoremWitnessRecord(
                id="qr_stride_classification_prime97_stride2",
                claim_id="qr_stride_classification",
                kind="theorem-witness",
                label="cross-namespace theorem witness",
                tuple_display="(base=10, p=97, stride=2, B=100, q=1, k=3)",
                parameters={"base": 10, "p": 97, "stride": 2},
                summary="Intentional cross-namespace theorem fixture.",
                evidence=("lean/QRTour/Examples.lean",),
            )
        ],
    )

    with pytest.raises(
        ValueError,
        match=(
            "references unresolved Lean declarations "
            r"\['coordinate_quotientQ_eq_four'\] in namespace QRTour\.Prime97"
        ),
    ):
        registry_module.load_lean_worked_examples()


def test_lean_worked_example_loader_rejects_missing_witness_ids(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def example_module_records() -> list[registry_module.LeanModuleRecord]:
        return [
            registry_module.LeanModuleRecord(
                id="QRTour.Examples",
                path="lean/QRTour/Examples.lean",
                current_role="fixture",
                promotion_decision="keep as public example surface, not atlas-backed",
                claim_ids=(),
                rationale="fixture",
            )
        ]

    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_worked_examples.json"
        return [
            {
                "module_path": "lean/QRTour/Examples.lean",
                "namespace": "QRTour.Prime97",
                "claim_ids": ["qr_stride_classification"],
                "theorem_names": ["k_is_qr_generator"],
                "current_role": "missing witness fixture",
                "witness_ids": ["missing_witness"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(registry_module, "load_lean_module_index", example_module_records)
    monkeypatch.setattr(registry_module, "load_theorem_witnesses", lambda: [])

    with pytest.raises(ValueError, match="references missing witness ids \\['missing_witness'\\]"):
        registry_module.load_lean_worked_examples()


def test_lean_worked_example_loader_rejects_non_example_module_surface(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_worked_examples.json"
        return [
            {
                "module_path": "lean/QRTour/Examples.lean",
                "namespace": "QRTour.Prime97",
                "claim_ids": ["qr_stride_classification"],
                "theorem_names": ["k_is_qr_generator"],
                "current_role": "non-example module witness fixture",
                "witness_ids": ["qr_stride_classification_prime97_stride2"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "load_theorem_witnesses",
        lambda: [
            registry_module.TheoremWitnessRecord(
                id="qr_stride_classification_prime97_stride2",
                claim_id="qr_stride_classification",
                kind="theorem-witness",
                label="non-example module witness",
                tuple_display="(base=10, p=97, stride=2, B=100, q=1, k=3)",
                parameters={"base": 10, "p": 97, "stride": 2},
                summary="Intentional non-example module fixture.",
                evidence=("lean/QRTour/Examples.lean",),
            )
        ],
    )
    monkeypatch.setattr(
        registry_module,
        "load_lean_module_index",
        lambda: [
            registry_module.LeanModuleRecord(
                id="QRTour.Examples",
                path="lean/QRTour/Examples.lean",
                current_role="fixture",
                promotion_decision="keep as public support surface",
                claim_ids=(),
                rationale="fixture",
            )
        ],
    )

    with pytest.raises(
        ValueError,
        match="should use a Lean module classified as a public example surface",
    ):
        registry_module.load_lean_worked_examples()


def test_lean_worked_example_loader_rejects_claim_carrier_role_text(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def example_module_records() -> list[registry_module.LeanModuleRecord]:
        return [
            registry_module.LeanModuleRecord(
                id="QRTour.Examples",
                path="lean/QRTour/Examples.lean",
                current_role="fixture",
                promotion_decision="keep as public example surface, not atlas-backed",
                claim_ids=(),
                rationale="fixture",
            )
        ]

    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_worked_examples.json"
        return [
            {
                "module_path": "lean/QRTour/Examples.lean",
                "namespace": "QRTour.Prime97",
                "claim_ids": ["qr_stride_classification"],
                "theorem_names": ["k_is_qr_generator"],
                "current_role": "Canonical prime theorem carrier for the tuple `(base=10, p=97, stride=2)`.",
                "witness_ids": ["qr_stride_classification_prime97_stride2"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(registry_module, "load_lean_module_index", example_module_records)
    monkeypatch.setattr(
        registry_module,
        "load_theorem_witnesses",
        lambda: [
            registry_module.TheoremWitnessRecord(
                id="qr_stride_classification_prime97_stride2",
                claim_id="qr_stride_classification",
                kind="theorem-witness",
                label="claim-carrier-role witness",
                tuple_display="(base=10, p=97, stride=2, B=100, q=1, k=3)",
                parameters={"base": 10, "p": 97, "stride": 2},
                summary="Intentional role-text drift fixture.",
                evidence=("lean/QRTour/Examples.lean",),
            )
        ],
    )

    with pytest.raises(
        ValueError,
        match="should describe a witness-facing example role",
    ):
        registry_module.load_lean_worked_examples()


def test_lean_worked_example_loader_rejects_direct_claim_tags_on_example_module(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_worked_examples.json"
        return [
            {
                "module_path": "lean/QRTour/Examples.lean",
                "namespace": "QRTour.Prime97",
                "claim_ids": ["qr_stride_classification"],
                "theorem_names": ["k_is_qr_generator"],
                "current_role": "claim-tag drift witness fixture",
                "witness_ids": ["qr_stride_classification_prime97_stride2"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(
        registry_module,
        "load_theorem_witnesses",
        lambda: [
            registry_module.TheoremWitnessRecord(
                id="qr_stride_classification_prime97_stride2",
                claim_id="qr_stride_classification",
                kind="theorem-witness",
                label="claim-tag drift witness",
                tuple_display="(base=10, p=97, stride=2, B=100, q=1, k=3)",
                parameters={"base": 10, "p": 97, "stride": 2},
                summary="Intentional direct-claim-tag fixture.",
                evidence=("lean/QRTour/Examples.lean",),
            )
        ],
    )
    monkeypatch.setattr(
        registry_module,
        "load_lean_module_index",
        lambda: [
            registry_module.LeanModuleRecord(
                id="QRTour.Examples",
                path="lean/QRTour/Examples.lean",
                current_role="fixture",
                promotion_decision="keep as public example surface, not atlas-backed",
                claim_ids=("qr_stride_classification",),
                rationale="fixture",
            )
        ],
    )

    with pytest.raises(
        ValueError,
        match="should use a public example module without direct claim tags",
    ):
        registry_module.load_lean_worked_examples()


def test_lean_worked_example_loader_rejects_claim_witness_drift(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def example_module_records() -> list[registry_module.LeanModuleRecord]:
        return [
            registry_module.LeanModuleRecord(
                id="QRTour.Examples",
                path="lean/QRTour/Examples.lean",
                current_role="fixture",
                promotion_decision="keep as public example surface, not atlas-backed",
                claim_ids=(),
                rationale="fixture",
            )
        ]

    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_worked_examples.json"
        return [
            {
                "module_path": "lean/QRTour/Examples.lean",
                "namespace": "QRTour.Prime97",
                "claim_ids": ["qr_stride_classification"],
                "theorem_names": ["k_is_qr_generator"],
                "current_role": "claim drift witness fixture",
                "witness_ids": ["qr_stride_classification_prime97_stride2"],
            }
        ]

    drifted_witness = registry_module.TheoremWitnessRecord(
        id="qr_stride_classification_prime97_stride2",
        claim_id="series_q_weighted_identity",
        kind="theorem-witness",
        label="drifted theorem witness",
        tuple_display="(base=10, p=97, stride=2, B=100, q=1, k=3)",
        parameters={"base": 10, "p": 97, "stride": 2},
        summary="Intentional claim drift fixture.",
        evidence=("lean/QRTour/Examples.lean",),
    )

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(registry_module, "load_lean_module_index", example_module_records)
    monkeypatch.setattr(registry_module, "load_theorem_witnesses", lambda: [drifted_witness])

    with pytest.raises(ValueError, match="should keep claim ids aligned with theorem witnesses"):
        registry_module.load_lean_worked_examples()


def test_lean_worked_example_loader_rejects_witnesses_missing_examples_evidence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def example_module_records() -> list[registry_module.LeanModuleRecord]:
        return [
            registry_module.LeanModuleRecord(
                id="QRTour.Examples",
                path="lean/QRTour/Examples.lean",
                current_role="fixture",
                promotion_decision="keep as public example surface, not atlas-backed",
                claim_ids=(),
                rationale="fixture",
            )
        ]

    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_worked_examples.json"
        return [
            {
                "module_path": "lean/QRTour/Examples.lean",
                "namespace": "QRTour.Prime97",
                "claim_ids": ["qr_stride_classification"],
                "theorem_names": ["k_is_qr_generator"],
                "current_role": "missing evidence witness fixture",
                "witness_ids": ["qr_stride_classification_prime97_stride2"],
            }
        ]

    drifted_witness = registry_module.TheoremWitnessRecord(
        id="qr_stride_classification_prime97_stride2",
        claim_id="qr_stride_classification",
        kind="theorem-witness",
        label="missing evidence witness",
        tuple_display="(base=10, p=97, stride=2, B=100, q=1, k=3)",
        parameters={"base": 10, "p": 97, "stride": 2},
        summary="Intentional evidence drift fixture.",
        evidence=("lean/QRTour/QuadraticResidues.lean",),
    )

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(registry_module, "load_lean_module_index", example_module_records)
    monkeypatch.setattr(registry_module, "load_theorem_witnesses", lambda: [drifted_witness])

    with pytest.raises(
        ValueError,
        match="should point to theorem witnesses citing lean/QRTour/Examples.lean",
    ):
        registry_module.load_lean_worked_examples()


def test_lean_worked_example_loader_rejects_theorem_witness_without_namespace_coverage(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def example_module_records() -> list[registry_module.LeanModuleRecord]:
        return [
            registry_module.LeanModuleRecord(
                id="QRTour.Examples",
                path="lean/QRTour/Examples.lean",
                current_role="fixture",
                promotion_decision="keep as public example surface, not atlas-backed",
                claim_ids=(),
                rationale="fixture",
            )
        ]

    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_worked_examples.json"
        return [
            {
                "module_path": "lean/QRTour/Examples.lean",
                "namespace": "QRTour.Prime97",
                "claim_ids": ["qr_stride_classification"],
                "theorem_names": ["k_is_qr_generator"],
                "current_role": "missing namespace coverage witness fixture",
                "witness_ids": ["qr_stride_classification_prime97_stride2"],
            }
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(registry_module, "load_lean_module_index", example_module_records)
    monkeypatch.setattr(
        registry_module,
        "load_theorem_witnesses",
        lambda: [
            registry_module.TheoremWitnessRecord(
                id="qr_stride_classification_prime97_stride2",
                claim_id="qr_stride_classification",
                kind="theorem-witness",
                label="covered example witness",
                tuple_display="(base=10, p=97, stride=2, B=100, q=1, k=3)",
                parameters={"base": 10, "p": 97, "stride": 2},
                summary="Intentional covered example fixture.",
                evidence=("lean/QRTour/Examples.lean",),
            ),
            registry_module.TheoremWitnessRecord(
                id="series_q_weighted_identity_prime97_stride2",
                claim_id="series_q_weighted_identity",
                kind="theorem-witness",
                label="uncovered example witness",
                tuple_display="(base=10, N=97, stride=2, B=100, q=1, k=3)",
                parameters={"base": 10, "N": 97, "stride": 2},
                summary="Intentional uncovered example fixture.",
                evidence=("lean/QRTour/Examples.lean",),
            ),
        ],
    )

    with pytest.raises(
        ValueError,
        match=(
            "theorem witness series_q_weighted_identity_prime97_stride2 cites public example "
            r"surface\(s\) \['lean/QRTour/Examples\.lean'\] but no lean_worked_examples row references it"
        ),
    ):
        registry_module.load_lean_worked_examples()


def test_lean_worked_example_loader_rejects_theorem_witness_mapped_to_multiple_namespaces(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def example_module_records() -> list[registry_module.LeanModuleRecord]:
        return [
            registry_module.LeanModuleRecord(
                id="QRTour.Examples",
                path="lean/QRTour/Examples.lean",
                current_role="fixture",
                promotion_decision="keep as public example surface, not atlas-backed",
                claim_ids=(),
                rationale="fixture",
            )
        ]

    def fake_load_json(filename: str) -> list[dict[str, object]]:
        assert filename == "lean_worked_examples.json"
        return [
            {
                "module_path": "lean/QRTour/Examples.lean",
                "namespace": "QRTour.Prime97",
                "claim_ids": ["qr_stride_classification"],
                "theorem_names": ["k_is_qr_generator"],
                "current_role": "duplicate mapping witness fixture prime",
                "witness_ids": ["qr_stride_classification_prime97_stride2"],
            },
            {
                "module_path": "lean/QRTour/Examples.lean",
                "namespace": "QRTour.Composite249",
                "claim_ids": ["qr_stride_classification"],
                "theorem_names": ["coordinate_goodMode"],
                "current_role": "duplicate mapping witness fixture composite",
                "witness_ids": ["qr_stride_classification_prime97_stride2"],
            },
        ]

    monkeypatch.setattr(registry_module, "_load_json", fake_load_json)
    monkeypatch.setattr(registry_module, "load_lean_module_index", example_module_records)
    monkeypatch.setattr(
        registry_module,
        "load_theorem_witnesses",
        lambda: [
            registry_module.TheoremWitnessRecord(
                id="qr_stride_classification_prime97_stride2",
                claim_id="qr_stride_classification",
                kind="theorem-witness",
                label="duplicate example witness",
                tuple_display="(base=10, p=97, stride=2, B=100, q=1, k=3)",
                parameters={"base": 10, "p": 97, "stride": 2},
                summary="Intentional duplicate example fixture.",
                evidence=("lean/QRTour/Examples.lean",),
            )
        ],
    )

    with pytest.raises(
        ValueError,
        match=(
            "theorem witness qr_stride_classification_prime97_stride2 should map to exactly one "
            r"worked-example namespace on \['lean/QRTour/Examples\.lean'\], got "
            r"\['QRTour\.Prime97', 'QRTour\.Composite249'\]"
        ),
    ):
        registry_module.load_lean_worked_examples()


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
