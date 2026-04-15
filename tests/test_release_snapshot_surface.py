import json
from pathlib import Path

from bridge_reptends import (
    load_claim_registry,
    load_lean_claim_carriers,
    load_lean_frontier_lanes,
    load_lean_module_index,
    load_lean_open_claim_boundaries,
    load_lean_worked_examples,
)
from bridge_reptends.build_expository_note import render_expository_note_lines
from bridge_reptends.ci_checks import LEAN_TARGETS
from bridge_reptends.build_release_snapshot import (
    build_release_snapshot,
    render_release_snapshot_lines,
)
from bridge_reptends.search import build_example_atlas
from bridge_reptends.sync_registry_docs import registry_doc_updates, sync_registry_docs


ROOT = Path(__file__).resolve().parent.parent
SNAPSHOT_DATA = ROOT / "data" / "release_snapshot.json"
SNAPSHOT_DOC = ROOT / "docs" / "RELEASE_SNAPSHOT.md"
PUBLISHED_ATLAS = ROOT / "data" / "example_atlas.json"
EXPOSITORY_NOTE = ROOT / "docs" / "EXPOSITORY_NOTE.md"
README = ROOT / "README.md"
PYPROJECT = ROOT / "pyproject.toml"


def _lean_module_id(path: str) -> str:
    return path.removeprefix("lean/").removesuffix(".lean").replace("/", ".")


def test_release_snapshot_json_matches_generator() -> None:
    assert SNAPSHOT_DATA.exists()
    assert json.loads(SNAPSHOT_DATA.read_text()) == build_release_snapshot()


def test_release_snapshot_doc_matches_generator() -> None:
    assert SNAPSHOT_DOC.exists()
    assert SNAPSHOT_DOC.read_text() == "\n".join(render_release_snapshot_lines()) + "\n"


def test_release_snapshot_packages_track_18_fields() -> None:
    snapshot = build_release_snapshot()
    published_atlas = json.loads(PUBLISHED_ATLAS.read_text())
    drifted_docs = [path.relative_to(ROOT).as_posix() for path in sync_registry_docs(check=True)]
    expected_atlas = build_example_atlas(max_n=1200, max_p=1200, top=8)
    expected_note = "\n".join(render_expository_note_lines()) + "\n"
    claims_by_id = {claim.id: claim for claim in load_claim_registry()}

    assert snapshot["snapshot_kind"] == "release_snapshot"
    assert snapshot["schema_version"] == "1.3"

    proof_status = snapshot["proof_status"]
    assert proof_status["claim_counts"] == {
        "classical": 3,
        "reproved-here": 8,
        "implemented-here": 1,
        "empirical": 1,
        "open": 2,
    }
    assert proof_status["open_claims"] == [
        {
            "id": "small_k_visibility_threshold",
            "title": "Exact visibility threshold for carried prefixes",
        },
        {
            "id": "carry_dfa_factorization",
            "title": "Canonical factorization of long division into orbit and carry",
        },
    ]

    open_claim_boundary = snapshot["open_claim_boundary"]
    assert open_claim_boundary["path"] == "data/lean_open_claim_boundaries.json"
    assert open_claim_boundary["theorem_guide_path"] == "lean/THEOREM_GUIDE.md"
    assert open_claim_boundary["claims"] == [
        {
            "id": record.claim_id,
            "title": claims_by_id[record.claim_id].title,
            "segment_count": len(record.segments),
            "support_module_count": len(claims_by_id[record.claim_id].lean_support_items),
            "support_theorem_count": sum(
                len(item.theorems) for item in claims_by_id[record.claim_id].lean_support_items
            ),
            "support_modules": [
                _lean_module_id(path)
                for segment in record.segments
                for path in segment.module_paths
            ],
            "support_theorem_counts": [
                {
                    "module": _lean_module_id(item.module),
                    "count": len(item.theorems),
                }
                for item in claims_by_id[record.claim_id].lean_support_items
            ],
        }
        for record in load_lean_open_claim_boundaries()
    ]

    module_index = load_lean_module_index()
    lean_public_surface = snapshot["lean_public_surface"]
    assert lean_public_surface["claim_tagged_modules"] == [
        record.id for record in module_index if record.claim_ids
    ]
    assert lean_public_surface["claim_free_modules"] == [
        record.id for record in module_index if not record.claim_ids
    ]
    assert lean_public_surface["counts"]["claim_tagged"] == len(
        lean_public_surface["claim_tagged_modules"]
    )
    assert lean_public_surface["counts"]["claim_free"] == len(
        lean_public_surface["claim_free_modules"]
    )

    lean_hygiene = snapshot["lean_hygiene"]
    assert lean_hygiene == {
        "ci_source_path": "bridge_reptends/ci_checks.py",
        "ci_entrypoint": "ci-checks",
        "ci_module_entrypoint": "python -m bridge_reptends.ci_checks",
        "no_sorry_scan_root": "lean",
        "no_sorry_status": "clean",
        "no_sorry_matches": [],
        "no_eval_status": "clean",
        "no_eval_matches": [],
        "public_build_target_count": len(LEAN_TARGETS),
        "public_build_targets": list(LEAN_TARGETS),
    }

    registry_doc_surface = snapshot["registry_doc_surface"]
    assert registry_doc_surface == {
        "sync_source_path": "bridge_reptends/sync_registry_docs.py",
        "sync_entrypoint": "sync-registry-docs",
        "sync_module_entrypoint": "python -m bridge_reptends.sync_registry_docs",
        "sync_check_entrypoint": "python -m bridge_reptends.sync_registry_docs --check",
        "managed_doc_count": len(registry_doc_updates()),
        "managed_docs": [path.relative_to(ROOT).as_posix() for path in registry_doc_updates()],
        "status": "synchronized" if not drifted_docs else "stale",
        "drifted_docs": drifted_docs,
    }

    lean_claim_surface = snapshot["lean_claim_surface"]
    assert lean_claim_surface["claim_carrier_path"] == "data/lean_claim_carriers.json"
    assert lean_claim_surface["worked_examples_path"] == "data/lean_worked_examples.json"
    assert lean_claim_surface["atlas_backed_claim_count"] == len(load_lean_claim_carriers())
    assert lean_claim_surface["claim_ids"] == [
        record.claim_id for record in load_lean_claim_carriers()
    ]
    assert lean_claim_surface["worked_example_count"] == len(load_lean_worked_examples())
    assert lean_claim_surface["worked_example_namespaces"] == [
        record.namespace for record in load_lean_worked_examples()
    ]

    next_frontier = snapshot["next_lean_frontier"]
    assert next_frontier == {
        "path": "data/lean_frontier_lanes.json",
        "theorem_guide_path": "lean/THEOREM_GUIDE.md",
        "lane_count": len(load_lean_frontier_lanes()),
        "lanes": [
            {
                "label": record.label,
                "summary": record.summary,
            }
            for record in load_lean_frontier_lanes()
        ],
    }

    published_dataset = snapshot["published_dataset"]
    assert published_dataset["dataset_kind"] == "published_example_atlas"
    assert published_dataset["schema_version"] == published_atlas["schema_version"]
    assert published_dataset["status"] == (
        "synchronized" if published_atlas == expected_atlas else "stale"
    )
    assert published_dataset["build_command"] == published_atlas["manifest"]["build_command"]

    generated_note = snapshot["generated_note"]
    assert generated_note["path"] == "docs/EXPOSITORY_NOTE.md"
    assert generated_note["status"] == (
        "synchronized" if EXPOSITORY_NOTE.read_text() == expected_note else "stale"
    )
    assert generated_note["build_command"] == "python -m bridge_reptends.build_expository_note"

    assert "data/lean_claim_carriers.json" in snapshot["manifest"]["source_files"]
    assert "data/lean_frontier_lanes.json" in snapshot["manifest"]["source_files"]
    assert "data/lean_open_claim_boundaries.json" in snapshot["manifest"]["source_files"]
    assert "data/lean_worked_examples.json" in snapshot["manifest"]["source_files"]
    assert "data/throughlines.json" in snapshot["manifest"]["source_files"]
    assert "bridge_reptends/sync_registry_docs.py" in snapshot["manifest"]["source_files"]


def test_release_snapshot_doc_mentions_snapshot_inputs_and_statuses() -> None:
    text = SNAPSHOT_DOC.read_text()

    assert "proof-status counts" in text
    assert "Lean Claim Surface" in text
    assert "Lean Hygiene" in text
    assert "Next Lean Frontier" in text
    assert "Registry-Backed Docs" in text
    assert "open-claim boundary" in text
    assert "Open-Claim Lean Boundary" in text
    assert "next-frontier lanes" in text
    assert "frontier lanes" in text
    assert "named support theorems" in text
    assert "Lean public-surface audit" in text
    assert "Lean hygiene status" in text
    assert "atlas-backed claim carriers" in text
    assert "worked example namespaces" in text
    assert "public theorem module ids" in text
    assert "public support module ids" in text
    assert "public example module ids" in text
    assert "infrastructure module ids" in text
    assert "claim-tagged module ids" in text
    assert "claim-free module ids" in text
    assert "published dataset version" in text
    assert "generated-note status" in text
    assert "bridge_reptends/ci_checks.py" in text
    assert "bridge_reptends/sync_registry_docs.py" in text
    assert "ci-checks" in text
    assert "python -m bridge_reptends.ci_checks" in text
    assert "sync-registry-docs" in text
    assert "python -m bridge_reptends.sync_registry_docs" in text
    assert "python -m bridge_reptends.sync_registry_docs --check" in text
    assert "no-`sorry` status" in text
    assert "no-`#eval` status" in text
    assert "focused public Lean build target ids" in text
    assert "data/lean_claim_carriers.json" in text
    assert "data/lean_frontier_lanes.json" in text
    assert "data/lean_open_claim_boundaries.json" in text
    assert "data/lean_worked_examples.json" in text
    assert "data/throughlines.json" in text
    for target in LEAN_TARGETS:
        assert target in text
    assert "QRTour.OrbitWeave" in text
    assert "QRTour.Prime97" in text
    assert "QRTour.Composite996" in text
    assert "QRTour.Examples" in text
    assert "QRTour.Basic" in text
    assert "QRTour.PrimitiveRoots" in text
    assert "GeometricStack.OrbitBufferDuality" in text
    assert "QRTour.Visibility" in text
    assert "QRTour.CarryTransducer" in text
    assert "QRTour.Visibility (5)" in text
    assert "QRTour.CompositeVisibility (7)" in text
    assert "QRTour.CarryComparison (8)" in text
    assert "QRTour.CarryTransducer (3)" in text
    assert "QRTour.CarryComparison (10)" in text
    assert "theorem frontier" in text
    assert "promotion audit" in text
    assert "theorem-witness tooling" in text
    assert "data/example_atlas.json" in text
    assert "docs/EXPOSITORY_NOTE.md" in text
    assert "`synchronized`" in text


def test_release_snapshot_renderer_uses_supplied_snapshot_payload() -> None:
    snapshot = build_release_snapshot()
    snapshot["proof_status"]["claim_counts"] = {
        "classical": 10,
        "reproved-here": 20,
        "implemented-here": 30,
        "empirical": 40,
        "open": 50,
    }
    snapshot["proof_status"]["open_claims"] = [
        {
            "id": "synthetic_open_claim",
            "title": "Synthetic open boundary for renderer regression coverage",
        }
    ]
    snapshot["theorem_witness_surface"]["total_witness_records"] = 600
    snapshot["theorem_witness_surface"]["witness_counts"] = {
        "theorem-witness": 111,
        "empirical-witness": 222,
        "open-target": 267,
    }
    snapshot["next_lean_frontier"]["lane_count"] = 2
    snapshot["next_lean_frontier"]["lanes"] = [
        {
            "label": "synthetic frontier lane",
            "summary": "Synthetic frontier summary for renderer regression coverage",
        },
        {
            "label": "synthetic support lane",
            "summary": "Another synthetic lane for release snapshot rendering",
        },
    ]

    text = "\n".join(render_release_snapshot_lines(snapshot))

    assert "- total claims: 150" in text
    assert "- classical: 10" in text
    assert "- reproved-here: 20" in text
    assert "- implemented-here: 30" in text
    assert "- empirical: 40" in text
    assert "- open: 50" in text
    assert "- `synthetic_open_claim` - Synthetic open boundary for renderer regression coverage" in text
    assert "- total witness records: 600" in text
    assert "- theorem-witness: 111" in text
    assert "- empirical-witness: 222" in text
    assert "- open-target: 267" in text
    assert "- frontier lanes: `2`" in text
    assert "- synthetic frontier lane: Synthetic frontier summary for renderer regression coverage" in text
    assert "- synthetic support lane: Another synthetic lane for release snapshot rendering" in text
    assert "Exact visibility threshold for carried prefixes" not in text
    assert "Canonical factorization of long division into orbit and carry" not in text
    assert "theorem frontier" not in text
    assert "promotion audit" not in text


def test_release_snapshot_surface_is_exposed_in_readme_and_cli() -> None:
    readme = README.read_text()
    pyproject = PYPROJECT.read_text()

    assert "build-release-snapshot" in readme
    assert "docs/RELEASE_SNAPSHOT.md" in readme
    assert "data/release_snapshot.json" in readme
    assert 'build-release-snapshot = "bridge_reptends.build_release_snapshot:main"' in pyproject
