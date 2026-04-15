"""
Generate a release snapshot for the current formal/documentation surface.

This packages the current proof-status counts, open-claim boundary, Lean
public-surface audit, published dataset version, and generated-note sync state
into stable JSON and Markdown artifacts for branch/release/paper handoffs.
"""

from __future__ import annotations

from collections import Counter
import json
from pathlib import Path
from typing import Any

from .build_expository_note import render_expository_note_lines
from .ci_checks import LEAN_TARGETS, _lean_sorry_matches, _public_lean_eval_matches
from .registry import (
    STATUS_ORDER,
    load_claim_registry,
    load_lean_claim_carriers,
    load_lean_frontier_lanes,
    load_lean_open_claim_boundaries,
    load_lean_module_index,
    load_lean_worked_examples,
    load_theorem_witnesses,
    render_proof_system_legend_lines,
)
from .search import build_example_atlas
from .sync_registry_docs import registry_doc_updates, sync_registry_docs


ROOT = Path(__file__).resolve().parent.parent
SNAPSHOT_DOC_PATH = ROOT / "docs" / "RELEASE_SNAPSHOT.md"
SNAPSHOT_DATA_PATH = ROOT / "data" / "release_snapshot.json"
PUBLISHED_ATLAS_PATH = ROOT / "data" / "example_atlas.json"
EXPOSITORY_NOTE_PATH = ROOT / "docs" / "EXPOSITORY_NOTE.md"
RELEASE_SNAPSHOT_SCHEMA_VERSION = "1.3"


def _doc_link(path: str) -> str:
    return f"[{Path(path).name}]({ROOT / path})"


def _status_counts(items: list[str], ordered_keys: tuple[str, ...]) -> dict[str, int]:
    counts = Counter(items)
    return {key: counts.get(key, 0) for key in ordered_keys}


def _load_json_if_present(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text())


def _json_sync_status(path: Path, expected: dict[str, Any]) -> str:
    current = _load_json_if_present(path)
    if current is None:
        return "missing"
    return "synchronized" if current == expected else "stale"


def _text_sync_status(path: Path, expected: str) -> str:
    if not path.exists():
        return "missing"
    return "synchronized" if path.read_text() == expected else "stale"


def _lean_module_id(path: str) -> str:
    return path.removeprefix("lean/").removesuffix(".lean").replace("/", ".")


def _lean_surface_summary() -> dict[str, Any]:
    module_index = load_lean_module_index()
    public_theorem = [
        record.id
        for record in module_index
        if record.promotion_decision.startswith("keep as public theorem surface")
    ]
    public_support = [
        record.id
        for record in module_index
        if record.promotion_decision.startswith("keep as public support surface")
    ]
    public_example = [
        record.id
        for record in module_index
        if "public example surface" in record.promotion_decision
    ]
    umbrella = [
        record.id
        for record in module_index
        if record.path in ("lean/QRTour.lean", "lean/GeometricStack.lean")
    ]
    infrastructure = [
        record.id
        for record in module_index
        if record.id not in set(public_theorem + public_support + public_example)
    ]
    claim_tagged = [record.id for record in module_index if record.claim_ids]
    claim_free = [record.id for record in module_index if not record.claim_ids]
    return {
        "module_index_path": "data/lean_module_index.json",
        "theorem_guide_path": "lean/THEOREM_GUIDE.md",
        "total_modules": len(module_index),
        "umbrella_modules": umbrella,
        "public_theorem_modules": public_theorem,
        "public_support_modules": public_support,
        "public_example_modules": public_example,
        "infrastructure_modules": infrastructure,
        "claim_tagged_modules": claim_tagged,
        "claim_free_modules": claim_free,
        "counts": {
            "public_theorem": len(public_theorem),
            "public_support": len(public_support),
            "public_example": len(public_example),
            "infrastructure": len(infrastructure),
            "claim_tagged": len(claim_tagged),
            "claim_free": len(claim_free),
        },
    }


def _open_claim_boundary_summary(claims: list[Any]) -> dict[str, Any]:
    boundaries = load_lean_open_claim_boundaries()
    claims_by_id = {claim.id: claim for claim in claims}
    return {
        "path": "data/lean_open_claim_boundaries.json",
        "theorem_guide_path": "lean/THEOREM_GUIDE.md",
        "claims": [
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
            for record in boundaries
        ],
    }


def _lean_claim_surface_summary() -> dict[str, Any]:
    carriers = load_lean_claim_carriers()
    worked_examples = load_lean_worked_examples()
    return {
        "claim_carrier_path": "data/lean_claim_carriers.json",
        "worked_examples_path": "data/lean_worked_examples.json",
        "atlas_backed_claim_count": len(carriers),
        "claim_ids": [record.claim_id for record in carriers],
        "worked_example_count": len(worked_examples),
        "worked_example_namespaces": [record.namespace for record in worked_examples],
    }


def _next_lean_frontier_summary() -> dict[str, Any]:
    lanes = load_lean_frontier_lanes()
    return {
        "path": "data/lean_frontier_lanes.json",
        "theorem_guide_path": "lean/THEOREM_GUIDE.md",
        "lane_count": len(lanes),
        "lanes": [
            {
                "label": record.label,
                "summary": record.summary,
            }
            for record in lanes
        ],
    }


def _lean_hygiene_summary() -> dict[str, Any]:
    no_sorry_matches = _lean_sorry_matches()
    no_eval_matches = _public_lean_eval_matches()
    return {
        "ci_source_path": "bridge_reptends/ci_checks.py",
        "ci_entrypoint": "ci-checks",
        "ci_module_entrypoint": "python -m bridge_reptends.ci_checks",
        "no_sorry_scan_root": "lean",
        "no_sorry_status": "clean" if not no_sorry_matches else "sorry-present",
        "no_sorry_matches": no_sorry_matches,
        "no_eval_status": "clean" if not no_eval_matches else "eval-present",
        "no_eval_matches": no_eval_matches,
        "public_build_target_count": len(LEAN_TARGETS),
        "public_build_targets": list(LEAN_TARGETS),
    }


def _registry_doc_surface_summary() -> dict[str, Any]:
    managed_docs = [path.relative_to(ROOT).as_posix() for path in registry_doc_updates()]
    drifted_docs = [path.relative_to(ROOT).as_posix() for path in sync_registry_docs(check=True)]
    return {
        "sync_source_path": "bridge_reptends/sync_registry_docs.py",
        "sync_entrypoint": "sync-registry-docs",
        "sync_module_entrypoint": "python -m bridge_reptends.sync_registry_docs",
        "sync_check_entrypoint": "python -m bridge_reptends.sync_registry_docs --check",
        "managed_doc_count": len(managed_docs),
        "managed_docs": managed_docs,
        "status": "synchronized" if not drifted_docs else "stale",
        "drifted_docs": drifted_docs,
    }


def build_release_snapshot() -> dict[str, Any]:
    claims = load_claim_registry()
    witnesses = load_theorem_witnesses()
    expected_atlas = build_example_atlas(max_n=1200, max_p=1200, top=8)
    checked_in_atlas = _load_json_if_present(PUBLISHED_ATLAS_PATH)
    atlas = checked_in_atlas or expected_atlas
    expected_note = "\n".join(render_expository_note_lines()) + "\n"

    return {
        "snapshot_kind": "release_snapshot",
        "schema_version": RELEASE_SNAPSHOT_SCHEMA_VERSION,
        "manifest": {
            "build_command": "python -m bridge_reptends.build_release_snapshot",
            "builder": "bridge_reptends.build_release_snapshot:build_release_snapshot",
            "normalization": "UTF-8 JSON, indent=2, sort_keys=True, trailing newline",
            "source_files": [
                "bridge_reptends/build_release_snapshot.py",
                "bridge_reptends/build_expository_note.py",
                "bridge_reptends/ci_checks.py",
                "bridge_reptends/search.py",
                "bridge_reptends/sync_registry_docs.py",
                "data/claim_registry.json",
                "data/lean_claim_carriers.json",
                "data/lean_frontier_lanes.json",
                "data/lean_module_index.json",
                "data/lean_open_claim_boundaries.json",
                "data/lean_worked_examples.json",
                "data/theorem_witnesses.json",
                "data/throughlines.json",
                "data/example_atlas.json",
                "docs/EXPOSITORY_NOTE.md",
            ],
        },
        "proof_status": {
            "status_source_path": "docs/PROOF_STATUS_ATLAS.md",
            "claim_counts": _status_counts(
                [claim.status for claim in claims],
                STATUS_ORDER,
            ),
            "open_claims": [
                {"id": claim.id, "title": claim.title}
                for claim in claims
                if claim.status == "open"
            ],
        },
        "lean_public_surface": _lean_surface_summary(),
        "lean_hygiene": _lean_hygiene_summary(),
        "registry_doc_surface": _registry_doc_surface_summary(),
        "lean_claim_surface": _lean_claim_surface_summary(),
        "next_lean_frontier": _next_lean_frontier_summary(),
        "open_claim_boundary": _open_claim_boundary_summary(claims),
        "theorem_witness_surface": {
            "witness_atlas_path": "docs/THEOREM_WITNESS_ATLAS.md",
            "witness_counts": _status_counts(
                [record.kind for record in witnesses],
                ("theorem-witness", "empirical-witness", "open-target"),
            ),
            "total_witness_records": len(witnesses),
        },
        "published_dataset": {
            "path": "data/example_atlas.json",
            "dataset_kind": atlas["dataset_kind"],
            "schema_version": atlas["schema_version"],
            "status": _json_sync_status(PUBLISHED_ATLAS_PATH, expected_atlas),
            "build_command": atlas["manifest"]["build_command"],
            "builder": atlas["manifest"]["builder"],
            "source_files": atlas["manifest"]["source_files"],
            "provenance": atlas["provenance"],
        },
        "generated_note": {
            "path": "docs/EXPOSITORY_NOTE.md",
            "status": _text_sync_status(EXPOSITORY_NOTE_PATH, expected_note),
            "build_command": "python -m bridge_reptends.build_expository_note",
            "builder": "bridge_reptends.build_expository_note:render_expository_note_lines",
        },
    }


def render_release_snapshot_lines(snapshot: dict[str, Any] | None = None) -> tuple[str, ...]:
    data = build_release_snapshot() if snapshot is None else snapshot
    proof_status = data["proof_status"]
    lean_surface = data["lean_public_surface"]
    lean_hygiene = data["lean_hygiene"]
    registry_doc_surface = data["registry_doc_surface"]
    lean_claim_surface = data["lean_claim_surface"]
    next_frontier = data["next_lean_frontier"]
    open_claim_boundary = data["open_claim_boundary"]
    theorem_witness_surface = data["theorem_witness_surface"]
    published_dataset = data["published_dataset"]
    generated_note = data["generated_note"]
    proof_status_lines = [
        f"- total claims: {sum(proof_status['claim_counts'].values())}",
        *(
            f"- {status}: {count}"
            for status, count in proof_status["claim_counts"].items()
        ),
    ]
    open_claim_lines = [
        f"- `{claim['id']}` - {claim['title']}"
        for claim in proof_status["open_claims"]
    ]
    theorem_witness_summary_lines = [
        f"- total witness records: {theorem_witness_surface['total_witness_records']}",
        *(
            f"- {kind}: {count}"
            for kind, count in theorem_witness_surface["witness_counts"].items()
        ),
    ]

    lines = [
        "# Release Snapshot",
        "",
        "This generated snapshot packages the current proof-status counts, open-claim boundary, Lean public-surface audit, Lean hygiene status, next-frontier lanes, published dataset version, and generated-note status.",
        "",
        "## Proof-System Legend",
        "",
        *render_proof_system_legend_lines(),
        "",
        "## Current Proof Status",
        "",
        f"Use {_doc_link(proof_status['status_source_path'])} as the theorem-level status source of truth.",
        "Current registry counts:",
        "",
        *proof_status_lines,
        "",
        "Current open claim IDs:",
        *open_claim_lines,
        "",
        "## Lean Public Surface",
        "",
        f"Use {_doc_link(lean_surface['theorem_guide_path'])} and {_doc_link(lean_surface['module_index_path'])} for the full module audit.",
        f"- total indexed Lean modules: `{lean_surface['total_modules']}`",
        f"- umbrella surfaces: `{', '.join(lean_surface['umbrella_modules'])}`",
        f"- public theorem surfaces: `{lean_surface['counts']['public_theorem']}`",
        f"- public theorem module ids: `{', '.join(lean_surface['public_theorem_modules'])}`",
        f"- public support surfaces: `{lean_surface['counts']['public_support']}`",
        f"- public support module ids: `{', '.join(lean_surface['public_support_modules'])}`",
        f"- public example surfaces: `{lean_surface['counts']['public_example']}`",
        f"- public example module ids: `{', '.join(lean_surface['public_example_modules'])}`",
        f"- infrastructure-only modules: `{lean_surface['counts']['infrastructure']}`",
        f"- infrastructure module ids: `{', '.join(lean_surface['infrastructure_modules'])}`",
        f"- claim-tagged modules: `{lean_surface['counts']['claim_tagged']}`",
        f"- claim-tagged module ids: `{', '.join(lean_surface['claim_tagged_modules'])}`",
        f"- claim-free modules: `{lean_surface['counts']['claim_free']}`",
        f"- claim-free module ids: `{', '.join(lean_surface['claim_free_modules'])}`",
        "",
        "## Lean Hygiene",
        "",
        f"Use {_doc_link(lean_hygiene['ci_source_path'])} for the current theorem-surface hygiene entrypoint.",
        f"- CI entrypoint: `{lean_hygiene['ci_entrypoint']}` via `{lean_hygiene['ci_module_entrypoint']}`",
        f"- no-`sorry` status on `{lean_hygiene['no_sorry_scan_root']}`: `{lean_hygiene['no_sorry_status']}`",
        f"- no-`#eval` status on focused public Lean targets: `{lean_hygiene['no_eval_status']}`",
        f"- focused public Lean build targets: `{lean_hygiene['public_build_target_count']}`",
        f"- focused public Lean build target ids: `{', '.join(lean_hygiene['public_build_targets'])}`",
        "",
        "## Registry-Backed Docs",
        "",
        f"Use {_doc_link(registry_doc_surface['sync_source_path'])} for the registry-backed theorem/doc sync entrypoint.",
        (
            f"- sync entrypoint: `{registry_doc_surface['sync_entrypoint']}` via "
            f"`{registry_doc_surface['sync_module_entrypoint']}`"
        ),
        f"- check command: `{registry_doc_surface['sync_check_entrypoint']}`",
        f"- managed theorem/doc surfaces: `{registry_doc_surface['managed_doc_count']}`",
        f"- sync status: `{registry_doc_surface['status']}`",
        (
            f"- drifted docs: "
            f"`{', '.join(registry_doc_surface['drifted_docs']) if registry_doc_surface['drifted_docs'] else 'none'}`"
        ),
        "",
        "## Lean Claim Surface",
        "",
        (
            f"Use {_doc_link(lean_claim_surface['claim_carrier_path'])} and "
            f"{_doc_link(lean_claim_surface['worked_examples_path'])} for the atlas-backed "
            "claim-carrier and worked-example registries."
        ),
        f"- atlas-backed claim carriers: `{lean_claim_surface['atlas_backed_claim_count']}`",
        f"- carrier claim IDs: `{', '.join(lean_claim_surface['claim_ids'])}`",
        f"- worked example namespaces: `{', '.join(lean_claim_surface['worked_example_namespaces'])}`",
        "",
        "## Next Lean Frontier",
        "",
        (
            f"Use {_doc_link(next_frontier['theorem_guide_path'])} and "
            f"{_doc_link(next_frontier['path'])} for the current registry-backed "
            "release-facing frontier lanes."
        ),
        f"- frontier lanes: `{next_frontier['lane_count']}`",
        *(
            f"- {lane['label']}: {lane['summary']}"
            for lane in next_frontier["lanes"]
        ),
        "",
        "## Open-Claim Lean Boundary",
        "",
        (
            f"Use {_doc_link(open_claim_boundary['theorem_guide_path'])} and "
            f"{_doc_link(open_claim_boundary['path'])} for the exact support order "
            "beneath the remaining open claims."
        ),
        *(
            "- `{id}` - `{support_module_count}` support modules / "
            "`{support_theorem_count}` named support theorems: `{breakdown}`.".format(
                id=claim["id"],
                support_module_count=claim["support_module_count"],
                support_theorem_count=claim["support_theorem_count"],
                breakdown=", ".join(
                    f"{item['module']} ({item['count']})"
                    for item in claim["support_theorem_counts"]
                ),
            )
            for claim in open_claim_boundary["claims"]
        ),
        "",
        "## Theorem-Witness Surface",
        "",
        f"Use {_doc_link(theorem_witness_surface['witness_atlas_path'])} as the claim-linked witness source of truth.",
        *theorem_witness_summary_lines,
        "",
        "## Published Dataset",
        "",
        f"- {_doc_link(published_dataset['path'])} - dataset `{published_dataset['dataset_kind']}` with schema `{published_dataset['schema_version']}` and status `{published_dataset['status']}`.",
        f"- Build command: `{published_dataset['build_command']}`",
        f"- Source files: `{', '.join(published_dataset['source_files'])}`",
        "",
        "## Generated Note",
        "",
        f"- {_doc_link(generated_note['path'])} - status `{generated_note['status']}` against `{generated_note['builder']}`.",
        f"- Build command: `{generated_note['build_command']}`",
    ]
    return tuple(lines)


def sync_release_snapshot() -> tuple[Path, Path]:
    snapshot = build_release_snapshot()
    SNAPSHOT_DATA_PATH.write_text(json.dumps(snapshot, indent=2, sort_keys=True) + "\n")
    SNAPSHOT_DOC_PATH.write_text("\n".join(render_release_snapshot_lines(snapshot)) + "\n")
    return SNAPSHOT_DATA_PATH, SNAPSHOT_DOC_PATH


def main() -> None:
    for path in sync_release_snapshot():
        print(path.relative_to(ROOT))


if __name__ == "__main__":
    main()
