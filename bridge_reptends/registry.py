"""
Machine-readable registry for claims, module roles, witnesses, sources, counterexamples, and vocabulary.

The repo uses these records to keep public prose aligned with exact statements:
- claims are tagged as classical / reproved-here / empirical / implemented-here / open
- Lean modules are classified as claim carriers, public support, or infrastructure
- theorem witnesses tie claim IDs to canonical tuples, empirical families, or open targets
- counterexamples point back to the claims they correct
- vocabulary entries map coined labels to standard terminology
"""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any


DATA_DIR = Path(__file__).resolve().parent.parent / "data"
STATUS_ORDER = ("classical", "reproved-here", "implemented-here", "empirical", "open")


@dataclass(frozen=True)
class LiteratureSource:
    id: str
    author: str
    title: str
    url: str
    tags: tuple[str, ...]


@dataclass(frozen=True)
class VocabularyEntry:
    id: str
    preferred_label: str
    repo_aliases: tuple[str, ...]
    meaning: str
    scope: str


@dataclass(frozen=True)
class CounterexampleRecord:
    id: str
    claim_id: str
    legacy_claim: str
    parameters: dict[str, Any]
    observed: str
    replacement: str


@dataclass(frozen=True)
class ClaimRecord:
    id: str
    title: str
    statement: str
    status: str
    repo_status: str
    proof_status: str
    evidence: tuple[str, ...]
    vocabulary_ids: tuple[str, ...]
    source_ids: tuple[str, ...]
    counterexample_ids: tuple[str, ...]


@dataclass(frozen=True)
class LeanModuleRecord:
    id: str
    path: str
    current_role: str
    promotion_decision: str
    claim_ids: tuple[str, ...]
    rationale: str


@dataclass(frozen=True)
class TheoremWitnessRecord:
    id: str
    claim_id: str
    kind: str
    label: str
    tuple_display: str
    parameters: dict[str, Any]
    summary: str
    evidence: tuple[str, ...]


def _load_json(filename: str) -> Any:
    with (DATA_DIR / filename).open() as handle:
        return json.load(handle)


def load_literature_map() -> list[LiteratureSource]:
    """Load the curated literature/source list."""
    return [
        LiteratureSource(
            id=entry["id"],
            author=entry["author"],
            title=entry["title"],
            url=entry["url"],
            tags=tuple(entry["tags"]),
        )
        for entry in _load_json("literature_map.json")
    ]


def load_vocabulary() -> list[VocabularyEntry]:
    """Load the standardized vocabulary table."""
    return [
        VocabularyEntry(
            id=entry["id"],
            preferred_label=entry["preferred_label"],
            repo_aliases=tuple(entry["repo_aliases"]),
            meaning=entry["meaning"],
            scope=entry["scope"],
        )
        for entry in _load_json("vocabulary.json")
    ]


def load_counterexamples() -> list[CounterexampleRecord]:
    """Load the counterexample registry."""
    return [
        CounterexampleRecord(
            id=entry["id"],
            claim_id=entry["claim_id"],
            legacy_claim=entry["legacy_claim"],
            parameters=dict(entry["parameters"]),
            observed=entry["observed"],
            replacement=entry["replacement"],
        )
        for entry in _load_json("counterexamples.json")
    ]


def load_claim_registry() -> list[ClaimRecord]:
    """Load the proof-status atlas."""
    return [
        ClaimRecord(
            id=entry["id"],
            title=entry["title"],
            statement=entry["statement"],
            status=entry["status"],
            repo_status=entry["repo_status"],
            proof_status=entry["proof_status"],
            evidence=tuple(entry["evidence"]),
            vocabulary_ids=tuple(entry["vocabulary_ids"]),
            source_ids=tuple(entry["source_ids"]),
            counterexample_ids=tuple(entry["counterexample_ids"]),
        )
        for entry in _load_json("claim_registry.json")
    ]


def load_lean_module_index() -> list[LeanModuleRecord]:
    """Load the Lean module role/promotion index."""
    return [
        LeanModuleRecord(
            id=entry["id"],
            path=entry["path"],
            current_role=entry["current_role"],
            promotion_decision=entry["promotion_decision"],
            claim_ids=tuple(entry["claim_ids"]),
            rationale=entry["rationale"],
        )
        for entry in _load_json("lean_module_index.json")
    ]


def load_theorem_witnesses() -> list[TheoremWitnessRecord]:
    """Load the theorem-witness atlas."""
    return [
        TheoremWitnessRecord(
            id=entry["id"],
            claim_id=entry["claim_id"],
            kind=entry["kind"],
            label=entry["label"],
            tuple_display=entry["tuple_display"],
            parameters=dict(entry["parameters"]),
            summary=entry["summary"],
            evidence=tuple(entry["evidence"]),
        )
        for entry in _load_json("theorem_witnesses.json")
    ]


def literature_lookup() -> dict[str, LiteratureSource]:
    """Index the literature map by source id."""
    return {source.id: source for source in load_literature_map()}


def vocabulary_lookup() -> dict[str, VocabularyEntry]:
    """Index the vocabulary registry by vocabulary id."""
    return {entry.id: entry for entry in load_vocabulary()}


def counterexample_lookup() -> dict[str, CounterexampleRecord]:
    """Index the counterexample registry by id."""
    return {record.id: record for record in load_counterexamples()}


def claim_lookup() -> dict[str, ClaimRecord]:
    """Index the claim registry by id."""
    return {record.id: record for record in load_claim_registry()}


def lean_module_lookup() -> dict[str, LeanModuleRecord]:
    """Index the Lean module registry by module id."""
    return {record.id: record for record in load_lean_module_index()}


def theorem_witness_lookup() -> dict[str, TheoremWitnessRecord]:
    """Index the theorem-witness registry by witness id."""
    return {record.id: record for record in load_theorem_witnesses()}


def claim_context_for_parameters(
    related_claim_ids: tuple[str, ...] | list[str],
    *,
    base: int | None = None,
    n: int | None = None,
    actual: int | None = None,
    core: int | None = None,
    requested_blocks: int | None = None,
) -> dict[str, list[str]]:
    """
    Match claim and witness context for a concrete exported example.

    This keeps search/report rows tied to the registry without requiring each
    export surface to hard-code witness ids.
    """
    claims = claim_lookup()
    related_ids = [claim_id for claim_id in related_claim_ids if claim_id in claims]
    matched_witnesses: list[TheoremWitnessRecord] = []
    family_members = {value for value in (n, actual, core) if value is not None}

    for witness in load_theorem_witnesses():
        if witness.claim_id not in related_ids:
            continue
        params = witness.parameters
        if base is not None and "base" in params and params["base"] != base:
            continue
        if (
            requested_blocks is not None
            and "requestedBlocks" in params
            and params["requestedBlocks"] != requested_blocks
        ):
            continue
        if actual is not None and core is not None:
            if params.get("actual") == actual and params.get("core") == core:
                matched_witnesses.append(witness)
                continue
        if n is not None:
            if params.get("N") == n or params.get("n") == n or params.get("p") == n:
                matched_witnesses.append(witness)
                continue
        family_n = params.get("family_N")
        if isinstance(family_n, list) and family_members.intersection(family_n):
            matched_witnesses.append(witness)

    return {
        "related_claim_ids": related_ids,
        "related_open_claim_ids": [
            claim_id for claim_id in related_ids if claims[claim_id].status == "open"
        ],
        "matching_claim_ids": sorted({witness.claim_id for witness in matched_witnesses}),
        "matching_witness_ids": [witness.id for witness in matched_witnesses],
    }


def theorem_witnesses_by_claim(
    witnesses: list[TheoremWitnessRecord] | None = None,
) -> dict[str, tuple[TheoremWitnessRecord, ...]]:
    """Group theorem witnesses by claim id."""
    records = witnesses or load_theorem_witnesses()
    grouped: dict[str, list[TheoremWitnessRecord]] = {}
    for record in records:
        grouped.setdefault(record.claim_id, []).append(record)
    return {claim_id: tuple(entries) for claim_id, entries in grouped.items()}


def claims_by_status(claims: list[ClaimRecord] | None = None) -> dict[str, tuple[ClaimRecord, ...]]:
    """Group claims by their status in a stable order."""
    records = claims or load_claim_registry()
    grouped: dict[str, list[ClaimRecord]] = {status: [] for status in STATUS_ORDER}
    for record in records:
        grouped.setdefault(record.status, []).append(record)
    return {status: tuple(grouped.get(status, [])) for status in STATUS_ORDER}


def status_counts(claims: list[ClaimRecord] | None = None) -> tuple[tuple[str, int], ...]:
    """Return registry status counts in stable display order."""
    grouped = claims_by_status(claims)
    return tuple((status, len(grouped[status])) for status in STATUS_ORDER)


def open_claims(claims: list[ClaimRecord] | None = None) -> tuple[ClaimRecord, ...]:
    """Return claims explicitly tagged as open."""
    grouped = claims_by_status(claims)
    return grouped["open"]


def render_registry_summary_lines(claims: list[ClaimRecord] | None = None) -> tuple[str, ...]:
    """Render a small status summary block suitable for docs/tests."""
    records = claims or load_claim_registry()
    lines = [f"- total claims: {len(records)}"]
    lines.extend(f"- {status}: {count}" for status, count in status_counts(records))
    return tuple(lines)


def render_open_claim_lines(claims: list[ClaimRecord] | None = None) -> tuple[str, ...]:
    """Render a short open-claims list suitable for docs/tests."""
    return tuple(
        f"- `{record.id}` - {record.title}"
        for record in open_claims(claims)
    )


def _doc_link(path: str) -> str:
    """Render a Markdown doc link using the repo's absolute-path convention."""
    return f"[{Path(path).name}]({DATA_DIR.parent / path})"


def render_claim_table_lines(claims: list[ClaimRecord] | None = None) -> tuple[str, ...]:
    """Render the proof-status claim table for public docs."""
    records = claims or load_claim_registry()
    lines = [
        "| Claim ID | Status | Exact Statement | Repo Evidence |",
        "|----------|--------|-----------------|---------------|",
    ]
    for record in records:
        evidence_links = ", ".join(_doc_link(path) for path in record.evidence)
        lines.append(
            f"| `{record.id}` | `{record.status}` | {record.statement} | {evidence_links} |"
        )
    return tuple(lines)


def render_vocabulary_table_lines(entries: list[VocabularyEntry] | None = None) -> tuple[str, ...]:
    """Render the standardized vocabulary table for public docs."""
    records = entries or load_vocabulary()
    lines = [
        "| Vocabulary ID | Preferred Label | Repo Alias | Exact Meaning | Scope |",
        "|---------------|-----------------|-----------|---------------|-------|",
    ]
    for entry in records:
        aliases = ", ".join(entry.repo_aliases)
        lines.append(
            f"| `{entry.id}` | {entry.preferred_label} | {aliases} | {entry.meaning} | {entry.scope} |"
        )
    return tuple(lines)


def render_lean_module_index_lines(
    modules: list[LeanModuleRecord] | None = None,
) -> tuple[str, ...]:
    """Render the Lean module audit table for the theorem guide."""
    records = modules or load_lean_module_index()
    lines = [
        "| Module | Current role | Promotion decision | Associated claim IDs |",
        "|--------|--------------|--------------------|----------------------|",
    ]
    for record in records:
        claim_ids = ", ".join(f"`{claim_id}`" for claim_id in record.claim_ids) or "none"
        module_link = f"[{record.path.removeprefix('lean/')}]({DATA_DIR.parent / record.path})"
        lines.append(
            f"| {module_link} | {record.current_role} | {record.promotion_decision} | {claim_ids} |"
        )
    return tuple(lines)


def render_theorem_witness_summary_lines(
    witnesses: list[TheoremWitnessRecord] | None = None,
) -> tuple[str, ...]:
    """Render a short theorem-witness summary block suitable for docs/tests."""
    records = witnesses or load_theorem_witnesses()
    kind_order = ("theorem-witness", "empirical-witness", "open-target")
    counts = {kind: 0 for kind in kind_order}
    for record in records:
        counts[record.kind] = counts.get(record.kind, 0) + 1
    lines = [f"- total witness records: {len(records)}"]
    lines.extend(f"- {kind}: {counts.get(kind, 0)}" for kind in kind_order)
    extra_kinds = sorted(kind for kind in counts if kind not in kind_order)
    lines.extend(f"- {kind}: {counts[kind]}" for kind in extra_kinds)
    return tuple(lines)


def render_theorem_witness_table_lines(
    witnesses: list[TheoremWitnessRecord] | None = None,
    claims: dict[str, ClaimRecord] | None = None,
) -> tuple[str, ...]:
    """Render the theorem-witness atlas table for public docs."""
    records = witnesses or load_theorem_witnesses()
    claim_records = claims or claim_lookup()
    lines = [
        "| Witness ID | Claim ID | Claim Status | Kind | Canonical tuple or family | Why this witness | Repo Evidence |",
        "|------------|----------|--------------|------|---------------------------|------------------|---------------|",
    ]
    for record in records:
        claim_status = claim_records[record.claim_id].status
        evidence_links = ", ".join(_doc_link(path) for path in record.evidence)
        lines.append(
            f"| `{record.id}` | `{record.claim_id}` | `{claim_status}` | `{record.kind}` | {record.tuple_display} | {record.summary} | {evidence_links} |"
        )
    return tuple(lines)
