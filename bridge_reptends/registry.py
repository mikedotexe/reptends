"""
Machine-readable registry for claims, sources, counterexamples, and vocabulary.

The repo uses these records to keep public prose aligned with exact statements:
- claims are tagged as classical / reproved-here / empirical / implemented-here / open
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
