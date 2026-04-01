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
REPO_ROOT = DATA_DIR.parent
STATUS_ORDER = ("classical", "reproved-here", "implemented-here", "empirical", "open")
SAME_CORE_BOUNDARY_CONTRAST_WITNESS_IDS = (
    "same_core_threshold_shift_interval_996_over_249",
    "carry_dfa_factorization_target_249_498_996_same_core",
)


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
    lean_support_items: tuple["LeanSupportItem", ...]


@dataclass(frozen=True)
class LeanModuleRecord:
    id: str
    path: str
    current_role: str
    promotion_decision: str
    claim_ids: tuple[str, ...]
    rationale: str


@dataclass(frozen=True)
class LeanSupportItem:
    module: str
    theorems: tuple[str, ...]
    role: str


@dataclass(frozen=True)
class LeanClaimCarrierRecord:
    claim_id: str
    module_paths: tuple[str, ...]
    theorem_names: tuple[str, ...]


@dataclass(frozen=True)
class LeanOpenClaimBoundarySegment:
    module_paths: tuple[str, ...]
    summary: str
    joiner: str = ", "


@dataclass(frozen=True)
class LeanOpenClaimBoundaryRecord:
    claim_id: str
    segments: tuple[LeanOpenClaimBoundarySegment, ...]


@dataclass(frozen=True)
class LeanFrontierLaneRecord:
    label: str
    summary: str


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
            lean_support_items=tuple(
                LeanSupportItem(
                    module=item["module"],
                    theorems=tuple(item["theorems"]),
                    role=item["role"],
                )
                for item in entry.get("lean_support_items", [])
            ),
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


def load_lean_claim_carriers() -> list[LeanClaimCarrierRecord]:
    """Load the atlas-backed Lean claim-carrier table metadata."""
    return [
        LeanClaimCarrierRecord(
            claim_id=entry["claim_id"],
            module_paths=tuple(entry["module_paths"]),
            theorem_names=tuple(entry["theorem_names"]),
        )
        for entry in _load_json("lean_claim_carriers.json")
    ]


def load_lean_open_claim_boundaries() -> list[LeanOpenClaimBoundaryRecord]:
    """Load the theorem-guide open-claim boundary metadata."""
    return [
        LeanOpenClaimBoundaryRecord(
            claim_id=entry["claim_id"],
            segments=tuple(
                LeanOpenClaimBoundarySegment(
                    module_paths=tuple(segment["module_paths"]),
                    summary=segment["summary"],
                    joiner=segment.get("joiner", ", "),
                )
                for segment in entry["segments"]
            ),
        )
        for entry in _load_json("lean_open_claim_boundaries.json")
    ]


def load_lean_frontier_lanes() -> list[LeanFrontierLaneRecord]:
    """Load the theorem-guide Lean frontier lane scaffold."""
    return [
        LeanFrontierLaneRecord(
            label=entry["label"],
            summary=entry["summary"],
        )
        for entry in _load_json("lean_frontier_lanes.json")
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


def render_proof_system_legend_lines() -> tuple[str, ...]:
    """Render the public proof-system legend used by theorem-facing docs."""
    return (
        "- `Lean-formalized`: proved in the Lean tree and suitable for theorem-level citation in the current public surface.",
        "- `Agda-locally-proved`: discharged inside the Agda pedagogical companion surface without relying on Agda postulates.",
        "- `Agda-postulated but Lean-backed`: still explicit as an Agda postulate, but closed by Lean or an atlas-backed Lean-backed claim in this repo.",
        "- `empirical`: implemented and regression-tested here, but not promoted to theorem status.",
        "- `open`: tracked as an unresolved claim boundary or interface question, not an established result.",
    )


def render_theorem_guide_status_source_lines() -> tuple[str, ...]:
    """Render the theorem-guide status-source intro block."""
    atlas = _repo_link("docs/PROOF_STATUS_ATLAS.md", "docs/PROOF_STATUS_ATLAS.md")
    return (
        f"Use {atlas} as the public status source of truth. This note is the Lean-facing module and theorem index for the current formal surface.",
    )


def _doc_link(path: str) -> str:
    """Render a Markdown doc link using the repo's absolute-path convention."""
    return f"[{Path(path).name}]({DATA_DIR.parent / path})"


def _repo_link(path: str, label: str | None = None) -> str:
    """Render a Markdown link using the repo's absolute-path convention."""
    return f"[{label or path}]({REPO_ROOT / path})"


def _lean_doc_link(path: str) -> str:
    """Render a Lean module link using theorem-guide path labels."""
    return f"[{path.removeprefix('lean/')}]({DATA_DIR.parent / path})"


def _theorem_guide_status_label(status: str) -> str:
    """Render the theorem-guide carrier status label."""
    if status == "classical":
        return "`classical` with Lean backing in repo evidence"
    return f"`{status}`"


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


def render_open_claim_lean_support_lines(
    claims: list[ClaimRecord] | None = None,
) -> tuple[str, ...]:
    """Render a short open-claim Lean-support crosswalk for the theorem guide."""
    records = claims or load_claim_registry()
    lines = [
        "| Claim ID | Lean module | Representative finite lemmas | Boundary role |",
        "|----------|-------------|------------------------------|---------------|",
    ]
    for record in records:
        if record.status != "open":
            continue
        for item in record.lean_support_items:
            theorem_names = ", ".join(f"`{name}`" for name in item.theorems)
            lines.append(
                f"| `{record.id}` | {_doc_link(item.module)} | {theorem_names} | {item.role} |"
            )
    return tuple(lines)


def render_lean_claim_carrier_lines(
    carriers: list[LeanClaimCarrierRecord] | None = None,
    claims: dict[str, ClaimRecord] | None = None,
    witnesses: list[TheoremWitnessRecord] | None = None,
) -> tuple[str, ...]:
    """Render the theorem-guide atlas-backed claim-carrier table."""
    records = carriers or load_lean_claim_carriers()
    claim_records = claims or claim_lookup()
    witness_records = witnesses or load_theorem_witnesses()
    witnesses_by_claim = theorem_witnesses_by_claim(witness_records)
    lines = [
        "| Claim ID | Atlas Status | Lean module(s) | Main theorem names | Canonical witness ID(s) |",
        "|----------|--------------|----------------|--------------------|-------------------------|",
    ]
    for record in records:
        claim = claim_records[record.claim_id]
        if claim.status == "open":
            raise ValueError(f"open claim {record.claim_id} cannot appear in the atlas-backed carrier table")
        module_links = ", ".join(_lean_doc_link(path) for path in record.module_paths)
        theorem_names = ", ".join(f"`{name}`" for name in record.theorem_names)
        witness_ids = tuple(
            witness.id
            for witness in witnesses_by_claim.get(record.claim_id, ())
            if witness.kind == "theorem-witness"
        )
        if not witness_ids:
            raise ValueError(f"claim carrier {record.claim_id} is missing a theorem witness")
        witness_cell = ", ".join(f"`{witness_id}`" for witness_id in witness_ids)
        lines.append(
            f"| `{record.claim_id}` | {_theorem_guide_status_label(claim.status)} | {module_links} | {theorem_names} | {witness_cell} |"
        )
    return tuple(lines)


def render_theorem_guide_claim_carrier_lines() -> tuple[str, ...]:
    """Backward-compatible theorem-guide claim-carrier wrapper."""
    return render_lean_claim_carrier_lines()


def render_lean_open_claim_boundary_lines(
    boundaries: list[LeanOpenClaimBoundaryRecord] | None = None,
    claims: dict[str, ClaimRecord] | None = None,
) -> tuple[str, ...]:
    """Render the theorem-guide open-claim boundary table."""
    records = boundaries or load_lean_open_claim_boundaries()
    claim_records = claims or claim_lookup()
    lines = [
        "| Claim ID | Current Lean boundary |",
        "|----------|-----------------------|",
    ]
    for record in records:
        claim = claim_records[record.claim_id]
        if claim.status != "open":
            raise ValueError(
                f"non-open claim {record.claim_id} cannot appear in the open-claim boundary table"
            )
        boundary_text = "; ".join(
            f"{segment.joiner.join(_lean_doc_link(path) for path in segment.module_paths)} {segment.summary}"
            for segment in record.segments
        )
        lines.append(f"| `{record.claim_id}` | {boundary_text} |")
    return tuple(lines)


def render_theorem_guide_open_boundary_lines() -> tuple[str, ...]:
    """Backward-compatible theorem-guide open-boundary wrapper."""
    return render_lean_open_claim_boundary_lines()


def render_lean_frontier_lane_lines(
    lanes: list[LeanFrontierLaneRecord] | None = None,
) -> tuple[str, ...]:
    """Render the bounded Lean-frontier scaffold for the theorem guide."""
    records = lanes or load_lean_frontier_lanes()
    return tuple(f"- `{record.label}`: {record.summary}" for record in records)


def render_theorem_guide_module_index_source_lines() -> tuple[str, ...]:
    """Render the theorem-guide module-index backing note."""
    backing = _repo_link("data/lean_module_index.json", "lean_module_index.json")
    return (f"This audit table is generated from {backing}.",)


def render_theorem_guide_next_frontier_lines() -> tuple[str, ...]:
    """Render the theorem-guide next-frontier bullet list."""
    witness_atlas = _repo_link("docs/THEOREM_WITNESS_ATLAS.md", "THEOREM_WITNESS_ATLAS.md")
    return (
        "- theorem frontier: strengthen same-core visibility and fixed-window carry/visibility arithmetic beyond the current quotient-scaling, scaled-raw-coefficient endpoint criteria, and exact certificate layer, while keeping `small_k_visibility_threshold` and `carry_dfa_factorization` explicitly `open`",
        "- promotion audit: decide whether any of `PrimitiveRoots`, `BridgeQuality`, or the remaining bridge-specialized support modules deserve their own atlas claim IDs, and classify the rest explicitly as public support or infrastructure",
        f"- theorem-witness tooling: extend the now-generated {witness_atlas} into search outputs, site-facing data, and targeted research exports so the formal surface and the open-claim surface are easier to inspect and publish without hand-maintained drift",
    )


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
        module_link = _lean_doc_link(record.path)
        lines.append(
            f"| {module_link} | {record.current_role} | {record.promotion_decision} | {claim_ids} |"
        )
    return tuple(lines)


def render_proof_status_footer_lines() -> tuple[str, ...]:
    """Render the proof-atlas footer/reference note."""
    discoveries = _repo_link("DISCOVERIES.md", "DISCOVERIES.md")
    roadmap = _repo_link("docs/ROADMAP.md", "docs/ROADMAP.md")
    registry = _repo_link("data/claim_registry.json", "claim_registry.json")
    return (
        f"Use {discoveries} for exploratory context and {roadmap} for implementation follow-through on these open items.",
        "",
        f"Machine-readable backing lives in {registry}.",
    )


def render_proof_status_track_five_notes_lines() -> tuple[str, ...]:
    """Render the proof-atlas Track 5 notes block."""
    quadratic_residues = _lean_doc_link("lean/QRTour/QuadraticResidues.lean")
    digits = _lean_doc_link("lean/QRTour/Digits.lean")
    signed_bridge = _lean_doc_link("lean/QRTour/SignedBridge.lean")
    p_adic_bridge = _lean_doc_link("lean/QRTour/PAdicBridge.lean")
    composite_period = _lean_doc_link("lean/QRTour/CompositePeriod.lean")
    preperiod = _lean_doc_link("lean/QRTour/Preperiod.lean")
    visibility = _lean_doc_link("lean/QRTour/Visibility.lean")
    carry_comparison = _lean_doc_link("lean/QRTour/CarryComparison.lean")
    composite_visibility = _lean_doc_link("lean/QRTour/CompositeVisibility.lean")
    return (
        f"- {quadratic_residues} now formalizes the QR-generator power-count theorem `qrGenerator_pow_count_eq_totient`, which proves the `φ((p-1)/2)` count for powers of a fixed QR generator.",
        "- The same Lean module now closes the base-level stride-count reduction via the full-order reduction lemmas and `base_qrGenerator_pow_count_eq_totient`, so the `ord_p(B) ∈ {h, 2h}` classification is now fully formalized at the theorem level.",
        f"- {digits} now carries the digit/remainder Euclidean equation and the exact digit periodicity theorem, so digit periodicity is no longer just implicit Lean support.",
        f"- {signed_bridge} now carries the signed bridge recurrence theorem, so the plus/minus bridge package and the `2k` sign-cancellation law are part of the public Lean claim surface.",
        f"- {p_adic_bridge} now carries the bridge block-value periodicity claim, so the block-value geometric sequence and its `ord_p(d)` periodicity are no longer just analogy-level support.",
        f"- {composite_period} now formalizes the finite-product order theorem `orderOf_pi`, the pairwise CRT theorem `orderOf_unitsChineseRemainder`, and the finite prime-power CRT theorem `orderOf_unitsEquivPrimePowers`.",
        f"- {preperiod} now formalizes both the local valuation theorem `preperiodPrimeSteps_le_iff` and the global base-prime-support maximum `preperiodSteps`, including `preperiodSteps_le_of_local_bounds` and `basePrimeSupportFactor_dvd_base_pow_preperiodSteps`.",
        f"- {visibility} now formalizes the exact fixed-window gap certificate, proves it is equivalent to visible-prefix agreement at fixed `(requestedBlocks, lookaheadBlocks)`, derives the necessary tail-mass lower bound beneath that certificate, and transports the certificate to larger lookahead windows once a visible prefix has stabilized.",
        f"- {carry_comparison} now packages aligned finite carry/remainder traces, proves certified finite output agreement under the exact fixed-window certificate, lifts the generic certificate-transport layer to larger visible windows, consumes the exact same-core `k^s` transport theorem to reprove shifted visible-word/output agreement from stripped-core certificates, and now also extracts exact finite state-alignment records with observed state-pair projections, local carry-balance and remainder-balance equations at each aligned position, exact finite-window functional criteria for the observed remainder-to-carry and carry-to-remainder state-pair lists, finite transition-compatibility theorems under those criteria, and explicit finite conflict lemmas refuting them when the observed pair list disagrees.",
        f"- {composite_visibility} now packages same-core families for actual denominators versus stripped periodic cores using the preperiod factor layer, including exact quotient-scaling, exact/lower/upper endpoint labels, scaled-raw-coefficient sufficient criteria for the non-power interval endpoints, near-denominator coordinate-selection criteria, exact same-core transport of the first visible mismatch boundary in the `k`-power regime, and exact same-core transport of the raw tail-mass lower-bound inequality, the shifted coarse `k^(n+L) < modulus` sufficient condition, and the exact fixed-window lookahead certificate itself between the stripped core at `(n, L)` and the actual denominator at `(n + s, L)`.",
        "- The stripped-periodic-modulus statement in the composite pipeline remains classical/computational in the repo; Lean now covers the finite prime-power CRT order theorem, the max-over-base-primes preperiod step count, the stripping-factor divisibility layer, and the same-core family packaging built on top of that exact arithmetic.",
    )


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


def render_same_core_boundary_note_lines(
    witnesses: list[TheoremWitnessRecord] | None = None,
) -> tuple[str, ...]:
    """Render a short atlas-backed contrast note for the same-core frontier."""
    records = witnesses or load_theorem_witnesses()
    witness_map = {record.id: record for record in records}
    visibility = witness_map[SAME_CORE_BOUNDARY_CONTRAST_WITNESS_IDS[0]]
    carry = witness_map[SAME_CORE_BOUNDARY_CONTRAST_WITNESS_IDS[1]]
    return (
        "| Surface | Atlas witness | Current boundary signal |",
        "|---------|---------------|-------------------------|",
        f"| Exact same-core visibility transport | `{visibility.id}` | Claim `{visibility.claim_id}`: {visibility.summary} |",
        f"| Same-core selector-family failure | `{carry.id}` | Claim `{carry.claim_id}`: {carry.summary} Therefore exact same-core `carryToRemainderFunctional` transport is not currently claimed. |",
    )


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
