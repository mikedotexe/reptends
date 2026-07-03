"""
Machine-readable registry for claims, module roles, witnesses, sources, counterexamples, and vocabulary.

The repo uses these records to keep public prose aligned with exact statements:
- claims are tagged as classical / reproved-here / empirical / implemented-here / open
- Lean modules are classified as claim carriers, public support, or infrastructure
- Lean worked examples tie example namespaces to concrete theorem entry points
  and theorem-witness rows
- theorem witnesses tie claim IDs to canonical tuples, empirical families, or open targets
- counterexamples point back to the claims they correct
- vocabulary entries map coined labels to standard terminology
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
import json
from pathlib import Path
import re
import shlex
from typing import Any


DATA_DIR = Path(__file__).resolve().parent.parent / "data"
REPO_ROOT = DATA_DIR.parent
STATUS_ORDER = ("classical", "reproved-here", "implemented-here", "empirical", "open")
SAME_CORE_BOUNDARY_CONTRAST_WITNESS_IDS = (
    "same_core_threshold_shift_interval_996_over_249",
    "carry_dfa_factorization_target_249_498_996_same_core",
)
EXAMPLES_OPEN_BOUNDARY_NAMESPACE = "QRTour.Composite996"
KNOWN_SEARCH_SURFACE_IDS = frozenset(
    {
        "small-residue-coordinates",
        "small-residue-coordinates-q1",
        "legacy-counterexamples",
        "composite-profiles",
        "visibility-profiles",
        "visibility-counterexamples",
        "visibility-optics",
        "visibility-base-compare",
        "instrument-atlas",
        "chart-invariance",
        "same-core-visibility",
        "carry-factorization",
        "carry-factorization-selector",
        "carry-selector-non-k1",
        "carry-selector-same-core",
        "carry-selector-research",
        "orbit-carry-frontier",
        "orbit-carry-trace",
        "state-merging",
        "state-merging-same-core",
        "quotient-obstructions",
        "quotient-obstruction-families",
        "same-core-obstruction-correlates",
        "prime-qr-generators",
        "published-atlas",
        "theorem-witnesses",
    }
)
KNOWN_ATLAS_SECTION_IDS = frozenset(
    {
        "throughlines",
        "canonical_examples",
        "claim_witnesses",
        "orbit_carry_frontier",
        "carry_dfa",
        "carry_selector",
        "carry_selector_families",
        "state_merging",
        "state_merging_families",
        "visibility",
        "visibility_families",
        "composite_examples",
        "composite_families",
        "carry_selector_research",
        "state_merging_research",
        "state_merging_same_core",
    }
)
_EXAMPLES_OPEN_BOUNDARY_NOTE_ROWS = (
    (
        "small_k_visibility_threshold",
        EXAMPLES_OPEN_BOUNDARY_NAMESPACE,
        (
            "sameCore_firstIncomingCarryPosition_shift_exact",
            "sameCore_localOverflowBoundary_shift_exact",
            "sameCore_firstVisibleMismatchPosition_shift_exact",
            "sameCore_lookaheadCertificateHolds_iff_add_exact",
        ),
        "same_core_threshold_shift_interval_996_over_249",
        "same_core_threshold_shift_interval",
        "theorem-witness",
        "package the exact one-block same-core shift and the exact fixed-window lookahead-certificate transport, but do not claim a sharp minimal-lookahead or global visibility formula.",
    ),
    (
        "carry_dfa_factorization",
        EXAMPLES_OPEN_BOUNDARY_NAMESPACE,
        (
            "actual996_stateAlignments_remainderToCarryStepFunctional",
            "core249_carryToRemainderFunctional_one_zero",
            "actual996_carryToRemainder_conflict_two_zero",
            "sameCore_carryToRemainderTransport_counterexample",
            "actual996_not_carryToRemainderFunctional",
            "actual996_stateAlignments_remainderToCarry_transition_compatible",
            "actual996_quotientOnly_profile",
            "core249_remainderToCarryFunctional",
            "core249_stateAlignments_remainderToCarry_transition_compatible",
            "core249_not_carryToRemainderFunctional",
        ),
        "carry_dfa_factorization_target_249_498_996_same_core",
        "carry_dfa_factorization",
        "open-target",
        "prove exact finite same-core functionality and asymmetry on selected windows, surface the stripped-core `1/0` functional witness and the shifted-actual `2/0` conflict explicitly, explicitly refute forward same-core `carryToRemainderFunctional` transport on the exact `1/0 -> 2/0` pair, but do not promote a global canonical factorization theorem.",
    ),
)
LEAN_DECL_PATTERN = re.compile(
    r"^(?:@\[[^\n]+\]\s*)?"
    r"(?:(?:private|noncomputable|protected|partial|unsafe)\s+)*"
    r"(?:def|theorem|lemma|abbrev)\s+([A-Za-z0-9_'.]+)",
    re.MULTILINE,
)
LEAN_NAMESPACE_PATTERN = re.compile(r"^\s*namespace\s+([A-Za-z0-9_'.]+)", re.MULTILINE)
LEAN_DECL_LINE_PATTERN = re.compile(
    r"^\s*(?:@\[[^\n]+\]\s*)?"
    r"(?:(?:private|noncomputable|protected|partial|unsafe)\s+)*"
    r"(?:def|theorem|lemma|abbrev)\s+([A-Za-z0-9_'.]+)"
)
LEAN_NAMESPACE_LINE_PATTERN = re.compile(r"^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$")
LEAN_END_LINE_PATTERN = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_'.]+))?\s*$")


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
class LeanWorkedExampleRecord:
    module_path: str
    namespace: str
    claim_ids: tuple[str, ...]
    theorem_names: tuple[str, ...]
    current_role: str
    witness_ids: tuple[str, ...]


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


@dataclass(frozen=True)
class ThroughlineSearchRecord:
    id: str
    label: str
    summary: str
    command: str
    atlas_section_id: str | None


@dataclass(frozen=True)
class ThroughlineLadderRecord:
    id: str
    label: str
    claim_ids: tuple[str, ...]
    witness_ids: tuple[str, ...]
    counterexample_ids: tuple[str, ...]
    summary: str


@dataclass(frozen=True)
class ThroughlineRecord:
    id: str
    kind: str
    title: str
    headline: str
    status_note: str
    claim_ids: tuple[str, ...]
    open_claim_ids: tuple[str, ...]
    witness_ids: tuple[str, ...]
    counterexample_ids: tuple[str, ...]
    featured_searches: tuple[ThroughlineSearchRecord, ...]
    ladder: tuple[ThroughlineLadderRecord, ...]


def _load_json(filename: str) -> Any:
    with (DATA_DIR / filename).open() as handle:
        return json.load(handle)


@lru_cache(maxsize=None)
def _lean_declaration_names(path: str) -> frozenset[str]:
    """Cache simple Lean declaration names for a source file."""
    text = (REPO_ROOT / path).read_text()
    return frozenset(match.group(1) for match in LEAN_DECL_PATTERN.finditer(text))


@lru_cache(maxsize=None)
def _lean_namespace_names(path: str) -> frozenset[str]:
    """Cache explicit Lean namespace declarations for a source file."""
    text = (REPO_ROOT / path).read_text()
    return frozenset(match.group(1) for match in LEAN_NAMESPACE_PATTERN.finditer(text))


def _lean_reference_candidates(name: str) -> tuple[str, ...]:
    """Accept either fully qualified or namespace-local Lean theorem names."""
    parts = name.split(".")
    return tuple(dict.fromkeys(".".join(parts[index:]) for index in range(len(parts))))


def _qualify_lean_namespace(name: str, current_namespace: str | None) -> str:
    """Resolve a relative namespace name against the current Lean namespace."""
    if current_namespace is None or "." in name:
        return name
    return f"{current_namespace}.{name}"


def _ensure_repo_path_exists(path: str, *, context: str) -> None:
    """Reject registry paths that do not exist in the repo."""
    if not (REPO_ROOT / path).exists():
        raise ValueError(f"{context} references missing repo path {path}")


def _ensure_unique_values(values: list[str], *, context: str) -> None:
    """Reject duplicate registry keys that would blur the public surface."""
    seen: set[str] = set()
    for value in values:
        if value in seen:
            raise ValueError(f"{context} must be unique, got duplicate {value!r}")
        seen.add(value)


def _ensure_lean_module_id_matches_path(module_id: str, path: str, *, context: str) -> None:
    """Reject Lean module ids that drift from their source path."""
    expected_id = path.removeprefix("lean/").removesuffix(".lean").replace("/", ".")
    if module_id != expected_id:
        raise ValueError(
            f"{context} uses Lean module id {module_id} but {path} implies {expected_id}"
        )


def _ensure_lean_declarations_resolve(
    module_paths: tuple[str, ...] | list[str],
    names: tuple[str, ...] | list[str],
    *,
    context: str,
) -> None:
    """Reject registry theorem names that do not resolve in their Lean modules."""
    missing = [
        name
        for name in names
        if not any(
            any(
                decl_name == candidate or decl_name.endswith(f".{candidate}")
                for decl_name in _lean_declaration_names(path)
            )
            for path in module_paths
            for candidate in _lean_reference_candidates(name)
        )
    ]
    if missing:
        raise ValueError(
            f"{context} references unresolved Lean declarations {missing} in {tuple(module_paths)}"
        )


def _lean_module_resolves_any_declaration(
    path: str,
    names: tuple[str, ...] | list[str],
) -> bool:
    """Return whether a Lean module resolves at least one listed declaration name."""
    declarations = _lean_declaration_names(path)
    return any(
        any(
            decl_name == candidate or decl_name.endswith(f".{candidate}")
            for decl_name in declarations
        )
        for name in names
        for candidate in _lean_reference_candidates(name)
    )


def _ensure_lean_modules_contribute_named_declarations(
    module_paths: tuple[str, ...] | list[str],
    names: tuple[str, ...] | list[str],
    *,
    context: str,
) -> None:
    """Reject claim-carrier module lists that include paths unused by the named theorem surface."""
    uncovered_paths = [
        path for path in module_paths if not _lean_module_resolves_any_declaration(path, names)
    ]
    if uncovered_paths:
        raise ValueError(
            f"{context} lists Lean carrier modules without any named theorem coverage: "
            f"{uncovered_paths}"
        )


def _ensure_lean_namespace_declared(path: str, namespace: str, *, context: str) -> None:
    """Reject worked-example namespaces that are not declared in the target Lean file."""
    namespaces = _lean_namespace_names(path)
    if namespace not in namespaces:
        raise ValueError(
            f"{context} references undeclared Lean namespace {namespace} in {path}"
        )


@lru_cache(maxsize=None)
def _lean_namespace_local_declaration_names(path: str) -> dict[str, frozenset[str]]:
    """Cache namespace-local Lean declaration names for a source file."""
    declarations: dict[str, set[str]] = {}
    namespace_stack: list[str] = []

    for line in (REPO_ROOT / path).read_text().splitlines():
        namespace_match = LEAN_NAMESPACE_LINE_PATTERN.match(line)
        if namespace_match is not None:
            current_namespace = namespace_stack[-1] if namespace_stack else None
            namespace = _qualify_lean_namespace(namespace_match.group(1), current_namespace)
            namespace_stack.append(namespace)
            declarations.setdefault(namespace, set())
            continue

        end_match = LEAN_END_LINE_PATTERN.match(line)
        if end_match is not None and end_match.group(1) is not None:
            end_name = end_match.group(1)
            while namespace_stack:
                current = namespace_stack.pop()
                if end_name == current or end_name == current.split(".")[-1]:
                    break
            continue

        declaration_match = LEAN_DECL_LINE_PATTERN.match(line)
        if declaration_match is not None and namespace_stack:
            declarations.setdefault(namespace_stack[-1], set()).add(declaration_match.group(1))

    return {namespace: frozenset(names) for namespace, names in declarations.items()}


def _ensure_lean_namespace_declarations_resolve(
    path: str,
    namespace: str,
    names: tuple[str, ...] | list[str],
    *,
    context: str,
) -> None:
    """Reject worked-example theorem names that drift outside their declared namespace."""
    declared_names = _lean_namespace_local_declaration_names(path).get(namespace, frozenset())
    namespace_prefix = f"{namespace}."
    missing: list[str] = []

    for name in names:
        if "." in name:
            if not name.startswith(namespace_prefix):
                missing.append(name)
                continue
            local_name = name.removeprefix(namespace_prefix)
        else:
            local_name = name
        if local_name not in declared_names:
            missing.append(name)

    if missing:
        raise ValueError(
            f"{context} references unresolved Lean declarations {missing} in namespace {namespace}"
        )


def _ensure_lean_worked_example_consistency(
    record: LeanWorkedExampleRecord,
    *,
    witnesses_by_id: dict[str, TheoremWitnessRecord],
    context: str,
) -> None:
    """Reject worked-example rows that drift from the theorem-witness registry."""
    if not record.claim_ids:
        raise ValueError(f"{context} is missing claim ids")
    if not record.theorem_names:
        raise ValueError(f"{context} is missing theorem names")
    if not record.witness_ids:
        raise ValueError(f"{context} is missing witness ids")
    missing_witness_ids = [witness_id for witness_id in record.witness_ids if witness_id not in witnesses_by_id]
    if missing_witness_ids:
        raise ValueError(f"{context} references missing witness ids {missing_witness_ids}")
    non_theorem_witness_ids = [
        witness_id
        for witness_id in record.witness_ids
        if witnesses_by_id[witness_id].kind != "theorem-witness"
    ]
    if non_theorem_witness_ids:
        raise ValueError(
            f"{context} must reference theorem witnesses, got {non_theorem_witness_ids}"
        )
    witness_claim_ids = tuple(
        dict.fromkeys(witnesses_by_id[witness_id].claim_id for witness_id in record.witness_ids)
    )
    if record.claim_ids != witness_claim_ids:
        raise ValueError(
            f"{context} should keep claim ids aligned with theorem witnesses: "
            f"{record.claim_ids} != {witness_claim_ids}"
        )
    missing_module_citations = [
        witness_id
        for witness_id in record.witness_ids
        if record.module_path not in witnesses_by_id[witness_id].evidence
    ]
    if missing_module_citations:
        raise ValueError(
            f"{context} should point to theorem witnesses citing {record.module_path}, got "
            f"{missing_module_citations}"
        )


def _ensure_lean_worked_example_module_role(
    record: LeanWorkedExampleRecord,
    *,
    modules_by_path: dict[str, LeanModuleRecord],
    context: str,
) -> None:
    """Reject worked-example rows that drift from the Lean module index classification."""
    _ensure_indexed_lean_module_paths(
        (record.module_path,),
        modules_by_path=modules_by_path,
        context=context,
    )
    module = modules_by_path[record.module_path]
    if module.claim_ids:
        raise ValueError(
            f"{context} should use a public example module without direct claim tags, got "
            f"{module.claim_ids}"
        )
    if "public example surface" not in module.promotion_decision:
        raise ValueError(
            f"{context} should use a Lean module classified as a public example surface, got "
            f"{module.promotion_decision!r}"
        )


def _ensure_lean_worked_example_role_text(
    record: LeanWorkedExampleRecord,
    *,
    context: str,
) -> None:
    """Reject worked-example role text that drifts into claim-carrier framing."""
    role = record.current_role.strip()
    if not role:
        raise ValueError(f"{context} is missing current_role")

    lowered = role.lower()
    if "witness" not in lowered:
        raise ValueError(
            f"{context} should describe a witness-facing example role, got {record.current_role!r}"
        )
    if "claim carrier" in lowered or "theorem carrier" in lowered:
        raise ValueError(
            f"{context} should remain a worked-example witness surface rather than a claim carrier, got "
            f"{record.current_role!r}"
        )


def _ensure_theorem_witness_example_surface_coverage(
    records: tuple[LeanWorkedExampleRecord, ...] | list[LeanWorkedExampleRecord],
    *,
    witnesses: tuple[TheoremWitnessRecord, ...] | list[TheoremWitnessRecord],
    modules_by_path: dict[str, LeanModuleRecord],
) -> None:
    """Reject theorem witnesses that drift away from the worked-example namespace index."""
    example_surface_paths = {
        path
        for path, module in modules_by_path.items()
        if "public example surface" in module.promotion_decision
    }
    if not example_surface_paths:
        return

    namespaces_by_witness_id: dict[str, list[LeanWorkedExampleRecord]] = {}
    for record in records:
        for witness_id in record.witness_ids:
            namespaces_by_witness_id.setdefault(witness_id, []).append(record)

    for witness in witnesses:
        if witness.kind != "theorem-witness":
            continue
        cited_example_surface_paths = tuple(
            path for path in witness.evidence if path in example_surface_paths
        )
        if not cited_example_surface_paths:
            continue

        matching_records = [
            record
            for record in namespaces_by_witness_id.get(witness.id, [])
            if record.module_path in cited_example_surface_paths
        ]
        if not matching_records:
            raise ValueError(
                f"theorem witness {witness.id} cites public example surface(s) "
                f"{list(cited_example_surface_paths)} but no lean_worked_examples row references it"
            )
        if len(matching_records) != 1:
            raise ValueError(
                f"theorem witness {witness.id} should map to exactly one worked-example namespace "
                f"on {list(cited_example_surface_paths)}, got "
                f"{[record.namespace for record in matching_records]}"
            )


def _ensure_claim_exists(
    claim_id: str,
    *,
    claims_by_id: dict[str, ClaimRecord],
    context: str,
) -> ClaimRecord:
    """Reject registry rows that reference unknown claim ids."""
    if claim_id not in claims_by_id:
        raise ValueError(f"{context} references unknown claim id {claim_id}")
    return claims_by_id[claim_id]


def _ensure_indexed_lean_module_paths(
    module_paths: tuple[str, ...] | list[str],
    *,
    modules_by_path: dict[str, LeanModuleRecord],
    context: str,
) -> None:
    """Reject Lean module paths that are not present in the module index."""
    missing_paths = [path for path in module_paths if path not in modules_by_path]
    if missing_paths:
        raise ValueError(f"{context} references unindexed Lean module paths {missing_paths}")


def _ensure_modules_tag_claim(
    claim_id: str,
    module_paths: tuple[str, ...] | list[str],
    *,
    modules_by_path: dict[str, LeanModuleRecord],
    context: str,
) -> None:
    """Reject Lean module references that omit the corresponding claim tag."""
    missing_claim_tags = [
        path for path in module_paths if claim_id not in modules_by_path[path].claim_ids
    ]
    if missing_claim_tags:
        raise ValueError(
            f"{context} lists modules without the corresponding claim tag {claim_id}: "
            f"{missing_claim_tags}"
        )


def _ensure_claim_has_theorem_witness(
    claim_id: str,
    *,
    witnesses_by_claim: dict[str, tuple[TheoremWitnessRecord, ...]],
    context: str,
) -> None:
    """Reject atlas-backed carrier rows that do not have a theorem witness."""
    theorem_witnesses = [
        witness for witness in witnesses_by_claim.get(claim_id, ()) if witness.kind == "theorem-witness"
    ]
    if not theorem_witnesses:
        raise ValueError(f"{context} is missing a theorem witness")


def _ensure_claim_evidence_covers_modules(
    claim: ClaimRecord,
    module_paths: tuple[str, ...] | list[str],
    *,
    context: str,
) -> None:
    """Reject Lean claim-carrier rows that cite modules missing from atlas evidence."""
    missing_evidence = [path for path in module_paths if path not in claim.evidence]
    if missing_evidence:
        raise ValueError(
            f"{context} lists Lean carrier modules outside claim_registry evidence: "
            f"{missing_evidence}"
        )


def _open_boundary_module_paths(record: LeanOpenClaimBoundaryRecord) -> tuple[str, ...]:
    """Flatten a boundary record into its ordered module-path list."""
    return tuple(path for segment in record.segments for path in segment.module_paths)


def _ensure_open_claim_support_items_valid(
    record: ClaimRecord,
    *,
    modules_by_path: dict[str, LeanModuleRecord],
) -> None:
    """Reject open-claim Lean support rows that drift from the Lean module surface."""
    if record.status != "open":
        return
    for item in record.lean_support_items:
        context = f"open claim support {record.id}"
        _ensure_repo_path_exists(item.module, context=context)
        _ensure_indexed_lean_module_paths(
            (item.module,),
            modules_by_path=modules_by_path,
            context=context,
        )
        _ensure_modules_tag_claim(
            record.id,
            (item.module,),
            modules_by_path=modules_by_path,
            context=context,
        )
        if not item.theorems:
            raise ValueError(f"{context} is missing theorem names")
        _ensure_lean_declarations_resolve(
            (item.module,),
            item.theorems,
            context=context,
        )
        if not item.role:
            raise ValueError(f"{context} is missing a boundary role")


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
    records = [
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
    modules_by_path = {record.path: record for record in load_lean_module_index()}
    for record in records:
        _ensure_open_claim_support_items_valid(
            record,
            modules_by_path=modules_by_path,
        )
    return records


def load_lean_module_index() -> list[LeanModuleRecord]:
    """Load the Lean module role/promotion index."""
    records = [
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
    _ensure_unique_values(
        [record.id for record in records],
        context="Lean module index ids",
    )
    _ensure_unique_values(
        [record.path for record in records],
        context="Lean module index paths",
    )
    for record in records:
        _ensure_repo_path_exists(record.path, context=f"Lean module index {record.id}")
        _ensure_lean_module_id_matches_path(
            record.id,
            record.path,
            context=f"Lean module index {record.id}",
        )
    return records


def load_lean_claim_carriers() -> list[LeanClaimCarrierRecord]:
    """Load the atlas-backed Lean claim-carrier table metadata."""
    records = [
        LeanClaimCarrierRecord(
            claim_id=entry["claim_id"],
            module_paths=tuple(entry["module_paths"]),
            theorem_names=tuple(entry["theorem_names"]),
        )
        for entry in _load_json("lean_claim_carriers.json")
    ]
    _ensure_unique_values(
        [record.claim_id for record in records],
        context="Lean claim carrier claim ids",
    )
    claims_by_id = claim_lookup()
    modules_by_path = {record.path: record for record in load_lean_module_index()}
    witnesses_by_claim = theorem_witnesses_by_claim()
    for record in records:
        claim = _ensure_claim_exists(
            record.claim_id,
            claims_by_id=claims_by_id,
            context=f"claim carrier {record.claim_id}",
        )
        if claim.status == "open":
            raise ValueError(
                f"claim carrier {record.claim_id} cannot reference open claim {record.claim_id}"
            )
        if not record.module_paths:
            raise ValueError(f"claim carrier {record.claim_id} is missing module paths")
        if not record.theorem_names:
            raise ValueError(f"claim carrier {record.claim_id} is missing theorem names")
        for module_path in record.module_paths:
            _ensure_repo_path_exists(
                module_path,
                context=f"claim carrier {record.claim_id}",
            )
        _ensure_indexed_lean_module_paths(
            record.module_paths,
            modules_by_path=modules_by_path,
            context=f"claim carrier {record.claim_id}",
        )
        _ensure_modules_tag_claim(
            record.claim_id,
            record.module_paths,
            modules_by_path=modules_by_path,
            context=f"claim carrier {record.claim_id}",
        )
        _ensure_claim_evidence_covers_modules(
            claim,
            record.module_paths,
            context=f"claim carrier {record.claim_id}",
        )
        _ensure_lean_declarations_resolve(
            record.module_paths,
            record.theorem_names,
            context=f"claim carrier {record.claim_id}",
        )
        _ensure_lean_modules_contribute_named_declarations(
            record.module_paths,
            record.theorem_names,
            context=f"claim carrier {record.claim_id}",
        )
        _ensure_claim_has_theorem_witness(
            record.claim_id,
            witnesses_by_claim=witnesses_by_claim,
            context=f"claim carrier {record.claim_id}",
        )
    return records


def load_lean_open_claim_boundaries() -> list[LeanOpenClaimBoundaryRecord]:
    """Load the theorem-guide open-claim boundary metadata."""
    records = [
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
    _ensure_unique_values(
        [record.claim_id for record in records],
        context="Lean open-claim boundary claim ids",
    )
    claims_by_id = claim_lookup()
    modules_by_path = {record.path: record for record in load_lean_module_index()}
    for record in records:
        claim = _ensure_claim_exists(
            record.claim_id,
            claims_by_id=claims_by_id,
            context=f"open claim boundary {record.claim_id}",
        )
        if claim.status != "open":
            raise ValueError(
                f"open claim boundary {record.claim_id} cannot reference non-open claim {record.claim_id}"
            )
        if not record.segments:
            raise ValueError(f"open claim boundary {record.claim_id} is missing segments")
        for segment in record.segments:
            if not segment.summary:
                raise ValueError(
                    f"open claim boundary {record.claim_id} is missing a segment summary"
                )
            if not segment.module_paths:
                raise ValueError(
                    f"open claim boundary {record.claim_id} is missing segment module paths"
                )
            for module_path in segment.module_paths:
                _ensure_repo_path_exists(
                    module_path,
                    context=f"open claim boundary {record.claim_id}",
                )
            _ensure_indexed_lean_module_paths(
                segment.module_paths,
                modules_by_path=modules_by_path,
                context=f"open claim boundary {record.claim_id}",
            )
            _ensure_modules_tag_claim(
                record.claim_id,
                segment.module_paths,
                modules_by_path=modules_by_path,
                context=f"open claim boundary {record.claim_id}",
            )
        support_modules = tuple(item.module for item in claim.lean_support_items)
        boundary_modules = _open_boundary_module_paths(record)
        if support_modules != boundary_modules:
            raise ValueError(
                f"open claim boundary {record.claim_id} should stay aligned with claim_registry "
                f"lean_support_items: {boundary_modules} != {support_modules}"
            )
    return records


def load_lean_frontier_lanes() -> list[LeanFrontierLaneRecord]:
    """Load the theorem-guide Lean frontier lane scaffold."""
    records = [
        LeanFrontierLaneRecord(
            label=entry["label"],
            summary=entry["summary"],
        )
        for entry in _load_json("lean_frontier_lanes.json")
    ]
    seen_labels: set[str] = set()
    for record in records:
        if not record.label:
            raise ValueError("Lean frontier lane is missing a label")
        if not record.summary:
            raise ValueError(f"Lean frontier lane {record.label!r} is missing a summary")
        if record.label in seen_labels:
            raise ValueError(f"Lean frontier lane labels must be unique, got duplicate {record.label!r}")
        seen_labels.add(record.label)
    return records


def load_lean_worked_examples() -> list[LeanWorkedExampleRecord]:
    """Load the theorem-guide worked-example rows."""
    records = [
        LeanWorkedExampleRecord(
            module_path=entry["module_path"],
            namespace=entry["namespace"],
            claim_ids=tuple(entry["claim_ids"]),
            theorem_names=tuple(entry["theorem_names"]),
            current_role=entry["current_role"],
            witness_ids=tuple(entry["witness_ids"]),
        )
        for entry in _load_json("lean_worked_examples.json")
    ]
    _ensure_unique_values(
        [record.namespace for record in records],
        context="Lean worked example namespaces",
    )
    witness_records = load_theorem_witnesses()
    witnesses_by_id = {record.id: record for record in witness_records}
    modules_by_path = {record.path: record for record in load_lean_module_index()}
    for record in records:
        _ensure_repo_path_exists(record.module_path, context=f"worked example {record.namespace}")
        _ensure_lean_worked_example_module_role(
            record,
            modules_by_path=modules_by_path,
            context=f"worked example {record.namespace}",
        )
        _ensure_lean_worked_example_role_text(
            record,
            context=f"worked example {record.namespace}",
        )
        _ensure_lean_namespace_declared(
            record.module_path,
            record.namespace,
            context=f"worked example {record.namespace}",
        )
        _ensure_lean_namespace_declarations_resolve(
            record.module_path,
            record.namespace,
            record.theorem_names,
            context=f"worked example {record.namespace}",
        )
        _ensure_lean_worked_example_consistency(
            record,
            witnesses_by_id=witnesses_by_id,
            context=f"worked example {record.namespace}",
        )
    _ensure_theorem_witness_example_surface_coverage(
        records,
        witnesses=witness_records,
        modules_by_path=modules_by_path,
    )
    return records


def _expected_theorem_witness_kind(claim_status: str) -> str:
    """Return the allowed witness kind for a claim status."""
    if claim_status == "open":
        return "open-target"
    if claim_status == "empirical":
        return "empirical-witness"
    return "theorem-witness"


def _ensure_theorem_witness_valid(
    record: TheoremWitnessRecord,
    *,
    claims_by_id: dict[str, ClaimRecord],
    modules_by_path: dict[str, LeanModuleRecord],
    seen_ids: set[str],
) -> None:
    """Reject theorem-witness rows that drift from the claim and Lean surfaces."""
    context = f"theorem witness {record.id}"
    if not record.id:
        raise ValueError("theorem witness is missing an id")
    if record.id in seen_ids:
        raise ValueError(f"{context} uses duplicate witness id {record.id}")
    seen_ids.add(record.id)

    claim = _ensure_claim_exists(
        record.claim_id,
        claims_by_id=claims_by_id,
        context=context,
    )

    if not record.kind:
        raise ValueError(f"{context} is missing a witness kind")
    expected_kind = _expected_theorem_witness_kind(claim.status)
    if record.kind != expected_kind:
        raise ValueError(
            f"{context} expected witness kind {expected_kind} for claim status "
            f"{claim.status}, got {record.kind}"
        )
    if not record.label:
        raise ValueError(f"{context} is missing a label")
    if not record.tuple_display:
        raise ValueError(f"{context} is missing a tuple display")
    if not record.summary:
        raise ValueError(f"{context} is missing a summary")
    if not record.parameters:
        raise ValueError(f"{context} is missing parameters")
    if not record.evidence:
        raise ValueError(f"{context} is missing evidence paths")

    for evidence_path in record.evidence:
        _ensure_repo_path_exists(evidence_path, context=context)
        if evidence_path.startswith("lean/") and evidence_path.endswith(".lean"):
            _ensure_indexed_lean_module_paths(
                (evidence_path,),
                modules_by_path=modules_by_path,
                context=context,
            )

    if not set(record.evidence).intersection(claim.evidence):
        raise ValueError(
            f"{context} should share at least one evidence path with claim {record.claim_id}"
        )


def _search_surface_id_from_command(command: str) -> str | None:
    """Return the search surface id referenced by a user-facing command string."""
    tokens = shlex.split(command)
    if len(tokens) >= 2 and tokens[0] == "search-reptends":
        return tokens[1]
    if len(tokens) >= 4 and tokens[:3] == ["python", "-m", "bridge_reptends.search"]:
        return tokens[3]
    return None


def _ensure_throughline_search_valid(
    record: ThroughlineSearchRecord,
    *,
    context: str,
) -> None:
    """Reject throughline search entries that drift from public search/atlas surfaces."""
    if not record.id:
        raise ValueError(f"{context} is missing a search id")
    if not record.label:
        raise ValueError(f"{context} is missing a search label")
    if not record.summary:
        raise ValueError(f"{context} is missing a search summary")
    if not record.command:
        raise ValueError(f"{context} is missing a search command")

    search_surface_id = _search_surface_id_from_command(record.command)
    if search_surface_id is None:
        raise ValueError(
            f"{context} should point to a `search-reptends` command surface, got {record.command!r}"
        )
    if search_surface_id not in KNOWN_SEARCH_SURFACE_IDS:
        raise ValueError(
            f"{context} references unknown search surface {search_surface_id!r}"
        )
    if (
        record.atlas_section_id is not None
        and record.atlas_section_id not in KNOWN_ATLAS_SECTION_IDS
    ):
        raise ValueError(
            f"{context} references unknown atlas section {record.atlas_section_id!r}"
        )


def _ensure_throughline_ladder_valid(
    record: ThroughlineLadderRecord,
    *,
    context: str,
    claims_by_id: dict[str, ClaimRecord],
    witnesses_by_id: dict[str, TheoremWitnessRecord],
    counterexamples_by_id: dict[str, CounterexampleRecord],
) -> None:
    """Reject ladder rows that drift from the registry-backed support surfaces."""
    if not record.id:
        raise ValueError(f"{context} is missing a ladder id")
    if not record.label:
        raise ValueError(f"{context} is missing a ladder label")
    if not record.summary:
        raise ValueError(f"{context} is missing a ladder summary")
    if not record.claim_ids:
        raise ValueError(f"{context} is missing ladder claim ids")
    if not record.witness_ids:
        raise ValueError(f"{context} is missing ladder witness ids")

    missing_claim_ids = [claim_id for claim_id in record.claim_ids if claim_id not in claims_by_id]
    if missing_claim_ids:
        raise ValueError(f"{context} references missing claim ids {missing_claim_ids}")
    missing_witness_ids = [witness_id for witness_id in record.witness_ids if witness_id not in witnesses_by_id]
    if missing_witness_ids:
        raise ValueError(f"{context} references missing witness ids {missing_witness_ids}")
    missing_counterexample_ids = [
        counterexample_id
        for counterexample_id in record.counterexample_ids
        if counterexample_id not in counterexamples_by_id
    ]
    if missing_counterexample_ids:
        raise ValueError(
            f"{context} references missing counterexample ids {missing_counterexample_ids}"
        )


def _ensure_throughline_valid(
    record: ThroughlineRecord,
    *,
    claims_by_id: dict[str, ClaimRecord],
    witnesses_by_id: dict[str, TheoremWitnessRecord],
    counterexamples_by_id: dict[str, CounterexampleRecord],
) -> None:
    """Reject throughline rows that drift from the public registry/search surface."""
    context = f"throughline {record.id}"
    if not record.id:
        raise ValueError("throughline is missing an id")
    if record.kind != "research-thesis":
        raise ValueError(f"{context} expected kind 'research-thesis', got {record.kind!r}")
    if not record.title:
        raise ValueError(f"{context} is missing a title")
    if not record.headline:
        raise ValueError(f"{context} is missing a headline")
    if not record.status_note:
        raise ValueError(f"{context} is missing a status note")
    if not record.claim_ids:
        raise ValueError(f"{context} is missing claim ids")
    if not record.open_claim_ids:
        raise ValueError(f"{context} is missing open claim ids")
    if not record.witness_ids:
        raise ValueError(f"{context} is missing witness ids")
    if not record.featured_searches:
        raise ValueError(f"{context} is missing featured searches")
    if not record.ladder:
        raise ValueError(f"{context} is missing ladder entries")

    missing_claim_ids = [claim_id for claim_id in record.claim_ids if claim_id not in claims_by_id]
    if missing_claim_ids:
        raise ValueError(f"{context} references missing claim ids {missing_claim_ids}")
    missing_open_claim_ids = [
        claim_id for claim_id in record.open_claim_ids if claim_id not in claims_by_id
    ]
    if missing_open_claim_ids:
        raise ValueError(f"{context} references missing open claim ids {missing_open_claim_ids}")
    non_open_claim_ids = [
        claim_id for claim_id in record.open_claim_ids if claims_by_id[claim_id].status != "open"
    ]
    if non_open_claim_ids:
        raise ValueError(f"{context} expected open claim ids, got {non_open_claim_ids}")
    if not set(record.open_claim_ids).issubset(record.claim_ids):
        raise ValueError(f"{context} should include open claim ids inside claim_ids")

    missing_witness_ids = [witness_id for witness_id in record.witness_ids if witness_id not in witnesses_by_id]
    if missing_witness_ids:
        raise ValueError(f"{context} references missing witness ids {missing_witness_ids}")
    missing_counterexample_ids = [
        counterexample_id
        for counterexample_id in record.counterexample_ids
        if counterexample_id not in counterexamples_by_id
    ]
    if missing_counterexample_ids:
        raise ValueError(
            f"{context} references missing counterexample ids {missing_counterexample_ids}"
        )

    _ensure_unique_values(
        [entry.id for entry in record.featured_searches],
        context=f"{context} featured search ids",
    )
    for entry in record.featured_searches:
        _ensure_throughline_search_valid(entry, context=f"{context} search {entry.id}")

    _ensure_unique_values(
        [entry.id for entry in record.ladder],
        context=f"{context} ladder ids",
    )
    for entry in record.ladder:
        _ensure_throughline_ladder_valid(
            entry,
            context=f"{context} ladder {entry.id}",
            claims_by_id=claims_by_id,
            witnesses_by_id=witnesses_by_id,
            counterexamples_by_id=counterexamples_by_id,
        )


def load_theorem_witnesses() -> list[TheoremWitnessRecord]:
    """Load the theorem-witness atlas."""
    records = [
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
    claims_by_id = claim_lookup()
    modules_by_path = {record.path: record for record in load_lean_module_index()}
    seen_ids: set[str] = set()
    for record in records:
        _ensure_theorem_witness_valid(
            record,
            claims_by_id=claims_by_id,
            modules_by_path=modules_by_path,
            seen_ids=seen_ids,
        )
    return records


def load_throughlines() -> list[ThroughlineRecord]:
    """Load the research-thesis throughline registry."""
    records = [
        ThroughlineRecord(
            id=entry["id"],
            kind=entry["kind"],
            title=entry["title"],
            headline=entry["headline"],
            status_note=entry["status_note"],
            claim_ids=tuple(entry["claim_ids"]),
            open_claim_ids=tuple(entry["open_claim_ids"]),
            witness_ids=tuple(entry["witness_ids"]),
            counterexample_ids=tuple(entry["counterexample_ids"]),
            featured_searches=tuple(
                ThroughlineSearchRecord(
                    id=search["id"],
                    label=search["label"],
                    summary=search["summary"],
                    command=search["command"],
                    atlas_section_id=search.get("atlas_section_id"),
                )
                for search in entry["featured_searches"]
            ),
            ladder=tuple(
                ThroughlineLadderRecord(
                    id=ladder["id"],
                    label=ladder["label"],
                    claim_ids=tuple(ladder["claim_ids"]),
                    witness_ids=tuple(ladder["witness_ids"]),
                    counterexample_ids=tuple(ladder.get("counterexample_ids", ())),
                    summary=ladder["summary"],
                )
                for ladder in entry["ladder"]
            ),
        )
        for entry in _load_json("throughlines.json")
    ]
    _ensure_unique_values([record.id for record in records], context="Throughline ids")
    claims_by_id = claim_lookup()
    witnesses_by_id = theorem_witness_lookup()
    counterexamples_by_id = counterexample_lookup()
    for record in records:
        _ensure_throughline_valid(
            record,
            claims_by_id=claims_by_id,
            witnesses_by_id=witnesses_by_id,
            counterexamples_by_id=counterexamples_by_id,
        )
    return records


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


def throughline_lookup() -> dict[str, ThroughlineRecord]:
    """Index the research-thesis throughline registry by id."""
    return {record.id: record for record in load_throughlines()}


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
            _ensure_lean_declarations_resolve(
                (item.module,),
                item.theorems,
                context=f"open claim support {record.id}",
            )
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
        _ensure_lean_declarations_resolve(
            record.module_paths,
            record.theorem_names,
            context=f"claim carrier {record.claim_id}",
        )
        _ensure_lean_modules_contribute_named_declarations(
            record.module_paths,
            record.theorem_names,
            context=f"claim carrier {record.claim_id}",
        )
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


def render_lean_worked_example_lines(
    worked_examples: list[LeanWorkedExampleRecord] | None = None,
    witnesses: list[TheoremWitnessRecord] | None = None,
) -> tuple[str, ...]:
    """Render the theorem-guide worked-example table."""
    records = worked_examples or load_lean_worked_examples()
    witness_records = witnesses or load_theorem_witnesses()
    witnesses_by_id = {record.id: record for record in witness_records}
    lines = [
        "| Lean example namespace | Atlas claim IDs | Example theorem entry points | Current role | Witness-atlas entry points |",
        "|------------------------|-----------------|------------------------------|--------------|----------------------------|",
    ]
    for record in records:
        _ensure_lean_declarations_resolve(
            (record.module_path,),
            record.theorem_names,
            context=f"worked example {record.namespace}",
        )
        _ensure_lean_worked_example_consistency(
            record,
            witnesses_by_id=witnesses_by_id,
            context=f"worked example {record.namespace}",
        )
        namespace_cell = f"{_lean_doc_link(record.module_path)} `{record.namespace}`"
        claim_cell = ", ".join(f"`{claim_id}`" for claim_id in record.claim_ids)
        theorem_cell = ", ".join(f"`{name}`" for name in record.theorem_names)
        witness_cell = ", ".join(f"`{witness_id}`" for witness_id in record.witness_ids)
        lines.append(
            f"| {namespace_cell} | {claim_cell} | {theorem_cell} | {record.current_role} | {witness_cell} |"
        )
    return tuple(lines)


def _ensure_name_subsequence(
    names: tuple[str, ...] | list[str],
    reference_names: tuple[str, ...] | list[str],
    *,
    context: str,
) -> None:
    """Reject curated code-name lists that drift out of their parent registry order."""
    positions: list[int] = []
    missing: list[str] = []
    reference = tuple(reference_names)

    for name in names:
        try:
            positions.append(reference.index(name))
        except ValueError:
            missing.append(name)

    if missing:
        raise ValueError(f"{context} references names outside the parent registry order: {missing}")
    if positions != sorted(positions):
        raise ValueError(f"{context} should follow worked-example theorem order: {list(names)}")


def render_examples_open_boundary_note_lines(
    worked_examples: list[LeanWorkedExampleRecord] | None = None,
    witnesses: list[TheoremWitnessRecord] | None = None,
    claims: list[ClaimRecord] | None = None,
) -> tuple[str, ...]:
    """Render the worked-example open-boundary note for `QRTour/Examples.lean`."""
    records = {record.namespace: record for record in (worked_examples or load_lean_worked_examples())}
    witness_map = {record.id: record for record in (witnesses or load_theorem_witnesses())}
    claims_by_id = _claims_by_id(claims)
    lines: list[str] = []

    for (
        claim_id,
        namespace,
        theorem_names,
        witness_id,
        witness_claim_id,
        witness_kind,
        summary,
    ) in _EXAMPLES_OPEN_BOUNDARY_NOTE_ROWS:
        claim = claims_by_id.get(claim_id)
        if claim is None:
            raise ValueError(f"missing claim record for examples open-boundary note {claim_id}")
        if claim.status != "open":
            raise ValueError(
                f"examples open-boundary note expected open claim {claim_id}, got {claim.status}"
            )

        record = records.get(namespace)
        if record is None:
            raise ValueError(
                f"examples open-boundary note references missing worked-example namespace {namespace}"
            )
        missing_theorems = [name for name in theorem_names if name not in record.theorem_names]
        if missing_theorems:
            raise ValueError(
                f"examples open-boundary note {claim_id} references theorem names "
                f"outside {namespace}: {missing_theorems}"
            )
        _ensure_name_subsequence(
            theorem_names,
            record.theorem_names,
            context=f"examples open-boundary note {claim_id}",
        )

        witness = witness_map.get(witness_id)
        if witness is None:
            raise ValueError(f"examples open-boundary note references missing witness {witness_id}")
        if witness.claim_id != witness_claim_id:
            raise ValueError(
                "examples open-boundary note expected witness "
                f"{witness.id} to carry claim {witness_claim_id}, got {witness.claim_id}"
            )
        if witness.kind != witness_kind:
            raise ValueError(
                "examples open-boundary note expected witness "
                f"{witness.id} to have kind {witness_kind}, got {witness.kind}"
            )
        theorem_cell = _join_code_names(theorem_names)
        lines.append(
            f"- `{claim_id}` remains `open`: on `{namespace}`, {theorem_cell} {summary} "
            f"The related atlas entry is `{witness.id}`."
        )

    return tuple(lines)


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
    return tuple(
        f"- {record.label}: {record.summary}"
        for record in load_lean_frontier_lanes()
    )


def _lean_module_id_from_path(path: str) -> str:
    """Convert a Lean source path to the corresponding import/module id."""
    return path.removeprefix("lean/").removesuffix(".lean").replace("/", ".")


def _join_code_names(names: tuple[str, ...] | list[str], *, pair_joiner: str = " and ") -> str:
    """Render a short list of backticked code ids."""
    rendered = [f"`{name}`" for name in names]
    if not rendered:
        raise ValueError("expected at least one code name")
    if len(rendered) == 1:
        return rendered[0]
    if len(rendered) == 2:
        return f"{rendered[0]}{pair_joiner}{rendered[1]}"
    return f"{', '.join(rendered[:-1])}, and {rendered[-1]}"


def _join_rendered_items(items: tuple[str, ...] | list[str], *, pair_joiner: str = " and ") -> str:
    """Render a short list of already-formatted items."""
    rendered = list(items)
    if not rendered:
        raise ValueError("expected at least one rendered item")
    if len(rendered) == 1:
        return rendered[0]
    if len(rendered) == 2:
        return f"{rendered[0]}{pair_joiner}{rendered[1]}"
    return f"{', '.join(rendered[:-1])}, and {rendered[-1]}"


def _qr_tour_theorem_surface_groups(
    carriers: list[LeanClaimCarrierRecord],
) -> tuple[tuple[tuple[str, ...], tuple[str, ...]], ...]:
    """Group consecutive claim-carrier rows that share the same module tuple."""
    groups: list[tuple[tuple[str, ...], tuple[str, ...]]] = []
    current_modules: tuple[str, ...] | None = None
    current_claims: list[str] = []

    for record in carriers:
        if current_modules is None or record.module_paths != current_modules:
            if current_modules is not None:
                groups.append((current_modules, tuple(current_claims)))
            current_modules = record.module_paths
            current_claims = [record.claim_id]
            continue
        current_claims.append(record.claim_id)

    if current_modules is not None:
        groups.append((current_modules, tuple(current_claims)))

    return tuple(groups)


def render_qr_tour_theorem_surface_lines(
    carriers: list[LeanClaimCarrierRecord] | None = None,
) -> tuple[str, ...]:
    """Render the registry-backed theorem-surface summary in `lean/QRTour.lean`."""
    records = carriers or load_lean_claim_carriers()
    lines = []
    for module_paths, claim_ids in _qr_tour_theorem_surface_groups(records):
        module_ids = tuple(_lean_module_id_from_path(path) for path in module_paths)
        lines.append(
            f"- {_join_code_names(module_ids, pair_joiner=' together with ')} for {_join_code_names(claim_ids)}"
        )
    lines.extend(
        [
            "",
            "Support modules such as `QRTour.RemainderOrbit`, `QRTour.Bridge`,",
            "`QRTour.CosetStructure`, and `QRTour.CompositeVisibility` package the exact",
            "infrastructure beneath those public statements. The carry modules also sit on",
            "the theorem boundary: they carry the exact finite",
            "`carry_window_transducer` claim while still serving as support beneath the",
            "open global `carry_dfa_factorization` claim.",
            "`QRTour.PrimitiveRoots` remains general generator infrastructure above the",
            "current QR-specific claim surface, and `QRTour.BridgeQuality` remains an",
            "exploratory bridge-quality support layer rather than an atlas-backed theorem",
            "carrier.",
        ]
    )
    return tuple(lines)


def render_readme_lean_claim_surface_lines(
    carriers: list[LeanClaimCarrierRecord] | None = None,
) -> tuple[str, ...]:
    """Render the README Lean claim-carrier summary from the registry-backed surface."""
    records = carriers or load_lean_claim_carriers()
    return tuple(
        f"- {_join_rendered_items(tuple(_lean_doc_link(path) for path in module_paths), pair_joiner=' together with ')} closes {_join_code_names(claim_ids)}"
        for module_paths, claim_ids in _qr_tour_theorem_surface_groups(records)
    )


def _throughline_by_id(
    throughline_id: str,
    throughlines: list[ThroughlineRecord] | None = None,
) -> ThroughlineRecord:
    """Return one throughline record by id."""
    records = throughlines or load_throughlines()
    for record in records:
        if record.id == throughline_id:
            return record
    raise ValueError(f"missing throughline record {throughline_id}")


def render_throughline_research_thesis_lines(
    throughline_id: str = "orbit_plus_carry_factorization",
    *,
    throughlines: list[ThroughlineRecord] | None = None,
) -> tuple[str, ...]:
    """Render the flagship research-thesis block for README/docs surfaces."""
    record = _throughline_by_id(throughline_id, throughlines)
    exact_claim_ids = tuple(claim_id for claim_id in record.claim_ids if claim_id not in record.open_claim_ids)
    witness_cell = _join_code_names(record.witness_ids)
    counterexample_cell = _join_code_names(record.counterexample_ids)
    lines = [
        f"- Kind: `{record.kind}`",
        f"- Thesis ID: `{record.id}`",
        f"- Title: {record.title}",
        f"- Headline: {record.headline}",
        f"- Status note: {record.status_note}",
        f"- Exact support claims: {_join_code_names(exact_claim_ids)}",
        f"- Open frontier claims: {_join_code_names(record.open_claim_ids)}",
        f"- Canonical witness anchors: {witness_cell}",
        f"- Obstruction records: {counterexample_cell}",
    ]
    lines.extend(
        f"- Search surface `{entry.id}`: {entry.summary} Command: `{entry.command}`"
        for entry in record.featured_searches
    )
    return tuple(lines)


def render_throughline_witness_ladder_lines(
    throughline_id: str = "orbit_plus_carry_factorization",
    *,
    throughlines: list[ThroughlineRecord] | None = None,
) -> tuple[str, ...]:
    """Render the throughline witness ladder for the theorem-witness atlas."""
    record = _throughline_by_id(throughline_id, throughlines)
    lines = [
        "| Ladder rung | Registry support |",
        "|-------------|------------------|",
    ]
    for ladder in record.ladder:
        claim_cell = _join_code_names(ladder.claim_ids)
        witness_cell = _join_code_names(ladder.witness_ids)
        detail = f"Claims {claim_cell}; witnesses {witness_cell}. {ladder.summary}"
        if ladder.counterexample_ids:
            detail += f" Counterexamples: {_join_code_names(ladder.counterexample_ids)}."
        lines.append(f"| {ladder.label} | {detail} |")
    return tuple(lines)


def render_theorem_guide_throughline_layer_lines(
    throughline_id: str = "orbit_plus_carry_factorization",
    *,
    throughlines: list[ThroughlineRecord] | None = None,
) -> tuple[str, ...]:
    """Render the Lean-facing module grouping for the orbit/carry throughline."""
    record = _throughline_by_id(throughline_id, throughlines)
    claims = claim_lookup()
    exact_orbit_ids = {
        "digit_periodicity",
        "preperiod_from_base_factors",
        "series_q_weighted_identity",
        "positive_q_good_modes",
    }
    carry_layer_ids = {
        "incoming_carry_position_formula",
        "same_core_threshold_shift_interval",
        "carry_window_transducer",
    }
    frontier_ids = tuple(record.open_claim_ids)

    def _lean_modules_for_claims(claim_ids: set[str]) -> tuple[str, ...]:
        modules = tuple(
            dict.fromkeys(
                path
                for claim_id in record.claim_ids
                if claim_id in claim_ids
                for path in claims[claim_id].evidence
                if path.startswith("lean/") and path.endswith(".lean")
            )
        )
        return modules

    orbit_modules = _lean_modules_for_claims(exact_orbit_ids)
    carry_modules = _lean_modules_for_claims(carry_layer_ids)
    frontier_modules = tuple(
        dict.fromkeys(
            path
            for claim_id in frontier_ids
            for item in claims[claim_id].lean_support_items
            for path in (item.module,)
        )
    )
    return (
        f"- orbit-layer support: {_join_rendered_items(tuple(_lean_doc_link(path) for path in orbit_modules))} back {_join_code_names(tuple(claim_id for claim_id in record.claim_ids if claim_id in exact_orbit_ids))}",
        f"- carry-layer support: {_join_rendered_items(tuple(_lean_doc_link(path) for path in carry_modules))} back {_join_code_names(tuple(claim_id for claim_id in record.claim_ids if claim_id in carry_layer_ids))}",
        f"- factorization-frontier support: {_join_rendered_items(tuple(_lean_doc_link(path) for path in frontier_modules))} stay beneath {_join_code_names(record.open_claim_ids)} and keep the throughline classificatory rather than theorem-promoting",
    )


def _claims_by_id(claims: list[ClaimRecord] | None = None) -> dict[str, ClaimRecord]:
    """Index claim records by claim id."""
    return {record.id: record for record in (claims or load_claim_registry())}


def _claim_status_anchor_line(
    claims_by_id: dict[str, ClaimRecord],
    claim_id: str,
    *,
    require_open: bool = False,
) -> str:
    """Render one status-anchor bullet from the claim registry."""
    if claim_id not in claims_by_id:
        raise ValueError(f"missing claim record for status-anchor claim {claim_id}")
    record = claims_by_id[claim_id]
    if require_open and record.status != "open":
        raise ValueError(f"expected open claim for status-anchor line {claim_id}, got {record.status}")
    verb = "remains" if require_open else "is"
    return f"- Claim ID `{claim_id}` {verb} `{record.status}`."


def render_carry_transducer_status_anchor_lines(
    claims: list[ClaimRecord] | None = None,
) -> tuple[str, ...]:
    """Render the registry-backed status anchor for `docs/CARRY_TRANSDUCER.md`."""
    claims_by_id = _claims_by_id(claims)
    return (
        _claim_status_anchor_line(claims_by_id, "carry_window_transducer"),
        (
            f"{_claim_status_anchor_line(claims_by_id, 'small_k_visibility_threshold', require_open=True)[:-1]} "
            f"and is now split into exact observables in {_doc_link('docs/CARRIED_PREFIX_VISIBILITY.md')}."
        ),
        _claim_status_anchor_line(claims_by_id, "carry_dfa_factorization", require_open=True),
        "- Preferred standard label: `carry-propagated block normalization`.",
    )


def render_carried_prefix_visibility_status_anchor_lines(
    claims: list[ClaimRecord] | None = None,
) -> tuple[str, ...]:
    """Render the registry-backed status anchor for `docs/CARRIED_PREFIX_VISIBILITY.md`."""
    claims_by_id = _claims_by_id(claims)
    return (
        _claim_status_anchor_line(claims_by_id, "small_k_visibility_heuristic"),
        _claim_status_anchor_line(claims_by_id, "incoming_carry_position_formula"),
        _claim_status_anchor_line(claims_by_id, "small_k_visibility_threshold", require_open=True),
        (
            "- Preferred standard labels: `raw coefficient stream`, "
            "`carry-propagated block normalization`, `raw-prefix agreement length`."
        ),
    )


_QR_TOUR_OPEN_BOUNDARY_SUMMARIES = {
    "small_k_visibility_threshold": (
        "Lean currently proves the exact fixed-window certificate, same-core "
        "transport, and certified finite visible-word agreement beneath that "
        "boundary"
    ),
    "carry_dfa_factorization": (
        "Lean currently proves finite carry normalization, traced comparison, "
        "restricted coordinate-level morphism packaging, and finite "
        "state-alignment criteria beneath that boundary"
    ),
}


def render_qr_tour_open_boundary_lines(
    claims: list[ClaimRecord] | None = None,
) -> tuple[str, ...]:
    """Render the open-claim boundary bullets in `lean/QRTour.lean`."""
    records = open_claims(claims)
    missing = [record.id for record in records if record.id not in _QR_TOUR_OPEN_BOUNDARY_SUMMARIES]
    if missing:
        raise ValueError(f"missing QRTour open-boundary summary for {missing}")
    return tuple(
        f"- `{record.id}` remains `open`; {_QR_TOUR_OPEN_BOUNDARY_SUMMARIES[record.id]}"
        for record in records
    )


def _render_lean_import_lines(
    directory: str,
    modules: list[LeanModuleRecord] | None = None,
) -> tuple[str, ...]:
    """Render umbrella import lines from the ordered Lean module index."""
    return tuple(
        f"import {record.id}"
        for record in (modules or load_lean_module_index())
        if record.path.startswith(f"lean/{directory}/") and record.path.endswith(".lean")
    )


def render_qr_tour_import_lines(
    modules: list[LeanModuleRecord] | None = None,
) -> tuple[str, ...]:
    """Render the ordered `QRTour.lean` umbrella imports from the module index."""
    return _render_lean_import_lines("QRTour", modules)


_QR_TOUR_MODULE_DESCRIPTIONS = {
    "QRTour.Basic": "Prime field setup with `ZMod p`",
    "QRTour.RemainderOrbit": "Long division remainders and the main theorem",
    "QRTour.Bridge": '"Bridge primes" of form p = B^k - d with block structure',
    "QRTour.CosetStructure": "Two-coset partition based on QR/NQR numerators",
    "QRTour.QuadraticResidues": (
        "QR definitions and QR generators, including the exact order/gcd "
        "classification for QR-generating powers"
    ),
    "QRTour.OrbitWeave": "block-coordinate arithmetic for the q-weighted series layer",
    "QRTour.Digits": "Digit-remainder duality and reptend periodicity",
    "QRTour.PrimitiveRoots": (
        "Full generators (primitive roots) and subgroup generators; support-only "
        "infrastructure above the current atlas-backed QR surface"
    ),
    "QRTour.BridgeQuality": (
        "Approximate bridges, deficit metrics, factor inheritance; exploratory "
        "support only, not an atlas-backed theorem carrier"
    ),
    "QRTour.SignedBridge": "Unified plus/minus bridges, alternating sign structure",
    "QRTour.PAdicBridge": "P-adic structure in bridges, block values, periodicity",
    "QRTour.CompositePeriod": "finite-family CRT period theorem for composite moduli",
    "QRTour.Preperiod": "local valuation theorem behind composite preperiod lengths",
    "QRTour.Visibility": "exact incoming-carry boundaries and same-core threshold shifts",
    "QRTour.CarryTransducer": "finite carry-normalization on raw coefficient words",
    "QRTour.CarryComparison": "exact finite-window carry/remainder trace alignment",
    "QRTour.Factorization": "restricted finite-window remainder-to-carry morphism layer",
    "QRTour.CompositeVisibility": "same-core family packaging for stripped periodic cores",
    "QRTour.ChartInvariance": "finite chart-observation and witness surface for visibility geometry",
    "QRTour.Examples": (
        "Worked prime, small composite, positive-q composite, and same-core "
        "composite examples"
    ),
}


def render_qr_tour_module_lines(
    modules: list[LeanModuleRecord] | None = None,
) -> tuple[str, ...]:
    """Render the ordered QRTour module summary list in `lean/QRTour.lean`."""
    records = [
        record
        for record in (modules or load_lean_module_index())
        if record.path.startswith("lean/QRTour/") and record.path.endswith(".lean")
    ]
    expected_ids = {record.id for record in records}
    description_ids = set(_QR_TOUR_MODULE_DESCRIPTIONS)
    if expected_ids != description_ids:
        missing = sorted(expected_ids - description_ids)
        extra = sorted(description_ids - expected_ids)
        raise ValueError(f"QRTour module descriptions out of sync: missing={missing}, extra={extra}")

    lines: list[str] = []
    for record in records:
        lines.append(f"- `{record.id}` - {_QR_TOUR_MODULE_DESCRIPTIONS[record.id]}")
    return tuple(lines)


_GEOMETRIC_STACK_MODULE_DESCRIPTIONS = {
    "GeometricStack.Family": "base-invariant family definitions for capacities and geometric powers",
    "GeometricStack.Capacity": "capacity-index packaging and threshold-bound layer",
    "GeometricStack.Scale": "fixed-scale direct and overflow decomposition layer",
    "GeometricStack.Valuation": "capacity-as-valuation and digit-count companion layer",
    "GeometricStack.Positional": "positional-digit companion surface for the scale decomposition",
    "GeometricStack.OrbitBufferDuality": "repunit remainder-orbit conjugacy and periodicity companion layer",
}


def render_geometric_stack_module_lines(
    modules: list[LeanModuleRecord] | None = None,
) -> tuple[str, ...]:
    """Render the ordered GeometricStack module summary list in `lean/GeometricStack.lean`."""
    records = [
        record
        for record in (modules or load_lean_module_index())
        if record.path.startswith("lean/GeometricStack/") and record.path.endswith(".lean")
    ]
    expected_ids = {record.id for record in records}
    description_ids = set(_GEOMETRIC_STACK_MODULE_DESCRIPTIONS)
    if expected_ids != description_ids:
        missing = sorted(expected_ids - description_ids)
        extra = sorted(description_ids - expected_ids)
        raise ValueError(
            f"GeometricStack module descriptions out of sync: missing={missing}, extra={extra}"
        )

    return tuple(
        f"- `{record.id}` - {_GEOMETRIC_STACK_MODULE_DESCRIPTIONS[record.id]}" for record in records
    )


def render_geometric_stack_import_lines(
    modules: list[LeanModuleRecord] | None = None,
) -> tuple[str, ...]:
    """Render the ordered `GeometricStack.lean` umbrella imports from the module index."""
    return _render_lean_import_lines("GeometricStack", modules)


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
    if visibility.claim_id != "same_core_threshold_shift_interval":
        raise ValueError(
            "same-core boundary note expected witness "
            f"{visibility.id} to carry claim same_core_threshold_shift_interval, "
            f"got {visibility.claim_id}"
        )
    if visibility.kind != "theorem-witness":
        raise ValueError(
            "same-core boundary note expected witness "
            f"{visibility.id} to have kind theorem-witness, got {visibility.kind}"
        )
    if carry.claim_id != "carry_dfa_factorization":
        raise ValueError(
            "same-core boundary note expected witness "
            f"{carry.id} to carry claim carry_dfa_factorization, got {carry.claim_id}"
        )
    if carry.kind != "open-target":
        raise ValueError(
            "same-core boundary note expected witness "
            f"{carry.id} to have kind open-target, got {carry.kind}"
        )
    return (
        "| Surface | Atlas witness | Current boundary signal |",
        "|---------|---------------|-------------------------|",
        f"| Exact same-core visibility transport | `{visibility.id}` | Claim `{visibility.claim_id}`: {visibility.summary} |",
        f"| Same-core selector-family failure | `{carry.id}` | Claim `{carry.claim_id}`: {carry.summary} This keeps forward same-core `carryToRemainderFunctional` transport outside the current Lean claim surface. |",
    )


def render_theorem_witness_table_lines(
    witnesses: list[TheoremWitnessRecord] | None = None,
    claims: dict[str, ClaimRecord] | None = None,
    worked_examples: list[LeanWorkedExampleRecord] | None = None,
) -> tuple[str, ...]:
    """Render the theorem-witness atlas table for public docs."""
    records = witnesses or load_theorem_witnesses()
    claim_records = claims or claim_lookup()
    worked_example_records = worked_examples or load_lean_worked_examples()
    worked_examples_by_witness_id: dict[str, list[LeanWorkedExampleRecord]] = {}
    for record in worked_example_records:
        for witness_id in record.witness_ids:
            worked_examples_by_witness_id.setdefault(witness_id, []).append(record)
    lines = [
        "| Witness ID | Claim ID | Claim Status | Kind | Canonical tuple or family | Why this witness | Lean example namespace(s) | Repo Evidence |",
        "|------------|----------|--------------|------|---------------------------|------------------|---------------------------|---------------|",
    ]
    for record in records:
        claim_status = claim_records[record.claim_id].status
        worked_example_cell = ", ".join(
            f"{_lean_doc_link(example.module_path)} `{example.namespace}`"
            for example in worked_examples_by_witness_id.get(record.id, ())
        ) or "-"
        evidence_links = ", ".join(_doc_link(path) for path in record.evidence)
        lines.append(
            f"| `{record.id}` | `{record.claim_id}` | `{claim_status}` | `{record.kind}` | {record.tuple_display} | {record.summary} | {worked_example_cell} | {evidence_links} |"
        )
    return tuple(lines)
