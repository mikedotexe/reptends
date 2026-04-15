#!/usr/bin/env python3
"""
Search and dataset generation for notable reptend examples.

This module turns the repo's exploratory scripts into reusable outputs:
- bridge-candidate ranking for readable q-weighted skeletons
- distinct leaderboards for q=1 bridges, nontrivial bridges, composites, and prime QR examples
- claim-linked theorem-witness exports for the current atlas-backed formal surface,
  including linked Lean worked-example metadata
- explicit legacy counterexample search
- composite CRT profile export
- a curated example atlas suitable for docs and the site
"""

from __future__ import annotations

import csv
import json
from dataclasses import asdict, dataclass
from math import gcd
from pathlib import Path

from .analysis import (
    analyze_prime,
    find_qr_strides,
    multiplicative_order,
    reptend_type,
)
from .composite import (
    canonical_composite_case_studies,
    canonical_composite_family_case_studies,
    crt_period_profile,
)
from .orbit_weave import factorize, find_good_modes, skeleton_vs_actual, strip_base_factors
from .registry import (
    STATUS_ORDER,
    claim_context_for_parameters,
    claim_lookup,
    load_counterexamples,
    load_lean_worked_examples,
    load_theorem_witnesses,
    load_throughlines,
)
from .transducer import (
    canonical_carry_dfa_examples,
    canonical_carry_selector_case_studies,
    canonical_carry_selector_family_studies,
    canonical_state_merging_case_studies,
    canonical_state_merging_family_studies,
    carry_factorization_rows,
    carry_selector_profile_class,
    carry_selector_profile_rows,
    carry_selector_research_rows,
    non_k_one_state_relabeling_rows,
    quotient_obstruction_census_from_rows,
    same_core_obstruction_correlate_rows,
    quotient_obstruction_family_rows,
    quotient_obstruction_rows,
    same_core_obstruction_phase_rows,
    same_core_selector_family_rows,
    state_merging_rows,
    state_merging_same_core_rows,
)
from .visibility import (
    canonical_visibility_case_studies,
    canonical_visibility_family_studies,
    incoming_carry_counterexample_rows,
    same_core_visibility_rows,
    visibility_profile_rows,
)


DEFAULT_MIN_SIGNAL_MODULUS = 19
PUBLISHED_ATLAS_SCHEMA_VERSION = "2.16"
WITNESS_KIND_ORDER = ("theorem-witness", "empirical-witness", "open-target")


def sieve_primes(max_n: int) -> list[int]:
    """Simple sieve of Eratosthenes."""
    if max_n < 2:
        return []
    sieve = [True] * (max_n + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(max_n**0.5) + 1):
        if sieve[i]:
            for j in range(i * i, max_n + 1, i):
                sieve[j] = False
    return [i for i in range(2, max_n + 1) if sieve[i]]


def _leading_match_count(lhs: list[str], rhs: list[str]) -> int:
    count = 0
    for left, right in zip(lhs, rhs):
        if left != right:
            break
        count += 1
    return count


@dataclass(frozen=True)
class BridgeCandidate:
    n: int
    periodic_modulus: int
    base: int
    m: int
    B: int
    k: int
    q: int
    period: int
    preperiod_digits: int
    visible_prefix: int
    q_is_one: bool
    is_trivial_period: bool
    score: int
    primary_vocabulary_id: str
    explanation: str


@dataclass(frozen=True)
class PrimeQRExample:
    p: int
    base: int
    reptend_type: str
    preferred_stride: int
    preferred_k: int
    stride_count: int
    score: int
    primary_vocabulary_id: str
    explanation: str


@dataclass(frozen=True)
class CompositeHighlight:
    n: int
    stripped_modulus: int
    base: int
    global_order: int
    preperiod_digits: int
    component_count: int
    best_m: int | None
    best_k: int | None
    best_q: int | None
    score: int
    primary_vocabulary_id: str
    explanation: str


@dataclass(frozen=True)
class CanonicalExample:
    label: str
    n: int
    category: str
    primary_vocabulary_id: str
    explanation: str


def build_claim_witness_rows(
    *,
    claim_id: str | None = None,
    status: str | None = None,
    kind: str | None = None,
    lean_example_namespace: str | None = None,
) -> list[dict[str, object]]:
    """Return enriched theorem-witness rows for search/site-facing exports."""
    claims = claim_lookup()
    worked_example_namespaces_by_witness_id: dict[str, list[str]] = {}
    worked_examples_by_witness_id: dict[str, list[dict[str, object]]] = {}
    for record in load_lean_worked_examples():
        worked_example_row = {
            "module_path": record.module_path,
            "namespace": record.namespace,
            "claim_ids": list(record.claim_ids),
            "theorem_names": list(record.theorem_names),
        }
        for witness_id in record.witness_ids:
            worked_example_namespaces_by_witness_id.setdefault(witness_id, []).append(record.namespace)
            worked_examples_by_witness_id.setdefault(witness_id, []).append(worked_example_row)
    known_worked_example_namespaces = {
        namespace
        for namespaces in worked_example_namespaces_by_witness_id.values()
        for namespace in namespaces
    }
    if claim_id is not None and claim_id not in claims:
        raise ValueError(f"unknown claim_id: {claim_id}")
    if status is not None and status not in STATUS_ORDER:
        raise ValueError(f"unknown claim status: {status}")
    if kind is not None and kind not in WITNESS_KIND_ORDER:
        raise ValueError(f"unknown witness kind: {kind}")
    if (
        lean_example_namespace is not None
        and lean_example_namespace not in known_worked_example_namespaces
    ):
        raise ValueError(f"unknown lean example namespace: {lean_example_namespace}")

    rows: list[dict[str, object]] = []
    for witness in load_theorem_witnesses():
        claim = claims[witness.claim_id]
        lean_example_namespaces = list(
            dict.fromkeys(worked_example_namespaces_by_witness_id.get(witness.id, ()))
        )
        lean_examples = list(worked_examples_by_witness_id.get(witness.id, ()))
        if claim_id is not None and witness.claim_id != claim_id:
            continue
        if status is not None and claim.status != status:
            continue
        if kind is not None and witness.kind != kind:
            continue
        if (
            lean_example_namespace is not None
            and lean_example_namespace not in lean_example_namespaces
        ):
            continue
        rows.append(
            {
                "witness_id": witness.id,
                "claim_id": witness.claim_id,
                "claim_title": claim.title,
                "claim_status": claim.status,
                "kind": witness.kind,
                "label": witness.label,
                "tuple_display": witness.tuple_display,
                "parameters": witness.parameters,
                "summary": witness.summary,
                "lean_example_namespaces": lean_example_namespaces,
                "lean_examples": lean_examples,
                "evidence": list(witness.evidence),
            }
        )
    status_rank = {value: index for index, value in enumerate(STATUS_ORDER)}
    kind_rank = {value: index for index, value in enumerate(WITNESS_KIND_ORDER)}
    rows.sort(
        key=lambda row: (
            status_rank[row["claim_status"]],
            row["claim_id"],
            kind_rank[row["kind"]],
            row["witness_id"],
        )
    )
    return rows


def _bridge_score(
    *,
    periodic_modulus: int,
    period: int,
    k: int,
    q_is_one: bool,
    visible_prefix: int,
    preperiod_digits: int,
    m: int,
) -> int:
    """
    Score bridge examples for pedagogical signal.

    Rewards:
    - nontrivial period,
    - longer exact carried prefix,
    - small residue k,
    - q=1 bridge structure,
    - shorter block width and smaller preperiod,
    - moderate-size moduli over giant lookalikes when the structure is otherwise the same.
    """
    return (
        (420 if period > 1 else 0)
        + (140 if q_is_one else 0)
        + 28 * visible_prefix
        + 2 * min(period, 90)
        + (25 if k <= 3 else 0)
        + (30 if k == 1 else 0)
        - 22 * max(k - 1, 0)
        - 16 * preperiod_digits
        - 18 * max(m - 1, 0)
        - max(periodic_modulus - 100, 0) // 8
    )


def _frontier_row_within_bound(
    *,
    max_n: int,
    n: int | None = None,
    members: list[int] | tuple[int, ...] | None = None,
) -> bool:
    """Return whether a frontier row stays inside the requested search bound."""
    if n is not None and n > max_n:
        return False
    if members is not None and any(member > max_n for member in members):
        return False
    return True


def build_orbit_carry_frontier_groups(
    *,
    max_n: int = 1200,
    base: int = 10,
    n_blocks: int = 8,
) -> dict[str, list[dict[str, object]]]:
    """
    Group the flagship orbit/carry throughline examples for docs, search, and site use.

    The groups intentionally mix exact support, implemented finite-window carry
    evidence, and open/frontier targets without promoting the global
    factorization claim beyond its current atlas status.
    """
    witness_rows = {row["witness_id"]: row for row in build_claim_witness_rows()}
    carry_cases_by_n = {
        case.n: case for case in canonical_carry_dfa_examples(base=base)
    }
    counterexamples_by_id = {
        record.id: record for record in load_counterexamples()
        if record.claim_id == "carry_dfa_factorization"
    }
    selector_families_by_label = {
        case.label: case for case in canonical_carry_selector_family_studies(base=base)
    }

    orbit_layer_examples: list[dict[str, object]] = []
    for n, label, claim_ids, witness_id, signal in (
        (
            19,
            "Prime remainder orbit",
            ("digit_periodicity",),
            "digit_periodicity_prime19_base10",
            "A compact prime witness where the Euclidean digit step and the closed remainder orbit are both easy to inspect.",
        ),
        (
            97,
            "Clean q-weighted coordinate",
            ("series_q_weighted_identity",),
            "series_q_weighted_identity_prime97_stride2",
            "The raw block layer is literally powers of k in the canonical decimal q = 1 coordinate.",
        ),
        (
            249,
            "Positive-q composite coordinate",
            ("series_q_weighted_identity", "positive_q_good_modes"),
            "series_q_weighted_identity_n249_stride3",
            "The raw coefficient stream stays exact outside the special q = 1 bridge case.",
        ),
        (
            996,
            "Preperiod to periodic core",
            ("preperiod_from_base_factors",),
            "preperiod_from_base_factors_n996_base10",
            "Base-supported factors create only a finite preperiod before the orbit lands on the periodic core.",
        ),
    ):
        if not _frontier_row_within_bound(max_n=max_n, n=n):
            continue
        witness = witness_rows[witness_id]
        orbit_layer_examples.append(
            {
                "group": "orbit_layer_examples",
                "label": label,
                "n": n,
                "members": [n],
                "row_kind": "witness",
                "claim_context": claim_context_for_parameters(claim_ids, base=base, n=n),
                "witness_id": witness_id,
                "summary": witness["summary"],
                "signal": signal,
            }
        )

    carry_layer_examples: list[dict[str, object]] = []
    for n in (21, 97, 996):
        if not _frontier_row_within_bound(max_n=max_n, n=n):
            continue
        case = carry_cases_by_n[n]
        carry_layer_examples.append(
            {
                "group": "carry_layer_examples",
                "label": case.label,
                "n": case.n,
                "members": [case.n],
                "row_kind": "case-study",
                "claim_context": claim_context_for_parameters(
                    ("carry_window_transducer", "carry_dfa_factorization"),
                    base=base,
                    n=case.n,
                ),
                "distinctive_feature": case.distinctive_feature,
                "implemented_boundary": case.factorization_status[0],
                "open_boundary": case.factorization_status[1],
                "summary_lines": list(case.comparison.summary_lines()),
            }
        )

    frontier_targets: list[dict[str, object]] = []
    for witness_id, label, signal in (
        (
            "small_k_visibility_threshold_target_97_249_996",
            "Visibility threshold frontier",
            "The exact incoming-carry layer is closed, but the sharp global visibility threshold is still open.",
        ),
        (
            "carry_dfa_factorization_target_21_97_996",
            "Canonical orbit-plus-carry trio",
            "These canonical denominators separate trivial relabeling, quotient-only prime behavior, and quotient-only composite/preperiod behavior.",
        ),
        (
            "carry_dfa_factorization_target_249_498_996_same_core",
            "Same-core frontier family",
            "The same-core family keeps the exact same-core visibility layer adjacent to the still-open state-level factorization question.",
        ),
    ):
        witness = witness_rows[witness_id]
        params = witness["parameters"]
        members = (
            list(params["N"])
            if isinstance(params.get("N"), list)
            else list(params["members"])
            if isinstance(params.get("members"), list)
            else list(params["family_N"])
            if isinstance(params.get("family_N"), list)
            else [int(params["actual"]), int(params["core"])]
            if "actual" in params and "core" in params
            else []
        )
        n = members[0] if members else None
        if not _frontier_row_within_bound(max_n=max_n, n=n, members=members or None):
            continue
        frontier_targets.append(
            {
                "group": "frontier_targets",
                "label": label,
                "n": n,
                "members": members,
                "row_kind": "open-target",
                "claim_context": claim_context_for_parameters(
                    (str(witness["claim_id"]),),
                    base=base,
                    n=n,
                    actual=int(params["actual"]) if "actual" in params else None,
                    core=int(params["core"]) if "core" in params else None,
                    requested_blocks=int(params["requestedBlocks"]) if "requestedBlocks" in params else None,
                ),
                "witness_id": witness_id,
                "summary": witness["summary"],
                "signal": signal,
            }
        )

    obstruction_families: list[dict[str, object]] = []
    for counterexample_id in (
        "carry_state_relabeling_failure_97",
        "carry_state_relabeling_failure_996",
        "carry_selector_monotonicity_failure_21",
        "carry_selector_core_invariance_failure_996",
    ):
        counterexample = counterexamples_by_id[counterexample_id]
        params = counterexample.parameters
        n = int(params["N"]) if "N" in params else int(params["actual"]) if "actual" in params else None
        members = (
            [int(params["core"]), int(params["actual"])]
            if "core" in params and "actual" in params
            else [n]
            if n is not None
            else None
        )
        if not _frontier_row_within_bound(max_n=max_n, n=n, members=members):
            continue
        obstruction_families.append(
            {
                "group": "obstruction_families",
                "label": counterexample.legacy_claim,
                "n": n,
                "members": members,
                "row_kind": "counterexample",
                "counterexample_id": counterexample.id,
                "observed": counterexample.observed,
                "replacement": counterexample.replacement,
            }
        )

    same_core_family = selector_families_by_label["Same-core relabeling loss"]
    if _frontier_row_within_bound(max_n=max_n, members=same_core_family.members):
        obstruction_families.append(
            {
                "group": "obstruction_families",
                "label": same_core_family.label,
                "n": None,
                "members": list(same_core_family.members),
                "row_kind": "family-study",
                "summary": same_core_family.explanation,
                "signal": "The selector profile is not determined by stripped periodic core alone.",
            }
        )

    return {
        "orbit_layer_examples": orbit_layer_examples,
        "carry_layer_examples": carry_layer_examples,
        "frontier_targets": frontier_targets,
        "obstruction_families": obstruction_families,
    }


def orbit_carry_frontier_rows(
    max_n: int,
    *,
    base: int = 10,
    n_blocks: int = 8,
) -> list[dict[str, object]]:
    """Flatten the grouped orbit/carry frontier surface for CLI export."""
    group_order = (
        "orbit_layer_examples",
        "carry_layer_examples",
        "frontier_targets",
        "obstruction_families",
    )
    grouped = build_orbit_carry_frontier_groups(
        max_n=max_n,
        base=base,
        n_blocks=n_blocks,
    )
    rows: list[dict[str, object]] = []
    for group in group_order:
        rows.extend(grouped[group])
    return rows


def _canonical_state_merging_case_entry(case) -> dict[str, object]:
    profile = case.profile
    comparison = case.comparison
    report = comparison.decision_report
    forward = report.remainder_to_carry_map
    reverse = report.carry_to_remainder_map
    return {
        "label": case.label,
        "n": case.n,
        "base": case.base,
        "explanation": case.explanation,
        "theorem_candidate": case.theorem_candidate,
        "heuristic_note": case.heuristic_note,
        "counterexample_target": case.counterexample_target,
        "primary_vocabulary_id": case.primary_vocabulary_id,
        "summary_lines": list(comparison.summary_lines()),
        "selected_coordinate": {
            "m": comparison.m,
            "B": comparison.B,
            "q": comparison.q,
            "k": comparison.k,
        },
        "factorization_regime": comparison.decision_report.regime,
        "obstruction_class": report.obstruction_class,
        "obstruction_summary": report.obstruction_summary,
        "observed_alignment_bijection": report.observed_alignment_bijection,
        "carry_state_count": report.carry_state_count,
        "remainder_state_count": report.remainder_state_count,
        "carry_class_count": report.carry_class_count,
        "remainder_class_count": report.remainder_class_count,
        "graph_state_gap": report.graph_state_gap,
        "minimized_class_gap": report.minimized_class_gap,
        "profile_class": carry_selector_profile_class(profile),
        "transition_signature": list(profile.transition_signature),
        "forward_profile": forward.export(),
        "reverse_profile": reverse.export(),
        "compression_targets": [
            {
                "target_state": target,
                "source_states": list(sources),
                "preimage_size": len(sources),
            }
            for target, sources in report.compression_targets
        ],
        "forward_preimage_signature": forward.preimage_signature,
        "reverse_preimage_signature": reverse.preimage_signature,
        "forward_ambiguity_signature": forward.ambiguity_signature,
        "reverse_ambiguity_signature": reverse.ambiguity_signature,
        "alignment_rows": list(comparison.alignment_rows),
        "claim_context": {
            **claim_context_for_parameters(
                ("carry_window_transducer", "carry_dfa_factorization"),
                base=comparison.base,
                n=comparison.n,
            ),
        },
    }


def _canonical_state_merging_family_entry(
    family,
    *,
    base: int,
) -> dict[str, object]:
    def _compress_adjacent(labels: list[str]) -> list[str]:
        compressed: list[str] = []
        for label in labels:
            if not compressed or compressed[-1] != label:
                compressed.append(label)
        return compressed

    member_cases = [
        _canonical_state_merging_case_entry(case)
        for case in family.member_cases
    ]
    family_row = {
        "core_n": strip_base_factors(family.members[0], base)[0],
        "base": base,
        "members": [case["n"] for case in member_cases],
        "selected_members": [case["n"] for case in member_cases],
        "selected_regimes": [case["factorization_regime"] for case in member_cases],
        "selected_obstruction_classes": [case["obstruction_class"] for case in member_cases],
        "forward_preimage_signatures": [
            case["forward_preimage_signature"] for case in member_cases
        ],
        "reverse_ambiguity_signatures": [
            case["reverse_ambiguity_signature"] for case in member_cases
        ],
    }
    family_row["has_regime_disagreement"] = len(set(family_row["selected_regimes"])) > 1
    family_row["has_obstruction_class_disagreement"] = (
        len(set(family_row["selected_obstruction_classes"])) > 1
    )
    family_row["has_forward_preimage_disagreement"] = (
        len(set(family_row["forward_preimage_signatures"])) > 1
    )
    family_row["has_reverse_ambiguity_disagreement"] = (
        len(set(family_row["reverse_ambiguity_signatures"])) > 1
    )
    class_set = set(family_row["selected_obstruction_classes"])
    family_row["has_hidden_graph_obstruction_member"] = "hidden_graph_obstruction" in class_set
    family_row["has_visible_preimage_compression_member"] = "visible_preimage_compression" in class_set
    family_row["crosses_relabeling_hidden_visible_classes"] = {
        "state_relabeling",
        "hidden_graph_obstruction",
        "visible_preimage_compression",
    }.issubset(class_set)
    family_row["has_state_merging_disagreement"] = (
        family_row["has_regime_disagreement"]
        or family_row["has_obstruction_class_disagreement"]
        or family_row["has_forward_preimage_disagreement"]
        or family_row["has_reverse_ambiguity_disagreement"]
    )
    family_row["relabeling_members"] = [
        member
        for member, obstruction_class in zip(
            family_row["members"],
            family_row["selected_obstruction_classes"],
        )
        if obstruction_class == "state_relabeling"
    ]
    family_row["hidden_members"] = [
        member
        for member, obstruction_class in zip(
            family_row["members"],
            family_row["selected_obstruction_classes"],
        )
        if obstruction_class == "hidden_graph_obstruction"
    ]
    family_row["visible_members"] = [
        member
        for member, obstruction_class in zip(
            family_row["members"],
            family_row["selected_obstruction_classes"],
        )
        if obstruction_class == "visible_preimage_compression"
    ]
    family_row["compressed_class_path"] = _compress_adjacent(
        list(family_row["selected_obstruction_classes"])
    )
    family_row["compressed_obstruction_path"] = _compress_adjacent(
        [
            obstruction_class
            for obstruction_class in family_row["selected_obstruction_classes"]
            if obstruction_class in {"hidden_graph_obstruction", "visible_preimage_compression"}
        ]
    )
    family_row["first_relabeling_member"] = (
        family_row["relabeling_members"][0] if family_row["relabeling_members"] else None
    )
    family_row["first_non_relabeling_member"] = next(
        (
            member
            for member, obstruction_class in zip(
                family_row["members"],
                family_row["selected_obstruction_classes"],
            )
            if obstruction_class != "state_relabeling"
        ),
        None,
    )
    family_row["first_hidden_member"] = (
        family_row["hidden_members"][0] if family_row["hidden_members"] else None
    )
    family_row["first_visible_member"] = (
        family_row["visible_members"][0] if family_row["visible_members"] else None
    )
    family_row["has_visible_after_hidden"] = bool(
        family_row["first_hidden_member"] is not None
        and any(member > family_row["first_hidden_member"] for member in family_row["visible_members"])
    )
    family_row["has_rehidden_after_visible"] = bool(
        family_row["first_visible_member"] is not None
        and any(member > family_row["first_visible_member"] for member in family_row["hidden_members"])
    )
    family_row["hidden_visible_switch_count"] = max(
        len(family_row["compressed_obstruction_path"]) - 1,
        0,
    )
    family_row["has_nonmonotone_hidden_visible_switching"] = (
        family_row["hidden_visible_switch_count"] >= 2
    )
    class_path_text = " -> ".join(family_row["compressed_class_path"]) or "none"
    if family_row["has_nonmonotone_hidden_visible_switching"]:
        family_row["phase_summary"] = (
            f"same-core path {class_path_text} with "
            f"{family_row['hidden_visible_switch_count']} hidden/visible switches"
        )
    elif family_row["has_rehidden_after_visible"]:
        family_row["phase_summary"] = (
            f"same-core path {class_path_text} re-hides after visible compression appears"
        )
    elif family_row["has_visible_after_hidden"]:
        family_row["phase_summary"] = (
            f"same-core path {class_path_text} becomes visible after an earlier hidden phase"
        )
    elif family_row["first_visible_member"] is not None:
        family_row["phase_summary"] = (
            f"same-core path {class_path_text} reaches visible compression without later re-hiding"
        )
    elif family_row["first_hidden_member"] is not None:
        family_row["phase_summary"] = (
            f"same-core path {class_path_text} stays hidden once the family leaves relabeling"
        )
    else:
        family_row["phase_summary"] = f"same-core path {class_path_text}"
    family_row.update(
        claim_context_for_parameters(
            ("carry_window_transducer", "carry_dfa_factorization"),
            base=base,
            actual=max(family.members),
            core=int(family_row["core_n"]),
            requested_blocks=8,
        )
    )
    return {
        "label": family.label,
        "members": list(family.members),
        "explanation": family.explanation,
        "theorem_candidate": family.theorem_candidate,
        "heuristic_note": family.heuristic_note,
        "counterexample_target": family.counterexample_target,
        "primary_vocabulary_id": family.primary_vocabulary_id,
        "summary_lines": list(family.summary_lines),
        "family_row": family_row,
        "member_cases": member_cases,
    }


def _composite_signal_score(
    *,
    n: int,
    stripped_modulus: int,
    global_order: int,
    preperiod_digits: int,
    component_count: int,
    factors: dict[int, int],
    best_k: int,
    best_q: int,
) -> int:
    """
    Score composite examples for explanatory value rather than raw size.

    Rewards:
    - small residue coordinates,
    - explicit CRT splitting,
    - moderate global periods that are still readable,
    - preperiod/composite structure that differs from the stripped periodic core.
    """
    repeated_prime_power = any(exponent > 1 for exponent in factors.values())
    if best_k == 1:
        readability_bonus = 220
    elif best_k <= 4:
        readability_bonus = 170
    elif best_k <= 6:
        readability_bonus = 110
    else:
        readability_bonus = max(0, 80 - 10 * (best_k - 6))

    if 20 <= global_order <= 60:
        period_bonus = 100
    elif 6 <= global_order <= 120:
        period_bonus = 70
    else:
        period_bonus = 35

    if best_k == 1:
        quotient_bonus = 0
    elif best_q <= 9:
        quotient_bonus = 180
    elif best_q <= 25:
        quotient_bonus = 120
    elif best_q <= 100:
        quotient_bonus = 40
    else:
        quotient_bonus = 0

    direct_core_bonus = 0
    if (
        n == stripped_modulus
        and best_k <= 4
        and best_q <= 9
        and 20 <= global_order <= 60
    ):
        direct_core_bonus = 220

    return (
        140 * min(component_count, 2)
        + (140 if stripped_modulus != n else 0)
        + (60 if preperiod_digits > 0 else 0)
        + (80 if repeated_prime_power else 0)
        + readability_bonus
        + quotient_bonus
        + direct_core_bonus
        + period_bonus
        - 3 * preperiod_digits
        - n // 20
    )


def _build_bridge_candidate(
    n: int,
    *,
    base: int = 10,
    kmax: int = 5,
    mmax: int = 12,
    n_blocks: int = 12,
) -> BridgeCandidate | None:
    periodic_modulus, _ = strip_base_factors(n, base)
    if periodic_modulus == 1 or gcd(periodic_modulus, base) != 1:
        return None

    modes = find_good_modes(periodic_modulus, base=base, kmax=kmax, mmax=mmax, sort_by="k")
    if not modes:
        return None

    m, k, q = modes[0]
    B = base ** m
    period = multiplicative_order(B, periodic_modulus) or 0
    comparison = skeleton_vs_actual(n, base=base, n_blocks=n_blocks, prefer_m=m)
    k = comparison["k"]
    q = comparison["q"]
    if k > kmax:
        return None
    visible_prefix = _leading_match_count(comparison["carried"], comparison["actual"])
    profile = crt_period_profile(n, base)
    q_is_one = (q == 1)
    explanation_bits = [
        f"small-residue block coordinate with remainder k = {k}",
        f"quotient q = {q}",
        f"raw coefficients qk^j visible for {visible_prefix} block(s)",
    ]
    if q_is_one:
        explanation_bits.insert(1, "raw coefficients qk^j reduce to literal powers of k")
    if profile.preperiod_digits:
        explanation_bits.append(f"preperiod length {profile.preperiod_digits} digit(s)")
    explanation_bits.append(f"period {period} block(s)")

    return BridgeCandidate(
        n=n,
        periodic_modulus=periodic_modulus,
        base=base,
        m=m,
        B=B,
        k=k,
        q=q,
        period=period,
        preperiod_digits=profile.preperiod_digits,
        visible_prefix=visible_prefix,
        q_is_one=q_is_one,
        is_trivial_period=(period <= 1),
        score=_bridge_score(
            periodic_modulus=periodic_modulus,
            period=period,
            k=k,
            q_is_one=q_is_one,
            visible_prefix=visible_prefix,
            preperiod_digits=profile.preperiod_digits,
            m=m,
        ),
        primary_vocabulary_id="good_mode",
        explanation="; ".join(explanation_bits),
    )


@dataclass(frozen=True)
class LegacyCounterexample:
    p: int
    base: int
    reptend_type: str
    qr_strides: tuple[int, ...]
    legacy_claim: str


def rank_bridge_candidates(
    max_n: int,
    *,
    base: int = 10,
    kmax: int = 5,
    mmax: int = 12,
    top: int | None = 20,
    n_blocks: int = 12,
    require_nontrivial: bool = True,
    require_q_one: bool | None = None,
    min_periodic_modulus: int = DEFAULT_MIN_SIGNAL_MODULUS,
    dedupe_periodic_modulus: bool = True,
) -> list[BridgeCandidate]:
    """
    Rank moduli by how legible their early q-weighted skeleton is.

    Defaults favor high-signal examples:
    - nontrivial period only,
    - periodic modulus at least 19,
    - separate `require_q_one=True` when the pure bridge case is desired.
    """
    candidates: list[BridgeCandidate] = []
    for n in range(2, max_n + 1):
        candidate = _build_bridge_candidate(
            n,
            base=base,
            kmax=kmax,
            mmax=mmax,
            n_blocks=n_blocks,
        )
        if candidate is None:
            continue
        if candidate.periodic_modulus < min_periodic_modulus:
            continue
        if require_nontrivial and candidate.is_trivial_period:
            continue
        if require_q_one is not None and candidate.q_is_one != require_q_one:
            continue
        candidates.append(candidate)

    candidates.sort(
        key=lambda entry: (
            -entry.score,
            entry.k,
            entry.preperiod_digits,
            entry.m,
            entry.n,
        )
    )
    if dedupe_periodic_modulus:
        deduped: list[BridgeCandidate] = []
        seen_periodic_moduli: set[int] = set()
        for candidate in candidates:
            if candidate.periodic_modulus in seen_periodic_moduli:
                continue
            seen_periodic_moduli.add(candidate.periodic_modulus)
            deduped.append(candidate)
        candidates = deduped
    return candidates if top is None else candidates[:top]


def rank_q_one_bridges(
    max_n: int,
    *,
    base: int = 10,
    kmax: int = 5,
    mmax: int = 12,
    top: int | None = 20,
    n_blocks: int = 12,
    min_periodic_modulus: int = DEFAULT_MIN_SIGNAL_MODULUS,
) -> list[BridgeCandidate]:
    """Rank q = 1 bridge cases with nontrivial period by default."""
    return rank_bridge_candidates(
        max_n,
        base=base,
        kmax=kmax,
        mmax=mmax,
        top=top,
        n_blocks=n_blocks,
        require_nontrivial=True,
        require_q_one=True,
        min_periodic_modulus=min_periodic_modulus,
        dedupe_periodic_modulus=True,
    )


def rank_prime_qr_examples(
    max_p: int,
    *,
    base: int = 10,
    top: int | None = 20,
    min_half: int = 9,
) -> list[PrimeQRExample]:
    """
    Rank prime examples where the base has QR-generating strides.

    The ranking favors examples with:
    - a small QR-generating stride,
    - a small generator residue k = base^m mod p,
    - a reasonably large QR subgroup.
    """
    records: list[PrimeQRExample] = []
    for p in sieve_primes(max_p):
        if p <= 2 or p == base:
            continue
        analysis = analyze_prime(p, base)
        if analysis.stride_count == 0 or analysis.half < min_half:
            continue

        preferred_stride = min(
            analysis.qr_strides,
            key=lambda stride: (stride, pow(base, stride, p)),
        )
        preferred_k = pow(base, preferred_stride, p)
        score = (
            max(0, 180 - 4 * preferred_stride)
            + 2 * min(analysis.stride_count, 30)
            + min(analysis.half, 30)
            - 3 * max(preferred_k - 1, 0)
        )
        if preferred_stride == 1:
            score += 20
        elif preferred_stride == 2:
            score += 60
        if preferred_k <= 5:
            score += 35

        explanation = (
            f"generator of the QR subgroup at stride {preferred_stride}; "
            f"remainder k = {preferred_k}; reptend type {analysis.reptend_type}; "
            f"{analysis.stride_count} QR-generating stride(s)"
        )

        records.append(
            PrimeQRExample(
                p=p,
                base=base,
                reptend_type=analysis.reptend_type,
                preferred_stride=preferred_stride,
                preferred_k=preferred_k,
                stride_count=analysis.stride_count,
                score=score,
                primary_vocabulary_id="qr_generator",
                explanation=explanation,
            )
        )

    records.sort(
        key=lambda entry: (
            -entry.score,
            entry.preferred_k,
            entry.preferred_stride,
            entry.p,
        )
    )
    return records if top is None else records[:top]


def find_legacy_counterexamples(max_p: int, bases: list[int]) -> list[LegacyCounterexample]:
    """
    Search for explicit counterexamples to the old stride prose.
    """
    records: list[LegacyCounterexample] = []
    for p in sieve_primes(max_p):
        if p <= 2:
            continue
        for base in bases:
            if base == p:
                continue
            classification = reptend_type(p, base)
            qr_strides = tuple(find_qr_strides(p, base))
            if classification == "full":
                expected = tuple(range(2, p - 1, 2))
                if qr_strides != expected:
                    records.append(
                        LegacyCounterexample(
                            p=p,
                            base=base,
                            reptend_type=classification,
                            qr_strides=qr_strides,
                            legacy_claim="full reptend => all even strides",
                        )
                    )
            elif classification == "half":
                reptend_len = multiplicative_order(base, p) or 0
                expected = tuple(range(1, reptend_len + 1))
                if qr_strides != expected:
                    records.append(
                        LegacyCounterexample(
                            p=p,
                            base=base,
                            reptend_type=classification,
                            qr_strides=qr_strides,
                            legacy_claim="half reptend => all consecutive strides",
                        )
                    )
    return records


def rank_composite_highlights(
    max_n: int,
    *,
    base: int = 10,
    top: int | None = 20,
    min_n: int = 21,
    dedupe_periodic_core: bool = True,
) -> list[CompositeHighlight]:
    """
    Rank composite examples that best exhibit CRT and preperiod structure.
    """
    highlights: list[CompositeHighlight] = []
    for n in range(2, max_n + 1):
        if n < min_n:
            continue
        factors = factorize(n)
        if not factors:
            continue
        is_composite = sum(factors.values()) > 1
        if not is_composite:
            continue

        profile = crt_period_profile(n, base)
        if profile.stripped_modulus == 1:
            continue

        modes = find_good_modes(profile.stripped_modulus, base=base, kmax=12, mmax=12, sort_by="k")
        best_mode = modes[0] if modes else None
        if best_mode is None:
            continue
        if best_mode[1] > 6:
            continue
        best_m, best_k, best_q = best_mode
        component_count = len(profile.components)
        score = _composite_signal_score(
            n=n,
            stripped_modulus=profile.stripped_modulus,
            global_order=profile.global_order,
            preperiod_digits=profile.preperiod_digits,
            component_count=component_count,
            factors=factors,
            best_k=best_k,
            best_q=best_q,
        )

        component_summary = ", ".join(
            f"{component.modulus} (ord {component.local_order})"
            for component in profile.components
        )
        explanation = (
            f"remainder orbit under multiplication by the base splits by CRT across {component_summary}; "
            f"global period {profile.global_order}; "
            f"preperiod {profile.preperiod_digits} digit(s)"
        )
        explanation += f"; small-residue block coordinate m = {best_m} gives q = {best_q}, k = {best_k}"

        highlights.append(
            CompositeHighlight(
                n=n,
                stripped_modulus=profile.stripped_modulus,
                base=base,
                global_order=profile.global_order,
                preperiod_digits=profile.preperiod_digits,
                component_count=component_count,
                best_m=best_m,
                best_k=best_k,
                best_q=best_q,
                score=score,
                primary_vocabulary_id="remainder_orbit",
                explanation=explanation,
            )
        )

    highlights.sort(
        key=lambda entry: (
            -entry.score,
            entry.preperiod_digits,
            entry.n,
        )
    )
    if dedupe_periodic_core:
        deduped: list[CompositeHighlight] = []
        seen_keys: set[tuple[int, bool]] = set()
        for highlight in highlights:
            key = (highlight.stripped_modulus, highlight.preperiod_digits > 0)
            if key in seen_keys:
                continue
            seen_keys.add(key)
            deduped.append(highlight)
        highlights = deduped
    return highlights if top is None else highlights[:top]


def composite_profile_rows(max_n: int, *, base: int = 10) -> list[dict[str, object]]:
    """
    Build a flat dataset of composite/CRT profiles.
    """
    rows: list[dict[str, object]] = []
    for n in range(2, max_n + 1):
        factors = []
        remaining = n
        divisor = 2
        while divisor * divisor <= remaining:
            exponent = 0
            while remaining % divisor == 0:
                remaining //= divisor
                exponent += 1
            if exponent:
                factors.append((divisor, exponent))
            divisor += 1 if divisor == 2 else 2
        if remaining > 1:
            factors.append((remaining, 1))
        if len(factors) < 2 and not any(exponent > 1 for _, exponent in factors):
            continue

        profile = crt_period_profile(n, base)
        if profile.stripped_modulus == 1:
            continue
        rows.append(
            {
                "n": n,
                "stripped_modulus": profile.stripped_modulus,
                "preperiod_digits": profile.preperiod_digits,
                "global_order": profile.global_order,
                "carmichael_value": profile.carmichael_value,
                "components": ";".join(
                    f"{component.modulus}:ord={component.local_order}:lambda={component.local_lambda}"
                    for component in profile.components
                ),
            }
        )
    return rows


def build_example_atlas(
    *,
    max_n: int = 500,
    max_p: int = 500,
    base: int = 10,
    top: int = 8,
) -> dict[str, object]:
    """
    Build the published example atlas for docs, the site, and note generation.

    This is the stable publication layer. Exploratory search commands may emit
    additional CSV rows, but the site and docs consume this schema-versioned
    atlas with deterministic manifest/provenance metadata.
    """
    q_one_bridges = rank_q_one_bridges(max_n, base=base, top=top)
    nontrivial_bridges = rank_bridge_candidates(max_n, base=base, top=top)
    composite_pool = rank_composite_highlights(max_n, base=base, top=None)
    composite_by_n = {candidate.n: candidate for candidate in composite_pool}
    composite_highlights = [
        composite_by_n[n]
        for n in (21, 27, 249, 996)
        if n in composite_by_n
    ]
    composite_highlights.extend(
        candidate
        for candidate in composite_pool
        if candidate.n not in {highlight.n for highlight in composite_highlights}
    )
    composite_highlights = composite_highlights[:top]
    prime_qr = rank_prime_qr_examples(max_p, base=base, top=top)
    composite_case_studies = canonical_composite_case_studies(base=base)
    composite_family_studies = canonical_composite_family_case_studies(base=base)
    carry_cases = canonical_carry_dfa_examples(base=base)
    carry_selector_cases = canonical_carry_selector_case_studies(base=base)
    carry_selector_families = canonical_carry_selector_family_studies(base=base)
    carry_selector_research = carry_selector_research_rows()
    state_merging_cases = canonical_state_merging_case_studies(base=base)
    state_merging_families = canonical_state_merging_family_studies(base=base)
    state_merging_selected_rows = state_merging_rows(max_n, base=base, n_blocks=8, max_m=8)
    quotient_obstruction_census = quotient_obstruction_census_from_rows(
        state_merging_selected_rows,
        base=base,
        max_n=max_n,
        n_blocks=8,
    )
    state_merging_case_entries = [
        _canonical_state_merging_case_entry(case)
        for case in state_merging_cases
    ]
    state_merging_family_entries = [
        _canonical_state_merging_family_entry(
            family,
            base=base,
        )
        for family in state_merging_families
    ]
    state_merging_research_rows = [
        *state_merging_case_entries,
        *[
            member
            for family in state_merging_family_entries
            for member in family["member_cases"]
            if member["n"] not in {entry["n"] for entry in state_merging_case_entries}
        ],
    ]
    state_merging_research_rows.sort(key=lambda row: int(row["n"]))
    quotient_obstruction_family_research = quotient_obstruction_family_rows(
        max_n,
        base=base,
        n_blocks=8,
        max_m=8,
    )
    visibility_cases = canonical_visibility_case_studies(base=base)
    visibility_families = canonical_visibility_family_studies(base=base)
    claim_witness_rows = build_claim_witness_rows()
    frontier_groups = build_orbit_carry_frontier_groups(max_n=max_n, base=base, n_blocks=8)
    throughlines = load_throughlines()

    canonical_examples = [
        CanonicalExample(
            label="Constant-coefficient bridge",
            n=37,
            category="canonical",
            primary_vocabulary_id="good_mode",
            explanation="small-residue block coordinate with remainder k = 1 and quotient q = 27, so the raw coefficients qk^j are the constant sequence 27",
        ),
        CanonicalExample(
            label="Prime q=1 bridge",
            n=97,
            category="canonical",
            primary_vocabulary_id="good_mode",
            explanation="small-residue block coordinate with q = 1 and remainder k = 3, so the raw coefficients qk^j reduce to literal powers of k and the period is nontrivial",
        ),
        CanonicalExample(
            label="Composite periodic core",
            n=249,
            category="canonical",
            primary_vocabulary_id="remainder_orbit",
            explanation="remainder orbit under multiplication by the base splits by CRT across 3 and 83 while still admitting a readable small-residue block coordinate",
        ),
        CanonicalExample(
            label="Composite with preperiod",
            n=996,
            category="canonical",
            primary_vocabulary_id="remainder_orbit",
            explanation="strip base factors to the purely periodic modulus 249; the example shows both preperiod behavior and a q = 1 bridge-style coordinate",
        ),
        CanonicalExample(
            label="Prime QR counterexample",
            n=19,
            category="canonical",
            primary_vocabulary_id="qr_generator",
            explanation="generator of the QR subgroup appears at stride 2, but the exact QR-generating strides are not all even, making this a useful high-signal counterexample",
        ),
    ]

    payload = {
        "schema_version": PUBLISHED_ATLAS_SCHEMA_VERSION,
        "dataset_kind": "published_example_atlas",
        "manifest": {
            "publication_layer": "published",
            "build_command": f"search-reptends published-atlas --max {max_n} --top {top} --output data/example_atlas.json",
            "builder": "bridge_reptends.search:build_example_atlas",
            "normalization": "UTF-8 JSON, indent=2, sort_keys=True, trailing newline",
            "source_files": [
                "bridge_reptends/search.py",
                "bridge_reptends/composite.py",
                "bridge_reptends/transducer.py",
                "bridge_reptends/visibility.py",
                "data/claim_registry.json",
                "data/lean_worked_examples.json",
                "data/theorem_witnesses.json",
                "data/throughlines.json",
                "data/vocabulary.json",
            ],
        },
        "provenance": {
            "base": base,
            "max_n": max_n,
            "max_p": max_p,
            "top": top,
            "standard_label_first": True,
            "cross_base_selector_bases": [7, 10, 12],
        },
        "metadata": {
            "base": base,
            "max_n": max_n,
            "max_p": max_p,
            "top": top,
            "standard_label_first": True,
            "publication_layer": "published",
        },
        "leaderboards": {
            "bridge_q1": [asdict(candidate) for candidate in q_one_bridges],
            "bridge_nontrivial": [asdict(candidate) for candidate in nontrivial_bridges],
            "composite_crt": [asdict(candidate) for candidate in composite_highlights],
            "prime_qr": [asdict(candidate) for candidate in prime_qr],
        },
        "canonical_examples": [asdict(example) for example in canonical_examples],
        "throughlines": {
            "featured_ids": [record.id for record in throughlines],
            "rows": [
                {
                    "id": record.id,
                    "kind": record.kind,
                    "title": record.title,
                    "headline": record.headline,
                    "status_note": record.status_note,
                    "claim_ids": list(record.claim_ids),
                    "open_claim_ids": list(record.open_claim_ids),
                    "witness_ids": list(record.witness_ids),
                    "counterexample_ids": list(record.counterexample_ids),
                    "featured_searches": [
                        {
                            "id": entry.id,
                            "label": entry.label,
                            "summary": entry.summary,
                            "command": entry.command,
                            "atlas_section_id": entry.atlas_section_id,
                        }
                        for entry in record.featured_searches
                    ],
                    "ladder": [
                        {
                            "id": entry.id,
                            "label": entry.label,
                            "claim_ids": list(entry.claim_ids),
                            "witness_ids": list(entry.witness_ids),
                            "counterexample_ids": list(entry.counterexample_ids),
                            "summary": entry.summary,
                        }
                        for entry in record.ladder
                    ],
                }
                for record in throughlines
            ],
        },
        "claim_witnesses": {
            "featured_ids": [
                "series_q_weighted_identity_prime97_stride2",
                "same_core_threshold_shift_interval_996_over_249",
                "small_k_visibility_threshold_target_97_249_996",
                "carry_dfa_factorization_target_21_97_996",
            ],
            "rows": claim_witness_rows,
        },
        "case_studies": {
            "orbit_carry_frontier": frontier_groups,
            "composite_examples": [asdict(case) for case in composite_case_studies],
            "composite_families": [asdict(case) for case in composite_family_studies],
            "carry_dfa": [
                {
                    "label": case.label,
                    "n": case.n,
                    "distinctive_feature": case.distinctive_feature,
                    "factorization_status": {
                        "implemented": case.factorization_status[0],
                        "open_boundary": case.factorization_status[1],
                    },
                    "claim_context": claim_context_for_parameters(
                        ("carry_window_transducer", "carry_dfa_factorization"),
                        base=base,
                        n=case.n,
                    ),
                    "summary_lines": list(case.comparison.summary_lines()),
                }
                for case in carry_cases
            ],
            "carry_selector": [
                {
                    "label": case.label,
                    "n": case.n,
                    "base": case.base,
                    "explanation": case.explanation,
                    "theorem_candidate": case.theorem_candidate,
                    "heuristic_note": case.heuristic_note,
                    "counterexample_target": case.counterexample_target,
                    "primary_vocabulary_id": case.primary_vocabulary_id,
                    "summary_lines": list(case.profile.selector_summary_lines),
                    "profile": {
                        "selected_m": case.profile.selected_m,
                        "profile_class": carry_selector_profile_class(case.profile),
                        "transition_signature": list(case.profile.transition_signature),
                        "relabeling_modes": list(case.profile.relabeling_modes),
                        "quotient_modes": list(case.profile.quotient_modes),
                        "finite_word_only_modes": list(case.profile.finite_word_only_modes),
                        "has_isolated_relabeling_window": case.profile.has_isolated_relabeling_window,
                        "selected_k": case.profile.selected_step.k if case.profile.selected_step else None,
                        "selected_q": case.profile.selected_step.q if case.profile.selected_step else None,
                    },
                }
                for case in carry_selector_cases
            ],
            "carry_selector_families": [
                asdict(case)
                for case in carry_selector_families
            ],
            "state_merging": [
                entry
                for entry in state_merging_case_entries
            ],
            "state_merging_families": [
                entry
                for entry in state_merging_family_entries
            ],
            "visibility": [
                {
                    "label": case.label,
                    "family_id": case.family_id,
                    "n": case.n,
                    "explanation": case.explanation,
                    "theorem_candidate": case.theorem_candidate,
                    "heuristic_note": case.heuristic_note,
                    "counterexample_target": case.counterexample_target,
                    "claim_context": claim_context_for_parameters(
                        (
                            "incoming_carry_position_formula",
                            "small_k_visibility_threshold",
                            "small_k_visibility_heuristic",
                        ),
                        base=base,
                        n=case.n,
                        requested_blocks=case.profile.requested_blocks,
                    ),
                    "summary_lines": list(case.profile.summary_lines()),
                    "profile": {
                        "periodic_modulus": case.profile.periodic_modulus,
                        "base": case.profile.base,
                        "m": case.profile.m,
                        "B": case.profile.B,
                        "q": case.profile.q,
                        "k": case.profile.k,
                        "period": case.profile.period,
                        "preperiod_digits": case.profile.preperiod_digits,
                        "requested_blocks": case.profile.requested_blocks,
                        "lookahead_lower_bound": case.profile.lookahead_lower_bound,
                        "lookahead_blocks": case.profile.lookahead_blocks,
                        "certified_lookahead_blocks": case.profile.certified_lookahead_blocks,
                        "raw_prefix_agreement_length": case.profile.raw_prefix_agreement_length,
                        "first_local_overflow_position": case.profile.first_local_overflow_position,
                        "first_incoming_carry_position": case.profile.first_incoming_carry_position,
                        "first_mismatch_position": case.profile.first_mismatch_position,
                        "exact_gap_numerator": case.profile.exact_gap_numerator,
                        "mismatch_regime": case.profile.mismatch_regime,
                        "agreement_identity_holds": case.profile.agreement_identity_holds,
                        "incoming_carry_formula_holds": case.profile.incoming_carry_formula_holds,
                        "lookahead_certificate_matches": case.profile.lookahead_certificate_matches,
                    },
                }
                for case in visibility_cases
            ],
            "visibility_families": [
                asdict(case)
                for case in visibility_families
            ],
        },
        "research_layers": {
            "carry_selector": {
                "publication_status": "published_research_layer",
                "decision": (
                    "Selector profiles are now part of the published atlas as a research layer: "
                    "non-k = 1 relabeling windows and same-core disagreement recur in bounded sweeps "
                    "across bases 7, 10, and 12."
                ),
                "classification_bound": 120,
                "bases": carry_selector_research,
            },
            "state_merging": {
                "publication_status": "published_research_layer",
                "decision": (
                    "The preimage-fiber profile (state-merging atlas) now makes finite-window "
                    "collapse/compression visible directly on the selected Track 17 coordinate, "
                    "and the quotient-only cases now split into visible preimage compression "
                    "versus hidden graph obstruction without promoting `carry_dfa_factorization` "
                    "beyond its current open status."
                ),
                "base": base,
                "classification_bound": max_n,
                "quotient_candidate_only_count": quotient_obstruction_census["quotient_candidate_only_count"],
                "visible_preimage_compression_count": quotient_obstruction_census["visible_preimage_compression_count"],
                "hidden_graph_obstruction_count": quotient_obstruction_census["hidden_graph_obstruction_count"],
                "representative_visible_ns": quotient_obstruction_census["representative_visible_ns"],
                "representative_hidden_ns": quotient_obstruction_census["representative_hidden_ns"],
                "summary_lines": quotient_obstruction_census["summary_lines"],
                "rows": [
                    row
                    for row in state_merging_research_rows
                    if int(row["n"]) in {17, 21, 34, 68, 85, 89, 97, 249, 498, 996}
                ],
            },
            "state_merging_same_core": {
                "publication_status": "published_research_layer",
                "decision": (
                    "Same-core state-merging families separate stripped-core orbit data from the "
                    "actual finite-window compression profile, and now keep the relabeling / hidden "
                    "/ visible obstruction split, including non-monotone re-hiding after visibility, "
                    "explicit beneath the open "
                    "`carry_dfa_factorization` boundary."
                ),
                "base": base,
                "rows": [
                    row
                    for row in quotient_obstruction_family_research
                    if int(row["core_n"]) in {17, 249}
                ],
            }
        },
    }
    return json.loads(json.dumps(payload, sort_keys=True))


def _write_csv(filename: str | Path, rows: list[dict[str, object]]) -> None:
    if not rows:
        return
    fieldnames: list[str] = []
    for row in rows:
        for field in row.keys():
            if field not in fieldnames:
                fieldnames.append(field)
    with Path(filename).open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def _write_json(filename: str | Path, payload: dict[str, object]) -> None:
    Path(filename).write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def main() -> None:
    """CLI entry point for dataset generation."""
    import argparse

    parser = argparse.ArgumentParser(
        description="Search and export published reptend datasets with standard-label-first help text"
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    bridge_parser = subparsers.add_parser(
        "small-residue-coordinates",
        aliases=["bridges"],
        help="Rank small-residue block coordinates (legacy alias: bridges)",
    )
    bridge_parser.add_argument("--max", type=int, default=500)
    bridge_parser.add_argument("--base", type=int, default=10)
    bridge_parser.add_argument("--kmax", type=int, default=5)
    bridge_parser.add_argument("--mmax", type=int, default=12)
    bridge_parser.add_argument("--top", type=int, default=20)
    bridge_parser.add_argument("--output", type=str, default=None)
    bridge_parser.add_argument("--include-trivial", action="store_true", help="Include period-1 bridge cases")

    q1_parser = subparsers.add_parser(
        "small-residue-coordinates-q1",
        aliases=["bridges-q1"],
        help="Rank q = 1 small-residue block coordinates (legacy alias: bridges-q1)",
    )
    q1_parser.add_argument("--max", type=int, default=500)
    q1_parser.add_argument("--base", type=int, default=10)
    q1_parser.add_argument("--kmax", type=int, default=5)
    q1_parser.add_argument("--mmax", type=int, default=12)
    q1_parser.add_argument("--top", type=int, default=20)
    q1_parser.add_argument("--output", type=str, default=None)

    legacy_parser = subparsers.add_parser("legacy-counterexamples", help="Find counterexamples to old stride heuristics")
    legacy_parser.add_argument("--max", type=int, default=500)
    legacy_parser.add_argument("--bases", type=str, default="2,7,10,12")
    legacy_parser.add_argument("--output", type=str, default=None)

    composite_parser = subparsers.add_parser(
        "composite-profiles",
        aliases=["composites"],
        help="Export composite CRT profiles (legacy alias: composites)",
    )
    composite_parser.add_argument("--max", type=int, default=500)
    composite_parser.add_argument("--base", type=int, default=10)
    composite_parser.add_argument("--output", type=str, default=None)

    visibility_parser = subparsers.add_parser(
        "visibility-profiles",
        aliases=["visibility"],
        help="Export exact carried-prefix visibility observables (legacy alias: visibility)",
    )
    visibility_parser.add_argument("--max", type=int, default=500)
    visibility_parser.add_argument("--base", type=int, default=10)
    visibility_parser.add_argument("--blocks", type=int, default=8)
    visibility_parser.add_argument("--output", type=str, default=None)

    visibility_counterexample_parser = subparsers.add_parser(
        "visibility-counterexamples",
        help="Export cases where incoming carry appears before the local overflow boundary",
    )
    visibility_counterexample_parser.add_argument("--max", type=int, default=500)
    visibility_counterexample_parser.add_argument("--base", type=int, default=10)
    visibility_counterexample_parser.add_argument("--blocks", type=int, default=8)
    visibility_counterexample_parser.add_argument("--output", type=str, default=None)

    same_core_parser = subparsers.add_parser(
        "same-core-visibility",
        help="Export same-core family comparisons for interval and exact shift laws",
    )
    same_core_parser.add_argument("--max", type=int, default=500)
    same_core_parser.add_argument("--base", type=int, default=10)
    same_core_parser.add_argument("--blocks", type=int, default=8)
    same_core_parser.add_argument("--output", type=str, default=None)

    factorization_parser = subparsers.add_parser(
        "carry-factorization",
        help="Export bounded Track 17 carry/DFA factorization regimes and relabeling counterexamples",
    )
    factorization_parser.add_argument("--max", type=int, default=500)
    factorization_parser.add_argument("--base", type=int, default=10)
    factorization_parser.add_argument("--blocks", type=int, default=8)
    factorization_parser.add_argument("--output", type=str, default=None)

    factorization_selector_parser = subparsers.add_parser(
        "carry-factorization-selector",
        help="Export Track 17 selector profiles across candidate block widths",
    )
    factorization_selector_parser.add_argument("--max", type=int, default=500)
    factorization_selector_parser.add_argument("--base", type=int, default=10)
    factorization_selector_parser.add_argument("--blocks", type=int, default=8)
    factorization_selector_parser.add_argument("--output", type=str, default=None)

    factorization_non_k_one_parser = subparsers.add_parser(
        "carry-selector-non-k1",
        help="Export selected non-k = 1 state-relabeling windows",
    )
    factorization_non_k_one_parser.add_argument("--max", type=int, default=500)
    factorization_non_k_one_parser.add_argument("--base", type=int, default=10)
    factorization_non_k_one_parser.add_argument("--blocks", type=int, default=8)
    factorization_non_k_one_parser.add_argument("--output", type=str, default=None)

    factorization_same_core_parser = subparsers.add_parser(
        "carry-selector-same-core",
        help="Export grouped same-core selector-family disagreements",
    )
    factorization_same_core_parser.add_argument("--max", type=int, default=500)
    factorization_same_core_parser.add_argument("--base", type=int, default=10)
    factorization_same_core_parser.add_argument("--blocks", type=int, default=8)
    factorization_same_core_parser.add_argument("--output", type=str, default=None)

    factorization_research_parser = subparsers.add_parser(
        "carry-selector-research",
        help="Export bounded cross-base selector-profile summaries for the published research layer",
    )
    factorization_research_parser.add_argument("--max", type=int, default=120)
    factorization_research_parser.add_argument("--bases", type=str, default="7,10,12")
    factorization_research_parser.add_argument("--blocks", type=int, default=8)
    factorization_research_parser.add_argument("--output", type=str, default=None)

    orbit_carry_frontier_parser = subparsers.add_parser(
        "orbit-carry-frontier",
        help="Export the flagship orbit-layer, carry-layer, frontier-target, and obstruction-family grouping for the repo's research thesis",
    )
    orbit_carry_frontier_parser.add_argument("--max", type=int, default=1200)
    orbit_carry_frontier_parser.add_argument("--base", type=int, default=10)
    orbit_carry_frontier_parser.add_argument("--blocks", type=int, default=8)
    orbit_carry_frontier_parser.add_argument("--output", type=str, default=None)

    state_merging_parser = subparsers.add_parser(
        "state-merging",
        help="Export selected-coordinate preimage-fiber profiles (public alias: state-merging atlas)",
    )
    state_merging_parser.add_argument("--max", type=int, default=500)
    state_merging_parser.add_argument("--base", type=int, default=10)
    state_merging_parser.add_argument("--blocks", type=int, default=8)
    state_merging_parser.add_argument("--output", type=str, default=None)

    state_merging_same_core_parser = subparsers.add_parser(
        "state-merging-same-core",
        help="Export same-core family disagreement rows for selected-coordinate preimage-fiber profiles",
    )
    state_merging_same_core_parser.add_argument("--max", type=int, default=500)
    state_merging_same_core_parser.add_argument("--base", type=int, default=10)
    state_merging_same_core_parser.add_argument("--blocks", type=int, default=8)
    state_merging_same_core_parser.add_argument("--output", type=str, default=None)

    quotient_obstructions_parser = subparsers.add_parser(
        "quotient-obstructions",
        help="Export visible preimage compression and hidden graph obstruction rows for quotient-only selected coordinates",
    )
    quotient_obstructions_parser.add_argument("--max", type=int, default=500)
    quotient_obstructions_parser.add_argument("--base", type=int, default=10)
    quotient_obstructions_parser.add_argument("--blocks", type=int, default=8)
    quotient_obstructions_parser.add_argument("--output", type=str, default=None)

    quotient_obstruction_families_parser = subparsers.add_parser(
        "quotient-obstruction-families",
        help="Export same-core family rows spanning relabeling, hidden, and visible quotient-only obstruction classes",
    )
    quotient_obstruction_families_parser.add_argument("--max", type=int, default=500)
    quotient_obstruction_families_parser.add_argument("--base", type=int, default=10)
    quotient_obstruction_families_parser.add_argument("--blocks", type=int, default=8)
    quotient_obstruction_families_parser.add_argument("--output", type=str, default=None)

    same_core_obstruction_phases_parser = subparsers.add_parser(
        "same-core-obstruction-phases",
        help="Export same-core family phase paths showing when selected-coordinate obstructions turn visible, stay hidden, or re-hide",
    )
    same_core_obstruction_phases_parser.add_argument("--max", type=int, default=1200)
    same_core_obstruction_phases_parser.add_argument("--base", type=int, default=10)
    same_core_obstruction_phases_parser.add_argument("--blocks", type=int, default=8)
    same_core_obstruction_phases_parser.add_argument("--output", type=str, default=None)

    same_core_obstruction_correlates_parser = subparsers.add_parser(
        "same-core-obstruction-correlates",
        help="Export empirical correlates separating same-core re-hiding families from one-way-visible families at the selected bound",
    )
    same_core_obstruction_correlates_parser.add_argument("--max", type=int, default=2000)
    same_core_obstruction_correlates_parser.add_argument("--base", type=int, default=10)
    same_core_obstruction_correlates_parser.add_argument("--blocks", type=int, default=8)
    same_core_obstruction_correlates_parser.add_argument("--output", type=str, default=None)

    prime_qr_parser = subparsers.add_parser(
        "prime-qr-generators",
        aliases=["prime-qr"],
        help="Rank generators of the quadratic-residue subgroup (legacy alias: prime-qr)",
    )
    prime_qr_parser.add_argument("--max", type=int, default=500)
    prime_qr_parser.add_argument("--base", type=int, default=10)
    prime_qr_parser.add_argument("--top", type=int, default=20)
    prime_qr_parser.add_argument("--output", type=str, default=None)

    atlas_parser = subparsers.add_parser(
        "published-atlas",
        aliases=["atlas"],
        help="Build the published example atlas (legacy alias: atlas)",
    )
    atlas_parser.add_argument("--max", type=int, default=500)
    atlas_parser.add_argument("--base", type=int, default=10)
    atlas_parser.add_argument("--top", type=int, default=8)
    atlas_parser.add_argument("--output", type=str, default=None)

    witness_parser = subparsers.add_parser(
        "theorem-witnesses",
        help="Export claim-linked theorem, empirical, or open-target witness rows from the registry-backed theorem surface",
    )
    witness_parser.add_argument("--claim", type=str, default=None, help="Restrict to a single claim ID")
    witness_parser.add_argument("--status", type=str, choices=STATUS_ORDER, default=None, help="Restrict by claim status")
    witness_parser.add_argument(
        "--kind",
        type=str,
        choices=WITNESS_KIND_ORDER,
        default=None,
        help="Restrict by witness kind",
    )
    witness_parser.add_argument(
        "--lean-example",
        type=str,
        default=None,
        help="Restrict to a Lean worked-example namespace such as QRTour.Composite996",
    )
    witness_parser.add_argument("--output", type=str, default=None)

    args = parser.parse_args()

    if args.command in {"small-residue-coordinates", "bridges"}:
        candidates = rank_bridge_candidates(
            args.max,
            base=args.base,
            kmax=args.kmax,
            mmax=args.mmax,
            top=None if args.top <= 0 else args.top,
            require_nontrivial=not args.include_trivial,
        )
        rows = [
            {
                "n": candidate.n,
                "periodic_modulus": candidate.periodic_modulus,
                "base": candidate.base,
                "m": candidate.m,
                "B": candidate.B,
                "k": candidate.k,
                "q": candidate.q,
                "period": candidate.period,
                "preperiod_digits": candidate.preperiod_digits,
                "visible_prefix": candidate.visible_prefix,
                "q_is_one": candidate.q_is_one,
                "score": candidate.score,
                "primary_vocabulary_id": candidate.primary_vocabulary_id,
                "explanation": candidate.explanation,
            }
            for candidate in candidates
        ]
    elif args.command in {"small-residue-coordinates-q1", "bridges-q1"}:
        rows = [
            {
                "n": candidate.n,
                "periodic_modulus": candidate.periodic_modulus,
                "base": candidate.base,
                "m": candidate.m,
                "B": candidate.B,
                "k": candidate.k,
                "q": candidate.q,
                "period": candidate.period,
                "preperiod_digits": candidate.preperiod_digits,
                "visible_prefix": candidate.visible_prefix,
                "score": candidate.score,
                "primary_vocabulary_id": candidate.primary_vocabulary_id,
                "explanation": candidate.explanation,
            }
            for candidate in rank_q_one_bridges(
                args.max,
                base=args.base,
                kmax=args.kmax,
                mmax=args.mmax,
                top=None if args.top <= 0 else args.top,
            )
        ]
    elif args.command == "legacy-counterexamples":
        bases = [int(base) for base in args.bases.split(",")]
        rows = [
            {
                "p": record.p,
                "base": record.base,
                "reptend_type": record.reptend_type,
                "legacy_claim": record.legacy_claim,
                "qr_strides": list(record.qr_strides),
            }
            for record in find_legacy_counterexamples(args.max, bases)
        ]
    elif args.command in {"prime-qr-generators", "prime-qr"}:
        rows = [
            {
                "p": record.p,
                "base": record.base,
                "reptend_type": record.reptend_type,
                "preferred_stride": record.preferred_stride,
                "preferred_k": record.preferred_k,
                "stride_count": record.stride_count,
                "score": record.score,
                "primary_vocabulary_id": record.primary_vocabulary_id,
                "explanation": record.explanation,
            }
            for record in rank_prime_qr_examples(
                args.max,
                base=args.base,
                top=None if args.top <= 0 else args.top,
            )
        ]
    elif args.command in {"published-atlas", "atlas"}:
        payload = build_example_atlas(
            max_n=args.max,
            max_p=args.max,
            base=args.base,
            top=args.top,
        )
        if args.output:
            _write_json(args.output, payload)
        else:
            print(json.dumps(payload, indent=2))
        return
    elif args.command == "theorem-witnesses":
        rows = build_claim_witness_rows(
            claim_id=args.claim,
            status=args.status,
            kind=args.kind,
            lean_example_namespace=args.lean_example,
        )
    elif args.command in {"visibility-profiles", "visibility"}:
        rows = visibility_profile_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
        )
    elif args.command == "visibility-counterexamples":
        rows = incoming_carry_counterexample_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
        )
    elif args.command == "same-core-visibility":
        rows = same_core_visibility_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
        )
    elif args.command == "carry-factorization":
        rows = carry_factorization_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
        )
    elif args.command == "carry-factorization-selector":
        rows = carry_selector_profile_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
        )
    elif args.command == "carry-selector-non-k1":
        rows = non_k_one_state_relabeling_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
        )
    elif args.command == "carry-selector-same-core":
        rows = same_core_selector_family_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
        )
    elif args.command == "carry-selector-research":
        rows = carry_selector_research_rows(
            args.max,
            bases=tuple(int(piece) for piece in args.bases.split(",") if piece.strip()),
            n_blocks=args.blocks,
        )
    elif args.command == "orbit-carry-frontier":
        rows = orbit_carry_frontier_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
        )
    elif args.command == "state-merging":
        rows = state_merging_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
            max_m=8,
        )
    elif args.command == "state-merging-same-core":
        rows = state_merging_same_core_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
            max_m=8,
        )
    elif args.command == "quotient-obstructions":
        rows = quotient_obstruction_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
            max_m=8,
        )
    elif args.command == "quotient-obstruction-families":
        rows = quotient_obstruction_family_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
            max_m=8,
        )
    elif args.command == "same-core-obstruction-phases":
        rows = same_core_obstruction_phase_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
            max_m=8,
        )
    elif args.command == "same-core-obstruction-correlates":
        rows = same_core_obstruction_correlate_rows(
            args.max,
            base=args.base,
            n_blocks=args.blocks,
            max_m=8,
        )
    else:
        rows = composite_profile_rows(args.max, base=args.base)

    if args.output:
        _write_csv(args.output, rows)
    else:
        for row in rows[:20]:
            print(row)


if __name__ == "__main__":
    main()
