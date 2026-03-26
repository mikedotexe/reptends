#!/usr/bin/env python3
"""
Search and dataset generation for notable reptend examples.

This module turns the repo's exploratory scripts into reusable outputs:
- bridge-candidate ranking for readable q-weighted skeletons
- distinct leaderboards for q=1 bridges, nontrivial bridges, composites, and prime QR examples
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
from .registry import claim_context_for_parameters, claim_lookup, load_theorem_witnesses
from .transducer import (
    canonical_carry_dfa_examples,
    canonical_carry_selector_case_studies,
    canonical_carry_selector_family_studies,
    carry_factorization_rows,
    carry_selector_profile_class,
    carry_selector_profile_rows,
    carry_selector_research_rows,
    non_k_one_state_relabeling_rows,
    same_core_selector_family_rows,
)
from .visibility import (
    canonical_visibility_case_studies,
    canonical_visibility_family_studies,
    incoming_carry_counterexample_rows,
    same_core_visibility_rows,
    visibility_profile_rows,
)


DEFAULT_MIN_SIGNAL_MODULUS = 19
PUBLISHED_ATLAS_SCHEMA_VERSION = "2.9"


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


def build_claim_witness_rows() -> list[dict[str, object]]:
    """Return enriched theorem-witness rows for search/site-facing exports."""
    claims = claim_lookup()
    rows: list[dict[str, object]] = []
    for witness in load_theorem_witnesses():
        claim = claims[witness.claim_id]
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
                "evidence": list(witness.evidence),
            }
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
    visibility_cases = canonical_visibility_case_studies(base=base)
    visibility_families = canonical_visibility_family_studies(base=base)
    claim_witness_rows = build_claim_witness_rows()

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
                "data/theorem_witnesses.json",
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
            }
        },
    }
    return json.loads(json.dumps(payload, sort_keys=True))


def _write_csv(filename: str | Path, rows: list[dict[str, object]]) -> None:
    if not rows:
        return
    fieldnames = list(rows[0].keys())
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
    else:
        rows = composite_profile_rows(args.max, base=args.base)

    if args.output:
        _write_csv(args.output, rows)
    else:
        for row in rows[:20]:
            print(row)


if __name__ == "__main__":
    main()
