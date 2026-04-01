"""
Generate the concise expository note from the registry and published atlas.
"""

from __future__ import annotations

from pathlib import Path

from .registry import (
    claim_lookup,
    load_theorem_witnesses,
    open_claims,
    render_open_claim_lines,
    render_proof_system_legend_lines,
    render_registry_summary_lines,
    render_theorem_witness_summary_lines,
    vocabulary_lookup,
)
from .search import build_example_atlas


ROOT = Path(__file__).resolve().parent.parent
NOTE_PATH = ROOT / "docs" / "EXPOSITORY_NOTE.md"


def _doc_link(path: str) -> str:
    return f"[{Path(path).name}]({ROOT / path})"


def render_expository_note_lines() -> tuple[str, ...]:
    claims = claim_lookup()
    vocabulary = vocabulary_lookup()
    witnesses = {record.id: record for record in load_theorem_witnesses()}
    atlas = build_example_atlas(max_n=1200, max_p=1200, top=8)

    classical_ids = (
        "series_q_weighted_identity",
        "power_order_formula",
        "crt_period_lcm",
        "preperiod_from_base_factors",
        "incoming_carry_position_formula",
        "same_core_threshold_shift_interval",
    )
    formalized_ids = (
        "qr_stride_classification",
        "digit_periodicity",
        "signed_bridge_recurrence",
        "bridge_block_value_periodicity",
        "crt_period_lcm",
        "preperiod_from_base_factors",
    )
    implementation_ids = (
        "carry_window_transducer",
        "positive_q_good_modes",
        "small_k_visibility_heuristic",
    )

    lines = [
        "# Expository Note",
        "",
        "This note is generated from the claim registry, theorem-witness registry, vocabulary registry, and published example atlas.",
        "Each theorem-level item is tagged by claim ID and points back to concrete evidence.",
        "",
        "## Proof-System Legend",
        "",
        *render_proof_system_legend_lines(),
        "",
        "## Release Snapshot",
        "",
        f"Use {_doc_link('docs/PROOF_STATUS_ATLAS.md')} as the theorem-level status source of truth.",
        "Current registry counts:",
        "",
        *render_registry_summary_lines(),
        "",
        "Current open claim IDs:",
        *render_open_claim_lines(),
        "",
        "## Theorem-Witness Surface",
        "",
        f"Use {_doc_link('docs/THEOREM_WITNESS_ATLAS.md')} for the claim-linked witness registry.",
        *render_theorem_witness_summary_lines(),
        "",
        f"- `{witnesses['series_q_weighted_identity_prime97_stride2'].id}` -> `{witnesses['series_q_weighted_identity_prime97_stride2'].claim_id}`: {witnesses['series_q_weighted_identity_prime97_stride2'].tuple_display}",
        f"- `{witnesses['same_core_threshold_shift_interval_996_over_249'].id}` -> `{witnesses['same_core_threshold_shift_interval_996_over_249'].claim_id}`: {witnesses['same_core_threshold_shift_interval_996_over_249'].tuple_display}",
        f"- `{witnesses['small_k_visibility_threshold_target_97_249_996'].id}` -> `{witnesses['small_k_visibility_threshold_target_97_249_996'].claim_id}`: {witnesses['small_k_visibility_threshold_target_97_249_996'].tuple_display}",
        f"- `{witnesses['carry_dfa_factorization_target_21_97_996'].id}` -> `{witnesses['carry_dfa_factorization_target_21_97_996'].claim_id}`: {witnesses['carry_dfa_factorization_target_21_97_996'].tuple_display}",
        "",
        "## Classical Background",
        "",
    ]

    for claim_id in classical_ids:
        claim = claims[claim_id]
        evidence = ", ".join(_doc_link(path) for path in claim.evidence)
        lines.extend(
            [
                f"- `{claim.id}` ({claim.status})",
                f"  Statement: {claim.statement}",
                f"  Evidence: {evidence}",
            ]
        )

    lines.extend(
        [
            "",
            "## Formalized Results",
            "",
        ]
    )
    for claim_id in formalized_ids:
        claim = claims[claim_id]
        evidence = ", ".join(_doc_link(path) for path in claim.evidence)
        lines.extend(
            [
                f"- `{claim.id}` ({claim.status})",
                f"  Statement: {claim.statement}",
                f"  Proof status: {claim.proof_status}",
                f"  Evidence: {evidence}",
            ]
        )

    lines.extend(
        [
            "",
            "## Implementation Layers",
            "",
            (
                f"- Standard vocabulary anchors: `{vocabulary['good_mode'].preferred_label}`, "
                f"`{vocabulary['remainder_orbit'].preferred_label}`, "
                f"`{vocabulary['carry_layer'].preferred_label}`."
            ),
        ]
    )
    for claim_id in implementation_ids:
        claim = claims[claim_id]
        evidence = ", ".join(_doc_link(path) for path in claim.evidence)
        lines.extend(
            [
                f"- `{claim.id}` ({claim.status})",
                f"  Statement: {claim.statement}",
                f"  Repo status: {claim.repo_status}",
                f"  Evidence: {evidence}",
            ]
        )

    lines.extend(
        [
            "",
            "## Curated Examples",
            "",
        ]
    )
    for example in atlas["canonical_examples"]:
        lines.append(
            f"- `1/{example['n']}` - {example['label']}: {example['explanation']}"
        )
    lines.extend(
        [
            "",
            "Composite family case studies:",
        ]
    )
    for case in atlas["case_studies"]["composite_families"]:
        lines.append(
            f"- {case['label']} ({', '.join(str(member) for member in case['members'])}) - {case['explanation']}"
        )
    lines.extend(
        [
            "",
            "Carry / DFA case studies:",
        ]
    )
    for case in atlas["case_studies"]["carry_dfa"]:
        lines.extend(
            [
                f"- `1/{case['n']}` - {case['label']}: {case['distinctive_feature']}",
                f"  Implemented boundary: {case['factorization_status']['implemented']}",
                f"  Open boundary: {case['factorization_status']['open_boundary']}",
            ]
        )
    lines.extend(
        [
            "",
            "Carry selector case studies:",
        ]
    )
    for case in atlas["case_studies"]["carry_selector"]:
        lines.extend(
            [
                f"- `1/{case['n']}` - {case['label']}: {case['explanation']}",
                f"  Selector summary: class {case['profile']['profile_class']}, selected m {case['profile']['selected_m']}, selected k {case['profile']['selected_k']}, relabeling modes {case['profile']['relabeling_modes']}",
                f"  Theorem candidate: {case['theorem_candidate']}",
                f"  Counterexample target: {case['counterexample_target']}",
            ]
        )
    lines.extend(
        [
            "",
            "Carry selector family studies:",
        ]
    )
    for family in atlas["case_studies"]["carry_selector_families"]:
        lines.append(
            f"- {family['label']} ({', '.join(str(member) for member in family['members'])}) - {family['explanation']}"
        )
    lines.extend(
        [
            "",
            "Carry selector cross-base summary:",
        ]
    )
    for row in atlas["research_layers"]["carry_selector"]["bases"]:
        lines.extend(
            [
                f"- base {row['base']} up to N <= {row['classification_bound']}: {row['non_k_one_count']} selected non-k = 1 relabeling windows and {row['same_core_disagreement_count']} same-core disagreement groups.",
                f"  Publication decision: {row['publication_decision']}",
            ]
        )
    lines.extend(
        [
            "",
            "Carried-prefix visibility case studies:",
        ]
    )
    for case in atlas["case_studies"]["visibility"]:
        lines.extend(
            [
                f"- `1/{case['n']}` - {case['label']}: {case['explanation']}",
                f"  Exact observable summary: raw-prefix agreement {case['profile']['raw_prefix_agreement_length']}/{case['profile']['requested_blocks']}, first incoming carry {case['profile']['first_incoming_carry_position']}, first local overflow {case['profile']['first_local_overflow_position']}, lookahead {case['profile']['lookahead_blocks']}",
                f"  Theorem candidate: {case['theorem_candidate']}",
                f"  Counterexample target: {case['counterexample_target']}",
            ]
        )
    lines.extend(
        [
            "",
            "Visibility family studies:",
        ]
    )
    for family in atlas["case_studies"]["visibility_families"]:
        lines.append(
            f"- {family['label']} ({', '.join(str(member) for member in family['members'])}) - {family['explanation']}"
        )

    covered_claim_ids = (
        set(classical_ids)
        | set(formalized_ids)
        | set(implementation_ids)
        | {claim.id for claim in open_claims()}
    )
    missing_claims = [
        claim for claim_id, claim in claims.items() if claim_id not in covered_claim_ids
    ]
    if missing_claims:
        lines.extend(
            [
                "",
                "## Additional Registry Claims",
                "",
            ]
        )
        for claim in missing_claims:
            evidence = ", ".join(_doc_link(path) for path in claim.evidence)
            lines.extend(
                [
                    f"- `{claim.id}` ({claim.status})",
                    f"  Statement: {claim.statement}",
                    f"  Evidence: {evidence}",
                ]
            )

    lines.extend(
        [
            "",
            "## Open Questions",
            "",
        ]
    )
    for claim in open_claims():
        evidence = ", ".join(_doc_link(path) for path in claim.evidence)
        lines.extend(
            [
                f"- `{claim.id}`",
                f"  Statement: {claim.statement}",
                f"  Evidence: {evidence}",
            ]
        )

    return tuple(lines)


def sync_expository_note() -> Path:
    NOTE_PATH.write_text("\n".join(render_expository_note_lines()) + "\n")
    return NOTE_PATH


def main() -> None:
    path = sync_expository_note()
    print(path.relative_to(ROOT))


if __name__ == "__main__":
    main()
