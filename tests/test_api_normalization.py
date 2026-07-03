import subprocess
import sys

from bridge_reptends import (
    body_term,
    build_example_atlas,
    build_published_example_atlas,
    build_visibility_profiles,
    CertificateWorkbenchRecord,
    certificate_first_scaffold_mapping_lint_payload,
    certificate_fixture_mapping_lint_payload,
    certificate_lean_fixture_payload,
    certificate_lean_fixture_rows,
    certificate_lean_stub_payload,
    certificate_lean_stub_rows,
    certificate_workbench_rows,
    certified_positive_lookahead_coefficient_conflict_atlas_rows,
    certified_positive_lookahead_coefficient_conflict_family_rows,
    certified_positive_lookahead_coefficient_conflict_rows,
    certified_positive_lookahead_state_window_rows,
    CoefficientConflictCertificate,
    composite68_congruence_family_rows,
    composite68_cross_base_obstruction_sweep_rows,
    canonical_composite_families,
    canonical_composite_family_case_studies,
    compare_raw_coefficients_to_blocks,
    correction_term,
    find_good_modes,
    find_small_residue_block_coordinates,
    flux,
    LookaheadCertificate,
    observability_atlas_rows,
    observability_instrument_comparison_rows,
    observability_mod_stable_carry_loss_rows,
    observability_next_source_shape_family_rows,
    observability_program_atlas_rows,
    observability_shape13_k4_mod_stable_carry_loss_rows,
    observability_shape187_k188_family_rows,
    observability_shape17_k4_family_rows,
    observability_target_signature_rows,
    observability_target_split_rows,
    prime_power_lifting_family,
    prime_power_order_lifting_family,
    print_skeleton_analysis,
    render_raw_coefficient_analysis,
    skeleton_vs_actual,
    StateMapCertificate,
    visibility_profile_rows,
    weave,
)


def test_standard_label_aliases_remain_compatible() -> None:
    assert body_term is weave
    assert correction_term is flux
    assert callable(certified_positive_lookahead_coefficient_conflict_atlas_rows)
    assert callable(certified_positive_lookahead_coefficient_conflict_family_rows)
    assert callable(certified_positive_lookahead_coefficient_conflict_rows)
    assert callable(certified_positive_lookahead_state_window_rows)
    assert callable(certificate_first_scaffold_mapping_lint_payload)
    assert callable(certificate_fixture_mapping_lint_payload)
    assert callable(certificate_lean_fixture_payload)
    assert callable(certificate_lean_fixture_rows)
    assert callable(certificate_lean_stub_payload)
    assert callable(certificate_lean_stub_rows)
    assert callable(certificate_workbench_rows)
    assert callable(observability_atlas_rows)
    assert callable(observability_instrument_comparison_rows)
    assert callable(observability_mod_stable_carry_loss_rows)
    assert callable(observability_next_source_shape_family_rows)
    assert callable(observability_program_atlas_rows)
    assert callable(observability_shape13_k4_mod_stable_carry_loss_rows)
    assert callable(observability_shape187_k188_family_rows)
    assert callable(observability_shape17_k4_family_rows)
    assert callable(observability_target_signature_rows)
    assert callable(observability_target_split_rows)
    assert CertificateWorkbenchRecord.__name__ == "CertificateWorkbenchRecord"
    assert CoefficientConflictCertificate.__name__ == "CoefficientConflictCertificate"
    assert LookaheadCertificate.__name__ == "LookaheadCertificate"
    assert StateMapCertificate.__name__ == "StateMapCertificate"
    assert callable(composite68_congruence_family_rows)
    assert callable(composite68_cross_base_obstruction_sweep_rows)
    assert find_small_residue_block_coordinates is find_good_modes
    assert compare_raw_coefficients_to_blocks is skeleton_vs_actual
    assert render_raw_coefficient_analysis is print_skeleton_analysis
    assert prime_power_order_lifting_family is prime_power_lifting_family
    assert canonical_composite_families is canonical_composite_family_case_studies
    assert build_published_example_atlas is build_example_atlas
    assert build_visibility_profiles is visibility_profile_rows


def test_cli_help_uses_standard_names_and_mentions_legacy_aliases() -> None:
    result = subprocess.run(
        [sys.executable, "-m", "bridge_reptends.search", "--help"],
        check=True,
        capture_output=True,
        text=True,
    )
    help_text = result.stdout

    assert "small-residue-coordinates" in help_text
    assert "small-residue-coordinates-q1" in help_text
    assert "prime-qr-generators" in help_text
    assert "composite-profiles" in help_text
    assert "visibility-composite68-congruence-family" in help_text
    assert "visibility-profiles" in help_text
    assert "visibility-counterexamples" in help_text
    assert "visibility-certified-lookahead" in help_text
    assert "visibility-coefficient-conflicts" in help_text
    assert "visibility-coefficient-conflict-atlas" in help_text
    assert "visibility-coefficient-conflict-families" in help_text
    assert "visibility-composite68-base-sweep" in help_text
    assert "visibility-optics" in help_text
    assert "visibility-certificate-workbench" in help_text
    assert "observability-atlas" in help_text
    assert "observability-program-atlas" in help_text
    assert "observability-instrument-compare" in help_text
    assert "observability-mod-stable-carry-loss" in help_text
    assert "observability-shape13-k4-mod-stable-carry-loss" in help_text
    assert "observability-shape17-k4-family" in help_text
    assert "observability-next-source-shape-family" in help_text
    assert "observability-shape187-k188-family" in help_text
    assert "observability-target-signatures" in help_text
    assert "observability-target-split" in help_text
    assert "visibility-certificate-lean-fixtures" in help_text
    assert "visibility-certificate-lean-stubs" in help_text
    assert "visibility-base-compare" in help_text
    assert "instrument-atlas" in help_text
    assert "chart-invariance" in help_text
    assert "same-core-visibility" in help_text
    assert "carry-factorization" in help_text
    assert "carry-factorization-selector" in help_text
    assert "carry-selector-non-k1" in help_text
    assert "carry-selector-same-core" in help_text
    assert "carry-selector-research" in help_text
    assert "orbit-carry-frontier" in help_text
    assert "orbit-carry-trace" in help_text
    assert "published-atlas" in help_text
    assert "theorem-witnesses" in help_text
    assert "legacy alias" in help_text


def test_certificate_lean_stubs_help_lists_fixture_mapping_lint_options() -> None:
    result = subprocess.run(
        [sys.executable, "-m", "bridge_reptends.search", "visibility-certificate-lean-stubs", "--help"],
        check=True,
        capture_output=True,
        text=True,
    )
    help_text = result.stdout

    assert "--namespace" in help_text
    assert "--candidate-base" in help_text
    assert "--candidate-n" in help_text
    assert "--first-scaffold-only" in help_text
    assert "--namespace-prefix" in help_text
    assert "--module-path" in help_text


def test_theorem_witness_cli_help_mentions_lean_example_filter() -> None:
    result = subprocess.run(
        [sys.executable, "-m", "bridge_reptends.search", "theorem-witnesses", "--help"],
        check=True,
        capture_output=True,
        text=True,
    )
    help_text = result.stdout

    assert "--lean-example" in help_text
    assert "QRTour.Composite996" in help_text
