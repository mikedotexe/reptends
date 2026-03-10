import subprocess
import sys

from bridge_reptends import (
    body_term,
    build_example_atlas,
    build_published_example_atlas,
    build_visibility_profiles,
    canonical_composite_families,
    canonical_composite_family_case_studies,
    compare_raw_coefficients_to_blocks,
    correction_term,
    find_good_modes,
    find_small_residue_block_coordinates,
    flux,
    prime_power_lifting_family,
    prime_power_order_lifting_family,
    print_skeleton_analysis,
    render_raw_coefficient_analysis,
    skeleton_vs_actual,
    visibility_profile_rows,
    weave,
)


def test_standard_label_aliases_remain_compatible() -> None:
    assert body_term is weave
    assert correction_term is flux
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
    assert "visibility-profiles" in help_text
    assert "visibility-counterexamples" in help_text
    assert "same-core-visibility" in help_text
    assert "carry-factorization" in help_text
    assert "carry-factorization-selector" in help_text
    assert "carry-selector-non-k1" in help_text
    assert "carry-selector-same-core" in help_text
    assert "carry-selector-research" in help_text
    assert "published-atlas" in help_text
    assert "legacy alias" in help_text
