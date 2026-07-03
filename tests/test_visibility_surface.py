from pathlib import Path

from bridge_reptends import load_claim_registry


ROOT = Path(__file__).resolve().parent.parent
THEOREM_GUIDE = ROOT / "lean" / "THEOREM_GUIDE.md"


def test_small_k_visibility_support_lists_coarse_prefix_equality_corollary() -> None:
    claim = next(
        claim
        for claim in load_claim_registry()
        if claim.id == "small_k_visibility_threshold"
    )
    item = next(
        item
        for item in claim.lean_support_items
        if item.module == "lean/QRTour/Visibility.lean"
    )

    theorem_name = "BlockCoordinate.emittedPrefixValue_eq_truncatedVisiblePrefixValue_of_remainderK_pow_lt_modulus"

    assert theorem_name in item.theorems
    assert "coarse `k^(n+L) < modulus` prefix-equality corollary" in item.role

    row = next(
        line
        for line in THEOREM_GUIDE.read_text().splitlines()
        if line.startswith("| `small_k_visibility_threshold` | [Visibility.lean]")
    )

    assert f"`{theorem_name}`" in row
    assert "coarse `k^(n+L) < modulus` prefix-equality corollary" in row
