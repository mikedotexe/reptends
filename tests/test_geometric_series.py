from fractions import Fraction

from bridge_reptends import canonical_fraction
from bridge_reptends.orbit_weave import (
    apply_carry,
    best_bridge_mode,
    raw_power_blocks,
    raw_series_blocks,
    skeleton_vs_actual,
)


def test_canonical_fraction_is_the_exact_q_weighted_identity() -> None:
    for modulus, m in [(37, 3), (97, 2), (249, 3)]:
        q, denominator, _ = canonical_fraction(modulus, m)
        assert Fraction(1, modulus) == Fraction(q, denominator)


def test_good_coordinate_search_requires_positive_q() -> None:
    assert best_bridge_mode(37, base=10, kmax=12) == 3


def test_q_weighted_series_matches_non_bridge_example() -> None:
    result = skeleton_vs_actual(37, n_blocks=6)

    assert result["q"] == 27
    assert result["k"] == 1
    assert raw_series_blocks(result["q"], result["k"], 6) == [27] * 6
    assert apply_carry(raw_series_blocks(result["q"], result["k"], 6), result["B"]) == ["027"] * 6
    assert result["carried"][:6] == ["027"] * 6
    assert result["actual"][:6] == ["027"] * 6


def test_q_equals_one_special_case_uses_literal_powers() -> None:
    result = skeleton_vs_actual(97, prefer_m=2, n_blocks=12)

    assert result["q"] == 1
    assert result["raw"][:6] == raw_power_blocks(result["k"], result["m"], 6)
    assert result["carried"][:5] == result["actual"][:5]
