from math import gcd

from bridge_reptends import (
    find_qr_strides,
    multiplicative_order,
    reptend_type,
    stride_order,
)
from bridge_reptends.orbit_weave import phi


BASES = [2, 7, 10, 12]


def primes_up_to(limit: int) -> list[int]:
    primes: list[int] = []
    for n in range(2, limit + 1):
        if all(n % d for d in range(2, int(n**0.5) + 1)):
            primes.append(n)
    return primes


def expected_qr_strides(p: int, base: int) -> list[int]:
    reptend_len = multiplicative_order(base, p)
    if reptend_len is None:
        return []

    half = (p - 1) // 2
    return [
        m
        for m in range(1, reptend_len + 1)
        if reptend_len // gcd(reptend_len, m) == half
    ]


def test_counterexamples_to_the_old_stride_prose() -> None:
    assert find_qr_strides(19, 10) == [2, 4, 8, 10, 14, 16]
    assert find_qr_strides(19, 10) != list(range(2, 18, 2))

    assert find_qr_strides(31, 10) == [1, 2, 4, 7, 8, 11, 13, 14]
    assert find_qr_strides(31, 10) != list(range(1, 15))


def test_stride_order_matches_order_over_gcd_formula() -> None:
    for p in primes_up_to(200):
        if p <= 2:
            continue
        for base in BASES:
            if p == base:
                continue

            reptend_len = multiplicative_order(base, p)
            if reptend_len is None:
                continue

            for stride in range(1, reptend_len + 1):
                assert stride_order(p, base, stride) == reptend_len // gcd(reptend_len, stride)


def test_exact_qr_stride_classification_across_bases() -> None:
    for p in primes_up_to(200):
        if p <= 2:
            continue
        for base in BASES:
            if p == base:
                continue
            assert find_qr_strides(p, base) == expected_qr_strides(p, base)


def test_qr_stride_count_is_phi_of_half_in_nondegenerate_cases() -> None:
    for p in primes_up_to(200):
        if p <= 2:
            continue

        half = (p - 1) // 2
        for base in BASES:
            if p == base:
                continue

            reptend_len = multiplicative_order(base, p)
            if reptend_len is None:
                continue

            expected = phi(half) if reptend_len in (half, p - 1) else 0
            assert len(find_qr_strides(p, base)) == expected


def test_reptend_type_matches_base_order() -> None:
    assert reptend_type(19, 10) == "full"
    assert reptend_type(31, 10) == "half"
    assert reptend_type(41, 10) == "degenerate"
