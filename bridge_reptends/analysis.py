#!/usr/bin/env python3
"""
Core analysis functions for reptend structure.

This module provides:
- Universal functions for multiplicative order and long-division remainders
- Prime-specific functions for QR/coset analysis requiring prime p

Standard algebraic starting point:
for a block base B = base^m and modulus N, write

    B = qN + k, with 0 <= k < N.

Then

    1/N = q/(B-k) = (q/B) * 1/(1-k/B) = Σ q*k^j / B^(j+1).

The literal power pattern 1, k, k^2, ... is the special case q = 1, i.e.
N = B - k. That is the clean "bridge" case emphasized by the demos.

Authors: Mike & Claude
Date: December 2025
"""

from dataclasses import dataclass
from math import gcd
from typing import Optional


def multiplicative_order(a: int, n: int) -> Optional[int]:
    """
    Compute ord_n(a) - the multiplicative order of a modulo n.

    Returns the smallest positive integer m such that a^m ≡ 1 (mod n),
    or None if gcd(a, n) ≠ 1.

    Works for any modulus n (not just primes). By Lagrange's theorem,
    ord_n(a) divides |G| for any finite group G.
    """
    if gcd(a, n) != 1:
        return None

    order = 1
    val = a % n
    while val != 1:
        val = (val * a) % n
        order += 1
        if order > n:
            return None  # Shouldn't happen for coprime a, n
    return order


def long_division_remainders(n: int, base: int = 10, steps: Optional[int] = None) -> list[int]:
    """
    Get the remainder sequence from long division of 1/n in given base.

    Works for any n coprime to base (not just primes).

    The remainders satisfy:
        r_0 = 1
        r_{i+1} = (base * r_i) mod n

    So r_i ≡ base^i (mod n).

    If steps is None, computes until the sequence repeats (ord_n(base) steps).
    """
    if steps is None:
        steps = multiplicative_order(base, n) or n

    remainders = [1]
    r = 1
    for _ in range(steps - 1):
        r = (r * base) % n
        remainders.append(r)
    return remainders


def stride_order(p: int, base: int, stride: int) -> Optional[int]:
    """
    Compute ord_p(base^stride) using the exact order formula.

    If r = ord_p(base), then

        ord_p(base^stride) = r / gcd(r, stride).

    Returns None when base and p are not coprime.
    """
    reptend_len = multiplicative_order(base, p)
    if reptend_len is None:
        return None
    return reptend_len // gcd(reptend_len, stride)


def reptend_type(p: int, base: int) -> str:
    """
    Classify the prime/base pair by the order of the base.

    Returns one of:
    - "full" if ord_p(base) = p - 1
    - "half" if ord_p(base) = (p - 1) / 2
    - "degenerate" otherwise
    """
    reptend_len = multiplicative_order(base, p)
    half = (p - 1) // 2

    if reptend_len == p - 1:
        return "full"
    if reptend_len == half:
        return "half"
    return "degenerate"


def find_generator(remainders: list[int], n: int) -> Optional[int]:
    """
    Find the constant ratio k such that r_{i+1} = k * r_i (mod n).

    Works for any modulus n (not just primes).

    For long-division remainders, this should always be the base.
    But this function works for any geometric sequence mod n.

    Returns None if the sequence isn't geometric (constant ratio).
    """
    if len(remainders) < 2:
        return None

    # k = r_1 * r_0^{-1} mod n
    # Using Python 3.8+ modular inverse: pow(a, -1, n)
    try:
        r_0_inv = pow(remainders[0], -1, n)
    except ValueError:
        return None  # No inverse exists (not coprime to n)
    k = (remainders[1] * r_0_inv) % n

    # Verify the ratio is constant
    for i in range(len(remainders) - 1):
        try:
            r_i_inv = pow(remainders[i], -1, n)
        except ValueError:
            return None
        ratio = (remainders[i + 1] * r_i_inv) % n
        if ratio != k:
            return None

    return k


def is_qr_generator(k: int, p: int) -> bool:
    """
    Check if k is a QR-generator for (Z/pZ)*.

    A QR-generator has multiplicative order exactly (p-1)/2,
    meaning it generates the entire quadratic residue subgroup.
    """
    half = (p - 1) // 2
    ord_k = multiplicative_order(k, p)
    return ord_k == half


def find_qr_strides(p: int, base: int) -> list[int]:
    """
    Find all strides m where base^m is a QR-generator mod p.

    Let r = ord_p(base) and half = (p-1)/2. Then

        ord_p(base^m) = r / gcd(r, m).

    So base^m is a QR-generator exactly when

        r / gcd(r, m) = half.

    This gives an exact classification:
    QR-generating strides exist iff r is half or 2*half = p-1.

    Returns sorted list of stride values.
    """
    reptend_len = multiplicative_order(base, p)
    if reptend_len is None:
        return []

    half = (p - 1) // 2
    return [
        m
        for m in range(1, reptend_len + 1)
        if reptend_len // gcd(reptend_len, m) == half
    ]


@dataclass
class PrimeAnalysis:
    """Complete analysis of a prime's reptend structure in a given base."""
    p: int
    base: int
    reptend_length: int          # ord_p(base)
    half: int                    # (p-1)/2
    qr_strides: list[int]        # All m where base^m is QR-generator
    stride_count: int            # len(qr_strides)
    base_is_qr_gen: bool         # Is base itself a QR-generator? (1 in qr_strides)
    reptend_type: str            # full / half / degenerate
    family: Optional[str] = None # Detected family (if any)


def analyze_prime(p: int, base: int = 10) -> PrimeAnalysis:
    """
    Complete analysis of a prime's reptend structure.

    Returns a PrimeAnalysis with:
    - reptend_length: ord_p(base)
    - half: (p-1)/2
    - qr_strides: all m where base^m is QR-generator
    - stride_count: number of QR-generating strides
    - base_is_qr_gen: whether base itself is a QR-generator
    """
    reptend_length = multiplicative_order(base, p)
    if reptend_length is None:
        # base and p not coprime - shouldn't happen for prime p and base < p
        reptend_length = 0

    half = (p - 1) // 2
    qr_strides = find_qr_strides(p, base)

    return PrimeAnalysis(
        p=p,
        base=base,
        reptend_length=reptend_length,
        half=half,
        qr_strides=qr_strides,
        stride_count=len(qr_strides),
        base_is_qr_gen=(1 in qr_strides),
        reptend_type=reptend_type(p, base),
    )


def stride_fingerprint(p: int, bases: list[int]) -> dict:
    """
    Compute the stride fingerprint across multiple bases.

    Returns a dict mapping base -> qr_strides list.
    This is the "signature" that might reveal family structure.
    """
    return {base: find_qr_strides(p, base) for base in bases}


# =============================================================================
# Quick demo
# =============================================================================

if __name__ == "__main__":
    print("=" * 70)
    print("BRIDGE REPTENDS - Prime Analysis Demo")
    print("=" * 70)

    # Test with p = 97 (our canonical example)
    p = 97
    bases = [2, 7, 10, 12]

    print(f"\nAnalyzing p = {p}")
    print(f"half = (p-1)/2 = {(p-1)//2}")
    print()

    for base in bases:
        analysis = analyze_prime(p, base)
        print(f"Base {base:2d}: reptend_len = {analysis.reptend_length:2d}, "
              f"qr_strides = {analysis.qr_strides}, "
              f"count = {analysis.stride_count}")

    print()
    print("Fingerprint:")
    fp = stride_fingerprint(p, bases)
    for base, strides in fp.items():
        print(f"  base {base}: {strides}")

    print()
    print("-" * 70)
    print("Testing a few more primes...")
    print("-" * 70)

    test_primes = [7, 13, 17, 19, 23, 41, 97]
    print(f"\n{'prime':>5} {'half':>5} {'reptend':>7} {'qr_strides':>20} {'count':>5}")
    print("-" * 50)

    for p in test_primes:
        analysis = analyze_prime(p, base=10)
        strides_str = str(analysis.qr_strides) if analysis.qr_strides else "[]"
        print(f"{p:5d} {analysis.half:5d} {analysis.reptend_length:7d} {strides_str:>20} {analysis.stride_count:5d}")
