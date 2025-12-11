#!/usr/bin/env python3
"""
REPTEND ANALYSIS - Core functions for exploring quadratic residue structure

This module provides the fundamental analysis primitives for understanding
reptends (repeating decimal expansions) through the lens of group theory.

Key insight: Reptends are orbits in multiplicative groups, not decimal curiosities.

Authors: Mike & Claude
Date: December 2025
"""

from dataclasses import dataclass
from math import gcd
from typing import Optional


def multiplicative_order(a: int, p: int) -> Optional[int]:
    """
    Compute ord_p(a) - the multiplicative order of a modulo p.

    Returns the smallest positive integer m such that a^m ≡ 1 (mod p),
    or None if gcd(a, p) ≠ 1.

    By Lagrange's theorem, ord_p(a) divides φ(p) = p-1 for prime p.
    """
    if gcd(a, p) != 1:
        return None

    order = 1
    val = a % p
    while val != 1:
        val = (val * a) % p
        order += 1
        if order > p:
            return None  # Shouldn't happen for coprime a, p
    return order


def long_division_remainders(p: int, base: int = 10, steps: Optional[int] = None) -> list[int]:
    """
    Get the remainder sequence from long division of 1/p in given base.

    The remainders satisfy:
        r_0 = 1
        r_{n+1} = (base * r_n) mod p

    So r_n ≡ base^n (mod p).

    If steps is None, computes until the sequence repeats (ord_p(base) steps).
    """
    if steps is None:
        steps = multiplicative_order(base, p) or p

    remainders = [1]
    r = 1
    for _ in range(steps - 1):
        r = (r * base) % p
        remainders.append(r)
    return remainders


def find_generator(remainders: list[int], p: int) -> Optional[int]:
    """
    Find the constant ratio k such that r_{i+1} = k * r_i (mod p).

    For long-division remainders, this should always be the base.
    But this function works for any geometric sequence mod p.

    Returns None if the sequence isn't geometric (constant ratio).
    """
    if len(remainders) < 2:
        return None

    # k = r_1 * r_0^{-1} mod p
    # Using Fermat's little theorem: r_0^{-1} = r_0^{p-2}
    r_0_inv = pow(remainders[0], p - 2, p)
    k = (remainders[1] * r_0_inv) % p

    # Verify the ratio is constant
    for i in range(len(remainders) - 1):
        r_i_inv = pow(remainders[i], p - 2, p)
        ratio = (remainders[i + 1] * r_i_inv) % p
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

    This is the key "fingerprint" of a prime: which powers of the base
    generate the quadratic residue subgroup?

    Returns sorted list of stride values.
    """
    half = (p - 1) // 2
    reptend_len = multiplicative_order(base, p)

    if reptend_len is None:
        return []

    qr_strides = []
    for m in range(1, reptend_len + 1):
        k = pow(base, m, p)
        if is_qr_generator(k, p):
            qr_strides.append(m)

    return qr_strides


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
    print("REPTEND ANALYSIS - Core Functions Demo")
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
