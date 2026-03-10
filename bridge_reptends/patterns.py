#!/usr/bin/env python3
"""
Deeper exploration of stride patterns.

This module illustrates exact order-theoretic facts about QR-generating
strides and then looks for secondary patterns in the resulting stride sets.

Authors: Mike & Claude
Date: December 2025
"""

from math import gcd
from collections import defaultdict

from .analysis import (
    multiplicative_order,
    reptend_type,
    find_qr_strides,
    analyze_prime,
)


def euler_phi(n: int) -> int:
    """Euler's totient function φ(n)."""
    result = n
    p = 2
    while p * p <= n:
        if n % p == 0:
            while n % p == 0:
                n //= p
            result -= result // p
        p += 1
    if n > 1:
        result -= result // n
    return result


def factorize(n: int) -> dict[int, int]:
    """Prime factorization of n. Returns dict of prime -> exponent."""
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def sieve_primes(max_n: int) -> list[int]:
    """Simple sieve of Eratosthenes."""
    if max_n < 2:
        return []
    sieve = [True] * (max_n + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(max_n**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, max_n + 1, i):
                sieve[j] = False
    return [i for i in range(2, max_n + 1) if sieve[i]]


def investigate_stride_count_formula(max_p: int = 500, base: int = 10):
    """
    Verify the exact stride-count formula.

    Let r = ord_p(base) and half = (p-1)/2. Then QR-generating strides exist
    iff r is half or p-1, and in those cases the count is φ(half).
    """
    print("=" * 70)
    print("VERIFYING: Stride Count vs φ(half)")
    print("=" * 70)

    primes = [p for p in sieve_primes(max_p) if p > 2 and p != base]

    matches = 0
    data = []

    for p in primes:
        half = (p - 1) // 2
        phi_half = euler_phi(half)
        reptend_len = multiplicative_order(base, p)
        qr_strides = find_qr_strides(p, base)
        stride_count = len(qr_strides)

        ratio = stride_count / phi_half if phi_half > 0 else 0
        exact_count = phi_half if reptend_len in (half, p - 1) else 0

        data.append({
            'p': p,
            'half': half,
            'phi_half': phi_half,
            'reptend_len': reptend_len,
            'stride_count': stride_count,
            'exact_count': exact_count,
            'ratio': ratio,
            'factors_half': factorize(half),
        })

        if stride_count == exact_count:
            matches += 1

    print(f"\nPrime/base pairs matching the exact formula: {matches}/{len(primes)}")

    # Look at the ratios
    ratios = [d['ratio'] for d in data]
    print(f"Ratio stride_count/φ(half) statistics:")
    print(f"  Min: {min(ratios):.3f}")
    print(f"  Max: {max(ratios):.3f}")
    print(f"  Avg: {sum(ratios)/len(ratios):.3f}")

    # Group by ratio
    ratio_groups = defaultdict(list)
    for d in data:
        # Round ratio to nearest 0.1
        r = round(d['ratio'], 1)
        ratio_groups[r].append(d['p'])

    print("\nPrimes grouped by ratio (stride_count / φ(half)):")
    for r in sorted(ratio_groups.keys()):
        primes_in_group = ratio_groups[r][:10]  # Show up to 10
        print(f"  ratio ≈ {r}: {len(ratio_groups[r])} primes, e.g. {primes_in_group}")

    return data


def investigate_reptend_vs_strides(max_p: int = 500, base: int = 10):
    """
    Investigate how reptend length controls stride existence.

    Exact fact: stride 1 appears iff ord_p(base) = (p-1)/2.
    """
    print("\n" + "=" * 70)
    print("INVESTIGATING: Reptend Length vs Stride Existence")
    print("=" * 70)

    primes = [p for p in sieve_primes(max_p) if p > 2 and p != base]

    full_reptend = []      # ord = p-1
    half_reptend = []      # ord = (p-1)/2
    other_reptend = []     # ord is something else

    for p in primes:
        ord_base = multiplicative_order(base, p)
        half = (p - 1) // 2
        qr_strides = find_qr_strides(p, base)

        if ord_base == p - 1:
            full_reptend.append((p, qr_strides))
        elif ord_base == half:
            half_reptend.append((p, qr_strides))
        else:
            other_reptend.append((p, ord_base, half, qr_strides))

    print(f"\nFull reptend primes (ord_p({base}) = p-1): {len(full_reptend)}")
    for p, strides in full_reptend[:10]:
        print(f"  p={p}: strides={strides[:5]}{'...' if len(strides) > 5 else ''}")

    print(f"\nHalf reptend primes (ord_p({base}) = (p-1)/2): {len(half_reptend)}")
    has_stride_1 = sum(1 for p, strides in half_reptend if 1 in strides)
    print(f"  Of these, {has_stride_1} have stride 1 (base is QR-gen)")
    for p, strides in half_reptend[:10]:
        print(f"  p={p}: strides={strides[:5]}{'...' if len(strides) > 5 else ''}")

    print(f"\nOther reptend primes: {len(other_reptend)}")
    for p, ord_b, half, strides in other_reptend[:10]:
        print(f"  p={p}: ord={ord_b}, half={half}, strides={strides[:5]}{'...' if len(strides) > 5 else ''}")


def investigate_stride_patterns(max_p: int = 200, base: int = 10):
    """
    Look for arithmetic patterns in stride lists.

    After the exact order classification is fixed, look for residual
    arithmetic structure in the stride values themselves.
    """
    print("\n" + "=" * 70)
    print("INVESTIGATING: Stride Arithmetic Patterns")
    print("=" * 70)

    primes = [p for p in sieve_primes(max_p) if p > 2 and p != base]

    for p in primes:
        half = (p - 1) // 2
        qr_strides = find_qr_strides(p, base)

        if len(qr_strides) < 2:
            continue

        # Check for arithmetic progression
        diffs = [qr_strides[i+1] - qr_strides[i] for i in range(len(qr_strides)-1)]
        is_ap = len(set(diffs)) == 1

        # Check if strides are all odd or all even
        parities = set(s % 2 for s in qr_strides)

        print(f"\np={p}, half={half}, reptend_type={reptend_type(p, base)}")
        print(f"  Strides: {qr_strides}")
        print(f"  Differences: {diffs}")
        print(f"  Is AP: {is_ap} (common diff = {diffs[0] if is_ap else 'N/A'})")
        print(f"  Parities: {'all even' if parities == {0} else 'all odd' if parities == {1} else 'mixed'}")


def investigate_base_invariance_deeper(primes: list[int], bases: list[int] = [2, 7, 10, 12]):
    """
    Deeper look at base-invariance: what IS invariant?

    The stride VALUES differ by base, but what structural properties are preserved?
    """
    print("\n" + "=" * 70)
    print("INVESTIGATING: Base-Invariance Structure")
    print("=" * 70)

    for p in primes:
        half = (p - 1) // 2
        print(f"\np = {p}, half = {half}")

        analyses = {}
        for base in bases:
            if p == base:
                continue
            ord_base = multiplicative_order(base, p)
            qr_strides = find_qr_strides(p, base)
            analyses[base] = {
                'ord': ord_base,
                'strides': qr_strides,
                'count': len(qr_strides),
                'min_stride': min(qr_strides) if qr_strides else None,
                'first_stride_ratio': qr_strides[0] / ord_base if qr_strides else None,
            }

        for base, a in analyses.items():
            ord_str = f"{a['ord']:4d}" if a['ord'] else "None"
            ratio_str = f"{a['first_stride_ratio']:.3f}" if a['first_stride_ratio'] else "N/A"
            print(f"  base {base:2d}: ord={ord_str}, count={a['count']:3d}, "
                  f"first_stride={a['min_stride']}, first/ord={ratio_str}")

        # Are counts the same?
        counts = [a['count'] for a in analyses.values()]
        print(f"  Count invariant? {len(set(counts)) == 1}")


# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    print("PATTERN ANALYSIS - Investigating Stride Structure")
    print("=" * 70)

    # Run investigations
    data = investigate_stride_count_formula(max_p=300, base=10)
    investigate_reptend_vs_strides(max_p=300, base=10)
    investigate_stride_patterns(max_p=100, base=10)

    # Deep dive on a few interesting primes
    interesting_primes = [17, 41, 97, 101, 113]
    investigate_base_invariance_deeper(interesting_primes)
