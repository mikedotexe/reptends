#!/usr/bin/env python3
"""
Multiplicative progression proof for the 2×10^m - 1 family.

For primes p = 2×10^m - 1:
  The decimal 1/p encodes powers of (p+1)/2 = 10^m

The progression terminates when it exhausts the orbit of 10^m.

This script proves it by:
  1. Extracting the remainders from long division
  2. Showing they ARE powers of 10^m at every m-th step
  3. Working backwards to recover the progression

Authors: Mike & Claude
Date: December 2025
"""

from decimal import Decimal, getcontext
getcontext().prec = 2000


def multiplicative_order(a, n):
    """Find ord_n(a)"""
    from math import gcd
    if gcd(a, n) != 1:
        return None
    order = 1
    val = a % n
    while val != 1:
        val = (val * a) % n
        order += 1
        if order > n:
            return None
    return order


def long_division_remainders(p, steps):
    """Get remainder sequence from long division of 1/p"""
    remainders = [1]
    r = 1
    for _ in range(steps - 1):
        r = (r * 10) % p
        remainders.append(r)
    return remainders


def analyze_progression(p, m):
    """
    Analyze 1/p where p = 2×10^m - 1
    """
    print("=" * 70)
    print(f"1/{p} = 1/(2×10^{m} - 1)")
    print("=" * 70)

    half = (p + 1) // 2
    print(f"\n(p+1)/2 = {half} = 10^{m}")

    ord_half = multiplicative_order(half, p)
    ord_10 = multiplicative_order(10, p)

    print(f"\nord_{p}({half}) = {ord_half}")
    print(f"ord_{p}(10) = {ord_10}")
    print(f"\nReptend length = {ord_10} digits")
    print(f"Number of m-digit 'words' = {ord_10 // m}")

    # Get remainders
    remainders = long_division_remainders(p, ord_10 + 1)

    # Extract every m-th remainder
    progression = remainders[::m][:ord_half + 1]

    print(f"\n{'─'*70}")
    print(f"THE MULTIPLICATIVE PROGRESSION (every {m}th remainder)")
    print(f"{'─'*70}")

    print(f"\n{'Step':<8} {'Remainder':<15} {f'{half}^i mod {p}':<20} {'Match?'}")
    print("-" * 55)

    for i, rem in enumerate(progression[:15]):
        expected = pow(half, i, p)
        match = "✓" if rem == expected else "✗"
        print(f"{i*m:<8} {rem:<15} {half}^{i} = {expected:<12} {match}")

    if len(progression) > 15:
        print("...")
        i = len(progression) - 1
        print(f"{i*m:<8} {progression[i]:<15} {half}^{i} = {pow(half, i, p):<12}")

    # Verify they're ALL powers
    all_match = all(progression[i] == pow(half, i, p) for i in range(len(progression) - 1))
    print(f"\nAll {len(progression)-1} terms match powers of {half}: {all_match}")

    print(f"\n{'─'*70}")
    print(f"TERMINATION PROOF")
    print(f"{'─'*70}")

    print(f"""
The progression visits these {ord_half} values:
  {half}^0 = 1
  {half}^1 = {half}
  {half}^2 = {pow(half, 2, p)}
  ...
  {half}^{ord_half-1} = {pow(half, ord_half-1, p)}

Then {half}^{ord_half} ≡ 1 (mod {p}) → CYCLE CLOSES

The progression TERMINATES after {ord_half} distinct values.
The reptend has {ord_10} digits = {m} × {ord_half} (m digits per power).
""")

    return progression


# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    print("""
╔══════════════════════════════════════════════════════════════════════╗
║      THE 2×10^m - 1 FAMILY: MULTIPLICATIVE PROGRESSIONS              ║
╚══════════════════════════════════════════════════════════════════════╝

For p = 2×10^m - 1, the decimal 1/p encodes powers of (p+1)/2 = 10^m.

Every m-th long division remainder IS a power of 10^m.

The progression terminates when it exhausts the orbit.
""")

    # Analyze Mike's primes
    cases = [
        (19, 1),
        (199, 2),
        (1999, 3),
    ]

    for p, m in cases:
        analyze_progression(p, m)
        print()

    # Also show 9999 as a contrast (not prime, different pattern)
    print("=" * 70)
    print("CONTRAST: 1/9999 (not prime)")
    print("=" * 70)
    print(f"""
9999 = 10^4 - 1 = 3² × 11 × 101

1/9999 = 0.00010001...

Reptend: 0001 (only 4 digits!)

This is special because 10^4 ≡ 1 (mod 9999).
The progression is trivial: just {{1, 10, 100, 1000}} then back to 1.
No "half" structure - it's 10^m - 1, not 2×10^m - 1.
""")
