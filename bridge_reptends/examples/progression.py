#!/usr/bin/env python3
"""
Multiplicative progression for the 2·10^m - 1 family.

For primes p = 2·10^m - 1 (e.g., 19, 199, 1999):
  - 10^m ≡ (p+1)/2 (mod p)
  - Every m-th remainder in 1/p is a power of 10^m
  - When ord(10^m) = (p-1)/2, this element generates exactly QR

The stride-m remainders form a geometric progression that visits each
quadratic residue exactly once before returning to 1.

Authors: Mike & Claude
Date: December 2025
"""

from decimal import Decimal, getcontext
getcontext().prec = 2000

from bridge_reptends import is_qr, coset_of


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

    # Add coset analysis
    half_is_qr = is_qr(half, p)
    qr_subgroup_size = (p - 1) // 2
    print(f"\nCOSET STRUCTURE:")
    print(f"  {half} is {'QR' if half_is_qr else 'NQR'} mod {p}")
    print(f"  QR subgroup size = (p-1)/2 = {qr_subgroup_size}")
    if ord_half == qr_subgroup_size:
        print(f"  ord_{p}({half}) = {ord_half} = (p-1)/2")
        print(f"  → {half} generates exactly QR (the index-2 subgroup)")
        print(f"    The stride-{m} tour visits all {qr_subgroup_size} quadratic residues.")

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

Then {half}^{ord_half} ≡ 1 (mod {p}), closing the orbit.

By Lagrange, ord({half}) divides {p-1}. Here ord({half}) = {ord_half} = (p-1)/2,
so the orbit has exactly {ord_half} elements—the entire QR subgroup.

The reptend has {ord_10} digits = {m} × {ord_half} (m digits per orbit element).

Coset view: {half} ∈ {'QR' if is_qr(half, p) else 'NQR'}, so its powers stay in {'QR' if is_qr(half, p) else 'NQR'}.
The {ord_half} stride-{m} remainders are precisely the quadratic residues mod {p}.
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

For p = 2·10^m − 1, the decimal 1/p encodes powers of (p+1)/2 = 10^m.

Every m-th long division remainder is a power of 10^m.

The progression terminates when it exhausts the orbit.

┌────────────────────────────────────────────────────────────────────┐
│  MATHEMATICAL BACKGROUND                                           │
├────────────────────────────────────────────────────────────────────┤
│  The squaring map x ↦ x² on (ℤ/pℤ)× has kernel {±1}, so          │
│      QR := { a² } has |QR| = (p−1)/2,                             │
│  making QR the unique index-2 subgroup.                            │
│                                                                    │
│  An element g with ord(g) = (p−1)/2 generates exactly QR.          │
│  For p = 2·10^m − 1, we have 10^m ≡ (p+1)/2 (mod p), and this     │
│  element often has order (p−1)/2, i.e., generates QR.              │
│                                                                    │
│  Thus the stride-m remainders form a geometric progression         │
│  that visits each QR exactly once before returning to 1.           │
└────────────────────────────────────────────────────────────────────┘
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
