#!/usr/bin/env python3
"""
Orbit Weave + Closure Flux: Interactive Demo

This demo shows the algebraic decomposition of reptend integers:
    R = W + F
where:
    R = (B^L - 1) / M    (reptend integer)
    W = (B^L - k^L) / M  (orbit weave - finite body)
    F = (k^L - 1) / M    (closure flux - correction)
    k = B mod M          (bridge residue)
    L = ord_M(B)         (orbit length)

Run with: python -m bridge_reptends.examples.orbit_weave_demo

Authors: Mike & Claude
Date: December 2025
"""

from ..orbit_weave import (
    orbit_weave_analysis,
    print_analysis,
    print_skeleton_analysis,
    factorize,
    best_bridge_mode,
)
from ..analysis import multiplicative_order, is_qr_generator


def demo_canonical_example():
    """The canonical example: 1/97 in base 10."""
    print("=" * 70)
    print("CANONICAL EXAMPLE: 1/97")
    print("=" * 70)

    ow = orbit_weave_analysis(97)
    print_analysis(ow)

    print("\n--- Interpretation ---")
    print(f"The reptend 1/97 has {ow.digits} digits = {ow.L} blocks of {ow.m}.")
    print(f"Bridge residue k = {ow.k} = 100 mod 97.")
    print(f"This is the 'gap' d in the coset view.")

    if ow.k is not None and is_qr_generator(ow.k, ow.M):
        print(f"k = {ow.k} is a QR-generator (ord = {multiplicative_order(ow.k, ow.M)} = (p-1)/2).")
        print("So the weave W traverses the entire QR subgroup.")


def demo_composites():
    """Show how the decomposition handles composites."""
    print("\n" + "=" * 70)
    print("COMPOSITES: Stripping base factors")
    print("=" * 70)

    examples = [96, 200, 996, 9996]

    for N in examples:
        ow = orbit_weave_analysis(N)
        print(f"\nN = {N}")
        if ow.stripped_factors:
            factors_str = " × ".join(f"{p}^{e}" for p, e in ow.stripped_factors.items())
            print(f"  Stripped: {factors_str}")
            print(f"  Purely periodic M = {ow.M}")
        if ow.terminates:
            print("  Terminates (no reptend)")
        elif not ow.too_large:
            print(f"  Mode m={ow.m}, k={ow.k}, L={ow.L} blocks")
            print(f"  R = W + F verified: {ow.R == ow.W + ow.F}")


def demo_mode_selection():
    """Show how mode selection finds small bridge residues."""
    print("\n" + "=" * 70)
    print("MODE SELECTION: Finding small bridge residue k")
    print("=" * 70)

    primes = [7, 13, 17, 19, 97, 139, 199, 1999]

    print(f"\n{'Prime':>6} {'Best m':>7} {'k':>5} {'L blocks':>9} {'Reason':>20}")
    print("-" * 55)

    for p in primes:
        m_bridge = best_bridge_mode(p, base=10, kmax=5)
        if m_bridge:
            k = pow(10, m_bridge, p)
            L = multiplicative_order(100 if m_bridge == 2 else 10**m_bridge, p)
            reason = f"10^{m_bridge} ≡ {k} (mod {p})"
        else:
            m_bridge = len(str(p))
            k = pow(10, m_bridge, p)
            L = multiplicative_order(10**m_bridge, p) or 0
            reason = "near-power default"

        print(f"{p:>6} {m_bridge:>7} {k:>5} {L:>9} {reason:>20}")


def demo_research_questions():
    """Explore some of the research questions."""
    print("\n" + "=" * 70)
    print("RESEARCH: Factorization of W and F")
    print("=" * 70)

    # Small examples where we can show factorization
    for N in [7, 13, 19]:
        ow = orbit_weave_analysis(N)
        if ow.too_large or ow.terminates:
            continue

        print(f"\nN = {N}")
        print(f"  R = {ow.R}")
        print(f"  W = {ow.W}")
        print(f"  F = {ow.F}")

        # Factor small values
        if ow.R and ow.R < 10**12:
            R_factors = factorize(ow.R)
            W_factors = factorize(ow.W) if ow.W else {}
            F_factors = factorize(ow.F) if ow.F and ow.F > 0 else {}

            print(f"  R factors: {R_factors}")
            print(f"  W factors: {W_factors}")
            print(f"  F factors: {F_factors}")


def demo_near_power_family():
    """The 2×10^m - 1 family: 19, 199, 1999, ..."""
    print("\n" + "=" * 70)
    print("NEAR-POWER FAMILY: p = 2×10^m - 1")
    print("=" * 70)

    for m in range(1, 5):
        p = 2 * (10**m) - 1
        ow = orbit_weave_analysis(p)

        print(f"\np = 2×10^{m} - 1 = {p}")
        if ow.too_large:
            print(f"  [too large: {ow.digits} digits]")
            continue

        print(f"  Mode m={ow.m}, k={ow.k}, L={ow.L}")
        print(f"  Bridge factor t = (B-k)/M = {ow.bridge_factor}")

        # Check if k is QR-generator
        half = (p - 1) // 2
        ord_k = multiplicative_order(ow.k, p)
        if ord_k == half:
            print(f"  k={ow.k} is QR-generator (ord = {ord_k} = half)")


def demo_skeleton_and_carry():
    """Show the two-layer structure: skeleton + carry."""
    print("\n" + "=" * 70)
    print("SKELETON + CARRY: The Two-Layer Structure")
    print("=" * 70)

    print("""
For N = B - k (near a power of base):
  1/N = 1/(B-k) = (1/B) × 1/(1 - k/B) = Σ k^j / B^(j+1)

Layer 1 (SKELETON): Raw blocks are powers of k: 1, k, k², k³, ...
Layer 2 (CARRY):    When k^j ≥ B, overflow carries left
Layer 3 (FLUX):     Cyclic closure when reptend wraps around
""")

    print("The 10^n - 4 family (k=4 in all cases):")
    for N in [96, 996, 9996]:
        print_skeleton_analysis(N, n_blocks=12)


if __name__ == "__main__":
    demo_canonical_example()
    demo_composites()
    demo_mode_selection()
    demo_skeleton_and_carry()
    demo_research_questions()
    demo_near_power_family()

    print("\n" + "=" * 70)
    print("Demo complete. See DISCOVERIES.md for research questions.")
    print("=" * 70)
