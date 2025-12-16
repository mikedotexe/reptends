#!/usr/bin/env python3
"""
Coset structure analysis for quadratic residue reptends.

The multiplicative group (ℤ/pℤ)* splits into exactly two cosets:
- QR (quadratic residues / squares)
- NQR (non-quadratic residues / non-squares)

Key insight: When computing a/p in base B:
- The numerator a determines which coset the orbit lives in
- All remainders in the orbit stay in that coset forever
- The gap d = B^k - p traverses within the coset

This module provides utilities for:
- Testing QR membership (Euler's criterion)
- Finding block structure (the gap d = B^k - p)
- Extracting digit blocks that reveal coset traversal

Authors: Mike & Claude
Date: December 2025
"""

from dataclasses import dataclass
from typing import Optional

from .analysis import multiplicative_order


# Standard digit characters for bases up to 36
DIGIT_CHARS = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'


def is_qr(a: int, p: int) -> bool:
    """
    Test if a is a quadratic residue mod p using Euler's criterion.

    WARNING: This function requires p to be PRIME. For composite moduli,
    use the Jacobi symbol instead (different semantics).

    For prime p and a coprime to p:
        a is QR ⟺ a^((p-1)/2) ≡ 1 (mod p)

    Returns True for QR, False for NQR.
    Returns True for a ≡ 0 (mod p) by convention.

    Note: The Euler criterion is a primality-dependent concept. The geometric
    series skeleton (1/N = Σ k^j / B^(j+1)) works for ANY N coprime to base,
    but QR/NQR coset analysis specifically requires prime moduli.
    """
    a = a % p
    if a == 0:
        return True  # 0 is trivially a square
    return pow(a, (p - 1) // 2, p) == 1


def coset_of(a: int, p: int) -> str:
    """
    Return 'QR' or 'NQR' based on coset membership.

    WARNING: Requires p to be PRIME. See is_qr() for details.
    """
    return 'QR' if is_qr(a, p) else 'NQR'


def format_digit(d: int, base: int) -> str:
    """Format a single digit in the given base (A, B, C... for bases > 10)."""
    if d < 0 or d >= base or d >= len(DIGIT_CHARS):
        return '?'
    return DIGIT_CHARS[d]


@dataclass
class BlockStructure:
    """Analysis of block structure for a prime-base pair."""
    p: int
    base: int
    k: int                    # block width (number of digits per block)
    d: int                    # gap = base^k - p
    gap_ratio: float          # d/p (small = sweet spot)
    d_order: int              # ord_p(d)
    d_is_qr: bool             # d is in QR coset
    d_is_qr_generator: bool   # d generates entire QR subgroup


def find_block_structure(p: int, base: int, max_k: int = 10) -> Optional[BlockStructure]:
    """
    Find the best block width k where d = base^k - p is small and useful.

    Searches for the smallest k where:
    - d = base^k - p is positive (so base^k > p)
    - d is relatively small compared to p (sweet spot)
    - d has interesting order (ideally generates QR subgroup)

    Returns None if no suitable k found within max_k.
    """
    half = (p - 1) // 2

    for k in range(1, max_k + 1):
        power = base ** k
        if power <= p:
            continue

        d = power - p
        if d <= 0 or d >= p:
            continue

        gap_ratio = d / p
        d_order = multiplicative_order(d, p)
        d_is_qr = is_qr(d, p)
        d_is_qr_gen = (d_order == half)

        # Return first valid structure (smallest k with base^k > p)
        return BlockStructure(
            p=p,
            base=base,
            k=k,
            d=d,
            gap_ratio=gap_ratio,
            d_order=d_order or 0,
            d_is_qr=d_is_qr,
            d_is_qr_generator=d_is_qr_gen,
        )

    return None


@dataclass
class Block:
    """A single block from the reptend expansion."""
    index: int                # block number (0, 1, 2, ...)
    start_remainder: int      # remainder at start of block
    digits: str               # digit string for this block
    coset: str                # 'QR' or 'NQR'


def get_blocks(
    numerator: int,
    p: int,
    base: int,
    k: int,
    n_blocks: int
) -> list[Block]:
    """
    Extract digit blocks for numerator/p in given base with block width k.

    Each block contains k consecutive digits from the reptend expansion.
    The start_remainder shows where the block begins in the orbit.

    Args:
        numerator: The numerator a in a/p
        p: The prime denominator
        base: The base for digit extraction
        k: Block width (digits per block)
        n_blocks: Number of blocks to extract

    Returns:
        List of Block objects with (index, start_remainder, digits, coset)
    """
    r = numerator % p
    blocks = []

    for block_idx in range(n_blocks):
        start_r = r
        coset = coset_of(start_r, p)
        digit_str = ''

        for _ in range(k):
            digit = (r * base) // p
            r = (r * base) % p
            digit_str += format_digit(digit, base)

        blocks.append(Block(
            index=block_idx,
            start_remainder=start_r,
            digits=digit_str,
            coset=coset,
        ))

    return blocks


def get_block_remainders(
    numerator: int,
    p: int,
    d: int,
    n_blocks: int
) -> list[int]:
    """
    Get the sequence of block-start remainders.

    These are: a, a*d, a*d², a*d³, ... (mod p)

    This shows how the gap d traverses within the coset.
    """
    remainders = []
    r = numerator % p
    for _ in range(n_blocks):
        remainders.append(r)
        r = (r * d) % p
    return remainders


@dataclass
class CosetAnalysis:
    """Complete coset analysis for a prime-base pair."""
    p: int
    base: int
    half: int                 # (p-1)/2 = size of each coset
    block: BlockStructure     # block structure info
    qr_example: int           # example QR numerator
    nqr_example: int          # example NQR numerator


def analyze_coset_structure(p: int, base: int = 10) -> Optional[CosetAnalysis]:
    """
    Analyze the coset/block structure for a prime-base pair.

    Returns a CosetAnalysis with:
    - Block structure (k, d, gap ratio)
    - Example QR and NQR numerators
    - Coset sizes
    """
    block = find_block_structure(p, base)
    if block is None:
        return None

    half = (p - 1) // 2

    # Find smallest QR and NQR examples
    qr_example = 1  # 1 is always QR
    nqr_example = None
    for a in range(2, p):
        if not is_qr(a, p):
            nqr_example = a
            break

    if nqr_example is None:
        nqr_example = 2  # fallback (shouldn't happen for p > 2)

    return CosetAnalysis(
        p=p,
        base=base,
        half=half,
        block=block,
        qr_example=qr_example,
        nqr_example=nqr_example,
    )


def compare_coset_representatives(
    p: int,
    base: int,
    qr_numerator: int,
    nqr_numerator: int,
    n_blocks: int = 10
) -> dict:
    """
    Compare block patterns of a QR and NQR numerator.

    Shows that both cosets have identical structure,
    just translated by multiplication.

    Returns dict with block comparisons and verification.
    """
    block_info = find_block_structure(p, base)
    if block_info is None:
        return {"error": "No suitable block structure found"}

    k = block_info.k

    qr_blocks = get_blocks(qr_numerator, p, base, k, n_blocks)
    nqr_blocks = get_blocks(nqr_numerator, p, base, k, n_blocks)

    # Verify coset membership is preserved
    qr_all_qr = all(b.coset == 'QR' for b in qr_blocks)
    nqr_all_nqr = all(b.coset == 'NQR' for b in nqr_blocks)

    return {
        "p": p,
        "base": base,
        "block_width": k,
        "gap_d": block_info.d,
        "qr_numerator": qr_numerator,
        "nqr_numerator": nqr_numerator,
        "qr_blocks": qr_blocks,
        "nqr_blocks": nqr_blocks,
        "qr_stays_in_qr": qr_all_qr,
        "nqr_stays_in_nqr": nqr_all_nqr,
        "coset_closure_verified": qr_all_qr and nqr_all_nqr,
    }


# =============================================================================
# Quick demo
# =============================================================================

if __name__ == "__main__":
    print("=" * 70)
    print("COSET ANALYSIS - Demo")
    print("=" * 70)

    # Test with p = 139, base = 12 (canonical coset example)
    p, base = 139, 12

    print(f"\nAnalyzing p = {p}, base = {base}")

    analysis = analyze_coset_structure(p, base)
    if analysis:
        print(f"\nBlock structure:")
        print(f"  k = {analysis.block.k} (digits per block)")
        print(f"  d = {analysis.block.d} (gap = {base}^{analysis.block.k} - {p})")
        print(f"  gap ratio = {analysis.block.gap_ratio:.2%} of p")
        print(f"  d is {'QR' if analysis.block.d_is_qr else 'NQR'}")
        print(f"  d generates QR: {analysis.block.d_is_qr_generator}")

        print(f"\nCoset examples:")
        print(f"  QR example: {analysis.qr_example}")
        print(f"  NQR example: {analysis.nqr_example}")

        print(f"\nBlock comparison (first 8 blocks):")
        comparison = compare_coset_representatives(p, base, 1, 3, 8)

        print(f"\n  {'1/' + str(p):>8}  {'3/' + str(p):>8}")
        print(f"  {'rem':>4} {'digits':>6}  {'rem':>4} {'digits':>6}")
        print("  " + "-" * 26)

        for qb, nb in zip(comparison["qr_blocks"], comparison["nqr_blocks"]):
            print(f"  {qb.start_remainder:>4} {qb.digits:>6}  {nb.start_remainder:>4} {nb.digits:>6}")

        print(f"\n  Coset closure verified: {comparison['coset_closure_verified']}")

    print()
    print("-" * 70)
    print("Testing is_qr on small examples:")
    print("-" * 70)

    for test_p in [7, 13, 17]:
        qrs = [a for a in range(1, test_p) if is_qr(a, test_p)]
        nqrs = [a for a in range(1, test_p) if not is_qr(a, test_p)]
        print(f"  p={test_p}: QRs={qrs}, NQRs={nqrs}")
