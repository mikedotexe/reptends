#!/usr/bin/env python3
"""
PRIME SWEEP - Systematic exploration of reptend structure across primes

Sweeps through primes and collects stride fingerprints to discover:
1. Family patterns in stride distributions
2. Base-invariance of stride counts
3. Relationship between reptend length and QR-strides

Authors: Mike & Claude
Date: December 2025
"""

import csv
import sys
from collections import defaultdict
from dataclasses import dataclass
from typing import Iterator

from reptend_analysis import (
    analyze_prime,
    multiplicative_order,
    stride_fingerprint,
    PrimeAnalysis,
)


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


@dataclass
class StrideSummary:
    """Summary of stride analysis for a prime across multiple bases."""
    p: int
    half: int
    analyses: dict[int, PrimeAnalysis]  # base -> analysis
    stride_counts: dict[int, int]       # base -> count
    is_count_invariant: bool            # Do all coprime bases have same count?


def analyze_prime_multibase(p: int, bases: list[int]) -> StrideSummary:
    """
    Analyze a prime across multiple bases.

    Returns summary including whether stride count is base-invariant.
    """
    analyses = {}
    stride_counts = {}

    for base in bases:
        if base % p == 0:
            continue  # Skip bases divisible by p
        analysis = analyze_prime(p, base)
        analyses[base] = analysis
        stride_counts[base] = analysis.stride_count

    # Check base-invariance: are all counts the same?
    counts = list(stride_counts.values())
    is_count_invariant = len(set(counts)) <= 1 if counts else True

    return StrideSummary(
        p=p,
        half=(p - 1) // 2,
        analyses=analyses,
        stride_counts=stride_counts,
        is_count_invariant=is_count_invariant,
    )


def sweep_primes(max_p: int, bases: list[int], verbose: bool = True) -> list[StrideSummary]:
    """
    Sweep through all primes up to max_p, analyzing each in all given bases.
    """
    primes = sieve_primes(max_p)
    # Skip p=2 (no interesting structure) and bases that are in our list
    primes = [p for p in primes if p > 2 and p not in bases]

    results = []
    for i, p in enumerate(primes):
        if verbose and (i + 1) % 100 == 0:
            print(f"  Processed {i + 1}/{len(primes)} primes...", file=sys.stderr)

        summary = analyze_prime_multibase(p, bases)
        results.append(summary)

    return results


def write_csv(results: list[StrideSummary], bases: list[int], filename: str):
    """Write sweep results to CSV."""
    with open(filename, 'w', newline='') as f:
        writer = csv.writer(f)

        # Header
        header = ['prime', 'half']
        for base in bases:
            header.extend([f'reptend_b{base}', f'strides_b{base}', f'count_b{base}'])
        header.append('count_invariant')
        writer.writerow(header)

        # Data
        for s in results:
            row = [s.p, s.half]
            for base in bases:
                if base in s.analyses:
                    a = s.analyses[base]
                    row.extend([
                        a.reptend_length,
                        str(a.qr_strides),
                        a.stride_count,
                    ])
                else:
                    row.extend(['', '', ''])
            row.append(s.is_count_invariant)
            writer.writerow(row)


def print_summary_stats(results: list[StrideSummary], bases: list[int]):
    """Print summary statistics from sweep."""
    print("\n" + "=" * 70)
    print("SWEEP SUMMARY STATISTICS")
    print("=" * 70)

    total = len(results)
    print(f"\nTotal primes analyzed: {total}")

    # Count-invariance
    invariant = sum(1 for r in results if r.is_count_invariant)
    print(f"Count-invariant primes: {invariant} ({100*invariant/total:.1f}%)")

    # Stride count distribution per base
    for base in bases:
        counts = [r.stride_counts.get(base, 0) for r in results if base in r.stride_counts]
        if counts:
            zero_count = sum(1 for c in counts if c == 0)
            avg_count = sum(counts) / len(counts)
            max_count = max(counts)
            print(f"\nBase {base}:")
            print(f"  Primes with 0 QR-strides: {zero_count} ({100*zero_count/len(counts):.1f}%)")
            print(f"  Average stride count: {avg_count:.2f}")
            print(f"  Max stride count: {max_count}")

    # Find primes with interesting patterns
    print("\n" + "-" * 70)
    print("INTERESTING PRIMES")
    print("-" * 70)

    # Primes where base 10 has QR-stride 1 (base itself is QR-gen)
    base_is_qrgen = [r for r in results if r.analyses.get(10) and 1 in r.analyses[10].qr_strides]
    print(f"\nPrimes where 10 is QR-generator: {len(base_is_qrgen)}")
    if len(base_is_qrgen) <= 20:
        print(f"  {[r.p for r in base_is_qrgen]}")

    # Primes with highest stride counts
    by_count = sorted(results, key=lambda r: r.stride_counts.get(10, 0), reverse=True)
    print(f"\nTop 10 primes by base-10 stride count:")
    for r in by_count[:10]:
        if 10 in r.stride_counts:
            print(f"  p={r.p}: count={r.stride_counts[10]}, half={r.half}")

    # Non-invariant primes (different stride counts in different bases)
    non_invariant = [r for r in results if not r.is_count_invariant]
    print(f"\nPrimes with non-invariant stride counts: {len(non_invariant)}")
    if len(non_invariant) <= 10:
        for r in non_invariant:
            print(f"  p={r.p}: {r.stride_counts}")


def print_fingerprint_families(results: list[StrideSummary], bases: list[int]):
    """Group primes by their stride fingerprints."""
    print("\n" + "=" * 70)
    print("FINGERPRINT FAMILIES (grouped by stride count pattern)")
    print("=" * 70)

    # Group by tuple of stride counts
    families = defaultdict(list)
    for r in results:
        counts = tuple(r.stride_counts.get(b, -1) for b in bases)
        families[counts].append(r.p)

    # Sort by family size
    sorted_families = sorted(families.items(), key=lambda x: -len(x[1]))

    print(f"\nUnique fingerprint patterns: {len(families)}")
    print("\nTop 20 largest families:")
    for i, (pattern, primes) in enumerate(sorted_families[:20]):
        pattern_str = ", ".join(f"b{b}:{c}" for b, c in zip(bases, pattern))
        print(f"  [{pattern_str}]: {len(primes)} primes")
        if len(primes) <= 5:
            print(f"    {primes}")


# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description='Sweep primes for reptend structure')
    parser.add_argument('--max', type=int, default=1000, help='Maximum prime to analyze')
    parser.add_argument('--bases', type=str, default='2,7,10,12', help='Comma-separated bases')
    parser.add_argument('--output', type=str, default=None, help='Output CSV file')
    parser.add_argument('--quiet', action='store_true', help='Minimal output')
    args = parser.parse_args()

    bases = [int(b) for b in args.bases.split(',')]

    print("=" * 70)
    print(f"PRIME SWEEP: Analyzing primes up to {args.max}")
    print(f"Bases: {bases}")
    print("=" * 70)

    results = sweep_primes(args.max, bases, verbose=not args.quiet)

    if args.output:
        write_csv(results, bases, args.output)
        print(f"\nResults written to {args.output}")

    if not args.quiet:
        print_summary_stats(results, bases)
        print_fingerprint_families(results, bases)
