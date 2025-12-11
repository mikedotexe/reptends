"""
Quadratic residue reptend analysis.

This package provides tools for exploring the group-theoretic structure
underlying reptends (repeating decimal expansions). The key insight:
reptends aren't decimal curiosities—they're group theory wearing a
decimal costume.

Core functions:
    multiplicative_order - Compute ord_p(a)
    long_division_remainders - Get remainder sequence from 1/p
    find_generator - Find constant ratio k in geometric sequence
    is_qr_generator - Check if k generates QR subgroup
    find_qr_strides - Find all m where base^m is QR-generator
    analyze_prime - Complete analysis of a prime's reptend structure

Data classes:
    PrimeAnalysis - Complete analysis results for a prime

Example:
    >>> from qr_reptends import analyze_prime
    >>> analysis = analyze_prime(97, base=10)
    >>> print(f"ord_97(10) = {analysis.reptend_length}")
    ord_97(10) = 96
    >>> print(f"QR-strides: {analysis.qr_strides[:5]}...")
    QR-strides: [2, 6, 10, 14, 18]...

Authors: Mike & Claude
Date: December 2025
"""

from .analysis import (
    multiplicative_order,
    long_division_remainders,
    find_generator,
    is_qr_generator,
    find_qr_strides,
    analyze_prime,
    stride_fingerprint,
    PrimeAnalysis,
)

__all__ = [
    "multiplicative_order",
    "long_division_remainders",
    "find_generator",
    "is_qr_generator",
    "find_qr_strides",
    "analyze_prime",
    "stride_fingerprint",
    "PrimeAnalysis",
]

__version__ = "0.1.0"
