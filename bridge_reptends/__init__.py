"""
Bridge reptend analysis - geometric series structure in repeating decimals.

## The Core Insight (Universal)

For any N coprime to base B, with k = B mod N:

    1/N = (1/B) × 1/(1 - k/B) = Σ k^j / B^(j+1)

The digit blocks are **powers of k**: 1, k, k², k³, ...

When k is small ("bridge" denominators like N = 10² - 3 = 97), the power
pattern is visible for many blocks before carry disrupts it.

## The Three Layers

| Layer    | What                                    | Universal? |
|----------|-----------------------------------------|------------|
| Skeleton | Raw powers k^j                          | Yes, any N |
| Carry    | Overflow correction when k^j ≥ B^m      | Yes, any N |
| Closure  | Cyclic wrap after ord_N(B) blocks       | Yes, any N |

## The Prime Bonus

When N is prime, the multiplicative group (ℤ/pℤ)* splits into exactly
two cosets (QR and NQR). This explains:
- Why certain k values generate half the group
- The trichotomy (full/half/degenerate reptends)
- Base-invariant stride counts

But the skeleton structure works for 1/96, 1/996, 1/9996 just as well.

Core functions:
    # Universal (any N coprime to base)
    multiplicative_order - Compute ord_n(a)
    long_division_remainders - Get remainder sequence from 1/n
    orbit_weave_analysis - Algebraic decomposition R = W + F
    skeleton_vs_actual - Compare raw powers to actual blocks
    print_skeleton_analysis - Visualize skeleton + carry structure

    # Prime-specific (requires prime p)
    is_qr - Test quadratic residue membership (Euler's criterion)
    is_qr_generator - Check if k generates QR subgroup
    find_qr_strides - Find all m where base^m is QR-generator
    analyze_prime - Complete analysis of a prime's reptend structure
    analyze_coset_structure - Analyze coset/block structure

Example:
    >>> from bridge_reptends import print_skeleton_analysis
    >>> print_skeleton_analysis(996)  # Works for composite!
    # Shows: skeleton powers, carried values, actual long-division blocks

    >>> from bridge_reptends import analyze_prime, is_qr
    >>> analysis = analyze_prime(97, base=10)  # Prime-specific
    >>> print(f"3 is {'QR' if is_qr(3, 97) else 'NQR'} mod 97")
    3 is NQR mod 97

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

from .coset import (
    is_qr,
    coset_of,
    format_digit,
    find_block_structure,
    get_blocks,
    get_block_remainders,
    analyze_coset_structure,
    compare_coset_representatives,
    BlockStructure,
    Block,
    CosetAnalysis,
    DIGIT_CHARS,
)

from .orbit_weave import (
    orbit_weave_analysis,
    reptend_integer,
    weave,
    flux,
    verify_decomposition,
    best_bridge_mode,
    strip_base_factors,
    factorize,
    phi,
    carmichael_lambda,
    OrbitWeaveAnalysis,
    # Skeleton + carry analysis
    skeleton_vs_actual,
    print_skeleton_analysis,
    raw_power_blocks,
    apply_carry,
    # Orbit Core: good coordinates
    find_good_modes,
    canonical_fraction,
)

__all__ = [
    # analysis.py
    "multiplicative_order",
    "long_division_remainders",
    "find_generator",
    "is_qr_generator",
    "find_qr_strides",
    "analyze_prime",
    "stride_fingerprint",
    "PrimeAnalysis",
    # coset.py
    "is_qr",
    "coset_of",
    "format_digit",
    "find_block_structure",
    "get_blocks",
    "get_block_remainders",
    "analyze_coset_structure",
    "compare_coset_representatives",
    "BlockStructure",
    "Block",
    "CosetAnalysis",
    "DIGIT_CHARS",
    # orbit_weave.py
    "orbit_weave_analysis",
    "reptend_integer",
    "weave",
    "flux",
    "verify_decomposition",
    "best_bridge_mode",
    "strip_base_factors",
    "factorize",
    "phi",
    "carmichael_lambda",
    "OrbitWeaveAnalysis",
    "skeleton_vs_actual",
    "print_skeleton_analysis",
    "raw_power_blocks",
    "apply_carry",
    # Orbit Core: good coordinates
    "find_good_modes",
    "canonical_fraction",
]

__version__ = "0.2.0"
