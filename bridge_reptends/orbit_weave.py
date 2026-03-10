#!/usr/bin/env python3
"""
Algebraic decomposition of reptend integers.

For a purely periodic modulus M and block base B, write

    B = qM + k, with 0 <= k < M.

Then

    1/M = q/(B-k) = (q/B) * 1/(1-k/B) = Σ q*k^j / B^(j+1).

The reptend integer also decomposes as

    R = W + F

where:
- R = (B^L - 1)/M
- W = (B^L - k^L)/M
- F = (k^L - 1)/M
- L = ord_M(B)

The labels "orbit weave" for W and "closure flux" for F are optional
terminology for this standard algebraic split.

Authors: Mike & Claude
Date: December 2025
"""

from dataclasses import dataclass
from math import gcd, log10
from typing import Optional

from .analysis import multiplicative_order


# =============================================================================
# Number Theory Utilities
# =============================================================================

def factorize(n: int) -> dict[int, int]:
    """
    Return prime factorization as {prime: exponent} dict.

    Example: factorize(360) = {2: 3, 3: 2, 5: 1}
    """
    if n <= 1:
        return {}
    factors: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def phi(n: int) -> int:
    """
    Euler's totient function: count of integers 1..n coprime to n.

    phi(p) = p-1 for prime p
    phi(p^k) = p^(k-1) * (p-1)
    phi(mn) = phi(m) * phi(n) when gcd(m,n) = 1
    """
    if n <= 0:
        return 0
    if n == 1:
        return 1
    factors = factorize(n)
    result = n
    for p in factors:
        result = (result // p) * (p - 1)
    return result


def carmichael_lambda(n: int) -> int:
    """
    Carmichael function: smallest m such that a^m ≡ 1 (mod n) for all a coprime to n.

    For primes: lambda(p) = p-1
    For prime powers: lambda(p^k) = p^(k-1)*(p-1), except lambda(2^k) = 2^(k-2) for k >= 3
    For composites: lambda(n) = lcm of lambda over prime power factors

    This is the "universal exponent" for (Z/nZ)*.
    """
    if n <= 0:
        return 0
    if n == 1:
        return 1

    factors = factorize(n)

    def lambda_prime_power(p: int, k: int) -> int:
        if p == 2:
            if k == 1:
                return 1
            elif k == 2:
                return 2
            else:  # k >= 3
                return 2 ** (k - 2)
        else:
            return (p - 1) * (p ** (k - 1))

    def lcm(a: int, b: int) -> int:
        return a * b // gcd(a, b)

    result = 1
    for p, k in factors.items():
        result = lcm(result, lambda_prime_power(p, k))
    return result


def strip_base_factors(n: int, base: int = 10) -> tuple[int, dict[int, int]]:
    """
    Remove all factors of base from n.

    Returns (M, removed) where:
    - M is n with all base factors removed (gcd(M, base) = 1)
    - removed is {prime: exponent} of the removed factors

    For base 10: strip_base_factors(97) = (97, {})
                 strip_base_factors(200) = (1, {2: 3, 5: 2})
    """
    base_factors = factorize(base)
    removed: dict[int, int] = {}
    M = n

    for p in base_factors:
        count = 0
        while M % p == 0:
            M //= p
            count += 1
        if count > 0:
            removed[p] = count

    return M, removed


def ceil_div(x: int, y: int) -> int:
    """Ceiling division: smallest n such that n*y >= x."""
    return (x + y - 1) // y


# =============================================================================
# Mode Selection
# =============================================================================

def best_bridge_mode(M: int, base: int = 10, kmax: int = 5, mmax: int = 24) -> Optional[int]:
    """
    Find block width m where k = base^m mod M is small (1 <= k <= kmax).

    A small k means base^m ≈ some multiple of M, giving clean block structure.
    These are "bridge" modes where the gap is small.

    Returns None if no such m exists within mmax.
    """
    if gcd(M, base) != 1:
        return None

    for m in range(1, mmax + 1):
        B = base ** m
        if B <= M:
            continue
        k = B % M
        if 1 <= k <= kmax:
            return m
    return None


def near_power_mode(N: int, base: int = 10) -> tuple[int, int]:
    """
    Find the "near power" mode: m = digits(N), d = base^m - N.

    For N = 97: m = 2, d = 100 - 97 = 3
    For N = 997: m = 3, d = 1000 - 997 = 3

    This is a natural mode when N is close to a power of base.
    """
    if N <= 0:
        return 1, base - N
    m = len(str(N)) if base == 10 else int(log10(N) / log10(base)) + 1
    B = base ** m
    d = B - N
    return m, d


def find_good_modes(
    M: int,
    base: int = 10,
    kmax: int = 5,
    mmax: int = 24,
    sort_by: str = "k"
) -> list[tuple[int, int, int]]:
    """
    Find ALL block widths m where k = base^m mod M is small.

    Returns list of (m, k, q) tuples where:
    - m: block width (exponent)
    - k: bridge residue (k = B mod M, where B = base^m)
    - q: quotient in B = qM + k

    The canonical decomposition B = qM + k gives:
        1/M = q/(B-k)

    Parameters:
        M: modulus (should be coprime to base)
        base: number base (default 10)
        kmax: maximum acceptable bridge residue
        mmax: maximum block width to search
        sort_by: "k" (smallest k first), "m" (smallest m first), or "ratio" (k/M)

    Example:
        >>> find_good_modes(19, base=10, kmax=5)
        [(18, 1, 52631578947368421), ..., (2, 5, 5), ...]
        # In particular, m=2 gives 100 = 5×19 + 5.

        >>> find_good_modes(37, base=10, kmax=5)
        [(3, 1, 27)]
        # 1000 = 27×37 + 1, so k=1, q=27
    """
    if gcd(M, base) != 1:
        return []

    modes = []
    for m in range(1, mmax + 1):
        B = base ** m
        if B <= M:
            continue
        k = B % M
        if 1 <= k <= kmax:
            q = (B - k) // M  # Since k = B mod M, (B-k) is divisible by M
            modes.append((m, k, q))

    # Sort based on preference
    if sort_by == "k":
        modes.sort(key=lambda x: (x[1], x[0]))  # k first, then m
    elif sort_by == "m":
        modes.sort(key=lambda x: x[0])
    elif sort_by == "ratio":
        modes.sort(key=lambda x: x[1] / M)

    return modes


def canonical_fraction(M: int, m: int, base: int = 10) -> tuple[int, int, str]:
    """
    Show the canonical fraction representation 1/M = q/(B-k).

    For modulus M with block width m:
    - B = base^m
    - k = B mod M (bridge residue)
    - q = (B - k) / M (quotient)

    Since B = qM + k, we have B - k = qM.
    So: 1/M = q/(qM) = q/(B-k)

    Returns (q, B-k, explanation_string)

    Example:
        >>> canonical_fraction(19, 2, base=10)
        (5, 95, "1/19 = 5/95 = 5/(100-5)")

        >>> canonical_fraction(37, 3, base=10)
        (27, 999, "1/37 = 27/999 = 27/(1000-1)")
    """
    B = base ** m
    k = B % M
    q = (B - k) // M
    denominator = B - k  # = qM

    explanation = f"1/{M} = {q}/{denominator} = {q}/({B}-{k})"

    return q, denominator, explanation


# =============================================================================
# Block Utilities
# =============================================================================

def blocks_of_unit_fraction(N: int, m: int, nblocks: int, base: int = 10) -> list[str]:
    """
    Compute digit blocks from long division of 1/N.

    Each block has m digits (base-10 by default).
    Returns list of zero-padded block strings.
    """
    B = base ** m
    r = 1 % N
    blocks: list[str] = []

    for _ in range(nblocks):
        r *= B
        q = r // N
        r %= N
        blocks.append(str(q).zfill(m))

    return blocks


def int_to_blocks(x: int, m: int, L: int) -> list[str]:
    """
    Convert integer x to L blocks of m digits each.

    Pads with leading zeros to fill m*L digits total.
    """
    s = str(x).zfill(m * L)
    return [s[i:i+m] for i in range(0, len(s), m)]


# =============================================================================
# Reptend Integer Decomposition
# =============================================================================

def reptend_integer(B: int, L: int, M: int) -> int:
    """
    R = (B^L - 1) / M

    The reptend as an integer. For base B with orbit length L,
    this is the repeating part of 1/M written as a single integer.

    Requires: B^L ≡ 1 (mod M)
    """
    BL = pow(B, L)
    assert (BL - 1) % M == 0, f"B^L - 1 not divisible by M"
    return (BL - 1) // M


def weave(B: int, L: int, k: int, M: int) -> int:
    """
    W = (B^L - k^L) / M

    Main body term in the algebraic decomposition.

    Requires: B^L - k^L ≡ 0 (mod M)
    """
    BL = pow(B, L)
    kL = pow(k, L)
    diff = BL - kL
    assert diff % M == 0, f"B^L - k^L not divisible by M"
    return diff // M


def flux(k: int, L: int, M: int) -> int:
    """
    F = (k^L - 1) / M

    Correction term in the algebraic decomposition.

    Requires: k^L ≡ 1 (mod M)
    """
    kL = pow(k, L)
    assert (kL - 1) % M == 0, f"k^L - 1 not divisible by M"
    return (kL - 1) // M


def verify_decomposition(B: int, L: int, k: int, M: int) -> bool:
    """
    Verify that R = W + F holds.

    Returns True if the decomposition is valid.
    """
    R = reptend_integer(B, L, M)
    W = weave(B, L, k, M)
    F = flux(k, L, M)
    return R == W + F


# =============================================================================
# Analysis Dataclass and Main Function
# =============================================================================

@dataclass
class OrbitWeaveAnalysis:
    """Complete orbit weave analysis for a modulus."""
    N: int                      # Original input
    M: int                      # Reduced modulus (base factors stripped)
    base: int                   # Base (default 10)
    m: int                      # Block width (mode)
    B: int                      # Block base = base^m
    k: int                      # Bridge residue = B mod M
    L: int                      # Orbit length = ord_M(B)
    digits: int                 # Total digits = m * L

    # Preperiod info (from stripped base factors)
    preperiod_blocks: int       # Number of preperiod blocks
    stripped_factors: dict      # Factors removed from N

    # The decomposition (None if too large to compute)
    R: Optional[int] = None     # Reptend integer
    W: Optional[int] = None     # Orbit weave
    F: Optional[int] = None     # Closure flux

    # Analysis flags
    too_large: bool = False     # True if digits > threshold
    terminates: bool = False    # True if M = 1 (no reptend)

    # Bridge factor for geometric series interpretation
    # 1/M = t * sum(k^i / B^(i+1)) where t = (B-k)/M
    bridge_factor: Optional[int] = None

    def blocks(self, source: str = "R", n: int = 10) -> list[str]:
        """Get first n blocks of R, W, or F."""
        if self.too_large or self.terminates:
            return []
        x = {"R": self.R, "W": self.W, "F": self.F}.get(source)
        if x is None:
            return []
        return int_to_blocks(x, self.m, self.L)[:n]

    @property
    def q(self) -> Optional[int]:
        """
        Quotient in the canonical decomposition B = qM + k.

        Alias for bridge_factor, with clearer semantics in the
        "Orbit Core" framework where:
        - B = base^m (block base)
        - k = B mod M (bridge residue)
        - q = (B - k) / M (quotient)

        The identity 1/M = q/(B-k) = q/(qM) follows directly.
        """
        return self.bridge_factor


def orbit_weave_analysis(
    N: int,
    base: int = 10,
    prefer_m: Optional[int] = None,
    kmax: int = 5,
    max_digits: int = 6000
) -> OrbitWeaveAnalysis:
    """
    Full orbit weave analysis for 1/N.

    Parameters:
    - N: The denominator to analyze
    - base: Number base (default 10)
    - prefer_m: Force specific block width (default: auto-select)
    - kmax: Maximum bridge residue for mode selection
    - max_digits: Skip large integer computation if digits exceed this

    Returns OrbitWeaveAnalysis with decomposition R = W + F.
    """
    # Strip base factors to get purely periodic modulus
    M, stripped = strip_base_factors(N, base)

    # Handle terminating case
    if M == 1:
        m, _ = near_power_mode(N, base)
        return OrbitWeaveAnalysis(
            N=N, M=1, base=base, m=m, B=base**m, k=0, L=0, digits=0,
            preperiod_blocks=0, stripped_factors=stripped,
            terminates=True
        )

    # Check coprimality
    if gcd(M, base) != 1:
        raise ValueError(f"M={M} not coprime to base={base} after stripping")

    # Choose mode (block width m)
    if prefer_m is not None:
        m = prefer_m
    else:
        m_bridge = best_bridge_mode(M, base, kmax=kmax)
        if m_bridge is not None:
            m = m_bridge
        else:
            m, _ = near_power_mode(N, base)

    B = base ** m
    k = B % M

    # Compute orbit length
    L = multiplicative_order(B, M)
    if L is None or L == 0:
        # Shouldn't happen if M coprime to base
        L = carmichael_lambda(M)  # Fallback

    digits = m * L

    # Preperiod blocks from stripped factors
    max_stripped_exp = max(stripped.values()) if stripped else 0
    preperiod_blocks = ceil_div(max_stripped_exp, m) if max_stripped_exp > 0 else 0

    # Check size limit
    if digits > max_digits:
        return OrbitWeaveAnalysis(
            N=N, M=M, base=base, m=m, B=B, k=k, L=L, digits=digits,
            preperiod_blocks=preperiod_blocks, stripped_factors=stripped,
            too_large=True
        )

    # Compute the decomposition
    BL = pow(B, L)
    kL = pow(k, L)

    R = (BL - 1) // M
    W = (BL - kL) // M
    F = (kL - 1) // M

    # Verify decomposition
    assert R == W + F, f"Decomposition failed: R={R}, W+F={W+F}"

    # Bridge factor for geometric series
    bridge_factor = (B - k) // M if (B - k) % M == 0 else None

    return OrbitWeaveAnalysis(
        N=N, M=M, base=base, m=m, B=B, k=k, L=L, digits=digits,
        preperiod_blocks=preperiod_blocks, stripped_factors=stripped,
        R=R, W=W, F=F, bridge_factor=bridge_factor
    )


# =============================================================================
# Skeleton + Carry Analysis
# =============================================================================

def raw_series_blocks(q: int, k: int, n_blocks: int) -> list[int]:
    """
    Exact geometric coefficients q*k^0, q*k^1, q*k^2, ...

    These are the block coefficients in

        1/N = q/(B-k) = Σ q*k^j / B^(j+1).

    In the special case q = 1 (equivalently N = B - k), these reduce to
    literal powers of k.
    """
    return [q * (k ** j) for j in range(n_blocks)]


def raw_power_blocks(k: int, m: int, n_blocks: int) -> list[int]:
    """
    Raw geometric skeleton in the special q = 1 case: k^0, k^1, k^2, ...

    This is the bridge case N = B - k, where the exact coefficients are
    literal powers of k.
    """
    return [k**j for j in range(n_blocks)]


def apply_carry(raw_blocks: list[int], B: int) -> list[str]:
    """
    Apply carry propagation from right to left.

    When raw_block[j] >= B, the overflow carries into block[j-1].
    Returns list of m-digit block strings after carry stabilization.
    """
    m = len(str(B - 1))  # digit width
    n = len(raw_blocks)

    # Work with a copy, propagate carry from right to left
    blocks = list(raw_blocks)

    # Multiple passes until stable (carry can cascade)
    changed = True
    while changed:
        changed = False
        for j in range(n - 1, 0, -1):  # right to left, skip leftmost
            if blocks[j] >= B:
                carry = blocks[j] // B
                blocks[j] = blocks[j] % B
                blocks[j - 1] += carry
                changed = True

    # Format as zero-padded strings
    return [str(b).zfill(m) for b in blocks]


def skeleton_vs_actual(N: int, base: int = 10, n_blocks: int = 12,
                       prefer_m: int | None = None) -> dict:
    """
    Compare exact geometric coefficients to actual long-division blocks.

    Parameters:
    - N: denominator
    - base: number base (default 10)
    - n_blocks: number of blocks to compute
    - prefer_m: force specific block width (None = auto-detect near-power mode)

    Returns dict with:
    - raw: the q*k^j coefficient blocks (before carry)
    - carried: raw blocks with carry applied
    - actual: true long-division blocks
    - q: quotient in B = qN + k
    - overflow_at: first index where q*k^j >= B
    - flux_visible: indices where carried != raw (showing carry effect)
    """
    M, stripped = strip_base_factors(N, base)
    if M == 1:
        return {"terminates": True}

    # Use near-power mode by default (shows the skeleton most clearly)
    if prefer_m is not None:
        m = prefer_m
    else:
        m, d = near_power_mode(N, base)
        # Use near-power mode when d is small (< 20), otherwise find bridge mode
        if d > 20:
            m_bridge = best_bridge_mode(M, base, kmax=12)
            if m_bridge is not None:
                m = m_bridge

    B = base ** m
    k = B % N
    q = (B - k) // N

    # Exact geometric coefficients in 1/N = q/(B-k)
    raw = raw_series_blocks(q, k, n_blocks)

    # Apply carry
    carried = apply_carry(raw, B)

    # Actual long-division blocks
    actual = blocks_of_unit_fraction(N, m, n_blocks, base)

    # Find first overflow
    overflow_at = None
    for j, r in enumerate(raw):
        if r >= B:
            overflow_at = j
            break

    # Find where carry changed things
    raw_strs = [str(r).zfill(m) if r < B else f"[{r}]" for r in raw]
    flux_visible = [j for j in range(n_blocks) if carried[j] != raw_strs[j].strip("[]").zfill(m)]

    return {
        "N": N,
        "M": M,
        "m": m,
        "B": B,
        "k": k,
        "q": q,
        "raw": raw,
        "raw_display": raw_strs,
        "carried": carried,
        "actual": actual,
        "overflow_at": overflow_at,
        "flux_visible": flux_visible,
        "terminates": False,
    }


def print_skeleton_analysis(N: int, base: int = 10, n_blocks: int = 12,
                           prefer_m: int | None = None) -> None:
    """
    Print the skeleton + carry analysis for 1/N.

    Shows:
    - Raw power blocks k^j (geometric skeleton)
    - Carried blocks (after overflow correction)
    - Actual blocks (from long division)
    - Where they diverge
    """
    result = skeleton_vs_actual(N, base, n_blocks, prefer_m)

    if result.get("terminates"):
        print(f"\n1/{N} terminates (no reptend)")
        return

    print(f"\n{'='*60}")
    print(f"SKELETON + CARRY ANALYSIS: 1/{N}")
    print(f"{'='*60}")

    print(f"Mode m={result['m']}, B=10^{result['m']}={result['B']}")
    print(f"Write B = qN + k with q={result['q']} and k={result['k']}")
    print(f"  {result['B']} = {result['q']}×{N} + {result['k']}")
    if result['M'] != N:
        print(f"Coprime part M = {result['M']} (stripped base factors)")

    if result["q"] == 1:
        print(f"\nRaw skeleton (special q=1 case, coefficients k^j):")
    else:
        print(f"\nRaw skeleton (exact coefficients q·k^j):")
    print(f"  {' '.join(result['raw_display'][:n_blocks])}")

    if result['overflow_at'] is not None:
        print(f"\n  First overflow at j={result['overflow_at']}: "
              f"coefficient = {result['raw'][result['overflow_at']]} >= {result['B']}")

    print(f"\nAfter carry propagation:")
    print(f"  {' '.join(result['carried'][:n_blocks])}")

    print(f"\nActual (long division):")
    print(f"  {' '.join(result['actual'][:n_blocks])}")

    # Compare and find match region
    match_count = 0
    for c, a in zip(result['carried'], result['actual']):
        if c == a:
            match_count += 1
        else:
            break

    total = min(len(result['carried']), len(result['actual']))
    if match_count == total:
        print(f"\n✓ Carried skeleton matches actual blocks perfectly!")
    else:
        print(f"\n✓ Skeleton valid for first {match_count} blocks")
        print(f"  Blocks 0-{match_count-1}: geometric coefficients + carry = actual digits")
        print(f"  Block {match_count}+: cyclic closure effects (correction term)")
        print(f"  (The infinite geometric series diverges from finite reptend)")


# =============================================================================
# Display and Demo
# =============================================================================

def print_analysis(ow: OrbitWeaveAnalysis, nblocks: int = 10) -> None:
    """Pretty-print the algebraic decomposition analysis."""
    print(f"\nN = {ow.N}")

    if ow.stripped_factors:
        factors_str = " * ".join(f"{p}^{e}" for p, e in ow.stripped_factors.items())
        print(f"  stripped base factors: {factors_str}")
        print(f"  purely periodic modulus M = {ow.M}")

    if ow.terminates:
        print("  terminates (no reptend)")
        return

    print(f"  mode m = {ow.m}, B = {ow.base}^{ow.m} = {ow.B}")
    print(f"  bridge residue k = B mod M = {ow.k}")
    print(f"  orbit length L = ord_M(B) = {ow.L} blocks = {ow.digits} digits")

    if ow.preperiod_blocks > 0:
        print(f"  preperiod: {ow.preperiod_blocks} block(s)")

    if ow.too_large:
        print(f"  [skipping large integers: {ow.digits} digits]")
        return

    # Show blocks
    showL = min(ow.L, nblocks)
    Rb = ow.blocks("R", showL)
    Wb = ow.blocks("W", showL)

    print(f"  reptend R blocks: {' '.join(Rb)}{'...' if ow.L > showL else ''}")
    print(f"  body term W ('weave') blocks: {' '.join(Wb)}{'...' if ow.L > showL else ''}")
    print(f"  correction term F ('closure flux') = {ow.F}")

    if ow.bridge_factor is not None:
        print(f"  bridge factor t = (B-k)/M = {ow.bridge_factor}")

    # Show first few powers of k
    powers = [pow(ow.k, i, ow.M) for i in range(min(8, ow.L))]
    print(f"  k^i mod M: {powers}...")


if __name__ == "__main__":
    import sys

    print("=" * 70)
    print("ALGEBRAIC REPTEND DECOMPOSITION")
    print("=" * 70)

    # Default test cases
    if len(sys.argv) >= 2:
        Ns = [int(x) for x in sys.argv[1:]]
    else:
        Ns = [7, 19, 97, 96, 996, 9996, 199, 1999, 139]

    for N in Ns:
        ow = orbit_weave_analysis(N)
        print_analysis(ow)

        # Verify decomposition
        if not ow.terminates and not ow.too_large:
            assert ow.R == ow.W + ow.F, "Decomposition verification failed!"

    print("\n" + "=" * 70)
    print("All decompositions verified: R = W + F")
    print("=" * 70)
