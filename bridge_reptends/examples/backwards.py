#!/usr/bin/env python3
"""
Working backwards: Proving reptends terminate.

Given only the reptend of 1/p, we recover the remainder sequence and show
it forms a geometric progression k^0, k^1, ..., k^(n-1) in (ℤ/pℤ)×.

By Lagrange, ord(k) divides p-1, so the orbit is finite. The "infinite"
decimal is this finite orbit on infinite repeat.

Coset structure: the remainders traverse either the QR or NQR coset,
depending on k. When ord(k) = (p-1)/2, k generates exactly QR.

Authors: Mike & Claude
Date: December 2025
"""

from decimal import Decimal, getcontext
getcontext().prec = 500

from bridge_reptends import is_qr, coset_of


def get_reptend(p):
    """Get the reptend of 1/p"""
    dec = str(Decimal(1) / Decimal(p))[2:]

    # Find the period
    for period in range(1, p):
        if len(dec) >= 2 * period:
            if all(dec[i] == dec[i % period] for i in range(2 * period)):
                return dec[:period]
    return dec[:p-1]


def work_backwards(p, reptend):
    """
    Given a reptend, work backwards to recover the remainder sequence.
    Returns the sequence of remainders (which are powers of some k).
    """
    digits = [int(d) for d in reptend]
    n = len(digits)

    # The key constraint: r_n = r_0 = 1 (periodicity)
    remainders = [None] * (n + 1)
    remainders[n] = 1

    # Work backwards
    for i in range(n - 1, -1, -1):
        d = digits[i]
        r_next = remainders[i + 1]

        # Find r_i such that (10 × r_i) // p = d and (10 × r_i) % p = r_next
        for r in range(1, p):
            if (10 * r) // p == d and (10 * r) % p == r_next:
                remainders[i] = r
                break

    return remainders[:-1]


def find_generator(remainders, p):
    """Find the constant ratio k such that r_{i+1} = k * r_i mod p"""
    if len(remainders) < 2:
        return None

    # k = r_1 * r_0^{-1} mod p
    r_0_inv = pow(remainders[0], p - 2, p)  # Fermat's little theorem
    k = (remainders[1] * r_0_inv) % p

    # Verify it's constant
    for i in range(len(remainders) - 1):
        r_i_inv = pow(remainders[i], p - 2, p)
        ratio = (remainders[i + 1] * r_i_inv) % p
        if ratio != k:
            return None

    return k


def prove_termination(p):
    """
    The complete backwards proof for 1/p.
    """
    print("=" * 70)
    print(f"BACKWARDS PROOF OF TERMINATION: 1/{p}")
    print("=" * 70)

    # Step 1: Get the reptend
    reptend = get_reptend(p)
    n = len(reptend)

    print(f"\nStep 1: The reptend of 1/{p}")
    print(f"  Reptend: {reptend}")
    print(f"  Length: {n} digits")

    # Step 2: Work backwards to get remainders
    remainders = work_backwards(p, reptend)

    print(f"\nStep 2: Working backwards from r_{n} = 1")
    print(f"  Recovered remainders: {remainders}")

    # Step 3: Find the generator
    k = find_generator(remainders, p)

    print(f"\nStep 3: Find the geometric structure")
    if k:
        print(f"  The remainders form powers of k = {k}")
        print(f"  Verification: {k}^i mod {p} = {[pow(k, i, p) for i in range(n)]}")
        match = remainders == [pow(k, i, p) for i in range(n)]
        print(f"  Match: {match}")

        # Add coset insight with Euler's criterion
        k_coset = coset_of(k, p)
        euler_result = pow(k, (p - 1) // 2, p)
        print(f"\n  Coset membership:")
        print(f"    k = {k}, and {k}^{(p-1)//2} ≡ {euler_result} (mod {p})")
        print(f"    By Euler's criterion, {k} ∈ {'QR' if euler_result == 1 else 'NQR'}.")
        if k_coset == 'QR':
            print(f"    Since k ∈ QR, powers k^i remain in QR (product of squares is a square).")
        else:
            print(f"    Since k ∈ NQR, powers k^i alternate between QR and NQR.")

    # Step 4: The termination argument
    print(f"\nStep 4: Termination")
    print(f"  {'─'*60}")
    print(f"""
  The remainder sequence is: {k}^0, {k}^1, ..., {k}^{n-1} (mod {p})

  This is a finite sequence of {n} distinct values.

  By Lagrange, ord({k}) divides |(ℤ/{p}ℤ)×| = {p-1}.
  Here ord({k}) = {n}, and indeed {n} | {p-1} (quotient {(p-1)//n}).

  At step {n}: {k}^{n} ≡ 1 (mod {p}), closing the orbit.

  The orbit of {k} has exactly {n} elements. After visiting all of them,
  the sequence returns to 1—there's nowhere else to go.

  The "infinite" decimal 0.{reptend}{reptend}...
  is this finite {n}-step orbit on infinite repeat.

  ────────────────────────────────────────────────────────────────────
  Summary: The reptend encodes {n} powers of {k}.
           The orbit closes at {k}^{n} ≡ 1.
           k = {k} ∈ {'QR' if is_qr(k, p) else 'NQR'}, so powers {'stay in QR' if is_qr(k, p) else 'alternate QR/NQR'}.
  ────────────────────────────────────────────────────────────────────
""")

    return k, n, remainders


# =============================================================================
# MAIN: Demonstrate with 1/7 and 1/41
# =============================================================================

if __name__ == "__main__":
    print("""
╔══════════════════════════════════════════════════════════════════════╗
║     WORKING BACKWARDS: PROVING REPTENDS ENCODE FINITE SEQUENCES      ║
╚══════════════════════════════════════════════════════════════════════╝

Given ONLY the reptend of 1/p, we can:
  1. Work backwards to recover the remainder sequence
  2. Show the remainders are powers of some k
  3. Prove the sequence must terminate when the orbit closes

This proves the "infinite" decimal is actually finite information.

┌────────────────────────────────────────────────────────────────────┐
│  MATHEMATICAL BACKGROUND                                           │
├────────────────────────────────────────────────────────────────────┤
│  The remainder sequence of 1/p lives in (ℤ/pℤ)×, which is cyclic  │
│  of order p − 1. Any orbit under multiplication by k must close:  │
│  by Lagrange, ord(k) ∣ p − 1, so k^n = 1 for some n ≤ p − 1.      │
│                                                                    │
│  The squaring map x ↦ x² has kernel {±1}, giving                  │
│      QR := { a² } with |QR| = (p−1)/2.                            │
│  Euler's criterion classifies: a ∈ QR ⟺ a^((p−1)/2) ≡ 1.         │
│                                                                    │
│  Thus (ℤ/pℤ)× partitions into exactly two cosets: QR and NQR.     │
└────────────────────────────────────────────────────────────────────┘
""")

    # 1/7 - the simplest case
    prove_termination(7)

    print("\n" + "=" * 70)
    print("A SECOND EXAMPLE: 1/41")
    print("=" * 70)

    # 1/41 - small orbit (only 5 elements)
    prove_termination(41)

    print("\n" + "=" * 70)
    print("A THIRD EXAMPLE: 1/37")
    print("=" * 70)

    # 1/37 - very small orbit (only 3 elements!)
    prove_termination(37)
