#!/usr/bin/env python3
"""
WORKING BACKWARDS: Proving Reptends Terminate

This script demonstrates that we can take ANY reptend and work backwards
to prove it encodes a finite geometric sequence that must terminate.

The "infinite" repeating decimal is proven finite by construction.

Authors: Mike & Claude
Date: December 2025
"""

from decimal import Decimal, getcontext
getcontext().prec = 500

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
    
    # Step 4: The termination argument
    print(f"\nStep 4: THE TERMINATION PROOF")
    print(f"  ─" * 30)
    print(f"""
  The remainder sequence is: {k}^0, {k}^1, ..., {k}^{n-1} (mod {p})
  
  This is a FINITE sequence of {n} distinct values.
  
  At step {n}: {k}^{n} ≡ 1 (mod {p})
  
  The sequence MUST terminate because:
    • The orbit of {k} in (Z/{p}Z)* has exactly {n} elements
    • After {n} steps, we've visited every element in the orbit
    • The next step returns to 1 (nowhere new to go)
    
  The "infinite" decimal 0.{reptend}{reptend}...
  is just this finite {n}-step tour on infinite repeat.
  
  ════════════════════════════════════════════════════════════════════
  CONCLUSION: The reptend encodes {n} powers of {k}.
              The progression TERMINATES at {k}^{n-1} = {pow(k, n-1, p)}.
              Then it cycles forever, but the CONTENT is finite.
  ════════════════════════════════════════════════════════════════════
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

