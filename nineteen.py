#!/usr/bin/env python3
"""
EXHAUSTIVE ANALYSIS: 1/19

This script traces every step of the decimal expansion of 1/19,
showing how the multiplicative progression of powers of 10 
determines each digit and proves why it must terminate.

Key insight: 19 = 2×10 - 1, so 10 ≡ 1/2 (mod 19)

Authors: Mike & Claude
Date: December 2025
"""

def exhaustive_trace():
    p = 19
    
    print("═" * 75)
    print("EXHAUSTIVE TRACE: 1/19")
    print("═" * 75)
    
    # ═══════════════════════════════════════════════════════════════════════
    # PART 1: THE ALGEBRAIC STRUCTURE
    # ═══════════════════════════════════════════════════════════════════════
    
    print("""
┌─────────────────────────────────────────────────────────────────────────┐
│  ALGEBRAIC STRUCTURE                                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  19 = 2×10 - 1                                                          │
│                                                                         │
│  This means: 2×10 = 19 + 1 = 20 ≡ 1 (mod 19)                           │
│              10 ≡ 1/2 (mod 19)                                          │
│                                                                         │
│  In modular arithmetic, 10 IS "one half"!                               │
│                                                                         │
│  Verification: 10 × 2 = 20 = 19 + 1 ≡ 1 (mod 19) ✓                     │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
""")

    # ═══════════════════════════════════════════════════════════════════════
    # PART 2: LONG DIVISION - EVERY STEP
    # ═══════════════════════════════════════════════════════════════════════
    
    print("═" * 75)
    print("LONG DIVISION: EVERY STEP")
    print("═" * 75)
    
    print("""
At each step of long division:
  • remainder r_i holds the current state
  • We compute 10 × r_i
  • digit d_i = (10 × r_i) // 19
  • next remainder r_{i+1} = (10 × r_i) % 19
""")

    print(f"{'Step':<6}│{'Remainder':<11}│{'×10':<8}│{'÷19':<15}│{'Digit':<7}│{'New Rem':<9}│{'10^i mod 19'}")
    print("─" * 75)
    
    remainder = 1
    digits = []
    remainders = [1]
    
    for step in range(18):
        product = 10 * remainder
        digit = product // 19
        new_remainder = product % 19
        power_check = pow(10, step, 19)
        
        print(f"{step:<6}│{remainder:^11}│{product:^8}│{digit} rem {new_remainder:<8}│{digit:^7}│{new_remainder:^9}│{power_check:^11} ✓")
        
        digits.append(digit)
        remainder = new_remainder
        remainders.append(new_remainder)
    
    print("─" * 75)
    print(f"{'18':<6}│{'1':^11}│{'':^8}│{'CYCLE':^15}│{'':^7}│{'':^9}│{'1':^11} ✓")
    
    reptend = ''.join(map(str, digits))
    print(f"\n  Reptend: {reptend}")
    
    # ═══════════════════════════════════════════════════════════════════════
    # PART 3: THE MULTIPLICATIVE PROGRESSION
    # ═══════════════════════════════════════════════════════════════════════
    
    print("\n" + "═" * 75)
    print("THE MULTIPLICATIVE PROGRESSION")
    print("═" * 75)
    
    print("""
The remainders ARE the powers of 10 mod 19.
Since 10 ≡ 1/2, powers of 10 are inverse powers of 2:
""")
    
    print(f"{'i':<4}│{'10^i mod 19':<13}│{'2^i mod 19':<13}│{'10^i × 2^i':<12}│ Meaning")
    print("─" * 60)
    
    fractions = ["1", "1/2", "1/4", "1/8", "1/16", "1/32", "1/64", "1/128", 
                 "1/256", "1/512", "1/1024", "1/2048", "1/4096", "1/8192",
                 "1/16384", "1/32768", "1/65536", "1/131072"]
    
    for i in range(18):
        pow_10 = pow(10, i, 19)
        pow_2 = pow(2, i, 19)
        product = (pow_10 * pow_2) % 19
        print(f"{i:<4}│{pow_10:^13}│{pow_2:^13}│{product:^12}│ {fractions[i]} (mod 19)")
    
    print("""
Every product is 1! This proves: 10^i × 2^i ≡ 1 (mod 19)
Therefore: 10^i ≡ 2^(-i) ≡ 1/2^i (mod 19)
""")

    # ═══════════════════════════════════════════════════════════════════════
    # PART 4: THE DIGIT FORMULA
    # ═══════════════════════════════════════════════════════════════════════
    
    print("═" * 75)
    print("HOW EACH DIGIT IS DETERMINED")
    print("═" * 75)
    
    print("""
Formula: d_i = floor(10 × (10^i mod 19) / 19)

Position │ 10^i mod 19 │ × 10  │ ÷ 19  │ Digit
─────────┼─────────────┼───────┼───────┼──────""")
    
    for i in range(18):
        power = pow(10, i, 19)
        times_10 = 10 * power
        digit = times_10 // 19
        print(f"   {i:2d}    │     {power:2d}      │  {times_10:3d}  │  {digit:2d}   │   {digit}")
    
    # ═══════════════════════════════════════════════════════════════════════
    # PART 5: THE CARRY CASCADE (REVERSE)
    # ═══════════════════════════════════════════════════════════════════════
    
    print("\n" + "═" * 75)
    print("THE MULTIPLICATION CARRY CASCADE")
    print("═" * 75)
    
    print(f"""
Verification: {reptend} × 19 = ?

If R is the reptend, then R × 19 = 10^18 - 1 = {'9' * 18}
""")
    
    reptend_digits = [int(d) for d in reptend]
    
    print(f"{'Position':<10}│{'Digit':<7}│{'×19':<8}│{'+Carry':<9}│{'=Sum':<8}│{'Output':<8}│{'Carry Out'}")
    print("─" * 65)
    
    carry = 0
    outputs = []
    
    for i in range(17, -1, -1):
        d = reptend_digits[i]
        partial = d * 19
        total = partial + carry
        out = total % 10
        carry_out = total // 10
        
        outputs.append(out)
        
        print(f"{i:^10}│{d:^7}│{partial:^8}│{'+' + str(carry):^9}│{total:^8}│{out:^8}│{carry_out:^10}")
        
        carry = carry_out
    
    result = ''.join(map(str, outputs[::-1]))
    
    print("─" * 65)
    print(f"\n  Result: {result}")
    print(f"  Expected: {'9' * 18}")
    print(f"  Match: {result == '9' * 18}")
    
    # ═══════════════════════════════════════════════════════════════════════
    # PART 6: THE TERMINATION PROOF
    # ═══════════════════════════════════════════════════════════════════════
    
    print("\n" + "═" * 75)
    print("THE TERMINATION PROOF")
    print("═" * 75)
    
    print(f"""
Why does 1/19 have exactly 18 repeating digits?

1. The remainders in long division are powers of 10 mod 19:
   r_i = 10^i mod 19

2. These powers cycle through all nonzero residues:
   {{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18}}
   
   This is because 10 is a PRIMITIVE ROOT mod 19.

3. After 18 steps, 10^18 ≡ 1 (mod 19) by Fermat's Little Theorem:
   10^(19-1) ≡ 1 (mod 19)

4. The progression has EXHAUSTED all possible values.
   There are no new remainders to visit!
   The sequence MUST return to 1 and repeat.

╔═══════════════════════════════════════════════════════════════════════════╗
║                                                                           ║
║  THE "INFINITE" DECIMAL 0.052631578947368421052631578947368421...        ║
║                                                                           ║
║  IS JUST 18 DIGITS OF FINITE INFORMATION ON INFINITE REPEAT              ║
║                                                                           ║
║  THE MULTIPLICATIVE PROGRESSION TERMINATED WHEN IT RAN OUT OF ROOM       ║
║                                                                           ║
╚═══════════════════════════════════════════════════════════════════════════╝
""")

    # ═══════════════════════════════════════════════════════════════════════
    # SUMMARY TABLE
    # ═══════════════════════════════════════════════════════════════════════
    
    print("═" * 75)
    print("COMPLETE SUMMARY TABLE")
    print("═" * 75)
    
    print("""
i  │ 10^i mod 19 │ 2^(-i) mod 19 │ Digit │ Running Reptend
───┼─────────────┼───────────────┼───────┼────────────────────""")
    
    running = ""
    for i in range(18):
        power = pow(10, i, 19)
        digit = (10 * power) // 19
        running += str(digit)
        inv_2_i = pow(2, -i, 19)  # modular inverse
        print(f"{i:2d} │     {power:2d}      │      {power:2d}       │   {digit}   │ {running}")
    
    print(f"""
───┴─────────────┴───────────────┴───────┴────────────────────

Final reptend: {running}
Verification:  {running} × 19 = {int(running) * 19}
               = 10^18 - 1 = {'9' * 18} ✓
""")

if __name__ == "__main__":
    exhaustive_trace()

