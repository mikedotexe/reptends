/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.RemainderOrbit
import QRTour.PrimitiveRoots
import QRTour.Digits
import QRTour.Bridge

/-!
# Concrete Example: p = 97

This module instantiates the QR Tour theory for the canonical example:
- p = 97 (prime)
- B = 10 (decimal)
- m = 2 (stride)
- k = 10² mod 97 = 3

The key fact is that ord₉₇(3) = 48 = (97-1)/2, making 3 a generator of the
quadratic residue subgroup.

## Main Results

* `QRTour.Prime97.k_eq_three` - 10² ≡ 3 (mod 97)
* `QRTour.Prime97.order_of_three` - ord₉₇(3) = 48
* `QRTour.Prime97.qr_tour` - Application of the main theorem

## Computational Verification

In Lean, we can computationally verify facts like:
- 10² mod 97 = 100 mod 97 = 3
- 3^48 mod 97 = 1
- The 48 values 3⁰, 3¹, ..., 3⁴⁷ are all distinct mod 97
-/

namespace QRTour.Prime97

/-! ### Prime 97 -/

/-- 97 is prime. -/
instance : Fact (Nat.Prime 97) := ⟨by native_decide⟩

/-- 97 ≠ 2 (it's an odd prime). -/
theorem p_ne_two : (97 : ℕ) ≠ 2 := by decide

/-! ### Base-Stride Configuration -/

/-- The base-stride configuration for p=97, B=10, m=2. -/
def bs : BaseStride 97 where
  B := 10
  m := 2
  hB_coprime := by native_decide
  hm_pos := by decide

/-! ### Computational Verifications -/

/-- 10² mod 97 = 3 -/
example : (10 : ZMod 97) ^ 2 = 3 := by native_decide

/-- k = 3 as an element of ZMod 97 -/
theorem k_eq_three : (bs.k : ZMod 97) = 3 := by native_decide

/-- half 97 = 48 -/
example : half 97 = 48 := by native_decide

/-- 3^48 = 1 in (ZMod 97)ˣ -/
theorem three_pow_48_eq_one : (3 : ZMod 97) ^ 48 = 1 := by native_decide

/-- The first few remainders in the stride-2 sequence -/
example : strideRemainder bs 0 = 1 := by native_decide  -- 10^0 = 1
example : strideRemainder bs 1 = 3 := by native_decide  -- 10^2 = 100 ≡ 3
example : strideRemainder bs 2 = 9 := by native_decide  -- 10^4 ≡ 3² = 9
example : strideRemainder bs 3 = 27 := by native_decide -- 10^6 ≡ 3³ = 27
example : strideRemainder bs 4 = 81 := by native_decide -- 10^8 ≡ 3⁴ = 81

/-! ### Order of 3

Proving that ord₉₇(3) = 48 is the key fact. orderOf is not directly computable
with native_decide, so we use sorry as a placeholder.
-/

/-- 3 has order 48 in (ZMod 97)ˣ.

This is verified by checking:
1. 3^48 = 1 (so orderOf 3 | 48)
2. 3^k ≠ 1 for all proper divisors k of 48
-/
theorem order_of_three : orderOf (Units.mk0 (3 : ZMod 97) (by decide)) = 48 := by
  rw [orderOf_eq_iff (by decide : 0 < 48)]
  constructor
  · native_decide  -- 3^48 = 1
  · intro m hm hm_pos
    -- For m < 48 with m > 0, we need 3^m ≠ 1
    -- The only values we need to check are divisors of 48: 1, 2, 3, 4, 6, 8, 12, 16, 24
    interval_cases m <;> native_decide

/-! ### 3 is a Quadratic Residue

3 is a QR mod 97 because it's a power of 10, which is itself a QR.
-/

/-- 10² ≡ 3 (mod 97), so 3 is a quadratic residue.

We compute 10² = 100 ≡ 3 (mod 97).  -/
theorem three_is_square : IsSquare (3 : ZMod 97) := by
  use 10
  native_decide

/-! ### 3 is a QR Generator -/

/-- 3 (or rather, Units.mk0 3 _) is a QR generator for p = 97.

This means:
1. 3 is a quadratic residue mod 97
2. ord₉₇(3) = 48 = (97-1)/2
-/
theorem k_is_qr_generator : QRGenerator bs.k := by
  constructor
  · -- 3 is a QR
    rw [k_eq_three]
    exact three_is_square
  · -- orderOf = 48 = half 97
    have h : bs.k = Units.mk0 (3 : ZMod 97) (by decide) := by
      ext
      exact k_eq_three
    rw [h, order_of_three]
    native_decide

/-! ### The Main Theorem Applied -/

/-- The QR tour theorem for p = 97:
Every quadratic residue mod 97 appears as strideRemainder bs j for some j < 48. -/
theorem qr_tour : ∀ a : (ZMod 97)ˣ, IsSquare (a : ZMod 97) →
    ∃ j : ℕ, j < 48 ∧ strideRemainder bs j = a :=
  qr_tour_cover bs p_ne_two k_is_qr_generator

/-! ### Explicit Enumeration

We can explicitly list the 48 quadratic residues by computing 3^j for j = 0..47.
-/

/-- The 48 quadratic residues mod 97, in the order visited by the QR tour. -/
def qrList : List (ZMod 97) :=
  List.map (fun j => strideRemainder bs j) (List.range 48)

/-! ### Primitive Root: 5 is a Full Generator

5 is a primitive root mod 97, meaning ord₉₇(5) = 96 = 97 - 1.
Its powers enumerate ALL nonzero residues mod 97.
-/

/-- 5 is nonzero in ZMod 97. -/
theorem five_ne_zero : (5 : ZMod 97) ≠ 0 := by decide

/-- 5 as a unit in (ZMod 97)ˣ. -/
def five_unit : (ZMod 97)ˣ := Units.mk0 5 five_ne_zero

/-- 5^96 = 1 in ZMod 97. -/
example : (5 : ZMod 97) ^ 96 = 1 := by native_decide

/-- 5 has order 96 = p - 1 in (ZMod 97)ˣ, making it a primitive root. -/
theorem order_of_five : orderOf five_unit = 96 := by
  rw [orderOf_eq_iff (by decide : 0 < 96)]
  constructor
  · native_decide  -- 5^96 = 1
  · intro m hm hm_pos
    -- For m < 96 with m > 0, we need 5^m ≠ 1
    -- Divisors of 96: 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48
    interval_cases m <;> native_decide

/-- 5 is a full generator (primitive root) of (ZMod 97)ˣ. -/
theorem five_is_full_generator : FullGenerator five_unit where
  order_eq := order_of_five

/-- 5² = 25 mod 97, which is a QR generator (has order 48). -/
theorem five_sq_is_qr_generator : QRGenerator (five_unit ^ 2) :=
  full_implies_qr_square p_ne_two five_unit five_is_full_generator

/-! ### Bridge Prime: 97 = 10² - 3

97 is a "bridge prime" because 97 = 100 - 3 = 10² - 3.
This means 10² ≡ 3 (mod 97), giving beautiful block structure in the reptend.
-/

/-- 97 = 10² - 3 is a bridge prime configuration. -/
theorem bridge_97_demo : Bridge 10 97 2 3 := bridge_97

/-- Block-starting remainders form powers of 3:
r[0] = 1 = 3⁰, r[2] = 3¹, r[4] = 3², etc. -/
example : @remainder 97 _ 10 0 = 3 ^ 0 := by native_decide
example : @remainder 97 _ 10 2 = 3 ^ 1 := by native_decide
example : @remainder 97 _ 10 4 = 3 ^ 2 := by native_decide
example : @remainder 97 _ 10 6 = 3 ^ 3 := by native_decide

/-- The k-step recurrence: r[n+2] = 3 × r[n] for any n.
This is the bridge property in action! -/
example : @remainder 97 _ 10 (0 + 2) = 3 * @remainder 97 _ 10 0 := by native_decide
example : @remainder 97 _ 10 (5 + 2) = 3 * @remainder 97 _ 10 5 := by native_decide
example : @remainder 97 _ 10 (10 + 2) = 3 * @remainder 97 _ 10 10 := by native_decide

/-! ### Digit Examples

The reptend digits of 1/97 in base 10.
-/

/-- First few digits of 1/97 in decimal. -/
example : digit 97 10 0 = 0 := by native_decide  -- First digit is 0 (1 × 10 = 10 < 97)
example : digit 97 10 1 = 1 := by native_decide  -- 10 × 10 = 100, 100/97 = 1
example : digit 97 10 2 = 0 := by native_decide  -- 3 × 10 = 30 < 97
example : digit 97 10 3 = 3 := by native_decide  -- 30 × 10 = 300, 300/97 = 3

end QRTour.Prime97
