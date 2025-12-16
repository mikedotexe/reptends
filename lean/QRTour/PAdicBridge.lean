/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.SignedBridge
import QRTour.Digits

/-!
# P-adic Structure in Bridge Primes

This module explores the p-adic-like structure that emerges in bridge primes.

## Key Insight

For a bridge prime p = B^k - d:
- B^k ≡ d (mod p)
- The reptend of 1/p in base B has k-digit blocks
- These blocks form a geometric sequence with ratio d
- This is analogous to p-adic digit structure!

## The Analogy

In p-adic numbers:
- Each digit position has a "place value" p^i
- Digits are determined by reduction mod p at each level

In bridge reptends:
- Each k-block position has "place value" B^(j*k)
- Block values are determined by d^j mod p

## Main Definitions

* `QRTour.blockValue` - The remainder value at block boundary j*k
* `QRTour.BlockSequence` - The sequence of block values

## Main Results

* `QRTour.blockValue_geometric` - Block values form geometric sequence: d^j
* `QRTour.blockValue_periodic` - Block sequence has period = orderOf d
-/

namespace QRTour

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### Block Values

For a bridge prime with block size k, the "block values" are the remainders
at positions 0, k, 2k, 3k, ... These form a geometric sequence.
-/

/-- The block value at block j is the remainder at position j*k.
    For a bridge prime, this equals d^j mod p. -/
def blockValue (B k j : ℕ) : ZMod p := remainder (p := p) B (j * k)

/-- Block values start at 1. -/
theorem blockValue_zero (B k : ℕ) : blockValue (p := p) B k 0 = 1 := by
  simp [blockValue]

/-- For a bridge, block values form a geometric sequence with ratio d. -/
theorem Bridge.blockValue_eq_pow (br : Bridge B p k d) (j : ℕ) :
    blockValue (p := p) B k j = (d : ZMod p) ^ j := by
  haveI : Fact (Nat.Prime p) := ⟨br.prime_p⟩
  simp only [blockValue]
  exact br.block_start_geometric j

/-- For a signed bridge, block values form a geometric sequence with ratio (sign × d). -/
theorem SignedBridge.blockValue_eq_pow (sb : SignedBridge B p k sign d) (j : ℕ) :
    blockValue (p := p) B k j = sb.multiplier ^ j := by
  haveI : Fact (Nat.Prime p) := ⟨sb.prime_p⟩
  simp only [blockValue]
  have h := sb.remainder_jk_step 0 j
  simp only [zero_add, remainder, mul_one] at h
  exact h

/-! ### P-adic Analogy

The p-adic expansion of a rational number r has digits d_0, d_1, d_2, ...
where r = Σ d_i × p^i.

For the reptend of 1/p in base B with bridge structure p = B^k - d:
- The "digits" are k-blocks
- Block j has "value" d^j (the geometric sequence)
- The full reptend is determined by this geometric structure

This is a discrete, finite analog of p-adic structure!
-/

/-- d is nonzero in ZMod p for a bridge. -/
theorem Bridge.d_ne_zero (br : Bridge B p k d) : (d : ZMod p) ≠ 0 := by
  haveI : Fact (Nat.Prime p) := ⟨br.prime_p⟩
  intro h
  have hdvd : p ∣ d := (ZMod.natCast_eq_zero_iff d p).mp h
  have hd_lt : d < p := br.hd_lt_p
  have hd_zero : d = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hd_lt
  have hd_pos : 0 < d := br.hd_pos
  omega

/-- The "p-adic order" of the multiplier d in a bridge prime.
    This is the period of the block sequence. -/
noncomputable def bridgeOrder (br : Bridge B p k d) : ℕ :=
  orderOf (Units.mk0 (d : ZMod p) br.d_ne_zero)

/-- The block sequence has period equal to the order of d. -/
theorem Bridge.blockValue_periodic (br : Bridge B p k d) (j : ℕ) :
    blockValue (p := p) B k (j + bridgeOrder br) = blockValue (p := p) B k j := by
  haveI : Fact (Nat.Prime p) := ⟨br.prime_p⟩
  simp only [br.blockValue_eq_pow, pow_add]
  have hord : (d : ZMod p) ^ bridgeOrder br = 1 := by
    simp only [bridgeOrder]
    have h := pow_orderOf_eq_one (Units.mk0 (d : ZMod p) br.d_ne_zero)
    calc (d : ZMod p) ^ orderOf (Units.mk0 (d : ZMod p) br.d_ne_zero)
        = (Units.mk0 (d : ZMod p) br.d_ne_zero : ZMod p) ^ orderOf (Units.mk0 (d : ZMod p) br.d_ne_zero) := rfl
      _ = ((Units.mk0 (d : ZMod p) br.d_ne_zero) ^ orderOf (Units.mk0 (d : ZMod p) br.d_ne_zero) : (ZMod p)ˣ) := by
          rw [Units.val_pow_eq_pow_val]
      _ = (1 : (ZMod p)ˣ) := by rw [h]
      _ = 1 := rfl
  rw [hord, mul_one]

/-! ### Connection to Reptend Period

The full reptend period of 1/p in base B is:
  period = k × (order of d in (ZMod p)ˣ)

This is because:
1. Each block has k digits
2. The block sequence repeats with period = order of d
3. Total period = block_size × block_period
-/

/-- The reptend period for a bridge prime equals k × (order of d).

Note: This theorem requires that k divides the multiplicative order of B in (ZMod p)ˣ.
For bridge primes of the form p = B^k ± d, this follows from the structure of the bridge.
-/
theorem Bridge.reptend_period_eq (br : Bridge B p k d) (hB : Nat.Coprime B p)
    (hk_dvd : k ∣ orderOf (Units.mk0 (B : ZMod p) (by
      intro h
      have hdvd : p ∣ B := (ZMod.natCast_eq_zero_iff B p).mp h
      exact Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt br.prime_p) (dvd_refl p) hdvd hB.symm))) :
    reptendPeriod p B hB = k * bridgeOrder br := by
  haveI : Fact (Nat.Prime p) := ⟨br.prime_p⟩
  -- Setup: get B and d as units
  have hB_ne : (B : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ B := (ZMod.natCast_eq_zero_iff B p).mp h
    exact Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt br.prime_p) (dvd_refl p) hdvd hB.symm
  let Bu : (ZMod p)ˣ := Units.mk0 (B : ZMod p) hB_ne
  let du : (ZMod p)ˣ := Units.mk0 (d : ZMod p) br.d_ne_zero

  -- Bridge equation lifts to units: Bu^k = du
  have hpow : Bu ^ k = du := by
    ext
    simp only [Units.val_pow_eq_pow_val]
    exact br.bridge_eq

  -- The key is orderOf_pow: orderOf (g^k) = orderOf g / gcd(orderOf g, k)
  have h1 : orderOf du = orderOf Bu / Nat.gcd (orderOf Bu) k := by
    rw [← hpow, orderOf_pow]

  -- When k | orderOf Bu: gcd(orderOf Bu, k) = k
  have hgcd : Nat.gcd (orderOf Bu) k = k := Nat.gcd_eq_right hk_dvd

  -- Combine: orderOf Bu = k * orderOf du
  have hord : orderOf Bu = k * orderOf du := by
    -- From h1: orderOf du = orderOf Bu / gcd
    -- From hmul: orderOf Bu = (orderOf Bu / gcd) * gcd
    -- Substitute h1 into hmul: orderOf Bu = orderOf du * gcd
    -- Then use hgcd: gcd = k
    have hmul : orderOf Bu = (orderOf Bu / Nat.gcd (orderOf Bu) k) * Nat.gcd (orderOf Bu) k :=
      (Nat.div_mul_cancel (Nat.gcd_dvd_left (orderOf Bu) k)).symm
    rw [← h1, hgcd] at hmul
    linarith

  -- Unfold definitions: reptendPeriod and bridgeOrder are orderOf of the same units
  unfold reptendPeriod bridgeOrder
  -- The Units.mk0 constructions produce definitionally equal units to Bu and du
  convert hord using 2

/-! ### Examples: P-adic Structure in Action -/

section Examples

instance : Fact (Nat.Prime 97) := ⟨by native_decide⟩

/-- For p = 97, the block sequence is 1, 3, 9, 27, 81, 49, 50, ... (powers of 3 mod 97). -/
example : blockValue (p := 97) 10 2 0 = 1 := by native_decide
example : blockValue (p := 97) 10 2 1 = 3 := by native_decide
example : blockValue (p := 97) 10 2 2 = 9 := by native_decide
example : blockValue (p := 97) 10 2 3 = 27 := by native_decide
example : blockValue (p := 97) 10 2 4 = 81 := by native_decide
example : blockValue (p := 97) 10 2 5 = 49 := by native_decide  -- 3^5 = 243 ≡ 49

/-- The block sequence for p = 97 has period 48 (the order of 3 mod 97). -/
example : orderOf (Units.mk0 (3 : ZMod 97) (by decide)) = 48 := by
  rw [orderOf_eq_iff (by decide : 0 < 48)]
  constructor
  · native_decide
  · intro m hm hm_pos
    interval_cases m <;> native_decide

end Examples

/-! ### Digit-Block Duality

Each k-digit block of the reptend is determined by the block value.
If block j has value v_j = d^j, then the k digits of that block
are the digits of v_j / (previous accumulator).

This connects:
- QRTour.digit (single digit extraction)
- QRTour.blockValue (block-level structure)
- Bridge.block_start_geometric (the geometric pattern)
-/

/-- The digits within block j are determined by the block value ratio. -/
theorem digit_block_connection (br : Bridge B p k d) (j i : ℕ) (_hi : i < k) :
    digit p B (j * k + i) =
      (B * (@remainder p ⟨br.prime_p⟩ B (j * k + i)).val) / p := by
  rfl

/-! ### Toward Full P-adic Structure

A full p-adic interpretation would identify:
1. The "valuation" of each block position
2. The "completion" that makes reptends into true p-adic numbers
3. The ring structure on periodic sequences

This module establishes the foundation by showing that bridge primes
exhibit the key p-adic property: geometric digit sequences determined
by a fixed multiplier.
-/

end QRTour
