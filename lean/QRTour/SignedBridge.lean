/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.Bridge
import QRTour.BridgeQuality

/-!
# Signed Bridges: Unifying Plus and Minus Exponential Forms

This module unifies the two "almost exponential" patterns for primes:
- **Minus bridges**: p = B^k - d → B^k ≡ +d (mod p), e.g., 97 = 10² - 3
- **Plus bridges**: p = B^k + d → B^k ≡ -d (mod p), e.g., 101 = 10² + 1

The plus case gives alternating sign structure: if B^k ≡ -d, then r[n+k] = -d × r[n],
and after 2k steps the sign cancels: r[n+2k] = d² × r[n].

## Main Definitions

* `QRTour.BridgeSign` - Inductive type for plus/minus classification
* `QRTour.SignedBridge` - Unified structure: B^k ≡ sign × d (mod p)

## Main Results

* `QRTour.SignedBridge.remainder_k_step` - r[n+k] = (sign × d) × r[n]
* `QRTour.SignedBridge.remainder_2k_step` - r[n+2k] = d² × r[n] (sign always cancels)
* `QRTour.Bridge.toSignedBridge` - Every Bridge is a minus SignedBridge

## Examples

- p = 97 = 10² - 3: SignedBridge with sign = minus, d = 3
- p = 101 = 10² + 1: SignedBridge with sign = plus, d = 1 (alternating!)
- p = 103 = 10² + 3: SignedBridge with sign = plus, d = 3
-/

namespace QRTour

/-! ### Bridge Sign Classification -/

/-- Sign classification for bridge primes.
- `plus`: p = B^k + d, so B^k ≡ -d (mod p)
- `minus`: p = B^k - d, so B^k ≡ +d (mod p) -/
inductive BridgeSign : Type
  | plus  : BridgeSign
  | minus : BridgeSign
  deriving DecidableEq, Repr

/-- Convert sign to integer multiplier: plus → -1, minus → +1 -/
def BridgeSign.toInt : BridgeSign → ℤ
  | .plus => -1
  | .minus => 1

/-- The sign multiplier squared is always 1. -/
theorem BridgeSign.toInt_sq (s : BridgeSign) : s.toInt ^ 2 = 1 := by
  cases s <;> native_decide

/-- The sign multiplier is nonzero. -/
theorem BridgeSign.toInt_ne_zero (s : BridgeSign) : s.toInt ≠ 0 := by
  cases s <;> decide

/-! ### Signed Bridge Structure -/

/-- A signed bridge captures both plus and minus exponential forms.
For sign = minus: p = B^k - d, so B^k ≡ d (mod p)
For sign = plus: p = B^k + d, so B^k ≡ -d (mod p)

The key equation is: B^k ≡ sign.toInt × d (mod p) -/
structure SignedBridge (B p k : ℕ) (sign : BridgeSign) (d : ℕ) where
  /-- p is prime -/
  prime_p : Nat.Prime p
  /-- k is positive (the power) -/
  hk_pos : 0 < k
  /-- d is positive (the deficit) -/
  hd_pos : 0 < d
  /-- d < p (so d is a valid residue) -/
  hd_lt_p : d < p
  /-- The signed bridge equation: B^k = sign × d in ZMod p -/
  bridge_eq : (B : ZMod p) ^ k = sign.toInt * d

/-! ### Remainder Recurrence -/

/-- The signed multiplier as an element of ZMod p. -/
def SignedBridge.multiplier (_sb : SignedBridge B p k sign d) : ZMod p :=
  (sign.toInt * d : ℤ)

/-- The key k-step recurrence for signed bridges: r[n+k] = multiplier × r[n]. -/
theorem SignedBridge.remainder_k_step (sb : SignedBridge B p k sign d) (n : ℕ) :
    @remainder p ⟨sb.prime_p⟩ B (n + k) = sb.multiplier * @remainder p ⟨sb.prime_p⟩ B n := by
  simp only [remainder_eq_pow, pow_add, sb.bridge_eq, multiplier]
  -- Goal: B^n * (sign.toInt * d) = (sign.toInt * d : ℤ) * B^n
  push_cast
  ring

/-- Iterated k-step recurrence. -/
theorem SignedBridge.remainder_jk_step (sb : SignedBridge B p k sign d) (n j : ℕ) :
    @remainder p ⟨sb.prime_p⟩ B (n + j * k) =
      sb.multiplier ^ j * @remainder p ⟨sb.prime_p⟩ B n := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc @remainder p ⟨sb.prime_p⟩ B (n + (j + 1) * k)
        = @remainder p ⟨sb.prime_p⟩ B ((n + j * k) + k) := by ring_nf
      _ = sb.multiplier * @remainder p ⟨sb.prime_p⟩ B (n + j * k) :=
          sb.remainder_k_step (n + j * k)
      _ = sb.multiplier * (sb.multiplier ^ j * @remainder p ⟨sb.prime_p⟩ B n) := by rw [ih]
      _ = sb.multiplier ^ (j + 1) * @remainder p ⟨sb.prime_p⟩ B n := by ring

/-- The signed multiplier squared equals d². -/
theorem SignedBridge.multiplier_sq_eq (sb : SignedBridge B p k sign d) :
    sb.multiplier ^ 2 = (d : ZMod p) ^ 2 := by
  haveI : Fact (Nat.Prime p) := ⟨sb.prime_p⟩
  simp only [multiplier]
  -- (sign.toInt * d)^2 = sign.toInt^2 * d^2 = 1 * d^2 = d^2
  have h1 : ((sign.toInt * d : ℤ) : ZMod p) ^ 2 =
      (sign.toInt : ZMod p) ^ 2 * (d : ZMod p) ^ 2 := by
    push_cast
    ring
  rw [h1]
  have hsq : (sign.toInt : ZMod p) ^ 2 = 1 := by
    cases sign <;> simp [BridgeSign.toInt]
  rw [hsq, one_mul]

/-- Double k-step: the sign always cancels, giving r[n+2k] = d² × r[n].
This is the key insight for plus bridges: after two steps, we're back to positive multiplication. -/
theorem SignedBridge.remainder_2k_step (sb : SignedBridge B p k sign d) (n : ℕ) :
    @remainder p ⟨sb.prime_p⟩ B (n + 2 * k) =
      (d : ZMod p) ^ 2 * @remainder p ⟨sb.prime_p⟩ B n := by
  have h := sb.remainder_jk_step n 2
  simp only [sb.multiplier_sq_eq] at h
  exact h

/-! ### Conversion from Bridge -/

/-- Every (minus) Bridge is a SignedBridge with sign = minus. -/
def Bridge.toSignedBridge (br : Bridge B p k d) : SignedBridge B p k .minus d where
  prime_p := br.prime_p
  hk_pos := br.hk_pos
  hd_pos := br.hd_pos
  hd_lt_p := br.hd_lt_p
  bridge_eq := by
    simp only [BridgeSign.toInt, one_mul, Int.cast_one]
    exact br.bridge_eq

/-! ### Examples -/

section Examples

instance : Fact (Nat.Prime 97) := ⟨by native_decide⟩
instance : Fact (Nat.Prime 101) := ⟨by native_decide⟩
instance : Fact (Nat.Prime 103) := ⟨by native_decide⟩

/-! #### p = 97: Minus Bridge (10² - 3 = 97) -/

/-- 97 = 10² - 3 is a minus bridge. -/
theorem signed_bridge_97 : SignedBridge 10 97 2 .minus 3 where
  prime_p := by native_decide
  hk_pos := by decide
  hd_pos := by decide
  hd_lt_p := by decide
  bridge_eq := by native_decide

/-- 97 can be obtained from the existing Bridge. -/
example : SignedBridge 10 97 2 .minus 3 := bridge_97.toSignedBridge

/-- For 97, remainders form positive geometric sequence: 1, 3, 9, 27, ... -/
example : @remainder 97 _ 10 0 = 1 := by native_decide
example : @remainder 97 _ 10 2 = 3 := by native_decide
example : @remainder 97 _ 10 4 = 9 := by native_decide
example : @remainder 97 _ 10 6 = 27 := by native_decide

/-! #### p = 101: Plus Bridge (10² + 1 = 101) -/

/-- 101 = 10² + 1 is a plus bridge with d = 1.
Key: 10² = 100 ≡ -1 (mod 101), giving alternating structure! -/
theorem signed_bridge_101 : SignedBridge 10 101 2 .plus 1 where
  prime_p := by native_decide
  hk_pos := by decide
  hd_pos := by decide
  hd_lt_p := by decide
  bridge_eq := by native_decide

/-- For 101, 10² ≡ -1, so the stride-2 remainders alternate: 1, -1, 1, -1, ... -/
example : (10 : ZMod 101) ^ 2 = -1 := by native_decide
example : @remainder 101 _ 10 0 = 1 := by native_decide
example : @remainder 101 _ 10 2 = 100 := by native_decide  -- 100 ≡ -1 mod 101
example : @remainder 101 _ 10 4 = 1 := by native_decide    -- (-1)² = 1
example : @remainder 101 _ 10 6 = 100 := by native_decide  -- back to -1

/-- The alternating pattern: r[2] = -r[0], r[4] = r[0], etc. -/
example : @remainder 101 _ 10 2 = -(@remainder 101 _ 10 0) := by native_decide
example : @remainder 101 _ 10 4 = @remainder 101 _ 10 0 := by native_decide

/-! #### p = 103: Plus Bridge (10² + 3 = 103) -/

/-- 103 = 10² + 3 is a plus bridge with d = 3.
Key: 10² = 100 ≡ -3 (mod 103). -/
theorem signed_bridge_103 : SignedBridge 10 103 2 .plus 3 where
  prime_p := by native_decide
  hk_pos := by decide
  hd_pos := by decide
  hd_lt_p := by decide
  bridge_eq := by native_decide

/-- For 103, 10² ≡ -3 (mod 103). -/
example : (10 : ZMod 103) ^ 2 = -3 := by native_decide
example : (10 : ZMod 103) ^ 2 = 100 := by native_decide  -- 100 ≡ -3 mod 103

/-- Stride-2 remainders for 103: 1, -3, 9, -27, ... (alternating signs with ×3) -/
example : @remainder 103 _ 10 0 = 1 := by native_decide
example : @remainder 103 _ 10 2 = 100 := by native_decide  -- ≡ -3
example : @remainder 103 _ 10 4 = 9 := by native_decide    -- (-3)² ÷ 1 = 9
example : @remainder 103 _ 10 6 = 76 := by native_decide   -- 9 × (-3) ≡ -27 ≡ 76

/-- Double-step for 103: sign cancels, factor is 9 = 3². -/
example : @remainder 103 _ 10 4 = 9 * @remainder 103 _ 10 0 := by native_decide
example : @remainder 103 _ 10 8 = 9 * @remainder 103 _ 10 4 := by native_decide

end Examples

/-! ### Classification by Signed Residue

The `signedResidue` from BridgeQuality tells us the sign:
- Positive signed residue → minus bridge
- Negative signed residue → plus bridge -/

/-- Classify a configuration as plus or minus based on signed residue. -/
def classifySign (B p k : ℕ) : BridgeSign :=
  if signedResidue B p k ≥ 0 then .minus else .plus

/-- For a minus bridge, the residue B^k mod p equals d. -/
theorem SignedBridge.minus_residue_eq (sb : SignedBridge B p k .minus d) :
    B ^ k % p = d := by
  haveI : Fact (Nat.Prime p) := ⟨sb.prime_p⟩
  have h : (B : ZMod p) ^ k = d := by
    simpa [BridgeSign.toInt] using sb.bridge_eq
  rw [← Nat.cast_pow] at h
  have := congrArg ZMod.val h
  simp only [ZMod.val_natCast] at this
  rw [Nat.mod_eq_of_lt sb.hd_lt_p] at this
  exact this

/-- For a plus bridge, the residue B^k mod p equals p - d. -/
theorem SignedBridge.plus_residue_eq (sb : SignedBridge B p k .plus d) :
    B ^ k % p = p - d := by
  haveI : Fact (Nat.Prime p) := ⟨sb.prime_p⟩
  have h : (B : ZMod p) ^ k = -d := by
    simpa [BridgeSign.toInt] using sb.bridge_eq
  rw [← Nat.cast_pow] at h
  have hval := congrArg ZMod.val h
  simp only [ZMod.val_natCast] at hval
  -- -d in ZMod p has value p - d (when d < p, d > 0)
  have hd_lt : d < p := sb.hd_lt_p
  have hneg : (-d : ZMod p).val = p - d := by
    have hd_ne : (d : ZMod p) ≠ 0 := by
      intro hdvd
      have hdvd' : p ∣ d := (ZMod.natCast_eq_zero_iff d p).mp hdvd
      have hd_zero : d = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' hd_lt
      have : 0 < d := sb.hd_pos
      omega
    haveI : NeZero (d : ZMod p) := ⟨hd_ne⟩
    rw [ZMod.val_neg_of_ne_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hd_lt]
  rw [hneg] at hval
  exact hval

/-- The deficit from BridgeQuality is at most d for a signed bridge. -/
theorem SignedBridge.deficit_le (sb : SignedBridge B p k sign d) :
    bridgeDeficit B p k ≤ d := by
  simp only [bridgeDeficit, bridgeResidue]
  cases sign with
  | minus =>
    have heq := sb.minus_residue_eq
    rw [heq]
    exact Nat.min_le_left d (p - d)
  | plus =>
    have heq := sb.plus_residue_eq
    rw [heq]
    have hp_gt : p > d := sb.hd_lt_p
    by_cases h : p - d ≤ d
    · calc min (p - d) (p - (p - d))
          ≤ p - d := Nat.min_le_left _ _
        _ ≤ d := h
    · push_neg at h
      have hsub : p - (p - d) = d := by omega
      rw [hsub]
      exact Nat.min_le_right (p - d) d

end QRTour
