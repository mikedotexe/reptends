/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.Bridge

/-!
# Bridge Quality: Distance from Clean Exponential

When is a prime p "almost" a bridge prime? For any prime p and base B, we can
ask: for which k is B^k mod p closest to a small value?

## Key Insight

For p = B^k - d (exact bridge), we have B^k ≡ d (mod p) with d small.
For p ≈ B^k - d (approximate bridge), the residue B^k mod p tells us the "deficit".

The smaller the deficit, the cleaner the block-level structure in the reptend.

## Main Definitions

* `QRTour.bridgeResidue` - B^k mod p as a natural number
* `QRTour.bridgeDeficit` - min(residue, p - residue), the "distance to clean"
* `QRTour.ApproxBridge` - Configuration capturing approximate bridge structure

## Main Results

* `QRTour.ApproxBridge.remainder_k_step` - r[n+k] = residue × r[n] (always true!)

## Examples

For p = 97, B = 10:
- k=1: 10^1 mod 97 = 10, deficit = 10
- k=2: 10^2 mod 97 = 3, deficit = 3  ← Best! (exact bridge)
- k=3: 10^3 mod 97 = 30, deficit = 30
- k=4: 10^4 mod 97 = 9, deficit = 9

For p = 101, B = 10:
- k=1: 10^1 mod 101 = 10, deficit = 10
- k=2: 10^2 mod 101 = 100, deficit = 1  ← p = 10² + 1, so 10² ≡ -1!
- k=4: 10^4 mod 101 = 1, deficit = 1   ← Full period divides 4

The k=2 case for 101 is fascinating: 10² ≡ -1 (mod 101), giving alternating signs!
-/

namespace QRTour

/-! ### Bridge Residue and Deficit -/

/-- The bridge residue: B^k mod p as a natural number. -/
def bridgeResidue (B p k : ℕ) : ℕ := B ^ k % p

/-- The bridge deficit: distance from B^k to the nearest multiple of p.
    This measures how "clean" a bridge the (B, p, k) configuration makes. -/
def bridgeDeficit (B p k : ℕ) : ℕ :=
  min (bridgeResidue B p k) (p - bridgeResidue B p k)

/-- The residue equals B^k in ZMod p. -/
theorem bridgeResidue_eq_pow (B p k : ℕ) [Fact (Nat.Prime p)] :
    (bridgeResidue B p k : ZMod p) = (B : ZMod p) ^ k := by
  simp only [bridgeResidue, ← Nat.cast_pow]
  rw [ZMod.natCast_mod]

/-! ### Approximate Bridge Structure -/

/-- An approximate bridge captures any (B, p, k) configuration.
    The key insight: B^k ≡ residue (mod p) ALWAYS holds, so we always get
    the k-step recurrence r[n+k] = residue × r[n]. The question is just
    how "nice" the residue is. -/
structure ApproxBridge (B p k : ℕ) where
  /-- p is prime -/
  prime_p : Nat.Prime p
  /-- k is positive -/
  hk_pos : 0 < k
  /-- B is coprime to p -/
  hB_coprime : Nat.Coprime B p

/-- The residue for an approximate bridge. -/
def ApproxBridge.residue (_ab : ApproxBridge B p k) : ℕ := bridgeResidue B p k

/-- The deficit (quality measure) for an approximate bridge. -/
def ApproxBridge.deficit (_ab : ApproxBridge B p k) : ℕ := bridgeDeficit B p k

/-- The residue is nonzero (since B is coprime to p). -/
theorem ApproxBridge.residue_ne_zero (ab : ApproxBridge B p k) : ab.residue ≠ 0 := by
  simp only [ApproxBridge.residue, bridgeResidue]
  intro h
  have hdvd : p ∣ B ^ k := Nat.dvd_of_mod_eq_zero h
  have hdvdB : p ∣ B := Nat.Prime.dvd_of_dvd_pow ab.prime_p hdvd
  have hgcd := Nat.dvd_gcd hdvdB (dvd_refl p)
  rw [ab.hB_coprime] at hgcd
  exact Nat.Prime.not_dvd_one ab.prime_p hgcd

/-- The residue is less than p. -/
theorem ApproxBridge.residue_lt_p (ab : ApproxBridge B p k) : ab.residue < p := by
  simp only [ApproxBridge.residue, bridgeResidue]
  exact Nat.mod_lt _ ab.prime_p.pos

/-- The key recurrence holds for ANY approximate bridge. -/
theorem ApproxBridge.remainder_k_step (ab : ApproxBridge B p k) (n : ℕ) :
    @remainder p ⟨ab.prime_p⟩ B (n + k) = ab.residue * @remainder p ⟨ab.prime_p⟩ B n := by
  simp only [remainder_eq_pow, ApproxBridge.residue, bridgeResidue, pow_add]
  rw [mul_comm]
  congr 1
  rw [← Nat.cast_pow, ZMod.natCast_mod]

/-- Iterated k-step recurrence. -/
theorem ApproxBridge.remainder_jk_step (ab : ApproxBridge B p k) (n j : ℕ) :
    @remainder p ⟨ab.prime_p⟩ B (n + j * k) =
      (ab.residue : ZMod p) ^ j * @remainder p ⟨ab.prime_p⟩ B n := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc @remainder p ⟨ab.prime_p⟩ B (n + (j + 1) * k)
        = @remainder p ⟨ab.prime_p⟩ B ((n + j * k) + k) := by ring_nf
      _ = ab.residue * @remainder p ⟨ab.prime_p⟩ B (n + j * k) := ab.remainder_k_step (n + j * k)
      _ = ab.residue * ((ab.residue : ZMod p) ^ j * @remainder p ⟨ab.prime_p⟩ B n) := by rw [ih]
      _ = (ab.residue : ZMod p) ^ (j + 1) * @remainder p ⟨ab.prime_p⟩ B n := by ring

/-! ### Quality Comparison

A bridge is "better" when its deficit is smaller. An exact Bridge (from Bridge.lean)
has deficit = d, which can be very small.
-/

/-- An exact bridge has deficit equal to d. -/
theorem exact_bridge_deficit (br : Bridge B p k d) :
    bridgeDeficit B p k ≤ d := by
  simp only [bridgeDeficit, bridgeResidue]
  -- B^k mod p = d for exact bridge
  have h : B ^ k % p = d := by
    have heq : (B : ZMod p) ^ k = d := br.bridge_eq
    have hd_lt : d < p := br.hd_lt_p
    rw [← Nat.cast_pow] at heq
    have := congrArg ZMod.val heq
    simp only [ZMod.val_natCast] at this
    rw [Nat.mod_eq_of_lt hd_lt] at this
    exact this
  rw [h]
  exact Nat.min_le_left d (p - d)

/-! ### Examples: Comparing Bridges -/

section Examples

instance : Fact (Nat.Prime 97) := ⟨by native_decide⟩
instance : Fact (Nat.Prime 101) := ⟨by native_decide⟩

-- p = 97: Best bridge at k=2 with deficit 3
example : bridgeResidue 10 97 1 = 10 := by native_decide
example : bridgeResidue 10 97 2 = 3 := by native_decide   -- Best!
example : bridgeResidue 10 97 3 = 30 := by native_decide
example : bridgeResidue 10 97 4 = 9 := by native_decide

example : bridgeDeficit 10 97 1 = 10 := by native_decide
example : bridgeDeficit 10 97 2 = 3 := by native_decide   -- Smallest deficit
example : bridgeDeficit 10 97 3 = 30 := by native_decide
example : bridgeDeficit 10 97 4 = 9 := by native_decide

-- p = 101: Fascinating case! 10² ≡ -1 (mod 101)
example : bridgeResidue 10 101 1 = 10 := by native_decide
example : bridgeResidue 10 101 2 = 100 := by native_decide  -- = 101 - 1 = -1!
example : bridgeResidue 10 101 3 = 91 := by native_decide   -- = -10
example : bridgeResidue 10 101 4 = 1 := by native_decide    -- Back to 1!

example : bridgeDeficit 10 101 1 = 10 := by native_decide
example : bridgeDeficit 10 101 2 = 1 := by native_decide   -- deficit 1, but residue is -1!
example : bridgeDeficit 10 101 3 = 10 := by native_decide
example : bridgeDeficit 10 101 4 = 1 := by native_decide   -- Full period!

/-- 101 has the property that 10² ≡ -1 (mod 101).
    This means r[n+2] = -r[n], giving alternating sign structure! -/
theorem p101_neg_one : (10 : ZMod 101) ^ 2 = -1 := by native_decide

/-- For 101, the 2-block structure alternates signs. -/
example : @remainder 101 _ 10 0 = 1 := by native_decide
example : @remainder 101 _ 10 2 = 100 := by native_decide  -- = -1 mod 101
example : @remainder 101 _ 10 4 = 1 := by native_decide    -- back to 1

end Examples

/-! ### Signed Residue

For analysis, it's often better to think of the residue as a signed integer
in the range (-(p-1)/2, (p-1)/2]. -/

/-- The signed residue: in range (-(p-1)/2, (p-1)/2]. -/
def signedResidue (B p k : ℕ) : ℤ :=
  let r := bridgeResidue B p k
  if r ≤ p / 2 then (r : ℤ) else (r : ℤ) - (p : ℤ)

example : signedResidue 10 97 2 = 3 := by native_decide
example : signedResidue 10 101 2 = -1 := by native_decide  -- Negative!

/-! ### Factor Inheritance: Divisors of Bridge Numbers Inherit Structure

Key insight: If n = B^k - d and p | n (with d < p), then B^k ≡ d (mod p).
So prime factors of "bridge numbers" inherit the bridge structure!

Example: 95 = 10² - 5, and 19 | 95, so 10² ≡ 5 (mod 19).
This explains why 1/19 has the same multiplier pattern as 1/95 would.
-/

/-- If p divides B^k - d (and d < p), then B^k ≡ d (mod p). -/
theorem factor_inherits_bridge {B k d p : ℕ} (_hp : Nat.Prime p) (hd_lt : d < p)
    (hdiv : p ∣ B ^ k - d) (hBk_ge : d ≤ B ^ k) :
    (B : ZMod p) ^ k = d := by
  -- B^k - d ≡ 0 (mod p), so B^k ≡ d (mod p)
  have hdiv_mod : (B ^ k - d) % p = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hmod : B ^ k % p = d % p := by
    have h1 : B ^ k = (B ^ k - d) + d := (Nat.sub_add_cancel hBk_ge).symm
    have h2 : ((B ^ k - d) + d) % p = ((B ^ k - d) % p + d % p) % p := by
      exact Nat.add_mod (B ^ k - d) d p
    rw [h1, h2, hdiv_mod, zero_add, Nat.mod_mod]
  rw [← Nat.cast_pow]
  conv_lhs => rw [← ZMod.natCast_mod (B ^ k) p]
  simp only [hmod, Nat.mod_eq_of_lt hd_lt]

/-- 19 divides 95 = 10² - 5, so 10² ≡ 5 (mod 19). -/
instance : Fact (Nat.Prime 19) := ⟨by native_decide⟩

example : (19 : ℕ) ∣ (10 ^ 2 - 5) := by native_decide
example : (10 : ZMod 19) ^ 2 = 5 := by native_decide

/-- 19 inherits its bridge structure from 95 = 10² - 5. -/
theorem bridge_19_from_95 : Bridge 10 19 2 5 where
  prime_p := by native_decide
  hk_pos := by decide
  hd_pos := by decide
  hd_lt_p := by decide
  bridge_eq := by native_decide

/-- The multiplier for 1/19 is 5, giving the geometric sequence 1, 5, 6, 11, 17, 9, 7, ... -/
example : bridgeResidue 10 19 2 = 5 := by native_decide
example : @remainder 19 _ 10 0 = 1 := by native_decide
example : @remainder 19 _ 10 2 = 5 := by native_decide
example : @remainder 19 _ 10 4 = 6 := by native_decide   -- 5² = 25 ≡ 6
example : @remainder 19 _ 10 6 = 11 := by native_decide  -- 5³ = 125 ≡ 11

/-- The absolute value of signed residue equals the deficit. -/
theorem signedResidue_abs_eq_deficit (B p k : ℕ) (hp : 0 < p) :
    (signedResidue B p k).natAbs = bridgeDeficit B p k := by
  simp only [signedResidue, bridgeDeficit]
  split_ifs with h
  · -- Case: r ≤ p/2, so signedResidue = r (positive)
    have hr_lt : bridgeResidue B p k < p := Nat.mod_lt _ hp
    have hle : bridgeResidue B p k ≤ p - bridgeResidue B p k := by omega
    simp only [Int.natAbs_natCast]
    rw [Nat.min_eq_left hle]
  · -- Case: r > p/2, so signedResidue = r - p (negative)
    push_neg at h
    have hr_lt : bridgeResidue B p k < p := Nat.mod_lt _ hp
    have hlt : p - bridgeResidue B p k < bridgeResidue B p k := by omega
    rw [Nat.min_eq_right (Nat.le_of_lt hlt)]
    have heq : (bridgeResidue B p k : ℤ) - (p : ℤ) = -((p : ℤ) - bridgeResidue B p k) := by ring
    rw [heq, Int.natAbs_neg]
    have hsub : (p : ℤ) - bridgeResidue B p k = ((p - bridgeResidue B p k : ℕ) : ℤ) := by
      rw [Int.ofNat_sub (Nat.le_of_lt hr_lt)]
    rw [hsub, Int.natAbs_natCast]

end QRTour
