/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.QuadraticResidues

/-!
# Remainder Orbits and the QR Tour

This module proves the main theorem connecting long-division remainders to
quadratic residues. When computing 1/p in base B, the remainder sequence
r[0], r[1], r[2], ... satisfies r[n] = B^n (mod p). Taking stride-m samples
gives r[j*m] = k^j where k = B^m mod p.

## Main Definitions

* `QRTour.BaseStride` - Configuration with base B and stride m
* `QRTour.remainder` - The long-division remainder sequence
* `QRTour.BaseStride.k` - The key value k = B^m mod p

## Main Results

* `QRTour.remainder_eq_pow` - r[n] = B^n in ZMod p
* `QRTour.stride_orbit` - r[j*m] = k^j
* `QRTour.qr_tour_cover` - If k is a QR generator, stride-m remainders cover all QRs
-/

namespace QRTour

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### Base-Stride Configuration -/

/-- Configuration for the remainder orbit: base B and stride m. -/
structure BaseStride (p : ℕ) [Fact (Nat.Prime p)] where
  /-- The base for positional notation (e.g., 10 for decimal) -/
  B : ℕ
  /-- The stride length -/
  m : ℕ
  /-- B is coprime to p (so B is a unit mod p) -/
  hB_coprime : Nat.Coprime B p
  /-- m is positive -/
  hm_pos : 0 < m

namespace BaseStride

variable (bs : BaseStride p)

/-- B as a nonzero element of ZMod p. -/
theorem B_ne_zero : (bs.B : ZMod p) ≠ 0 := by
  intro h
  -- B = 0 mod p implies p | B, but gcd(B, p) = 1, so p = 1, contradiction
  have h_dvd : p ∣ bs.B := (ZMod.natCast_eq_zero_iff bs.B p).mp h
  have h_gcd := Nat.dvd_gcd h_dvd (dvd_refl p)
  rw [bs.hB_coprime] at h_gcd
  have h_le : p ≤ 1 := Nat.le_of_dvd Nat.one_pos h_gcd
  have h_gt : 1 < p := hp.out.one_lt
  exact Nat.not_succ_le_self 1 (Nat.lt_of_lt_of_le h_gt h_le)

/-- B as a unit in (ZMod p)ˣ. -/
def Bunit : (ZMod p)ˣ := Units.mk0 (bs.B : ZMod p) bs.B_ne_zero

/-- k = B^m mod p, the key value that generates the QR orbit. -/
def k : (ZMod p)ˣ := bs.Bunit ^ bs.m

/-- k equals B^m as elements of ZMod p. -/
theorem k_eq_pow : (bs.k : ZMod p) = bs.B ^ bs.m := by
  simp only [k, Bunit, Units.val_pow_eq_pow_val, Units.val_mk0]

end BaseStride

/-! ### Remainder Sequence

The long-division remainder sequence for 1/p in base B:
- r[0] = 1
- r[n+1] = B * r[n] mod p
-/

/-- The long-division remainder sequence for base B. -/
def remainder (B : ℕ) : ℕ → ZMod p
  | 0 => 1
  | n + 1 => B * remainder B n

/-- The remainder at step n equals B^n mod p. -/
@[simp]
theorem remainder_eq_pow (B : ℕ) (n : ℕ) : remainder B n = (B : ZMod p) ^ n := by
  induction n with
  | zero => simp [remainder]
  | succ n ih => simp [remainder, ih, pow_succ, mul_comm]

/-! ### Stride Orbit

Sampling the remainder sequence at stride m gives powers of k.
-/

variable (bs : BaseStride p)

/-- The stride-m remainder at position j equals k^j. -/
theorem stride_orbit (j : ℕ) :
    remainder bs.B (j * bs.m) = (bs.k : ZMod p) ^ j := by
  simp [remainder_eq_pow, bs.k_eq_pow, ← pow_mul, mul_comm]

/-- Convenience: stride-m remainder as a function. -/
def strideRemainder (j : ℕ) : ZMod p := remainder bs.B (j * bs.m)

/-- The stride remainder equals k^j. -/
@[simp]
theorem strideRemainder_eq_pow (j : ℕ) :
    strideRemainder bs j = (bs.k : ZMod p) ^ j := stride_orbit bs j

/-! ### QR Tour Cover Theorem

The main result: if k is a QR generator, the stride-m remainders cover all QRs.
-/

/-- Main theorem: if k is a QR generator, stride-m remainders visit all quadratic residues. -/
theorem qr_tour_cover (hp_odd : p ≠ 2) (hk : QRGenerator bs.k) :
    ∀ a : (ZMod p)ˣ, IsSquare (a : ZMod p) →
      ∃ j : ℕ, j < half p ∧ strideRemainder bs j = a := by
  intro a ha
  -- Get j from the QR generator enumeration
  obtain ⟨j, hj_lt, hj_eq⟩ := qr_generator_generates_qrs hp_odd bs.k hk a ha
  use j, hj_lt
  simp only [strideRemainder_eq_pow]
  -- k^j = a as units, so (k : ZMod p)^j = (a : ZMod p)
  rw [← hj_eq]
  simp only [Units.val_pow_eq_pow_val]

/-- The stride-m remainders hit exactly (p-1)/2 distinct values. -/
theorem strideRemainder_image_card (_hp_odd : p ≠ 2) (hk : QRGenerator bs.k) :
    Finset.card (Finset.image (strideRemainder bs) (Finset.range (half p))) = half p := by
  -- strideRemainder bs = (fun j => (bs.k : ZMod p) ^ j)
  -- The map is injective on the range, so the cardinality equals the range size
  have h_injOn : Set.InjOn (strideRemainder bs) (Finset.range (half p)) := by
    intro i hi j hj heq
    rw [Finset.coe_range, Set.mem_Iio] at hi hj
    simp only [strideRemainder_eq_pow] at heq
    -- (bs.k : ZMod p) ^ i = (bs.k : ZMod p) ^ j implies i = j (mod orderOf bs.k)
    have heq' : bs.k ^ i = bs.k ^ j := by
      apply Units.val_injective
      simp only [Units.val_pow_eq_pow_val, heq]
    rw [pow_eq_pow_iff_modEq, hk.order_eq_half] at heq'
    exact Nat.ModEq.eq_of_lt_of_lt heq' hi hj
  rw [Finset.card_image_of_injOn h_injOn, Finset.card_range]

end QRTour
