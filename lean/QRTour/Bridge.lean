/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.RemainderOrbit
import QRTour.Digits

/-!
# Bridge Primes: "Just Under a Power" Structure

This module formalizes primes of the form p = B^k - d, which exhibit beautiful
block-level structure in their reptends. These "bridge primes" satisfy B^k ≡ d (mod p),
which means the remainder sequence has a clean k-step recurrence: r[n+k] = d × r[n].

## Examples

- p = 97 = 10² - 3: d = 3 has order 48 = (97-1)/2, a QR generator!
- p = 997 = 10³ - 3: d = 3 has order 498 = (997-1)/2, also a QR generator!

## Main Definitions

* `QRTour.Bridge` - A bridge prime configuration: p = B^k - d

## Main Results

* `QRTour.Bridge.remainder_k_step` - r[n+k] = d × r[n] in ZMod p
* `QRTour.Bridge.block_start_geometric` - k-digit blocks form geometric progression
-/

namespace QRTour

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### Bridge Prime Configuration -/

/-- A bridge prime configuration captures p = B^k - d.
This means B^k ≡ d (mod p), giving clean k-step dynamics. -/
structure Bridge (B p k d : ℕ) where
  /-- p is prime -/
  prime_p : Nat.Prime p
  /-- k is positive (the power) -/
  hk_pos : 0 < k
  /-- d is positive (the "deficit") -/
  hd_pos : 0 < d
  /-- d < p (so d is a valid residue) -/
  hd_lt_p : d < p
  /-- The bridge equation: B^k = d in ZMod p -/
  bridge_eq : (B : ZMod p) ^ k = d

/-! ### k-Step Remainder Recurrence -/

/-- The key k-step recurrence: r[n + k] = d × r[n].
This follows directly from B^k ≡ d (mod p). -/
theorem Bridge.remainder_k_step (br : Bridge B p k d) (n : ℕ) :
    remainder (p := p) B (n + k) = d * remainder (p := p) B n := by
  haveI : Fact (Nat.Prime p) := ⟨br.prime_p⟩
  simp only [remainder_eq_pow, pow_add, br.bridge_eq]
  ring

/-- Iterated k-step: r[n + j*k] = d^j × r[n]. -/
theorem Bridge.remainder_jk_step (br : Bridge B p k d) (n j : ℕ) :
    remainder (p := p) B (n + j * k) = (d : ZMod p) ^ j * remainder (p := p) B n := by
  haveI : Fact (Nat.Prime p) := ⟨br.prime_p⟩
  induction j with
  | zero => simp
  | succ j ih =>
    calc remainder (p := p) B (n + (j + 1) * k)
        = remainder (p := p) B ((n + j * k) + k) := by ring_nf
      _ = d * remainder (p := p) B (n + j * k) := br.remainder_k_step (n + j * k)
      _ = d * ((d : ZMod p) ^ j * remainder (p := p) B n) := by rw [ih]
      _ = (d : ZMod p) ^ (j + 1) * remainder (p := p) B n := by ring

/-- Block-starting remainders form a geometric sequence in powers of d. -/
theorem Bridge.block_start_geometric (br : Bridge B p k d) (j : ℕ) :
    remainder (p := p) B (j * k) = (d : ZMod p) ^ j := by
  haveI : Fact (Nat.Prime p) := ⟨br.prime_p⟩
  have := br.remainder_jk_step 0 j
  simp only [zero_add, remainder, mul_one] at this
  exact this

/-! ### Concrete Bridge Examples -/

/-- 97 = 10² - 3 is a bridge prime with k = 2, d = 3. -/
theorem bridge_97 : Bridge 10 97 2 3 where
  prime_p := by decide
  hk_pos := by decide
  hd_pos := by decide
  hd_lt_p := by decide
  bridge_eq := by native_decide

-- Note: 997 = 10³ - 3 is also a bridge prime, but native_decide for 997³
-- is computationally expensive. The theory applies identically.

section Examples

-- Provide the Fact instance for concrete examples
instance : Fact (Nat.Prime 97) := ⟨by native_decide⟩

/-- For 97, block starting remainders: r[0]=1, r[2]=3, r[4]=9, r[6]=27, ... -/
example : @remainder 97 _ 10 0 = 1 := by native_decide
example : @remainder 97 _ 10 2 = 3 := by native_decide
example : @remainder 97 _ 10 4 = 9 := by native_decide
example : @remainder 97 _ 10 6 = 27 := by native_decide
example : @remainder 97 _ 10 8 = 81 := by native_decide

end Examples

end QRTour
