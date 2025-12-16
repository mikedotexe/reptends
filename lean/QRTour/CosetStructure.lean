/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.Bridge
import QRTour.QuadraticResidues

/-!
# Two-Coset Structure of Bridge Reptends

This module explores the observation that for bridge primes p = B^k - d,
the reptends of a/p partition into two cosets of (ℤ/pℤ)* based on whether
a is a quadratic residue.

## Key Insight

For p = 139 = 12² - 5:
- QR numerators (1, 3, 4, 5, ...) give remainders in the QR coset
- NQR numerators (2, 6, 7, 8, ...) give remainders in the NQR coset
- The pattern "toggles" at block boundaries (every k = 2 steps)

This reveals a hidden two-fold symmetry in the remainder sequences!

## Main Results

* `QRTour.factor_bridge_structure` - Factors of B^k - d inherit bridge structure
-/

namespace QRTour

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### Factor Inheritance

The observation that 19 | 95 = 10² - 5 suggests a factor tower phenomenon.
If p | (B^k - d) with d < p, then p inherits the bridge equation B^k ≡ d.
-/

/-- If p divides B^k - d with d < p, then p inherits bridge-like structure. -/
theorem factor_bridge_structure (B k d p : ℕ) (_hp : Nat.Prime p)
    (hdiv : p ∣ B^k - d) (_hd_pos : 0 < d) (_hd_lt : d < p) (hBk : d < B^k) :
    (B : ZMod p)^k = d := by
  haveI : Fact (Nat.Prime p) := ⟨_hp⟩
  -- Since p | (B^k - d) and d < B^k, we have B^k - d ≡ 0 (mod p)
  -- Therefore B^k ≡ d (mod p)
  have hsub : (B^k - d) % p = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hmod : B^k % p = d % p := by
    have h1 : B^k = (B^k - d) + d := by omega
    rw [h1, Nat.add_mod, hsub, zero_add, Nat.mod_mod]
  -- Convert to ZMod: natCast values equal iff congruent mod p
  simp only [← Nat.cast_pow]
  exact (ZMod.natCast_eq_natCast_iff' (B^k) d p).mpr hmod

/-! ### Enumeration Strategy

To enumerate useful items for our pursuit:

1. **Bridge Primes**: p = B^k ± d with small d
   - These have clean k-periodic structure
   - QR/NQR cosets are well-behaved

2. **Factor Towers**: Primes dividing B^k ± d
   - Inherit bridge structure from parent
   - May have different period but same coset behavior

3. **Coset Representatives**: For each p, find minimal QR and NQR values
   - These generate the two coset orbits efficiently
   - Help identify the alternation pattern

4. **Period Analysis**: The lcm of k and orderOf(B)
   - Determines full reptend period
   - Coset toggle points are at multiples of k
-/

section Examples

instance instPrime139 : Fact (Nat.Prime 139) := ⟨by native_decide⟩

/-- For p = 139 = 12² - 5, verify the bridge equation. -/
example : (12 : ZMod 139)^2 = 5 := by native_decide

/-- 1 is QR (trivially). -/
example : IsSquare (1 : ZMod 139) := ⟨1, by simp⟩

/-- 5 is QR in ZMod 139 (since 5 = 12² mod 139 and 12 exists). -/
example : IsSquare (5 : ZMod 139) := ⟨12, by native_decide⟩

end Examples

end QRTour