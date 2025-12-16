/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Quadratic Residues and QR Generators

This module defines quadratic residues modulo a prime and the notion of a
"QR generator" - an element whose powers enumerate all quadratic residues.

## Main Definitions

* `QRTour.QRGenerator` - An element k is a QR generator if it's a quadratic residue
  with multiplicative order equal to (p-1)/2.

## Main Results

* `QRTour.isSquare_units_iff_pow_half_eq_one` - Euler's criterion: a is a QR iff a^((p-1)/2) = 1
* `QRTour.qr_generator_generates_qrs` - Powers of a QR generator enumerate all QRs

## Porting Notes

The Agda version used a Σ-type `QR a = Σ x. x² ≡ₚ a`. In Lean/Mathlib, we use
the predicate `IsSquare : α → Prop` which is equivalent but integrates better
with the library.
-/

namespace QRTour

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ### Quadratic Residues

In Mathlib, quadratic residues are characterized by `IsSquare`.
For `ZMod p` with prime p, this is equivalent to the Legendre symbol being 1.
-/

/-- A QR generator is a unit k with order (p-1)/2 that is itself a quadratic residue.
Such an element generates the unique subgroup of index 2 in the cyclic group (ZMod p)ˣ. -/
structure QRGenerator (k : (ZMod p)ˣ) : Prop where
  /-- The generator is a quadratic residue -/
  isSquare : IsSquare (k : ZMod p)
  /-- The order equals half of p - 1 -/
  order_eq_half : orderOf k = half p

/-! ### Euler's Criterion

The key connection: a nonzero element is a QR iff its ((p-1)/2)-th power equals 1.
-/

/-- For odd prime p, p / 2 = (p - 1) / 2 = half p. -/
theorem prime_div_two_eq_half (hp_odd : p ≠ 2) : p / 2 = half p := by
  -- From Nat.two_mul_odd_div_two: 2 * (p / 2) = p - 1 for odd p
  have hodd : p % 2 = 1 := hp.out.mod_two_eq_one_iff_ne_two.mpr hp_odd
  have h := Nat.two_mul_odd_div_two hodd
  -- So p / 2 = (p - 1) / 2
  simp only [half]
  omega

/-- Euler's criterion for units: a unit is a square iff its half-power is 1. -/
theorem isSquare_units_iff_pow_half_eq_one (hp_odd : p ≠ 2) (a : (ZMod p)ˣ) :
    IsSquare (a : ZMod p) ↔ a ^ (half p) = 1 := by
  -- Rewrite half p as p / 2 using our helper
  rw [← prime_div_two_eq_half hp_odd]
  -- Connect IsSquare (a : ZMod p) to ∃ y : (ZMod p)ˣ, y ^ 2 = a
  have h_equiv : IsSquare (a : ZMod p) ↔ (∃ y : (ZMod p)ˣ, y ^ 2 = a) := by
    constructor
    · rintro ⟨z, hz⟩
      have hz_ne : z ≠ 0 := by
        intro h
        simp only [h, mul_zero] at hz
        exact Units.ne_zero a hz
      refine ⟨Units.mk0 z hz_ne, ?_⟩
      ext
      simp only [sq, Units.val_mul, Units.val_mk0, hz]
    · rintro ⟨y, hy⟩
      refine ⟨y.val, ?_⟩
      rw [sq] at hy
      simp only [← Units.val_mul, hy]
  rw [h_equiv]
  -- Now use Mathlib's Euler criterion
  exact ZMod.euler_criterion_units p a

/-! ### QR Generator Enumeration

When k has order (p-1)/2, its powers k^0, k^1, ..., k^((p-1)/2 - 1) are all distinct
and form the complete set of quadratic residues.
-/

/-- The powers of a QR generator enumerate all quadratic residues. -/
theorem qr_generator_generates_qrs (hp_odd : p ≠ 2) (k : (ZMod p)ˣ) (hk : QRGenerator k) :
    ∀ a : (ZMod p)ˣ, IsSquare (a : ZMod p) →
      ∃ j : ℕ, j < half p ∧ k ^ j = a := by
  intro a ha
  -- Step 1: a^(half p) = 1 by Euler's criterion
  have ha_pow : a ^ (half p) = 1 := (isSquare_units_iff_pow_half_eq_one hp_odd a).mp ha
  -- Step 2: k^(half p) = 1 since orderOf k = half p
  have hk_pow : k ^ (half p) = 1 := by rw [← hk.order_eq_half]; exact pow_orderOf_eq_one k
  -- Step 3: Both a and k are in the kernel of the (half p)-power map
  let ker := (powMonoidHom (half p) : (ZMod p)ˣ →* (ZMod p)ˣ).ker
  have ha_ker : a ∈ ker := by rw [MonoidHom.mem_ker, powMonoidHom_apply]; exact ha_pow
  -- Step 4: zpowers k ⊆ ker (any power of k has k^(half p) = 1)
  have zpowers_le_ker : Subgroup.zpowers k ≤ ker := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, hk_pow, one_zpow]
  -- Step 5: Cardinality argument - both have the same size, so they're equal
  have card_zpowers : Nat.card (Subgroup.zpowers k) = half p := by
    rw [Nat.card_zpowers, hk.order_eq_half]
  have card_ker : Nat.card ker = half p := by
    have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units]
    have := IsCyclic.card_powMonoidHom_ker (G := (ZMod p)ˣ) (half p)
    rw [this, hcard]
    -- gcd(p - 1, half p) = half p since half p = (p-1)/2 divides p - 1
    have hdiv : half p ∣ p - 1 := by
      use 2
      rw [mul_comm]
      exact half_spec p hp_odd
    exact Nat.gcd_eq_right hdiv
  -- Step 6: Same cardinality + subset ⟹ equality
  have zpowers_eq_ker : Subgroup.zpowers k = ker := by
    apply Subgroup.eq_of_le_of_card_ge zpowers_le_ker
    rw [card_ker, card_zpowers]
  -- Step 7: a ∈ ker = zpowers k, so a = k^j for some j
  have ha_zpowers : a ∈ Subgroup.zpowers k := zpowers_eq_ker ▸ ha_ker
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ha_zpowers
  -- Step 8: Reduce j modulo half p to get 0 ≤ j' < half p with k^j' = a
  have hhalf_pos : 0 < half p := by
    simp only [half]
    have hp_ge_3 : 3 ≤ p := hp.out.two_le.lt_of_ne' hp_odd
    omega
  use (j % (half p : ℤ)).toNat
  constructor
  · have hmod_nonneg : 0 ≤ j % (half p : ℤ) := Int.emod_nonneg j (by omega : (half p : ℤ) ≠ 0)
    have hmod_lt : j % (half p : ℤ) < half p := Int.emod_lt_of_pos j (by omega)
    omega
  · rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg j (by omega))]
    -- k^(j mod half p) = k^j = a since orderOf k = half p
    have heq : k ^ (j % (half p : ℤ)) = k ^ j := by
      rw [zpow_eq_zpow_iff_modEq, hk.order_eq_half]
      exact Int.mod_modEq j (half p)
    rw [heq, hj]

/-- Corollary: The number of distinct powers k^j for j < half p equals half p. -/
theorem qr_generator_orbit_card (_hp_odd : p ≠ 2) (k : (ZMod p)ˣ) (hk : QRGenerator k) :
    Finset.card (Finset.image (fun j => k ^ j) (Finset.range (half p))) = half p := by
  -- The map j ↦ k^j is injective on [0, orderOf k) = [0, half p)
  have h_injOn : Set.InjOn (fun j => k ^ j) (Finset.range (half p)) := by
    intro i hi j hj hij
    rw [Finset.coe_range, Set.mem_Iio] at hi hj
    simp only at hij
    -- k^i = k^j implies i ≡ j (mod orderOf k)
    rw [pow_eq_pow_iff_modEq] at hij
    rw [hk.order_eq_half] at hij
    -- Since both i, j < half p, and i ≡ j (mod half p), we have i = j
    exact Nat.ModEq.eq_of_lt_of_lt hij hi hj
  rw [Finset.card_image_of_injOn h_injOn, Finset.card_range]

end QRTour
