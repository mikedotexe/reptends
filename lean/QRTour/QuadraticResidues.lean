/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.Basic
import Mathlib.Data.Nat.Totient
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
* `QRTour.qrGenerator_iff_order_eq_half` - in `(ZMod p)ˣ`, order `half p` already forces QR
* `QRTour.pow_isQRGenerator_iff` - exact classification of which powers are QR generators
* `QRTour.pow_isQRGenerator_iff_coprime_half` - for a QR generator `k`, `k^m` is QR-generating iff `m` is coprime to `(p-1)/2`
* `QRTour.qrGenerator_pow_count_eq_totient` - the number of QR-generating powers of a QR generator is `φ((p-1)/2)`
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

noncomputable instance instDecidableQRGenerator (k : (ZMod p)ˣ) : Decidable (QRGenerator k) := by
  classical
  exact decidable_of_iff (IsSquare (k : ZMod p) ∧ orderOf k = half p) <| by
    constructor
    · rintro ⟨hk_square, hk_order⟩
      exact ⟨hk_square, hk_order⟩
    · intro hqr
      exact ⟨hqr.isSquare, hqr.order_eq_half⟩

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

/-! ### QR Generators via Order

In the unit group `(ZMod p)ˣ`, an element of order `half p` is automatically a
quadratic residue: its `half p` power is `1`, so Euler's criterion applies.
-/

/-- In `(ZMod p)ˣ`, being a QR generator is equivalent to having order `half p`. -/
theorem qrGenerator_iff_order_eq_half (hp_odd : p ≠ 2) (k : (ZMod p)ˣ) :
    QRGenerator k ↔ orderOf k = half p := by
  constructor
  · intro hk
    exact hk.order_eq_half
  · intro hk_order
    constructor
    · exact (isSquare_units_iff_pow_half_eq_one hp_odd k).2 <| by
        rw [← hk_order]
        exact pow_orderOf_eq_one k
    · exact hk_order

/-- Exact classification of which powers of `g` are QR generators. -/
theorem pow_isQRGenerator_iff (hp_odd : p ≠ 2) (g : (ZMod p)ˣ) (m : ℕ) :
    QRGenerator (g ^ m) ↔ orderOf g / Nat.gcd (orderOf g) m = half p := by
  rw [qrGenerator_iff_order_eq_half hp_odd (g ^ m), orderOf_pow]

/-- For a fixed QR generator `k`, the power `k^m` is QR-generating exactly when `m`
is coprime to `(p-1)/2`. -/
theorem pow_isQRGenerator_iff_coprime_half (hp_odd : p ≠ 2) (k : (ZMod p)ˣ)
    (hk : QRGenerator k) (m : ℕ) :
    QRGenerator (k ^ m) ↔ Nat.Coprime (half p) m := by
  rw [pow_isQRGenerator_iff hp_odd k m, hk.order_eq_half]
  have hhalf_pos : 0 < half p := by
    simp only [half]
    have hp_ge_3 : 3 ≤ p := hp.out.two_le.lt_of_ne' hp_odd
    omega
  constructor
  · intro h
    have hgcd_eq_one : Nat.gcd (half p) m = 1 := by
      have hgcd_pos : 0 < Nat.gcd (half p) m := Nat.gcd_pos_of_pos_left m hhalf_pos
      have hmul :
          half p = half p * Nat.gcd (half p) m := by
        exact (Nat.div_eq_iff_eq_mul_left hgcd_pos (Nat.gcd_dvd_left (half p) m)).1 h
      apply Nat.eq_of_mul_eq_mul_left hhalf_pos
      simpa [one_mul, mul_comm] using hmul.symm
    exact Nat.coprime_iff_gcd_eq_one.mpr hgcd_eq_one
  · intro hcop
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.div_one]

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

/-- The number of powers `k^m` with `0 ≤ m < (p-1)/2` that are again QR generators
is `φ((p-1)/2)`. -/
theorem qrGenerator_pow_count_eq_totient (hp_odd : p ≠ 2) (k : (ZMod p)ˣ)
    (hk : QRGenerator k) :
    Finset.card ((Finset.range (half p)).filter (fun m => QRGenerator (k ^ m))) =
      Nat.totient (half p) := by
  classical
  rw [Nat.totient_eq_card_coprime]
  refine congrArg Finset.card ?_
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [pow_isQRGenerator_iff_coprime_half hp_odd k hk]

/-- If `g` has full order `p - 1`, then `g^m` is QR-generating exactly when `m`
is even and its half is coprime to `(p-1)/2`. -/
theorem pow_isQRGenerator_iff_even_and_coprime_half_of_full_order
    (hp_odd : p ≠ 2) (g : (ZMod p)ˣ) (hg : orderOf g = p - 1) (m : ℕ) :
    QRGenerator (g ^ m) ↔ Even m ∧ Nat.Coprime (half p) (m / 2) := by
  rw [pow_isQRGenerator_iff hp_odd g m, hg]
  have hhalf_pos : 0 < half p := by
    simp only [half]
    have hp_ge_3 : 3 ≤ p := hp.out.two_le.lt_of_ne' hp_odd
    omega
  have hfull_pos : 0 < p - 1 := by
    have hp_ge_3 : 3 ≤ p := hp.out.two_le.lt_of_ne' hp_odd
    omega
  have hspec : p - 1 = 2 * half p := half_spec p hp_odd
  constructor
  · intro h
    have hgcd_pos : 0 < Nat.gcd (p - 1) m := Nat.gcd_pos_of_pos_left m hfull_pos
    have hmul : p - 1 = half p * Nat.gcd (p - 1) m := by
      exact (Nat.div_eq_iff_eq_mul_left hgcd_pos (Nat.gcd_dvd_left (p - 1) m)).1 h
    have hgcd_eq_two : Nat.gcd (p - 1) m = 2 := by
      have hcompare : half p * 2 = half p * Nat.gcd (p - 1) m := by
        calc
          half p * 2 = p - 1 := by simpa [Nat.mul_comm] using hspec.symm
          _ = half p * Nat.gcd (p - 1) m := hmul
      exact Nat.eq_of_mul_eq_mul_left hhalf_pos hcompare.symm
    have htwo_dvd_m : 2 ∣ m := hgcd_eq_two ▸ Nat.gcd_dvd_right (p - 1) m
    rcases htwo_dvd_m with ⟨n, hm2⟩
    refine ⟨⟨n, by simpa [Nat.two_mul, Nat.add_comm] using hm2⟩, ?_⟩
    have hgcd_half : Nat.gcd (half p) n = 1 := by
      have : 2 * Nat.gcd (half p) n = 2 := by
        calc
          2 * Nat.gcd (half p) n = Nat.gcd (2 * half p) (2 * n) := by
            symm
            exact Nat.gcd_mul_left 2 (half p) n
          _ = Nat.gcd (p - 1) m := by simpa [hspec, hm2]
          _ = 2 := hgcd_eq_two
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    have hm_div : m / 2 = n := by
      simpa [hm2, Nat.mul_comm] using Nat.mul_div_right n (by decide : 0 < 2)
    exact Nat.coprime_iff_gcd_eq_one.mpr (by simpa [hm_div] using hgcd_half)
  · rintro ⟨h_even, hcop⟩
    rcases h_even with ⟨n, hn⟩
    have hm2 : m = 2 * n := by simpa [Nat.two_mul, Nat.add_comm] using hn
    have hm_div : m / 2 = n := by
      simpa [hm2, Nat.mul_comm] using Nat.mul_div_right n (by decide : 0 < 2)
    have hgcd_eq_two : Nat.gcd (p - 1) m = 2 := by
      calc
        Nat.gcd (p - 1) m = Nat.gcd (2 * half p) (2 * n) := by simpa [hspec, hm2]
        _ = 2 * Nat.gcd (half p) n := Nat.gcd_mul_left 2 (half p) n
        _ = 2 := by rw [Nat.coprime_iff_gcd_eq_one.mp (by simpa [hm_div] using hcop), mul_one]
    rw [hgcd_eq_two, hspec]
    simpa [Nat.mul_comm] using Nat.mul_div_right (half p) (by decide : 0 < 2)

/-- If the base element already has order `(p-1)/2`, then exactly `φ((p-1)/2)` of its
powers below that order are QR-generating. -/
theorem order_eq_half_qrGenerator_pow_count_eq_totient
    (hp_odd : p ≠ 2) (g : (ZMod p)ˣ) (hg : orderOf g = half p) :
    Finset.card ((Finset.range (half p)).filter (fun m => QRGenerator (g ^ m))) =
      Nat.totient (half p) := by
  exact qrGenerator_pow_count_eq_totient hp_odd g ((qrGenerator_iff_order_eq_half hp_odd g).2 hg)

/-- If the base element has full order `p - 1`, then exactly `φ((p-1)/2)` of its
powers below that order are QR-generating. -/
theorem order_eq_full_qrGenerator_pow_count_eq_totient
    (hp_odd : p ≠ 2) (g : (ZMod p)ˣ) (hg : orderOf g = p - 1) :
    Finset.card ((Finset.range (p - 1)).filter (fun m => QRGenerator (g ^ m))) =
      Nat.totient (half p) := by
  classical
  rw [Nat.totient_eq_card_coprime]
  let source := (Finset.range (half p)).filter (fun n => Nat.Coprime (half p) n)
  let target := (Finset.range (p - 1)).filter (fun m => QRGenerator (g ^ m))
  suffices source.card = target.card by simpa [source, target] using this.symm
  apply Finset.card_nbij (fun n => 2 * n)
  · intro n hn
    have hn' : n ∈ source := by simpa [source] using hn
    rcases Finset.mem_filter.mp hn' with ⟨hn_lt, hn_coprime⟩
    show 2 * n ∈ target
    apply Finset.mem_filter.mpr
    constructor
    · have hn_lt' : n < half p := by simpa using hn_lt
      rw [Finset.mem_range]
      calc
        2 * n < 2 * half p := Nat.mul_lt_mul_of_pos_left hn_lt' (by decide : 0 < 2)
        _ = p - 1 := (half_spec p hp_odd).symm
    · exact
        (pow_isQRGenerator_iff_even_and_coprime_half_of_full_order hp_odd g hg (2 * n)).2
          ⟨⟨n, by omega⟩, by simpa [Nat.mul_comm] using hn_coprime⟩
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (by simpa [Nat.mul_comm] using hab)
  · intro m hm
    have hm' : m ∈ target := by simpa [target] using hm
    rcases Finset.mem_filter.mp hm' with ⟨hm_lt, hm_qr⟩
    rcases (pow_isQRGenerator_iff_even_and_coprime_half_of_full_order hp_odd g hg m).1 hm_qr with
      ⟨h_even, hcop⟩
    rcases h_even with ⟨n, hn⟩
    have hm2 : m = 2 * n := by simpa [Nat.two_mul, Nat.add_comm] using hn
    refine ⟨n, ?_, by simpa [hm2]⟩
    show n ∈ source
    apply Finset.mem_filter.mpr
    constructor
    · rw [Finset.mem_range]
      rw [Finset.mem_range] at hm_lt
      have hm_lt' : 2 * n < 2 * half p := by simpa [hm2, half_spec p hp_odd] using hm_lt
      exact Nat.lt_of_mul_lt_mul_left hm_lt'
    · simpa [hm2, Nat.mul_comm] using hcop

/-- Base-level stride count theorem for QR-generating powers.

If the base element has order `(p-1)/2` or `p-1`, then the number of strides
producing a QR generator is exactly `φ((p-1)/2)`. -/
theorem base_qrGenerator_pow_count_eq_totient
    (hp_odd : p ≠ 2) (g : (ZMod p)ˣ)
    (hg : orderOf g = half p ∨ orderOf g = p - 1) :
    Finset.card ((Finset.range (orderOf g)).filter (fun m => QRGenerator (g ^ m))) =
      Nat.totient (half p) := by
  rcases hg with hg_half | hg_full
  · simpa [hg_half] using order_eq_half_qrGenerator_pow_count_eq_totient hp_odd g hg_half
  · simpa [hg_full] using order_eq_full_qrGenerator_pow_count_eq_totient hp_odd g hg_full

end QRTour
