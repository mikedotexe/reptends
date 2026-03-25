/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Orbit-Weave Coordinate Arithmetic

This module begins the Lean surface for the exact `B = qM + k` layer tracked in
the proof atlas. Its current scope is deliberately finite:

- package the Euclidean-division data behind a block coordinate,
- expose the raw coefficient stream `q * k^j`,
- keep the standard labels (`quotient q`, `remainder k`) at the API boundary.

The heavier rational-series and carry-facing theorems belong in later passes.
-/

namespace QRTour

open Finset
open scoped BigOperators

/-- A block coordinate with block base `B = base^stride` and positive modulus. -/
structure BlockCoordinate where
  base : ℕ
  modulus : ℕ
  stride : ℕ
  modulus_pos : 0 < modulus

/-- The block base `B = base^stride`. -/
def BlockCoordinate.blockBase (C : BlockCoordinate) : ℕ := C.base ^ C.stride

/-- The quotient `q` in `B = qM + k`. -/
def BlockCoordinate.quotientQ (C : BlockCoordinate) : ℕ := C.blockBase / C.modulus

/-- The remainder `k = B mod M`. -/
def BlockCoordinate.remainderK (C : BlockCoordinate) : ℕ := C.blockBase % C.modulus

/-- A good mode is a coordinate where the block base exceeds the modulus. -/
def BlockCoordinate.goodMode (C : BlockCoordinate) : Prop := C.modulus < C.blockBase

/-- The raw coefficient `q * k^j` before carry normalization. -/
def BlockCoordinate.rawCoefficient (C : BlockCoordinate) (j : ℕ) : ℕ :=
  C.quotientQ * C.remainderK ^ j

/-- The exact rational block term `q*k^j / B^(j+1)`. -/
def BlockCoordinate.partialSumQ (C : BlockCoordinate) (n : ℕ) : ℚ :=
  ∑ j ∈ range n, (C.rawCoefficient j : ℚ) / (C.blockBase : ℚ) ^ (j + 1)

/-- The exact real block term `q*k^j / B^(j+1)`. -/
noncomputable def BlockCoordinate.seriesTermR (C : BlockCoordinate) (j : ℕ) : ℝ :=
  (C.rawCoefficient j : ℝ) / (C.blockBase : ℝ) ^ (j + 1)

/-- The rational ratio `k / B`. -/
def BlockCoordinate.ratioQ (C : BlockCoordinate) : ℚ :=
  (C.remainderK : ℚ) / C.blockBase

/-- The real ratio `k / B`. -/
noncomputable def BlockCoordinate.ratioR (C : BlockCoordinate) : ℝ :=
  (C.remainderK : ℝ) / C.blockBase

/-- The reptend integer `R = (B^L - 1) / M`. -/
def BlockCoordinate.reptendInteger (C : BlockCoordinate) (period : ℕ) : ℕ :=
  (C.blockBase ^ period - 1) / C.modulus

/-- The body term `W = (B^L - k^L) / M`. -/
def BlockCoordinate.bodyTerm (C : BlockCoordinate) (period : ℕ) : ℕ :=
  (C.blockBase ^ period - C.remainderK ^ period) / C.modulus

/-- The correction term `F = (k^L - 1) / M`. -/
def BlockCoordinate.correctionTerm (C : BlockCoordinate) (period : ℕ) : ℕ :=
  (C.remainderK ^ period - 1) / C.modulus

/-- The block base decomposes as `B = qM + k`. -/
theorem BlockCoordinate.blockBase_eq_quotientQ_mul_modulus_add_remainderK
    (C : BlockCoordinate) :
    C.blockBase = C.quotientQ * C.modulus + C.remainderK := by
  simpa [BlockCoordinate.quotientQ, BlockCoordinate.remainderK, Nat.mul_comm] using
    (Nat.div_add_mod C.blockBase C.modulus).symm

/-- The remainder coordinate satisfies `0 <= k < M`. -/
theorem BlockCoordinate.remainderK_lt_modulus (C : BlockCoordinate) :
    C.remainderK < C.modulus := by
  exact Nat.mod_lt C.blockBase C.modulus_pos

/-- In a good mode, the block base is positive. -/
theorem BlockCoordinate.blockBase_pos_of_goodMode (C : BlockCoordinate) (hgood : C.goodMode) :
    0 < C.blockBase := by
  exact lt_trans C.modulus_pos hgood

/-- In a good mode, the remainder coordinate is strictly smaller than the block base. -/
theorem BlockCoordinate.remainderK_lt_blockBase (C : BlockCoordinate) (hgood : C.goodMode) :
    C.remainderK < C.blockBase := by
  exact lt_trans C.remainderK_lt_modulus hgood

/-- The Euclidean quotient is positive exactly on good block coordinates. -/
theorem BlockCoordinate.quotientQ_pos_of_goodMode (C : BlockCoordinate) (hgood : C.goodMode) :
    0 < C.quotientQ := by
  by_contra hq
  have hq0 : C.quotientQ = 0 := Nat.eq_zero_of_not_pos hq
  have hklt : C.remainderK < C.blockBase := C.remainderK_lt_blockBase hgood
  rw [C.blockBase_eq_quotientQ_mul_modulus_add_remainderK, hq0] at hklt
  simp at hklt

/-- The Euclidean decomposition also reads `qM = B - k`. -/
theorem BlockCoordinate.quotientQ_mul_modulus_eq_blockBase_sub_remainderK (C : BlockCoordinate) :
    C.quotientQ * C.modulus = C.blockBase - C.remainderK := by
  have h := C.blockBase_eq_quotientQ_mul_modulus_add_remainderK
  omega

/-- The quotient is exactly the gap `(B-k)/M`. -/
theorem BlockCoordinate.quotientQ_eq_gap_div_modulus (C : BlockCoordinate) :
    C.quotientQ = (C.blockBase - C.remainderK) / C.modulus := by
  calc
    C.quotientQ = (C.modulus * C.quotientQ) / C.modulus := by
      exact (Nat.mul_div_right C.quotientQ C.modulus_pos).symm
    _ = (C.quotientQ * C.modulus) / C.modulus := by rw [Nat.mul_comm]
    _ = (C.blockBase - C.remainderK) / C.modulus := by
      rw [C.quotientQ_mul_modulus_eq_blockBase_sub_remainderK]

/-- Claim `positive_q_good_modes`: a good mode gives a positive quotient `q = (B-k)/M`. -/
theorem BlockCoordinate.positive_q_good_modes (C : BlockCoordinate) (hgood : C.goodMode) :
    0 < (C.blockBase - C.remainderK) / C.modulus := by
  rw [← C.quotientQ_eq_gap_div_modulus]
  exact C.quotientQ_pos_of_goodMode hgood

@[simp] theorem BlockCoordinate.rawCoefficient_zero (C : BlockCoordinate) :
    C.rawCoefficient 0 = C.quotientQ := by
  simp [BlockCoordinate.rawCoefficient]

@[simp] theorem BlockCoordinate.rawCoefficient_succ (C : BlockCoordinate) (j : ℕ) :
    C.rawCoefficient (j + 1) = C.rawCoefficient j * C.remainderK := by
  unfold BlockCoordinate.rawCoefficient
  rw [pow_succ]
  ac_rfl

/-- Rewriting a rational series term as a scaled geometric-ratio power. -/
theorem BlockCoordinate.partialSumQ_term_eq_scale_mul_ratio_pow (C : BlockCoordinate)
    (hgood : C.goodMode) (j : ℕ) :
    (C.rawCoefficient j : ℚ) / (C.blockBase : ℚ) ^ (j + 1) =
      ((C.quotientQ : ℚ) / C.blockBase) * C.ratioQ ^ j := by
  have hB0 : (C.blockBase : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (C.blockBase_pos_of_goodMode hgood))
  unfold BlockCoordinate.ratioQ BlockCoordinate.rawCoefficient
  rw [show ((C.blockBase : ℚ) ^ (j + 1)) = (C.blockBase : ℚ) * (C.blockBase : ℚ) ^ j by
    rw [pow_succ']]
  rw [div_pow]
  field_simp [hB0]
  all_goals simp [Nat.cast_mul, Nat.cast_pow]

/-- Finite partial sums of the `q*k^j` series have the exact closed form. -/
theorem BlockCoordinate.partialSumQ_eq_finite (C : BlockCoordinate) (hgood : C.goodMode) (n : ℕ) :
    C.partialSumQ n =
      (((C.blockBase : ℚ) ^ n - (C.remainderK : ℚ) ^ n) /
        ((C.modulus : ℚ) * (C.blockBase : ℚ) ^ n)) := by
  let B : ℚ := C.blockBase
  let k : ℚ := C.remainderK
  let q : ℚ := C.quotientQ
  let x : ℚ := C.ratioQ
  have hB0 : B ≠ 0 := by
    dsimp [B]
    exact_mod_cast (Nat.ne_of_gt (C.blockBase_pos_of_goodMode hgood))
  have hklt : k < B := by
    dsimp [k, B]
    exact_mod_cast (C.remainderK_lt_blockBase hgood)
  have hx : x ≠ 1 := by
    dsimp [x]
    have hxlt : x < 1 := by
      dsimp [BlockCoordinate.ratioQ]
      exact (div_lt_one (show (0 : ℚ) < B by positivity)).2 hklt
    linarith
  have hm0 : (C.modulus : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt C.modulus_pos)
  have hgap0 : B - k ≠ 0 := by
    linarith
  have hkB0 : k - B ≠ 0 := by
    linarith
  have hx0 : x - 1 ≠ 0 := by
    exact sub_ne_zero.mpr hx
  have hgap : q * (C.modulus : ℚ) = B - k := by
    dsimp [q, k, B]
    have hkle : C.remainderK ≤ C.blockBase := le_of_lt (C.remainderK_lt_blockBase hgood)
    exact_mod_cast C.quotientQ_mul_modulus_eq_blockBase_sub_remainderK
  have hxpow : x ^ n = k ^ n / B ^ n := by
    dsimp [x, BlockCoordinate.ratioQ]
    rw [div_pow]
  have hxsub : x - 1 = (k - B) / B := by
    dsimp [x, BlockCoordinate.ratioQ]
    rw [show (1 : ℚ) = B / B by rw [div_self hB0], sub_div]
  have hfrac :
      (q / B) * ((k ^ n / B ^ n - 1) / ((k - B) / B)) = (q / (B - k)) * (1 - k ^ n / B ^ n) := by
    have haux :
        ((k ^ n / B ^ n - 1) / ((k - B) / B)) = (B / (B - k)) * (1 - k ^ n / B ^ n) := by
      field_simp [hB0, hgap0, hkB0]
      ring_nf
    rw [haux]
    field_simp [hB0, hgap0]
  have hquot : q / (B - k) = (1 : ℚ) / C.modulus := by
    field_simp [hm0, hgap0]
    linarith [hgap]
  calc
    C.partialSumQ n
      = (q / B) * ∑ j ∈ range n, x ^ j := by
          unfold BlockCoordinate.partialSumQ
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simpa [B, q, x] using C.partialSumQ_term_eq_scale_mul_ratio_pow hgood j
    _ = (q / B) * ((x ^ n - 1) / (x - 1)) := by rw [geom_sum_eq hx n]
    _ = (q / B) * ((k ^ n / B ^ n - 1) / ((k - B) / B)) := by rw [hxpow, hxsub]
    _ = (q / (B - k)) * (1 - k ^ n / B ^ n) := hfrac
    _ = ((1 : ℚ) / C.modulus) * (1 - k ^ n / B ^ n) := by rw [hquot]
    _ = ((1 : ℚ) / C.modulus) * (1 - x ^ n) := by rw [hxpow]
    _ = (B ^ n - k ^ n) / ((C.modulus : ℚ) * B ^ n) := by
          rw [hxpow]
          field_simp [hB0, hm0]

/-- Exact rational identity `1/M = q/(B-k)` on good block coordinates. -/
theorem BlockCoordinate.one_div_modulus_eq_quotientQ_div_gap (C : BlockCoordinate)
    (hgood : C.goodMode) :
    (1 : ℚ) / C.modulus = (C.quotientQ : ℚ) / ((C.blockBase : ℚ) - C.remainderK) := by
  have hm0 : (C.modulus : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt C.modulus_pos)
  have hgap0 : ((C.blockBase : ℚ) - C.remainderK) ≠ 0 := by
    have hklt : (C.remainderK : ℚ) < C.blockBase := by
      exact_mod_cast (C.remainderK_lt_blockBase hgood)
    have hgap_pos : (0 : ℚ) < (C.blockBase : ℚ) - C.remainderK := by
      linarith
    linarith
  have hgap :
      (C.quotientQ : ℚ) * C.modulus = (C.blockBase : ℚ) - C.remainderK := by
    have hkle : C.remainderK ≤ C.blockBase := le_of_lt (C.remainderK_lt_blockBase hgood)
    exact_mod_cast C.quotientQ_mul_modulus_eq_blockBase_sub_remainderK
  field_simp [hm0, hgap0]
  simpa [mul_comm] using hgap.symm

/-- Claim `series_q_weighted_identity`: the exact `q*k^j / B^(j+1)` series sums to `1/M`. -/
theorem BlockCoordinate.series_q_weighted_identity (C : BlockCoordinate) (hgood : C.goodMode) :
    HasSum (fun j : ℕ => C.seriesTermR j) ((1 : ℝ) / C.modulus) := by
  let B : ℝ := C.blockBase
  let k : ℝ := C.remainderK
  let q : ℝ := C.quotientQ
  let x : ℝ := C.ratioR
  have hB0 : B ≠ 0 := by
    dsimp [B]
    exact_mod_cast (Nat.ne_of_gt (C.blockBase_pos_of_goodMode hgood))
  have hklt : k < B := by
    dsimp [k, B]
    exact_mod_cast (C.remainderK_lt_blockBase hgood)
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, BlockCoordinate.ratioR]
    positivity
  have hx_lt_one : x < 1 := by
    dsimp [x, BlockCoordinate.ratioR]
    exact (div_lt_one (show (0 : ℝ) < B by positivity)).2 hklt
  have hgeom :
      HasSum (fun j : ℕ => (q / B) * x ^ j) ((q / B) * (1 - x)⁻¹) :=
    (hasSum_geometric_of_lt_one hx_nonneg hx_lt_one).mul_left (q / B)
  have hgap0 : B - k ≠ 0 := by
    linarith
  have hquot :
      (q / B) * (1 - x)⁻¹ = (1 : ℝ) / C.modulus := by
    have hm0 : (C.modulus : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt C.modulus_pos)
    have hgap :
        q * (C.modulus : ℝ) = B - k := by
      dsimp [q, k, B]
      have hkle : C.remainderK ≤ C.blockBase := le_of_lt (C.remainderK_lt_blockBase hgood)
      exact_mod_cast C.quotientQ_mul_modulus_eq_blockBase_sub_remainderK
    have hx0 : 1 - x ≠ 0 := by
      linarith
    have hxsub : 1 - x = (B - k) / B := by
      dsimp [x, BlockCoordinate.ratioR]
      rw [show (1 : ℝ) = B / B by rw [div_self hB0], sub_div]
    have hscale : (q / B) * (1 - x)⁻¹ = q / (B - k) := by
      have haux : (1 - x)⁻¹ = B / (B - k) := by
        rw [hxsub]
        field_simp [hB0, hgap0, hx0]
      rw [haux]
      field_simp [hB0, hgap0]
    rw [hscale]
    field_simp [hm0, hgap0]
    linarith [hgap]
  convert hgeom using 1
  · ext j
    dsimp [B, q, x, BlockCoordinate.seriesTermR, BlockCoordinate.ratioR, BlockCoordinate.rawCoefficient]
    rw [show ((C.blockBase : ℝ) ^ (j + 1)) = (C.blockBase : ℝ) * (C.blockBase : ℝ) ^ j by
      rw [pow_succ']]
    rw [div_pow]
    field_simp [hB0]
    all_goals simp [Nat.cast_mul, Nat.cast_pow]
  · exact hquot.symm

/-- The modulus divides the exact gap `B - k`. -/
theorem BlockCoordinate.modulus_dvd_blockBase_sub_remainderK (C : BlockCoordinate) :
    C.modulus ∣ C.blockBase - C.remainderK := by
  refine ⟨C.quotientQ, ?_⟩
  simpa [Nat.mul_comm] using C.quotientQ_mul_modulus_eq_blockBase_sub_remainderK.symm

/-- The modulus divides `B^L - k^L` for every period length `L`. -/
theorem BlockCoordinate.modulus_dvd_blockBase_pow_sub_remainderK_pow
    (C : BlockCoordinate) (period : ℕ) :
    C.modulus ∣ C.blockBase ^ period - C.remainderK ^ period := by
  exact dvd_trans C.modulus_dvd_blockBase_sub_remainderK
    (Nat.sub_dvd_pow_sub_pow C.blockBase C.remainderK period)

/-- The body term clears the modulus exactly. -/
theorem BlockCoordinate.bodyTerm_mul_modulus_eq
    (C : BlockCoordinate) (period : ℕ) :
    C.bodyTerm period * C.modulus = C.blockBase ^ period - C.remainderK ^ period := by
  unfold BlockCoordinate.bodyTerm
  rw [Nat.mul_comm]
  exact Nat.mul_div_cancel' (C.modulus_dvd_blockBase_pow_sub_remainderK_pow period)

/-- The correction term clears the modulus exactly when `k^L - 1` is divisible by `M`. -/
theorem BlockCoordinate.correctionTerm_mul_modulus_eq
    (C : BlockCoordinate) (period : ℕ)
    (hclosure : C.modulus ∣ C.remainderK ^ period - 1) :
    C.correctionTerm period * C.modulus = C.remainderK ^ period - 1 := by
  unfold BlockCoordinate.correctionTerm
  rw [Nat.mul_comm]
  exact Nat.mul_div_cancel' hclosure

/-- The reptend integer clears the modulus exactly when the closure term does. -/
theorem BlockCoordinate.reptendInteger_mul_modulus_eq
    (C : BlockCoordinate) (period : ℕ) (hgood : C.goodMode)
    (hpow : 1 ≤ C.remainderK ^ period)
    (hclosure : C.modulus ∣ C.remainderK ^ period - 1) :
    C.reptendInteger period * C.modulus = C.blockBase ^ period - 1 := by
  have hpow_le : C.remainderK ^ period ≤ C.blockBase ^ period := by
    exact Nat.pow_le_pow_left (le_of_lt (C.remainderK_lt_blockBase hgood)) period
  have hdiv_total : C.modulus ∣ C.blockBase ^ period - 1 := by
    have hsplit :
        C.blockBase ^ period - 1 =
          (C.blockBase ^ period - C.remainderK ^ period) + (C.remainderK ^ period - 1) := by
      omega
    rw [hsplit]
    exact dvd_add (C.modulus_dvd_blockBase_pow_sub_remainderK_pow period) hclosure
  unfold BlockCoordinate.reptendInteger
  rw [Nat.mul_comm]
  exact Nat.mul_div_cancel' hdiv_total

/-- The exact body/correction decomposition `R = W + F`. -/
theorem BlockCoordinate.reptendInteger_eq_bodyTerm_add_correctionTerm
    (C : BlockCoordinate) (period : ℕ) (hgood : C.goodMode)
    (hpow : 1 ≤ C.remainderK ^ period)
    (hclosure : C.modulus ∣ C.remainderK ^ period - 1) :
    C.reptendInteger period = C.bodyTerm period + C.correctionTerm period := by
  have hpow_le : C.remainderK ^ period ≤ C.blockBase ^ period := by
    exact Nat.pow_le_pow_left (le_of_lt (C.remainderK_lt_blockBase hgood)) period
  apply Nat.eq_of_mul_eq_mul_right C.modulus_pos
  rw [Nat.add_mul]
  rw [C.reptendInteger_mul_modulus_eq period hgood hpow hclosure]
  rw [C.bodyTerm_mul_modulus_eq period, C.correctionTerm_mul_modulus_eq period hclosure]
  omega

section Examples

def prime97Stride2 : BlockCoordinate where
  base := 10
  modulus := 97
  stride := 2
  modulus_pos := by decide

def prime37Stride3 : BlockCoordinate where
  base := 10
  modulus := 37
  stride := 3
  modulus_pos := by decide

example : prime97Stride2.blockBase = 100 := by native_decide
example : prime97Stride2.quotientQ = 1 := by native_decide
example : prime97Stride2.remainderK = 3 := by native_decide
example : prime97Stride2.rawCoefficient 4 = 81 := by native_decide

example : prime37Stride3.blockBase = 1000 := by native_decide
example : prime37Stride3.quotientQ = 27 := by native_decide
example : prime37Stride3.remainderK = 1 := by native_decide
example : prime37Stride3.rawCoefficient 5 = 27 := by native_decide
example : prime37Stride3.bodyTerm 1 = 27 := by native_decide
example : prime37Stride3.correctionTerm 1 = 0 := by native_decide
example : prime37Stride3.reptendInteger 1 = 27 := by native_decide
example :
    prime37Stride3.reptendInteger 1 =
      prime37Stride3.bodyTerm 1 + prime37Stride3.correctionTerm 1 := by
  refine prime37Stride3.reptendInteger_eq_bodyTerm_add_correctionTerm 1 ?_ ?_ ?_
  · show 37 < 10 ^ 3
    native_decide
  · show 1 ≤ 1 ^ 1
    native_decide
  · show 37 ∣ 1 ^ 1 - 1
    native_decide

end Examples

end QRTour
