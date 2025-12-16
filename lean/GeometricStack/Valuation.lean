/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GeometricStack.Capacity
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Capacity as Discrete Valuation

This module connects GeometricStack's capacity index to:
1. Mathlib's `Nat.digits` - showing capacity + 1 = number of digits
2. Valuation-like properties - monotonicity, bounds, uniqueness

## Key Insight

The p-adic valuation v_p(n) counts how many times p divides n.
Our capacity T_n = Nat.log k (B n) counts how many k-powers fit in B^n.

Both satisfy:
- **Monotonicity**: larger inputs → larger/equal values
- **Bounds**: the value characterizes the "level" of the input
- **Uniqueness**: there's exactly one right answer

## Connection to Prior Art

From lean-perfectoid-spaces: "bounded norms akin to word sizes, log-based indices"
From divided_powers_journal: decomposition with bounds and uniqueness
From Nat.digits: floor(log_b n) + 1 = number of digits

Our capacity index IS the floor-log that Nat.digits uses internally!

## Main Results

* `capacityIndex_eq_log` - capacity is exactly Nat.log
* `capacity_add_one_eq_digits_length` - capacity + 1 = (Nat.digits k n).length
* `capacityIndex_mono` - capacity is monotonic (valuation-like)
-/

namespace GeometricStack

variable (F : Family)

/-! ### Connection to Nat.digits -/

/-- The capacity index equals floor(log_k(n)).
    This is the core connection to Mathlib's digit theory. -/
theorem capacityIndex_eq_log (hk : 1 < F.k) (n : ℕ) :
    capacityIndex F hk n = Nat.log F.k (F.B n) := rfl

/-- The number of base-k digits of n equals Nat.log k n + 1 (for n > 0).
    This connects capacity to digit counting. -/
theorem digits_length_eq_log_add_one (k n : ℕ) (hk : 1 < k) (hn : 0 < n) :
    (Nat.digits k n).length = Nat.log k n + 1 := by
  exact Nat.digits_len k n hk (Nat.pos_iff_ne_zero.mp hn)

/-- Capacity + 1 equals the number of base-k digits of B[n].
    This is the key bridge between GeometricStack and digit theory!

    Interpretation: The capacity tells us "how many k-power terms fit" in B[n],
    which is exactly one less than the number of digits needed to represent B[n].
-/
theorem capacity_add_one_eq_digits_length (hk : 1 < F.k) (n : ℕ) (_ : 0 < n) :
    capacityIndex F hk n + 1 = (Nat.digits F.k (F.B n)).length := by
  rw [capacityIndex_eq_log, digits_length_eq_log_add_one]
  · exact hk
  · exact F.B_pos n

/-- Alternative form: capacity = digits.length - 1 -/
theorem capacityIndex_eq_digits_length_sub_one (hk : 1 < F.k) (n : ℕ) (hn : 0 < n) :
    capacityIndex F hk n = (Nat.digits F.k (F.B n)).length - 1 := by
  have h := capacity_add_one_eq_digits_length F hk n hn
  omega

/-! ### Valuation-like Properties

These properties make capacity behave like a discrete valuation:
measuring the "level" or "size" of elements in a structured way.
-/

/-- Capacity index is monotonic: larger word sizes have larger capacities.
    This is analogous to valuations being monotonic under certain conditions. -/
theorem capacityIndex_mono' (hk : 1 < F.k) : Monotone (capacityIndex F hk) := by
  intro m n hmn
  exact capacity_mono F hk hmn

/-- The capacity bounds are tight: k^T ≤ B[n] < k^(T+1).
    This is the defining property of floor-log. -/
theorem capacity_bounds (hk : 1 < F.k) (n : ℕ) (_ : 0 < n) :
    F.k ^ (capacityIndex F hk n) ≤ F.B n ∧ F.B n < F.k ^ (capacityIndex F hk n + 1) := by
  constructor
  · -- k^T ≤ B[n]
    simp only [capacityIndex, Family.B]
    have hB : F.base ^ n ≠ 0 := Nat.pos_iff_ne_zero.mp (F.B_pos n)
    exact Nat.pow_log_le_self F.k hB
  · -- B[n] < k^(T+1)
    simp only [capacityIndex, Family.B]
    exact Nat.lt_pow_succ_log_self hk (F.base ^ n)

/-- Capacity is characterized by the bounds: if k^t ≤ B[n] < k^(t+1), then t = T_n. -/
theorem capacity_char (hk : 1 < F.k) (n t : ℕ)
    (hle : F.k ^ t ≤ F.B n) (hlt : F.B n < F.k ^ (t + 1)) :
    t = capacityIndex F hk n := by
  simp only [capacityIndex, Family.B]
  have hB_pos : F.base ^ n ≠ 0 := Nat.pos_iff_ne_zero.mp (F.B_pos n)
  exact ((Nat.log_eq_iff (Or.inr ⟨hk, hB_pos⟩)).mpr ⟨hle, hlt⟩).symm

/-! ### Concrete Examples -/

section Examples

/-- For a standard family with base = 10, k = 2:
    The capacity index tells us how many doublings fit in 10^n. -/
example : Nat.log 2 (10 ^ 3) = 9 := by native_decide  -- 2^9 = 512 ≤ 1000 < 1024 = 2^10
example : Nat.log 2 (10 ^ 6) = 19 := by native_decide  -- 2^19 ≤ 10^6 < 2^20

/-- The number of base-2 digits of 1000 is 10 (since log_2(1000) = 9). -/
example : (Nat.digits 2 1000).length = 10 := by native_decide

/-- Connection: log_2(1000) + 1 = 10 = number of binary digits. -/
example : Nat.log 2 1000 + 1 = (Nat.digits 2 1000).length := by native_decide

end Examples

/-! ### Interpretation: Clean Window as Digit Theory

The "clean window" theorem from Capacity.lean says:
  ∀ i ≤ T_n, a[i] < B[n]

In digit-theoretic terms, this says:
  The first T_n + 1 powers of k all "fit" in B[n].

This is precisely the digit-counting insight: to represent B[n] in base k,
you need T_n + 1 digits, numbered 0 through T_n.
-/

/-- The clean window theorem rephrased in terms of digit positions:
    For each digit position i ∈ {0, ..., T_n}, the place value k^i fits in B[n]. -/
theorem clean_window_as_digits (hk : 1 < F.k) (n : ℕ) (_ : 0 < n)
    (c : Capacity F n) (_ : c.T = capacityIndex F hk n) :
    ∀ i, i ≤ c.T → F.k ^ i < F.B n := by
  intro i hi
  have hpow := c.pow_below i hi
  simp only [Family.a] at hpow
  exact hpow

/-! ### Toward Full Valuation Structure

A proper valuation on a ring R satisfies:
- v(0) = ∞
- v(xy) = v(x) + v(y)
- v(x + y) ≥ min(v(x), v(y))

Our capacity doesn't form a ring valuation directly, but it shares:
- Monotonicity (larger → larger)
- Bounds characterization (log-based)
- Uniqueness (exactly one valid answer)

The connection to p-adic valuations:
- v_p(n) = largest k with p^k | n
- capacity(n) = largest k with k^k ≤ n

Both measure "level" in a power hierarchy.
-/

/-- The capacity index on the sequence a[i] = k^i gives:
    capacityIndex F hk n is the largest i such that k^i ≤ B[n]. -/
theorem capacity_is_largest_fitting (hk : 1 < F.k) (n : ℕ) (hn : 0 < n) (i : ℕ) :
    F.k ^ i ≤ F.B n ↔ i ≤ capacityIndex F hk n := by
  constructor
  · -- k^i ≤ B[n] → i ≤ T
    intro hle
    simp only [capacityIndex, Family.B]
    have hB_ne : F.base ^ n ≠ 0 := Nat.pos_iff_ne_zero.mp (F.B_pos n)
    exact (Nat.le_log_iff_pow_le hk hB_ne).mpr hle
  · -- i ≤ T → k^i ≤ B[n]
    intro hi
    have hT := (capacity_bounds F hk n hn).1
    exact Nat.le_trans (Nat.pow_le_pow_right (Nat.one_le_of_lt hk) hi) hT

end GeometricStack
