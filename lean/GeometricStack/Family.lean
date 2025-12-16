/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Ring.Nat

/-!
# Geometric Stack Family

This module defines the basic structure for geometric sequences and word capacities.
It ports the Agda `GeometricStack.Family` module.

## Main Definitions

* `GeometricStack.Family` - A configuration with base and multiplier k
* `GeometricStack.Family.a` - The geometric sequence a[i] = k^i
* `GeometricStack.Family.B` - Word capacities B[n] = base^n

## Mathematical Background

A "geometric stack" models sequences of values k^0, k^1, k^2, ... that need to
be stored in words of increasing size. The word capacity at level n is base^n.

This abstraction is useful for analyzing how many terms of a geometric sequence
fit in various word sizes, and how overflow occurs when terms exceed capacity.
-/

namespace GeometricStack

/-- A geometric stack family is determined by:
- `base`: the radix for word sizes (≥ 2)
- `k`: the geometric multiplier (≥ 1)

The geometric sequence is a[i] = k^i.
Word capacities are B[n] = base^n.
-/
structure Family where
  /-- The base radix for word sizes -/
  base : ℕ
  /-- The geometric multiplier -/
  k : ℕ
  /-- Base is at least 2 -/
  base_ge_2 : 2 ≤ base
  /-- k is at least 1 -/
  k_ge_1 : 1 ≤ k

namespace Family

variable (F : Family)

/-! ### The Geometric Sequence -/

/-- The geometric sequence: a[i] = k^i -/
def a (i : ℕ) : ℕ := F.k ^ i

/-- a[0] = 1 -/
@[simp]
theorem a_zero : F.a 0 = 1 := by simp [a]

/-- a[1] = k -/
@[simp]
theorem a_one : F.a 1 = F.k := by simp [a]

/-- a[i+1] = k * a[i] -/
theorem a_succ (i : ℕ) : F.a (i + 1) = F.k * F.a i := by
  simp [a, pow_succ, mul_comm]

/-- The sequence is monotonically increasing (when k ≥ 1). -/
theorem a_mono {i j : ℕ} (hij : i ≤ j) : F.a i ≤ F.a j := by
  simp only [a]
  exact Nat.pow_le_pow_right F.k_ge_1 hij

/-- Strict monotonicity when k > 1. -/
theorem a_strictMono (hk : 1 < F.k) {i j : ℕ} (hij : i < j) : F.a i < F.a j := by
  simp only [a]
  exact Nat.pow_lt_pow_right hk hij

/-! ### Word Capacities -/

/-- Word capacity at level n: B[n] = base^n -/
def B (n : ℕ) : ℕ := F.base ^ n

/-- B[0] = 1 -/
@[simp]
theorem B_zero : F.B 0 = 1 := by simp [B]

/-- B[1] = base -/
@[simp]
theorem B_one : F.B 1 = F.base := by simp [B]

/-- B[n+1] = base * B[n] -/
theorem B_succ (n : ℕ) : F.B (n + 1) = F.base * F.B n := by
  simp [B, pow_succ, mul_comm]

/-- Word capacities are monotonically increasing. -/
theorem B_mono {m n : ℕ} (hmn : m ≤ n) : F.B m ≤ F.B n := by
  simp only [B]
  exact Nat.pow_le_pow_right (Nat.one_le_of_lt F.base_ge_2) hmn

/-- Strict monotonicity of capacities. -/
theorem B_strictMono {m n : ℕ} (hmn : m < n) : F.B m < F.B n := by
  simp only [B]
  exact Nat.pow_lt_pow_right F.base_ge_2 hmn

/-- B[n] is always positive. -/
theorem B_pos (n : ℕ) : 0 < F.B n := by
  simp only [B]
  exact Nat.pow_pos (Nat.lt_of_lt_of_le Nat.zero_lt_two F.base_ge_2)

/-- a[i] is always positive (when k ≥ 1). -/
theorem a_pos (i : ℕ) : 0 < F.a i := by
  simp only [a]
  exact Nat.pow_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one F.k_ge_1)

end Family

end GeometricStack
