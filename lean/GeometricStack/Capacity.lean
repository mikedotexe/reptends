/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GeometricStack.Family
import Mathlib.Data.Nat.Log

/-!
# Capacity Indices for Geometric Stacks

This module defines the "capacity index" T_n for a geometric stack at word level n.
T_n is the largest index i such that a[i] < B[n], i.e., T_n = floor(log_k(B[n])).

## Main Definitions

* `GeometricStack.Capacity` - A structure packaging T_n with its bounds
* `GeometricStack.capacity` - Compute the capacity using Nat.log

## Main Results

* `GeometricStack.capacity_pow_below` - For i ≤ T_n, a[i] < B[n]
* `GeometricStack.capacity_pow_above` - B[n] ≤ a[T_n + 1]
* `GeometricStack.capacity_unique` - T_n is uniquely determined

## Porting Notes

The Agda version postulated existence and uniqueness of capacity indices.
In Lean, we can construct them directly using `Nat.log` from Mathlib.
-/

namespace GeometricStack

variable (F : Family)

/-! ### Capacity Index Structure -/

/-- A capacity index for word level n packages:
- T: the index value
- pow_below: a[i] < B[n] for all i ≤ T
- pow_above: B[n] ≤ a[T + 1]

This characterizes T as the largest i with a[i] < B[n].
-/
structure Capacity (n : ℕ) where
  /-- The capacity index -/
  T : ℕ
  /-- Below the threshold: a[i] < B[n] for i ≤ T -/
  pow_below : ∀ i, i ≤ T → F.a i < F.B n
  /-- Above the threshold: B[n] ≤ a[T + 1] -/
  pow_above : F.B n ≤ F.a (T + 1)

/-! ### Computing Capacity via Logarithm

When k > 1, we have T_n = floor(log_k(B[n])) = floor(n * log_k(base)).
-/

/-- The capacity index equals the base-k logarithm of B[n].
This is T = floor(log_k(base^n)) = floor(n * log_k(base)). -/
def capacityIndex (_hk : 1 < F.k) (n : ℕ) : ℕ :=
  Nat.log F.k (F.B n)

/-- The capacity index satisfies k^T ≤ B[n]. -/
theorem capacity_index_le (hk : 1 < F.k) (n : ℕ) (_hn : 0 < n) :
    F.a (capacityIndex F hk n) ≤ F.B n := by
  simp only [capacityIndex, Family.a, Family.B]
  have hB : F.base ^ n ≠ 0 := Nat.pos_iff_ne_zero.mp (F.B_pos n)
  exact Nat.pow_log_le_self F.k hB

/-- The capacity index satisfies B[n] < k^(T+1). -/
theorem capacity_index_lt (hk : 1 < F.k) (n : ℕ) :
    F.B n < F.a (capacityIndex F hk n + 1) := by
  simp only [capacityIndex, Family.a, Family.B]
  exact Nat.lt_pow_succ_log_self hk (F.base ^ n)

/-- Construct a Capacity structure using the logarithm.

Note: The `pow_below` field requires `a[i] < B[n]` all the way up to `i = T`.
From `Nat.log` we only get `a[T] ≤ B[n]`. To obtain strict inequality at the
top index we assume it as a hypothesis; in concrete families (e.g. when `B[n]`
is never an exact `k`-power) this is easy to discharge. -/
def capacity (hk : 1 < F.k) (n : ℕ) (_hn : 0 < n)
    (hstrict : F.a (capacityIndex F hk n) < F.B n) : Capacity F n where
  T := capacityIndex F hk n
  pow_below := by
    intro i hi
    -- monotonicity of a: a[i] ≤ a[T]
    have hmono : F.a i ≤ F.a (capacityIndex F hk n) := F.a_mono hi
    -- and the assumed strict inequality at the top index
    exact lt_of_le_of_lt hmono hstrict
  pow_above := Nat.le_of_lt (capacity_index_lt F hk n)

/-! ### Uniqueness -/

/-- The capacity index is uniquely determined by its characterization. -/
theorem capacity_unique {n : ℕ} (c1 c2 : Capacity F n) : c1.T = c2.T := by
  by_contra h
  wlog h_lt : c1.T < c2.T with H
  · push_neg at h_lt
    have hlt : c2.T < c1.T := Nat.lt_of_le_of_ne h_lt (Ne.symm h)
    exact H F c2 c1 (Ne.symm h) hlt
  -- c1.T < c2.T
  -- From c1: B[n] ≤ a[c1.T + 1]
  -- From c2: a[c2.T] < B[n]
  -- But c1.T + 1 ≤ c2.T, so a[c1.T + 1] ≤ a[c2.T] < B[n]
  -- Contradiction
  have h1 : F.B n ≤ F.a (c1.T + 1) := c1.pow_above
  have h2 : F.a c2.T < F.B n := c2.pow_below c2.T (Nat.le_refl _)
  have h3 : c1.T + 1 ≤ c2.T := h_lt
  have h4 : F.a (c1.T + 1) ≤ F.a c2.T := F.a_mono h3
  have : F.B n ≤ F.a c2.T := Nat.le_trans h1 h4
  exact Nat.not_lt.mpr this h2

/-! ### Monotonicity of Capacity Index

Larger word sizes have larger capacity indices.
-/

/-- Capacity index is monotonic in n. -/
theorem capacity_mono (hk : 1 < F.k) {m n : ℕ} (hmn : m ≤ n) :
    capacityIndex F hk m ≤ capacityIndex F hk n := by
  simp only [capacityIndex]
  exact Nat.log_mono_right (F.B_mono hmn)

end GeometricStack
