/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GeometricStack.Capacity

/-!
# Scale Decomposition for Geometric Stacks

This module defines the "scale" decomposition of a geometric stack at a fixed
word level. Each term a[i] = k^i is decomposed as:

  a[i] = illegal[i] * B_s + direct[i]

where B_s = base^n is the word capacity at the chosen scale n.

## Main Definitions

* `GeometricStack.Scale` - A configuration fixing word level n and capacity
* `GeometricStack.Scale.direct` - The "in-bounds" part: a[i] mod B_s
* `GeometricStack.Scale.illegal` - The "overflow" part: a[i] / B_s

## Main Results

* `GeometricStack.Scale.stack_decomp` - a[i] = illegal[i] * B_s + direct[i]
* `GeometricStack.Scale.illegal_zero_up_to_T` - For i ≤ T, illegal[i] = 0
* `GeometricStack.Scale.direct_eq_a_up_to_T` - For i ≤ T, direct[i] = a[i]

## Terminology

- "Direct" values fit within the word capacity
- "Illegal" values overflow the word capacity
- The "clean window" is i ∈ [0, T] where no overflow occurs
-/

namespace GeometricStack

variable (F : Family)

/-! ### Scale Structure -/

/-- A scale fixes a word level n and provides the capacity information.
At this scale, values are decomposed relative to B_s = base^n. -/
structure Scale where
  /-- The word level -/
  n : ℕ
  /-- n is positive (so B_s > 1) -/
  n_pos : 0 < n
  /-- The capacity at this level -/
  cap : Capacity F n

namespace Scale

variable {F} (S : Scale F)

/-- The word capacity at this scale: B_s = base^n -/
def Bs : ℕ := F.B S.n

/-- B_s is positive. -/
theorem Bs_pos : 0 < S.Bs := F.B_pos S.n

/-- B_s > 1 when n > 0 and base ≥ 2. -/
theorem Bs_gt_one : 1 < S.Bs := by
  simp only [Bs, Family.B]
  calc 1 = F.base ^ 0 := by simp
    _ < F.base ^ S.n := Nat.pow_lt_pow_right F.base_ge_2 S.n_pos

/-! ### Decomposition -/

/-- The "direct" part of a[i]: what fits in the word. -/
def direct (i : ℕ) : ℕ := F.a i % S.Bs

/-- The "illegal" (overflow) part of a[i]: what doesn't fit. -/
def illegal (i : ℕ) : ℕ := F.a i / S.Bs

/-- The fundamental decomposition: a[i] = illegal[i] * B_s + direct[i] -/
theorem stack_decomp (i : ℕ) :
    F.a i = S.illegal i * S.Bs + S.direct i := by
  simp only [illegal, direct]
  rw [mul_comm]
  exact (Nat.div_add_mod (F.a i) S.Bs).symm

/-- Direct values are bounded by B_s. -/
theorem direct_lt_Bs (i : ℕ) : S.direct i < S.Bs := by
  simp only [direct]
  exact Nat.mod_lt (F.a i) S.Bs_pos

/-! ### The Clean Window

For indices i ≤ T (the capacity index), we have a[i] < B_s,
so the decomposition is trivial: illegal[i] = 0 and direct[i] = a[i].
-/

/-- In the clean window (i ≤ T), overflow is zero. -/
theorem illegal_zero_up_to_T (i : ℕ) (hi : i ≤ S.cap.T) :
    S.illegal i = 0 := by
  simp only [illegal]
  rw [Nat.div_eq_zero_iff]
  right
  exact S.cap.pow_below i hi

/-- In the clean window (i ≤ T), direct equals the original value. -/
theorem direct_eq_a_up_to_T (i : ℕ) (hi : i ≤ S.cap.T) :
    S.direct i = F.a i := by
  simp only [direct]
  rw [Nat.mod_eq_of_lt]
  exact S.cap.pow_below i hi

/-- Beyond the clean window (i > T), overflow begins. -/
theorem illegal_pos_beyond_T (i : ℕ) (hi : S.cap.T < i) :
    0 < S.illegal i := by
  simp only [illegal]
  rw [Nat.div_pos_iff]
  constructor
  · exact S.Bs_pos
  · -- Need: B_s ≤ a[i]
    calc S.Bs ≤ F.a (S.cap.T + 1) := S.cap.pow_above
      _ ≤ F.a i := F.a_mono hi

/-! ### Illegal Value Growth -/

/-- Illegal values are monotonically increasing. -/
theorem illegal_mono {i j : ℕ} (hij : i ≤ j) :
    S.illegal i ≤ S.illegal j := by
  simp only [illegal]
  exact Nat.div_le_div_right (F.a_mono hij)

/-- The illegal value at T+1. -/
theorem illegal_at_succ_T :
    S.illegal (S.cap.T + 1) = F.a (S.cap.T + 1) / S.Bs := rfl

/-! ### Decomposition Uniqueness

The decomposition v = illegal * B_s + direct with direct < B_s is unique.
This is analogous to uniqueness in divided power representations.
-/

/-- The decomposition is unique: given v and B_s, there's exactly one valid (q, r) pair.
    This is the uniqueness property of Euclidean division. -/
theorem decomposition_unique (v : ℕ) :
    ∃! p : ℕ × ℕ, v = p.1 * S.Bs + p.2 ∧ p.2 < S.Bs := by
  use (v / S.Bs, v % S.Bs)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mul_comm]; exact (Nat.div_add_mod v S.Bs).symm
  · exact Nat.mod_lt v S.Bs_pos
  · intro ⟨q', r'⟩ ⟨heq, hlt⟩
    simp only [Prod.mk.injEq]
    constructor
    · -- q' = v / S.Bs: use that (q' * S.Bs + r') / S.Bs = q' when r' < S.Bs
      have h1 : (q' * S.Bs + r') / S.Bs = q' := by
        rw [mul_comm, add_comm, Nat.add_mul_div_left _ _ S.Bs_pos, Nat.div_eq_of_lt hlt, zero_add]
      rw [← heq] at h1
      exact h1.symm
    · -- r' = v % S.Bs: use that (q' * S.Bs + r') % S.Bs = r' when r' < S.Bs
      have h2 : (q' * S.Bs + r') % S.Bs = r' := by
        rw [mul_comm, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      rw [← heq] at h2
      exact h2.symm

/-- Alternative statement: decomposition recovers from parts. -/
theorem decomposition_recover (q r : ℕ) (hr : r < S.Bs) :
    (q * S.Bs + r) / S.Bs = q ∧ (q * S.Bs + r) % S.Bs = r := by
  constructor
  · rw [mul_comm, add_comm, Nat.add_mul_div_left _ _ S.Bs_pos, Nat.div_eq_of_lt hr, zero_add]
  · rw [mul_comm, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- The direct part is exactly the remainder. -/
theorem direct_eq_mod (i : ℕ) : S.direct i = F.a i % S.Bs := rfl

/-- The illegal part is exactly the quotient. -/
theorem illegal_eq_div (i : ℕ) : S.illegal i = F.a i / S.Bs := rfl

end Scale

end GeometricStack
