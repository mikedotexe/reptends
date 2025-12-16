/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GeometricStack.Scale
import GeometricStack.Valuation
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Positional Number System Formalization

This module connects GeometricStack's Scale decomposition to Mathlib's digit theory.

## Key Insight

The Scale decomposition `a[i] = illegal[i] * B_s + direct[i]` mirrors positional notation:
- `direct[i] = a[i] % B_s` is the least significant "digit" (when B_s is the radix)
- `illegal[i] = a[i] / B_s` is the remaining "digits" as a number

When `a[i] = k^i` and `B_s = base^n`, this provides:
1. A digit-based view of geometric sequences
2. Connection to reptend digit extraction via QRTour.Digits
3. Formal proof that capacity index equals digit count minus one

## Main Results

* `aDigits` - Digits of a[i] in base B_s
* `direct_eq_digits_head` - Scale.direct equals first digit
* `illegal_eq_ofDigits_tail` - Scale.illegal equals ofDigits of remaining digits
* `aDigitCount_eq_one_iff` - a[i] has one digit iff i ≤ T
-/

namespace GeometricStack

variable (F : Family)

/-! ### Digit-Based View of Geometric Sequences -/

/-- The digits of a[i] in base B_s (the word capacity at scale n). -/
def aDigits (S : Scale F) (i : ℕ) : List ℕ := Nat.digits S.Bs (F.a i)

/-- The number of digits of a[i] in base B_s. -/
def aDigitCount (S : Scale F) (i : ℕ) : ℕ := (aDigits F S i).length

/-- a[0] = k^0 = 1 gives [1] as its digit list. -/
theorem aDigits_zero_eq (S : Scale F) : aDigits F S 0 = [1] := by
  simp only [aDigits, Family.a, pow_zero]
  exact Nat.digits_of_lt S.Bs 1 Nat.one_ne_zero S.Bs_gt_one

/-! ### Scale-Digit Correspondence

The fundamental connection: Scale decomposition IS digit extraction.
-/

namespace Scale

variable {F} (S : Scale F)

/-- The direct part equals the first (least significant) digit in base B_s.

This is the core theorem: Scale.direct is exactly the LSD in positional notation. -/
theorem direct_eq_mod_Bs' (i : ℕ) :
    S.direct i = F.a i % S.Bs := rfl

/-- The illegal part equals the quotient, which represents the remaining digits. -/
theorem illegal_eq_div_Bs' (i : ℕ) :
    S.illegal i = F.a i / S.Bs := rfl

/-- The fundamental identity: digits reconstruction equals the original.
This is Mathlib's `Nat.ofDigits_digits` specialized to our setting. -/
theorem ofDigits_aDigits (i : ℕ) :
    Nat.ofDigits S.Bs (aDigits F S i) = F.a i := by
  simp only [aDigits]
  exact Nat.ofDigits_digits S.Bs (F.a i)

/-- Helper: S.Bs ≠ 1 -/
theorem Bs_ne_one : S.Bs ≠ 1 := ne_of_gt S.Bs_gt_one

/-- Direct part is the first digit (when a[i] > 0).

For a nonzero value v with digits [d₀, d₁, ...] (LSB first),
v % base = d₀ (the first digit). -/
theorem direct_eq_digits_head! (i : ℕ) (_ : F.a i ≠ 0) :
    S.direct i = (aDigits F S i).head! := by
  simp only [direct, aDigits]
  have h := Nat.head!_digits (b := S.Bs) (n := F.a i) S.Bs_ne_one
  exact h.symm

/-- The illegal part equals ofDigits of the tail of the digit list. -/
theorem illegal_eq_ofDigits_tail (i : ℕ) (hi : F.a i ≠ 0) :
    S.illegal i = Nat.ofDigits S.Bs (aDigits F S i).tail := by
  simp only [illegal, aDigits]
  have hdef := Nat.digits_def' S.Bs_gt_one (Nat.pos_of_ne_zero hi)
  rw [hdef, List.tail_cons, Nat.ofDigits_digits]

end Scale

/-! ### Capacity and Digit Count

The capacity index T relates to how many digits a[i] has.
For i ≤ T, a[i] fits in one "digit" (relative to B_s).
-/

variable {F}

/-- In the clean window (i ≤ T), a[i] has exactly one digit relative to B_s.
This is because a[i] < B_s means it fits in a single "digit position". -/
theorem aDigitCount_eq_one_of_le_T (S : Scale F) (i : ℕ) (hi : i ≤ S.cap.T) :
    aDigitCount F S i = 1 := by
  simp only [aDigitCount, aDigits]
  have hlt := S.cap.pow_below i hi
  have hne : F.a i ≠ 0 := Nat.pos_iff_ne_zero.mp (F.a_pos i)
  rw [Nat.digits_of_lt S.Bs (F.a i) hne hlt, List.length_singleton]

/-- Characterization: a[i] has one digit iff i ≤ T.

The forward direction uses: if i > T then a[i] ≥ B_s, so the digit list has length > 1.
The reverse direction is aDigitCount_eq_one_of_le_T. -/
theorem aDigitCount_eq_one_iff (S : Scale F) (i : ℕ) :
    aDigitCount F S i = 1 ↔ i ≤ S.cap.T := by
  constructor
  · -- aDigitCount = 1 → i ≤ T
    -- Proof sketch: if i > T then a[i] ≥ B_s, so digits has length > 1
    -- This contradicts aDigitCount = 1
    intro h
    by_contra hgt
    push_neg at hgt
    have hge := S.cap.pow_above
    have hai : S.Bs ≤ F.a i := by
      calc S.Bs ≤ F.a (S.cap.T + 1) := hge
           _ ≤ F.a i := F.a_mono hgt
    -- When a[i] ≥ B_s, log(a[i]) ≥ 1, so digits has length ≥ 2
    have hne : F.a i ≠ 0 := Nat.pos_iff_ne_zero.mp (F.a_pos i)
    simp only [aDigitCount, aDigits] at h
    rw [Nat.digits_len S.Bs (F.a i) S.Bs_gt_one hne] at h
    -- length = log + 1 = 1 means log = 0
    have hlog : Nat.log S.Bs (F.a i) = 0 := by omega
    -- But log = 0 with B_s > 1 means a[i] < B_s, contradicting hai
    -- Nat.lt_pow_succ_log_self : n < b ^ (log b n + 1)
    -- With log = 0: n < b^1 = b
    have hlt : F.a i < S.Bs := by
      have := Nat.lt_pow_succ_log_self S.Bs_gt_one (F.a i)
      simp only [hlog, pow_one] at this
      exact this
    exact absurd hlt (Nat.not_lt.mpr hai)
  · exact aDigitCount_eq_one_of_le_T S i

/-- Beyond the capacity, a[i] has more than one digit. -/
theorem aDigitCount_gt_one_of_gt_T (S : Scale F) (i : ℕ) (hi : S.cap.T < i) :
    1 < aDigitCount F S i := by
  have hnotone : ¬ (aDigitCount F S i = 1) := by
    intro heq
    have := (aDigitCount_eq_one_iff S i).mp heq
    omega
  have hne : F.a i ≠ 0 := Nat.pos_iff_ne_zero.mp (F.a_pos i)
  have hpos : 0 < aDigitCount F S i := by
    simp only [aDigitCount, aDigits]
    exact List.length_pos_of_ne_nil (Nat.digits_ne_nil_iff_ne_zero.mpr hne)
  omega

/-! ### Block Extraction

For multi-digit analysis: extracting n-digit blocks from the geometric sequence.
-/

variable (F)

/-- Extract an n-digit block: the value of the low-order n digits.
This equals v mod (base^n). -/
def block (n v : ℕ) : ℕ := v % (F.B n)

/-- Block extraction equals Scale.direct when scale has word-size n. -/
theorem block_eq_direct (S : Scale F) (i : ℕ) :
    block F S.n (F.a i) = S.direct i := by
  simp only [block, Scale.direct, Scale.Bs, Family.B]

/-- Block values are bounded by B[n]. -/
theorem block_lt_B (n v : ℕ) :
    block F n v < F.B n := by
  simp only [block]
  exact Nat.mod_lt v (F.B_pos n)

/-- For the geometric sequence, the block at position i equals k^i when i ≤ T. -/
theorem block_eq_a_up_to_T (S : Scale F) (i : ℕ) (hi : i ≤ S.cap.T) :
    block F S.n (F.a i) = F.a i := by
  rw [block_eq_direct]
  exact S.direct_eq_a_up_to_T i hi

/-! ### Connection to Valuation

Building on Valuation.lean: capacity + 1 = digit count.
-/

variable {F}

/-- The geometric sequence a[i] = k^i satisfies:
digits of a[i] in base B_s has length = log(a[i]) + 1. -/
theorem a_digits_length (S : Scale F) (i : ℕ) (hi : F.a i ≠ 0) :
    (Nat.digits S.Bs (F.a i)).length = Nat.log S.Bs (F.a i) + 1 :=
  Nat.digits_len S.Bs (F.a i) S.Bs_gt_one hi

/-- The digit count of a[i] is bounded by capacity considerations. -/
theorem aDigitCount_le_one_of_le_T (S : Scale F) (i : ℕ) (hi : i ≤ S.cap.T) :
    aDigitCount F S i ≤ 1 := by
  rw [aDigitCount_eq_one_of_le_T S i hi]

/-! ### Skeleton Interpretation

For reptend analysis: the "skeleton" is the sequence k^0, k^1, k^2, ...
displayed as digit blocks. When k is small, these blocks are visible
before carry correction obscures them.
-/

variable (F)

/-- The skeleton: raw powers of k, viewed as potential digit blocks.
These are the "uncorrected" values before carry propagation. -/
def skeleton (i : ℕ) : ℕ := F.a i

/-- Skeleton value at position i equals k^i. -/
theorem skeleton_eq_pow (i : ℕ) : skeleton F i = F.k ^ i := rfl

/-- The skeleton is visible (fits in one block) up to the capacity index. -/
theorem skeleton_visible_up_to_T (S : Scale F) (i : ℕ) (hi : i ≤ S.cap.T) :
    skeleton F i < S.Bs := S.cap.pow_below i hi

end GeometricStack
