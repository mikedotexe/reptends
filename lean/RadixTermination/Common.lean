import Mathlib

/-! Shared, zero-indexed definitions for denominator-independent radix schedules.
The first radix is `b 0`; `placeProduct b n` contains exactly `n` radices. -/
namespace RadixTermination

def placeProduct (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => placeProduct b n * b n

@[simp] theorem placeProduct_zero (b : ℕ → ℕ) : placeProduct b 0 = 1 := rfl

@[simp] theorem placeProduct_succ (b : ℕ → ℕ) (n : ℕ) :
    placeProduct b (n + 1) = placeProduct b n * b n := rfl

def ValidRadices (b : ℕ → ℕ) : Prop := ∀ n, 2 ≤ b n

def remainder (b : ℕ → ℕ) (A D n : ℕ) : ℕ :=
  (A * placeProduct b n) % D

def TerminatesAt (b : ℕ → ℕ) (A D n : ℕ) : Prop :=
  remainder b A D n = 0

def EventuallyTerminates (b : ℕ → ℕ) (A D : ℕ) : Prop :=
  ∃ n, TerminatesAt b A D n

end RadixTermination
