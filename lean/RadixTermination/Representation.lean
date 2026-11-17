import RadixTermination.Core

/-! The finite digit string denotes the same rational when division terminates.
Digits are zero-indexed; the weight of digit `k` is `1 / placeProduct b (k+1)`.
-/
namespace RadixTermination

/-- The rational value of the first `n` digits after the radix point. -/
def digitValue (b : ℕ → ℕ) (A D n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (digit b A D k : ℚ) / (placeProduct b (k + 1) : ℚ)

theorem exact_value (b : ℕ → ℕ) (hb : ValidRadices b)
    (A D n : ℕ) (hD : 0 < D) :
    (A : ℚ) / D = (digitPrefix b A D n : ℚ) / (placeProduct b n : ℚ) +
      (remainder b A D n : ℚ) / ((D : ℚ) * (placeProduct b n : ℚ)) := by
  have hp : (placeProduct b n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (placeProduct_pos b hb n))
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hs : (A : ℚ) * (placeProduct b n : ℚ) =
      (D : ℚ) * (digitPrefix b A D n : ℚ) + (remainder b A D n : ℚ) := by
    exact_mod_cast state_identity b A D n
  field_simp
  nlinarith [hs]

theorem digitValue_eq_prefix (b : ℕ → ℕ) (hb : ValidRadices b)
    (A D : ℕ) (hA : A < D) (n : ℕ) :
    digitValue b A D n = (digitPrefix b A D n : ℚ) / (placeProduct b n : ℚ) := by
  have hD : 0 < D := by omega
  induction n with
  | zero => simp [digitValue, digitPrefix, Nat.div_eq_of_lt hA]
  | succ n ih =>
    have hp : (placeProduct b n : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (placeProduct_pos b hb n))
    have hr : (b n : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (show 0 < b n by have := hb n; omega))
    rw [digitValue, Finset.sum_range_succ]
    change digitValue b A D n +
        (digit b A D n : ℚ) / (placeProduct b (n + 1) : ℚ) = _
    rw [ih, prefix_succ b A n hD, placeProduct_succ]
    push_cast
    field_simp

theorem terminating_digit_value (b : ℕ → ℕ) (hb : ValidRadices b)
    (A D : ℕ) (hA : A < D) (n : ℕ) (hn : TerminatesAt b A D n) :
    digitValue b A D n = (A : ℚ) / D := by
  have hv := exact_value b hb A D n (by omega)
  change remainder b A D n = 0 at hn
  rw [hn] at hv
  simpa [digitValue_eq_prefix b hb A D hA n] using hv.symm

end RadixTermination
