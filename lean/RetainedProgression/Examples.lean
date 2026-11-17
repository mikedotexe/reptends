import RetainedProgression.Bridge
import RadixTermination.Seeded

/-! The motivating reciprocal, its return after 166 steps, and a binary-block
representation of the same value. The 166-step return is checked here; minimality
of that period is not asserted by this module. -/
namespace RetainedProgression

theorem decimal_blocks_997_hasSum :
    HasSum (geometric 1000 3).term (1 / (997 : ℝ)) := by
  simpa using reciprocal_hasSum (B := 1000) (D := 997) (by decide) (by decide)

theorem decimal_blocks_997_value :
    (geometric 1000 3).value = 1 / (997 : ℝ) := decimal_blocks_997_hasSum.tsum_eq

theorem binary_blocks_997_hasSum :
    HasSum (geometric 1024 27).term (1 / (997 : ℝ)) := by
  simpa using reciprocal_hasSum (B := 1024) (D := 997) (by decide) (by decide)

theorem binary_blocks_997_value :
    (geometric 1024 27).value = 1 / (997 : ℝ) := binary_blocks_997_hasSum.tsum_eq

theorem distinct_progressions_same_value :
    geometric 1000 3 ≠ geometric 1024 27 ∧
      (geometric 1000 3).value = (geometric 1024 27).value := by
  constructor
  · intro h
    have hr := congrArg Expansion.radix h
    norm_num [geometric] at hr
  · rw [decimal_blocks_997_value, binary_blocks_997_value]

theorem evaluation_not_injective : ¬ Function.Injective Expansion.value := by
  intro h
  exact distinct_progressions_same_value.1 (h distinct_progressions_same_value.2)

theorem decimal_blocks_997_no_finite_completion (n : ℕ) :
    (geometric 1000 3).partialValue n < 1 / (997 : ℝ) := by
  rw [← decimal_blocks_997_value]
  exact partialValue_lt_value (by decide) (by decide) n

/-- Retained entries are coefficients, not bounded radix digits. -/
theorem coefficient_997_exceeds_digit_limit :
    (geometric 1000 3).coefficient 7 = 2187 ∧
      1000 < (geometric 1000 3).coefficient 7 := by
  norm_num

theorem return_997 : powerRemainder 3 997 166 = 1 := by
  norm_num [powerRemainder]

theorem all_returns_997 (n : ℕ) :
    powerRemainder 3 997 (n + 166) = powerRemainder 3 997 n :=
  remainder_return 3 997 166 n return_997

theorem growing_quotient_997 (n : ℕ) :
    powerQuotient 3 997 (n + 166) =
      powerQuotient 3 997 n + 3 ^ n * powerQuotient 3 997 166 :=
  quotient_return 3 166 n (by decide) return_997

theorem return_height_997 :
    0 < powerQuotient 3 997 166 ∧
      3 ^ 166 = 997 * powerQuotient 3 997 166 + 1 := by
  constructor
  · exact quotient_at_return_pos (by decide) (by decide) return_997
  · simpa only [return_997] using power_state_identity 3 997 166

theorem same_remainder_distinct_states_997 :
    powerRemainder 3 997 0 = powerRemainder 3 997 166 ∧
      liftedState 3 997 0 ≠ liftedState 3 997 166 := by
  constructor
  · norm_num [return_997, powerRemainder]
  · exact (liftedState_injective (by decide : 2 ≤ 3) 997).ne (by decide)

/-- Sharing a remainder does not identify the two different quotients. -/
theorem coefficient_quotient_is_not_digitPrefix :
    RadixTermination.digitPrefix (fun _ => 1000) 1 997 1 = 1 ∧
      powerQuotient 3 997 1 = 0 := by
  norm_num [ordinary_digitPrefix_eq, powerQuotient]

/-- Terminating notation and an infinite retained stream coexist for one value. -/
theorem termination_alongside_retention_997 :
    RadixTermination.EventuallyTerminates (RadixTermination.seededRadix 10) 1 997 ∧
      HasSum (geometric 1000 3).term (1 / (997 : ℝ)) ∧
      ∀ n, (geometric 1000 3).partialValue n < 1 / (997 : ℝ) := by
  exact ⟨RadixTermination.seededRadix_terminates (by decide) 1 997 (by decide),
    decimal_blocks_997_hasSum, decimal_blocks_997_no_finite_completion⟩

/-- Even a zero remainder can coexist with a growing retained progression.
The base-four numeral for one half finishes immediately; its geometric stream
of coefficients `1,2,4,...` has a positive tail at every finite stage. -/
theorem half_terminates_but_stream_continues :
    RadixTermination.TerminatesAt (fun _ => 4) 1 2 1 ∧
      HasSum (geometric 4 2).term (1 / (2 : ℝ)) ∧
      StrictMono (geometric 4 2).coefficient ∧
      ∀ n, (geometric 4 2).partialValue n < 1 / (2 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [RadixTermination.TerminatesAt, RadixTermination.remainder,
      RadixTermination.placeProduct]
  · simpa using reciprocal_hasSum (B := 4) (D := 2) (by decide) (by decide)
  · exact power_strictMono (by decide)
  · intro n
    have hv : (geometric 4 2).value = 1 / (2 : ℝ) := by
      simpa using reciprocal_value (B := 4) (D := 2) (by decide) (by decide)
    rw [← hv]
    exact partialValue_lt_value (by decide) (by decide) n

end RetainedProgression
