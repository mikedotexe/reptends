import RadixTermination.Coverage
import RadixTermination.Representation

/-! Small exact digit strings, plus instances for the two motivating fractions.
The large examples below assert eventual termination, not their minimal stopping
positions from the earlier numerical experiment.
-/
namespace RadixTermination

theorem seventh_consecutive_digits :
    [digit consecutive 1 7 0, digit consecutive 1 7 1,
      digit consecutive 1 7 2, digit consecutive 1 7 3,
      digit consecutive 1 7 4, digit consecutive 1 7 5] = [0, 0, 3, 2, 0, 6] := by
  norm_num [digit, remainder, placeProduct, consecutive]

theorem seventh_missing_digits :
    [digit missingRadix 1 7 0, digit missingRadix 1 7 1,
      digit missingRadix 1 7 2] = [1, 12, 180] := by
  norm_num [digit, remainder, placeProduct,
    smallestMissingPrime_ten, smallestMissingPrime_thirty]

theorem seventh_consecutive_first_stop :
    TerminatesAt consecutive 1 7 6 ∧
      ∀ n < 6, ¬ TerminatesAt consecutive 1 7 n := by
  constructor
  · norm_num [TerminatesAt, remainder, placeProduct, consecutive]
  · intro n hn
    interval_cases n <;> norm_num [TerminatesAt, remainder, placeProduct, consecutive]

theorem seventh_missing_first_stop :
    TerminatesAt missingRadix 1 7 3 ∧
      ∀ n < 3, ¬ TerminatesAt missingRadix 1 7 n := by
  constructor
  · norm_num [TerminatesAt, remainder, placeProduct,
      smallestMissingPrime_ten, smallestMissingPrime_thirty]
  · intro n hn
    interval_cases n <;> norm_num [TerminatesAt, remainder, placeProduct,
      smallestMissingPrime_ten, smallestMissingPrime_thirty]

theorem seventh_missing_value :
    digitValue missingRadix 1 7 3 = (1 : ℚ) / 7 :=
  terminating_digit_value missingRadix missingRadix_valid 1 7 (by decide) 3
    seventh_missing_first_stop.1

theorem seventh_missing_explicit_sum :
    (1 : ℚ) / 10 + 12 / 300 + 180 / 63000 = 1 / 7 := by norm_num

theorem denominator_997_terminates :
    EventuallyTerminates consecutive 1 997 ∧
      EventuallyTerminates missingRadix 1 997 :=
  ⟨consecutive_terminates 1 997 (by decide), missingRadix_terminates 1 997 (by decide)⟩

theorem denominator_9997_terminates :
    EventuallyTerminates consecutive 1 9997 ∧
      EventuallyTerminates missingRadix 1 9997 :=
  ⟨consecutive_terminates 1 9997 (by decide), missingRadix_terminates 1 9997 (by decide)⟩

end RadixTermination
