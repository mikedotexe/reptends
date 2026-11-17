import RadixRuns.PowerRuns
import RetainedProgression.Examples

/-! The reciprocal 1/997 as a sequence of actual one-digit return runs.
The theorems quantify over every position, including positions past 166. -/
namespace RadixRuns

abbrev run997 (n : ℕ) : Run := powerRun 997 3 (by decide) (by decide) n

abbrev state997 (n : ℕ) : DivisionState 997 :=
  powerState 997 3 (by decide) (by decide) n

theorem first_four_radices_997 :
    (run997 0).radix = 998 ∧ (run997 1).radix = 2992 ∧
      (run997 2).radix = 8974 ∧ (run997 3).radix = 26920 := by
  norm_num [run997, powerRadix]

theorem first_four_digits_997 :
    (run997 0).packed 1 997 = 1 ∧ (run997 1).packed 1 997 = 3 ∧
      (run997 2).packed 1 997 = 9 ∧ (run997 3).packed 1 997 = 27 := by
  norm_num [run997, powerRun_packed]

theorem run997_digit (n : ℕ) (j : Fin (run997 n).length) :
    (run997 n).digit 1 997 j = 3 ^ n :=
  powerRun_digit 997 3 (by decide) (by decide) n j

theorem run997_digit_legal (n : ℕ) : 3 ^ n < (run997 n).radix :=
  power_digit_legal (by decide) n

theorem run997_firstReturn (n : ℕ) :
    (run997 n).FirstReturn (state997 n).remainder 997 :=
  powerState_next_firstReturn 997 3 (by decide) (by decide) n

theorem state997_remainder (n : ℕ) : (state997 n).remainder = 1 :=
  powerState_remainder 997 3 (by decide) (by decide) n

theorem state997_value (n : ℕ) : (state997 n).value = 1 / (997 : ℚ) :=
  powerState_value 997 3 (by decide) (by decide) n

theorem state997_place_strictMono : StrictMono (fun n => (state997 n).place) :=
  powerState_place_strictMono 997 3 (by decide) (by decide)

theorem state997_injective : Function.Injective state997 :=
  powerState_injective 997 3 (by decide) (by decide)

theorem first_four_state_997 :
    (state997 4).place = 721361984161280 ∧
      (state997 4).quotient = 723532581907 ∧ (state997 4).remainder = 1 := by
  norm_num [state997, powerState, DivisionState.initial, DivisionState.advance,
    powerRun, Run.single, Run.scale, Run.packed, Run.tail, powerRadix]

/-- No special cutoff occurs at the earlier fixed-radix return position. -/
theorem powers_past_166_are_digits :
    (run997 166).packed 1 997 = 3 ^ 166 ∧
      (run997 167).packed 1 997 = 3 ^ 167 ∧
      (run997 168).packed 1 997 = 3 ^ 168 :=
  ⟨powerRun_packed 997 3 (by decide) (by decide) 166,
    powerRun_packed 997 3 (by decide) (by decide) 167,
    powerRun_packed 997 3 (by decide) (by decide) 168⟩

theorem same_remainder_growing_place_past_166 :
    (state997 166).remainder = (state997 167).remainder ∧
      (state997 166).place < (state997 167).place ∧
      state997 166 ≠ state997 167 := by
  refine ⟨by rw [state997_remainder, state997_remainder],
    state997_place_strictMono (by decide), ?_⟩
  exact state997_injective.ne (by decide)

theorem recorded_runs_997_preserve_value (n : ℕ) :
    ((DivisionState.initial 1 997 (by decide)).execute
      (powerRuns 997 3 (by decide) (by decide) n)).value = 1 / (997 : ℚ) := by
  rw [powerRuns_execute]
  exact state997_value n

theorem recorded_runs_997_are_first_returns (n : ℕ) :
    (DivisionState.initial 1 997 (by decide)).FirstReturnSequence
      (powerRuns 997 3 (by decide) (by decide) n) :=
  powerRuns_firstReturnSequence 997 3 (by decide) (by decide) n

theorem power_runs_997_have_infinite_value :
    HasSum (powerTerm 997 3) (1 / (997 : ℝ)) := power_997_hasSum

/-- The old geometric stream and the new legal-digit stream have equal values. -/
theorem power_runs_same_value_as_geometric_997 :
    HasSum (powerTerm 997 3) (RetainedProgression.geometric 1000 3).value := by
  rw [RetainedProgression.decimal_blocks_997_value]
  exact power_997_hasSum

theorem power_runs_different_weights_997 :
    powerTerm 997 3 0 ≠ (RetainedProgression.geometric 1000 3).term 0 := by
  norm_num [powerTerm, powerRadix, RadixTermination.placeProduct,
    RetainedProgression.geometric, RetainedProgression.Expansion.term]

end RadixRuns
