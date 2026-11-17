import RadixTermination.Core

/-! Consecutive radices `2,3,4,...` terminate every rational denominator. -/
namespace RadixTermination

def consecutive (n : ℕ) : ℕ := n + 2

theorem consecutive_valid : ValidRadices consecutive := by
  intro n
  simp [consecutive]

theorem placeProduct_consecutive (n : ℕ) :
    placeProduct consecutive n = (n + 1).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [placeProduct_succ, ih]
    simpa [consecutive, Nat.add_assoc, Nat.mul_comm] using
      (Nat.factorial_succ (n + 1)).symm

theorem consecutive_denominator_covered (D : ℕ) (hD : 0 < D) :
    D ∣ placeProduct consecutive (D - 1) := by
  rw [placeProduct_consecutive, Nat.sub_add_cancel hD]
  exact Nat.dvd_factorial hD le_rfl

theorem consecutive_terminates_at (A D : ℕ) (hD : 0 < D) :
    TerminatesAt consecutive A D (D - 1) :=
  terminatesAt_of_dvd consecutive A D (D - 1) (consecutive_denominator_covered D hD)

theorem consecutive_terminates (A D : ℕ) (hD : 0 < D) :
    EventuallyTerminates consecutive A D :=
  ⟨D - 1, consecutive_terminates_at A D hD⟩

end RadixTermination
