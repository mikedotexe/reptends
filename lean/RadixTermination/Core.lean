import RadixTermination.Common

/-! Exact mixed-radix division and its termination criterion. -/
namespace RadixTermination

/-- The accumulated mixed-radix digit prefix, as an integer. -/
def digitPrefix (b : ℕ → ℕ) (A D n : ℕ) : ℕ :=
  A * placeProduct b n / D

/-- The digit emitted when the next radix is `b n`. -/
def digit (b : ℕ → ℕ) (A D n : ℕ) : ℕ :=
  b n * remainder b A D n / D

theorem placeProduct_pos (b : ℕ → ℕ) (hb : ValidRadices b) (n : ℕ) :
    0 < placeProduct b n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [placeProduct_succ]
    exact Nat.mul_pos ih (by have := hb n; omega)

theorem placeProduct_dvd_of_le (b : ℕ → ℕ) {n m : ℕ} (h : n ≤ m) :
    placeProduct b n ∣ placeProduct b m := by
  induction h with
  | refl => exact dvd_refl _
  | @step m h ih =>
    exact dvd_trans ih (by rw [placeProduct_succ]; exact dvd_mul_right _ _)

@[simp] theorem remainder_zero (b : ℕ → ℕ) (A D : ℕ) :
    remainder b A D 0 = A % D := by
  simp [remainder]

theorem remainder_zero_of_lt (b : ℕ → ℕ) {A D : ℕ} (h : A < D) :
    remainder b A D 0 = A := by
  simpa using Nat.mod_eq_of_lt h

theorem remainder_lt (b : ℕ → ℕ) (A n : ℕ) {D : ℕ} (hD : 0 < D) :
    remainder b A D n < D := Nat.mod_lt _ hD

theorem remainder_succ (b : ℕ → ℕ) (A D n : ℕ) :
    remainder b A D (n + 1) = (b n * remainder b A D n) % D := by
  simp [remainder, placeProduct_succ, Nat.mul_comm, Nat.mul_left_comm]

theorem state_identity (b : ℕ → ℕ) (A D n : ℕ) :
    A * placeProduct b n = D * digitPrefix b A D n + remainder b A D n := by
  simpa [digitPrefix, remainder, Nat.add_comm] using
    (Nat.mod_add_div (A * placeProduct b n) D).symm

theorem step_identity (b : ℕ → ℕ) (A D n : ℕ) :
    b n * remainder b A D n =
      D * digit b A D n + remainder b A D (n + 1) := by
  rw [remainder_succ]
  simpa [digit, Nat.add_comm] using
    (Nat.mod_add_div (b n * remainder b A D n) D).symm

theorem digit_lt (b : ℕ → ℕ) (A n : ℕ) {D : ℕ}
    (hD : 0 < D) (hb : 0 < b n) : digit b A D n < b n := by
  unfold digit
  exact (Nat.div_lt_iff_lt_mul hD).2 (by
    simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left (remainder_lt b A n hD) hb)

theorem prefix_succ (b : ℕ → ℕ) (A n : ℕ) {D : ℕ} (hD : 0 < D) :
    digitPrefix b A D (n + 1) = b n * digitPrefix b A D n + digit b A D n := by
  have hn := state_identity b A D n
  have hs := state_identity b A D (n + 1)
  have hd := step_identity b A D n
  rw [placeProduct_succ] at hs
  nlinarith

theorem termination_iff_dvd (b : ℕ → ℕ) (A D n : ℕ)
    (hcop : Nat.Coprime A D) :
    TerminatesAt b A D n ↔ D ∣ placeProduct b n := by
  unfold TerminatesAt remainder
  rw [← Nat.dvd_iff_mod_eq_zero]
  exact hcop.symm.dvd_mul_left

theorem terminatesAt_of_dvd (b : ℕ → ℕ) (A D n : ℕ)
    (h : D ∣ placeProduct b n) : TerminatesAt b A D n := by
  unfold TerminatesAt remainder
  exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right h A)

theorem termination_persists (b : ℕ → ℕ) (A D : ℕ) {n m : ℕ}
    (hn : TerminatesAt b A D n) (hnm : n ≤ m) : TerminatesAt b A D m := by
  induction hnm with
  | refl => exact hn
  | @step m h ih =>
    unfold TerminatesAt at *
    rw [remainder_succ, ih]
    simp

theorem eventuallyTerminates_iff_denominator_covered (b : ℕ → ℕ) (A D : ℕ)
    (hcop : Nat.Coprime A D) :
    EventuallyTerminates b A D ↔ ∃ n, D ∣ placeProduct b n := by
  simp only [EventuallyTerminates, termination_iff_dvd b A D _ hcop]

theorem eventuallyTerminates_of_denominator_coverage (b : ℕ → ℕ)
    (hcover : ∀ D : ℕ, 0 < D → ∃ n, D ∣ placeProduct b n)
    (A D : ℕ) (hD : 0 < D) : EventuallyTerminates b A D := by
  obtain ⟨n, hn⟩ := hcover D hD
  exact ⟨n, terminatesAt_of_dvd b A D n hn⟩

end RadixTermination
