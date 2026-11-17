import RadixRuns.Encoding

/-! An exact division state can be advanced through any valid run. The radix
is supplied by the run rather than fixed globally, so preservation applies
equally at a radix change. No numeral display base enters the definitions. -/
namespace RadixRuns

structure DivisionState (D : ℕ) where
  place : ℕ
  quotient : ℕ
  remainder : ℕ
  place_pos : 0 < place
  remainder_lt : remainder < D

namespace DivisionState

def value {D : ℕ} (s : DivisionState D) : ℚ :=
  (s.quotient : ℚ) / s.place + (s.remainder : ℚ) / ((D : ℚ) * s.place)

def initial (A D : ℕ) (hA : A < D) : DivisionState D :=
  ⟨1, 0, A, by decide, hA⟩

@[simp] theorem initial_value (A D : ℕ) (hA : A < D) :
    (initial A D hA).value = (A : ℚ) / D := by
  simp [initial, value]

/-- Consume a complete fixed-radix run; the next call may use any new radix. -/
def advance {D : ℕ} (s : DivisionState D) (run : Run) : DivisionState D where
  place := s.place * run.scale
  quotient := s.quotient * run.scale + run.packed s.remainder D
  remainder := run.tail s.remainder D
  place_pos := Nat.mul_pos s.place_pos run.scale_pos
  remainder_lt := run.tail_lt s.remainder (by have := s.remainder_lt; omega)

@[simp] theorem advance_place {D : ℕ} (s : DivisionState D) (run : Run) :
    (s.advance run).place = s.place * run.scale := rfl

@[simp] theorem advance_prefix {D : ℕ} (s : DivisionState D) (run : Run) :
    (s.advance run).quotient = s.quotient * run.scale + run.packed s.remainder D := rfl

@[simp] theorem advance_remainder {D : ℕ} (s : DivisionState D) (run : Run) :
    (s.advance run).remainder = run.tail s.remainder D := rfl

/-- The packed run contributes precisely `A / (P * B^L)`. -/
theorem advance_prefix_value {D : ℕ} (s : DivisionState D) (run : Run) :
    ((s.advance run).quotient : ℚ) / (s.advance run).place =
      (s.quotient : ℚ) / s.place +
        (run.packed s.remainder D : ℚ) / ((s.place : ℚ) * run.scale) := by
  have hp : (s.place : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt s.place_pos)
  have hb : (run.scale : ℚ) ≠ 0 := by exact_mod_cast run.scale_ne_zero
  simp only [advance_prefix, advance_place, Nat.cast_add, Nat.cast_mul]
  field_simp

/-- Every run preserves the exact value, including its unfinished tail. -/
theorem advance_value {D : ℕ} (s : DivisionState D) (run : Run) :
    (s.advance run).value = s.value := by
  have hp : (s.place : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt s.place_pos)
  have hb : (run.scale : ℚ) ≠ 0 := by exact_mod_cast run.scale_ne_zero
  have hd : (D : ℚ) ≠ 0 := by
    exact_mod_cast (show D ≠ 0 by have := s.remainder_lt; omega)
  have he : (s.remainder : ℚ) * run.scale =
      (D : ℚ) * run.packed s.remainder D + run.tail s.remainder D := by
    exact_mod_cast run.decomposition s.remainder D
  simp only [value, advance_place, advance_prefix, advance_remainder,
    Nat.cast_add, Nat.cast_mul]
  field_simp
  nlinarith [he]

/-- In particular, changing from one run's radix to another preserves value. -/
theorem radix_change_preserves_value {D : ℕ} (s : DivisionState D)
    (first next : Run) :
    ((s.advance first).advance next).value = s.value := by
  rw [advance_value, advance_value]

/-- The familiar numerator/quotient/remainder certificate is also preserved. -/
theorem advance_identity {D : ℕ} (s : DivisionState D) (run : Run)
    (A : ℕ) (h : A * s.place = D * s.quotient + s.remainder) :
    A * (s.advance run).place =
      D * (s.advance run).quotient + (s.advance run).remainder := by
  have he := run.decomposition s.remainder D
  simp only [advance_place, advance_prefix, advance_remainder]
  nlinarith [h, he]

theorem advance_place_gt {D : ℕ} (s : DivisionState D) (run : Run) :
    s.place < (s.advance run).place := by
  simpa only [advance_place, Nat.mul_one] using
    Nat.mul_lt_mul_of_pos_left run.scale_gt_one s.place_pos

theorem remainder_at_return {D : ℕ} (s : DivisionState D) (run : Run)
    (h : run.Returns s.remainder D) : (s.advance run).remainder = s.remainder := h

/-- At a return, the run consumes the difference between the two absolute tails. -/
theorem return_contribution {D : ℕ} (s : DivisionState D) (run : Run)
    (h : run.Returns s.remainder D) :
    (run.packed s.remainder D : ℚ) / ((s.place : ℚ) * run.scale) =
      (s.remainder : ℚ) / D *
        (1 / (s.place : ℚ) - 1 / ((s.place : ℚ) * run.scale)) := by
  have hp : (s.place : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt s.place_pos)
  have hb : (run.scale : ℚ) ≠ 0 := by exact_mod_cast run.scale_ne_zero
  have hd : (D : ℚ) ≠ 0 := by
    exact_mod_cast (show D ≠ 0 by have := s.remainder_lt; omega)
  have he : (s.remainder : ℚ) * run.scale =
      (D : ℚ) * run.packed s.remainder D + s.remainder := by
    have hn := run.decomposition s.remainder D
    rw [show run.tail s.remainder D = s.remainder from h] at hn
    exact_mod_cast hn
  field_simp
  nlinarith [he]

/-- Interpret the ordered run records of a finite mixed-radix inscription. -/
def execute {D : ℕ} (s : DivisionState D) : List Run → DivisionState D
  | [] => s
  | run :: runs => execute (s.advance run) runs

theorem execute_append {D : ℕ} (first next : List Run) (s : DivisionState D) :
    s.execute (first ++ next) = (s.execute first).execute next := by
  induction first generalizing s with
  | nil => rfl
  | cons run runs ih => simpa only [List.cons_append, execute] using ih (s.advance run)

theorem execute_value {D : ℕ} (runs : List Run) (s : DivisionState D) :
    (s.execute runs).value = s.value := by
  induction runs generalizing s with
  | nil => rfl
  | cons run runs ih =>
    simpa only [execute, advance_value] using ih (s.advance run)

theorem execute_initial_value (A D : ℕ) (hA : A < D) (runs : List Run) :
    ((initial A D hA).execute runs).value = (A : ℚ) / D := by
  rw [execute_value, initial_value]

/-- The bars of an inscription can be certified as genuine first returns. -/
def FirstReturnSequence {D : ℕ} (s : DivisionState D) : List Run → Prop
  | [] => True
  | run :: runs => run.FirstReturn s.remainder D ∧
      FirstReturnSequence (s.advance run) runs

theorem execute_remainder_at_boundaries {D : ℕ} (runs : List Run)
    (s : DivisionState D) (h : s.FirstReturnSequence runs) :
    (s.execute runs).remainder = s.remainder := by
  induction runs generalizing s with
  | nil => rfl
  | cons run runs ih =>
    change run.FirstReturn s.remainder D ∧ (s.advance run).FirstReturnSequence runs at h
    change ((s.advance run).execute runs).remainder = s.remainder
    rw [ih (s.advance run) h.2]
    exact remainder_at_return s run h.1.1

theorem execute_identity {D : ℕ} (runs : List Run) (s : DivisionState D)
    (A : ℕ) (h : A * s.place = D * s.quotient + s.remainder) :
    A * (s.execute runs).place =
      D * (s.execute runs).quotient + (s.execute runs).remainder := by
  induction runs generalizing s with
  | nil => exact h
  | cons run runs ih => exact ih (s.advance run) (advance_identity s run A h)

theorem execute_place_product {D : ℕ} (runs : List Run) (s : DivisionState D) :
    (s.execute runs).place = s.place * (runs.map Run.scale).prod := by
  induction runs generalizing s with
  | nil => simp [execute]
  | cons run runs ih =>
    simpa [execute, advance_place, Nat.mul_assoc] using ih (s.advance run)

/-- A finite ledger records each run at its correct accumulated place scale. -/
def contributions {D : ℕ} (s : DivisionState D) : List Run → ℚ
  | [] => 0
  | run :: runs =>
      (run.packed s.remainder D : ℚ) / ((s.place : ℚ) * run.scale) +
        contributions (s.advance run) runs

theorem execute_prefix_value {D : ℕ} (runs : List Run) (s : DivisionState D) :
    ((s.execute runs).quotient : ℚ) / (s.execute runs).place =
      (s.quotient : ℚ) / s.place + s.contributions runs := by
  induction runs generalizing s with
  | nil => simp [execute, contributions]
  | cons run runs ih =>
    simp only [execute, contributions]
    rw [ih, advance_prefix_value]
    ring

theorem contributions_add_tail (A D : ℕ) (hA : A < D) (runs : List Run) :
    (initial A D hA).contributions runs +
      (((initial A D hA).execute runs).remainder : ℚ) /
        ((D : ℚ) * ((initial A D hA).execute runs).place) = (A : ℚ) / D := by
  have hv := execute_initial_value A D hA runs
  unfold value at hv
  rw [execute_prefix_value] at hv
  simpa [initial] using hv

end DivisionState
end RadixRuns
