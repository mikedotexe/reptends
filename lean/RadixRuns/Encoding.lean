import RadixTermination.Representation

/-! A run stores its operational radix and positive number of digit positions.
The printed base of an integer label does not enter these definitions. -/
namespace RadixRuns

structure Run where
  radix : ℕ
  length : ℕ
  radix_valid : 2 ≤ radix
  length_pos : 0 < length

namespace Run

def single (B : ℕ) (hB : 2 ≤ B) : Run := ⟨B, 1, hB, by decide⟩

def scale (run : Run) : ℕ := run.radix ^ run.length

def packed (run : Run) (R D : ℕ) : ℕ := R * run.scale / D

def tail (run : Run) (R D : ℕ) : ℕ := R * run.scale % D

def digit (run : Run) (R D : ℕ) (j : Fin run.length) : ℕ :=
  RadixTermination.digit (fun _ => run.radix) R D j.val

def Returns (run : Run) (R D : ℕ) : Prop := run.tail R D = R

def FirstReturn (run : Run) (R D : ℕ) : Prop :=
  run.Returns R D ∧ ∀ j : ℕ, 0 < j → j < run.length →
    (R * run.radix ^ j) % D ≠ R

@[simp] theorem single_radix (B : ℕ) (hB : 2 ≤ B) :
    (single B hB).radix = B := rfl

@[simp] theorem single_length (B : ℕ) (hB : 2 ≤ B) :
    (single B hB).length = 1 := rfl

@[simp] theorem single_scale (B : ℕ) (hB : 2 ≤ B) :
    (single B hB).scale = B := by simp [scale]

theorem scale_pos (run : Run) : 0 < run.scale := by
  exact pow_pos (by have := run.radix_valid; omega) _

theorem scale_gt_one (run : Run) : 1 < run.scale := by
  exact one_lt_pow' (by have := run.radix_valid; omega)
    (Nat.ne_of_gt run.length_pos)

theorem scale_ne_zero (run : Run) : run.scale ≠ 0 := Nat.ne_of_gt run.scale_pos

theorem decomposition (run : Run) (R D : ℕ) :
    R * run.scale = D * run.packed R D + run.tail R D := by
  simpa [packed, tail, Nat.add_comm] using (Nat.mod_add_div (R * run.scale) D).symm

theorem tail_lt (run : Run) (R : ℕ) {D : ℕ} (hD : 0 < D) :
    run.tail R D < D := Nat.mod_lt _ hD

theorem packed_lt_scale (run : Run) {R D : ℕ} (hR : R < D) :
    run.packed R D < run.scale := by
  apply (Nat.div_lt_iff_lt_mul (show 0 < D by omega)).2
  simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hR run.scale_pos

theorem digit_lt (run : Run) (R : ℕ) {D : ℕ} (hD : 0 < D)
    (j : Fin run.length) : run.digit R D j < run.radix := by
  exact RadixTermination.digit_lt (fun _ => run.radix) R j.val hD
    (by change 0 < run.radix; have := run.radix_valid; omega)

theorem firstReturn_returns (run : Run) {R D : ℕ} (h : run.FirstReturn R D) :
    run.Returns R D := h.1

theorem single_firstReturn_iff (B : ℕ) (hB : 2 ≤ B) (R D : ℕ) :
    (single B hB).FirstReturn R D ↔ (B * R) % D = R := by
  simp only [FirstReturn, Returns, tail, single_scale, single_length]
  constructor
  · intro h
    simpa [Nat.mul_comm] using h.1
  · intro h
    refine ⟨by simpa [Nat.mul_comm] using h, ?_⟩
    intro j hj hlt
    omega

end Run

@[simp] theorem constant_placeProduct (B n : ℕ) :
    RadixTermination.placeProduct (fun _ => B) n = B ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [RadixTermination.placeProduct_succ, ih, pow_succ]

/-- Horner evaluation of the first `n` digits, with the leading digit first. -/
def packDigits (B : ℕ) (digits : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => B * packDigits B digits n + digits n

theorem packDigits_division_eq_prefix (B R D : ℕ) (hR : R < D) (n : ℕ) :
    packDigits B (RadixTermination.digit (fun _ => B) R D) n =
      RadixTermination.digitPrefix (fun _ => B) R D n := by
  induction n with
  | zero => simp [packDigits, RadixTermination.digitPrefix, Nat.div_eq_of_lt hR]
  | succ n ih =>
    rw [packDigits, ih, RadixTermination.prefix_succ (fun _ => B) R n (by omega)]

namespace Run

/-- The run's packed integer is obtained by evaluating its emitted digits. -/
theorem packed_eq_horner (run : Run) {R D : ℕ} (hR : R < D) :
    run.packed R D =
      packDigits run.radix (RadixTermination.digit (fun _ => run.radix) R D)
        run.length := by
  rw [packDigits_division_eq_prefix run.radix R D hR run.length]
  simp [packed, scale, RadixTermination.digitPrefix]

def digitValue (run : Run) (R D : ℕ) : ℚ :=
  ∑ j ∈ Finset.range run.length,
    (RadixTermination.digit (fun _ => run.radix) R D j : ℚ) /
      (run.radix : ℚ) ^ (j + 1)

theorem digitValue_eq_packed (run : Run) {R D : ℕ} (hR : R < D) :
    run.digitValue R D = (run.packed R D : ℚ) / (run.scale : ℚ) := by
  have h := RadixTermination.digitValue_eq_prefix (fun _ => run.radix)
    (fun _ => run.radix_valid) R D hR run.length
  simpa [digitValue, RadixTermination.digitValue, RadixTermination.digitPrefix,
    packed, scale, pow_succ] using h

theorem digitValue_add_tail (run : Run) (R : ℕ) {D : ℕ} (hR : R < D) :
    run.digitValue R D + (run.tail R D : ℚ) / ((D : ℚ) * run.scale) =
      (R : ℚ) / D := by
  have h := RadixTermination.exact_value (fun _ => run.radix)
    (fun _ => run.radix_valid) R D run.length (by omega)
  rw [digitValue_eq_packed run hR]
  simpa [RadixTermination.digitPrefix, RadixTermination.remainder,
    packed, tail, scale] using h.symm

end Run
end RadixRuns
