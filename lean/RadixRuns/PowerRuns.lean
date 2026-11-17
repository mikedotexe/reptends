import RadixRuns.Core
import RadixRuns.Powers

/-! The powers construction as actual run records and evolving division states.
Every run has one digit and is a first return of the current remainder. -/
namespace RadixRuns

def powerRun (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) : Run :=
  Run.single (powerRadix D c n) (powerRadix_valid hD hc n)

@[simp] theorem powerRun_radix (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (powerRun D c hD hc n).radix = powerRadix D c n := rfl

@[simp] theorem powerRun_length (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (powerRun D c hD hc n).length = 1 := rfl

@[simp] theorem powerRun_scale (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (powerRun D c hD hc n).scale = powerRadix D c n := by
  simp [powerRun]

theorem powerRun_packed (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (powerRun D c hD hc n).packed 1 D = c ^ n := by
  have h := power_digit (c := c) hD n
  simpa [RadixTermination.digit, power_remainder hD, Run.packed] using h

theorem powerRun_firstReturn (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (powerRun D c hD hc n).FirstReturn 1 D := by
  rw [powerRun, Run.single_firstReturn_iff]
  simp [powerRadix, Nat.add_mod, Nat.mod_eq_of_lt hD]

theorem powerRun_tail (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (powerRun D c hD hc n).tail 1 D = 1 :=
  (powerRun_firstReturn D c hD hc n).1

theorem powerRun_digit (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ)
    (j : Fin (powerRun D c hD hc n).length) :
    (powerRun D c hD hc n).digit 1 D j = c ^ n := by
  have hj : j.val = 0 := by have h := j.isLt; simp only [powerRun_length] at h; omega
  have hp := powerRun_packed D c hD hc n
  simpa [Run.digit, RadixTermination.digit, hj, RadixTermination.remainder,
    RadixTermination.placeProduct, Nat.mod_eq_of_lt hD, Run.packed] using hp

def powerState (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) : ℕ → DivisionState D
  | 0 => DivisionState.initial 1 D hD
  | n + 1 => (powerState D c hD hc n).advance (powerRun D c hD hc n)

@[simp] theorem powerState_remainder (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (powerState D c hD hc n).remainder = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [powerState, DivisionState.advance_remainder, ih]
    exact powerRun_tail D c hD hc n

theorem powerState_place (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (powerState D c hD hc n).place =
      RadixTermination.placeProduct (powerRadix D c) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [powerState, DivisionState.advance_place, ih, powerRun_scale,
      RadixTermination.placeProduct_succ]

theorem powerState_quotient (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (powerState D c hD hc n).quotient =
      RadixTermination.digitPrefix (powerRadix D c) 1 D n := by
  induction n with
  | zero =>
    simp [powerState, DivisionState.initial, RadixTermination.digitPrefix,
      Nat.div_eq_of_lt hD]
  | succ n ih =>
    rw [powerState, DivisionState.advance_prefix, ih, powerState_remainder,
      powerRun_packed, powerRun_scale,
      RadixTermination.prefix_succ (powerRadix D c) 1 n (by omega), power_digit hD]
    ring

theorem powerState_value (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (powerState D c hD hc n).value = 1 / (D : ℚ) := by
  induction n with
  | zero => simp [powerState]
  | succ n ih => simpa only [powerState, DivisionState.advance_value] using ih

theorem powerState_next_firstReturn (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (powerRun D c hD hc n).FirstReturn (powerState D c hD hc n).remainder D := by
  rw [powerState_remainder]
  exact powerRun_firstReturn D c hD hc n

theorem powerState_place_strictMono (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) :
    StrictMono (fun n => (powerState D c hD hc n).place) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact DivisionState.advance_place_gt (powerState D c hD hc n) (powerRun D c hD hc n)

theorem powerState_injective (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) :
    Function.Injective (powerState D c hD hc) := by
  intro m n h
  exact (powerState_place_strictMono D c hD hc).injective
    (congrArg DivisionState.place h)

/-- The first `n` explicitly marked one-digit runs, in chronological order. -/
def powerRuns (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) : List Run :=
  (List.range n).map (powerRun D c hD hc)

theorem powerRuns_execute (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (DivisionState.initial 1 D hD).execute (powerRuns D c hD hc n) =
      powerState D c hD hc n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [powerRuns, List.range_succ, List.map_append, List.map_singleton,
      DivisionState.execute_append, DivisionState.execute]
    simpa only [powerState] using
      congrArg (fun s : DivisionState D => s.advance (powerRun D c hD hc n)) ih

theorem firstReturnSequence_of_constant_anchor {D R : ℕ} (runs : List Run)
    (s : DivisionState D) (hs : s.remainder = R)
    (hr : ∀ run ∈ runs, run.FirstReturn R D) : s.FirstReturnSequence runs := by
  induction runs generalizing s with
  | nil => trivial
  | cons run runs ih =>
    have hrun : run.FirstReturn s.remainder D := by
      rw [hs]
      exact hr run (by simp)
    refine ⟨hrun, ih (s.advance run) ?_ ?_⟩
    · exact (DivisionState.remainder_at_return s run hrun.1).trans hs
    · intro next hnext
      exact hr next (by simp [hnext])

theorem powerRuns_firstReturnSequence (D c : ℕ) (hD : 1 < D) (hc : 2 ≤ c)
    (n : ℕ) :
    (DivisionState.initial 1 D hD).FirstReturnSequence (powerRuns D c hD hc n) := by
  apply firstReturnSequence_of_constant_anchor _ _ (R := 1) rfl
  intro run hr
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr
  exact powerRun_firstReturn D c hD hc k

end RadixRuns
