import RadixTermination.Representation

/-! A mixed-radix expansion whose legal digits are successive powers.
The remainder is always one. These digits have the mixed-radix weights, not
the weights of the earlier fixed-radix geometric expansion. -/
namespace RadixRuns

open RadixTermination
open Filter Topology

/-- The radix chosen for the digit `c^n`. -/
def powerRadix (D c n : ℕ) : ℕ := D * c ^ n + 1

theorem powerRadix_valid {D c : ℕ} (hD : 1 < D) (hc : 2 ≤ c) :
    ValidRadices (powerRadix D c) := by
  intro n
  have hp : 0 < c ^ n := pow_pos (by omega) _
  dsimp [powerRadix]
  nlinarith

theorem power_remainder {D c : ℕ} (hD : 1 < D) (n : ℕ) :
    remainder (powerRadix D c) 1 D n = 1 := by
  induction n with
  | zero => simpa using remainder_zero_of_lt (powerRadix D c) hD
  | succ n ih =>
    rw [remainder_succ, ih]
    simp [powerRadix, Nat.add_mod, Nat.mod_eq_of_lt hD]

theorem power_digit {D c : ℕ} (hD : 1 < D) (n : ℕ) :
    digit (powerRadix D c) 1 D n = c ^ n := by
  have hs := step_identity (powerRadix D c) 1 D n
  rw [power_remainder hD n, power_remainder hD (n + 1)] at hs
  simp only [powerRadix, mul_one] at hs
  nlinarith

theorem power_digit_legal {D c : ℕ} (hD : 1 < D) (n : ℕ) :
    c ^ n < powerRadix D c n := by
  have hm := Nat.mul_le_mul_right (c ^ n) (show 1 ≤ D by omega)
  dsimp [powerRadix]
  omega

theorem powerRadix_strictMono {D c : ℕ} (hD : 0 < D) (hc : 2 ≤ c) :
    StrictMono (powerRadix D c) := by
  intro m n hmn
  have hp : c ^ m < c ^ n := pow_lt_pow_right₀ (by omega) hmn
  dsimp [powerRadix]
  nlinarith

theorem power_digits_strictMono {D c : ℕ} (hD : 1 < D) (hc : 2 ≤ c) :
    StrictMono (digit (powerRadix D c) 1 D) := by
  intro m n hmn
  rw [power_digit hD, power_digit hD]
  exact pow_lt_pow_right₀ (by omega) hmn

/-- Every finite prefix, together with its residual tail, is still `1/D`. -/
theorem power_prefix_add_tail {D c : ℕ} (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (digitPrefix (powerRadix D c) 1 D n : ℚ) /
        (placeProduct (powerRadix D c) n : ℚ) +
      1 / ((D : ℚ) * (placeProduct (powerRadix D c) n : ℚ)) = 1 / (D : ℚ) := by
  simpa only [power_remainder hD, Nat.cast_one] using
    (exact_value (powerRadix D c) (powerRadix_valid hD hc) 1 D n (by omega)).symm

theorem power_never_terminates {D c : ℕ} (hD : 1 < D) :
    ¬ EventuallyTerminates (powerRadix D c) 1 D := by
  rintro ⟨n, hn⟩
  change remainder (powerRadix D c) 1 D n = 0 at hn
  rw [power_remainder hD] at hn
  contradiction

theorem power_prefix_lt_value {D c : ℕ} (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (digitPrefix (powerRadix D c) 1 D n : ℚ) /
      (placeProduct (powerRadix D c) n : ℚ) < 1 / (D : ℚ) := by
  have hp : (0 : ℚ) < placeProduct (powerRadix D c) n := by
    exact_mod_cast placeProduct_pos (powerRadix D c) (powerRadix_valid hD hc) n
  have hd : (0 : ℚ) < D := by exact_mod_cast (show 0 < D by omega)
  have ht : (0 : ℚ) < 1 / ((D : ℚ) * placeProduct (powerRadix D c) n) := by positivity
  have he := power_prefix_add_tail hD hc n
  linarith

/-- The actual real contribution of digit `c^n` in the changing radices. -/
noncomputable def powerTerm (D c n : ℕ) : ℝ :=
  (c : ℝ) ^ n / (placeProduct (powerRadix D c) (n + 1) : ℝ)

theorem powerTerm_add_tail {D c : ℕ} (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    powerTerm D c n + 1 / ((D : ℝ) * placeProduct (powerRadix D c) (n + 1)) =
      1 / ((D : ℝ) * placeProduct (powerRadix D c) n) := by
  have hp : (placeProduct (powerRadix D c) n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (placeProduct_pos _ (powerRadix_valid hD hc) n))
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hb : ((D : ℝ) * (c : ℝ) ^ n + 1) ≠ 0 := by positivity
  unfold powerTerm
  rw [placeProduct_succ]
  simp only [powerRadix, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  field_simp

theorem power_partialSum_add_tail {D c : ℕ} (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (∑ k ∈ Finset.range n, powerTerm D c k) +
      1 / ((D : ℝ) * placeProduct (powerRadix D c) n) = 1 / (D : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_assoc, powerTerm_add_tail hD hc, ih]

theorem power_partialSum_lt_value {D c : ℕ} (hD : 1 < D) (hc : 2 ≤ c) (n : ℕ) :
    (∑ k ∈ Finset.range n, powerTerm D c k) < 1 / (D : ℝ) := by
  have hp : (0 : ℝ) < placeProduct (powerRadix D c) n := by
    exact_mod_cast placeProduct_pos _ (powerRadix_valid hD hc) n
  have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have ht : (0 : ℝ) < 1 / ((D : ℝ) * placeProduct (powerRadix D c) n) := by positivity
  have he := power_partialSum_add_tail hD hc n
  linarith

/-- Valid radices force at least geometric growth in the place product. -/
theorem two_pow_le_placeProduct (b : ℕ → ℕ) (hb : ValidRadices b) (n : ℕ) :
    2 ^ n ≤ placeProduct b n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, placeProduct_succ]
    exact Nat.mul_le_mul ih (hb n)

theorem index_lt_placeProduct (b : ℕ → ℕ) (hb : ValidRadices b) (n : ℕ) :
    n < placeProduct b n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [placeProduct_succ]
    have := hb n
    nlinarith

theorem placeProduct_tendsto_atTop (b : ℕ → ℕ) (hb : ValidRadices b) :
    Tendsto (fun n => (placeProduct b n : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  exact tendsto_atTop_mono (fun n => (index_lt_placeProduct b hb n).le) tendsto_id

theorem power_tail_tendsto_zero {D c : ℕ} (hD : 1 < D) (hc : 2 ≤ c) :
    Tendsto (fun n => 1 / ((D : ℝ) * placeProduct (powerRadix D c) n))
      atTop (𝓝 0) := by
  have ht := (tendsto_inv_atTop_zero.comp
    (placeProduct_tendsto_atTop (powerRadix D c) (powerRadix_valid hD hc))).const_mul
      (1 / (D : ℝ))
  simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using ht

/-- The mixed-radix powers have an actual infinite sum, equal to `1/D`. -/
theorem power_hasSum {D c : ℕ} (hD : 1 < D) (hc : 2 ≤ c) :
    HasSum (powerTerm D c) (1 / (D : ℝ)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by
    dsimp [powerTerm]
    positivity) _).2
  have ht := (tendsto_const_nhds (x := 1 / (D : ℝ))).sub (power_tail_tendsto_zero hD hc)
  have he (n : ℕ) : (∑ k ∈ Finset.range n, powerTerm D c k) =
      1 / (D : ℝ) - 1 / ((D : ℝ) * placeProduct (powerRadix D c) n) := by
    have := power_partialSum_add_tail hD hc n
    linarith
  simp only [he]
  simpa using ht

theorem power_997_remainder (n : ℕ) : remainder (powerRadix 997 3) 1 997 n = 1 :=
  power_remainder (by decide) n

theorem power_997_digit (n : ℕ) : digit (powerRadix 997 3) 1 997 n = 3 ^ n :=
  power_digit (by decide) n

theorem power_997_hasSum : HasSum (powerTerm 997 3) (1 / (997 : ℝ)) :=
  power_hasSum (by decide) (by decide)

end RadixRuns
