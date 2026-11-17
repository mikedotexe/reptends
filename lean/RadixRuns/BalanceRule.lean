import RadixRuns.BalanceContinue

/-! The public balance rule accepts zero as successful completion. The positive
continuation core is used only when the current radix does not finish exactly. -/
namespace RadixBalance
open HandoffSearch RadixTermination

def balance := Continuing.balance
def Fits (D r a B : ℕ) : Prop := D * a ≤ B * r ∧ B * r < D * a + D

def chosenRadix (D r a B : ℕ) : ℕ :=
  if balance D r a B = 0 then B else Continuing.chosenRadix D r a B

def chosenRemainder (D r a B : ℕ) : ℕ :=
  if balance D r a B = 0 then 0 else Continuing.chosenRemainder D r a B

theorem fits_iff_balance (D r a B : ℕ) :
    Fits D r a B ↔ 0 ≤ balance D r a B ∧ balance D r a B < D := by
  unfold Fits balance Continuing.balance
  constructor
  · rintro ⟨h₁,h₂⟩
    have h₁' : (D : ℤ) * a ≤ (B : ℤ) * r := by exact_mod_cast h₁
    have h₂' : (B : ℤ) * r < (D : ℤ) * a + D := by exact_mod_cast h₂
    omega
  · rintro ⟨h₁,h₂⟩
    constructor
    · exact_mod_cast (show (D : ℤ) * a ≤ (B : ℤ) * r by omega)
    · exact_mod_cast (show (B : ℤ) * r < (D : ℤ) * a + D by omega)

theorem balance_zero_iff (D r a B : ℕ) : balance D r a B = 0 ↔ B * r = D * a := by
  unfold balance Continuing.balance
  constructor
  · intro h
    exact_mod_cast (show (B : ℤ) * r = (D : ℤ) * a by omega)
  · intro h
    have hz : (B : ℤ) * r = (D : ℤ) * a := by exact_mod_cast h
    omega

theorem keep_radix {D r a B : ℕ} (hf : Fits D r a B) : chosenRadix D r a B = B := by
  unfold chosenRadix
  split_ifs with hz
  · rfl
  · apply Continuing.keep_radix
    have hn := (balance_zero_iff D r a B).not.mp hz
    unfold Fits at hf
    unfold Continuing.Fits
    omega

theorem change_radix {D r a B : ℕ} (hD : 0 < D) (hf : ¬ Fits D r a B) :
    chosenRadix D r a B = D * a / r + 1 := by
  have hz : balance D r a B ≠ 0 := by
    intro hz
    have he := (balance_zero_iff D r a B).mp hz
    apply hf
    unfold Fits
    omega
  have hc : ¬ Continuing.Fits D r a B := by unfold Fits Continuing.Fits at *; omega
  simp only [chosenRadix, if_neg hz]
  exact Continuing.change_radix hc

theorem chosen_bounds {D r a B : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (ha : Fits D r a B ∨ 0 < a) :
    2 ≤ chosenRadix D r a B ∧ chosenRemainder D r a B < D ∧
      chosenRadix D r a B * r = D * a + chosenRemainder D r a B := by
  by_cases hz : balance D r a B = 0
  · have he := (balance_zero_iff D r a B).mp hz
    simp only [chosenRadix, chosenRemainder, if_pos hz]
    omega
  · have hc : Continuing.Fits D r a B ∨ 0 < a := by
      rcases ha with hf | hp
      · left
        have hn := (balance_zero_iff D r a B).not.mp hz
        unfold Fits at hf
        unfold Continuing.Fits
        omega
      · exact Or.inr hp
    have h := Continuing.chosen_bounds hr hrD hB hc
    simpa only [chosenRadix, chosenRemainder, if_neg hz] using ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem chosen_digit {D r a B : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (ha : Fits D r a B ∨ 0 < a) : chosenRadix D r a B * r / D = a := by
  have h := chosen_bounds hr hrD hB ha
  exact certified_digit h.2.1 h.2.2

theorem chosen_remainder {D r a B : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (ha : Fits D r a B ∨ 0 < a) : chosenRadix D r a B * r % D = chosenRemainder D r a B := by
  have h := chosen_bounds hr hrD hB ha
  exact certified_remainder h.2.1 h.2.2

theorem chosen_digit_legal {D r a B : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (ha : Fits D r a B ∨ 0 < a) : a < chosenRadix D r a B := by
  have h := chosen_bounds hr hrD hB ha
  exact certified_digit_legal hrD (by omega) h.2.2

theorem zero_finishes {D r a B : ℕ} (hz : balance D r a B = 0) :
    chosenRadix D r a B = B ∧ chosenRemainder D r a B = 0 := by
  simp [chosenRadix, chosenRemainder, hz]

theorem positive_step_agrees {D r a B : ℕ} (hz : balance D r a B ≠ 0) :
    chosenRadix D r a B = Continuing.chosenRadix D r a B ∧
      chosenRemainder D r a B = Continuing.chosenRemainder D r a B := by
  simp [chosenRadix, chosenRemainder, hz]

theorem chosen_preserves_prefix {A D P Q r a B : ℕ}
    (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B) (ha : Fits D r a B ∨ 0 < a)
    (hv : D * Q + r = A * P) :
    D * (chosenRadix D r a B * Q + a) + chosenRemainder D r a B =
      A * (P * chosenRadix D r a B) :=
  bridge_preserves_identity hv (chosen_bounds hr hrD hB ha).2.2

theorem chosen_preserves_value {D P Q r a B : ℕ}
    (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B) (hP : 0 < P)
    (ha : Fits D r a B ∨ 0 < a) :
    ((chosenRadix D r a B * Q + a : ℕ) : ℚ) / (P * chosenRadix D r a B) +
      (chosenRemainder D r a B : ℚ) / (D * (P * chosenRadix D r a B)) =
      (Q : ℚ) / P + (r : ℚ) / (D * P) := by
  have h := chosen_bounds hr hrD hB ha
  exact bridge_preserves_value (by omega) hP (by omega) h.2.2

theorem finished_prefix_value {A D P Q : ℕ} (hD : 0 < D) (hP : 0 < P)
    (hv : D * Q = A * P) : (Q : ℚ) / P = (A : ℚ) / D := by
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hp : (P : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have he : (D : ℚ) * Q = (A : ℚ) * P := by exact_mod_cast hv
  field_simp
  nlinarith

theorem zero_remainder_only_zero_digits (D B : ℕ) : B * 0 / D = 0 ∧ B * 0 % D = 0 := by simp

theorem example_decimal_finish : balance 8 4 5 10 = 0 ∧ chosenRadix 8 4 5 10 = 10 ∧
    chosenRemainder 8 4 5 10 = 0 ∧ (125 : ℚ) / 1000 = 1 / 8 := by
  norm_num [balance, Continuing.balance, chosenRadix, chosenRemainder]


/-- A completed state remains completed. The zero padding is ordinary positional
notation; it does not pretend that later positive target terms were emitted. -/
def state (D B r : ℕ) (a : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (B, r)
  | n + 1 => let s := state D B r a n
    if s.2 = 0 then s else
      (chosenRadix D s.2 (a n) s.1, chosenRemainder D s.2 (a n) s.1)
def radices (D B r : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℕ := (state D B r a (n + 1)).1
def written (D B r : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  if (state D B r a n).2 = 0 then 0 else a n

theorem state_valid {D B r : ℕ} (_hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    2 ≤ (state D B r a n).1 ∧ (state D B r a n).2 < D := by
  induction n with
  | zero => exact ⟨hB,hrD⟩
  | succ n ih =>
    by_cases hz : (state D B r a n).2 = 0
    · simpa [state, hz] using ih
    · have h := chosen_bounds (by omega) ih.2 ih.1 (Or.inr (ha n))
      simpa [state, hz] using ⟨h.1,h.2.1⟩

theorem radices_valid {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) : ValidRadices (radices D B r a) :=
  fun n => (state_valid hr hrD hB a ha (n+1)).1

theorem state_step {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    radices D B r a n * (state D B r a n).2 =
      D * written D B r a n + (state D B r a (n+1)).2 := by
  have h := state_valid hr hrD hB a ha n
  by_cases hz : (state D B r a n).2 = 0
  · simp [radices,state,written,hz]
  · have he := (chosen_bounds (by omega) h.2 h.1 (Or.inr (ha n))).2.2
    simpa [radices,state,written,hz] using he

theorem state_remainder {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    remainder (radices D B r a) r D n = (state D B r a n).2 := by
  induction n with
  | zero => exact remainder_zero_of_lt _ hrD
  | succ n ih =>
    rw [remainder_succ, ih]
    exact certified_remainder (state_valid hr hrD hB a ha (n+1)).2 (state_step hr hrD hB a ha n)

theorem stream_digit {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    digit (radices D B r a) r D n = written D B r a n := by
  unfold digit
  rw [state_remainder hr hrD hB a ha]
  exact certified_digit (state_valid hr hrD hB a ha (n+1)).2 (state_step hr hrD hB a ha n)

theorem completed_stays_completed {D B r : ℕ} (a : ℕ → ℕ) (n : ℕ)
    (hz : (state D B r a n).2 = 0) :
    (state D B r a (n+1)).2 = 0 ∧ written D B r a n = 0 := by
  simp [state,written,hz]

open Filter Topology
noncomputable def term (D B r : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (written D B r a n : ℝ) / (placeProduct (radices D B r a) (n + 1) : ℝ)
noncomputable def tail (D B r : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((state D B r a n).2 : ℝ) / (D * placeProduct (radices D B r a) n)

theorem term_add_tail {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    term D B r a n + tail D B r a (n + 1) = tail D B r a n := by
  have hb := radices_valid hr hrD hB a ha
  have hp : (placeProduct (radices D B r a) n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (placeProduct_pos _ hb n))
  have hrad : (radices D B r a n : ℝ) ≠ 0 := by exact_mod_cast (show radices D B r a n ≠ 0 by have := hb n; omega)
  have hD : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have he : (radices D B r a n : ℝ) * (state D B r a n).2 = (D : ℝ) * written D B r a n + (state D B r a (n + 1)).2 := by
    exact_mod_cast state_step hr hrD hB a ha n
  unfold term tail
  rw [placeProduct_succ]
  push_cast
  field_simp
  nlinarith [he]

theorem partialSum_add_tail {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    (∑ k ∈ Finset.range n, term D B r a k) + tail D B r a n = (r : ℝ) / D := by
  induction n with
  | zero => simp [tail, state, placeProduct]
  | succ n ih => rw [Finset.sum_range_succ, add_assoc, term_add_tail hr hrD hB a ha, ih]

theorem tail_tendsto_zero {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) : Tendsto (tail D B r a) atTop (𝓝 0) := by
  have hb := radices_valid hr hrD hB a ha
  have ht := tendsto_inv_atTop_zero.comp (RadixRuns.placeProduct_tendsto_atTop _ hb)
  apply squeeze_zero (fun n => by unfold tail; positivity) _ ht
  intro n
  have hp : (0 : ℝ) < placeProduct (radices D B r a) n := by exact_mod_cast placeProduct_pos _ hb n
  have hD : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hrem : ((state D B r a n).2 : ℝ) ≤ D := by exact_mod_cast (state_valid hr hrD hB a ha n).2.le
  unfold tail
  calc
    _ ≤ (D : ℝ) / (D * placeProduct (radices D B r a) n) := div_le_div_of_nonneg_right hrem (by positivity)
    _ = _ := by simp only [Function.comp_apply]; field_simp

theorem stream_hasSum {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) : HasSum (term D B r a) ((r : ℝ) / D) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by unfold term; positivity) _).2
  have ht := (tendsto_const_nhds (x := (r : ℝ) / D)).sub (tail_tendsto_zero hr hrD hB a ha)
  have he (n : ℕ) : (∑ k ∈ Finset.range n, term D B r a k) = (r : ℝ) / D - tail D B r a n := by
    have := partialSum_add_tail hr hrD hB a ha n
    linarith
  simp only [he]
  simpa using ht

theorem after_prefix_hasSum {A D P Q r B : ℕ} (hr : 0 < r) (hrD : r < D)
    (hB : 2 ≤ B) (hP : 0 < P) (hv : D * Q + r = A * P)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) :
    HasSum (fun n => term D B r a n / (P : ℝ)) ((A : ℝ) / D - (Q : ℝ) / P) := by
  have hs := (stream_hasSum hr hrD hB a ha).div_const (P : ℝ)
  have hD : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hp : (P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have he : (D : ℝ) * Q + r = (A : ℝ) * P := by exact_mod_cast hv
  have hx : ((r : ℝ) / D) / P = (A : ℝ) / D - (Q : ℝ) / P := by field_simp; nlinarith [he]
  simpa only [hx] using hs

end RadixBalance
