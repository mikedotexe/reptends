import RadixRuns.HandoffSearch

/-! A signed balance selects whether to retain or replace the current radix.
Accepted zero digits are supported; the unconditional continuation theorem uses
positive targets, after any separately certified prefix (including seed zeros). -/
namespace RadixBalance.Continuing
open HandoffSearch RadixTermination Filter Topology

def balance (D r a B : ℕ) : ℤ := (B : ℤ) * r - (D : ℤ) * a
def Fits (D r a B : ℕ) : Prop := D * a < B * r ∧ B * r < D * a + D
instance (D r a B : ℕ) : Decidable (Fits D r a B) := inferInstanceAs (Decidable (_ ∧ _))

theorem fits_iff_balance (D r a B : ℕ) :
    Fits D r a B ↔ 0 < balance D r a B ∧ balance D r a B < D := by
  unfold Fits balance
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₁' : (D : ℤ) * a < (B : ℤ) * r := by exact_mod_cast h₁
    have h₂' : (B : ℤ) * r < (D : ℤ) * a + D := by exact_mod_cast h₂
    omega
  · rintro ⟨h₁, h₂⟩
    constructor
    · exact_mod_cast (show (D : ℤ) * a < (B : ℤ) * r by omega)
    · exact_mod_cast (show (B : ℤ) * r < (D : ℤ) * a + D by omega)

def chosenRadix (D r a B : ℕ) : ℕ := if Fits D r a B then B else nextRadix D r a
def chosenRemainder (D r a B : ℕ) : ℕ := chosenRadix D r a B * r - D * a

theorem keep_radix {D r a B : ℕ} (h : Fits D r a B) : chosenRadix D r a B = B := by
  simp [chosenRadix, h]
theorem change_radix {D r a B : ℕ} (h : ¬ Fits D r a B) :
    chosenRadix D r a B = D * a / r + 1 := by simp [chosenRadix, h, nextRadix]

theorem chosen_bounds {D r a B : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (ha : Fits D r a B ∨ 0 < a) :
    2 ≤ chosenRadix D r a B ∧ 0 < chosenRemainder D r a B ∧
      chosenRemainder D r a B < D ∧
      chosenRadix D r a B * r = D * a + chosenRemainder D r a B := by
  by_cases hf : Fits D r a B
  · have hk := keep_radix hf
    rcases hf with ⟨h₁, h₂⟩
    simp only [chosenRemainder, hk]
    omega
  · have hp : 0 < a := ha.resolve_left hf
    have he := next_step (D := D) (d := a) hr
    have ht := next_remainder_pos (D := D) (d := a) hr
    have hu := next_remainder_lt (d := a) hrD
    have hb := next_radix_valid hr hrD hp
    simp only [chosenRemainder, chosenRadix, if_neg hf]
    omega

theorem chosen_digit {D r a B : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (ha : Fits D r a B ∨ 0 < a) : chosenRadix D r a B * r / D = a := by
  have h := chosen_bounds hr hrD hB ha
  exact certified_digit h.2.2.1 h.2.2.2

theorem chosen_remainder {D r a B : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (ha : Fits D r a B ∨ 0 < a) :
    chosenRadix D r a B * r % D = chosenRemainder D r a B := by
  have h := chosen_bounds hr hrD hB ha
  exact certified_remainder h.2.2.1 h.2.2.2

theorem chosen_digit_legal {D r a B : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (ha : Fits D r a B ∨ 0 < a) : a < chosenRadix D r a B := by
  have h := chosen_bounds hr hrD hB ha
  exact certified_digit_legal hrD (by omega) h.2.2.2

theorem fits_iff_digit_and_positive_remainder {D r a B : ℕ} (hD : 0 < D) :
    Fits D r a B ↔ B * r / D = a ∧ 0 < B * r % D := by
  constructor
  · intro hf
    have he : B * r = D * a + (B * r - D * a) := by rcases hf with ⟨_, _⟩; omega
    have ht : B * r - D * a < D := by rcases hf with ⟨_, _⟩; omega
    have hd := certified_digit ht he
    have hm := certified_remainder ht he
    exact ⟨hd, by rw [hm]; rcases hf with ⟨_, _⟩; omega⟩
  · rintro ⟨hd, hm⟩
    have he := Nat.mod_add_div (B * r) D
    have ht := Nat.mod_lt (B * r) hD
    rw [hd] at he
    unfold Fits
    omega

theorem rejected_radix_changes {D r a B : ℕ} (hr : 0 < r) (hrD : r < D)
    (hB : 2 ≤ B) (ha : 0 < a) (hf : ¬ Fits D r a B) : chosenRadix D r a B ≠ B := by
  intro he
  have h := chosen_bounds hr hrD hB (Or.inr ha)
  have hd := chosen_digit hr hrD hB (Or.inr ha)
  have hm := chosen_remainder hr hrD hB (Or.inr ha)
  apply hf
  apply (fits_iff_digit_and_positive_remainder (by omega)).2
  rw [he] at hd hm
  exact ⟨hd, by rw [hm]; exact h.2.1⟩

theorem switched_radix_minimal {D r a B R t : ℕ} (hr : 0 < r)
    (hf : ¬ Fits D r a B) (ht : 0 < t) (he : R * r = D * a + t) :
    chosenRadix D r a B ≤ R := by
  simp only [chosenRadix, if_neg hf]
  exact next_radix_minimal hr ht he

theorem chosen_preserves_prefix {A D P Q r a B : ℕ}
    (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B) (ha : Fits D r a B ∨ 0 < a)
    (hv : D * Q + r = A * P) :
    D * (chosenRadix D r a B * Q + a) + chosenRemainder D r a B =
      A * (P * chosenRadix D r a B) :=
  bridge_preserves_identity hv (chosen_bounds hr hrD hB ha).2.2.2

def state (D B r : ℕ) (a : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (B, r)
  | n + 1 => let s := state D B r a n
    (chosenRadix D s.2 (a n) s.1, chosenRemainder D s.2 (a n) s.1)
def radices (D B r : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℕ := (state D B r a (n + 1)).1

theorem state_valid {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    2 ≤ (state D B r a n).1 ∧ 0 < (state D B r a n).2 ∧ (state D B r a n).2 < D := by
  induction n with
  | zero => exact ⟨hB, hr, hrD⟩
  | succ n ih =>
    have h := chosen_bounds ih.2.1 ih.2.2 ih.1 (Or.inr (ha n))
    exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem radices_valid {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) : ValidRadices (radices D B r a) :=
  fun n => (state_valid hr hrD hB a ha (n + 1)).1

theorem state_step {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    radices D B r a n * (state D B r a n).2 = D * a n + (state D B r a (n + 1)).2 := by
  have h := state_valid hr hrD hB a ha n
  exact (chosen_bounds h.2.1 h.2.2 h.1 (Or.inr (ha n))).2.2.2

theorem state_remainder {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    remainder (radices D B r a) r D n = (state D B r a n).2 := by
  induction n with
  | zero => exact remainder_zero_of_lt _ hrD
  | succ n ih =>
    rw [remainder_succ, ih]
    exact certified_remainder (state_valid hr hrD hB a ha (n + 1)).2.2 (state_step hr hrD hB a ha n)

theorem stream_digit {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    digit (radices D B r a) r D n = a n := by
  unfold digit
  rw [state_remainder hr hrD hB a ha]
  exact certified_digit (state_valid hr hrD hB a ha (n + 1)).2.2 (state_step hr hrD hB a ha n)

theorem stream_prefix_add_tail {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    (digitPrefix (radices D B r a) r D n : ℚ) / placeProduct (radices D B r a) n +
      ((state D B r a n).2 : ℚ) / (D * placeProduct (radices D B r a) n) = (r : ℚ) / D := by
  have h := (exact_value _ (radices_valid hr hrD hB a ha) r D n (by omega)).symm
  simpa only [state_remainder hr hrD hB a ha] using h

noncomputable def term (D B r : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (a n : ℝ) / (placeProduct (radices D B r a) (n + 1) : ℝ)
noncomputable def tail (D B r : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((state D B r a n).2 : ℝ) / (D * placeProduct (radices D B r a) n)

theorem term_add_tail {D B r : ℕ} (hr : 0 < r) (hrD : r < D) (hB : 2 ≤ B)
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    term D B r a n + tail D B r a (n + 1) = tail D B r a n := by
  have hb := radices_valid hr hrD hB a ha
  have hp : (placeProduct (radices D B r a) n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (placeProduct_pos _ hb n))
  have hrad : (radices D B r a n : ℝ) ≠ 0 := by exact_mod_cast (show radices D B r a n ≠ 0 by have := hb n; omega)
  have hD : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have he : (radices D B r a n : ℝ) * (state D B r a n).2 = (D : ℝ) * a n + (state D B r a (n + 1)).2 := by
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
  have hrem : ((state D B r a n).2 : ℝ) ≤ D := by exact_mod_cast (state_valid hr hrD hB a ha n).2.2.le
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

theorem powers_keep : Fits 997 243 243 1000 ∧ chosenRadix 997 243 243 1000 = 1000 := by
  norm_num [Fits, chosenRadix]
theorem powers_switch : balance 997 729 729 1000 = 2187 ∧ chosenRadix 997 729 729 1000 = 998 ∧
    chosenRemainder 997 729 729 1000 = 729 := by norm_num [balance, chosenRadix, chosenRemainder, Fits, nextRadix]
theorem fibonacci_seed : Fits 9899 1 0 100 := by norm_num [Fits]
theorem fibonacci_keep : Fits 9899 5534 55 100 ∧ chosenRemainder 9899 5534 55 100 = 8955 := by
  norm_num [Fits, chosenRadix, chosenRemainder]
theorem fibonacci_switch : balance 9899 8955 89 100 = 14489 ∧ chosenRadix 9899 8955 89 100 = 99 ∧
    chosenRemainder 9899 8955 89 100 = 5534 := by norm_num [balance, chosenRadix, chosenRemainder, Fits, nextRadix]
theorem fibonacci_next : balance 9899 5534 144 99 = -877590 ∧ chosenRadix 9899 5534 144 99 = 258 ∧
    chosenRemainder 9899 5534 144 99 = 2316 := by norm_num [balance, chosenRadix, chosenRemainder, Fits, nextRadix]
theorem counting_seed : Fits 998001 1 0 1000 := by norm_num [Fits]
theorem counting_keep : Fits 998001 996004 997 1000 ∧ chosenRemainder 998001 996004 997 1000 = 997003 := by
  norm_num [Fits, chosenRadix, chosenRemainder]
theorem counting_switch : balance 998001 997003 998 1000 = 998002 ∧ chosenRadix 998001 997003 998 1000 = 999 ∧
    chosenRemainder 998001 997003 998 1000 = 999 := by norm_num [balance, chosenRadix, chosenRemainder, Fits, nextRadix]
theorem zero_balance_switch : balance 8 1 1 8 = 0 ∧ chosenRadix 8 1 1 8 = 9 ∧
    chosenRemainder 8 1 1 8 = 1 := by norm_num [balance, chosenRadix, chosenRemainder, Fits, nextRadix]
end RadixBalance.Continuing
