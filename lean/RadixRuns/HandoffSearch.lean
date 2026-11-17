import RadixRuns.Powers

/-! Exact certificates and a universal adaptive schedule for prescribed positive digits.
All statements are independent of the glyphs used to print the natural numbers.
A bridge is one ordinary division step with a deliberately chosen next radix. -/
namespace HandoffSearch
open RadixTermination Filter Topology

/-- The only possible radix for specified entering remainder, digit and landing remainder. -/
def bridgeRadix (D r d t : ℕ) : ℕ := (D * d + t) / r

/-- This is an exact one-step test, not a claim that every desired bridge exists. -/
theorem bridge_exists_iff {D r d t : ℕ} (hr : 0 < r) :
    (∃ R : ℕ, 2 ≤ R ∧ R * r = D * d + t) ↔
      r ∣ D * d + t ∧ 2 ≤ bridgeRadix D r d t := by
  constructor
  · rintro ⟨R, hR, hstep⟩
    refine ⟨?_, ?_⟩
    · rw [← hstep]
      exact dvd_mul_left r R
    · simpa [bridgeRadix, ← hstep, Nat.mul_div_cancel _ hr] using hR
  · rintro ⟨hdiv, hR⟩
    exact ⟨bridgeRadix D r d t, hR, Nat.div_mul_cancel hdiv⟩

theorem bridge_radix_unique {D r d t R : ℕ} (hr : 0 < r)
    (hstep : R * r = D * d + t) : R = bridgeRadix D r d t := by
  simp [bridgeRadix, ← hstep, Nat.mul_div_cancel _ hr]

theorem certified_digit {D r d t R : ℕ} (ht : t < D)
    (hstep : R * r = D * d + t) : R * r / D = d := by
  rw [hstep]
  simp [Nat.add_div, Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht,
    show 0 < D by omega]
  exact ht

theorem certified_remainder {D r d t R : ℕ} (ht : t < D)
    (hstep : R * r = D * d + t) : R * r % D = t := by
  rw [hstep]
  simp [Nat.add_mod, Nat.mod_eq_of_lt ht]

theorem certified_digit_legal {D r d t R : ℕ} (hr : r < D) (hR : 0 < R)
    (hstep : R * r = D * d + t) : d < R := by
  have hlt := Nat.mul_lt_mul_of_pos_left hr hR
  nlinarith

/-- Every bridge preserves the exact numerator/prefix/remainder certificate. -/
theorem bridge_preserves_identity {A D P Q r d t R : ℕ}
    (hvalue : D * Q + r = A * P) (hstep : R * r = D * d + t) :
    D * (R * Q + d) + t = A * (P * R) := by
  calc
    D * (R * Q + d) + t = R * (D * Q + r) := by nlinarith [hstep]
    _ = A * (P * R) := by rw [hvalue]; ring

/-- Rational prefix and residual keep their value at a changed radix. -/
theorem bridge_preserves_value {D P Q r d t R : ℕ}
    (hD : 0 < D) (hP : 0 < P) (hR : 0 < R)
    (hstep : R * r = D * d + t) :
    ((R * Q + d : ℕ) : ℚ) / (P * R) + (t : ℚ) / (D * (P * R)) =
      (Q : ℚ) / P + (r : ℚ) / (D * P) := by
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hp : (P : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have hb : (R : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  have he : (R : ℚ) * r = (D : ℚ) * d + t := by exact_mod_cast hstep
  push_cast
  field_simp
  nlinarith [he]

/-- A common divisor of the denominator and entering remainder persists. -/
theorem common_divisor_persists {g D r R : ℕ} (hgD : g ∣ D) (hgr : g ∣ r) :
    g ∣ R * r % D := by
  exact (Nat.dvd_mod_iff hgD).mpr (dvd_mul_of_dvd_right hgr R)

/-- At a fixed remainder t, the emitted positive digit e must satisfy t | D*e. -/
theorem return_requires_divisibility {D t e R : ℕ}
    (hstep : R * t = D * e + t) : t ∣ D * e := by
  have hsum : t ∣ D * e + t := by rw [← hstep]; exact dvd_mul_left t R
  exact (Nat.dvd_add_iff_left (dvd_refl t)).mpr hsum

def returnRadix (D t e : ℕ) : ℕ := D * e / t + 1

theorem return_step {D t e : ℕ} (hdiv : t ∣ D * e) :
    returnRadix D t e * t = D * e + t := by
  unfold returnRadix
  rw [Nat.add_mul, Nat.one_mul, Nat.div_mul_cancel hdiv]

theorem return_radix_valid {D t e : ℕ} (ht : 0 < t) (htD : t < D)
    (he : 0 < e) : 2 ≤ returnRadix D t e := by
  have hmul : t ≤ D * e := by nlinarith
  have hq : 1 ≤ D * e / t := (Nat.le_div_iff_mul_le ht).2 (by simpa using hmul)
  unfold returnRadix
  omega

theorem return_digit {D t e : ℕ} (htD : t < D) (hdiv : t ∣ D * e) :
    returnRadix D t e * t / D = e :=
  certified_digit htD (return_step hdiv)

theorem return_remainder {D t e : ℕ} (htD : t < D) (hdiv : t ∣ D * e) :
    returnRadix D t e * t % D = t :=
  certified_remainder htD (return_step hdiv)

theorem return_exists_iff {D t e : ℕ} (ht : 0 < t) (htD : t < D) (he : 0 < e) :
    (∃ R : ℕ, 2 ≤ R ∧ R * t = D * e + t) ↔ t ∣ D * e := by
  constructor
  · rintro ⟨R, _, hstep⟩
    exact return_requires_divisibility hstep
  · intro hdiv
    exact ⟨returnRadix D t e, return_radix_valid ht htD he, return_step hdiv⟩

/-- Known common factor H of the desired future digits specifies a reusable anchor. -/
def continuationRadix (D t H : ℕ) (u : ℕ → ℕ) (n : ℕ) : ℕ :=
  (D * H / t) * u n + 1

theorem continuation_step {D t H : ℕ} (hdiv : t ∣ D * H) (u : ℕ → ℕ) (n : ℕ) :
    continuationRadix D t H u n * t = D * (H * u n) + t := by
  have he := Nat.div_mul_cancel hdiv
  unfold continuationRadix
  nlinarith [he]

theorem continuation_valid {D t H : ℕ} (ht : 0 < t) (htD : t < D)
    (hH : 0 < H) (u : ℕ → ℕ) (hu : ∀ n, 0 < u n) :
    ValidRadices (continuationRadix D t H u) := by
  have hq : 1 ≤ D * H / t := (Nat.le_div_iff_mul_le ht).2 (by nlinarith)
  intro n
  unfold continuationRadix
  have := hu n
  nlinarith

theorem continuation_remainder {D t H : ℕ} (htD : t < D)
    (hdiv : t ∣ D * H) (u : ℕ → ℕ) (n : ℕ) :
    remainder (continuationRadix D t H u) t D n = t := by
  induction n with
  | zero => exact remainder_zero_of_lt _ htD
  | succ n ih =>
    rw [remainder_succ, ih]
    exact certified_remainder htD (continuation_step hdiv u n)

theorem continuation_digit {D t H : ℕ} (htD : t < D)
    (hdiv : t ∣ D * H) (u : ℕ → ℕ) (n : ℕ) :
    digit (continuationRadix D t H u) t D n = H * u n := by
  unfold digit
  rw [continuation_remainder htD hdiv]
  exact certified_digit htD (continuation_step hdiv u n)

theorem continuation_prefix_add_tail {D t H : ℕ} (ht : 0 < t) (htD : t < D)
    (hH : 0 < H) (hdiv : t ∣ D * H) (u : ℕ → ℕ) (hu : ∀ n, 0 < u n) (n : ℕ) :
    (digitPrefix (continuationRadix D t H u) t D n : ℚ) /
        placeProduct (continuationRadix D t H u) n +
      (t : ℚ) / (D * placeProduct (continuationRadix D t H u) n) = (t : ℚ) / D := by
  have hv := (exact_value _ (continuation_valid ht htD hH u hu) t D n (by omega)).symm
  simpa [continuation_remainder htD hdiv] using hv

/-- A one-step landing certificate includes the subsequent common-factor target. -/
def UsableLanding (D r d H t : ℕ) : Prop :=
  0 < t ∧ t < D ∧ t ∣ D * H ∧ r ∣ D * d + t ∧ 2 ≤ bridgeRadix D r d t

theorem usable_landing_iff {D r d H t : ℕ} (hr : 0 < r) :
    UsableLanding D r d H t ↔
      0 < t ∧ t < D ∧ t ∣ D * H ∧ ∃ R, 2 ≤ R ∧ R * r = D * d + t := by
  unfold UsableLanding
  rw [bridge_exists_iff hr]

theorem example_counting_bridge :
    UsableLanding 81 73 8 1 9 ∧ bridgeRadix 81 73 8 9 = 9 := by
  norm_num [UsableLanding, bridgeRadix]

theorem example_power_bridge :
    UsableLanding 997 729 729 2187 729 ∧ bridgeRadix 997 729 729 729 = 998 := by
  norm_num [UsableLanding, bridgeRadix]

theorem example_power_next :
    returnRadix 997 729 2187 = 2992 ∧ 2992 * 729 / 997 = 2187 ∧
      2992 * 729 % 997 = 729 := by norm_num [returnRadix]


/-- The smallest next radix that emits d with a strictly positive remainder. -/
def nextRadix (D r d : ℕ) : ℕ := D * d / r + 1

def nextRemainder (D r d : ℕ) : ℕ := r - (D * d % r)

theorem next_remainder_pos {D r d : ℕ} (hr : 0 < r) :
    0 < nextRemainder D r d := by
  have h := Nat.mod_lt (D * d) hr
  unfold nextRemainder
  omega

theorem next_remainder_le (D r d : ℕ) : nextRemainder D r d ≤ r :=
  Nat.sub_le _ _

theorem next_remainder_lt {D r d : ℕ} (hrD : r < D) :
    nextRemainder D r d < D := lt_of_le_of_lt (next_remainder_le D r d) hrD

theorem next_step {D r d : ℕ} (hr : 0 < r) :
    nextRadix D r d * r = D * d + nextRemainder D r d := by
  have hmod := Nat.mod_lt (D * d) hr
  have hdiv := Nat.mod_add_div (D * d) r
  have hsub := Nat.sub_add_cancel (Nat.le_of_lt hmod)
  unfold nextRadix nextRemainder
  nlinarith

theorem next_radix_valid {D r d : ℕ} (hr : 0 < r) (hrD : r < D) (hd : 0 < d) :
    2 ≤ nextRadix D r d := return_radix_valid hr hrD hd

theorem next_digit {D r d : ℕ} (hr : 0 < r) (hrD : r < D) :
    nextRadix D r d * r / D = d :=
  certified_digit (next_remainder_lt hrD) (next_step hr)

theorem next_remainder {D r d : ℕ} (hr : 0 < r) (hrD : r < D) :
    nextRadix D r d * r % D = nextRemainder D r d :=
  certified_remainder (next_remainder_lt hrD) (next_step hr)

theorem next_radix_minimal {D r d R t : ℕ} (hr : 0 < r) (ht : 0 < t)
    (hstep : R * r = D * d + t) : nextRadix D r d ≤ R := by
  have hlt : D * d < R * r := by omega
  have hq : D * d / r < R := (Nat.div_lt_iff_lt_mul hr).2 hlt
  unfold nextRadix
  omega

/-- Zero is possible with positive residual precisely when doubling r stays below D. -/
theorem zero_digit_exists_iff {D r : ℕ} (hr : 0 < r) :
    (∃ R t : ℕ, 2 ≤ R ∧ 0 < t ∧ t < D ∧ R * r = t) ↔ 2 * r < D := by
  constructor
  · rintro ⟨R, t, hR, _, htD, he⟩
    nlinarith
  · intro h
    exact ⟨2, 2 * r, by omega, by positivity, h, rfl⟩

def adaptiveRemainder (D r : ℕ) (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => r
  | n + 1 => nextRemainder D (adaptiveRemainder D r d n) (d n)

def adaptiveRadix (D r : ℕ) (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  nextRadix D (adaptiveRemainder D r d n) (d n)

theorem adaptive_remainder_pos {D r : ℕ} (hr : 0 < r) (d : ℕ → ℕ) (n : ℕ) :
    0 < adaptiveRemainder D r d n := by
  induction n with
  | zero => exact hr
  | succ n ih => exact next_remainder_pos ih

theorem adaptive_remainder_le {D r : ℕ} (d : ℕ → ℕ) (n : ℕ) :
    adaptiveRemainder D r d n ≤ r := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (next_remainder_le _ _ _) ih

theorem adaptive_remainder_antitone (D r : ℕ) (d : ℕ → ℕ) :
    Antitone (adaptiveRemainder D r d) := by
  apply antitone_nat_of_succ_le
  intro n
  exact next_remainder_le _ _ _

/-- The positive adaptive remainders descend only finitely often. No time bound is claimed. -/
theorem adaptive_remainder_eventually_constant (D r : ℕ) (d : ℕ → ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      adaptiveRemainder D r d n = adaptiveRemainder D r d N := by
  classical
  have hex : ∃ k : ℕ, ∃ n : ℕ, adaptiveRemainder D r d n = k :=
    ⟨adaptiveRemainder D r d 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hex
  refine ⟨N, fun n hn => ?_⟩
  have hlo := Nat.find_min' hex (show ∃ j, adaptiveRemainder D r d j =
    adaptiveRemainder D r d n from ⟨n, rfl⟩)
  have hhi := adaptive_remainder_antitone D r d hn
  omega

theorem adaptive_radices_valid {D r : ℕ} (hr : 0 < r) (hrD : r < D)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) : ValidRadices (adaptiveRadix D r d) := by
  intro n
  exact next_radix_valid (adaptive_remainder_pos hr d n)
    (lt_of_le_of_lt (adaptive_remainder_le d n) hrD) (hd n)

theorem adaptive_remainder_eq {D r : ℕ} (hr : 0 < r) (hrD : r < D)
    (d : ℕ → ℕ) (n : ℕ) :
    remainder (adaptiveRadix D r d) r D n = adaptiveRemainder D r d n := by
  induction n with
  | zero => exact remainder_zero_of_lt _ hrD
  | succ n ih =>
    rw [remainder_succ, ih]
    exact next_remainder (adaptive_remainder_pos hr d n)
      (lt_of_le_of_lt (adaptive_remainder_le d n) hrD)

theorem adaptive_digit_eq {D r : ℕ} (hr : 0 < r) (hrD : r < D)
    (d : ℕ → ℕ) (n : ℕ) : digit (adaptiveRadix D r d) r D n = d n := by
  unfold digit
  rw [adaptive_remainder_eq hr hrD]
  exact next_digit (adaptive_remainder_pos hr d n)
    (lt_of_le_of_lt (adaptive_remainder_le d n) hrD)

theorem adaptive_digit_legal {D r : ℕ} (hr : 0 < r) (hrD : r < D)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) (n : ℕ) : d n < adaptiveRadix D r d n := by
  have h := digit_lt (adaptiveRadix D r d) r n (D := D) (by omega)
    (by have := adaptive_radices_valid hr hrD d hd n; omega)
  simpa only [adaptive_digit_eq hr hrD] using h

theorem adaptive_prefix_add_tail {D r : ℕ} (hr : 0 < r) (hrD : r < D)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) (n : ℕ) :
    (digitPrefix (adaptiveRadix D r d) r D n : ℚ) /
        placeProduct (adaptiveRadix D r d) n +
      (adaptiveRemainder D r d n : ℚ) / (D * placeProduct (adaptiveRadix D r d) n) =
        (r : ℚ) / D := by
  have hv := (exact_value _ (adaptive_radices_valid hr hrD d hd) r D n (by omega)).symm
  simpa [adaptive_remainder_eq hr hrD] using hv

theorem adaptive_never_terminates {D r : ℕ} (hr : 0 < r) (hrD : r < D)
    (d : ℕ → ℕ) : ¬ EventuallyTerminates (adaptiveRadix D r d) r D := by
  rintro ⟨n, hn⟩
  change remainder (adaptiveRadix D r d) r D n = 0 at hn
  rw [adaptive_remainder_eq hr hrD] at hn
  have := adaptive_remainder_pos (D := D) hr d n
  omega

noncomputable def adaptiveTerm (D r : ℕ) (d : ℕ → ℕ) (n : ℕ) : ℝ :=
  (d n : ℝ) / (placeProduct (adaptiveRadix D r d) (n + 1) : ℝ)

noncomputable def adaptiveTail (D r : ℕ) (d : ℕ → ℕ) (n : ℕ) : ℝ :=
  (adaptiveRemainder D r d n : ℝ) / (D * placeProduct (adaptiveRadix D r d) n)

theorem adaptive_term_add_tail {D r : ℕ} (hr : 0 < r) (hrD : r < D)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) (n : ℕ) :
    adaptiveTerm D r d n + adaptiveTail D r d (n + 1) = adaptiveTail D r d n := by
  have hb := adaptive_radices_valid hr hrD d hd
  have hp : (placeProduct (adaptiveRadix D r d) n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (placeProduct_pos _ hb n))
  have hrad : (adaptiveRadix D r d n : ℝ) ≠ 0 := by
    exact_mod_cast (show adaptiveRadix D r d n ≠ 0 by have := hb n; omega)
  have hD : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have he : (adaptiveRadix D r d n : ℝ) * adaptiveRemainder D r d n =
      (D : ℝ) * d n + adaptiveRemainder D r d (n + 1) := by
    exact_mod_cast next_step (D := D) (d := d n) (adaptive_remainder_pos hr d n)
  unfold adaptiveTerm adaptiveTail
  rw [placeProduct_succ]
  push_cast
  field_simp
  nlinarith [he]

theorem adaptive_partialSum_add_tail {D r : ℕ} (hr : 0 < r) (hrD : r < D)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) (n : ℕ) :
    (∑ k ∈ Finset.range n, adaptiveTerm D r d k) + adaptiveTail D r d n = (r : ℝ) / D := by
  induction n with
  | zero => simp [adaptiveTail, adaptiveRemainder]
  | succ n ih =>
    rw [Finset.sum_range_succ, add_assoc, adaptive_term_add_tail hr hrD d hd, ih]

theorem adaptive_tail_tendsto_zero {D r : ℕ} (hr : 0 < r) (hrD : r < D)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    Tendsto (adaptiveTail D r d) atTop (𝓝 0) := by
  have hb := adaptive_radices_valid hr hrD d hd
  have ht := tendsto_inv_atTop_zero.comp (RadixRuns.placeProduct_tendsto_atTop _ hb)
  apply squeeze_zero (fun n => by unfold adaptiveTail; positivity) _ ht
  intro n
  have hp : (0 : ℝ) < placeProduct (adaptiveRadix D r d) n := by
    exact_mod_cast placeProduct_pos _ hb n
  have hD : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hrem : (adaptiveRemainder D r d n : ℝ) ≤ D := by
    exact_mod_cast (le_of_lt (lt_of_le_of_lt (adaptive_remainder_le d n) hrD))
  unfold adaptiveTail
  calc
    _ ≤ (D : ℝ) / (D * placeProduct (adaptiveRadix D r d) n) :=
      div_le_div_of_nonneg_right hrem (by positivity)
    _ = _ := by simp only [Function.comp_apply]; field_simp

theorem adaptive_hasSum {D r : ℕ} (hr : 0 < r) (hrD : r < D)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    HasSum (adaptiveTerm D r d) ((r : ℝ) / D) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by unfold adaptiveTerm; positivity) _).2
  have ht := (tendsto_const_nhds (x := (r : ℝ) / D)).sub
    (adaptive_tail_tendsto_zero hr hrD d hd)
  have he (n : ℕ) : (∑ k ∈ Finset.range n, adaptiveTerm D r d k) =
      (r : ℝ) / D - adaptiveTail D r d n := by
    have := adaptive_partialSum_add_tail hr hrD d hd n
    linarith
  simp only [he]
  simpa using ht

/-- Scaling the adaptive tail preserves any already-written prefix of A/D. -/
theorem adaptive_after_prefix_hasSum {A D P Q r : ℕ} (hr : 0 < r) (hrD : r < D)
    (hP : 0 < P) (hvalue : D * Q + r = A * P)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    HasSum (fun n => adaptiveTerm D r d n / (P : ℝ))
      ((A : ℝ) / D - (Q : ℝ) / P) := by
  have hs := (adaptive_hasSum hr hrD d hd).div_const (P : ℝ)
  have hD : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hp : (P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have hv : (D : ℝ) * Q + r = (A : ℝ) * P := by exact_mod_cast hvalue
  have he : ((r : ℝ) / D) / P = (A : ℝ) / D - (Q : ℝ) / P := by
    field_simp
    nlinarith [hv]
  simpa only [he] using hs

theorem example_greedy_counting :
    nextRadix 81 73 8 = 9 ∧ nextRemainder 81 73 8 = 9 ∧
      nextRadix 81 9 9 = 82 := by norm_num [nextRadix, nextRemainder]

theorem example_greedy_powers :
    nextRadix 997 729 729 = 998 ∧ nextRemainder 997 729 729 = 729 ∧
      nextRadix 997 729 2187 = 2992 := by norm_num [nextRadix, nextRemainder]

theorem example_greedy_998001 :
    nextRadix 998001 997003 998 = 999 ∧ nextRemainder 998001 997003 998 = 999 ∧
      nextRadix 998001 999 999 = 998002 := by norm_num [nextRadix, nextRemainder]

end HandoffSearch
