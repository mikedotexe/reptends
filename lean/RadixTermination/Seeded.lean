import RadixTermination.Coverage

/-! Least-missing-prime radices from any starting radix at least two.
The termination guarantee does not depend on choosing decimal as the seed. -/
namespace RadixTermination

/-- Start with `seed`, then multiply by the least prime absent from the current radix. -/
def seededRadix (seed : ℕ) : ℕ → ℕ
  | 0 => seed
  | n + 1 => seededRadix seed n * smallestMissingPrime (seededRadix seed n)

@[simp] theorem seededRadix_zero (seed : ℕ) : seededRadix seed 0 = seed := rfl

@[simp] theorem seededRadix_succ (seed n : ℕ) :
    seededRadix seed (n + 1) =
      seededRadix seed n * smallestMissingPrime (seededRadix seed n) := rfl

theorem seededRadix_valid {seed : ℕ} (hseed : 2 ≤ seed) :
    ValidRadices (seededRadix seed) := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    rw [seededRadix_succ]
    have hp := smallestMissingPrime_two_le (seededRadix seed n)
    nlinarith

theorem seededRadix_pos {seed : ℕ} (hseed : 2 ≤ seed) (n : ℕ) :
    0 < seededRadix seed n :=
  lt_of_lt_of_le (by decide : 0 < 2) (seededRadix_valid hseed n)

theorem seededRadix_dvd_succ (seed n : ℕ) :
    seededRadix seed n ∣ seededRadix seed (n + 1) := by
  rw [seededRadix_succ]
  exact dvd_mul_right _ _

theorem seededRadix_dvd_of_le (seed : ℕ) {i j : ℕ} (hij : i ≤ j) :
    seededRadix seed i ∣ seededRadix seed j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction k with
  | zero => simp
  | succ k ih =>
    exact dvd_trans ih (by simpa [Nat.add_assoc] using seededRadix_dvd_succ seed (i + k))

@[simp] theorem seededRadix_ten (n : ℕ) : seededRadix 10 n = missingRadix n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [seededRadix_succ, missingRadix_succ, ih]

/-- The uniform bound allows an arbitrary initial radix, including odd seeds. -/
theorem prime_dvd_seededRadix {seed p n : ℕ} (hseed : 2 ≤ seed)
    (hp : p.Prime) (hle : p ≤ n + 1) : p ∣ seededRadix seed n := by
  induction n generalizing p with
  | zero => have := hp.two_le; omega
  | succ n ih =>
    by_cases hold : p ∣ seededRadix seed n
    · exact dvd_trans hold (seededRadix_dvd_succ seed n)
    · have hmin := smallestMissingPrime_le (seededRadix_pos hseed n) hp hold
      have hspec := smallestMissingPrime_spec (seededRadix_pos hseed n)
      have hbig : n + 1 < smallestMissingPrime (seededRadix seed n) := by
        by_contra h
        have hle' : smallestMissingPrime (seededRadix seed n) ≤ n + 1 := by omega
        exact hspec.2 (ih hspec.1 hle')
      have heq : p = smallestMissingPrime (seededRadix seed n) := by omega
      rw [seededRadix_succ, heq]
      exact dvd_mul_left _ _

/-- Separate the initial radix from the product of the remaining radices. -/
theorem placeProduct_eq_first_mul_tail (b : ℕ → ℕ) (n : ℕ) :
    placeProduct b (n + 1) = b 0 * placeProduct (fun i => b (i + 1)) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [placeProduct_succ, ih, placeProduct_succ]
    exact Nat.mul_assoc _ _ _

theorem tailPlaceProduct_dvd_placeProduct (b : ℕ → ℕ) (n : ℕ) :
    placeProduct (fun i => b (i + 1)) n ∣ placeProduct b (n + 1) := by
  rw [placeProduct_eq_first_mul_tail]
  exact dvd_mul_left _ _

theorem factorial_dvd_seededPlaceProduct {seed : ℕ} (hseed : 2 ≤ seed) (n : ℕ) :
    (n + 1).factorial ∣ placeProduct (seededRadix seed) (n + 1) := by
  apply dvd_trans _ (tailPlaceProduct_dvd_placeProduct (seededRadix seed) n)
  apply factorial_dvd_placeProduct_of_prime_coverage
  intro p i hp hpi
  exact prime_dvd_seededRadix hseed hp (by omega)

theorem seededRadix_denominator_covered {seed : ℕ} (hseed : 2 ≤ seed)
    (D : ℕ) (hD : 0 < D) : D ∣ placeProduct (seededRadix seed) D := by
  have hfact : D.factorial ∣ placeProduct (seededRadix seed) D := by
    simpa [Nat.sub_add_cancel hD] using factorial_dvd_seededPlaceProduct hseed (D - 1)
  exact dvd_trans (Nat.dvd_factorial hD le_rfl) hfact

/-- A conservative bound: at most `D` fractional positions for any seed at least two. -/
theorem seededRadix_terminates_at {seed : ℕ} (hseed : 2 ≤ seed)
    (A D : ℕ) (hD : 0 < D) : TerminatesAt (seededRadix seed) A D D :=
  terminatesAt_of_dvd (seededRadix seed) A D D
    (seededRadix_denominator_covered hseed D hD)

theorem seededRadix_terminates {seed : ℕ} (hseed : 2 ≤ seed)
    (A D : ℕ) (hD : 0 < D) : EventuallyTerminates (seededRadix seed) A D :=
  ⟨D, seededRadix_terminates_at hseed A D hD⟩

end RadixTermination
