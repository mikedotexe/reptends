import RadixTermination.MissingPrime
import RadixTermination.Consecutive

/-! Accumulating primes also accumulates their powers. This proves that the
actual least-missing-prime schedule covers each factorial, and therefore every
positive rational denominator. -/
namespace RadixTermination

/-- If every radix from position `s` contains `p`, then the first `n` radices
contain at least `n - s` copies of `p`. -/
theorem primePower_dvd_placeProduct_of_tail (b : ℕ → ℕ) (p s : ℕ)
    (h : ∀ i, s ≤ i → p ∣ b i) (n : ℕ) :
    p ^ (n - s) ∣ placeProduct b n := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hs : s ≤ n
    · have he : n + 1 - s = (n - s) + 1 := by omega
      rw [he, pow_succ, placeProduct_succ]
      exact Nat.mul_dvd_mul ih (h n hs)
    · have he : n + 1 - s = 0 := by omega
      simp [he]

/-- An elementary upper bound on the number of copies of a prime in a
factorial, in the form needed to compare with the radix tail. -/
theorem factorial_prime_exponent_le_tail {p n : ℕ} (hp : p.Prime)
    (hpn : p ≤ n + 1) :
    (n + 1).factorial.factorization p ≤ n - (p - 2) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hv : (p - 1) * (n + 1).factorial.factorization p < n + 1 := by
    rw [Nat.factorization_def _ hp]
    exact sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega)
  have hp2 := hp.two_le
  have ht : n - (p - 2) + (p - 2) = n := by omega
  have htpos : 1 ≤ n - (p - 2) := by omega
  have heq : p - 1 = (p - 2) + 1 := by omega
  rw [heq] at hv
  have hnonneg : 0 ≤ (p - 2) * (n - (p - 2) - 1) := Nat.zero_le _
  have htminus : n - (p - 2) - 1 + 1 = n - (p - 2) := by omega
  nlinarith

/-- Prime coverage by the corresponding position guarantees factorial
coverage in the accumulated place product. -/
theorem factorial_dvd_placeProduct_of_prime_coverage (b : ℕ → ℕ)
    (hcover : ∀ p i, p.Prime → p ≤ i + 2 → p ∣ b i) (n : ℕ) :
    (n + 1).factorial ∣ placeProduct b n := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
  intro p k hp hpk
  have hk : k ≤ (n + 1).factorial.factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).1 hpk
  by_cases hpn : p ≤ n + 1
  · have hbound := factorial_prime_exponent_le_tail hp hpn
    apply dvd_trans (pow_dvd_pow p (hk.trans hbound))
    apply primePower_dvd_placeProduct_of_tail b p (p - 2)
    intro i hi
    apply hcover p i hp
    have := hp.two_le
    omega
  · have hz : (n + 1).factorial.factorization p = 0 :=
      Nat.factorization_factorial_eq_zero_of_lt (by omega)
    have : k = 0 := by omega
    simp [this]

theorem factorial_dvd_missingPlaceProduct (n : ℕ) :
    (n + 1).factorial ∣ placeProduct missingRadix n := by
  apply factorial_dvd_placeProduct_of_prime_coverage
  intro p i hp hpi
  exact prime_dvd_missingRadix hp hpi

theorem consecutivePlaceProduct_dvd_missingPlaceProduct (n : ℕ) :
    placeProduct consecutive n ∣ placeProduct missingRadix n := by
  rw [placeProduct_consecutive]
  exact factorial_dvd_missingPlaceProduct n

theorem missingRadix_denominator_covered (D : ℕ) (hD : 0 < D) :
    D ∣ placeProduct missingRadix (D - 1) :=
  dvd_trans (consecutive_denominator_covered D hD)
    (consecutivePlaceProduct_dvd_missingPlaceProduct (D - 1))

theorem missingRadix_terminates_at (A D : ℕ) (hD : 0 < D) :
    TerminatesAt missingRadix A D (D - 1) :=
  terminatesAt_of_dvd missingRadix A D (D - 1)
    (missingRadix_denominator_covered D hD)

/-- The chosen schedule is independent of the fraction, but terminates every
fraction with positive denominator. -/
theorem missingRadix_terminates (A D : ℕ) (hD : 0 < D) :
    EventuallyTerminates missingRadix A D :=
  ⟨D - 1, missingRadix_terminates_at A D hD⟩

/-- Termination under consecutive radices implies
termination at the same position under least-missing-prime radices. -/
theorem missingRadix_terminatesAt_of_consecutive (A D n : ℕ)
    (h : TerminatesAt consecutive A D n) :
    TerminatesAt missingRadix A D n := by
  unfold TerminatesAt remainder at *
  apply Nat.mod_eq_zero_of_dvd
  exact dvd_trans (Nat.dvd_of_mod_eq_zero h)
    (Nat.mul_dvd_mul (dvd_refl A) (consecutivePlaceProduct_dvd_missingPlaceProduct n))

end RadixTermination
