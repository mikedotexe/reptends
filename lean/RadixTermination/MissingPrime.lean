import RadixTermination.Common

/-! The actual least-missing-prime schedule, beginning with radix ten.
The zero-base fallback only makes the search function total; the radix sequence
is proved to stay at least two. No fraction is consulted by this definition. -/
namespace RadixTermination

theorem exists_prime_not_dvd (b : ℕ) (hb : 0 < b) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ b := by
  have hp : (Nat.minFac (b + 1)).Prime := Nat.minFac_prime (by omega)
  refine ⟨Nat.minFac (b + 1), hp, ?_⟩
  intro h
  have hsub := Nat.dvd_sub (Nat.minFac_dvd (b + 1)) h
  have hone : Nat.minFac (b + 1) ∣ 1 := by simpa using hsub
  exact hp.not_dvd_one hone

/-- The least prime absent from a positive base; the unused zero input returns two. -/
def smallestMissingPrime (b : ℕ) : ℕ :=
  if hb : 0 < b then Nat.find (exists_prime_not_dvd b hb) else 2

theorem smallestMissingPrime_spec {b : ℕ} (hb : 0 < b) :
    (smallestMissingPrime b).Prime ∧ ¬ smallestMissingPrime b ∣ b := by
  simpa [smallestMissingPrime, hb] using Nat.find_spec (exists_prime_not_dvd b hb)

theorem smallestMissingPrime_le {b p : ℕ} (hb : 0 < b)
    (hp : p.Prime) (hnot : ¬ p ∣ b) : smallestMissingPrime b ≤ p := by
  simpa [smallestMissingPrime, hb] using
    Nat.find_min' (exists_prime_not_dvd b hb) (show p.Prime ∧ ¬ p ∣ b from ⟨hp, hnot⟩)

/-- A missing prime is chosen if every smaller prime is already present. -/
theorem smallestMissingPrime_eq {b p : ℕ} (hb : 0 < b)
    (hp : p.Prime) (hnot : ¬ p ∣ b)
    (hsmall : ∀ q : ℕ, q.Prime → q < p → q ∣ b) :
    smallestMissingPrime b = p := by
  apply Nat.le_antisymm (smallestMissingPrime_le hb hp hnot)
  by_contra h
  have hlt : smallestMissingPrime b < p := by omega
  exact (smallestMissingPrime_spec hb).2
    (hsmall _ (smallestMissingPrime_spec hb).1 hlt)

theorem smallestMissingPrime_two_le (b : ℕ) : 2 ≤ smallestMissingPrime b := by
  by_cases hb : 0 < b
  · exact (smallestMissingPrime_spec hb).1.two_le
  · simp [smallestMissingPrime, hb]

def missingRadix : ℕ → ℕ
  | 0 => 10
  | n + 1 => missingRadix n * smallestMissingPrime (missingRadix n)

@[simp] theorem missingRadix_zero : missingRadix 0 = 10 := rfl

@[simp] theorem missingRadix_succ (n : ℕ) :
    missingRadix (n + 1) = missingRadix n * smallestMissingPrime (missingRadix n) := rfl

theorem missingRadix_valid : ValidRadices missingRadix := by
  intro n
  induction n with
  | zero => norm_num [missingRadix]
  | succ n ih =>
    rw [missingRadix_succ]
    have hp := smallestMissingPrime_two_le (missingRadix n)
    nlinarith

theorem missingRadix_pos (n : ℕ) : 0 < missingRadix n :=
  lt_of_lt_of_le (by decide : 0 < 2) (missingRadix_valid n)

theorem missingRadix_dvd_succ (n : ℕ) : missingRadix n ∣ missingRadix (n + 1) := by
  rw [missingRadix_succ]
  exact dvd_mul_right _ _

theorem missingRadix_dvd_of_le {i j : ℕ} (hij : i ≤ j) :
    missingRadix i ∣ missingRadix j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction k with
  | zero => simp
  | succ k ih =>
    exact dvd_trans ih (by simpa [Nat.add_assoc] using missingRadix_dvd_succ (i + k))

/-- By position `n`, all primes at most `n+2` have entered the radix. -/
theorem prime_dvd_missingRadix {p n : ℕ} (hp : p.Prime) (hle : p ≤ n + 2) :
    p ∣ missingRadix n := by
  induction n generalizing p with
  | zero =>
    have : p = 2 := by have := hp.two_le; omega
    subst p
    norm_num [missingRadix]
  | succ n ih =>
    by_cases hold : p ∣ missingRadix n
    · exact dvd_trans hold (missingRadix_dvd_succ n)
    · have hmin := smallestMissingPrime_le (missingRadix_pos n) hp hold
      have hspec := smallestMissingPrime_spec (missingRadix_pos n)
      have hbig : n + 2 < smallestMissingPrime (missingRadix n) := by
        by_contra h
        have hle' : smallestMissingPrime (missingRadix n) ≤ n + 2 := by omega
        exact hspec.2 (ih hspec.1 hle')
      have heq : p = smallestMissingPrime (missingRadix n) := by omega
      rw [missingRadix_succ, heq]
      exact dvd_mul_left _ _


/-- The first search skips the already present primes two and five. -/
theorem smallestMissingPrime_ten : smallestMissingPrime 10 = 3 := by
  apply smallestMissingPrime_eq (by norm_num) (by norm_num) (by norm_num)
  intro q hq hlt
  interval_cases q <;> norm_num at *

theorem smallestMissingPrime_thirty : smallestMissingPrime 30 = 7 := by
  apply smallestMissingPrime_eq (by norm_num) (by norm_num) (by norm_num)
  intro q hq hlt
  interval_cases q <;> norm_num at *

theorem smallestMissingPrime_210 : smallestMissingPrime 210 = 11 := by
  apply smallestMissingPrime_eq (by norm_num) (by norm_num) (by norm_num)
  intro q hq hlt
  interval_cases q <;> norm_num at *

@[simp] theorem missingRadix_one : missingRadix 1 = 30 := by
  norm_num [missingRadix, smallestMissingPrime_ten]

@[simp] theorem missingRadix_two : missingRadix 2 = 210 := by
  norm_num [missingRadix, smallestMissingPrime_ten, smallestMissingPrime_thirty]

@[simp] theorem missingRadix_three : missingRadix 3 = 2310 := by
  norm_num [missingRadix, smallestMissingPrime_ten,
    smallestMissingPrime_thirty, smallestMissingPrime_210]

theorem missingRadix_initial_values :
    missingRadix 0 = 10 ∧ missingRadix 1 = 30 ∧
    missingRadix 2 = 210 ∧ missingRadix 3 = 2310 := by
  norm_num [missingRadix, smallestMissingPrime_ten,
    smallestMissingPrime_thirty, smallestMissingPrime_210]

end RadixTermination
