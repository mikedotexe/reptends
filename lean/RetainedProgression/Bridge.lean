import RetainedProgression.Value
import RetainedProgression.Lift
import RadixTermination.Core

/-! Connections to ordinary division and to an arbitrary ambient numeral base.
The coefficient lift and the ordinary digit prefix share their remainders, but
their quotients concern different growing quantities (`c^n` and `B^n`).
-/
namespace RetainedProgression

theorem fixedRadix_placeProduct (B n : ℕ) :
    RadixTermination.placeProduct (fun _ => B) n = B ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [RadixTermination.placeProduct_succ, ih, pow_succ]

/-- The uncarried coefficient powers and ordinary block-radix division have
the same remainders, although their full values and quotients need not agree. -/
theorem ordinary_remainder_eq_powerRemainder {B D : ℕ} (hDB : D ≤ B) (n : ℕ) :
    RadixTermination.remainder (fun _ => B) 1 D n =
      powerRemainder (B - D) D n := by
  have hmod : B ≡ B - D [MOD D] :=
    (Nat.modEq_sub_modulus_iff hDB).2 (Nat.ModEq.refl B)
  simpa [RadixTermination.remainder, fixedRadix_placeProduct, powerRemainder] using
    hmod.pow n

/-- The ordinary digit prefix is the quotient of the place scale, not the
quotient of the retained coefficient power. -/
theorem ordinary_digitPrefix_eq (B D n : ℕ) :
    RadixTermination.digitPrefix (fun _ => B) 1 D n = B ^ n / D := by
  simp [RadixTermination.digitPrefix, fixedRadix_placeProduct]

/-- A scaled coefficient splits into quotient and remainder contributions.
When `0 < D < B` and `c = B-D`, the left side is the exact geometric tail, and the quotient
contribution is the carry into the existing prefix. -/
theorem coefficient_tail_split (B c D n : ℕ) (hB : 0 < B) (hD : 0 < D) :
    (c : ℝ) ^ n / ((D : ℝ) * (B : ℝ) ^ n) =
      (powerQuotient c D n : ℝ) / (B : ℝ) ^ n +
      (powerRemainder c D n : ℝ) / ((D : ℝ) * (B : ℝ) ^ n) := by
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have hp : (B : ℝ) ^ n ≠ 0 := pow_ne_zero _ hb
  have hs : (c : ℝ) ^ n = (D : ℝ) * (powerQuotient c D n : ℝ) +
      (powerRemainder c D n : ℝ) := by
    exact_mod_cast power_state_identity c D n
  field_simp
  nlinarith [hs]

theorem reciprocal_partialValue_add_tail {B D : ℕ} (hD : 0 < D)
    (hDB : D < B) (n : ℕ) :
    (geometric B (B - D)).partialValue n +
      ((B - D : ℕ) : ℝ) ^ n / ((D : ℝ) * (B : ℝ) ^ n) = 1 / (D : ℝ) := by
  have hcast : ((B - D : ℕ) : ℝ) = (B : ℝ) - D := Nat.cast_sub hDB.le
  simpa [hcast, div_pow, div_div, mul_comm] using
    partialValue_add_tail (show B - D < B by omega) n

/-- The coefficient quotient measures exactly the carry added to a finite
uncarried prefix to obtain the ordinary normalized digit prefix. -/
theorem ordinary_prefix_eq_partialValue_add_carry {B D : ℕ}
    (hD : 0 < D) (hDB : D < B) (n : ℕ) :
    (RadixTermination.digitPrefix (fun _ => B) 1 D n : ℝ) / (B : ℝ) ^ n =
      (geometric B (B - D)).partialValue n +
      (powerQuotient (B - D) D n : ℝ) / (B : ℝ) ^ n := by
  have hB : 0 < B := by omega
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have hp : (B : ℝ) ^ n ≠ 0 := pow_ne_zero _ hb
  have hn := RadixTermination.state_identity (fun _ => B) 1 D n
  rw [fixedRadix_placeProduct, Nat.one_mul,
    ordinary_remainder_eq_powerRemainder hDB.le n] at hn
  have hn' : (B : ℝ) ^ n =
      (D : ℝ) * (RadixTermination.digitPrefix (fun _ => B) 1 D n : ℝ) +
      (powerRemainder (B - D) D n : ℝ) := by exact_mod_cast hn
  have hnorm :
      (RadixTermination.digitPrefix (fun _ => B) 1 D n : ℝ) / (B : ℝ) ^ n +
      (powerRemainder (B - D) D n : ℝ) / ((D : ℝ) * (B : ℝ) ^ n) =
        1 / (D : ℝ) := by
    field_simp
    nlinarith [hn']
  have hpartial := reciprocal_partialValue_add_tail hD hDB n
  rw [coefficient_tail_split B (B - D) D n hB hD] at hpartial
  linarith

/-- A convenient block size for an arbitrary ambient radix. The exponent is
a conservative existence witness, not a claim of optimal grouping. -/
def blockRadix (b D : ℕ) : ℕ := b ^ (D + 1)

theorem linear_le_pow {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : n + 1 ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hm : 2 * b ^ n ≤ b * b ^ n := Nat.mul_le_mul_right _ hb
    nlinarith

theorem blockRadix_bound {b : ℕ} (hb : 2 ≤ b) (D : ℕ) :
    D + 2 ≤ blockRadix b D := by
  simpa [blockRadix, Nat.add_assoc] using linear_le_pow hb (D + 1)

theorem blockRadix_multiplier_two_le {b : ℕ} (hb : 2 ≤ b) (D : ℕ) :
    2 ≤ blockRadix b D - D := by
  have := blockRadix_bound hb D
  omega

theorem blockRadix_hasSum {b D : ℕ} (hb : 2 ≤ b) (hD : 0 < D) :
    HasSum (geometric (blockRadix b D) (blockRadix b D - D)).term (1 / (D : ℝ)) := by
  apply reciprocal_hasSum hD
  have := blockRadix_bound hb D
  omega

theorem blockRadix_value {b D : ℕ} (hb : 2 ≤ b) (hD : 0 < D) :
    (geometric (blockRadix b D) (blockRadix b D - D)).value = 1 / (D : ℝ) := by
  exact (blockRadix_hasSum hb hD).tsum_eq

theorem blockRadix_coefficients_strictMono {b : ℕ} (hb : 2 ≤ b) (D : ℕ) :
    StrictMono (geometric (blockRadix b D) (blockRadix b D - D)).coefficient :=
  power_strictMono (blockRadix_multiplier_two_le hb D)

theorem blockRadix_lift_injective {b : ℕ} (hb : 2 ≤ b) (D : ℕ) :
    Function.Injective (liftedState (blockRadix b D - D) D) :=
  liftedState_injective (blockRadix_multiplier_two_le hb D) D

/-- Every ambient base permits a retained expansion of each positive reciprocal
with strictly growing coefficients and an injective quotient/remainder lift. -/
theorem every_base_has_retained_progression (b D : ℕ) (hb : 2 ≤ b) (hD : 0 < D) :
    ∃ k : ℕ, 0 < k ∧ D + 2 ≤ b ^ k ∧
      HasSum (geometric (b ^ k) (b ^ k - D)).term (1 / (D : ℝ)) ∧
      StrictMono (geometric (b ^ k) (b ^ k - D)).coefficient ∧
      Function.Injective (liftedState (b ^ k - D) D) := by
  refine ⟨D + 1, by omega, blockRadix_bound hb D, ?_, ?_, ?_⟩
  · exact blockRadix_hasSum hb hD
  · exact blockRadix_coefficients_strictMono hb D
  · exact blockRadix_lift_injective hb D

end RetainedProgression
