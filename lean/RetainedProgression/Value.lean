import RetainedProgression.Common

/-! The geometric retained stream genuinely converges to its reciprocal value.
Finite prefixes leave an explicit positive tail, so no finite prefix exhausts
the expansion when the multiplier is positive. -/
namespace RetainedProgression

theorem geometric_term_eq (B c n : ℕ) :
    (geometric B c).term n = ((c : ℝ) / B) ^ n / B := by
  simp [Expansion.term, div_pow, div_div, pow_succ]

theorem geometric_hasSum {B c : ℕ} (hc : c < B) :
    HasSum (geometric B c).term (1 / ((B : ℝ) - c)) := by
  have hB : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlt : (c : ℝ) < B := by exact_mod_cast hc
  have hratio : (c : ℝ) / B < 1 := (div_lt_one hB).2 hlt
  have hnonneg : (0 : ℝ) ≤ (c : ℝ) / B := div_nonneg (Nat.cast_nonneg _) hB.le
  have hsum := (hasSum_geometric_of_lt_one hnonneg hratio).div_const (B : ℝ)
  have hBne := ne_of_gt hB
  have hdiff : (B : ℝ) - c ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
  have he : (1 - (c : ℝ) / B)⁻¹ / B = 1 / ((B : ℝ) - c) := by
    field_simp
  have hfun : (fun n : ℕ => ((c : ℝ) / B) ^ n / B) = (geometric B c).term := by
    funext n
    exact (geometric_term_eq B c n).symm
  simpa only [hfun, he] using hsum

theorem geometric_value {B c : ℕ} (hc : c < B) :
    (geometric B c).value = 1 / ((B : ℝ) - c) :=
  (geometric_hasSum hc).tsum_eq

theorem reciprocal_hasSum {B D : ℕ} (hD : 0 < D) (hDB : D < B) :
    HasSum (geometric B (B - D)).term (1 / (D : ℝ)) := by
  have hlt : B - D < B := by omega
  have hcast : ((B - D : ℕ) : ℝ) = (B : ℝ) - D :=
    Nat.cast_sub hDB.le
  simpa [hcast] using geometric_hasSum hlt

theorem reciprocal_value {B D : ℕ} (hD : 0 < D) (hDB : D < B) :
    (geometric B (B - D)).value = 1 / (D : ℝ) :=
  (reciprocal_hasSum hD hDB).tsum_eq

theorem partialValue_add_tail {B c : ℕ} (hc : c < B) (n : ℕ) :
    (geometric B c).partialValue n + ((c : ℝ) / B) ^ n / ((B : ℝ) - c) =
      1 / ((B : ℝ) - c) := by
  have hB : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlt : (c : ℝ) < B := by exact_mod_cast hc
  have hBne := ne_of_gt hB
  have hdiff : (B : ℝ) - c ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
  induction n with
  | zero => simp [Expansion.partialValue]
  | succ n ih =>
    have hstep : (geometric B c).term n +
        ((c : ℝ) / B) ^ (n + 1) / ((B : ℝ) - c) =
        ((c : ℝ) / B) ^ n / ((B : ℝ) - c) := by
      rw [geometric_term_eq, pow_succ]
      field_simp
      ring
    unfold Expansion.partialValue at *
    rw [Finset.sum_range_succ, add_assoc, hstep, ih]

theorem geometric_term_pos {B c : ℕ} (hcpos : 0 < c) (hc : c < B) (n : ℕ) :
    0 < (geometric B c).term n := by
  have hB : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hc' : (0 : ℝ) < c := by exact_mod_cast hcpos
  rw [geometric_term_eq]
  positivity

theorem partialValue_strictMono {B c : ℕ} (hcpos : 0 < c) (hc : c < B) :
    StrictMono (geometric B c).partialValue := by
  apply strictMono_nat_of_lt_succ
  intro n
  unfold Expansion.partialValue
  rw [Finset.sum_range_succ]
  exact lt_add_of_pos_right _ (geometric_term_pos hcpos hc n)

theorem partialValue_lt_value {B c : ℕ} (hcpos : 0 < c) (hc : c < B) (n : ℕ) :
    (geometric B c).partialValue n < (geometric B c).value := by
  have hB : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hc' : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hlt : (c : ℝ) < B := by exact_mod_cast hc
  have htail : (0 : ℝ) < ((c : ℝ) / B) ^ n / ((B : ℝ) - c) := by
    exact div_pos (pow_pos (div_pos hc' hB) _) (sub_pos.mpr hlt)
  rw [geometric_value hc, ← partialValue_add_tail hc n]
  exact lt_add_of_pos_right _ htail

theorem geometric_term_strictAnti {B c : ℕ} (hcpos : 0 < c) (hc : c < B) :
    StrictAnti (geometric B c).term := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have hB : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlt : (c : ℝ) < B := by exact_mod_cast hc
  have hratio : (c : ℝ) / B < 1 := (div_lt_one hB).2 hlt
  have hn := geometric_term_pos hcpos hc n
  have he : (geometric B c).term (n + 1) =
      (geometric B c).term n * ((c : ℝ) / B) := by
    simp only [geometric_term_eq, pow_succ]
    ring
  rw [he]
  exact mul_lt_of_lt_one_right hn hratio

end RetainedProgression
