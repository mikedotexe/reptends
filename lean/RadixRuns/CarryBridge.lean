import RadixRuns.Encoding

/-! A position-by-position bridge between uncarried coefficients and ordinary
digits. Indices start at zero: coefficient `a * c^n` belongs to position `n+1`.
The arithmetic statements need only a positive denominator; the intended
growing proper-fraction examples additionally have `a < D` and `2 ≤ c`.
The coefficient quotient is distinct from the accumulated digit prefix. -/
namespace RadixRuns

/-- The remainder at a zero-based index in any fixed radix. This is the
base-invariant jump used by the public digit-by-index tool. -/
theorem indexed_remainder_general (a D B n : ℕ) :
    RadixTermination.remainder (fun _ => B) a D n = (a * B ^ n) % D := by
  simp [RadixTermination.remainder, constant_placeProduct]

/-- Read one ordinary digit directly from its zero-based index. -/
theorem indexed_digit_general (a D B n : ℕ) :
    RadixTermination.digit (fun _ => B) a D n =
      B * ((a * B ^ n) % D) / D := by
  rw [RadixTermination.digit, indexed_remainder_general]

/-- Ordinary long division and the coefficient progression have the same
indexed remainder, for arbitrary numerator and growth factor. -/
theorem indexed_remainder (a D c n : ℕ) :
    RadixTermination.remainder (fun _ => D + c) a D n = (a * c ^ n) % D := by
  simp [RadixTermination.remainder, constant_placeProduct, Nat.mul_mod,
    Nat.pow_mod]

/-- An ordinary digit can be found from its index without generating the
preceding digits. -/
theorem indexed_digit (a D c n : ℕ) :
    RadixTermination.digit (fun _ => D + c) a D n =
      (D + c) * ((a * c ^ n) % D) / D := by
  rw [RadixTermination.digit, indexed_remainder]

/-- A general Euclidean-division identity. Writing it as a balance in natural
numbers avoids hiding a truncated subtraction inside the carry formula. -/
theorem quotient_remainder_carry {D : ℕ} (hD : 0 < D) (c x : ℕ) :
    (D + c) * (x % D) / D + (D + c) * (x / D) = x + c * x / D := by
  have hx : x = D * (x / D) + x % D := by
    simpa only [Nat.add_comm] using (Nat.mod_add_div x D).symm
  have hsplit : (D + c) * x =
      D * ((D + c) * (x / D)) + (D + c) * (x % D) := by
    calc
      (D + c) * x = (D + c) * (D * (x / D) + x % D) := by rw [← hx]
      _ = _ := by ring
  have hleft : (D + c) * x / D =
      (D + c) * (x / D) + (D + c) * (x % D) / D := by
    rw [hsplit, Nat.mul_add_div hD]
  have hright : (D + c) * x / D = x + c * x / D := by
    rw [show (D + c) * x = D * x + c * x by ring, Nat.mul_add_div hD]
  omega

/-- Full coefficient plus incoming carry equals the displayed digit plus
the carry transferred toward the preceding position. -/
theorem ordinary_digit_carry_balance {D : ℕ} (hD : 0 < D) (a c n : ℕ) :
    RadixTermination.digit (fun _ => D + c) a D n +
        (D + c) * (a * c ^ n / D) =
      a * c ^ n + a * c ^ (n + 1) / D := by
  rw [indexed_digit]
  simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    quotient_remainder_carry hD c (a * c ^ n)

/-- Integer packing of the original coefficients, before normalization. -/
theorem scaled_geometric_pack_balance (a D c n : ℕ) :
    a * (D + c) ^ n =
      D * packDigits (D + c) (fun j => a * c ^ j) n + a * c ^ n := by
  induction n with
  | zero => simp [packDigits]
  | succ n ih =>
    simp only [packDigits, pow_succ]
    calc
      a * ((D + c) ^ n * (D + c)) = (D + c) * (a * (D + c) ^ n) := by ring
      _ = _ := by rw [ih]; ring

/-- At any finite boundary, normalization adds exactly one quotient carry. -/
theorem scaled_geometric_pack_carry {D : ℕ} (hD : 0 < D) (a c n : ℕ) :
    a * (D + c) ^ n / D =
      packDigits (D + c) (fun j => a * c ^ j) n + a * c ^ n / D := by
  rw [scaled_geometric_pack_balance]
  exact Nat.mul_add_div hD _ _

/-- The carry bridge for complete finite prefixes of a proper fraction. -/
theorem ordinary_prefix_boundary_carry {D a : ℕ} (ha : a < D) (c n : ℕ) :
    packDigits (D + c) (RadixTermination.digit (fun _ => D + c) a D) n =
      packDigits (D + c) (fun j => a * c ^ j) n + a * c ^ n / D := by
  rw [packDigits_division_eq_prefix _ _ _ ha]
  simpa only [RadixTermination.digitPrefix, constant_placeProduct] using
    scaled_geometric_pack_carry (show 0 < D by omega) a c n

/-- Dividing the integer prefix bridge by its place scale makes the exact
weighted carry crossing the boundary explicit. -/
theorem ordinary_prefix_boundary_value {D a : ℕ} (ha : a < D) (c n : ℕ) :
    (packDigits (D + c) (RadixTermination.digit (fun _ => D + c) a D) n : ℚ) /
        (D + c : ℕ) ^ n =
      (packDigits (D + c) (fun j => a * c ^ j) n : ℚ) / (D + c : ℕ) ^ n +
        (a * c ^ n / D : ℕ) / (D + c : ℕ) ^ n := by
  rw [ordinary_prefix_boundary_carry ha]
  push_cast
  ring

theorem carry_bridge_997_first_overlap :
    RadixTermination.digit (fun _ => 1000) 1 997 6 = 731 ∧
      (3 : ℕ) ^ 6 / 997 = 0 ∧ (3 : ℕ) ^ 7 / 997 = 2 := by
  norm_num [RadixTermination.digit, RadixTermination.remainder, constant_placeProduct]

theorem carry_bridge_997_overflow :
    RadixTermination.digit (fun _ => 1000) 1 997 7 = 193 ∧
      (3 : ℕ) ^ 7 / 997 = 2 ∧ (3 : ℕ) ^ 8 / 997 = 6 ∧
      (193 : ℕ) + 1000 * 2 = 2187 + 6 := by
  norm_num [RadixTermination.digit, RadixTermination.remainder, constant_placeProduct]

theorem carry_bridge_997_return :
    RadixTermination.digit (fun _ => 1000) 1 997 166 = 1 ∧
      (3 : ℕ) ^ 166 % 997 = 1 := by
  change RadixTermination.digit (fun _ => 997 + 3) 1 997 166 = 1 ∧
    (3 : ℕ) ^ 166 % 997 = 1
  rw [indexed_digit]
  norm_num

end RadixRuns
