import RetainedProgression.Common

/-! Powers can keep growing while their remainders repeat. The quotient and
remainder together retain the whole power. This is the coefficient progression
`c^n`; its quotient need not be a prefix of a numeral in radix `B`.
-/
namespace RetainedProgression

def powerQuotient (c D n : ℕ) : ℕ := c ^ n / D

def powerRemainder (c D n : ℕ) : ℕ := c ^ n % D

def liftedState (c D n : ℕ) : ℕ × ℕ :=
  (powerQuotient c D n, powerRemainder c D n)

theorem power_state_identity (c D n : ℕ) :
    c ^ n = D * powerQuotient c D n + powerRemainder c D n := by
  simpa [powerQuotient, powerRemainder, Nat.add_comm] using
    (Nat.mod_add_div (c ^ n) D).symm

theorem powerRemainder_lt (c n : ℕ) {D : ℕ} (hD : 0 < D) :
    powerRemainder c D n < D := Nat.mod_lt _ hD

theorem powerRemainder_succ (c D n : ℕ) :
    powerRemainder c D (n + 1) = (c * powerRemainder c D n) % D := by
  simp [powerRemainder, pow_succ, Nat.mul_comm]

theorem powerQuotient_succ (c n : ℕ) {D : ℕ} (hD : 0 < D) :
    powerQuotient c D (n + 1) =
      c * powerQuotient c D n + (c * powerRemainder c D n) / D := by
  have hprev := congrArg (fun x : ℕ => c * x) (power_state_identity c D n)
  have hnext := power_state_identity c D (n + 1)
  have hstep := Nat.mod_add_div (c * powerRemainder c D n) D
  rw [← powerRemainder_succ] at hstep
  rw [pow_succ] at hnext
  nlinarith

theorem power_strictMono {c : ℕ} (hc : 2 ≤ c) :
    StrictMono (fun n : ℕ => c ^ n) :=
  pow_right_strictMono₀ (by omega)

theorem power_unbounded {c : ℕ} (hc : 2 ≤ c) (M : ℕ) :
    ∃ n : ℕ, M < c ^ n := by
  exact ⟨M, Nat.lt_pow_self (by omega)⟩

/-- The quotient can stay constant initially; it is nondecreasing. -/
theorem powerQuotient_monotone {c : ℕ} (hc : 2 ≤ c) (D : ℕ) :
    Monotone (powerQuotient c D) := by
  intro n m hnm
  exact Nat.div_le_div_right ((power_strictMono hc).monotone hnm)

theorem powerQuotient_unbounded {c D : ℕ} (hc : 2 ≤ c) (hD : 0 < D)
    (M : ℕ) : ∃ n : ℕ, M < powerQuotient c D n := by
  obtain ⟨n, hn⟩ := power_unbounded hc ((M + 1) * D)
  refine ⟨n, ?_⟩
  have hle : M + 1 ≤ c ^ n / D := (Nat.le_div_iff_mul_le hD).2 hn.le
  exact lt_of_lt_of_le (Nat.lt_succ_self M) hle

/-- Retaining both coordinates distinguishes all powers, even though the
remainder coordinate alone can return to an earlier value. -/
theorem liftedState_injective {c : ℕ} (hc : 2 ≤ c) (D : ℕ) :
    Function.Injective (liftedState c D) := by
  intro n m h
  apply (power_strictMono hc).injective
  change c ^ n = c ^ m
  have hq := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  change powerQuotient c D n = powerQuotient c D m at hq
  change powerRemainder c D n = powerRemainder c D m at hr
  rw [power_state_identity c D n, power_state_identity c D m, hq, hr]

/-- At two visits to the same remainder, the later quotient is strictly larger.
No positivity hypothesis on `D` is needed: a repeated remainder is impossible
when `D=0` and the powers are strictly increasing. -/
theorem quotient_lt_of_same_remainder {c : ℕ} (hc : 2 ≤ c)
    (D : ℕ) {n m : ℕ} (hnm : n < m)
    (hr : powerRemainder c D n = powerRemainder c D m) :
    powerQuotient c D n < powerQuotient c D m := by
  have hp := power_strictMono hc hnm
  change c ^ n < c ^ m at hp
  have hn := power_state_identity c D n
  have hm := power_state_identity c D m
  by_contra h
  have hle : powerQuotient c D m ≤ powerQuotient c D n := by omega
  have hmul := Nat.mul_le_mul_left D hle
  omega

/-- Exact amount retained in the quotient between equal remainder states. -/
theorem quotient_gap_of_same_remainder (c D n m : ℕ)
    (hr : powerRemainder c D n = powerRemainder c D m) :
    D * (powerQuotient c D m - powerQuotient c D n) = c ^ m - c ^ n := by
  rw [Nat.mul_sub_left_distrib]
  rw [power_state_identity c D m, power_state_identity c D n, hr]
  omega

/-- A return to remainder one reproduces every later remainder after the same
number of steps. The whole power and its quotient remain distinct. -/
theorem remainder_return (c D L n : ℕ)
    (hreturn : powerRemainder c D L = 1) :
    powerRemainder c D (n + L) = powerRemainder c D n := by
  change c ^ L % D = 1 at hreturn
  simp [powerRemainder, pow_add, Nat.mul_mod, hreturn]

/-- The quotient increment on a return is exactly `c^n * quotient(L)`. -/
theorem quotient_return (c L n : ℕ) {D : ℕ} (hD : 0 < D)
    (hreturn : powerRemainder c D L = 1) :
    powerQuotient c D (n + L) =
      powerQuotient c D n + c ^ n * powerQuotient c D L := by
  have hn := power_state_identity c D n
  have hL := congrArg (fun x : ℕ => c ^ n * x) (power_state_identity c D L)
  have hnL := power_state_identity c D (n + L)
  rw [hreturn] at hL
  rw [remainder_return c D L n hreturn, pow_add] at hnL
  nlinarith

theorem quotient_at_return_pos {c D L : ℕ} (hc : 2 ≤ c) (hL : 0 < L)
    (hreturn : powerRemainder c D L = 1) :
    0 < powerQuotient c D L := by
  have hp : 1 < c ^ L := by simpa using power_strictMono hc hL
  have hs := power_state_identity c D L
  rw [hreturn] at hs
  by_contra h
  have hzero : powerQuotient c D L = 0 := by omega
  simp [hzero] at hs
  omega

end RetainedProgression
