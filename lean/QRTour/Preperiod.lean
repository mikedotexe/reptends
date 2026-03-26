/- 
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Preperiod from Base-Factor Valuations

Claim ID: `preperiod_from_base_factors`

For a prime `p` dividing the base, the local preperiod contribution is the
least exponent `t` such that `base^t` absorbs the full `p`-part of the
denominator. In valuation language, this is the ceiling quotient

`⌈v_p(n) / v_p(base)⌉`.

This module formalizes that local statement. The full repo formula

`max_i ceil(v_{p_i}(N) / v_{p_i}(base))`

is then the maximum of these local step counts over the prime divisors of the
base.
-/

namespace QRTour

open scoped BigOperators

/-- The local preperiod contribution of the prime `p` to the denominator `n`
with respect to the base `base`. -/
def preperiodPrimeSteps (p base n : ℕ) : ℕ :=
  padicValNat p n ⌈/⌉ padicValNat p base

/-- The global preperiod step count: the maximum local ceiling quotient over the
prime support of the base. -/
def preperiodSteps (base n : ℕ) : ℕ :=
  base.primeFactors.sup fun p => preperiodPrimeSteps p base n

/-- The part of `n` supported on the prime factors of the base. -/
def basePrimeSupportFactor (base n : ℕ) : ℕ :=
  ∏ p ∈ base.primeFactors, p ^ padicValNat p n

private noncomputable def basePrimeSupportFactorization (base n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset base.primeFactors
    (fun p => if p ∈ base.primeFactors then padicValNat p n else 0)
    (by
      intro p hp
      by_cases hmem : p ∈ base.primeFactors
      · exact hmem
      · simp [hmem] at hp)

/-- Every local preperiod contribution is bounded by the global maximum. -/
theorem preperiodPrimeSteps_le_preperiodSteps {p base n : ℕ}
    (hp : p ∈ base.primeFactors) :
    preperiodPrimeSteps p base n ≤ preperiodSteps base n := by
  show preperiodPrimeSteps p base n ≤
      base.primeFactors.sup (fun q : ℕ => preperiodPrimeSteps q base n)
  exact Finset.le_sup (f := fun q : ℕ => preperiodPrimeSteps q base n) hp

/-- The local `p`-part of `n` is absorbed by `base^t` exactly when `t` is at
least the ceiling quotient `⌈v_p(n) / v_p(base)⌉`. -/
theorem preperiodPrimeSteps_le_iff {p base n t : ℕ} [hp : Fact p.Prime]
    (hbase_pos : 0 < base) (hdiv : p ∣ base) :
    preperiodPrimeSteps p base n ≤ t ↔ p ^ padicValNat p n ∣ base ^ t := by
  have hbase_ne : base ≠ 0 := Nat.ne_of_gt hbase_pos
  have hpow_ne : base ^ t ≠ 0 := pow_ne_zero t hbase_ne
  have hval_pos : 0 < padicValNat p base := by
    exact lt_of_lt_of_le zero_lt_one (one_le_padicValNat_of_dvd hbase_ne hdiv)
  rw [preperiodPrimeSteps]
  rw [padicValNat_dvd_iff_le hpow_ne, padicValNat.pow t hbase_ne, mul_comm]
  exact ceilDiv_le_iff_le_mul hval_pos

/-- At the local ceiling quotient, `base^t` already absorbs the full `p`-part
of the denominator. -/
theorem pow_padicValNat_dvd_base_pow_preperiodPrimeSteps {p base n : ℕ} [hp : Fact p.Prime]
    (hbase_pos : 0 < base) (hdiv : p ∣ base) :
    p ^ padicValNat p n ∣ base ^ preperiodPrimeSteps p base n :=
  (preperiodPrimeSteps_le_iff hbase_pos hdiv).mp le_rfl

/-- The ceiling quotient is the minimal local step count with that divisibility
property. -/
theorem preperiodPrimeSteps_minimal {p base n t : ℕ} [hp : Fact p.Prime]
    (hbase_pos : 0 < base) (hdiv : p ∣ base)
    (ht : p ^ padicValNat p n ∣ base ^ t) :
    preperiodPrimeSteps p base n ≤ t :=
  (preperiodPrimeSteps_le_iff hbase_pos hdiv).mpr ht

/-- At the global preperiod step count, every prime factor of the base already
absorbs the corresponding prime-power contribution from the denominator. -/
theorem pow_padicValNat_dvd_base_pow_preperiodSteps {p base n : ℕ} [hp : Fact p.Prime]
    (hbase_pos : 0 < base) (hmem : p ∈ base.primeFactors) :
    p ^ padicValNat p n ∣ base ^ preperiodSteps base n := by
  have hdiv : p ∣ base := Nat.dvd_of_mem_primeFactors (n := base) hmem
  exact
    (preperiodPrimeSteps_le_iff (p := p) hbase_pos hdiv).mp
      (preperiodPrimeSteps_le_preperiodSteps hmem)

/-- The global preperiod step count is the least `t` satisfying all local
prime-power divisibility constraints coming from the prime support of the base. -/
theorem preperiodSteps_le_of_local_bounds {base n t : ℕ}
    (hlocal : ∀ p ∈ base.primeFactors, p ^ padicValNat p n ∣ base ^ t) :
    preperiodSteps base n ≤ t := by
  refine Finset.sup_le ?_
  intro p hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hbase_pos : 0 < base := by
    apply Nat.pos_of_ne_zero
    intro hzero
    simp [hzero] at hp
  exact
    preperiodPrimeSteps_minimal (p := p) hbase_pos
      (Nat.dvd_of_mem_primeFactors (n := base) hp) (hlocal p hp)

private theorem basePrimeSupportFactorization_apply (base n p : ℕ) :
    basePrimeSupportFactorization base n p =
      if p ∈ base.primeFactors then padicValNat p n else 0 := by
  simp [basePrimeSupportFactorization]

private theorem basePrimeSupportFactorization_prod (base n : ℕ) :
    (basePrimeSupportFactorization base n).prod (· ^ ·) = basePrimeSupportFactor base n := by
  classical
  unfold basePrimeSupportFactorization
  rw [Finsupp.onFinset_prod]
  · refine Finset.prod_congr rfl ?_
    intro p hp
    simp [hp]
  · intro p
    simp

private theorem factorization_basePrimeSupportFactor (base n : ℕ) :
    (basePrimeSupportFactor base n).factorization = basePrimeSupportFactorization base n := by
  rw [← basePrimeSupportFactorization_prod]
  refine Nat.prod_pow_factorization_eq_self ?_
  intro p hp
  unfold basePrimeSupportFactorization at hp
  exact
    Nat.prime_of_mem_primeFactors
    ((Finsupp.support_onFinset_subset :
      (Finsupp.onFinset base.primeFactors
        (fun q => if q ∈ base.primeFactors then padicValNat q n else 0)
        (by
          intro q hq
          by_cases hmem : q ∈ base.primeFactors
          · exact hmem
          · simp [hmem] at hq)).support ⊆ base.primeFactors) hp)

/-- The base-supported prime-power factor is always positive. -/
theorem basePrimeSupportFactor_pos (base n : ℕ) :
    0 < basePrimeSupportFactor base n := by
  unfold basePrimeSupportFactor
  apply Nat.pos_of_ne_zero
  exact Finset.prod_ne_zero_iff.mpr fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- The base-supported prime-power factor divides the original denominator. -/
theorem basePrimeSupportFactor_dvd (base n : ℕ) :
    basePrimeSupportFactor base n ∣ n := by
  have hleft_ne : basePrimeSupportFactor base n ≠ 0 :=
    Nat.ne_of_gt (basePrimeSupportFactor_pos base n)
  by_cases hn : n = 0
  · simp [hn]
  · rw [← Nat.factorization_le_iff_dvd hleft_ne hn]
    intro q
    by_cases hq : q ∈ base.primeFactors
    · have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
      haveI : Fact q.Prime := ⟨hq_prime⟩
      have hlocal : q ^ padicValNat q n ∣ n := pow_padicValNat_dvd (p := q)
      have hle : padicValNat q n ≤ n.factorization q :=
        hq_prime.pow_dvd_iff_le_factorization hn |>.mp hlocal
      rw [factorization_basePrimeSupportFactor, basePrimeSupportFactorization_apply, if_pos hq]
      simpa using hle
    · rw [factorization_basePrimeSupportFactor, basePrimeSupportFactorization_apply, if_neg hq]
      exact Nat.zero_le _

/-- The base-supported prime-power part of `n` divides `base^preperiodSteps`. -/
theorem basePrimeSupportFactor_dvd_base_pow_preperiodSteps {base n : ℕ}
    (hbase_pos : 0 < base) :
    basePrimeSupportFactor base n ∣ base ^ preperiodSteps base n := by
  have hleft_ne : basePrimeSupportFactor base n ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hright_ne : base ^ preperiodSteps base n ≠ 0 := by
    exact pow_ne_zero _ (Nat.ne_of_gt hbase_pos)
  rw [← Nat.factorization_le_iff_dvd hleft_ne hright_ne,
    factorization_basePrimeSupportFactor, Nat.factorization_pow]
  intro q
  by_cases hq : q ∈ base.primeFactors
  · have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    haveI : Fact q.Prime := ⟨hq_prime⟩
    have hlocal :
        q ^ padicValNat q n ∣ base ^ preperiodSteps base n :=
      pow_padicValNat_dvd_base_pow_preperiodSteps (p := q) hbase_pos hq
    have hle :
        padicValNat q n ≤ (base ^ preperiodSteps base n).factorization q :=
      hq_prime.pow_dvd_iff_le_factorization hright_ne |>.mp hlocal
    rw [basePrimeSupportFactorization_apply, if_pos hq]
    simpa using hle
  · rw [basePrimeSupportFactorization_apply, if_neg hq]
    exact Nat.zero_le _

section Examples

example : preperiodPrimeSteps 2 10 996 = 2 := by native_decide

example : preperiodPrimeSteps 5 10 125 = 3 := by native_decide

example : preperiodSteps 10 996 = 2 := by native_decide

example : basePrimeSupportFactor 10 996 = 4 := by native_decide

end Examples

end QRTour
