/- 
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.Visibility
import QRTour.Preperiod
import Mathlib.Tactic

/-!
# Composite Visibility Families

This module packages the family-level visibility comparison between an actual
denominator and its stripped periodic core.

The arithmetic content is deliberately modest and exact:

- `Preperiod` supplies the base-supported factor that is absorbed by the
  preperiod,
- `Visibility` supplies the generic same-`B`, same-`k` threshold-shift laws, and
- this module connects the two layers for actual/core coordinates chosen in the
  same block base, including exact quotient-scaling and near-denominator
  coordinate-selection criteria.

It does not claim a global lookahead formula, and it does not touch the open
carry/DFA factorization frontier.
-/

namespace QRTour

/-- Endpoint labels for the same-core threshold interval law. `exact` is the
collapsed power case, while `lower` and `upper` distinguish the two non-power
interval endpoints. -/
inductive ThresholdShiftEndpoint
  | exact
  | lower
  | upper
  deriving DecidableEq, Repr

/-- The purely periodic core obtained by stripping the base-supported factor
from `n`. -/
def strippedPeriodModulus (base n : ℕ) : ℕ :=
  n / basePrimeSupportFactor base n

/-- The stripped factor times the stripped modulus reconstructs the denominator. -/
theorem basePrimeSupportFactor_mul_strippedPeriodModulus (base n : ℕ) :
    basePrimeSupportFactor base n * strippedPeriodModulus base n = n := by
  unfold strippedPeriodModulus
  exact Nat.mul_div_cancel' (basePrimeSupportFactor_dvd base n)

/-- The stripped periodic core is positive for positive denominators. -/
theorem strippedPeriodModulus_pos {base n : ℕ} (hn : 0 < n) :
    0 < strippedPeriodModulus base n := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hmul := basePrimeSupportFactor_mul_strippedPeriodModulus base n
  rw [hzero, Nat.mul_zero] at hmul
  omega

/-- The block coordinate attached to the full denominator `n`. -/
def actualCoordinate (base n stride : ℕ) (hn : 0 < n) : BlockCoordinate :=
  { base := base, modulus := n, stride := stride, modulus_pos := hn }

/-- The block coordinate attached to the stripped periodic core of `n`. -/
def strippedCoordinate (base n stride : ℕ) (hn : 0 < n) : BlockCoordinate :=
  { base := base
    modulus := strippedPeriodModulus base n
    stride := stride
    modulus_pos := strippedPeriodModulus_pos hn }

/-- A same-core-compatible coordinate is one where the stride has already
absorbed the base-supported factor and the visible remainder sits below the
stripped periodic core. This is the exact finite hypothesis needed for the
actual and stripped-core coordinates to share the same `k`. -/
def sameCoreCompatible (base n stride : ℕ) (hn : 0 < n) : Prop :=
  preperiodSteps base n ≤ stride ∧
    (actualCoordinate base n stride hn).remainderK < strippedPeriodModulus base n

theorem sameCoreCompatible_iff
    {base n stride : ℕ} {hn : 0 < n} :
    sameCoreCompatible base n stride hn ↔
      preperiodSteps base n ≤ stride ∧
        (actualCoordinate base n stride hn).remainderK < strippedPeriodModulus base n := by
  rfl

/-- Once the stride reaches the preperiod step count, the base-supported factor
already divides the block base. -/
theorem basePrimeSupportFactor_dvd_blockBase_of_preperiodSteps_le
    {base n stride : ℕ}
    (hbase_pos : 0 < base)
    (hstride : preperiodSteps base n ≤ stride) :
    basePrimeSupportFactor base n ∣ base ^ stride := by
  exact dvd_trans
    (basePrimeSupportFactor_dvd_base_pow_preperiodSteps (base := base) (n := n) hbase_pos)
    (pow_dvd_pow base hstride)

/-- The stripped periodic core is no larger than the original denominator. -/
theorem strippedPeriodModulus_le (base n : ℕ) :
    strippedPeriodModulus base n ≤ n := by
  unfold strippedPeriodModulus
  exact Nat.div_le_self _ _

/-- If the actual denominator is a good mode, then so is its stripped core. -/
theorem strippedCoordinate_goodMode_of_actual_goodMode
    {base n stride : ℕ}
    (hn : 0 < n)
    (hgood : (actualCoordinate base n stride hn).goodMode) :
    (strippedCoordinate base n stride hn).goodMode := by
  change strippedPeriodModulus base n < base ^ stride
  exact lt_of_le_of_lt (strippedPeriodModulus_le base n)
    (by simpa [actualCoordinate, BlockCoordinate.goodMode] using hgood)

/-- In a same-core-compatible coordinate, the base-supported factor divides the
block base. -/
theorem sameCoreCompatible_basePrimeSupportFactor_dvd_blockBase
    {base n stride : ℕ} {hn : 0 < n}
    (hbase_pos : 0 < base)
    (hcompat : sameCoreCompatible base n stride hn) :
    basePrimeSupportFactor base n ∣ (actualCoordinate base n stride hn).blockBase := by
  simpa [actualCoordinate, BlockCoordinate.blockBase] using
    basePrimeSupportFactor_dvd_blockBase_of_preperiodSteps_le
      (base := base) (n := n) (stride := stride) hbase_pos hcompat.1

/-- In a same-core-compatible coordinate, the visible remainder is itself a
multiple of the base-supported factor. -/
theorem sameCoreCompatible_basePrimeSupportFactor_dvd_remainderK
    {base n stride : ℕ} {hn : 0 < n}
    (hbase_pos : 0 < base)
    (hcompat : sameCoreCompatible base n stride hn) :
    basePrimeSupportFactor base n ∣ (actualCoordinate base n stride hn).remainderK := by
  have hdivN : basePrimeSupportFactor base n ∣ n := basePrimeSupportFactor_dvd base n
  have hdivB :
      basePrimeSupportFactor base n ∣ (actualCoordinate base n stride hn).blockBase :=
    sameCoreCompatible_basePrimeSupportFactor_dvd_blockBase hbase_pos hcompat
  unfold actualCoordinate BlockCoordinate.remainderK BlockCoordinate.blockBase
  exact (Nat.dvd_mod_iff hdivN).2 hdivB

/-- Generic helper: if one modulus is a multiple of another and the smaller
remainder window is respected, the two coordinates share the same remainder. -/
theorem BlockCoordinate.remainderK_eq_of_modulus_eq_mul_and_remainder_lt
    {actual core : BlockCoordinate} {factor : ℕ}
    (hsharedB : actual.blockBase = core.blockBase)
    (hmod : actual.modulus = factor * core.modulus)
    (hrem : actual.remainderK < core.modulus) :
    core.remainderK = actual.remainderK := by
  have hactual :
      actual.quotientQ * actual.modulus + actual.remainderK = actual.blockBase := by
    unfold BlockCoordinate.quotientQ BlockCoordinate.remainderK
    simpa [Nat.mul_comm] using (Nat.div_add_mod actual.blockBase actual.modulus)
  calc
    core.remainderK = core.blockBase % core.modulus := rfl
    _ = actual.blockBase % core.modulus := by rw [hsharedB]
    _ = (actual.quotientQ * actual.modulus + actual.remainderK) % core.modulus := by
          rw [← hactual]
    _ = (actual.quotientQ * (factor * core.modulus) + actual.remainderK) % core.modulus := by
          rw [hmod]
    _ = actual.remainderK := by
          rw [show actual.quotientQ * (factor * core.modulus) =
              (actual.quotientQ * factor) * core.modulus by ac_rfl]
          rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hrem]

/-- Generic helper: under the same hypotheses, the quotient scales by the
modulus ratio. -/
theorem BlockCoordinate.quotientQ_eq_mul_of_modulus_eq_mul_and_remainder_lt
    {actual core : BlockCoordinate} {factor : ℕ}
    (hsharedB : actual.blockBase = core.blockBase)
    (hmod : actual.modulus = factor * core.modulus)
    (hrem : actual.remainderK < core.modulus)
    (hcore_pos : 0 < core.modulus) :
    core.quotientQ = actual.quotientQ * factor := by
  have hremEq :
      core.remainderK = actual.remainderK :=
    actual.remainderK_eq_of_modulus_eq_mul_and_remainder_lt hsharedB hmod hrem
  have hactual :
      actual.quotientQ * actual.modulus + actual.remainderK = actual.blockBase := by
    unfold BlockCoordinate.quotientQ BlockCoordinate.remainderK
    simpa [Nat.mul_comm] using (Nat.div_add_mod actual.blockBase actual.modulus)
  have hcore :
      core.quotientQ * core.modulus + core.remainderK = core.blockBase := by
    unfold BlockCoordinate.quotientQ BlockCoordinate.remainderK
    simpa [Nat.mul_comm] using (Nat.div_add_mod core.blockBase core.modulus)
  have hsum :
      core.quotientQ * core.modulus + actual.remainderK =
        (actual.quotientQ * factor) * core.modulus + actual.remainderK := by
    calc
      core.quotientQ * core.modulus + actual.remainderK
        = core.quotientQ * core.modulus + core.remainderK := by rw [hremEq]
      _ = core.blockBase := hcore
      _ = actual.blockBase := hsharedB.symm
      _ = actual.quotientQ * actual.modulus + actual.remainderK := by rw [← hactual]
      _ = (actual.quotientQ * factor) * core.modulus + actual.remainderK := by
            rw [hmod]
            ac_rfl
  have hmul :
      core.quotientQ * core.modulus = (actual.quotientQ * factor) * core.modulus :=
    Nat.add_right_cancel hsum
  exact Nat.eq_of_mul_eq_mul_right hcore_pos hmul

/-- The stripped core shares the same remainder `k` whenever the actual
remainder already lies below the stripped modulus. -/
theorem strippedCoordinate_remainderK_eq_of_remainder_lt
    {base n stride : ℕ}
    (hn : 0 < n)
    (hrem : (actualCoordinate base n stride hn).remainderK < strippedPeriodModulus base n) :
    (strippedCoordinate base n stride hn).remainderK =
      (actualCoordinate base n stride hn).remainderK := by
  exact
    (actualCoordinate base n stride hn).remainderK_eq_of_modulus_eq_mul_and_remainder_lt
      (hsharedB := rfl)
      (hmod := by
        simpa [actualCoordinate, strippedCoordinate, strippedPeriodModulus] using
          (basePrimeSupportFactor_mul_strippedPeriodModulus base n).symm)
      hrem

/-- Under the same remainder hypothesis, the stripped-core quotient is the
actual quotient scaled by the base-supported factor. -/
theorem strippedCoordinate_quotientQ_eq_of_remainder_lt
    {base n stride : ℕ}
    (hn : 0 < n)
    (hrem : (actualCoordinate base n stride hn).remainderK < strippedPeriodModulus base n) :
    (strippedCoordinate base n stride hn).quotientQ =
      (actualCoordinate base n stride hn).quotientQ * basePrimeSupportFactor base n := by
  exact
    (actualCoordinate base n stride hn).quotientQ_eq_mul_of_modulus_eq_mul_and_remainder_lt
      (hsharedB := rfl)
      (hmod := by
        simpa [actualCoordinate, strippedCoordinate, strippedPeriodModulus] using
          (basePrimeSupportFactor_mul_strippedPeriodModulus base n).symm)
      hrem
      (strippedPeriodModulus_pos hn)

/-- The visible remainder equality packaged through the same-core-compatible
predicate. -/
theorem sameCoreCompatible_remainderK_eq
    {base n stride : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn) :
    (strippedCoordinate base n stride hn).remainderK =
      (actualCoordinate base n stride hn).remainderK := by
  exact strippedCoordinate_remainderK_eq_of_remainder_lt hn hcompat.2

/-- The quotient scaling packaged through the same-core-compatible predicate. -/
theorem sameCoreCompatible_quotientQ_eq
    {base n stride : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn) :
    (strippedCoordinate base n stride hn).quotientQ =
      (actualCoordinate base n stride hn).quotientQ * basePrimeSupportFactor base n := by
  exact strippedCoordinate_quotientQ_eq_of_remainder_lt hn hcompat.2

/-- In same-core-compatible coordinates, each stripped-core raw coefficient is
the actual raw coefficient scaled by the base-supported factor. -/
theorem sameCoreCompatible_rawCoefficient_eq
    {base n stride j : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn) :
    (strippedCoordinate base n stride hn).rawCoefficient j =
      basePrimeSupportFactor base n * (actualCoordinate base n stride hn).rawCoefficient j := by
  unfold BlockCoordinate.rawCoefficient
  rw [sameCoreCompatible_quotientQ_eq hcompat, sameCoreCompatible_remainderK_eq hcompat]
  ac_rfl

/-- In the exact `k`-power same-core regime, the stripped-core raw coefficient
at `j` is literally the actual raw coefficient at `j + s`. -/
theorem sameCoreCompatible_rawCoefficient_shift_exact
    {base n stride s j : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (strippedCoordinate base n stride hn).rawCoefficient j =
      (actualCoordinate base n stride hn).rawCoefficient (j + s) := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  calc
    core.rawCoefficient j
      = basePrimeSupportFactor base n * actual.rawCoefficient j := by
          simpa [actual, core] using
            sameCoreCompatible_rawCoefficient_eq
              (base := base) (n := n) (stride := stride) (j := j) (hn := hn) hcompat
    _ = actual.remainderK ^ s * actual.rawCoefficient j := by rw [hfactor]
    _ = actual.remainderK ^ s * (actual.quotientQ * actual.remainderK ^ j) := by
          rw [BlockCoordinate.rawCoefficient]
    _ = actual.quotientQ * actual.remainderK ^ (j + s) := by
          rw [show actual.remainderK ^ (j + s) =
              actual.remainderK ^ j * actual.remainderK ^ s by rw [Nat.pow_add]]
          ac_rfl
    _ = actual.rawCoefficient (j + s) := by rw [BlockCoordinate.rawCoefficient]

/-- Canonical carried output at a position, computed from the infinite-tail
incoming carry rather than from a finite trace. This is the arithmetic payload
that finite state-alignment rows expose once their carry states are certified. -/
def BlockCoordinate.canonicalCarryBlockValue (C : BlockCoordinate) (j : ℕ) : ℕ :=
  (C.rawCoefficient j + C.incomingCarry j) % C.blockBase

/-- At position `1`, the canonical infinite-tail carry is the quotient of
`k^2` by the modulus. This is a small arithmetic normal form used by the
same-position obstruction family. -/
theorem BlockCoordinate.incomingCarry_one_eq_remainderK_sq_div_modulus
    (C : BlockCoordinate) (hgood : C.goodMode) :
    C.incomingCarry 1 = C.remainderK ^ 2 / C.modulus := by
  have hq : 0 < C.quotientQ := C.quotientQ_pos_of_goodMode hgood
  have hden : C.blockBase - C.remainderK = C.quotientQ * C.modulus := by
    rw [← C.quotientQ_mul_modulus_eq_blockBase_sub_remainderK]
  unfold BlockCoordinate.incomingCarry BlockCoordinate.rawCoefficient
  rw [hden]
  ring_nf
  exact Nat.mul_div_mul_left (C.remainderK ^ 2) C.modulus hq

/-- At position `2`, the canonical infinite-tail carry is the quotient of
`k^3` by the modulus. -/
theorem BlockCoordinate.incomingCarry_two_eq_remainderK_cu_div_modulus
    (C : BlockCoordinate) (hgood : C.goodMode) :
    C.incomingCarry 2 = C.remainderK ^ 3 / C.modulus := by
  have hq : 0 < C.quotientQ := C.quotientQ_pos_of_goodMode hgood
  have hden : C.blockBase - C.remainderK = C.quotientQ * C.modulus := by
    rw [← C.quotientQ_mul_modulus_eq_blockBase_sub_remainderK]
  unfold BlockCoordinate.incomingCarry BlockCoordinate.rawCoefficient
  rw [hden]
  ring_nf
  exact Nat.mul_div_mul_left (C.remainderK ^ 3) C.modulus hq

/-- Same-position idempotent-remainder obstruction hook.

If the remainder `k` is idempotent modulo the modulus, then canonical carried
outputs at positions `1` and `2` agree. Finite examples still need certified
state-alignment rows to connect these canonical carries to the displayed
finite trace. -/
theorem BlockCoordinate.samePositionIdempotent_hiddenCarryBlockValue
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hidempotent : C.remainderK * C.remainderK % C.modulus = C.remainderK) :
    C.canonicalCarryBlockValue 1 = C.canonicalCarryBlockValue 2 := by
  let k := C.remainderK
  let N := C.modulus
  let q := C.quotientQ
  let B := C.blockBase
  let t := k ^ 2 / N
  have hk_lt : k < N := by simpa [k, N] using C.remainderK_lt_modulus
  have hsq : k ^ 2 = N * t + k := by
    have h := Nat.div_add_mod (k ^ 2) N
    dsimp [t]
    rw [show k ^ 2 % N = k by simpa [k, N, pow_two] using hidempotent] at h
    exact h.symm
  have hcu : k ^ 3 = N * (t * (k + 1)) + k := by
    nlinarith [hsq]
  have hcarry1 : C.incomingCarry 1 = t := by
    simpa [k, N, t, pow_two] using
      C.incomingCarry_one_eq_remainderK_sq_div_modulus hgood
  have hcarry2 : C.incomingCarry 2 = t * (k + 1) := by
    rw [C.incomingCarry_two_eq_remainderK_cu_div_modulus hgood]
    dsimp [k, N, t] at hcu ⊢
    rw [hcu]
    rw [Nat.mul_add_div C.modulus_pos]
    rw [Nat.div_eq_of_lt hk_lt, add_zero]
  have hsum : C.rawCoefficient 2 + t * (k + 1) = C.rawCoefficient 1 + t + t * B := by
    have hB : B = q * N + k := by
      simpa [B, q, N, k, Nat.mul_comm] using
        C.blockBase_eq_quotientQ_mul_modulus_add_remainderK
    unfold BlockCoordinate.rawCoefficient
    dsimp [q, k, N, B] at hB hsq ⊢
    nlinarith [hsq, hB]
  unfold BlockCoordinate.canonicalCarryBlockValue
  rw [hcarry1, hcarry2]
  calc
    (C.rawCoefficient 1 + t) % C.blockBase
      = (C.rawCoefficient 1 + t + t * C.blockBase) % C.blockBase := by
          rw [Nat.add_mul_mod_self_right]
    _ = (C.rawCoefficient 2 + t * (k + 1)) % C.blockBase := by rw [hsum]

/-- Lean mirror of the exported Shape187/K188 same-position scaling
hypotheses. The fields encode the arithmetic reason why the row-level
idempotent-remainder check holds: the denominator is a scaled core, the
remainder is one past that core, and the scale divides the remainder. -/
structure BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses
    (C : BlockCoordinate) (coreModulus multiplier : ℕ) : Prop where
  goodMode : C.goodMode
  modulus_eq_multiplier_mul_core :
    C.modulus = multiplier * coreModulus
  remainderK_eq_core_plus_one :
    C.remainderK = coreModulus + 1
  multiplier_dvd_remainderK :
    multiplier ∣ C.remainderK

/-- The exported Shape187/K188 same-position scaling hypotheses imply the
idempotent-remainder condition used by the canonical carried-output theorem. -/
theorem BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses.idempotent_remainder
    {C : BlockCoordinate} {coreModulus multiplier : ℕ}
    (h : C.SamePositionScalingHiddenCarryBlockValueHypotheses
      coreModulus multiplier) :
    C.remainderK * C.remainderK % C.modulus = C.remainderK := by
  rcases h.multiplier_dvd_remainderK with ⟨scale, hscale⟩
  have hcore_succ : coreModulus + 1 = multiplier * scale := by
    rw [← h.remainderK_eq_core_plus_one, hscale]
  have hprod :
      C.remainderK * C.remainderK = scale * C.modulus + C.remainderK := by
    rw [h.remainderK_eq_core_plus_one, h.modulus_eq_multiplier_mul_core]
    nlinarith [hcore_succ]
  rw [hprod, Nat.add_comm]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt C.remainderK_lt_modulus

/-- A bundled Shape187/K188 same-position scaling hypothesis record is enough
to prove the canonical hidden carried-output equality at positions `1` and
`2`. -/
theorem BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses.hiddenCarryBlockValue_one_two
    {C : BlockCoordinate} {coreModulus multiplier : ℕ}
    (h : C.SamePositionScalingHiddenCarryBlockValueHypotheses
      coreModulus multiplier) :
    C.canonicalCarryBlockValue 1 = C.canonicalCarryBlockValue 2 := by
  exact C.samePositionIdempotent_hiddenCarryBlockValue
    h.goodMode h.idempotent_remainder

/-- Adapter from the exported Shape187/K188 same-position scaling hypothesis
bundle to the existing idempotent-remainder hidden-output proof path. -/
theorem BlockCoordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses
    (C : BlockCoordinate) {coreModulus multiplier : ℕ}
    (h : C.SamePositionScalingHiddenCarryBlockValueHypotheses
      coreModulus multiplier) :
    C.canonicalCarryBlockValue 1 = C.canonicalCarryBlockValue 2 := by
  exact h.hiddenCarryBlockValue_one_two

/-- If scaling a dividend does not push the original division remainder past
the divisor, division commutes with that scaling. This is the exact arithmetic
condition behind scaled same-core carry preservation. -/
theorem nat_mul_div_eq_mul_div_of_mul_mod_lt
    {x divisor scale : ℕ}
    (hdivisor : 0 < divisor)
    (hrem : scale * (x % divisor) < divisor) :
    (scale * x) / divisor = scale * (x / divisor) := by
  let quotient := x / divisor
  let remainder := x % divisor
  have hx : x = divisor * quotient + remainder := by
    dsimp [quotient, remainder]
    exact (Nat.div_add_mod x divisor).symm
  have hscaled :
      scale * x = divisor * (scale * quotient) + scale * remainder := by
    rw [hx]
    ring
  calc
    (scale * x) / divisor
      = (divisor * (scale * quotient) + scale * remainder) / divisor := by rw [hscaled]
    _ = scale * quotient + (scale * remainder) / divisor := by
          exact Nat.mul_add_div hdivisor (scale * quotient) (scale * remainder)
    _ = scale * quotient := by
          rw [Nat.div_eq_of_lt hrem, add_zero]

/-- Iff form of `nat_mul_div_eq_mul_div_of_mul_mod_lt`: scaling commutes with
division exactly when the scaled original remainder still lies below the
divisor. -/
theorem nat_mul_div_eq_mul_div_iff_mul_mod_lt
    {x divisor scale : ℕ}
    (hdivisor : 0 < divisor) :
    (scale * x) / divisor = scale * (x / divisor) ↔
      scale * (x % divisor) < divisor := by
  let quotient := x / divisor
  let remainder := x % divisor
  have hx : x = divisor * quotient + remainder := by
    dsimp [quotient, remainder]
    exact (Nat.div_add_mod x divisor).symm
  have hscaled :
      scale * x = divisor * (scale * quotient) + scale * remainder := by
    rw [hx]
    ring
  have hdiv :
      (scale * x) / divisor =
        scale * quotient + (scale * remainder) / divisor := by
    rw [hscaled]
    exact Nat.mul_add_div hdivisor (scale * quotient) (scale * remainder)
  constructor
  · intro h
    have hzero : (scale * remainder) / divisor = 0 := by
      have hcancel :
          scale * quotient + (scale * remainder) / divisor =
            scale * quotient + 0 := by
        calc
          scale * quotient + (scale * remainder) / divisor
            = (scale * x) / divisor := hdiv.symm
          _ = scale * (x / divisor) := h
          _ = scale * quotient + 0 := by simp [quotient]
      exact Nat.add_left_cancel hcancel
    have hzero_or_lt := (Nat.div_eq_zero_iff.mp hzero)
    cases hzero_or_lt with
    | inl hdivisor_zero => omega
    | inr hlt => simpa [remainder] using hlt
  · intro hrem
    exact nat_mul_div_eq_mul_div_of_mul_mod_lt hdivisor hrem

/-- If scaling a value does not push its block remainder past the modulus, then
block reduction commutes with that scaling. -/
theorem nat_mul_mod_eq_mul_mod_of_mul_mod_lt
    {x modulus scale : ℕ}
    (hrem : scale * (x % modulus) < modulus) :
    (scale * x) % modulus = scale * (x % modulus) := by
  let quotient := x / modulus
  let remainder := x % modulus
  have hx : x = modulus * quotient + remainder := by
    dsimp [quotient, remainder]
    exact (Nat.div_add_mod x modulus).symm
  have hscaled :
      scale * x = modulus * (scale * quotient) + scale * remainder := by
    rw [hx]
    ring
  calc
    (scale * x) % modulus
      = (modulus * (scale * quotient) + scale * remainder) % modulus := by rw [hscaled]
    _ = (scale * remainder) % modulus := by
          rw [show modulus * (scale * quotient) + scale * remainder =
              scale * remainder + modulus * (scale * quotient) by ac_rfl]
          exact Nat.add_mul_mod_self_left (scale * remainder) modulus (scale * quotient)
    _ = scale * remainder := Nat.mod_eq_of_lt hrem

/-- Iff form of `nat_mul_mod_eq_mul_mod_of_mul_mod_lt`: scaling commutes with
block reduction exactly when the scaled original remainder still lies below
the modulus. -/
theorem nat_mul_mod_eq_mul_mod_iff_mul_mod_lt
    {x modulus scale : ℕ}
    (hmodulus : 0 < modulus) :
    (scale * x) % modulus = scale * (x % modulus) ↔
      scale * (x % modulus) < modulus := by
  constructor
  · intro h
    have hlt : (scale * x) % modulus < modulus := Nat.mod_lt _ hmodulus
    simpa [h] using hlt
  · intro hrem
    exact nat_mul_mod_eq_mul_mod_of_mul_mod_lt hrem

/-- One-block scaled same-core raw-coefficient shift. If the base-supported
factor times `scale` is the shared remainder `k`, then the shifted actual raw
coefficient is the stripped-core raw coefficient scaled by `scale`.

For the Shape17/K4 family this distinguishes `17 -> 68`, where `scale = 1`,
from `17 -> 34`, where `scale = 2`. -/
theorem sameCoreCompatible_rawCoefficient_shift_scaled_one
    {base n stride scale j : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hscale :
      basePrimeSupportFactor base n * scale =
        (actualCoordinate base n stride hn).remainderK) :
    scale * (strippedCoordinate base n stride hn).rawCoefficient j =
      (actualCoordinate base n stride hn).rawCoefficient (j + 1) := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  unfold BlockCoordinate.rawCoefficient
  rw [sameCoreCompatible_quotientQ_eq hcompat, sameCoreCompatible_remainderK_eq hcompat]
  rw [show actual.remainderK ^ (j + 1) =
      actual.remainderK ^ j * actual.remainderK by rw [pow_succ]]
  rw [← hscale]
  ac_rfl

/-- One-block scaled same-core incoming-carry shift. The extra hypothesis is
the exact obstruction condition: after scaling, the dropped remainder in the
division by `B-k` must still fit below `B-k`. -/
theorem sameCoreCompatible_incomingCarry_shift_scaled_one
    {base n stride scale j : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hscale :
      basePrimeSupportFactor base n * scale =
        (actualCoordinate base n stride hn).remainderK)
    (hscaledRemainder :
      scale *
          ((strippedCoordinate base n stride hn).rawCoefficient (j + 1) %
            ((actualCoordinate base n stride hn).blockBase -
              (actualCoordinate base n stride hn).remainderK)) <
        (actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK) :
    scale * (strippedCoordinate base n stride hn).incomingCarry j =
      (actualCoordinate base n stride hn).incomingCarry (j + 1) := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hsharedB : core.blockBase = actual.blockBase := rfl
  have hsharedK : core.remainderK = actual.remainderK := by
    simpa [actual, core] using sameCoreCompatible_remainderK_eq (hn := hn) hcompat
  have hden :
      core.blockBase - core.remainderK = actual.blockBase - actual.remainderK := by
    rw [hsharedB, hsharedK]
  have hden_pos : 0 < core.blockBase - core.remainderK := by
    rw [hden]
    exact Nat.sub_pos_of_lt (actual.remainderK_lt_blockBase hgood)
  have hraw :
      scale * core.rawCoefficient (j + 1) =
        actual.rawCoefficient ((j + 1) + 1) := by
    simpa [actual, core] using
      sameCoreCompatible_rawCoefficient_shift_scaled_one
        (base := base) (n := n) (stride := stride) (scale := scale)
        (j := j + 1) (hn := hn) hcompat hscale
  have hdiv :
      (scale * core.rawCoefficient (j + 1)) /
          (core.blockBase - core.remainderK) =
        scale * (core.rawCoefficient (j + 1) /
          (core.blockBase - core.remainderK)) := by
    exact nat_mul_div_eq_mul_div_of_mul_mod_lt
      (x := core.rawCoefficient (j + 1))
      (divisor := core.blockBase - core.remainderK)
      (scale := scale)
      hden_pos
      (by simpa [actual, core, hden] using hscaledRemainder)
  calc
    scale * core.incomingCarry j
      = scale * (core.rawCoefficient (j + 1) / (core.blockBase - core.remainderK)) := by
          rfl
    _ = (scale * core.rawCoefficient (j + 1)) /
          (core.blockBase - core.remainderK) := by rw [hdiv]
    _ = actual.rawCoefficient ((j + 1) + 1) /
          (actual.blockBase - actual.remainderK) := by rw [hraw, hden]
    _ = actual.incomingCarry (j + 1) := by rfl

/-- One-block scaled same-core canonical carried-output shift. The two
inequalities say exactly where the arithmetic can fail: first at the incoming
carry quotient, and then at the final block reduction. -/
theorem sameCoreCompatible_canonicalCarryBlockValue_shift_scaled_one
    {base n stride scale j : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hscale :
      basePrimeSupportFactor base n * scale =
        (actualCoordinate base n stride hn).remainderK)
    (hscaledCarryRemainder :
      scale *
          ((strippedCoordinate base n stride hn).rawCoefficient (j + 1) %
            ((actualCoordinate base n stride hn).blockBase -
              (actualCoordinate base n stride hn).remainderK)) <
        (actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK)
    (hscaledBlockRemainder :
      scale *
          ((strippedCoordinate base n stride hn).canonicalCarryBlockValue j) <
        (strippedCoordinate base n stride hn).blockBase) :
    (actualCoordinate base n stride hn).canonicalCarryBlockValue (j + 1) =
      scale * (strippedCoordinate base n stride hn).canonicalCarryBlockValue j := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hraw :
      scale * core.rawCoefficient j = actual.rawCoefficient (j + 1) := by
    simpa [actual, core] using
      sameCoreCompatible_rawCoefficient_shift_scaled_one
        (base := base) (n := n) (stride := stride) (scale := scale)
        (j := j) (hn := hn) hcompat hscale
  have hcarry :
      scale * core.incomingCarry j = actual.incomingCarry (j + 1) := by
    simpa [actual, core] using
      sameCoreCompatible_incomingCarry_shift_scaled_one
        (base := base) (n := n) (stride := stride) (scale := scale)
        (j := j) (hn := hn) hgood hcompat hscale hscaledCarryRemainder
  have hsharedB : core.blockBase = actual.blockBase := rfl
  have hsum :
      scale * core.rawCoefficient j + scale * core.incomingCarry j =
        scale * (core.rawCoefficient j + core.incomingCarry j) := by
    ring
  unfold BlockCoordinate.canonicalCarryBlockValue
  rw [← hraw, ← hcarry]
  calc
    (scale * core.rawCoefficient j + scale * core.incomingCarry j) % actual.blockBase
      = (scale * (core.rawCoefficient j + core.incomingCarry j)) % core.blockBase := by
          rw [← hsharedB, hsum]
    _ = scale * ((core.rawCoefficient j + core.incomingCarry j) % core.blockBase) := by
          exact nat_mul_mod_eq_mul_mod_of_mul_mod_lt
            (x := core.rawCoefficient j + core.incomingCarry j)
            (modulus := core.blockBase)
            (scale := scale)
            hscaledBlockRemainder

/-- If the stripped core has a hidden canonical carried-output equality at two
positions, the scaled one-block same-core criterion transports that hidden
output equality to the shifted actual positions. -/
theorem sameCoreCompatible_hiddenCarryBlockValue_shift_scaled_one
    {base n stride scale left right : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hscale :
      basePrimeSupportFactor base n * scale =
        (actualCoordinate base n stride hn).remainderK)
    (hleftCarryRemainder :
      scale *
          ((strippedCoordinate base n stride hn).rawCoefficient (left + 1) %
            ((actualCoordinate base n stride hn).blockBase -
              (actualCoordinate base n stride hn).remainderK)) <
        (actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK)
    (hrightCarryRemainder :
      scale *
          ((strippedCoordinate base n stride hn).rawCoefficient (right + 1) %
            ((actualCoordinate base n stride hn).blockBase -
              (actualCoordinate base n stride hn).remainderK)) <
        (actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK)
    (hleftBlockRemainder :
      scale *
          ((strippedCoordinate base n stride hn).canonicalCarryBlockValue left) <
        (strippedCoordinate base n stride hn).blockBase)
    (hrightBlockRemainder :
      scale *
          ((strippedCoordinate base n stride hn).canonicalCarryBlockValue right) <
        (strippedCoordinate base n stride hn).blockBase)
    (hcoreHidden :
      (strippedCoordinate base n stride hn).canonicalCarryBlockValue left =
        (strippedCoordinate base n stride hn).canonicalCarryBlockValue right) :
    (actualCoordinate base n stride hn).canonicalCarryBlockValue (left + 1) =
      (actualCoordinate base n stride hn).canonicalCarryBlockValue (right + 1) := by
  rw [sameCoreCompatible_canonicalCarryBlockValue_shift_scaled_one
      (base := base) (n := n) (stride := stride) (scale := scale)
      (j := left) (hn := hn) hgood hcompat hscale hleftCarryRemainder
      hleftBlockRemainder]
  rw [sameCoreCompatible_canonicalCarryBlockValue_shift_scaled_one
      (base := base) (n := n) (stride := stride) (scale := scale)
      (j := right) (hn := hn) hgood hcompat hscale hrightCarryRemainder
      hrightBlockRemainder]
  rw [hcoreHidden]

/-- Scale-two specialization of
`sameCoreCompatible_hiddenCarryBlockValue_shift_scaled_one`. This is the
Lean-facing criterion used by the Shape13/K4 mod-stable carry-loss hook: once
the base-supported factor is exactly half of the shared remainder `k`, the only
extra arithmetic needed to transport a hidden core carried-output equality is
the pair of quotient-remainder and block-remainder bounds below. -/
theorem sameCoreCompatible_hiddenCarryBlockValue_shift_scale_two
    {base n stride left right : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hscale :
      basePrimeSupportFactor base n * 2 =
        (actualCoordinate base n stride hn).remainderK)
    (hleftCarryRemainder :
      2 *
          ((strippedCoordinate base n stride hn).rawCoefficient (left + 1) %
            ((actualCoordinate base n stride hn).blockBase -
              (actualCoordinate base n stride hn).remainderK)) <
        (actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK)
    (hrightCarryRemainder :
      2 *
          ((strippedCoordinate base n stride hn).rawCoefficient (right + 1) %
            ((actualCoordinate base n stride hn).blockBase -
              (actualCoordinate base n stride hn).remainderK)) <
        (actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK)
    (hleftBlockRemainder :
      2 *
          ((strippedCoordinate base n stride hn).canonicalCarryBlockValue left) <
        (strippedCoordinate base n stride hn).blockBase)
    (hrightBlockRemainder :
      2 *
          ((strippedCoordinate base n stride hn).canonicalCarryBlockValue right) <
        (strippedCoordinate base n stride hn).blockBase)
    (hcoreHidden :
      (strippedCoordinate base n stride hn).canonicalCarryBlockValue left =
        (strippedCoordinate base n stride hn).canonicalCarryBlockValue right) :
    (actualCoordinate base n stride hn).canonicalCarryBlockValue (left + 1) =
      (actualCoordinate base n stride hn).canonicalCarryBlockValue (right + 1) := by
  exact
    sameCoreCompatible_hiddenCarryBlockValue_shift_scaled_one
      (base := base) (n := n) (stride := stride) (scale := 2)
      (left := left) (right := right) (hn := hn)
      hgood hcompat hscale hleftCarryRemainder hrightCarryRemainder
      hleftBlockRemainder hrightBlockRemainder hcoreHidden

/-- Lean mirror of the exported Shape13/K4 scale-two hypothesis booleans.
It bundles exactly the arithmetic data needed to reuse
`sameCoreCompatible_hiddenCarryBlockValue_shift_scale_two`: good mode,
same-core compatibility, `basePrimeSupportFactor * 2 = k`, the two
quotient-remainder bounds below `B-k`, the two block-remainder bounds below
`B`, and the source-core hidden carried-output equality. -/
structure SameCoreScaleTwoHiddenCarryBlockValueHypotheses
    (base n stride left right : ℕ) (hn : 0 < n) : Prop where
  goodMode : (actualCoordinate base n stride hn).goodMode
  sameCoreCompatible_hyp : sameCoreCompatible base n stride hn
  basePrimeSupportFactor_times_two_eq_k :
    basePrimeSupportFactor base n * 2 =
      (actualCoordinate base n stride hn).remainderK
  left_scaled_quotient_remainder_lt_gap :
    2 *
        ((strippedCoordinate base n stride hn).rawCoefficient (left + 1) %
          ((actualCoordinate base n stride hn).blockBase -
            (actualCoordinate base n stride hn).remainderK)) <
      (actualCoordinate base n stride hn).blockBase -
        (actualCoordinate base n stride hn).remainderK
  right_scaled_quotient_remainder_lt_gap :
    2 *
        ((strippedCoordinate base n stride hn).rawCoefficient (right + 1) %
          ((actualCoordinate base n stride hn).blockBase -
            (actualCoordinate base n stride hn).remainderK)) <
      (actualCoordinate base n stride hn).blockBase -
        (actualCoordinate base n stride hn).remainderK
  left_scaled_block_remainder_lt_blockBase :
    2 *
        ((strippedCoordinate base n stride hn).canonicalCarryBlockValue left) <
      (strippedCoordinate base n stride hn).blockBase
  right_scaled_block_remainder_lt_blockBase :
    2 *
        ((strippedCoordinate base n stride hn).canonicalCarryBlockValue right) <
      (strippedCoordinate base n stride hn).blockBase
  source_core_hidden_carryBlockValue :
    (strippedCoordinate base n stride hn).canonicalCarryBlockValue left =
      (strippedCoordinate base n stride hn).canonicalCarryBlockValue right

/-- A bundled Shape13/K4 scale-two hypothesis record is enough to transport a
source-core hidden carried-output equality to the shifted actual coordinate. -/
theorem SameCoreScaleTwoHiddenCarryBlockValueHypotheses.hiddenCarryBlockValue_shift
    {base n stride left right : ℕ} {hn : 0 < n}
    (h : SameCoreScaleTwoHiddenCarryBlockValueHypotheses
      base n stride left right hn) :
    (actualCoordinate base n stride hn).canonicalCarryBlockValue (left + 1) =
      (actualCoordinate base n stride hn).canonicalCarryBlockValue (right + 1) := by
  exact
    sameCoreCompatible_hiddenCarryBlockValue_shift_scale_two
      (base := base) (n := n) (stride := stride)
      (left := left) (right := right) (hn := hn)
      h.goodMode h.sameCoreCompatible_hyp
      h.basePrimeSupportFactor_times_two_eq_k
      h.left_scaled_quotient_remainder_lt_gap
      h.right_scaled_quotient_remainder_lt_gap
      h.left_scaled_block_remainder_lt_blockBase
      h.right_scaled_block_remainder_lt_blockBase
      h.source_core_hidden_carryBlockValue

/-- Adapter from the exported Shape13/K4 scale-two hypothesis bundle to the
existing same-core hidden-output proof path. -/
theorem sameCoreCompatible_hiddenCarryBlockValue_shift_scale_two_of_exportedHypotheses
    {base n stride left right : ℕ} {hn : 0 < n}
    (h : SameCoreScaleTwoHiddenCarryBlockValueHypotheses
      base n stride left right hn) :
    (actualCoordinate base n stride hn).canonicalCarryBlockValue (left + 1) =
      (actualCoordinate base n stride hn).canonicalCarryBlockValue (right + 1) := by
  exact h.hiddenCarryBlockValue_shift

/-- In the exact `k`-power same-core regime, the actual body term splits into
the leading actual prefix of length `s` and the stripped-core suffix. -/
theorem sameCoreCompatible_bodyTerm_shift_exact
    {base n stride s length : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (actualCoordinate base n stride hn).bodyTerm (s + length) =
      (strippedCoordinate base n stride hn).bodyTerm length +
        (actualCoordinate base n stride hn).bodyTerm s *
          (actualCoordinate base n stride hn).blockBase ^ length := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  induction length with
  | zero =>
      simp [BlockCoordinate.bodyTerm]
  | succ length ih =>
      have hraw :
          core.rawCoefficient length = actual.rawCoefficient (s + length) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, actual, core] using
          sameCoreCompatible_rawCoefficient_shift_exact
            (base := base) (n := n) (stride := stride) (s := s)
            (j := length) (hn := hn) hcompat hfactor
      have hbodysucc :
          actual.blockBase * core.bodyTerm length + core.rawCoefficient length =
            core.bodyTerm (length + 1) := by
        simpa [actual, core, Nat.add_comm] using (core.bodyTerm_succ length).symm
      calc
        actual.bodyTerm (s + (length + 1))
          = actual.blockBase * actual.bodyTerm (s + length) + actual.rawCoefficient (s + length) := by
              rw [show s + (length + 1) = (s + length) + 1 by omega]
              simpa [actual] using actual.bodyTerm_succ (s + length)
        _ = actual.blockBase *
              (core.bodyTerm length + actual.bodyTerm s * actual.blockBase ^ length) +
              actual.rawCoefficient (s + length) := by
              rw [ih]
        _ = actual.blockBase * core.bodyTerm length +
              actual.blockBase * (actual.bodyTerm s * actual.blockBase ^ length) +
              core.rawCoefficient length := by
              rw [Nat.mul_add, hraw]
        _ = (actual.blockBase * core.bodyTerm length + core.rawCoefficient length) +
              actual.bodyTerm s * actual.blockBase ^ (length + 1) := by
              rw [pow_succ]
              ac_rfl
        _ = core.bodyTerm (length + 1) +
              actual.bodyTerm s * actual.blockBase ^ (length + 1) := by
              rw [hbodysucc]

/-- In the exact `k`-power same-core regime, the shifted actual truncated
visible-prefix integer is the stripped-core truncated prefix with a fixed
leading offset coming from the first `s` actual blocks. -/
theorem sameCoreCompatible_truncatedVisiblePrefixValue_shift_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (actualCoordinate base n stride hn).truncatedVisiblePrefixValue
        (requestedBlocks + s) lookaheadBlocks =
      (strippedCoordinate base n stride hn).truncatedVisiblePrefixValue
          requestedBlocks lookaheadBlocks +
        (actualCoordinate base n stride hn).bodyTerm s *
          (actualCoordinate base n stride hn).blockBase ^ requestedBlocks := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  let Bpow := actual.blockBase ^ lookaheadBlocks
  have hBpow_pos : 0 < Bpow := by
    dsimp [Bpow]
    exact pow_pos (actual.blockBase_pos_of_goodMode hgood) _
  have hdvd : Bpow ∣ (actual.bodyTerm s * actual.blockBase ^ requestedBlocks) * Bpow := by
    exact ⟨actual.bodyTerm s * actual.blockBase ^ requestedBlocks, by ac_rfl⟩
  calc
    actual.truncatedVisiblePrefixValue (requestedBlocks + s) lookaheadBlocks
      = actual.bodyTerm ((requestedBlocks + s) + lookaheadBlocks) / Bpow := by
          simp [actual, Bpow, BlockCoordinate.truncatedVisiblePrefixValue]
    _ = actual.bodyTerm (s + (requestedBlocks + lookaheadBlocks)) / Bpow := by
          rw [show (requestedBlocks + s) + lookaheadBlocks =
              s + (requestedBlocks + lookaheadBlocks) by omega]
    _ = (core.bodyTerm (requestedBlocks + lookaheadBlocks) +
          actual.bodyTerm s * actual.blockBase ^ (requestedBlocks + lookaheadBlocks)) / Bpow := by
          rw [sameCoreCompatible_bodyTerm_shift_exact
            (base := base) (n := n) (stride := stride) (s := s)
            (length := requestedBlocks + lookaheadBlocks) (hn := hn) hcompat hfactor]
    _ = (core.bodyTerm (requestedBlocks + lookaheadBlocks) +
          (actual.bodyTerm s * actual.blockBase ^ requestedBlocks) * Bpow) / Bpow := by
          rw [show actual.blockBase ^ (requestedBlocks + lookaheadBlocks) =
              actual.blockBase ^ requestedBlocks * Bpow by
                simp [Bpow, Nat.pow_add]]
          ac_rfl
    _ = core.bodyTerm (requestedBlocks + lookaheadBlocks) / Bpow +
          ((actual.bodyTerm s * actual.blockBase ^ requestedBlocks) * Bpow) / Bpow := by
          rw [Nat.add_comm, Nat.add_div_of_dvd_right hdvd, Nat.add_comm]
    _ = core.bodyTerm (requestedBlocks + lookaheadBlocks) / Bpow +
          actual.bodyTerm s * actual.blockBase ^ requestedBlocks := by
          simp [Bpow, hBpow_pos]
    _ = core.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks +
          actual.bodyTerm s * actual.blockBase ^ requestedBlocks := by
          rw [show Bpow = core.blockBase ^ lookaheadBlocks by rfl]
          simp [actual, core, BlockCoordinate.truncatedVisiblePrefixValue]

/-- In the exact `k`-power same-core regime, the shifted actual truncated
visible-prefix remainder agrees exactly with the stripped-core remainder. -/
theorem sameCoreCompatible_truncatedVisiblePrefixRemainder_shift_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (actualCoordinate base n stride hn).truncatedVisiblePrefixRemainder
        (requestedBlocks + s) lookaheadBlocks =
      (strippedCoordinate base n stride hn).truncatedVisiblePrefixRemainder
        requestedBlocks lookaheadBlocks := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  let Bpow := actual.blockBase ^ lookaheadBlocks
  calc
    actual.truncatedVisiblePrefixRemainder (requestedBlocks + s) lookaheadBlocks
      = actual.bodyTerm ((requestedBlocks + s) + lookaheadBlocks) % Bpow := by
          simp [actual, Bpow, BlockCoordinate.truncatedVisiblePrefixRemainder]
    _ = actual.bodyTerm (s + (requestedBlocks + lookaheadBlocks)) % Bpow := by
          rw [show (requestedBlocks + s) + lookaheadBlocks =
              s + (requestedBlocks + lookaheadBlocks) by omega]
    _ = (core.bodyTerm (requestedBlocks + lookaheadBlocks) +
          actual.bodyTerm s * actual.blockBase ^ (requestedBlocks + lookaheadBlocks)) % Bpow := by
          rw [sameCoreCompatible_bodyTerm_shift_exact
            (base := base) (n := n) (stride := stride) (s := s)
            (length := requestedBlocks + lookaheadBlocks) (hn := hn) hcompat hfactor]
    _ = (core.bodyTerm (requestedBlocks + lookaheadBlocks) +
          (actual.bodyTerm s * actual.blockBase ^ requestedBlocks) * Bpow) % Bpow := by
          rw [show actual.blockBase ^ (requestedBlocks + lookaheadBlocks) =
              actual.blockBase ^ requestedBlocks * Bpow by
                simp [Bpow, Nat.pow_add]]
          ac_rfl
    _ = core.bodyTerm (requestedBlocks + lookaheadBlocks) % Bpow := by
          rw [Nat.mul_comm, Nat.add_mul_mod_self_left]
    _ = core.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks := by
          rw [show Bpow = core.blockBase ^ lookaheadBlocks by rfl]
          simp [core, BlockCoordinate.truncatedVisiblePrefixRemainder]

/-- In the exact `k`-power same-core regime, the shifted actual lookahead gap
numerator agrees exactly with the stripped-core gap numerator. -/
theorem sameCoreCompatible_lookaheadGapNumerator_shift_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (actualCoordinate base n stride hn).lookaheadGapNumerator
        (requestedBlocks + s) lookaheadBlocks =
      (strippedCoordinate base n stride hn).lookaheadGapNumerator
        requestedBlocks lookaheadBlocks := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hrem :
      actual.truncatedVisiblePrefixRemainder (requestedBlocks + s) lookaheadBlocks =
        core.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks := by
    exact sameCoreCompatible_truncatedVisiblePrefixRemainder_shift_exact
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hcompat hfactor
  have hsharedBpow : actual.blockBase ^ lookaheadBlocks = core.blockBase ^ lookaheadBlocks := by
    rfl
  unfold BlockCoordinate.lookaheadGapNumerator
  rw [hrem, hsharedBpow]

/-- In the exact `k`-power same-core regime, the shifted actual emitted-prefix
integer is the stripped-core emitted prefix with that same leading offset. -/
theorem sameCoreCompatible_emittedPrefixValue_shift_exact
    {base n stride s requestedBlocks : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (actualCoordinate base n stride hn).emittedPrefixValue (requestedBlocks + s) =
      (strippedCoordinate base n stride hn).emittedPrefixValue requestedBlocks +
        (actualCoordinate base n stride hn).bodyTerm s *
          (actualCoordinate base n stride hn).blockBase ^ requestedBlocks := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hsharedK : core.remainderK = actual.remainderK := by
    simpa [actual, core] using sameCoreCompatible_remainderK_eq (hn := hn) hcompat
  have hmod :
      actual.modulus = actual.remainderK ^ s * core.modulus := by
    calc
      actual.modulus = basePrimeSupportFactor base n * core.modulus := by
        simpa [actual, core, strippedPeriodModulus] using
          (basePrimeSupportFactor_mul_strippedPeriodModulus base n).symm
      _ = actual.remainderK ^ s * core.modulus := by rw [hfactor]
  have hpow_pos : 0 < actual.remainderK ^ s := by
    rw [← hfactor]
    exact basePrimeSupportFactor_pos base n
  have htail :
      actual.remainderK ^ (requestedBlocks + s) / actual.modulus =
        core.remainderK ^ requestedBlocks / core.modulus := by
    calc
      actual.remainderK ^ (requestedBlocks + s) / actual.modulus
        = (actual.remainderK ^ requestedBlocks * actual.remainderK ^ s) /
            (core.modulus * actual.remainderK ^ s) := by
              rw [Nat.pow_add, hmod, Nat.mul_comm (actual.remainderK ^ s) core.modulus]
      _ = actual.remainderK ^ requestedBlocks / core.modulus := by
            exact Nat.mul_div_mul_right _ _ hpow_pos
      _ = core.remainderK ^ requestedBlocks / core.modulus := by
            rw [← hsharedK]
  calc
    actual.emittedPrefixValue (requestedBlocks + s)
      = actual.bodyTerm (requestedBlocks + s) +
          actual.remainderK ^ (requestedBlocks + s) / actual.modulus := by
          simpa [actual] using
            actual.emittedPrefixValue_eq_bodyTerm_add_remainderKPowDivModulus (requestedBlocks + s)
    _ = core.bodyTerm requestedBlocks +
          actual.bodyTerm s * actual.blockBase ^ requestedBlocks +
          actual.remainderK ^ (requestedBlocks + s) / actual.modulus := by
          rw [show requestedBlocks + s = s + requestedBlocks by omega]
          rw [sameCoreCompatible_bodyTerm_shift_exact
            (base := base) (n := n) (stride := stride) (s := s)
            (length := requestedBlocks) (hn := hn) hcompat hfactor]
    _ = core.bodyTerm requestedBlocks +
          core.remainderK ^ requestedBlocks / core.modulus +
          actual.bodyTerm s * actual.blockBase ^ requestedBlocks := by
          rw [htail]
          ac_rfl
    _ = core.emittedPrefixValue requestedBlocks +
          actual.bodyTerm s * actual.blockBase ^ requestedBlocks := by
          rw [← core.emittedPrefixValue_eq_bodyTerm_add_remainderKPowDivModulus requestedBlocks]

/-- In the exact `k`-power same-core regime, exact finite prefix equality on
the shifted actual window is equivalent to exact finite prefix equality on the
stripped-core window. -/
theorem sameCoreCompatible_emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (actualCoordinate base n stride hn).emittedPrefixValue (requestedBlocks + s) =
        (actualCoordinate base n stride hn).truncatedVisiblePrefixValue
          (requestedBlocks + s) lookaheadBlocks ↔
      (strippedCoordinate base n stride hn).emittedPrefixValue requestedBlocks =
        (strippedCoordinate base n stride hn).truncatedVisiblePrefixValue
          requestedBlocks lookaheadBlocks := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  rw [sameCoreCompatible_emittedPrefixValue_shift_exact
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (hn := hn) hcompat hfactor]
  rw [sameCoreCompatible_truncatedVisiblePrefixValue_shift_exact
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hgood hcompat hfactor]
  constructor
  · intro h
    exact Nat.add_right_cancel h
  · intro h
    exact congrArg (fun t => t + actual.bodyTerm s * actual.blockBase ^ requestedBlocks) h

/-- In the exact `k`-power same-core regime, the tail-versus-gap-modulus
inequality transports exactly between the shifted actual denominator and the
stripped core. This exposes the finite gap arithmetic directly beneath the
lookahead certificate. -/
theorem sameCoreCompatible_tail_lt_gapModulus_iff_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (actualCoordinate base n stride hn).remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) <
        (actualCoordinate base n stride hn).lookaheadGapNumerator
          (requestedBlocks + s) lookaheadBlocks *
          (actualCoordinate base n stride hn).modulus ↔
      (strippedCoordinate base n stride hn).remainderK ^ (requestedBlocks + lookaheadBlocks) <
        (strippedCoordinate base n stride hn).lookaheadGapNumerator
          requestedBlocks lookaheadBlocks *
          (strippedCoordinate base n stride hn).modulus := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hsharedK : core.remainderK = actual.remainderK := by
    simpa [actual, core] using sameCoreCompatible_remainderK_eq (hn := hn) hcompat
  have hmod :
      actual.modulus = actual.remainderK ^ s * core.modulus := by
    calc
      actual.modulus = basePrimeSupportFactor base n * core.modulus := by
        simpa [actual, core, strippedPeriodModulus] using
          (basePrimeSupportFactor_mul_strippedPeriodModulus base n).symm
      _ = actual.remainderK ^ s * core.modulus := by rw [hfactor]
  have hpow_pos : 0 < actual.remainderK ^ s := by
    rw [← hfactor]
    exact basePrimeSupportFactor_pos base n
  have hgap :
      actual.lookaheadGapNumerator (requestedBlocks + s) lookaheadBlocks =
        core.lookaheadGapNumerator requestedBlocks lookaheadBlocks := by
    simpa [actual, core] using
      sameCoreCompatible_lookaheadGapNumerator_shift_exact
        (base := base) (n := n) (stride := stride) (s := s)
        (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
        (hn := hn) hcompat hfactor
  constructor
  · intro hactual
    have hmul :
        actual.remainderK ^ s * actual.remainderK ^ (requestedBlocks + lookaheadBlocks) <
          actual.remainderK ^ s *
            (core.lookaheadGapNumerator requestedBlocks lookaheadBlocks * core.modulus) := by
      calc
        actual.remainderK ^ s * actual.remainderK ^ (requestedBlocks + lookaheadBlocks)
          = actual.remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) := by
              symm
              rw [show (requestedBlocks + s) + lookaheadBlocks =
                  s + (requestedBlocks + lookaheadBlocks) by omega]
              rw [Nat.pow_add]
        _ < actual.lookaheadGapNumerator (requestedBlocks + s) lookaheadBlocks * actual.modulus :=
              hactual
        _ = core.lookaheadGapNumerator requestedBlocks lookaheadBlocks * actual.modulus := by
              rw [hgap]
        _ = actual.remainderK ^ s *
              (core.lookaheadGapNumerator requestedBlocks lookaheadBlocks * core.modulus) := by
              rw [hmod]
              ac_rfl
    have hcoreTail :
        actual.remainderK ^ (requestedBlocks + lookaheadBlocks) <
          core.lookaheadGapNumerator requestedBlocks lookaheadBlocks * core.modulus :=
      Nat.lt_of_mul_lt_mul_left hmul
    simpa [core, hsharedK] using hcoreTail
  · intro hcore
    have hmul :
        actual.remainderK ^ s * core.remainderK ^ (requestedBlocks + lookaheadBlocks) <
          actual.remainderK ^ s *
            (core.lookaheadGapNumerator requestedBlocks lookaheadBlocks * core.modulus) :=
      Nat.mul_lt_mul_of_pos_left hcore hpow_pos
    have hmul' :
        actual.remainderK ^ s * actual.remainderK ^ (requestedBlocks + lookaheadBlocks) <
          actual.remainderK ^ s *
            (core.lookaheadGapNumerator requestedBlocks lookaheadBlocks * core.modulus) := by
      simpa [hsharedK] using hmul
    calc
      actual.remainderK ^ ((requestedBlocks + s) + lookaheadBlocks)
        = actual.remainderK ^ s * actual.remainderK ^ (requestedBlocks + lookaheadBlocks) := by
            rw [show (requestedBlocks + s) + lookaheadBlocks =
                s + (requestedBlocks + lookaheadBlocks) by omega]
            rw [Nat.pow_add]
      _ < actual.remainderK ^ s *
            (core.lookaheadGapNumerator requestedBlocks lookaheadBlocks * core.modulus) := hmul'
      _ = core.lookaheadGapNumerator requestedBlocks lookaheadBlocks * actual.modulus := by
            rw [hmod]
            ac_rfl
      _ = actual.lookaheadGapNumerator (requestedBlocks + s) lookaheadBlocks * actual.modulus := by
            rw [← hgap]

/-- In the exact `k`-power same-core regime, the fixed-window lookahead
certificate transports exactly between the stripped core at `(n, L)` and the
actual denominator at `(n + s, L)`. This is still a fixed-window theorem, not
the open minimal/global lookahead claim. -/
theorem sameCoreCompatible_lookaheadCertificateHolds_iff_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (actualCoordinate base n stride hn).lookaheadCertificateHolds
        (requestedBlocks + s) lookaheadBlocks ↔
      (strippedCoordinate base n stride hn).lookaheadCertificateHolds
        requestedBlocks lookaheadBlocks := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hcoreGood : core.goodMode :=
    strippedCoordinate_goodMode_of_actual_goodMode hn hgood
  rw [actual.lookaheadCertificateHolds_iff_tail_lt_gapModulus
      hgood (requestedBlocks + s) lookaheadBlocks]
  rw [core.lookaheadCertificateHolds_iff_tail_lt_gapModulus
      hcoreGood requestedBlocks lookaheadBlocks]
  exact sameCoreCompatible_tail_lt_gapModulus_iff_add_exact
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hcompat hfactor

/-- Forward transport form of the exact same-core fixed-window certificate. -/
theorem sameCoreCompatible_lookaheadCertificateHolds_of_core_lookaheadCertificate_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hcert :
      (strippedCoordinate base n stride hn).lookaheadCertificateHolds
        requestedBlocks lookaheadBlocks) :
    (actualCoordinate base n stride hn).lookaheadCertificateHolds
      (requestedBlocks + s) lookaheadBlocks :=
  (sameCoreCompatible_lookaheadCertificateHolds_iff_add_exact
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hgood hcompat hfactor).2 hcert

/-- Forward exact same-core certificate transport also packages any explicitly
larger lookahead window on the shifted actual denominator. -/
theorem sameCoreCompatible_lookaheadCertificateHolds_of_core_lookaheadCertificate_add_exact_add
    {base n stride s requestedBlocks lookaheadBlocks extraLookahead : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hcert :
      (strippedCoordinate base n stride hn).lookaheadCertificateHolds
        requestedBlocks lookaheadBlocks) :
    (actualCoordinate base n stride hn).lookaheadCertificateHolds
      (requestedBlocks + s) (lookaheadBlocks + extraLookahead) := by
  let actual := actualCoordinate base n stride hn
  have hcertActual :
      actual.lookaheadCertificateHolds (requestedBlocks + s) lookaheadBlocks :=
    sameCoreCompatible_lookaheadCertificateHolds_of_core_lookaheadCertificate_add_exact
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hgood hcompat hfactor hcert
  exact actual.lookaheadCertificateHolds_of_lookaheadCertificate_add
    hgood (requestedBlocks + s) lookaheadBlocks extraLookahead hcertActual

/-- Reverse transport form of the same exact fixed-window certificate. -/
theorem sameCoreCompatible_core_lookaheadCertificateHolds_of_actual_lookaheadCertificate_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hcert :
      (actualCoordinate base n stride hn).lookaheadCertificateHolds
        (requestedBlocks + s) lookaheadBlocks) :
    (strippedCoordinate base n stride hn).lookaheadCertificateHolds
      requestedBlocks lookaheadBlocks :=
  (sameCoreCompatible_lookaheadCertificateHolds_iff_add_exact
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hgood hcompat hfactor).1 hcert

/-- Reverse exact same-core certificate transport also packages any explicitly
larger lookahead window on the stripped core. -/
theorem sameCoreCompatible_core_lookaheadCertificateHolds_of_actual_lookaheadCertificate_add_exact_add
    {base n stride s requestedBlocks lookaheadBlocks extraLookahead : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hcert :
      (actualCoordinate base n stride hn).lookaheadCertificateHolds
        (requestedBlocks + s) lookaheadBlocks) :
    (strippedCoordinate base n stride hn).lookaheadCertificateHolds
      requestedBlocks (lookaheadBlocks + extraLookahead) := by
  let core := strippedCoordinate base n stride hn
  have hcoreGood : core.goodMode :=
    strippedCoordinate_goodMode_of_actual_goodMode hn hgood
  have hcertCore :
      core.lookaheadCertificateHolds requestedBlocks lookaheadBlocks :=
    sameCoreCompatible_core_lookaheadCertificateHolds_of_actual_lookaheadCertificate_add_exact
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hgood hcompat hfactor hcert
  exact core.lookaheadCertificateHolds_of_lookaheadCertificate_add
    hcoreGood requestedBlocks lookaheadBlocks extraLookahead hcertCore

/-- Same-core compatibility is equivalent to quotient scaling by the stripped
base-supported factor in the shared block base. This packages the exact
coordinate-selection condition in the same `q`-ratio language used by the
same-core visibility families. -/
theorem sameCoreCompatible_iff_quotientQ_scaling
    {base n stride : ℕ} {hn : 0 < n} :
    sameCoreCompatible base n stride hn ↔
      preperiodSteps base n ≤ stride ∧
        (strippedCoordinate base n stride hn).quotientQ =
          (actualCoordinate base n stride hn).quotientQ *
            basePrimeSupportFactor base n := by
  constructor
  · intro hcompat
    exact ⟨hcompat.1, sameCoreCompatible_quotientQ_eq hcompat⟩
  · intro hscaling
    refine ⟨hscaling.1, ?_⟩
    let actual := actualCoordinate base n stride hn
    let core := strippedCoordinate base n stride hn
    have hmod :
        actual.modulus = basePrimeSupportFactor base n * core.modulus := by
      simpa [actual, core, strippedPeriodModulus] using
        (basePrimeSupportFactor_mul_strippedPeriodModulus base n).symm
    have hsum :
        (actual.quotientQ * basePrimeSupportFactor base n) * core.modulus + actual.remainderK =
          (actual.quotientQ * basePrimeSupportFactor base n) * core.modulus + core.remainderK := by
      calc
        (actual.quotientQ * basePrimeSupportFactor base n) * core.modulus + actual.remainderK
          = actual.quotientQ * actual.modulus + actual.remainderK := by
              rw [hmod]
              ac_rfl
        _ = actual.blockBase := by
              simpa [Nat.mul_comm] using
                actual.blockBase_eq_quotientQ_mul_modulus_add_remainderK.symm
        _ = core.blockBase := rfl
        _ = core.quotientQ * core.modulus + core.remainderK := by
              simpa [Nat.mul_comm] using
                core.blockBase_eq_quotientQ_mul_modulus_add_remainderK
        _ = (actual.quotientQ * basePrimeSupportFactor base n) * core.modulus + core.remainderK := by
              rw [hscaling.2]
    have hremEq : actual.remainderK = core.remainderK := Nat.add_left_cancel hsum
    calc
      actual.remainderK = core.remainderK := hremEq
      _ < core.modulus := core.remainderK_lt_modulus

/-- A practical same-core coordinate-selection criterion: once the stride has
absorbed the preperiod and the block base lies strictly between `n` and
`n + strippedPeriodModulus`, the actual coordinate automatically lands in the
same-core-compatible window. This is the exact `q = 1` family criterion used by
examples like `996` in base `10`. -/
theorem sameCoreCompatible_of_goodMode_and_blockBase_lt_modulus_add_stripped
    {base n stride : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hpre : preperiodSteps base n ≤ stride)
    (hsmall :
      (actualCoordinate base n stride hn).blockBase < n + strippedPeriodModulus base n) :
    sameCoreCompatible base n stride hn := by
  refine ⟨hpre, ?_⟩
  let actual := actualCoordinate base n stride hn
  have hsmall' : actual.blockBase < n + strippedPeriodModulus base n := by
    simpa [actual] using hsmall
  have hblock_lt_two_n : actual.blockBase < n + n := by
    exact lt_of_lt_of_le hsmall' (Nat.add_le_add_left (strippedPeriodModulus_le base n) n)
  have hq_eq_one : actual.quotientQ = 1 := by
    have hq_pos : 0 < actual.quotientQ := actual.quotientQ_pos_of_goodMode hgood
    have hq_mul_le : actual.quotientQ * n ≤ actual.blockBase := by
      simpa [actual, actualCoordinate, BlockCoordinate.quotientQ, BlockCoordinate.blockBase] using
        Nat.div_mul_le_self actual.blockBase n
    have hq_lt_two : actual.quotientQ < 2 := by
      by_contra hq_not_lt
      have hq_ge_two : 2 ≤ actual.quotientQ := by omega
      have htwo_le_B : 2 * n ≤ actual.blockBase := by
        exact le_trans (Nat.mul_le_mul_right n hq_ge_two) hq_mul_le
      omega
    omega
  have hdecomp : actual.blockBase = n + actual.remainderK := by
    calc
      actual.blockBase = actual.quotientQ * n + actual.remainderK := by
        simpa [actual, actualCoordinate] using
          actual.blockBase_eq_quotientQ_mul_modulus_add_remainderK
      _ = n + actual.remainderK := by rw [hq_eq_one, one_mul]
  have hrem : actual.remainderK < strippedPeriodModulus base n := by
    omega
  simpa [actual] using hrem

/-- Same-core compatibility is enough to transfer good modes from the actual
denominator to the stripped core. -/
theorem sameCoreCompatible_goodMode_of_actual_goodMode
    {base n stride : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode) :
    (strippedCoordinate base n stride hn).goodMode := by
  exact strippedCoordinate_goodMode_of_actual_goodMode hn hgood

/-- In the exact `k`-power same-core regime, the raw tail-mass lower-bound
inequality for the stripped core at `(requestedBlocks, lookaheadBlocks)` is
equivalent to the shifted inequality for the actual denominator at
`(requestedBlocks + s, lookaheadBlocks)`. -/
theorem sameCoreCompatible_tailMassLowerBound_iff_add
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (actualCoordinate base n stride hn).rawCoefficient ((requestedBlocks + s) + lookaheadBlocks) <
        (actualCoordinate base n stride hn).blockBase ^ lookaheadBlocks *
          ((actualCoordinate base n stride hn).blockBase -
            (actualCoordinate base n stride hn).remainderK) ↔
      (strippedCoordinate base n stride hn).rawCoefficient (requestedBlocks + lookaheadBlocks) <
        (strippedCoordinate base n stride hn).blockBase ^ lookaheadBlocks *
          ((strippedCoordinate base n stride hn).blockBase -
            (strippedCoordinate base n stride hn).remainderK) := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hraw :
      core.rawCoefficient (requestedBlocks + lookaheadBlocks) =
        actual.rawCoefficient ((requestedBlocks + s) + lookaheadBlocks) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, actual, core] using
      sameCoreCompatible_rawCoefficient_shift_exact
        (base := base) (n := n) (stride := stride) (s := s)
        (j := requestedBlocks + lookaheadBlocks) (hn := hn) hcompat hfactor
  have hsharedK : core.remainderK = actual.remainderK := by
    simpa [actual, core] using sameCoreCompatible_remainderK_eq (hn := hn) hcompat
  constructor
  · intro hactual
    have hactual' :
        actual.rawCoefficient ((requestedBlocks + s) + lookaheadBlocks) <
          actual.blockBase ^ lookaheadBlocks * (actual.blockBase - actual.remainderK) := by
      simpa [actual] using hactual
    rw [← hraw] at hactual'
    simpa [actual, core, hsharedK] using hactual'
  · intro hcore
    have hcore' :
        core.rawCoefficient (requestedBlocks + lookaheadBlocks) <
          core.blockBase ^ lookaheadBlocks * (core.blockBase - core.remainderK) := by
      simpa [core] using hcore
    rw [hraw] at hcore'
    simpa [actual, core, hsharedK] using hcore'

/-- Exact-named same-core tail-mass transport theorem in the `k^s` regime. -/
theorem sameCoreCompatible_tailMassLowerBound_iff_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (actualCoordinate base n stride hn).rawCoefficient ((requestedBlocks + s) + lookaheadBlocks) <
        (actualCoordinate base n stride hn).blockBase ^ lookaheadBlocks *
          ((actualCoordinate base n stride hn).blockBase -
            (actualCoordinate base n stride hn).remainderK) ↔
      (strippedCoordinate base n stride hn).rawCoefficient (requestedBlocks + lookaheadBlocks) <
        (strippedCoordinate base n stride hn).blockBase ^ lookaheadBlocks *
          ((strippedCoordinate base n stride hn).blockBase -
            (strippedCoordinate base n stride hn).remainderK) := by
  exact sameCoreCompatible_tailMassLowerBound_iff_add
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hcompat hfactor

/-- Any exact lookahead certificate on the shifted actual denominator forces
the stripped core to satisfy the same raw tail-mass lower-bound inequality. -/
theorem sameCoreCompatible_tailMassLowerBound_of_actual_lookaheadCertificate_add
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hcert :
      (actualCoordinate base n stride hn).lookaheadCertificateHolds
        (requestedBlocks + s) lookaheadBlocks) :
    (strippedCoordinate base n stride hn).rawCoefficient (requestedBlocks + lookaheadBlocks) <
      (strippedCoordinate base n stride hn).blockBase ^ lookaheadBlocks *
        ((strippedCoordinate base n stride hn).blockBase -
          (strippedCoordinate base n stride hn).remainderK) := by
  let actual := actualCoordinate base n stride hn
  have htail :
      actual.rawCoefficient ((requestedBlocks + s) + lookaheadBlocks) <
        actual.blockBase ^ lookaheadBlocks * (actual.blockBase - actual.remainderK) :=
    actual.lookaheadCertificateHolds_implies_tailMassLowerBound
      (requestedBlocks := requestedBlocks + s) (lookaheadBlocks := lookaheadBlocks) hcert
  exact (sameCoreCompatible_tailMassLowerBound_iff_add_exact
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hcompat hfactor).mp htail

/-- Exact-named reverse same-core tail-mass implication in the `k^s` regime. -/
theorem sameCoreCompatible_tailMassLowerBound_of_actual_lookaheadCertificate_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hcert :
      (actualCoordinate base n stride hn).lookaheadCertificateHolds
        (requestedBlocks + s) lookaheadBlocks) :
    (strippedCoordinate base n stride hn).rawCoefficient (requestedBlocks + lookaheadBlocks) <
      (strippedCoordinate base n stride hn).blockBase ^ lookaheadBlocks *
        ((strippedCoordinate base n stride hn).blockBase -
          (strippedCoordinate base n stride hn).remainderK) := by
  exact sameCoreCompatible_tailMassLowerBound_of_actual_lookaheadCertificate_add
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hcompat hfactor hcert

/-- Any exact lookahead certificate on the stripped core forces the shifted
actual denominator to satisfy the same raw tail-mass lower-bound inequality. -/
theorem sameCoreCompatible_tailMassLowerBound_of_core_lookaheadCertificate_add
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hcert :
      (strippedCoordinate base n stride hn).lookaheadCertificateHolds
        requestedBlocks lookaheadBlocks) :
    (actualCoordinate base n stride hn).rawCoefficient ((requestedBlocks + s) + lookaheadBlocks) <
      (actualCoordinate base n stride hn).blockBase ^ lookaheadBlocks *
        ((actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK) := by
  let core := strippedCoordinate base n stride hn
  have htail :
      core.rawCoefficient (requestedBlocks + lookaheadBlocks) <
        core.blockBase ^ lookaheadBlocks * (core.blockBase - core.remainderK) :=
    core.lookaheadCertificateHolds_implies_tailMassLowerBound
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks) hcert
  exact (sameCoreCompatible_tailMassLowerBound_iff_add_exact
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hcompat hfactor).mpr htail

/-- Exact-named forward same-core tail-mass implication in the `k^s` regime. -/
theorem sameCoreCompatible_tailMassLowerBound_of_core_lookaheadCertificate_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hcert :
      (strippedCoordinate base n stride hn).lookaheadCertificateHolds
        requestedBlocks lookaheadBlocks) :
    (actualCoordinate base n stride hn).rawCoefficient ((requestedBlocks + s) + lookaheadBlocks) <
      (actualCoordinate base n stride hn).blockBase ^ lookaheadBlocks *
        ((actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK) := by
  exact sameCoreCompatible_tailMassLowerBound_of_core_lookaheadCertificate_add
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hcompat hfactor hcert

/-- In the exact `k`-power same-core regime, the coarse sufficient condition
`k^(n+L) < modulus` for the stripped core is equivalent to the shifted
condition for the actual denominator. -/
theorem sameCoreCompatible_remainderKPow_lt_modulus_iff_add
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (strippedCoordinate base n stride hn).remainderK ^ (requestedBlocks + lookaheadBlocks) <
        (strippedCoordinate base n stride hn).modulus ↔
      (actualCoordinate base n stride hn).remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) <
        (actualCoordinate base n stride hn).modulus := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hsharedK : core.remainderK = actual.remainderK := by
    simpa [actual, core] using sameCoreCompatible_remainderK_eq (hn := hn) hcompat
  have hmod :
      actual.modulus = actual.remainderK ^ s * core.modulus := by
    calc
      actual.modulus = basePrimeSupportFactor base n * core.modulus := by
        simpa [actual, core, strippedPeriodModulus] using
          (basePrimeSupportFactor_mul_strippedPeriodModulus base n).symm
      _ = actual.remainderK ^ s * core.modulus := by rw [hfactor]
  have hpow_pos : 0 < actual.remainderK ^ s := by
    rw [← hfactor]
    exact basePrimeSupportFactor_pos base n
  constructor
  · intro hcore
    have hmul :
        actual.remainderK ^ s * core.remainderK ^ (requestedBlocks + lookaheadBlocks) <
          actual.remainderK ^ s * core.modulus :=
      Nat.mul_lt_mul_of_pos_left hcore hpow_pos
    have hmul' :
        actual.remainderK ^ s * actual.remainderK ^ (requestedBlocks + lookaheadBlocks) <
          actual.remainderK ^ s * core.modulus := by
      simpa [hsharedK] using hmul
    calc
      actual.remainderK ^ ((requestedBlocks + s) + lookaheadBlocks)
        = actual.remainderK ^ s * actual.remainderK ^ (requestedBlocks + lookaheadBlocks) := by
            rw [show (requestedBlocks + s) + lookaheadBlocks =
                s + (requestedBlocks + lookaheadBlocks) by omega]
            rw [Nat.pow_add]
      _ < actual.remainderK ^ s * core.modulus := hmul'
      _ = actual.modulus := by rw [← hmod]
  · intro hactual
    have hmul :
        actual.remainderK ^ s * actual.remainderK ^ (requestedBlocks + lookaheadBlocks) <
          actual.remainderK ^ s * core.modulus := by
      calc
        actual.remainderK ^ s * actual.remainderK ^ (requestedBlocks + lookaheadBlocks)
          = actual.remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) := by
              symm
              rw [show (requestedBlocks + s) + lookaheadBlocks =
                  s + (requestedBlocks + lookaheadBlocks) by omega]
              rw [Nat.pow_add]
        _ < actual.modulus := hactual
        _ = actual.remainderK ^ s * core.modulus := by rw [hmod]
    have hcoreActual :
        actual.remainderK ^ (requestedBlocks + lookaheadBlocks) < core.modulus :=
      Nat.lt_of_mul_lt_mul_left hmul
    simpa [core, hsharedK] using hcoreActual

/-- The coarse `k^(n+L) < modulus` sufficient condition transports from the
stripped core to the shifted actual denominator in the exact `k`-power regime. -/
theorem sameCoreCompatible_lookaheadCertificateHolds_of_core_remainderKPow_lt_modulus_add
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hsmall :
      (strippedCoordinate base n stride hn).remainderK ^ (requestedBlocks + lookaheadBlocks) <
        (strippedCoordinate base n stride hn).modulus) :
    (actualCoordinate base n stride hn).lookaheadCertificateHolds
      (requestedBlocks + s) lookaheadBlocks := by
  let actual := actualCoordinate base n stride hn
  have hsmallActual :
      actual.remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) < actual.modulus :=
    (sameCoreCompatible_remainderKPow_lt_modulus_iff_add
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hcompat hfactor).mp hsmall
  exact actual.lookaheadCertificateHolds_of_remainderK_pow_lt_modulus
    hgood (requestedBlocks + s) lookaheadBlocks hsmallActual

/-- The same coarse sufficient condition also transports back from the shifted
actual denominator to the stripped core. -/
theorem sameCoreCompatible_stripped_lookaheadCertificateHolds_of_actual_remainderKPow_lt_modulus_add
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hsmall :
      (actualCoordinate base n stride hn).remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) <
        (actualCoordinate base n stride hn).modulus) :
    (strippedCoordinate base n stride hn).lookaheadCertificateHolds
      requestedBlocks lookaheadBlocks := by
  let core := strippedCoordinate base n stride hn
  have hsmallCore :
      core.remainderK ^ (requestedBlocks + lookaheadBlocks) < core.modulus :=
    (sameCoreCompatible_remainderKPow_lt_modulus_iff_add
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hcompat hfactor).mpr hsmall
  exact core.lookaheadCertificateHolds_of_remainderK_pow_lt_modulus
    (sameCoreCompatible_goodMode_of_actual_goodMode (base := base) (n := n)
      (stride := stride) (hn := hn) hgood)
    requestedBlocks lookaheadBlocks hsmallCore

/-- Same-core incoming-carry positions for an actual denominator and its
stripped periodic core satisfy the interval law once the chosen coordinate
really is same-`k`. -/
theorem strippedCoordinate_firstIncomingCarryPosition_shift_interval
    {base n stride s a c : ℕ}
    (hn : 0 < n)
    (hrem : (actualCoordinate base n stride hn).remainderK < strippedPeriodModulus base n)
    (hactual : (actualCoordinate base n stride hn).isFirstIncomingCarryPosition a)
    (hcore : (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hr_lower : (actualCoordinate base n stride hn).remainderK ^ s ≤ basePrimeSupportFactor base n)
    (hr_upper : basePrimeSupportFactor base n <
      (actualCoordinate base n stride hn).remainderK ^ (s + 1))
    (hroom : s + 1 ≤ a) :
    s ≤ a - c ∧ a - c ≤ s + 1 := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hsharedK : actual.remainderK = core.remainderK := by
    symm
    simpa [actual, core] using strippedCoordinate_remainderK_eq_of_remainder_lt hn hrem
  have hqCore : core.quotientQ = actual.quotientQ * basePrimeSupportFactor base n := by
    simpa [actual, core] using strippedCoordinate_quotientQ_eq_of_remainder_lt hn hrem
  have hqActual : 0 < actual.quotientQ := actual.quotientQ_pos_of_goodMode hgood
  exact
    BlockCoordinate.firstIncomingCarryPosition_shift_interval
      (actual := actual) (core := core)
      (hsharedB := rfl)
      (hsharedK := hsharedK)
      (hactual := hactual)
      (hcore := hcore)
      (hk := hk)
      (hqActual := hqActual)
      (hqCore := hqCore)
      (hr_lower := hr_lower)
      (hr_upper := hr_upper)
      (hroom := hroom)

/-- Same-core-compatible coordinates satisfy the incoming-carry interval law. -/
theorem sameCoreCompatible_firstIncomingCarryPosition_shift_interval
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isFirstIncomingCarryPosition a)
    (hcore : (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hr_lower : (actualCoordinate base n stride hn).remainderK ^ s ≤ basePrimeSupportFactor base n)
    (hr_upper : basePrimeSupportFactor base n <
      (actualCoordinate base n stride hn).remainderK ^ (s + 1))
    (hroom : s + 1 ≤ a) :
    s ≤ a - c ∧ a - c ≤ s + 1 := by
  exact strippedCoordinate_firstIncomingCarryPosition_shift_interval hn hcompat.2
    hactual hcore hk hgood hr_lower hr_upper hroom

/-- Exact `k`-power same-core ratios force an exact incoming-carry shift for
the actual/core pair. -/
theorem strippedCoordinate_firstIncomingCarryPosition_shift_exact
    {base n stride s a c : ℕ}
    (hn : 0 < n)
    (hrem : (actualCoordinate base n stride hn).remainderK < strippedPeriodModulus base n)
    (hactual : (actualCoordinate base n stride hn).isFirstIncomingCarryPosition a)
    (hcore : (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hs_le : s ≤ a) :
    a - c = s := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hsharedK : actual.remainderK = core.remainderK := by
    symm
    simpa [actual, core] using strippedCoordinate_remainderK_eq_of_remainder_lt hn hrem
  have hqCore : core.quotientQ = actual.quotientQ * actual.remainderK ^ s := by
    calc
      core.quotientQ = actual.quotientQ * basePrimeSupportFactor base n := by
        simpa [actual, core] using strippedCoordinate_quotientQ_eq_of_remainder_lt hn hrem
      _ = actual.quotientQ * actual.remainderK ^ s := by rw [hfactor]
  exact
    BlockCoordinate.firstIncomingCarryPosition_shift_exact
      (actual := actual) (core := core)
      (hsharedB := rfl)
      (hsharedK := hsharedK)
      (hactual := hactual)
      (hcore := hcore)
      (hk := hk)
      (hqCore := hqCore)
      (hs_le := hs_le)

/-- Same-core-compatible coordinates satisfy the exact incoming-carry shift law
whenever the stripping factor is an exact `k`-power. -/
theorem sameCoreCompatible_firstIncomingCarryPosition_shift_exact
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isFirstIncomingCarryPosition a)
    (hcore : (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hs_le : s ≤ a) :
    a - c = s := by
  exact strippedCoordinate_firstIncomingCarryPosition_shift_exact hn hcompat.2
    hactual hcore hk hfactor hs_le

/-- The same family packaging applies to local-overflow boundaries. -/
theorem strippedCoordinate_localOverflowBoundary_shift_interval
    {base n stride s a c : ℕ}
    (hn : 0 < n)
    (hrem : (actualCoordinate base n stride hn).remainderK < strippedPeriodModulus base n)
    (hactual : (actualCoordinate base n stride hn).isLocalOverflowBoundary a)
    (hcore : (strippedCoordinate base n stride hn).isLocalOverflowBoundary c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hr_lower : (actualCoordinate base n stride hn).remainderK ^ s ≤ basePrimeSupportFactor base n)
    (hr_upper : basePrimeSupportFactor base n <
      (actualCoordinate base n stride hn).remainderK ^ (s + 1))
    (hroom : s + 1 ≤ a) :
    s ≤ a - c ∧ a - c ≤ s + 1 := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hsharedK : actual.remainderK = core.remainderK := by
    symm
    simpa [actual, core] using strippedCoordinate_remainderK_eq_of_remainder_lt hn hrem
  have hqCore : core.quotientQ = actual.quotientQ * basePrimeSupportFactor base n := by
    simpa [actual, core] using strippedCoordinate_quotientQ_eq_of_remainder_lt hn hrem
  have hqActual : 0 < actual.quotientQ := actual.quotientQ_pos_of_goodMode hgood
  exact
    BlockCoordinate.localOverflowBoundary_shift_interval
      (actual := actual) (core := core)
      (hsharedB := rfl)
      (hsharedK := hsharedK)
      (hactual := hactual)
      (hcore := hcore)
      (hk := hk)
      (hqActual := hqActual)
      (hqCore := hqCore)
      (hr_lower := hr_lower)
      (hr_upper := hr_upper)
      (hroom := hroom)

/-- Same-core-compatible coordinates satisfy the local-overflow interval law. -/
theorem sameCoreCompatible_localOverflowBoundary_shift_interval
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isLocalOverflowBoundary a)
    (hcore : (strippedCoordinate base n stride hn).isLocalOverflowBoundary c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hr_lower : (actualCoordinate base n stride hn).remainderK ^ s ≤ basePrimeSupportFactor base n)
    (hr_upper : basePrimeSupportFactor base n <
      (actualCoordinate base n stride hn).remainderK ^ (s + 1))
    (hroom : s + 1 ≤ a) :
    s ≤ a - c ∧ a - c ≤ s + 1 := by
  exact strippedCoordinate_localOverflowBoundary_shift_interval hn hcompat.2
    hactual hcore hk hgood hr_lower hr_upper hroom

/-- Exact `k`-power same-core ratios force an exact local-overflow shift. -/
theorem strippedCoordinate_localOverflowBoundary_shift_exact
    {base n stride s a c : ℕ}
    (hn : 0 < n)
    (hrem : (actualCoordinate base n stride hn).remainderK < strippedPeriodModulus base n)
    (hactual : (actualCoordinate base n stride hn).isLocalOverflowBoundary a)
    (hcore : (strippedCoordinate base n stride hn).isLocalOverflowBoundary c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hs_le : s ≤ a) :
    a - c = s := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hsharedK : actual.remainderK = core.remainderK := by
    symm
    simpa [actual, core] using strippedCoordinate_remainderK_eq_of_remainder_lt hn hrem
  have hqCore : core.quotientQ = actual.quotientQ * actual.remainderK ^ s := by
    calc
      core.quotientQ = actual.quotientQ * basePrimeSupportFactor base n := by
        simpa [actual, core] using strippedCoordinate_quotientQ_eq_of_remainder_lt hn hrem
      _ = actual.quotientQ * actual.remainderK ^ s := by rw [hfactor]
  exact
    BlockCoordinate.localOverflowBoundary_shift_exact
      (actual := actual) (core := core)
      (hsharedB := rfl)
      (hsharedK := hsharedK)
      (hactual := hactual)
      (hcore := hcore)
      (hk := hk)
      (hqCore := hqCore)
      (hs_le := hs_le)

/-- Same-core-compatible coordinates satisfy the exact local-overflow shift law
whenever the stripping factor is an exact `k`-power. -/
theorem sameCoreCompatible_localOverflowBoundary_shift_exact
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isLocalOverflowBoundary a)
    (hcore : (strippedCoordinate base n stride hn).isLocalOverflowBoundary c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hs_le : s ≤ a) :
    a - c = s := by
  exact strippedCoordinate_localOverflowBoundary_shift_exact hn hcompat.2
    hactual hcore hk hfactor hs_le

/-- The first visible mismatch occurs at the earlier of the incoming-carry and
local-overflow boundaries. -/
def firstVisibleMismatchPosition (incomingCarryPosition localOverflowBoundary : ℕ) : ℕ :=
  min incomingCarryPosition localOverflowBoundary

/-- If the incoming-carry boundary is no later than the local-overflow
boundary, then it is already the first visible mismatch position. -/
theorem firstVisibleMismatchPosition_eq_incomingCarryPosition_of_le
    {incomingCarryPosition localOverflowBoundary : ℕ}
    (h : incomingCarryPosition ≤ localOverflowBoundary) :
    firstVisibleMismatchPosition incomingCarryPosition localOverflowBoundary =
      incomingCarryPosition := by
  unfold firstVisibleMismatchPosition
  exact min_eq_left h

/-- If the local-overflow boundary is no later than the incoming-carry
boundary, then it is already the first visible mismatch position. -/
theorem firstVisibleMismatchPosition_eq_localOverflowBoundary_of_le
    {incomingCarryPosition localOverflowBoundary : ℕ}
    (h : localOverflowBoundary ≤ incomingCarryPosition) :
    firstVisibleMismatchPosition incomingCarryPosition localOverflowBoundary =
      localOverflowBoundary := by
  unfold firstVisibleMismatchPosition
  exact min_eq_right h

@[simp] theorem firstVisibleMismatchPosition_self (boundary : ℕ) :
    firstVisibleMismatchPosition boundary boundary = boundary := by
  exact firstVisibleMismatchPosition_eq_incomingCarryPosition_of_le le_rfl

/-- If both threshold boundaries shift by either `s` or `s + 1`, then the first
visible mismatch position obeys the same interval law. -/
theorem firstVisibleMismatchPosition_shift_interval
    {incomingActual incomingCore overflowActual overflowCore s : ℕ}
    (hincoming_lower : s ≤ incomingActual - incomingCore)
    (hincoming_upper : incomingActual - incomingCore ≤ s + 1)
    (hoverflow_lower : s ≤ overflowActual - overflowCore)
    (hoverflow_upper : overflowActual - overflowCore ≤ s + 1) :
    s ≤ firstVisibleMismatchPosition incomingActual overflowActual -
        firstVisibleMismatchPosition incomingCore overflowCore ∧
      firstVisibleMismatchPosition incomingActual overflowActual -
          firstVisibleMismatchPosition incomingCore overflowCore ≤ s + 1 := by
  unfold firstVisibleMismatchPosition
  by_cases hs : s = 0
  · subst hs
    constructor
    · exact Nat.zero_le _
    ·
      have hincoming_upper' : incomingActual ≤ incomingCore + 1 := by
        simpa [Nat.add_comm] using (Nat.sub_le_iff_le_add.mp hincoming_upper)
      have hoverflow_upper' : overflowActual ≤ overflowCore + 1 := by
        simpa [Nat.add_comm] using (Nat.sub_le_iff_le_add.mp hoverflow_upper)
      have hmin_upper : min incomingActual overflowActual ≤ min incomingCore overflowCore + 1 := by
        calc
          min incomingActual overflowActual
            ≤ min (incomingCore + 1) (overflowCore + 1) := by
                exact min_le_min hincoming_upper' hoverflow_upper'
          _ = min incomingCore overflowCore + 1 := by
                rw [min_add_add_right]
      exact (Nat.sub_le_iff_le_add).2 (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmin_upper)
  ·
    have hs_pos : 0 < s := Nat.pos_of_ne_zero hs
    have hincoming_order : incomingCore ≤ incomingActual := by
      by_contra h
      have hlt : incomingActual < incomingCore := Nat.lt_of_not_ge h
      have hsub : incomingActual - incomingCore = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
      omega
    have hoverflow_order : overflowCore ≤ overflowActual := by
      by_contra h
      have hlt : overflowActual < overflowCore := Nat.lt_of_not_ge h
      have hsub : overflowActual - overflowCore = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
      omega
    have hincoming_lower' : incomingCore + s ≤ incomingActual := by
      simpa [Nat.add_comm] using
        (Nat.le_sub_iff_add_le hincoming_order).mp hincoming_lower
    have hincoming_upper' : incomingActual ≤ incomingCore + (s + 1) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.sub_le_iff_le_add.mp hincoming_upper)
    have hoverflow_lower' : overflowCore + s ≤ overflowActual := by
      simpa [Nat.add_comm] using
        (Nat.le_sub_iff_add_le hoverflow_order).mp hoverflow_lower
    have hoverflow_upper' : overflowActual ≤ overflowCore + (s + 1) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.sub_le_iff_le_add.mp hoverflow_upper)
    have hmin_lower : min incomingCore overflowCore + s ≤ min incomingActual overflowActual := by
      calc
        min incomingCore overflowCore + s
          = min (incomingCore + s) (overflowCore + s) := by
              rw [min_add_add_right]
        _ ≤ min incomingActual overflowActual := by
              exact min_le_min hincoming_lower' hoverflow_lower'
    have hmin_upper : min incomingActual overflowActual ≤ min incomingCore overflowCore + (s + 1) := by
      calc
        min incomingActual overflowActual
          ≤ min (incomingCore + (s + 1)) (overflowCore + (s + 1)) := by
              exact min_le_min hincoming_upper' hoverflow_upper'
        _ = min incomingCore overflowCore + (s + 1) := by
              rw [min_add_add_right]
    have hmin_order : min incomingCore overflowCore ≤ min incomingActual overflowActual := by
      exact le_trans (Nat.le_add_right _ _) hmin_lower
    constructor
    · exact (Nat.le_sub_iff_add_le hmin_order).2 (by simpa [Nat.add_comm] using hmin_lower)
    · exact (Nat.sub_le_iff_le_add).2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmin_upper)

/-- If both threshold boundaries shift exactly by `s`, then so does the first
visible mismatch position. -/
theorem firstVisibleMismatchPosition_shift_exact
    {incomingCore overflowCore s : ℕ} :
    firstVisibleMismatchPosition (incomingCore + s) (overflowCore + s) -
        firstVisibleMismatchPosition incomingCore overflowCore = s := by
  unfold firstVisibleMismatchPosition
  rw [min_add_add_right]
  exact Nat.add_sub_cancel_left _ _

/-- In the exact `k`-power same-core regime, the first visible mismatch
position shifts by the same amount as the incoming-carry and local-overflow
boundaries, provided those same-core boundaries are not later in the stripped
core than in the actual denominator. -/
theorem sameCoreCompatible_firstVisibleMismatchPosition_shift_exact
    {base n stride s incomingActual incomingCore overflowActual overflowCore : ℕ}
    {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hincomingActual :
      (actualCoordinate base n stride hn).isFirstIncomingCarryPosition incomingActual)
    (hincomingCore :
      (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition incomingCore)
    (hoverflowActual :
      (actualCoordinate base n stride hn).isLocalOverflowBoundary overflowActual)
    (hoverflowCore :
      (strippedCoordinate base n stride hn).isLocalOverflowBoundary overflowCore)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hs_le_incoming : s ≤ incomingActual)
    (hs_le_overflow : s ≤ overflowActual)
    (hincoming_order : incomingCore ≤ incomingActual)
    (hoverflow_order : overflowCore ≤ overflowActual) :
    firstVisibleMismatchPosition incomingActual overflowActual -
        firstVisibleMismatchPosition incomingCore overflowCore = s := by
  have hincomingShift :
      incomingActual - incomingCore = s :=
    sameCoreCompatible_firstIncomingCarryPosition_shift_exact
      hcompat hincomingActual hincomingCore hk hfactor hs_le_incoming
  have hoverflowShift :
      overflowActual - overflowCore = s :=
    sameCoreCompatible_localOverflowBoundary_shift_exact
      hcompat hoverflowActual hoverflowCore hk hfactor hs_le_overflow
  have hincomingEq : incomingActual = incomingCore + s := by
    simpa [Nat.add_comm] using
      (Nat.sub_eq_iff_eq_add hincoming_order).mp hincomingShift
  have hoverflowEq : overflowActual = overflowCore + s := by
    simpa [Nat.add_comm] using
      (Nat.sub_eq_iff_eq_add hoverflow_order).mp hoverflowShift
  rw [hincomingEq, hoverflowEq]
  exact firstVisibleMismatchPosition_shift_exact

/-- In a same-core-compatible coordinate, if the incoming-carry and
local-overflow boundaries each satisfy the non-power interval law, then the
first visible mismatch position also shifts by either `s` or `s + 1`. This
remains an exact finite-boundary theorem beneath the open global visibility
claim. -/
theorem sameCoreCompatible_firstVisibleMismatchPosition_shift_interval
    {base n stride s incomingActual incomingCore overflowActual overflowCore : ℕ}
    {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hincomingActual :
      (actualCoordinate base n stride hn).isFirstIncomingCarryPosition incomingActual)
    (hincomingCore :
      (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition incomingCore)
    (hoverflowActual :
      (actualCoordinate base n stride hn).isLocalOverflowBoundary overflowActual)
    (hoverflowCore :
      (strippedCoordinate base n stride hn).isLocalOverflowBoundary overflowCore)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hr_lower : (actualCoordinate base n stride hn).remainderK ^ s ≤
      basePrimeSupportFactor base n)
    (hr_upper : basePrimeSupportFactor base n <
      (actualCoordinate base n stride hn).remainderK ^ (s + 1))
    (hroom_incoming : s + 1 ≤ incomingActual)
    (hroom_overflow : s + 1 ≤ overflowActual) :
    s ≤ firstVisibleMismatchPosition incomingActual overflowActual -
        firstVisibleMismatchPosition incomingCore overflowCore ∧
      firstVisibleMismatchPosition incomingActual overflowActual -
          firstVisibleMismatchPosition incomingCore overflowCore ≤ s + 1 := by
  have hincomingShift :
      s ≤ incomingActual - incomingCore ∧ incomingActual - incomingCore ≤ s + 1 :=
    sameCoreCompatible_firstIncomingCarryPosition_shift_interval
      hcompat hincomingActual hincomingCore hk hgood hr_lower hr_upper hroom_incoming
  have hoverflowShift :
      s ≤ overflowActual - overflowCore ∧ overflowActual - overflowCore ≤ s + 1 :=
    sameCoreCompatible_localOverflowBoundary_shift_interval
      hcompat hoverflowActual hoverflowCore hk hgood hr_lower hr_upper hroom_overflow
  exact firstVisibleMismatchPosition_shift_interval
    hincomingShift.1 hincomingShift.2 hoverflowShift.1 hoverflowShift.2

/-- A scaled-raw-coefficient criterion for the lower incoming-carry endpoint:
if the base-supported factor times the actual coefficient at `a - s` is still
below the incoming-carry threshold, then the same-core shift is exactly `s`. -/
theorem sameCoreCompatible_firstIncomingCarryPosition_shift_lower_of_scaledRawCoefficient_lt_gap
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isFirstIncomingCarryPosition a)
    (hcore : (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hr_lower : (actualCoordinate base n stride hn).remainderK ^ s ≤ basePrimeSupportFactor base n)
    (hs_le : s ≤ a)
    (hscaled :
      basePrimeSupportFactor base n *
          (actualCoordinate base n stride hn).rawCoefficient (a - s) <
        (actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK) :
    a - c = s := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hsharedK : actual.remainderK = core.remainderK := by
    symm
    simpa [actual, core] using sameCoreCompatible_remainderK_eq hcompat
  have hqCore : core.quotientQ = actual.quotientQ * basePrimeSupportFactor base n := by
    simpa [actual, core] using sameCoreCompatible_quotientQ_eq hcompat
  have hlower :
      core.quotientQ * actual.remainderK ^ (a - s) <
        actual.blockBase - actual.remainderK := by
    calc
      core.quotientQ * actual.remainderK ^ (a - s)
        = core.rawCoefficient (a - s) := by
            rw [BlockCoordinate.rawCoefficient, hsharedK]
      _ = basePrimeSupportFactor base n * actual.rawCoefficient (a - s) := by
            simpa [actual, core] using
              sameCoreCompatible_rawCoefficient_eq
                (base := base) (n := n) (stride := stride)
                (hn := hn) (j := a - s) hcompat
      _ < actual.blockBase - actual.remainderK := hscaled
  exact
    BlockCoordinate.firstIncomingCarryPosition_shift_lower
      (actual := actual) (core := core)
      (hsharedB := rfl)
      (hsharedK := hsharedK)
      (hactual := hactual)
      (hcore := hcore)
      (hk := hk)
      (hqCore := hqCore)
      (hr_lower := hr_lower)
      (hs_le := hs_le)
      hlower

/-- A scaled-raw-coefficient criterion for the upper incoming-carry endpoint:
if the base-supported factor times the actual coefficient at `a - s` already
reaches the incoming-carry threshold, then the same-core shift is `s + 1`. -/
theorem sameCoreCompatible_firstIncomingCarryPosition_shift_upper_of_gap_le_scaledRawCoefficient
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isFirstIncomingCarryPosition a)
    (hcore : (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hr_upper : basePrimeSupportFactor base n <
      (actualCoordinate base n stride hn).remainderK ^ (s + 1))
    (hroom : s + 1 ≤ a)
    (hscaled :
      (actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK ≤
        basePrimeSupportFactor base n *
          (actualCoordinate base n stride hn).rawCoefficient (a - s)) :
    a - c = s + 1 := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hsharedK : actual.remainderK = core.remainderK := by
    symm
    simpa [actual, core] using sameCoreCompatible_remainderK_eq hcompat
  have hqActual : 0 < actual.quotientQ := actual.quotientQ_pos_of_goodMode hgood
  have hqCore : core.quotientQ = actual.quotientQ * basePrimeSupportFactor base n := by
    simpa [actual, core] using sameCoreCompatible_quotientQ_eq hcompat
  have hupper :
      actual.blockBase - actual.remainderK ≤
        core.quotientQ * actual.remainderK ^ (a - s) := by
    calc
      actual.blockBase - actual.remainderK
        ≤ basePrimeSupportFactor base n * actual.rawCoefficient (a - s) := hscaled
      _ = core.rawCoefficient (a - s) := by
            symm
            simpa [actual, core] using
              sameCoreCompatible_rawCoefficient_eq
                (base := base) (n := n) (stride := stride)
                (hn := hn) (j := a - s) hcompat
      _ = core.quotientQ * actual.remainderK ^ (a - s) := by
            rw [BlockCoordinate.rawCoefficient, hsharedK]
  exact
    BlockCoordinate.firstIncomingCarryPosition_shift_upper
      (actual := actual) (core := core)
      (hsharedB := rfl)
      (hsharedK := hsharedK)
      (hactual := hactual)
      (hcore := hcore)
      (hk := hk)
      (hqActual := hqActual)
      (hqCore := hqCore)
      (hr_upper := hr_upper)
      (hroom := hroom)
      hupper

/-- A scaled-raw-coefficient criterion for the lower local-overflow endpoint:
if the base-supported factor times the actual coefficient at `a - s` still
fits below the block base, then the same-core shift is exactly `s`. -/
theorem sameCoreCompatible_localOverflowBoundary_shift_lower_of_scaledRawCoefficient_lt_blockBase
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isLocalOverflowBoundary a)
    (hcore : (strippedCoordinate base n stride hn).isLocalOverflowBoundary c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hr_lower : (actualCoordinate base n stride hn).remainderK ^ s ≤ basePrimeSupportFactor base n)
    (hs_le : s ≤ a)
    (hscaled :
      basePrimeSupportFactor base n *
          (actualCoordinate base n stride hn).rawCoefficient (a - s) <
        (actualCoordinate base n stride hn).blockBase) :
    a - c = s := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hsharedK : actual.remainderK = core.remainderK := by
    symm
    simpa [actual, core] using sameCoreCompatible_remainderK_eq hcompat
  have hqCore : core.quotientQ = actual.quotientQ * basePrimeSupportFactor base n := by
    simpa [actual, core] using sameCoreCompatible_quotientQ_eq hcompat
  have hlower :
      core.quotientQ * actual.remainderK ^ (a - s) < actual.blockBase := by
    calc
      core.quotientQ * actual.remainderK ^ (a - s)
        = core.rawCoefficient (a - s) := by
            rw [BlockCoordinate.rawCoefficient, hsharedK]
      _ = basePrimeSupportFactor base n * actual.rawCoefficient (a - s) := by
            simpa [actual, core] using
              sameCoreCompatible_rawCoefficient_eq
                (base := base) (n := n) (stride := stride)
                (hn := hn) (j := a - s) hcompat
      _ < actual.blockBase := hscaled
  exact
    BlockCoordinate.localOverflowBoundary_shift_lower
      (actual := actual) (core := core)
      (hsharedB := rfl)
      (hsharedK := hsharedK)
      (hactual := hactual)
      (hcore := hcore)
      (hk := hk)
      (hqCore := hqCore)
      (hr_lower := hr_lower)
      (hs_le := hs_le)
      hlower

/-- A scaled-raw-coefficient criterion for the upper local-overflow endpoint:
if the base-supported factor times the actual coefficient at `a - s` has
already reached the block base, then the same-core shift is `s + 1`. -/
theorem sameCoreCompatible_localOverflowBoundary_shift_upper_of_blockBase_le_scaledRawCoefficient
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isLocalOverflowBoundary a)
    (hcore : (strippedCoordinate base n stride hn).isLocalOverflowBoundary c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hr_upper : basePrimeSupportFactor base n <
      (actualCoordinate base n stride hn).remainderK ^ (s + 1))
    (hroom : s + 1 ≤ a)
    (hscaled :
      (actualCoordinate base n stride hn).blockBase ≤
        basePrimeSupportFactor base n *
          (actualCoordinate base n stride hn).rawCoefficient (a - s)) :
    a - c = s + 1 := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hsharedK : actual.remainderK = core.remainderK := by
    symm
    simpa [actual, core] using sameCoreCompatible_remainderK_eq hcompat
  have hqActual : 0 < actual.quotientQ := actual.quotientQ_pos_of_goodMode hgood
  have hqCore : core.quotientQ = actual.quotientQ * basePrimeSupportFactor base n := by
    simpa [actual, core] using sameCoreCompatible_quotientQ_eq hcompat
  have hupper :
      actual.blockBase ≤ core.quotientQ * actual.remainderK ^ (a - s) := by
    calc
      actual.blockBase
        ≤ basePrimeSupportFactor base n * actual.rawCoefficient (a - s) := hscaled
      _ = core.rawCoefficient (a - s) := by
            symm
            simpa [actual, core] using
              sameCoreCompatible_rawCoefficient_eq
                (base := base) (n := n) (stride := stride)
                (hn := hn) (j := a - s) hcompat
      _ = core.quotientQ * actual.remainderK ^ (a - s) := by
            rw [BlockCoordinate.rawCoefficient, hsharedK]
  exact
    BlockCoordinate.localOverflowBoundary_shift_upper
      (actual := actual) (core := core)
      (hsharedB := rfl)
      (hsharedK := hsharedK)
      (hactual := hactual)
      (hcore := hcore)
      (hk := hk)
      (hqActual := hqActual)
      (hqCore := hqCore)
      (hr_upper := hr_upper)
      (hroom := hroom)
      hupper

/-- Endpoint classifier for same-core threshold shifts. The exact-power case is
kept separate from the non-power lower/upper interval endpoints. -/
def classifyThresholdShiftEndpoint (k factor s a c : ℕ) : Option ThresholdShiftEndpoint :=
  if factor = k ^ s then
    if a - c = s then some .exact else none
  else if k ^ s < factor ∧ factor < k ^ (s + 1) then
    if a - c = s then some .lower else if a - c = s + 1 then some .upper else none
  else
    none

theorem classifyThresholdShiftEndpoint_eq_exact
    {k factor s a c : ℕ}
    (hpow : factor = k ^ s)
    (hshift : a - c = s) :
    classifyThresholdShiftEndpoint k factor s a c = some .exact := by
  unfold classifyThresholdShiftEndpoint
  simp [hpow, hshift]

theorem classifyThresholdShiftEndpoint_eq_lower
    {k factor s a c : ℕ}
    (hlower : k ^ s < factor)
    (hupper : factor < k ^ (s + 1))
    (hshift : a - c = s) :
    classifyThresholdShiftEndpoint k factor s a c = some .lower := by
  unfold classifyThresholdShiftEndpoint
  simp [hlower.ne', hlower, hupper, hshift]

theorem classifyThresholdShiftEndpoint_eq_upper
    {k factor s a c : ℕ}
    (hlower : k ^ s < factor)
    (hupper : factor < k ^ (s + 1))
    (hshift : a - c = s + 1) :
    classifyThresholdShiftEndpoint k factor s a c = some .upper := by
  unfold classifyThresholdShiftEndpoint
  have hne : factor ≠ k ^ s := hlower.ne'
  simp [hne, hlower, hupper, hshift]

theorem classifyThresholdShiftEndpoint_eq_lower_iff
    {k factor s a c : ℕ} :
    classifyThresholdShiftEndpoint k factor s a c = some .lower ↔
      k ^ s < factor ∧ factor < k ^ (s + 1) ∧ a - c = s := by
  unfold classifyThresholdShiftEndpoint
  by_cases hpow : factor = k ^ s
  · simp [hpow]
  · by_cases hinterval : k ^ s < factor ∧ factor < k ^ (s + 1)
    · rcases hinterval with ⟨hlower, hupper⟩
      constructor
      · intro h
        by_cases hshift : a - c = s
        · simp [hpow, hlower, hupper, hshift] at h
          exact ⟨hlower, hupper, hshift⟩
        · simp [hpow, hlower, hupper, hshift] at h
      · rintro ⟨_, _, hshift⟩
        simp [hpow, hlower, hupper, hshift]
    · constructor
      · intro h
        simp [hpow, hinterval] at h
      · rintro ⟨hlower, hupper, _⟩
        exact (hinterval ⟨hlower, hupper⟩).elim

theorem classifyThresholdShiftEndpoint_eq_upper_iff
    {k factor s a c : ℕ} :
    classifyThresholdShiftEndpoint k factor s a c = some .upper ↔
      k ^ s < factor ∧ factor < k ^ (s + 1) ∧ a - c = s + 1 := by
  unfold classifyThresholdShiftEndpoint
  by_cases hpow : factor = k ^ s
  · simp [hpow]
  · by_cases hinterval : k ^ s < factor ∧ factor < k ^ (s + 1)
    · rcases hinterval with ⟨hlower, hupper⟩
      constructor
      · intro h
        by_cases hshift : a - c = s
        · simp [hpow, hlower, hupper, hshift] at h
        · simpa [hpow, hlower, hupper, hshift] using h
      · rintro ⟨_, _, hshift⟩
        simp [hpow, hlower, hupper, hshift]
    · constructor
      · intro h
        simp [hpow, hinterval] at h
      · rintro ⟨hlower, hupper, _⟩
        exact (hinterval ⟨hlower, hupper⟩).elim

/-- If both the incoming-carry and local-overflow boundaries carry the `lower`
non-power endpoint label, then the first visible mismatch boundary does too. -/
theorem firstVisibleMismatchPosition_endpoint_lower_of_incomingCarry_lower_and_localOverflow_lower
    {k factor s incomingActual incomingCore overflowActual overflowCore : ℕ}
    (hincoming :
      classifyThresholdShiftEndpoint k factor s incomingActual incomingCore = some .lower)
    (hoverflow :
      classifyThresholdShiftEndpoint k factor s overflowActual overflowCore = some .lower) :
    classifyThresholdShiftEndpoint k factor s
      (firstVisibleMismatchPosition incomingActual overflowActual)
      (firstVisibleMismatchPosition incomingCore overflowCore) = some .lower := by
  rcases (classifyThresholdShiftEndpoint_eq_lower_iff.mp hincoming) with
    ⟨hlower, hupper, hincomingShift⟩
  rcases (classifyThresholdShiftEndpoint_eq_lower_iff.mp hoverflow) with
    ⟨_, _, hoverflowShift⟩
  apply classifyThresholdShiftEndpoint_eq_lower
  · exact hlower
  · exact hupper
  · by_cases hs : s = 0
    · subst hs
      have hincomingLe : incomingActual ≤ incomingCore := by
        exact Nat.sub_eq_zero_iff_le.mp hincomingShift
      have hoverflowLe : overflowActual ≤ overflowCore := by
        exact Nat.sub_eq_zero_iff_le.mp hoverflowShift
      have hminLe :
          min incomingActual overflowActual ≤ min incomingCore overflowCore := by
        exact min_le_min hincomingLe hoverflowLe
      exact Nat.sub_eq_zero_of_le hminLe
    ·
      have hs_pos : 0 < s := Nat.pos_of_ne_zero hs
      have hincomingOrder : incomingCore ≤ incomingActual := by
        by_contra h
        have hlt : incomingActual < incomingCore := Nat.lt_of_not_ge h
        have hsub : incomingActual - incomingCore = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
        omega
      have hoverflowOrder : overflowCore ≤ overflowActual := by
        by_contra h
        have hlt : overflowActual < overflowCore := Nat.lt_of_not_ge h
        have hsub : overflowActual - overflowCore = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
        omega
      have hincomingEq : incomingActual = incomingCore + s := by
        exact (Nat.sub_eq_iff_eq_add' hincomingOrder).mp hincomingShift
      have hoverflowEq : overflowActual = overflowCore + s := by
        exact (Nat.sub_eq_iff_eq_add' hoverflowOrder).mp hoverflowShift
      rw [hincomingEq, hoverflowEq]
      exact firstVisibleMismatchPosition_shift_exact

/-- If both the incoming-carry and local-overflow boundaries carry the `upper`
non-power endpoint label, then the first visible mismatch boundary does too. -/
theorem firstVisibleMismatchPosition_endpoint_upper_of_incomingCarry_upper_and_localOverflow_upper
    {k factor s incomingActual incomingCore overflowActual overflowCore : ℕ}
    (hincoming :
      classifyThresholdShiftEndpoint k factor s incomingActual incomingCore = some .upper)
    (hoverflow :
      classifyThresholdShiftEndpoint k factor s overflowActual overflowCore = some .upper) :
    classifyThresholdShiftEndpoint k factor s
      (firstVisibleMismatchPosition incomingActual overflowActual)
      (firstVisibleMismatchPosition incomingCore overflowCore) = some .upper := by
  rcases (classifyThresholdShiftEndpoint_eq_upper_iff.mp hincoming) with
    ⟨hlower, hupper, hincomingShift⟩
  rcases (classifyThresholdShiftEndpoint_eq_upper_iff.mp hoverflow) with
    ⟨_, _, hoverflowShift⟩
  apply classifyThresholdShiftEndpoint_eq_upper
  · exact hlower
  · exact hupper
  · have hincomingOrder : incomingCore ≤ incomingActual := by
      by_contra h
      have hlt : incomingActual < incomingCore := Nat.lt_of_not_ge h
      have hsub : incomingActual - incomingCore = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
      omega
    have hoverflowOrder : overflowCore ≤ overflowActual := by
      by_contra h
      have hlt : overflowActual < overflowCore := Nat.lt_of_not_ge h
      have hsub : overflowActual - overflowCore = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
      omega
    have hincomingEq : incomingActual = incomingCore + (s + 1) := by
      exact (Nat.sub_eq_iff_eq_add' hincomingOrder).mp hincomingShift
    have hoverflowEq : overflowActual = overflowCore + (s + 1) := by
      exact (Nat.sub_eq_iff_eq_add' hoverflowOrder).mp hoverflowShift
    rw [hincomingEq, hoverflowEq]
    simpa using (firstVisibleMismatchPosition_shift_exact
      (incomingCore := incomingCore) (overflowCore := overflowCore) (s := s + 1))

/-- In the exact `k`-power same-core regime, the first visible mismatch
position also carries the `exact` endpoint label. -/
theorem sameCoreCompatible_firstVisibleMismatchPosition_endpoint_exact
    {base n stride s incomingActual incomingCore overflowActual overflowCore : ℕ}
    {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hincomingActual :
      (actualCoordinate base n stride hn).isFirstIncomingCarryPosition incomingActual)
    (hincomingCore :
      (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition incomingCore)
    (hoverflowActual :
      (actualCoordinate base n stride hn).isLocalOverflowBoundary overflowActual)
    (hoverflowCore :
      (strippedCoordinate base n stride hn).isLocalOverflowBoundary overflowCore)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hs_le_incoming : s ≤ incomingActual)
    (hs_le_overflow : s ≤ overflowActual)
    (hincoming_order : incomingCore ≤ incomingActual)
    (hoverflow_order : overflowCore ≤ overflowActual) :
    classifyThresholdShiftEndpoint
        (actualCoordinate base n stride hn).remainderK
        (basePrimeSupportFactor base n) s
        (firstVisibleMismatchPosition incomingActual overflowActual)
        (firstVisibleMismatchPosition incomingCore overflowCore) = some .exact := by
  apply classifyThresholdShiftEndpoint_eq_exact
  · exact hfactor
  · exact
      sameCoreCompatible_firstVisibleMismatchPosition_shift_exact
        hcompat hincomingActual hincomingCore hoverflowActual hoverflowCore
        hk hfactor hs_le_incoming hs_le_overflow hincoming_order hoverflow_order

/-- Exact `k`-power same-core ratios force the incoming-carry endpoint label
to be `exact`. -/
theorem sameCoreCompatible_firstIncomingCarryPosition_endpoint_exact
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isFirstIncomingCarryPosition a)
    (hcore : (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hs_le : s ≤ a) :
    classifyThresholdShiftEndpoint
        (actualCoordinate base n stride hn).remainderK
        (basePrimeSupportFactor base n) s a c = some .exact := by
  apply classifyThresholdShiftEndpoint_eq_exact
  · exact hfactor
  · exact sameCoreCompatible_firstIncomingCarryPosition_shift_exact hcompat hactual hcore hk hfactor hs_le

/-- Exact `k`-power same-core ratios force the local-overflow endpoint label
to be `exact`. -/
theorem sameCoreCompatible_localOverflowBoundary_endpoint_exact
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isLocalOverflowBoundary a)
    (hcore : (strippedCoordinate base n stride hn).isLocalOverflowBoundary c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hs_le : s ≤ a) :
    classifyThresholdShiftEndpoint
        (actualCoordinate base n stride hn).remainderK
        (basePrimeSupportFactor base n) s a c = some .exact := by
  apply classifyThresholdShiftEndpoint_eq_exact
  · exact hfactor
  · exact sameCoreCompatible_localOverflowBoundary_shift_exact hcompat hactual hcore hk hfactor hs_le

/-- In the non-power interval regime, the incoming-carry endpoint is `lower`
when the scaled actual coefficient at `a - s` is still below the gap
`B - k`. -/
theorem sameCoreCompatible_firstIncomingCarryPosition_endpoint_lower_of_scaledRawCoefficient_lt_gap
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isFirstIncomingCarryPosition a)
    (hcore : (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hfactor_lower : (actualCoordinate base n stride hn).remainderK ^ s <
      basePrimeSupportFactor base n)
    (hfactor_upper : basePrimeSupportFactor base n <
      (actualCoordinate base n stride hn).remainderK ^ (s + 1))
    (hs_le : s ≤ a)
    (hscaled :
      basePrimeSupportFactor base n *
          (actualCoordinate base n stride hn).rawCoefficient (a - s) <
        (actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK) :
    classifyThresholdShiftEndpoint
        (actualCoordinate base n stride hn).remainderK
        (basePrimeSupportFactor base n) s a c = some .lower := by
  apply classifyThresholdShiftEndpoint_eq_lower
  · exact hfactor_lower
  · exact hfactor_upper
  · exact
      sameCoreCompatible_firstIncomingCarryPosition_shift_lower_of_scaledRawCoefficient_lt_gap
        hcompat hactual hcore hk (le_of_lt hfactor_lower) hs_le hscaled

/-- In the non-power interval regime, the incoming-carry endpoint is `upper`
when the scaled actual coefficient at `a - s` has already reached the gap
`B - k`. -/
theorem sameCoreCompatible_firstIncomingCarryPosition_endpoint_upper_of_gap_le_scaledRawCoefficient
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isFirstIncomingCarryPosition a)
    (hcore : (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hfactor_lower : (actualCoordinate base n stride hn).remainderK ^ s <
      basePrimeSupportFactor base n)
    (hfactor_upper : basePrimeSupportFactor base n <
      (actualCoordinate base n stride hn).remainderK ^ (s + 1))
    (hroom : s + 1 ≤ a)
    (hscaled :
      (actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK ≤
        basePrimeSupportFactor base n *
          (actualCoordinate base n stride hn).rawCoefficient (a - s)) :
    classifyThresholdShiftEndpoint
        (actualCoordinate base n stride hn).remainderK
        (basePrimeSupportFactor base n) s a c = some .upper := by
  apply classifyThresholdShiftEndpoint_eq_upper
  · exact hfactor_lower
  · exact hfactor_upper
  · exact
      sameCoreCompatible_firstIncomingCarryPosition_shift_upper_of_gap_le_scaledRawCoefficient
        hcompat hactual hcore hk hgood hfactor_upper hroom hscaled

/-- In the non-power interval regime, the local-overflow endpoint is `lower`
when the scaled actual coefficient at `a - s` still fits below the block base. -/
theorem sameCoreCompatible_localOverflowBoundary_endpoint_lower_of_scaledRawCoefficient_lt_blockBase
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isLocalOverflowBoundary a)
    (hcore : (strippedCoordinate base n stride hn).isLocalOverflowBoundary c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hfactor_lower : (actualCoordinate base n stride hn).remainderK ^ s <
      basePrimeSupportFactor base n)
    (hfactor_upper : basePrimeSupportFactor base n <
      (actualCoordinate base n stride hn).remainderK ^ (s + 1))
    (hs_le : s ≤ a)
    (hscaled :
      basePrimeSupportFactor base n *
          (actualCoordinate base n stride hn).rawCoefficient (a - s) <
        (actualCoordinate base n stride hn).blockBase) :
    classifyThresholdShiftEndpoint
        (actualCoordinate base n stride hn).remainderK
        (basePrimeSupportFactor base n) s a c = some .lower := by
  apply classifyThresholdShiftEndpoint_eq_lower
  · exact hfactor_lower
  · exact hfactor_upper
  · exact
      sameCoreCompatible_localOverflowBoundary_shift_lower_of_scaledRawCoefficient_lt_blockBase
        hcompat hactual hcore hk (le_of_lt hfactor_lower) hs_le hscaled

/-- In the non-power interval regime, the local-overflow endpoint is `upper`
when the scaled actual coefficient at `a - s` has already reached the block base. -/
theorem sameCoreCompatible_localOverflowBoundary_endpoint_upper_of_blockBase_le_scaledRawCoefficient
    {base n stride s a c : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hactual : (actualCoordinate base n stride hn).isLocalOverflowBoundary a)
    (hcore : (strippedCoordinate base n stride hn).isLocalOverflowBoundary c)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hfactor_lower : (actualCoordinate base n stride hn).remainderK ^ s <
      basePrimeSupportFactor base n)
    (hfactor_upper : basePrimeSupportFactor base n <
      (actualCoordinate base n stride hn).remainderK ^ (s + 1))
    (hroom : s + 1 ≤ a)
    (hscaled :
      (actualCoordinate base n stride hn).blockBase ≤
        basePrimeSupportFactor base n *
          (actualCoordinate base n stride hn).rawCoefficient (a - s)) :
    classifyThresholdShiftEndpoint
        (actualCoordinate base n stride hn).remainderK
        (basePrimeSupportFactor base n) s a c = some .upper := by
  apply classifyThresholdShiftEndpoint_eq_upper
  · exact hfactor_lower
  · exact hfactor_upper
  · exact
      sameCoreCompatible_localOverflowBoundary_shift_upper_of_blockBase_le_scaledRawCoefficient
        hcompat hactual hcore hk hgood hfactor_upper hroom hscaled

/-- In the non-power interval regime, the first visible mismatch endpoint is
`lower` when both the incoming-carry and local-overflow same-core endpoint
criteria certify the lower endpoint. -/
theorem sameCoreCompatible_firstVisibleMismatchPosition_endpoint_lower_of_scaledRawCoefficient_lt_gap_and_lt_blockBase
    {base n stride s incomingActual incomingCore overflowActual overflowCore : ℕ}
    {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hincomingActual :
      (actualCoordinate base n stride hn).isFirstIncomingCarryPosition incomingActual)
    (hincomingCore :
      (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition incomingCore)
    (hoverflowActual :
      (actualCoordinate base n stride hn).isLocalOverflowBoundary overflowActual)
    (hoverflowCore :
      (strippedCoordinate base n stride hn).isLocalOverflowBoundary overflowCore)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hfactor_lower : (actualCoordinate base n stride hn).remainderK ^ s <
      basePrimeSupportFactor base n)
    (hfactor_upper : basePrimeSupportFactor base n <
      (actualCoordinate base n stride hn).remainderK ^ (s + 1))
    (hs_le_incoming : s ≤ incomingActual)
    (hs_le_overflow : s ≤ overflowActual)
    (hincoming_scaled :
      basePrimeSupportFactor base n *
          (actualCoordinate base n stride hn).rawCoefficient (incomingActual - s) <
        (actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK)
    (hoverflow_scaled :
      basePrimeSupportFactor base n *
          (actualCoordinate base n stride hn).rawCoefficient (overflowActual - s) <
        (actualCoordinate base n stride hn).blockBase) :
    classifyThresholdShiftEndpoint
        (actualCoordinate base n stride hn).remainderK
        (basePrimeSupportFactor base n) s
        (firstVisibleMismatchPosition incomingActual overflowActual)
        (firstVisibleMismatchPosition incomingCore overflowCore) = some .lower := by
  apply firstVisibleMismatchPosition_endpoint_lower_of_incomingCarry_lower_and_localOverflow_lower
  · exact
      sameCoreCompatible_firstIncomingCarryPosition_endpoint_lower_of_scaledRawCoefficient_lt_gap
        hcompat hincomingActual hincomingCore hk hfactor_lower hfactor_upper hs_le_incoming
        hincoming_scaled
  · exact
      sameCoreCompatible_localOverflowBoundary_endpoint_lower_of_scaledRawCoefficient_lt_blockBase
        hcompat hoverflowActual hoverflowCore hk hfactor_lower hfactor_upper hs_le_overflow
        hoverflow_scaled

/-- In the non-power interval regime, the first visible mismatch endpoint is
`upper` when both the incoming-carry and local-overflow same-core endpoint
criteria certify the upper endpoint. -/
theorem sameCoreCompatible_firstVisibleMismatchPosition_endpoint_upper_of_gap_le_scaledRawCoefficient_and_blockBase_le_scaledRawCoefficient
    {base n stride s incomingActual incomingCore overflowActual overflowCore : ℕ}
    {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hincomingActual :
      (actualCoordinate base n stride hn).isFirstIncomingCarryPosition incomingActual)
    (hincomingCore :
      (strippedCoordinate base n stride hn).isFirstIncomingCarryPosition incomingCore)
    (hoverflowActual :
      (actualCoordinate base n stride hn).isLocalOverflowBoundary overflowActual)
    (hoverflowCore :
      (strippedCoordinate base n stride hn).isLocalOverflowBoundary overflowCore)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hfactor_lower : (actualCoordinate base n stride hn).remainderK ^ s <
      basePrimeSupportFactor base n)
    (hfactor_upper : basePrimeSupportFactor base n <
      (actualCoordinate base n stride hn).remainderK ^ (s + 1))
    (hroom_incoming : s + 1 ≤ incomingActual)
    (hroom_overflow : s + 1 ≤ overflowActual)
    (hincoming_scaled :
      (actualCoordinate base n stride hn).blockBase -
          (actualCoordinate base n stride hn).remainderK ≤
        basePrimeSupportFactor base n *
          (actualCoordinate base n stride hn).rawCoefficient (incomingActual - s))
    (hoverflow_scaled :
      (actualCoordinate base n stride hn).blockBase ≤
        basePrimeSupportFactor base n *
          (actualCoordinate base n stride hn).rawCoefficient (overflowActual - s)) :
    classifyThresholdShiftEndpoint
        (actualCoordinate base n stride hn).remainderK
        (basePrimeSupportFactor base n) s
        (firstVisibleMismatchPosition incomingActual overflowActual)
        (firstVisibleMismatchPosition incomingCore overflowCore) = some .upper := by
  apply firstVisibleMismatchPosition_endpoint_upper_of_incomingCarry_upper_and_localOverflow_upper
  · exact
      sameCoreCompatible_firstIncomingCarryPosition_endpoint_upper_of_gap_le_scaledRawCoefficient
        hcompat hincomingActual hincomingCore hk hgood hfactor_lower hfactor_upper
        hroom_incoming hincoming_scaled
  · exact
      sameCoreCompatible_localOverflowBoundary_endpoint_upper_of_blockBase_le_scaledRawCoefficient
        hcompat hoverflowActual hoverflowCore hk hgood hfactor_lower hfactor_upper
        hroom_overflow hoverflow_scaled

section Examples

example : strippedPeriodModulus 10 996 = 249 := by
  native_decide

example : basePrimeSupportFactor 10 996 = 4 := by
  native_decide

example :
    (actualCoordinate 10 996 3 (by native_decide)).remainderK < strippedPeriodModulus 10 996 := by
  native_decide

example : sameCoreCompatible 10 996 3 (by native_decide) := by
  unfold sameCoreCompatible actualCoordinate
  native_decide

example : sameCoreCompatible 10 996 3 (by native_decide) := by
  exact sameCoreCompatible_of_goodMode_and_blockBase_lt_modulus_add_stripped
    (base := 10) (n := 996) (stride := 3) (hn := by native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
      native_decide)
    (by native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.blockBase strippedPeriodModulus
      native_decide)

example : sameCoreCompatible 7 56 3 (by native_decide) := by
  exact (sameCoreCompatible_iff_quotientQ_scaling (base := 7) (n := 56) (stride := 3)
    (hn := by native_decide)).2
    ⟨by native_decide, by native_decide⟩

example :
    (strippedCoordinate 10 996 3 (by native_decide)).remainderK =
      (actualCoordinate 10 996 3 (by native_decide)).remainderK := by
  exact sameCoreCompatible_remainderK_eq
    (base := 10) (n := 996) (stride := 3) (hn := by native_decide) (by
      unfold sameCoreCompatible actualCoordinate
      native_decide)

example :
    (strippedCoordinate 10 996 3 (by native_decide)).quotientQ =
      (actualCoordinate 10 996 3 (by native_decide)).quotientQ * basePrimeSupportFactor 10 996 := by
  exact sameCoreCompatible_quotientQ_eq
    (base := 10) (n := 996) (stride := 3) (hn := by native_decide) (by
      unfold sameCoreCompatible actualCoordinate
      native_decide)

example :
    classifyThresholdShiftEndpoint
      (actualCoordinate 10 996 3 (by native_decide)).remainderK
      (basePrimeSupportFactor 10 996) 1 4 3 = some .exact := by
  exact sameCoreCompatible_firstIncomingCarryPosition_endpoint_exact
    (base := 10) (n := 996) (stride := 3) (s := 1) (a := 4) (c := 3)
    (hn := by native_decide)
    (by
      unfold sameCoreCompatible actualCoordinate
      native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.isFirstIncomingCarryPosition
        isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
        BlockCoordinate.blockBase
      native_decide)
    (by
      unfold strippedCoordinate strippedPeriodModulus BlockCoordinate.isFirstIncomingCarryPosition
        isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
        BlockCoordinate.blockBase
      native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)

example :
    firstVisibleMismatchPosition 4 5 = 4 := by
  native_decide

example :
    0 ≤ firstVisibleMismatchPosition 4 5 - firstVisibleMismatchPosition 3 4 ∧
      firstVisibleMismatchPosition 4 5 - firstVisibleMismatchPosition 3 4 ≤ 1 := by
  exact firstVisibleMismatchPosition_shift_interval
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

example :
    classifyThresholdShiftEndpoint
      (actualCoordinate 10 996 3 (by native_decide)).remainderK
      (basePrimeSupportFactor 10 996) 1
      (firstVisibleMismatchPosition 4 4)
      (firstVisibleMismatchPosition 3 3) = some .exact := by
  exact sameCoreCompatible_firstVisibleMismatchPosition_endpoint_exact
    (base := 10) (n := 996) (stride := 3) (s := 1)
    (incomingActual := 4) (incomingCore := 3)
    (overflowActual := 4) (overflowCore := 3)
    (hn := by native_decide)
    (by
      unfold sameCoreCompatible actualCoordinate
      native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.isFirstIncomingCarryPosition
        isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
        BlockCoordinate.blockBase
      native_decide)
    (by
      unfold strippedCoordinate strippedPeriodModulus BlockCoordinate.isFirstIncomingCarryPosition
        isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
        BlockCoordinate.blockBase
      native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.isLocalOverflowBoundary
        isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
        BlockCoordinate.blockBase
      native_decide)
    (by
      unfold strippedCoordinate strippedPeriodModulus BlockCoordinate.isLocalOverflowBoundary
        isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
        BlockCoordinate.blockBase
      native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)

example :
    0 ≤ firstVisibleMismatchPosition 4 4 - firstVisibleMismatchPosition 3 3 ∧
      firstVisibleMismatchPosition 4 4 - firstVisibleMismatchPosition 3 3 ≤ 1 := by
  exact sameCoreCompatible_firstVisibleMismatchPosition_shift_interval
    (base := 10) (n := 498) (stride := 3) (s := 0)
    (incomingActual := 4) (incomingCore := 3)
    (overflowActual := 4) (overflowCore := 3)
    (hn := by native_decide)
    (by
      unfold sameCoreCompatible actualCoordinate
      native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.isFirstIncomingCarryPosition
        isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
        BlockCoordinate.blockBase
      native_decide)
    (by
      unfold strippedCoordinate strippedPeriodModulus BlockCoordinate.isFirstIncomingCarryPosition
        isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
        BlockCoordinate.blockBase
      native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.isLocalOverflowBoundary
        isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
        BlockCoordinate.blockBase
      native_decide)
    (by
      unfold strippedCoordinate strippedPeriodModulus BlockCoordinate.isLocalOverflowBoundary
        isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
        BlockCoordinate.blockBase
      native_decide)
    (by native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
      native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)

example :
    (actualCoordinate 10 996 3 (by native_decide)).lookaheadCertificateHolds 4 0 := by
  exact sameCoreCompatible_lookaheadCertificateHolds_of_core_remainderKPow_lt_modulus_add
    (base := 10) (n := 996) (stride := 3) (s := 1)
    (requestedBlocks := 3) (lookaheadBlocks := 0)
    (hn := by native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
      native_decide)
    (by
      unfold sameCoreCompatible actualCoordinate
      native_decide)
    (by native_decide)
    (by
      unfold strippedCoordinate strippedPeriodModulus BlockCoordinate.remainderK
      native_decide)

example :
    (strippedCoordinate 10 996 3 (by native_decide)).lookaheadCertificateHolds 3 0 := by
  exact sameCoreCompatible_stripped_lookaheadCertificateHolds_of_actual_remainderKPow_lt_modulus_add
    (base := 10) (n := 996) (stride := 3) (s := 1)
    (requestedBlocks := 3) (lookaheadBlocks := 0)
    (hn := by native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
      native_decide)
    (by
      unfold sameCoreCompatible actualCoordinate
      native_decide)
    (by native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.remainderK BlockCoordinate.blockBase
      native_decide)

example :
    (actualCoordinate 10 996 3 (by native_decide)).lookaheadCertificateHolds 8 1 ↔
      (strippedCoordinate 10 996 3 (by native_decide)).lookaheadCertificateHolds 7 1 := by
  exact sameCoreCompatible_lookaheadCertificateHolds_iff_add_exact
    (base := 10) (n := 996) (stride := 3) (s := 1)
    (requestedBlocks := 7) (lookaheadBlocks := 1)
    (hn := by native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
      native_decide)
    (by
      unfold sameCoreCompatible actualCoordinate
      native_decide)
    (by native_decide)

example :
    (actualCoordinate 12 20 2 (by native_decide)).lookaheadCertificateHolds 8 3 ↔
      (strippedCoordinate 12 20 2 (by native_decide)).lookaheadCertificateHolds 7 3 := by
  exact sameCoreCompatible_lookaheadCertificateHolds_iff_add_exact
    (base := 12) (n := 20) (stride := 2) (s := 1)
    (requestedBlocks := 7) (lookaheadBlocks := 3)
    (hn := by native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
      native_decide)
    (by
      unfold sameCoreCompatible actualCoordinate
      native_decide)
    (by native_decide)

example :
    classifyThresholdShiftEndpoint
      (actualCoordinate 12 10 2 (by native_decide)).remainderK
      (basePrimeSupportFactor 12 10) 0 1 1 = some .lower := by
  exact
    sameCoreCompatible_firstIncomingCarryPosition_endpoint_lower_of_scaledRawCoefficient_lt_gap
      (base := 12) (n := 10) (stride := 2) (s := 0) (a := 1) (c := 1)
      (hn := by native_decide)
      (by
        unfold sameCoreCompatible actualCoordinate
        native_decide)
      (by
        unfold actualCoordinate BlockCoordinate.isFirstIncomingCarryPosition
          isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
          BlockCoordinate.blockBase
        native_decide)
      (by
        unfold strippedCoordinate strippedPeriodModulus BlockCoordinate.isFirstIncomingCarryPosition
          isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
          BlockCoordinate.blockBase
        native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by
        unfold actualCoordinate BlockCoordinate.rawCoefficient BlockCoordinate.quotientQ
          BlockCoordinate.remainderK BlockCoordinate.blockBase
        native_decide)

example :
    classifyThresholdShiftEndpoint
      (actualCoordinate 12 70 2 (by native_decide)).remainderK
      (basePrimeSupportFactor 12 70) 0 3 2 = some .upper := by
  exact
    sameCoreCompatible_firstIncomingCarryPosition_endpoint_upper_of_gap_le_scaledRawCoefficient
      (base := 12) (n := 70) (stride := 2) (s := 0) (a := 3) (c := 2)
      (hn := by native_decide)
      (by
        unfold sameCoreCompatible actualCoordinate
        native_decide)
      (by
        unfold actualCoordinate BlockCoordinate.isFirstIncomingCarryPosition
          isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
          BlockCoordinate.blockBase
        native_decide)
      (by
        unfold strippedCoordinate strippedPeriodModulus BlockCoordinate.isFirstIncomingCarryPosition
          isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
          BlockCoordinate.blockBase
        native_decide)
      (by native_decide)
      (by
        unfold actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
        native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by
        unfold actualCoordinate BlockCoordinate.rawCoefficient BlockCoordinate.quotientQ
          BlockCoordinate.remainderK BlockCoordinate.blockBase
        native_decide)

example :
    classifyThresholdShiftEndpoint
      (actualCoordinate 12 20 2 (by native_decide)).remainderK
      (basePrimeSupportFactor 12 20) 1 2 1 = some .exact := by
  exact sameCoreCompatible_firstIncomingCarryPosition_endpoint_exact
    (base := 12) (n := 20) (stride := 2) (s := 1) (a := 2) (c := 1)
    (hn := by native_decide)
    (by
      unfold sameCoreCompatible actualCoordinate
      native_decide)
    (by
      unfold actualCoordinate BlockCoordinate.isFirstIncomingCarryPosition
        isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
        BlockCoordinate.blockBase
      native_decide)
    (by
      unfold strippedCoordinate strippedPeriodModulus BlockCoordinate.isFirstIncomingCarryPosition
        isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
        BlockCoordinate.blockBase
      native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)

example :
    classifyThresholdShiftEndpoint
      (actualCoordinate 12 10 2 (by native_decide)).remainderK
      (basePrimeSupportFactor 12 10) 0
      (firstVisibleMismatchPosition 1 1)
      (firstVisibleMismatchPosition 1 1) = some .lower := by
  exact
    sameCoreCompatible_firstVisibleMismatchPosition_endpoint_lower_of_scaledRawCoefficient_lt_gap_and_lt_blockBase
      (base := 12) (n := 10) (stride := 2) (s := 0)
      (incomingActual := 1) (incomingCore := 1)
      (overflowActual := 1) (overflowCore := 1)
      (hn := by native_decide)
      (by
        unfold sameCoreCompatible actualCoordinate
        native_decide)
      (by
        unfold actualCoordinate BlockCoordinate.isFirstIncomingCarryPosition
          isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
          BlockCoordinate.blockBase
        native_decide)
      (by
        unfold strippedCoordinate strippedPeriodModulus BlockCoordinate.isFirstIncomingCarryPosition
          isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
          BlockCoordinate.blockBase
        native_decide)
      (by
        unfold actualCoordinate BlockCoordinate.isLocalOverflowBoundary
          isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
          BlockCoordinate.blockBase
        native_decide)
      (by
        unfold strippedCoordinate strippedPeriodModulus BlockCoordinate.isLocalOverflowBoundary
          isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
          BlockCoordinate.blockBase
        native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)

example :
    classifyThresholdShiftEndpoint
      (actualCoordinate 12 70 2 (by native_decide)).remainderK
      (basePrimeSupportFactor 12 70) 0
      (firstVisibleMismatchPosition 3 3)
      (firstVisibleMismatchPosition 2 2) = some .upper := by
  exact
    sameCoreCompatible_firstVisibleMismatchPosition_endpoint_upper_of_gap_le_scaledRawCoefficient_and_blockBase_le_scaledRawCoefficient
      (base := 12) (n := 70) (stride := 2) (s := 0)
      (incomingActual := 3) (incomingCore := 2)
      (overflowActual := 3) (overflowCore := 2)
      (hn := by native_decide)
      (by
        unfold sameCoreCompatible actualCoordinate
        native_decide)
      (by
        unfold actualCoordinate BlockCoordinate.isFirstIncomingCarryPosition
          isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
          BlockCoordinate.blockBase
        native_decide)
      (by
        unfold strippedCoordinate strippedPeriodModulus BlockCoordinate.isFirstIncomingCarryPosition
          isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
          BlockCoordinate.blockBase
        native_decide)
      (by
        unfold actualCoordinate BlockCoordinate.isLocalOverflowBoundary
          isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
          BlockCoordinate.blockBase
        native_decide)
      (by
        unfold strippedCoordinate strippedPeriodModulus BlockCoordinate.isLocalOverflowBoundary
          isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
          BlockCoordinate.blockBase
        native_decide)
      (by native_decide)
      (by
        unfold actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
        native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by
        unfold actualCoordinate BlockCoordinate.rawCoefficient BlockCoordinate.quotientQ
          BlockCoordinate.remainderK BlockCoordinate.blockBase
        native_decide)
      (by
        unfold actualCoordinate BlockCoordinate.rawCoefficient BlockCoordinate.quotientQ
          BlockCoordinate.remainderK BlockCoordinate.blockBase
        native_decide)

end Examples

end QRTour
