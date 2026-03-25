/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.CarryTransducer
import Mathlib.Tactic

/-!
# Exact Visibility Boundaries

This module formalizes the exact incoming-carry boundary and the shared
adjacent-threshold law used in same-core visibility comparisons.
-/

namespace QRTour

/-- A geometric threshold boundary at index `j`: the `j`th coefficient is still
below the threshold, but the next one reaches it. -/
def isGeometricThresholdBoundary (threshold q k j : ℕ) : Prop :=
  q * k ^ j < threshold ∧ threshold ≤ q * k ^ (j + 1)

/-- Any later valid upper bound forces the threshold boundary index to be no larger. -/
theorem geometricThresholdBoundary_index_le_of_upper
    {threshold q k j n : ℕ}
    (hk : 1 < k)
    (hboundary : isGeometricThresholdBoundary threshold q k j)
    (hupper : threshold ≤ q * k ^ (n + 1)) :
    j ≤ n := by
  by_contra hjn
  have hnj : n + 1 ≤ j := by omega
  have hpow : k ^ (n + 1) ≤ k ^ j := Nat.pow_le_pow_right hk.le hnj
  have hmul : q * k ^ (n + 1) ≤ q * k ^ j := Nat.mul_le_mul_left q hpow
  exact not_le_of_gt hboundary.1 (le_trans hupper hmul)

/-- Any earlier strict lower bound forces the threshold boundary index to be no smaller. -/
theorem geometricThresholdBoundary_le_index_of_lower_lt
    {threshold q k j n : ℕ}
    (hk : 1 < k)
    (hboundary : isGeometricThresholdBoundary threshold q k j)
    (hlower : q * k ^ n < threshold) :
    n ≤ j := by
  by_contra hnj
  have hjn : j + 1 ≤ n := by omega
  have hpow : k ^ (j + 1) ≤ k ^ n := Nat.pow_le_pow_right hk.le hjn
  have hmul : q * k ^ (j + 1) ≤ q * k ^ n := Nat.mul_le_mul_left q hpow
  exact not_le_of_gt hlower (le_trans hboundary.2 hmul)

/-- The exact incoming carry into block `j`, written as a natural-number quotient. -/
def BlockCoordinate.incomingCarry (C : BlockCoordinate) (j : ℕ) : ℕ :=
  C.rawCoefficient (j + 1) / (C.blockBase - C.remainderK)

/-- The first incoming-carry boundary occurs when the next raw coefficient crosses `B - k`. -/
def BlockCoordinate.isFirstIncomingCarryPosition (C : BlockCoordinate) (j : ℕ) : Prop :=
  isGeometricThresholdBoundary (C.blockBase - C.remainderK) C.quotientQ C.remainderK j

/-- The adjacent local-overflow boundary: block `j` still fits, but block `j+1` does not. -/
def BlockCoordinate.isLocalOverflowBoundary (C : BlockCoordinate) (j : ℕ) : Prop :=
  isGeometricThresholdBoundary C.blockBase C.quotientQ C.remainderK j

/-- The truncated visible-prefix quotient obtained from the finite body term
through `requestedBlocks + lookaheadBlocks - 1`. -/
def BlockCoordinate.truncatedVisiblePrefixValue
    (C : BlockCoordinate) (requestedBlocks lookaheadBlocks : ℕ) : ℕ :=
  C.bodyTerm (requestedBlocks + lookaheadBlocks) / C.blockBase ^ lookaheadBlocks

/-- The base-`B^L` remainder of the same truncated visible prefix. -/
def BlockCoordinate.truncatedVisiblePrefixRemainder
    (C : BlockCoordinate) (requestedBlocks lookaheadBlocks : ℕ) : ℕ :=
  C.bodyTerm (requestedBlocks + lookaheadBlocks) % C.blockBase ^ lookaheadBlocks

/-- The exact gap numerator from the truncated prefix to the next integer. -/
def BlockCoordinate.lookaheadGapNumerator
    (C : BlockCoordinate) (requestedBlocks lookaheadBlocks : ℕ) : ℕ :=
  let remainder := C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks
  let modulus := C.blockBase ^ lookaheadBlocks
  if h : remainder = 0 then modulus else modulus - remainder

/-- Exact finite-window stabilization certificate for the first `requestedBlocks`
displayed blocks after `lookaheadBlocks` extra carried blocks. -/
def BlockCoordinate.lookaheadCertificateHolds
    (C : BlockCoordinate) (requestedBlocks lookaheadBlocks : ℕ) : Prop :=
  C.rawCoefficient (requestedBlocks + lookaheadBlocks) <
    C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK)

theorem BlockCoordinate.truncatedVisiblePrefixValue_mul_blockBasePow_add_remainder
    (C : BlockCoordinate) (requestedBlocks lookaheadBlocks : ℕ) :
    C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks * C.blockBase ^ lookaheadBlocks +
      C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks =
        C.bodyTerm (requestedBlocks + lookaheadBlocks) := by
  unfold BlockCoordinate.truncatedVisiblePrefixValue BlockCoordinate.truncatedVisiblePrefixRemainder
  simpa [Nat.mul_comm] using (Nat.div_add_mod (C.bodyTerm (requestedBlocks + lookaheadBlocks))
    (C.blockBase ^ lookaheadBlocks))

theorem BlockCoordinate.truncatedVisiblePrefixRemainder_lt_blockBasePow
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks <
      C.blockBase ^ lookaheadBlocks := by
  unfold BlockCoordinate.truncatedVisiblePrefixRemainder
  exact Nat.mod_lt _ (pow_pos (C.blockBase_pos_of_goodMode hgood) _)

theorem BlockCoordinate.lookaheadGapNumerator_pos
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    0 < C.lookaheadGapNumerator requestedBlocks lookaheadBlocks := by
  simp only [BlockCoordinate.lookaheadGapNumerator]
  dsimp
  split_ifs with hzero
  · exact pow_pos (C.blockBase_pos_of_goodMode hgood) _
  ·
    have hlt :
        C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks <
          C.blockBase ^ lookaheadBlocks :=
      C.truncatedVisiblePrefixRemainder_lt_blockBasePow hgood requestedBlocks lookaheadBlocks
    exact Nat.sub_pos_of_lt hlt

theorem BlockCoordinate.lookaheadGapNumerator_le_blockBasePow
    (C : BlockCoordinate) (requestedBlocks lookaheadBlocks : ℕ) :
    C.lookaheadGapNumerator requestedBlocks lookaheadBlocks ≤ C.blockBase ^ lookaheadBlocks := by
  simp only [BlockCoordinate.lookaheadGapNumerator]
  dsimp
  split_ifs with hzero
  · exact le_rfl
  · exact Nat.sub_le _ _

theorem BlockCoordinate.truncatedVisiblePrefixValue_balance
    (C : BlockCoordinate) (requestedBlocks lookaheadBlocks : ℕ) :
    C.blockBase ^ lookaheadBlocks *
        (C.blockBase ^ requestedBlocks - C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks * C.modulus) =
      C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * C.modulus +
        C.remainderK ^ (requestedBlocks + lookaheadBlocks) := by
  let q0 := C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks
  let rem := C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks
  let Bpow := C.blockBase ^ lookaheadBlocks
  have hdecomp :
      (q0 * Bpow + rem) * C.modulus = C.bodyTerm (requestedBlocks + lookaheadBlocks) * C.modulus := by
    simpa [q0, rem, Bpow, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      congrArg (fun t => t * C.modulus)
        (C.truncatedVisiblePrefixValue_mul_blockBasePow_add_remainder requestedBlocks lookaheadBlocks)
  have hbody :
      C.bodyTerm (requestedBlocks + lookaheadBlocks) * C.modulus =
        Bpow * C.blockBase ^ requestedBlocks - C.remainderK ^ (requestedBlocks + lookaheadBlocks) := by
    simpa [Bpow, pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      C.bodyTerm_mul_modulus_eq (requestedBlocks + lookaheadBlocks)
  rw [hbody] at hdecomp
  calc
    C.blockBase ^ lookaheadBlocks *
        (C.blockBase ^ requestedBlocks - C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks * C.modulus)
      = C.blockBase ^ lookaheadBlocks * C.blockBase ^ requestedBlocks -
          C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks * C.blockBase ^ lookaheadBlocks * C.modulus := by
            rw [Nat.mul_sub_left_distrib]
            ac_rfl
    _ = C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * C.modulus +
          C.remainderK ^ (requestedBlocks + lookaheadBlocks) := by
            dsimp [q0, rem, Bpow] at hdecomp
            omega

theorem BlockCoordinate.lookaheadCertificateHolds_iff_gap
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks ↔
      C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
        C.rawCoefficient (requestedBlocks + lookaheadBlocks) <
          C.blockBase ^ lookaheadBlocks * (C.blockBase - C.remainderK) := by
  simp only [BlockCoordinate.lookaheadCertificateHolds, BlockCoordinate.lookaheadGapNumerator]
  dsimp
  split_ifs with hzero
  · simp [hzero]
  ·
    constructor
    · intro hlt
      calc
        C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
            C.rawCoefficient (requestedBlocks + lookaheadBlocks)
            <
              C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
                (C.blockBase ^ lookaheadBlocks - C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks) *
                  (C.blockBase - C.remainderK) := by
                    exact Nat.add_lt_add_left hlt _
        _ = C.blockBase ^ lookaheadBlocks * (C.blockBase - C.remainderK) := by
              rw [Nat.add_comm, ← Nat.add_mul, Nat.sub_add_cancel
                (Nat.le_of_lt (C.truncatedVisiblePrefixRemainder_lt_blockBasePow hgood requestedBlocks lookaheadBlocks))]
    · intro hlt
      have hlt' :
          C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
            C.rawCoefficient (requestedBlocks + lookaheadBlocks) <
              C.blockBase ^ lookaheadBlocks * (C.blockBase - C.remainderK) := by
        simpa [Nat.add_comm] using hlt
      have hsum :
          C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
            C.rawCoefficient (requestedBlocks + lookaheadBlocks) <
              C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
                (C.blockBase ^ lookaheadBlocks - C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks) *
                  (C.blockBase - C.remainderK) := by
        rw [Nat.add_comm, ← Nat.add_mul, Nat.sub_add_cancel
          (Nat.le_of_lt (C.truncatedVisiblePrefixRemainder_lt_blockBasePow hgood requestedBlocks lookaheadBlocks))] at hlt'
        exact hlt'
      have hsub :
          C.rawCoefficient (requestedBlocks + lookaheadBlocks) <
            (C.blockBase ^ lookaheadBlocks - C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks) *
              (C.blockBase - C.remainderK) := by
        exact Nat.lt_of_add_lt_add_left hsum
      simpa [hzero] using hsub

theorem BlockCoordinate.emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_gap
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    C.emittedPrefixValue requestedBlocks = C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks ↔
      C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
        C.rawCoefficient (requestedBlocks + lookaheadBlocks) <
          C.blockBase ^ lookaheadBlocks * (C.blockBase - C.remainderK) := by
  let q0 := C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks
  let rem := C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks
  let Bpow := C.blockBase ^ lookaheadBlocks
  have hBpow_pos : 0 < Bpow := by
    dsimp [Bpow]
    exact pow_pos (C.blockBase_pos_of_goodMode hgood) _
  have hqpos : 0 < C.quotientQ := C.quotientQ_pos_of_goodMode hgood
  have hgap :
      C.blockBase - C.remainderK = C.quotientQ * C.modulus := by
    exact C.quotientQ_mul_modulus_eq_blockBase_sub_remainderK.symm
  have hbalance :
      Bpow * (C.blockBase ^ requestedBlocks - q0 * C.modulus) =
        rem * C.modulus + C.remainderK ^ (requestedBlocks + lookaheadBlocks) := by
    simpa [q0, rem, Bpow] using
      C.truncatedVisiblePrefixValue_balance requestedBlocks lookaheadBlocks
  constructor
  · intro heq
    have hpow_decomp :
        C.blockBase ^ requestedBlocks =
          q0 * C.modulus + C.blockBase ^ requestedBlocks % C.modulus := by
      dsimp [q0]
      rw [← heq, BlockCoordinate.emittedPrefixValue]
      simpa [Nat.mul_comm] using
        (Nat.div_add_mod (C.blockBase ^ requestedBlocks) C.modulus).symm
    have hlt_div : C.blockBase ^ requestedBlocks < (q0 + 1) * C.modulus := by
      rw [hpow_decomp]
      have hmod_lt : C.blockBase ^ requestedBlocks % C.modulus < C.modulus :=
        Nat.mod_lt _ C.modulus_pos
      have :
          q0 * C.modulus + C.blockBase ^ requestedBlocks % C.modulus <
            q0 * C.modulus + C.modulus := by
        exact Nat.add_lt_add_left hmod_lt _
      simpa [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
    have hlt_mul :
        Bpow * C.blockBase ^ requestedBlocks < Bpow * ((q0 + 1) * C.modulus) :=
      Nat.mul_lt_mul_of_pos_left hlt_div hBpow_pos
    have hsum :
        Bpow * C.blockBase ^ requestedBlocks =
          q0 * (Bpow * C.modulus) + (rem * C.modulus + C.remainderK ^ (requestedBlocks + lookaheadBlocks)) := by
      calc
        Bpow * C.blockBase ^ requestedBlocks
          = Bpow * (q0 * C.modulus) + Bpow * (C.blockBase ^ requestedBlocks - q0 * C.modulus) := by
              rw [Nat.mul_sub_left_distrib]
              omega
        _ = q0 * (Bpow * C.modulus) + (rem * C.modulus + C.remainderK ^ (requestedBlocks + lookaheadBlocks)) := by
              rw [hbalance]
              ac_rfl
    rw [hsum] at hlt_mul
    have hsmall :
        rem * C.modulus + C.remainderK ^ (requestedBlocks + lookaheadBlocks) < Bpow * C.modulus := by
      have htarget :
          Bpow * ((q0 + 1) * C.modulus) = q0 * (Bpow * C.modulus) + Bpow * C.modulus := by
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      rw [htarget] at hlt_mul
      exact Nat.lt_of_add_lt_add_left hlt_mul
    have hmul :
        C.quotientQ * (rem * C.modulus + C.remainderK ^ (requestedBlocks + lookaheadBlocks)) <
          C.quotientQ * (Bpow * C.modulus) :=
      Nat.mul_lt_mul_of_pos_left hsmall hqpos
    simpa [hgap, BlockCoordinate.rawCoefficient, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using hmul
  · intro hgapForm
    have hmul :
        C.quotientQ * (rem * C.modulus + C.remainderK ^ (requestedBlocks + lookaheadBlocks)) <
          C.quotientQ * (Bpow * C.modulus) := by
      simpa [hgap, BlockCoordinate.rawCoefficient, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        using hgapForm
    have hsmall :
        rem * C.modulus + C.remainderK ^ (requestedBlocks + lookaheadBlocks) < Bpow * C.modulus := by
      exact Nat.lt_of_mul_lt_mul_left hmul
    have hlt_div : C.blockBase ^ requestedBlocks < (q0 + 1) * C.modulus := by
      have hsum :
          Bpow * C.blockBase ^ requestedBlocks =
            q0 * (Bpow * C.modulus) + (rem * C.modulus + C.remainderK ^ (requestedBlocks + lookaheadBlocks)) := by
        calc
          Bpow * C.blockBase ^ requestedBlocks
            = Bpow * (q0 * C.modulus) + Bpow * (C.blockBase ^ requestedBlocks - q0 * C.modulus) := by
                rw [Nat.mul_sub_left_distrib]
                omega
          _ = q0 * (Bpow * C.modulus) + (rem * C.modulus + C.remainderK ^ (requestedBlocks + lookaheadBlocks)) := by
                rw [hbalance]
                ac_rfl
      have hlt_mul :
          Bpow * C.blockBase ^ requestedBlocks < Bpow * ((q0 + 1) * C.modulus) := by
        rw [hsum]
        have htarget :
            Bpow * ((q0 + 1) * C.modulus) = q0 * (Bpow * C.modulus) + Bpow * C.modulus := by
          simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        rw [htarget]
        exact Nat.add_lt_add_left hsmall _
      exact (Nat.mul_lt_mul_left hBpow_pos).1 hlt_mul
    have hge_div : q0 * C.modulus ≤ C.blockBase ^ requestedBlocks := by
      have hq0_le_body : q0 * Bpow ≤ C.bodyTerm (requestedBlocks + lookaheadBlocks) := by
        have := Nat.div_mul_le_self (C.bodyTerm (requestedBlocks + lookaheadBlocks)) (C.blockBase ^ lookaheadBlocks)
        simpa [q0, Bpow, Nat.mul_comm] using this
      have hq0_mod :
          q0 * Bpow * C.modulus ≤ C.bodyTerm (requestedBlocks + lookaheadBlocks) * C.modulus := by
        exact Nat.mul_le_mul_right _ hq0_le_body
      have hmul' :
          Bpow * (q0 * C.modulus) ≤ Bpow * C.blockBase ^ requestedBlocks := by
        calc
          Bpow * (q0 * C.modulus) = q0 * Bpow * C.modulus := by ac_rfl
          _ ≤ C.bodyTerm (requestedBlocks + lookaheadBlocks) * C.modulus := hq0_mod
          _ = Bpow * C.blockBase ^ requestedBlocks - C.remainderK ^ (requestedBlocks + lookaheadBlocks) := by
              rw [C.bodyTerm_mul_modulus_eq (requestedBlocks + lookaheadBlocks)]
              simp [Bpow, pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ ≤ Bpow * C.blockBase ^ requestedBlocks := Nat.sub_le _ _
      exact Nat.le_of_mul_le_mul_left hmul' hBpow_pos
    apply le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul C.modulus_pos).2 hlt_div)
    · exact (Nat.le_div_iff_mul_le C.modulus_pos).2 hge_div

theorem BlockCoordinate.emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_lookaheadCertificate
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    C.emittedPrefixValue requestedBlocks = C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks ↔
      C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks := by
  rw [C.emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_gap hgood,
    C.lookaheadCertificateHolds_iff_gap hgood]

theorem BlockCoordinate.lookaheadCertificateHolds_of_remainderK_pow_lt_modulus
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ)
    (hsmall : C.remainderK ^ (requestedBlocks + lookaheadBlocks) < C.modulus) :
    C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  have hq :
      C.rawCoefficient (requestedBlocks + lookaheadBlocks) < C.blockBase - C.remainderK := by
    unfold BlockCoordinate.rawCoefficient
    rw [← C.quotientQ_mul_modulus_eq_blockBase_sub_remainderK]
    exact Nat.mul_lt_mul_of_pos_left hsmall (C.quotientQ_pos_of_goodMode hgood)
  have hgap_le :
      C.blockBase - C.remainderK ≤
        C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) := by
    simpa using Nat.mul_le_mul_right (C.blockBase - C.remainderK)
      (Nat.succ_le_of_lt (C.lookaheadGapNumerator_pos hgood requestedBlocks lookaheadBlocks))
  exact lt_of_lt_of_le hq hgap_le

/-- Claim `incoming_carry_position_formula`: the incoming carry is `floor(q*k^(j+1)/(B-k))`. -/
theorem BlockCoordinate.incomingCarry_formula (C : BlockCoordinate) (j : ℕ) :
    C.incomingCarry j =
      (C.quotientQ * C.remainderK ^ (j + 1)) / (C.blockBase - C.remainderK) := by
  simp [BlockCoordinate.incomingCarry, BlockCoordinate.rawCoefficient]

/-- Incoming carry is positive exactly when the next raw coefficient reaches `B - k`. -/
theorem BlockCoordinate.incomingCarry_pos_iff
    (C : BlockCoordinate) (hgood : C.goodMode) (j : ℕ) :
    0 < C.incomingCarry j ↔ C.blockBase - C.remainderK ≤ C.rawCoefficient (j + 1) := by
  have hgap_pos : 0 < C.blockBase - C.remainderK := by
    exact Nat.sub_pos_of_lt (C.remainderK_lt_blockBase hgood)
  constructor
  · intro hcarry
    by_contra hlt
    have hzero : C.incomingCarry j = 0 := by
      unfold BlockCoordinate.incomingCarry
      exact Nat.div_eq_of_lt (lt_of_not_ge hlt)
    omega
  · intro hthreshold
    unfold BlockCoordinate.incomingCarry
    exact Nat.div_pos hthreshold hgap_pos

/-- The first incoming-carry position is exactly the least threshold-crossing index. -/
theorem BlockCoordinate.isFirstIncomingCarryPosition_iff
    (C : BlockCoordinate) (j : ℕ) :
    C.isFirstIncomingCarryPosition j ↔
      C.rawCoefficient j < C.blockBase - C.remainderK ∧
        C.blockBase - C.remainderK ≤ C.rawCoefficient (j + 1) := by
  simp [BlockCoordinate.isFirstIncomingCarryPosition, isGeometricThresholdBoundary,
    BlockCoordinate.rawCoefficient]

/-- The same first incoming-carry boundary, phrased using positivity of the carry term. -/
theorem BlockCoordinate.isFirstIncomingCarryPosition_iff_carry
    (C : BlockCoordinate) (hgood : C.goodMode) (j : ℕ) :
    C.isFirstIncomingCarryPosition j ↔
      C.rawCoefficient j < C.blockBase - C.remainderK ∧ 0 < C.incomingCarry j := by
  rw [C.isFirstIncomingCarryPosition_iff, C.incomingCarry_pos_iff hgood]

/-- Same-core threshold boundaries can shift by only `s` or `s+1` when the `q`-ratio
lies between consecutive powers of `k`. -/
theorem geometricThreshold_shift_interval
    {threshold qActual qCore k r s a c : ℕ}
    (hk : 1 < k)
    (hqActual : 0 < qActual)
    (hactual : isGeometricThresholdBoundary threshold qActual k a)
    (hcore : isGeometricThresholdBoundary threshold qCore k c)
    (hqCore : qCore = qActual * r)
    (hr_lower : k ^ s ≤ r)
    (hr_upper : r < k ^ (s + 1))
    (hroom : s + 1 ≤ a) :
    s ≤ a - c ∧ a - c ≤ s + 1 := by
  have hcore_le : c ≤ a - s := by
    apply geometricThresholdBoundary_index_le_of_upper hk hcore
    calc
      threshold ≤ qActual * k ^ (a + 1) := hactual.2
      _ = (qActual * k ^ s) * k ^ ((a - s) + 1) := by
        have hexp : a + 1 = s + ((a - s) + 1) := by omega
        rw [hexp, pow_add]
        ac_rfl
      _ ≤ (qActual * r) * k ^ ((a - s) + 1) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hr_lower)
      _ = qCore * k ^ ((a - s) + 1) := by
        rw [hqCore]
  have hcore_ge : a - (s + 1) ≤ c := by
    apply geometricThresholdBoundary_le_index_of_lower_lt hk hcore
    calc
      qCore * k ^ (a - (s + 1))
          = (qActual * r) * k ^ (a - (s + 1)) := by
              rw [hqCore]
      _ < (qActual * k ^ (s + 1)) * k ^ (a - (s + 1)) := by
        have hqr : qActual * r < qActual * k ^ (s + 1) :=
          Nat.mul_lt_mul_of_pos_left hr_upper hqActual
        exact Nat.mul_lt_mul_of_pos_right hqr (pow_pos (Nat.zero_lt_of_lt hk) _)
      _ = qActual * k ^ a := by
        calc
          (qActual * k ^ (s + 1)) * k ^ (a - (s + 1))
              = qActual * (k ^ (s + 1) * k ^ (a - (s + 1))) := by
                  ac_rfl
          _ = qActual * k ^ a := by
            congr 1
            rw [← pow_add]
            have hexp : (s + 1) + (a - (s + 1)) = a := by omega
            simp [hexp]
      _ < threshold := hactual.1
  omega

/-- Exact `k`-power ratios force an exact threshold shift. -/
theorem geometricThreshold_shift_exact
    {threshold qActual qCore k s a c : ℕ}
    (hk : 1 < k)
    (hactual : isGeometricThresholdBoundary threshold qActual k a)
    (hcore : isGeometricThresholdBoundary threshold qCore k c)
    (hqCore : qCore = qActual * k ^ s)
    (hs_le : s ≤ a) :
    a - c = s := by
  have hcore_le : c ≤ a - s := by
    apply geometricThresholdBoundary_index_le_of_upper hk hcore
    calc
      threshold ≤ qActual * k ^ (a + 1) := hactual.2
      _ = qCore * k ^ ((a - s) + 1) := by
        rw [hqCore]
        have hexp : a + 1 = s + ((a - s) + 1) := by omega
        rw [hexp, pow_add]
        ac_rfl
  have hcore_ge : a - s ≤ c := by
    apply geometricThresholdBoundary_le_index_of_lower_lt hk hcore
    calc
      qCore * k ^ (a - s) = qActual * k ^ a := by
        rw [hqCore]
        calc
          (qActual * k ^ s) * k ^ (a - s) = qActual * (k ^ s * k ^ (a - s)) := by
            ac_rfl
          _ = qActual * k ^ a := by
            congr 1
            rw [← pow_add]
            have hexp : s + (a - s) = a := by omega
            simp [hexp]
      _ < threshold := hactual.1
  omega

/-- Same-core incoming-carry positions satisfy the threshold-shift interval law. -/
theorem BlockCoordinate.firstIncomingCarryPosition_shift_interval
    {actual core : BlockCoordinate} {r s a c : ℕ}
    (hsharedB : actual.blockBase = core.blockBase)
    (hsharedK : actual.remainderK = core.remainderK)
    (hactual : actual.isFirstIncomingCarryPosition a)
    (hcore : core.isFirstIncomingCarryPosition c)
    (hk : 1 < actual.remainderK)
    (hqActual : 0 < actual.quotientQ)
    (hqCore : core.quotientQ = actual.quotientQ * r)
    (hr_lower : actual.remainderK ^ s ≤ r)
    (hr_upper : r < actual.remainderK ^ (s + 1))
    (hroom : s + 1 ≤ a) :
    s ≤ a - c ∧ a - c ≤ s + 1 := by
  have hactual' :
      isGeometricThresholdBoundary (actual.blockBase - actual.remainderK)
        actual.quotientQ actual.remainderK a := by
    simpa [BlockCoordinate.isFirstIncomingCarryPosition] using hactual
  have hcore' :
      isGeometricThresholdBoundary (actual.blockBase - actual.remainderK)
        core.quotientQ actual.remainderK c := by
    simpa [BlockCoordinate.isFirstIncomingCarryPosition, hsharedB, hsharedK] using hcore
  exact geometricThreshold_shift_interval hk hqActual hactual' hcore' hqCore
    hr_lower hr_upper hroom

/-- Exact `k`-power same-core ratios force an exact incoming-carry shift. -/
theorem BlockCoordinate.firstIncomingCarryPosition_shift_exact
    {actual core : BlockCoordinate} {s a c : ℕ}
    (hsharedB : actual.blockBase = core.blockBase)
    (hsharedK : actual.remainderK = core.remainderK)
    (hactual : actual.isFirstIncomingCarryPosition a)
    (hcore : core.isFirstIncomingCarryPosition c)
    (hk : 1 < actual.remainderK)
    (hqCore : core.quotientQ = actual.quotientQ * actual.remainderK ^ s)
    (hs_le : s ≤ a) :
    a - c = s := by
  have hactual' :
      isGeometricThresholdBoundary (actual.blockBase - actual.remainderK)
        actual.quotientQ actual.remainderK a := by
    simpa [BlockCoordinate.isFirstIncomingCarryPosition] using hactual
  have hcore' :
      isGeometricThresholdBoundary (actual.blockBase - actual.remainderK)
        core.quotientQ actual.remainderK c := by
    simpa [BlockCoordinate.isFirstIncomingCarryPosition, hsharedB, hsharedK] using hcore
  exact geometricThreshold_shift_exact hk hactual' hcore' hqCore hs_le

/-- The same interval law applies to adjacent local-overflow boundaries. -/
theorem BlockCoordinate.localOverflowBoundary_shift_interval
    {actual core : BlockCoordinate} {r s a c : ℕ}
    (hsharedB : actual.blockBase = core.blockBase)
    (hsharedK : actual.remainderK = core.remainderK)
    (hactual : actual.isLocalOverflowBoundary a)
    (hcore : core.isLocalOverflowBoundary c)
    (hk : 1 < actual.remainderK)
    (hqActual : 0 < actual.quotientQ)
    (hqCore : core.quotientQ = actual.quotientQ * r)
    (hr_lower : actual.remainderK ^ s ≤ r)
    (hr_upper : r < actual.remainderK ^ (s + 1))
    (hroom : s + 1 ≤ a) :
    s ≤ a - c ∧ a - c ≤ s + 1 := by
  have hactual' :
      isGeometricThresholdBoundary actual.blockBase actual.quotientQ actual.remainderK a := by
    simpa [BlockCoordinate.isLocalOverflowBoundary] using hactual
  have hcore' :
      isGeometricThresholdBoundary actual.blockBase core.quotientQ actual.remainderK c := by
    simpa [BlockCoordinate.isLocalOverflowBoundary, hsharedB, hsharedK] using hcore
  exact geometricThreshold_shift_interval hk hqActual hactual' hcore' hqCore
    hr_lower hr_upper hroom

/-- Exact `k`-power ratios force an exact adjacent local-overflow shift. -/
theorem BlockCoordinate.localOverflowBoundary_shift_exact
    {actual core : BlockCoordinate} {s a c : ℕ}
    (hsharedB : actual.blockBase = core.blockBase)
    (hsharedK : actual.remainderK = core.remainderK)
    (hactual : actual.isLocalOverflowBoundary a)
    (hcore : core.isLocalOverflowBoundary c)
    (hk : 1 < actual.remainderK)
    (hqCore : core.quotientQ = actual.quotientQ * actual.remainderK ^ s)
    (hs_le : s ≤ a) :
    a - c = s := by
  have hactual' :
      isGeometricThresholdBoundary actual.blockBase actual.quotientQ actual.remainderK a := by
    simpa [BlockCoordinate.isLocalOverflowBoundary] using hactual
  have hcore' :
      isGeometricThresholdBoundary actual.blockBase core.quotientQ actual.remainderK c := by
    simpa [BlockCoordinate.isLocalOverflowBoundary, hsharedB, hsharedK] using hcore
  exact geometricThreshold_shift_exact hk hactual' hcore' hqCore hs_le

end QRTour
