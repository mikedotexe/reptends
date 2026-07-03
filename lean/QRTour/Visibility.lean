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

/-- A geometric threshold boundary is unique once the geometric ratio exceeds `1`. -/
theorem geometricThresholdBoundary_unique
    {threshold q k j n : ℕ}
    (hk : 1 < k)
    (hj : isGeometricThresholdBoundary threshold q k j)
    (hn : isGeometricThresholdBoundary threshold q k n) :
    j = n := by
  apply Nat.le_antisymm
  · exact geometricThresholdBoundary_index_le_of_upper hk hj hn.2
  · exact geometricThresholdBoundary_index_le_of_upper hk hn hj.2

/-- The exact incoming carry into block `j`, written as a natural-number quotient. -/
def BlockCoordinate.incomingCarry (C : BlockCoordinate) (j : ℕ) : ℕ :=
  C.rawCoefficient (j + 1) / (C.blockBase - C.remainderK)

/-- The first incoming-carry boundary occurs when the next raw coefficient crosses `B - k`. -/
def BlockCoordinate.isFirstIncomingCarryPosition (C : BlockCoordinate) (j : ℕ) : Prop :=
  isGeometricThresholdBoundary (C.blockBase - C.remainderK) C.quotientQ C.remainderK j

/-- The adjacent local-overflow boundary: block `j` still fits, but block `j+1` does not. -/
def BlockCoordinate.isLocalOverflowBoundary (C : BlockCoordinate) (j : ℕ) : Prop :=
  isGeometricThresholdBoundary C.blockBase C.quotientQ C.remainderK j

/-- The first incoming-carry boundary is unique once `k > 1`. -/
theorem BlockCoordinate.isFirstIncomingCarryPosition_unique
    (C : BlockCoordinate) {j n : ℕ}
    (hk : 1 < C.remainderK)
    (hj : C.isFirstIncomingCarryPosition j)
    (hn : C.isFirstIncomingCarryPosition n) :
    j = n := by
  exact geometricThresholdBoundary_unique hk hj hn

/-- The local-overflow boundary is unique once `k > 1`. -/
theorem BlockCoordinate.isLocalOverflowBoundary_unique
    (C : BlockCoordinate) {j n : ℕ}
    (hk : 1 < C.remainderK)
    (hj : C.isLocalOverflowBoundary j)
    (hn : C.isLocalOverflowBoundary n) :
    j = n := by
  exact geometricThresholdBoundary_unique hk hj hn

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
  if remainder = 0 then modulus else modulus - remainder

/-- Exact finite-window stabilization certificate for the first `requestedBlocks`
displayed blocks after `lookaheadBlocks` extra carried blocks. -/
def BlockCoordinate.lookaheadCertificateHolds
    (C : BlockCoordinate) (requestedBlocks lookaheadBlocks : ℕ) : Prop :=
  C.rawCoefficient (requestedBlocks + lookaheadBlocks) <
    C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK)

/-- A fixed-window lookahead certificate is minimal when it holds at
`lookaheadBlocks` and fails at every smaller lookahead. -/
def BlockCoordinate.isMinimalLookaheadCertificate
    (C : BlockCoordinate) (requestedBlocks lookaheadBlocks : ℕ) : Prop :=
  C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks ∧
    ∀ earlierLookahead, earlierLookahead < lookaheadBlocks →
      ¬ C.lookaheadCertificateHolds requestedBlocks earlierLookahead

theorem BlockCoordinate.truncatedVisiblePrefixValue_mul_blockBasePow_add_remainder
    (C : BlockCoordinate) (requestedBlocks lookaheadBlocks : ℕ) :
    C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks * C.blockBase ^ lookaheadBlocks +
      C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks =
        C.bodyTerm (requestedBlocks + lookaheadBlocks) := by
  unfold BlockCoordinate.truncatedVisiblePrefixValue BlockCoordinate.truncatedVisiblePrefixRemainder
  simpa [Nat.mul_comm] using (Nat.div_add_mod (C.bodyTerm (requestedBlocks + lookaheadBlocks))
    (C.blockBase ^ lookaheadBlocks))

/-- With one lookahead block, the lower suffix of the body term is exactly the
next raw coefficient modulo the block base. -/
theorem BlockCoordinate.truncatedVisiblePrefixRemainder_one_eq_rawCoefficient_mod_blockBase
    (C : BlockCoordinate) (requestedBlocks : ℕ) :
    C.truncatedVisiblePrefixRemainder requestedBlocks 1 =
      C.rawCoefficient requestedBlocks % C.blockBase := by
  unfold BlockCoordinate.truncatedVisiblePrefixRemainder
  rw [pow_one]
  have hbody :
      C.bodyTerm (requestedBlocks + 1) =
        C.blockBase * C.bodyTerm requestedBlocks + C.rawCoefficient requestedBlocks := by
    exact C.bodyTerm_recurrence requestedBlocks
  rw [hbody]
  rw [Nat.add_comm, Nat.add_mul_mod_self_left]

/-- With two lookahead blocks, the lower suffix of the body term is exactly the
next two raw coefficients modulo the square of the block base. -/
theorem BlockCoordinate.truncatedVisiblePrefixRemainder_two_eq_rawCoefficient_suffix_mod_blockBase_sq
    (C : BlockCoordinate) (requestedBlocks : ℕ) :
    C.truncatedVisiblePrefixRemainder requestedBlocks 2 =
      (C.rawCoefficient requestedBlocks * C.blockBase +
        C.rawCoefficient (requestedBlocks + 1)) % C.blockBase ^ 2 := by
  unfold BlockCoordinate.truncatedVisiblePrefixRemainder
  have hbody1 :
      C.bodyTerm (requestedBlocks + 1) =
        C.blockBase * C.bodyTerm requestedBlocks + C.rawCoefficient requestedBlocks := by
    exact C.bodyTerm_recurrence requestedBlocks
  have hbody2 :
      C.bodyTerm (requestedBlocks + 2) =
        C.blockBase * C.bodyTerm (requestedBlocks + 1) +
          C.rawCoefficient (requestedBlocks + 1) := by
    simpa [Nat.add_assoc] using C.bodyTerm_recurrence (requestedBlocks + 1)
  rw [hbody2, hbody1]
  have hperm :
      C.blockBase * (C.blockBase * C.bodyTerm requestedBlocks + C.rawCoefficient requestedBlocks) +
          C.rawCoefficient (requestedBlocks + 1) =
        (C.rawCoefficient requestedBlocks * C.blockBase +
            C.rawCoefficient (requestedBlocks + 1)) +
          C.blockBase ^ 2 * C.bodyTerm requestedBlocks := by
    ring_nf
  rw [hperm]
  rw [Nat.add_mul_mod_self_left]

/-- With three lookahead blocks, the lower suffix of the body term is exactly
the next three raw coefficients modulo the cube of the block base. -/
theorem BlockCoordinate.truncatedVisiblePrefixRemainder_three_eq_rawCoefficient_suffix_mod_blockBase_cu
    (C : BlockCoordinate) (requestedBlocks : ℕ) :
    C.truncatedVisiblePrefixRemainder requestedBlocks 3 =
      (C.rawCoefficient requestedBlocks * C.blockBase ^ 2 +
        C.rawCoefficient (requestedBlocks + 1) * C.blockBase +
        C.rawCoefficient (requestedBlocks + 2)) % C.blockBase ^ 3 := by
  unfold BlockCoordinate.truncatedVisiblePrefixRemainder
  have hbody1 :
      C.bodyTerm (requestedBlocks + 1) =
        C.blockBase * C.bodyTerm requestedBlocks + C.rawCoefficient requestedBlocks := by
    exact C.bodyTerm_recurrence requestedBlocks
  have hbody2 :
      C.bodyTerm (requestedBlocks + 2) =
        C.blockBase * C.bodyTerm (requestedBlocks + 1) +
          C.rawCoefficient (requestedBlocks + 1) := by
    simpa [Nat.add_assoc] using C.bodyTerm_recurrence (requestedBlocks + 1)
  have hbody3 :
      C.bodyTerm (requestedBlocks + 3) =
        C.blockBase * C.bodyTerm (requestedBlocks + 2) +
          C.rawCoefficient (requestedBlocks + 2) := by
    simpa [Nat.add_assoc] using C.bodyTerm_recurrence (requestedBlocks + 2)
  rw [hbody3, hbody2, hbody1]
  have hperm :
      C.blockBase *
            (C.blockBase * (C.blockBase * C.bodyTerm requestedBlocks +
                C.rawCoefficient requestedBlocks) +
              C.rawCoefficient (requestedBlocks + 1)) +
          C.rawCoefficient (requestedBlocks + 2) =
        (C.rawCoefficient requestedBlocks * C.blockBase ^ 2 +
            C.rawCoefficient (requestedBlocks + 1) * C.blockBase +
            C.rawCoefficient (requestedBlocks + 2)) +
          C.blockBase ^ 3 * C.bodyTerm requestedBlocks := by
    ring_nf
  rw [hperm]
  rw [Nat.add_mul_mod_self_left]

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
  let kpow := C.remainderK ^ (requestedBlocks + lookaheadBlocks)
  have hdecomp :
      q0 * Bpow * C.modulus + rem * C.modulus =
        Bpow * C.blockBase ^ requestedBlocks - kpow := by
    calc
      q0 * Bpow * C.modulus + rem * C.modulus
        = (q0 * Bpow + rem) * C.modulus := by
            rw [Nat.add_mul]
      _ = C.bodyTerm (requestedBlocks + lookaheadBlocks) * C.modulus := by
            exact congrArg (fun t => t * C.modulus)
              (C.truncatedVisiblePrefixValue_mul_blockBasePow_add_remainder requestedBlocks lookaheadBlocks)
      _ = Bpow * C.blockBase ^ requestedBlocks - kpow := by
            simpa [Bpow, kpow, pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
              C.bodyTerm_mul_modulus_eq (requestedBlocks + lookaheadBlocks)
  have hkpow_le :
      kpow ≤ Bpow * C.blockBase ^ requestedBlocks := by
    dsimp [kpow, Bpow]
    calc
      C.remainderK ^ (requestedBlocks + lookaheadBlocks) ≤
          C.blockBase ^ (requestedBlocks + lookaheadBlocks) := by
            exact Nat.pow_le_pow_left (Nat.mod_le _ _) _
      _ = C.blockBase ^ lookaheadBlocks * C.blockBase ^ requestedBlocks := by
            rw [pow_add, Nat.mul_comm]
  have hsum :
      rem * C.modulus + kpow + Bpow * (q0 * C.modulus) =
        Bpow * C.blockBase ^ requestedBlocks := by
    calc
      rem * C.modulus + kpow + Bpow * (q0 * C.modulus)
        = (q0 * Bpow * C.modulus + rem * C.modulus) + kpow := by
            ac_rfl
      _ = (Bpow * C.blockBase ^ requestedBlocks - kpow) + kpow := by rw [hdecomp]
      _ = Bpow * C.blockBase ^ requestedBlocks := by rw [Nat.sub_add_cancel hkpow_le]
  have hsub :
      rem * C.modulus + kpow =
        Bpow * C.blockBase ^ requestedBlocks - Bpow * (q0 * C.modulus) :=
    Nat.eq_sub_of_add_eq hsum
  calc
    C.blockBase ^ lookaheadBlocks *
        (C.blockBase ^ requestedBlocks - C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks * C.modulus)
      = Bpow * C.blockBase ^ requestedBlocks - Bpow * (q0 * C.modulus) := by
          simp [q0, Bpow, Nat.mul_sub_left_distrib,
            Nat.mul_left_comm, Nat.mul_comm]
    _ = rem * C.modulus + kpow := by
          simpa [q0, rem, Bpow, kpow] using hsub.symm

theorem BlockCoordinate.truncatedVisiblePrefixValue_split
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    C.blockBase ^ lookaheadBlocks * C.blockBase ^ requestedBlocks =
      C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks *
          (C.blockBase ^ lookaheadBlocks * C.modulus) +
        (C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * C.modulus +
          C.remainderK ^ (requestedBlocks + lookaheadBlocks)) := by
  let q0 := C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks
  let rem := C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks
  let Bpow := C.blockBase ^ lookaheadBlocks
  have hq0_le :
      q0 * C.modulus ≤ C.blockBase ^ requestedBlocks := by
    have hBpow_pos : 0 < Bpow := by
      dsimp [Bpow]
      exact pow_pos (C.blockBase_pos_of_goodMode hgood) _
    have hq0Bpow_le :
        q0 * Bpow ≤ C.bodyTerm (requestedBlocks + lookaheadBlocks) := by
      dsimp [q0, Bpow]
      exact Nat.div_mul_le_self _ _
    have hmul :
        Bpow * (q0 * C.modulus) ≤ Bpow * C.blockBase ^ requestedBlocks := by
      calc
        Bpow * (q0 * C.modulus) = q0 * Bpow * C.modulus := by
          ac_rfl
        _ ≤ C.bodyTerm (requestedBlocks + lookaheadBlocks) * C.modulus := by
          exact Nat.mul_le_mul_right _ hq0Bpow_le
        _ = Bpow * C.blockBase ^ requestedBlocks -
              C.remainderK ^ (requestedBlocks + lookaheadBlocks) := by
              simpa [Bpow, pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
                C.bodyTerm_mul_modulus_eq (requestedBlocks + lookaheadBlocks)
        _ ≤ Bpow * C.blockBase ^ requestedBlocks := Nat.sub_le _ _
    exact Nat.le_of_mul_le_mul_left hmul hBpow_pos
  calc
    Bpow * C.blockBase ^ requestedBlocks
      = Bpow * ((C.blockBase ^ requestedBlocks - q0 * C.modulus) + q0 * C.modulus) := by
          rw [Nat.sub_add_cancel hq0_le]
    _ = Bpow * (C.blockBase ^ requestedBlocks - q0 * C.modulus) + Bpow * (q0 * C.modulus) := by
          rw [Nat.mul_add]
    _ = rem * C.modulus + C.remainderK ^ (requestedBlocks + lookaheadBlocks) +
          q0 * (Bpow * C.modulus) := by
          rw [C.truncatedVisiblePrefixValue_balance requestedBlocks lookaheadBlocks]
          simp [q0, rem, Bpow, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = q0 * (Bpow * C.modulus) +
          (rem * C.modulus + C.remainderK ^ (requestedBlocks + lookaheadBlocks)) := by
          ac_rfl

theorem BlockCoordinate.truncatedVisiblePrefixValue_mul_modulus_le
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks * C.modulus ≤
      C.blockBase ^ requestedBlocks := by
  let q0 := C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks
  let Bpow := C.blockBase ^ lookaheadBlocks
  have hBpow_pos : 0 < Bpow := by
    dsimp [Bpow]
    exact pow_pos (C.blockBase_pos_of_goodMode hgood) _
  have hq0Bpow_le :
      q0 * Bpow ≤ C.bodyTerm (requestedBlocks + lookaheadBlocks) := by
    dsimp [q0, Bpow]
    exact Nat.div_mul_le_self _ _
  have hmul :
      Bpow * (q0 * C.modulus) ≤ Bpow * C.blockBase ^ requestedBlocks := by
    calc
      Bpow * (q0 * C.modulus) = q0 * Bpow * C.modulus := by
        ac_rfl
      _ ≤ C.bodyTerm (requestedBlocks + lookaheadBlocks) * C.modulus := by
        exact Nat.mul_le_mul_right _ hq0Bpow_le
      _ = Bpow * C.blockBase ^ requestedBlocks -
            C.remainderK ^ (requestedBlocks + lookaheadBlocks) := by
            simpa [Bpow, pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
              C.bodyTerm_mul_modulus_eq (requestedBlocks + lookaheadBlocks)
      _ ≤ Bpow * C.blockBase ^ requestedBlocks := Nat.sub_le _ _
  exact Nat.le_of_mul_le_mul_left hmul hBpow_pos

theorem BlockCoordinate.lookaheadCertificateHolds_iff_tail_lt_gapModulus
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks ↔
      C.remainderK ^ (requestedBlocks + lookaheadBlocks) <
        C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * C.modulus := by
  unfold BlockCoordinate.lookaheadCertificateHolds BlockCoordinate.rawCoefficient
  have hgap :
      C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) =
        C.quotientQ * (C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * C.modulus) := by
    calc
      C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK)
        = C.lookaheadGapNumerator requestedBlocks lookaheadBlocks *
            (C.quotientQ * C.modulus) := by
              rw [C.quotientQ_mul_modulus_eq_blockBase_sub_remainderK]
      _ = C.quotientQ * (C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * C.modulus) := by
            ac_rfl
  rw [hgap]
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (Nat.mul_lt_mul_left (C.quotientQ_pos_of_goodMode hgood) :
      C.quotientQ * C.remainderK ^ (requestedBlocks + lookaheadBlocks) <
          C.quotientQ *
            (C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * C.modulus) ↔
        C.remainderK ^ (requestedBlocks + lookaheadBlocks) <
          C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * C.modulus)

theorem BlockCoordinate.lookaheadCertificateHolds_iff_gap
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks ↔
      C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
        C.rawCoefficient (requestedBlocks + lookaheadBlocks) <
          C.blockBase ^ lookaheadBlocks * (C.blockBase - C.remainderK) := by
  simp only [BlockCoordinate.lookaheadCertificateHolds, BlockCoordinate.lookaheadGapNumerator]
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
              have hrem_le :
                  C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks ≤
                    C.blockBase ^ lookaheadBlocks := by
                exact Nat.le_of_lt
                  (C.truncatedVisiblePrefixRemainder_lt_blockBasePow hgood requestedBlocks lookaheadBlocks)
              calc
                C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
                    (C.blockBase ^ lookaheadBlocks -
                      C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks) *
                      (C.blockBase - C.remainderK)
                  = (C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks +
                      (C.blockBase ^ lookaheadBlocks -
                        C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks)) *
                        (C.blockBase - C.remainderK) := by
                          rw [Nat.add_mul]
                  _ = C.blockBase ^ lookaheadBlocks * (C.blockBase - C.remainderK) := by
                          rw [Nat.add_sub_of_le hrem_le]
    · intro hlt
      have hrem_le :
          C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks ≤
            C.blockBase ^ lookaheadBlocks := by
        exact Nat.le_of_lt
          (C.truncatedVisiblePrefixRemainder_lt_blockBasePow hgood requestedBlocks lookaheadBlocks)
      have hdecomp :
          C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
              (C.blockBase ^ lookaheadBlocks - C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks) *
                (C.blockBase - C.remainderK) =
            C.blockBase ^ lookaheadBlocks * (C.blockBase - C.remainderK) := by
        calc
          C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
              (C.blockBase ^ lookaheadBlocks - C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks) *
                (C.blockBase - C.remainderK)
            = (C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks +
                (C.blockBase ^ lookaheadBlocks -
                  C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks)) *
                  (C.blockBase - C.remainderK) := by
                    rw [Nat.add_mul]
          _ = C.blockBase ^ lookaheadBlocks * (C.blockBase - C.remainderK) := by
                rw [Nat.add_sub_of_le hrem_le]
      have hsum :
          C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
            C.rawCoefficient (requestedBlocks + lookaheadBlocks) <
              C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
                (C.blockBase ^ lookaheadBlocks - C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks) *
                  (C.blockBase - C.remainderK) := by
        exact hlt.trans_eq hdecomp.symm
      have hsub :
          C.rawCoefficient (requestedBlocks + lookaheadBlocks) <
            (C.blockBase ^ lookaheadBlocks - C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks) *
              (C.blockBase - C.remainderK) := by
        exact Nat.lt_of_add_lt_add_left hsum
      simpa [hzero] using hsub

theorem BlockCoordinate.emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_tail_lt_gapModulus
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    C.emittedPrefixValue requestedBlocks =
        C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks ↔
      C.remainderK ^ (requestedBlocks + lookaheadBlocks) <
        C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * C.modulus := by
  let q0 := C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks
  let rem := C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks
  let Bpow := C.blockBase ^ lookaheadBlocks
  let kpow := C.remainderK ^ (requestedBlocks + lookaheadBlocks)
  have hBpow_pos : 0 < Bpow := by
    dsimp [Bpow]
    exact pow_pos (C.blockBase_pos_of_goodMode hgood) _
  have hq0_le :
      q0 * C.modulus ≤ C.blockBase ^ requestedBlocks := by
    simpa [q0] using
      C.truncatedVisiblePrefixValue_mul_modulus_le hgood requestedBlocks lookaheadBlocks
  have hsplit :
      Bpow * C.blockBase ^ requestedBlocks =
        q0 * (Bpow * C.modulus) + (rem * C.modulus + kpow) := by
    simpa [q0, rem, Bpow, kpow] using
      C.truncatedVisiblePrefixValue_split hgood requestedBlocks lookaheadBlocks
  constructor
  · intro heq
    have hpow_decomp :
        C.blockBase ^ requestedBlocks =
          q0 * C.modulus + C.blockBase ^ requestedBlocks % C.modulus := by
      dsimp [q0]
      rw [← heq, BlockCoordinate.emittedPrefixValue]
      simpa [Nat.mul_comm] using
        (Nat.div_add_mod (C.blockBase ^ requestedBlocks) C.modulus).symm
    have hlt_div :
        C.blockBase ^ requestedBlocks < (q0 + 1) * C.modulus := by
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
    have htarget :
        Bpow * ((q0 + 1) * C.modulus) = q0 * (Bpow * C.modulus) + Bpow * C.modulus := by
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    rw [hsplit, htarget] at hlt_mul
    have hsmall :
        rem * C.modulus + kpow < Bpow * C.modulus := by
      exact Nat.lt_of_add_lt_add_left hlt_mul
    unfold BlockCoordinate.lookaheadGapNumerator
    dsimp [rem, Bpow, kpow]
    split_ifs with hzero
    · simpa [rem, hzero] using hsmall
    ·
      have hrem_lt :
          C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks <
            C.blockBase ^ lookaheadBlocks :=
        C.truncatedVisiblePrefixRemainder_lt_blockBasePow hgood requestedBlocks lookaheadBlocks
      have hdecomp :
          C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * C.modulus +
              (C.blockBase ^ lookaheadBlocks -
                C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks) * C.modulus =
            C.blockBase ^ lookaheadBlocks * C.modulus := by
        calc
          C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * C.modulus +
              (C.blockBase ^ lookaheadBlocks -
                C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks) * C.modulus
            = (C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks +
                (C.blockBase ^ lookaheadBlocks -
                  C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks)) * C.modulus := by
                    rw [Nat.add_mul]
          _ = C.blockBase ^ lookaheadBlocks * C.modulus := by
                rw [Nat.add_sub_of_le (Nat.le_of_lt hrem_lt)]
      rw [← hdecomp] at hsmall
      exact Nat.lt_of_add_lt_add_left hsmall
  · intro htail
    have hsmall :
        rem * C.modulus + kpow < Bpow * C.modulus := by
      unfold BlockCoordinate.lookaheadGapNumerator at htail
      dsimp [rem, Bpow, kpow] at htail
      split_ifs at htail with hzero
      · simpa [rem, hzero] using htail
      ·
        have hrem_lt :
            C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks <
              C.blockBase ^ lookaheadBlocks :=
          C.truncatedVisiblePrefixRemainder_lt_blockBasePow hgood requestedBlocks lookaheadBlocks
        have hdecomp :
            C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * C.modulus +
                (C.blockBase ^ lookaheadBlocks -
                  C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks) * C.modulus =
              C.blockBase ^ lookaheadBlocks * C.modulus := by
          calc
            C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * C.modulus +
                (C.blockBase ^ lookaheadBlocks -
                  C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks) * C.modulus
              = (C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks +
                  (C.blockBase ^ lookaheadBlocks -
                    C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks)) * C.modulus := by
                      rw [Nat.add_mul]
            _ = C.blockBase ^ lookaheadBlocks * C.modulus := by
                  rw [Nat.add_sub_of_le (Nat.le_of_lt hrem_lt)]
        rw [← hdecomp]
        exact Nat.add_lt_add_left htail _
    have hlt_mul :
        Bpow * C.blockBase ^ requestedBlocks < Bpow * ((q0 + 1) * C.modulus) := by
      have htarget :
          Bpow * ((q0 + 1) * C.modulus) = q0 * (Bpow * C.modulus) + Bpow * C.modulus := by
        simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      rw [hsplit, htarget]
      exact Nat.add_lt_add_left hsmall _
    have hlt_div :
        C.blockBase ^ requestedBlocks < (q0 + 1) * C.modulus :=
      (Nat.mul_lt_mul_left hBpow_pos).1 hlt_mul
    apply le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul C.modulus_pos).2 hlt_div)
    · exact (Nat.le_div_iff_mul_le C.modulus_pos).2 hq0_le

theorem BlockCoordinate.emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_gap
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    C.emittedPrefixValue requestedBlocks = C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks ↔
      C.truncatedVisiblePrefixRemainder requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) +
        C.rawCoefficient (requestedBlocks + lookaheadBlocks) <
          C.blockBase ^ lookaheadBlocks * (C.blockBase - C.remainderK) := by
  exact
    (C.emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_tail_lt_gapModulus
      hgood requestedBlocks lookaheadBlocks).trans
      ((C.lookaheadCertificateHolds_iff_tail_lt_gapModulus
          hgood requestedBlocks lookaheadBlocks).symm.trans
        (C.lookaheadCertificateHolds_iff_gap hgood requestedBlocks lookaheadBlocks))

theorem BlockCoordinate.emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_lookaheadCertificate
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    C.emittedPrefixValue requestedBlocks = C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks ↔
      C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks := by
  rw [C.emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_tail_lt_gapModulus hgood,
    C.lookaheadCertificateHolds_iff_tail_lt_gapModulus hgood]

theorem BlockCoordinate.lookaheadCertificateHolds_of_remainderK_pow_lt_modulus
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ)
    (hsmall : C.remainderK ^ (requestedBlocks + lookaheadBlocks) < C.modulus) :
    C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks := by
  rw [C.lookaheadCertificateHolds_iff_tail_lt_gapModulus hgood]
  have hgap_le :
      C.modulus ≤ C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * C.modulus := by
    simpa [Nat.mul_comm] using
      Nat.mul_le_mul_right C.modulus
        (Nat.succ_le_of_lt (C.lookaheadGapNumerator_pos hgood requestedBlocks lookaheadBlocks))
  exact lt_of_lt_of_le hsmall hgap_le

/-- The coarse `k^(n+L) < modulus` condition already certifies emitted-prefix
equality at the fixed `(requestedBlocks, lookaheadBlocks)` window. -/
theorem BlockCoordinate.emittedPrefixValue_eq_truncatedVisiblePrefixValue_of_remainderK_pow_lt_modulus
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ)
    (hsmall : C.remainderK ^ (requestedBlocks + lookaheadBlocks) < C.modulus) :
    C.emittedPrefixValue requestedBlocks =
      C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks := by
  exact
    (C.emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_lookaheadCertificate
      hgood requestedBlocks lookaheadBlocks).2
      (C.lookaheadCertificateHolds_of_remainderK_pow_lt_modulus
        hgood requestedBlocks lookaheadBlocks hsmall)

@[simp] theorem BlockCoordinate.truncatedVisiblePrefixRemainder_zero
    (C : BlockCoordinate) (requestedBlocks : ℕ) :
    C.truncatedVisiblePrefixRemainder requestedBlocks 0 = 0 := by
  unfold BlockCoordinate.truncatedVisiblePrefixRemainder
  rw [pow_zero]
  exact Nat.mod_one _

@[simp] theorem BlockCoordinate.lookaheadGapNumerator_zero
    (C : BlockCoordinate) (requestedBlocks : ℕ) :
    C.lookaheadGapNumerator requestedBlocks 0 = 1 := by
  simp [BlockCoordinate.lookaheadGapNumerator]

theorem BlockCoordinate.lookaheadCertificateHolds_zero_iff_remainderK_pow_lt_modulus
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks : ℕ) :
    C.lookaheadCertificateHolds requestedBlocks 0 ↔
      C.remainderK ^ requestedBlocks < C.modulus := by
  rw [C.lookaheadCertificateHolds_iff_tail_lt_gapModulus hgood, C.lookaheadGapNumerator_zero]
  simp

theorem BlockCoordinate.lookaheadCertificateHolds_iff_remainderK_pow_lt_modulus_of_lookaheadGapNumerator_eq_one
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (hgap : C.lookaheadGapNumerator requestedBlocks lookaheadBlocks = 1) :
    C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks ↔
      C.remainderK ^ (requestedBlocks + lookaheadBlocks) < C.modulus := by
  rw [C.lookaheadCertificateHolds_iff_tail_lt_gapModulus hgood, hgap]
  simp

/-- The exact prefix-gap certificate is stronger than the coarse tail-mass
lower-bound inequality used by the Python lower-bound search. -/
theorem BlockCoordinate.lookaheadCertificateHolds_implies_tailMassLowerBound
    (C : BlockCoordinate) (requestedBlocks lookaheadBlocks : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    C.rawCoefficient (requestedBlocks + lookaheadBlocks) <
      C.blockBase ^ lookaheadBlocks * (C.blockBase - C.remainderK) := by
  calc
    C.rawCoefficient (requestedBlocks + lookaheadBlocks) <
        C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * (C.blockBase - C.remainderK) :=
      hcert
    _ ≤ C.blockBase ^ lookaheadBlocks * (C.blockBase - C.remainderK) := by
      exact Nat.mul_le_mul_right (C.blockBase - C.remainderK)
        (C.lookaheadGapNumerator_le_blockBasePow requestedBlocks lookaheadBlocks)

/-- The same necessary lower bound, phrased in the `k^(n+L)` tail-mass form. -/
theorem BlockCoordinate.lookaheadCertificateHolds_implies_remainderKPow_lt_blockBasePow_mul_modulus
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    C.remainderK ^ (requestedBlocks + lookaheadBlocks) <
      C.blockBase ^ lookaheadBlocks * C.modulus := by
  rw [C.lookaheadCertificateHolds_iff_tail_lt_gapModulus hgood] at hcert
  calc
    C.remainderK ^ (requestedBlocks + lookaheadBlocks) <
        C.lookaheadGapNumerator requestedBlocks lookaheadBlocks * C.modulus := hcert
    _ ≤ C.blockBase ^ lookaheadBlocks * C.modulus := by
      exact Nat.mul_le_mul_right C.modulus
        (C.lookaheadGapNumerator_le_blockBasePow requestedBlocks lookaheadBlocks)

/-- Every finite visible-prefix truncation lies below the emitted long-division
prefix integer. -/
theorem BlockCoordinate.truncatedVisiblePrefixValue_le_emittedPrefixValue
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks ≤
      C.emittedPrefixValue requestedBlocks := by
  unfold BlockCoordinate.emittedPrefixValue
  exact (Nat.le_div_iff_mul_le C.modulus_pos).2
    (C.truncatedVisiblePrefixValue_mul_modulus_le hgood requestedBlocks lookaheadBlocks)

/-- The finite truncated visible-prefix integer is monotone in the lookahead
window: adding one more carried block cannot decrease the visible prefix. -/
theorem BlockCoordinate.truncatedVisiblePrefixValue_le_succ
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ) :
    C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks ≤
      C.truncatedVisiblePrefixValue requestedBlocks (lookaheadBlocks + 1) := by
  have hpow_pos : 0 < C.blockBase ^ (lookaheadBlocks + 1) := by
    exact pow_pos (C.blockBase_pos_of_goodMode hgood) _
  have hmul_le :
      C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks *
          C.blockBase ^ (lookaheadBlocks + 1) ≤
        C.bodyTerm (requestedBlocks + (lookaheadBlocks + 1)) := by
    calc
      C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks *
          C.blockBase ^ (lookaheadBlocks + 1)
        = (C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks *
            C.blockBase ^ lookaheadBlocks) * C.blockBase := by
            rw [pow_succ']
            ac_rfl
      _ ≤ C.bodyTerm (requestedBlocks + lookaheadBlocks) * C.blockBase := by
            exact Nat.mul_le_mul_right C.blockBase (Nat.div_mul_le_self _ _)
      _ ≤ C.bodyTerm (requestedBlocks + lookaheadBlocks) * C.blockBase +
            C.rawCoefficient (requestedBlocks + lookaheadBlocks) := by
            exact Nat.le_add_right _ _
      _ = C.bodyTerm (requestedBlocks + (lookaheadBlocks + 1)) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_comm,
              Nat.mul_left_comm, Nat.mul_assoc] using
              (C.bodyTerm_succ (requestedBlocks + lookaheadBlocks)).symm
  exact (Nat.le_div_iff_mul_le hpow_pos).2 (by
    simpa [BlockCoordinate.truncatedVisiblePrefixValue] using hmul_le)

/-- The truncated visible-prefix integer is monotone for arbitrary additional
lookahead, not just one extra block. -/
theorem BlockCoordinate.truncatedVisiblePrefixValue_le_add
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks extraLookahead : ℕ) :
    C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks ≤
      C.truncatedVisiblePrefixValue requestedBlocks (lookaheadBlocks + extraLookahead) := by
  induction extraLookahead with
  | zero =>
      simp
  | succ extraLookahead ih =>
      calc
        C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks
          ≤ C.truncatedVisiblePrefixValue requestedBlocks (lookaheadBlocks + extraLookahead) := by
              simpa [Nat.add_assoc] using ih
        _ ≤ C.truncatedVisiblePrefixValue requestedBlocks ((lookaheadBlocks + extraLookahead) + 1) :=
              C.truncatedVisiblePrefixValue_le_succ hgood requestedBlocks (lookaheadBlocks + extraLookahead)
        _ = C.truncatedVisiblePrefixValue requestedBlocks
              (lookaheadBlocks + (extraLookahead + 1)) := by
              simp [Nat.add_assoc]

/-- Once a finite truncation already matches the emitted prefix integer, the
match persists after one more carried block. -/
theorem BlockCoordinate.emittedPrefixValue_eq_truncatedVisiblePrefixValue_of_eq_succ
    (C : BlockCoordinate) (hgood : C.goodMode) (requestedBlocks lookaheadBlocks : ℕ)
    (heq :
      C.emittedPrefixValue requestedBlocks =
        C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks) :
    C.emittedPrefixValue requestedBlocks =
      C.truncatedVisiblePrefixValue requestedBlocks (lookaheadBlocks + 1) := by
  apply le_antisymm
  · rw [heq]
    exact C.truncatedVisiblePrefixValue_le_succ hgood requestedBlocks lookaheadBlocks
  · exact C.truncatedVisiblePrefixValue_le_emittedPrefixValue hgood requestedBlocks (lookaheadBlocks + 1)

/-- Once a finite truncation matches the emitted prefix integer, the match
persists for any larger lookahead window. -/
theorem BlockCoordinate.emittedPrefixValue_eq_truncatedVisiblePrefixValue_of_eq_add
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks extraLookahead : ℕ)
    (heq :
      C.emittedPrefixValue requestedBlocks =
        C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks) :
    C.emittedPrefixValue requestedBlocks =
      C.truncatedVisiblePrefixValue requestedBlocks (lookaheadBlocks + extraLookahead) := by
  apply le_antisymm
  · rw [heq]
    exact C.truncatedVisiblePrefixValue_le_add hgood requestedBlocks lookaheadBlocks extraLookahead
  · exact C.truncatedVisiblePrefixValue_le_emittedPrefixValue hgood requestedBlocks
      (lookaheadBlocks + extraLookahead)

/-- Once a finite truncation matches the emitted prefix integer, the match
persists for any lookahead window at least as large as the current one. -/
theorem BlockCoordinate.emittedPrefixValue_eq_truncatedVisiblePrefixValue_of_eq_le
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks largerLookahead : ℕ)
    (hle : lookaheadBlocks ≤ largerLookahead)
    (heq :
      C.emittedPrefixValue requestedBlocks =
        C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks) :
    C.emittedPrefixValue requestedBlocks =
      C.truncatedVisiblePrefixValue requestedBlocks largerLookahead := by
  rcases Nat.exists_eq_add_of_le hle with ⟨extraLookahead, rfl⟩
  exact C.emittedPrefixValue_eq_truncatedVisiblePrefixValue_of_eq_add
    hgood requestedBlocks lookaheadBlocks extraLookahead heq

/-- Once the exact prefix-gap certificate holds, the finite truncated
visible-prefix integer itself has stabilized and remains unchanged at any
larger lookahead window. -/
theorem BlockCoordinate.truncatedVisiblePrefixValue_eq_of_lookaheadCertificate_add
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks extraLookahead : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks =
      C.truncatedVisiblePrefixValue requestedBlocks (lookaheadBlocks + extraLookahead) := by
  have hbase :
      C.emittedPrefixValue requestedBlocks =
        C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks :=
    (C.emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_lookaheadCertificate
      hgood requestedBlocks lookaheadBlocks).2 hcert
  have htransport :
      C.emittedPrefixValue requestedBlocks =
        C.truncatedVisiblePrefixValue requestedBlocks (lookaheadBlocks + extraLookahead) :=
    C.emittedPrefixValue_eq_truncatedVisiblePrefixValue_of_eq_add
      hgood requestedBlocks lookaheadBlocks extraLookahead hbase
  exact hbase.symm.trans htransport

/-- Once the exact prefix-gap certificate holds, the visible-prefix integer
stays stabilized on any larger lookahead window specified by an inequality. -/
theorem BlockCoordinate.truncatedVisiblePrefixValue_eq_of_lookaheadCertificate_le
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks largerLookahead : ℕ)
    (hle : lookaheadBlocks ≤ largerLookahead)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks =
      C.truncatedVisiblePrefixValue requestedBlocks largerLookahead := by
  rcases Nat.exists_eq_add_of_le hle with ⟨extraLookahead, rfl⟩
  exact C.truncatedVisiblePrefixValue_eq_of_lookaheadCertificate_add
    hgood requestedBlocks lookaheadBlocks extraLookahead hcert

/-- One-step stabilization form of the truncated visible-prefix equality. -/
theorem BlockCoordinate.truncatedVisiblePrefixValue_eq_of_lookaheadCertificate_succ
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks =
      C.truncatedVisiblePrefixValue requestedBlocks (lookaheadBlocks + 1) := by
  simpa using C.truncatedVisiblePrefixValue_eq_of_lookaheadCertificate_add
    hgood requestedBlocks lookaheadBlocks 1 hcert

/-- The exact prefix-gap certificate transports to any larger lookahead window:
once the first `requestedBlocks` blocks have stabilized, adding more carried
blocks keeps that same visible prefix. -/
theorem BlockCoordinate.lookaheadCertificateHolds_of_lookaheadCertificate_add
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks extraLookahead : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    C.lookaheadCertificateHolds requestedBlocks (lookaheadBlocks + extraLookahead) := by
  rw [← C.emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_lookaheadCertificate hgood] at hcert ⊢
  exact C.emittedPrefixValue_eq_truncatedVisiblePrefixValue_of_eq_add
    hgood requestedBlocks lookaheadBlocks extraLookahead hcert

/-- The exact prefix-gap certificate also transports along any explicit
lookahead inequality `lookaheadBlocks ≤ largerLookahead`. -/
theorem BlockCoordinate.lookaheadCertificateHolds_of_lookaheadCertificate_le
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks largerLookahead : ℕ)
    (hle : lookaheadBlocks ≤ largerLookahead)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    C.lookaheadCertificateHolds requestedBlocks largerLookahead := by
  rcases Nat.exists_eq_add_of_le hle with ⟨extraLookahead, rfl⟩
  exact C.lookaheadCertificateHolds_of_lookaheadCertificate_add
    hgood requestedBlocks lookaheadBlocks extraLookahead hcert

/-- One-step transport form of the exact prefix-gap certificate. -/
theorem BlockCoordinate.lookaheadCertificateHolds_of_lookaheadCertificate_succ
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    C.lookaheadCertificateHolds requestedBlocks (lookaheadBlocks + 1) := by
  simpa using C.lookaheadCertificateHolds_of_lookaheadCertificate_add
    hgood requestedBlocks lookaheadBlocks 1 hcert

/-- Once the exact prefix-gap certificate holds, its necessary raw tail-mass
lower bound also holds on any larger lookahead window obtained by adding more
carried blocks. -/
theorem BlockCoordinate.lookaheadCertificateHolds_implies_tailMassLowerBound_add
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks extraLookahead : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    C.rawCoefficient (requestedBlocks + (lookaheadBlocks + extraLookahead)) <
      C.blockBase ^ (lookaheadBlocks + extraLookahead) * (C.blockBase - C.remainderK) := by
  exact C.lookaheadCertificateHolds_implies_tailMassLowerBound
    (requestedBlocks := requestedBlocks)
    (lookaheadBlocks := lookaheadBlocks + extraLookahead)
    (C.lookaheadCertificateHolds_of_lookaheadCertificate_add
      hgood requestedBlocks lookaheadBlocks extraLookahead hcert)

/-- The necessary raw tail-mass lower bound also transports along any explicit
lookahead inequality `lookaheadBlocks ≤ largerLookahead`. -/
theorem BlockCoordinate.lookaheadCertificateHolds_implies_tailMassLowerBound_le
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks largerLookahead : ℕ)
    (hle : lookaheadBlocks ≤ largerLookahead)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    C.rawCoefficient (requestedBlocks + largerLookahead) <
      C.blockBase ^ largerLookahead * (C.blockBase - C.remainderK) := by
  rcases Nat.exists_eq_add_of_le hle with ⟨extraLookahead, rfl⟩
  simpa [Nat.add_assoc] using C.lookaheadCertificateHolds_implies_tailMassLowerBound_add
    hgood requestedBlocks lookaheadBlocks extraLookahead hcert

/-- One-step transport form of the necessary raw tail-mass lower bound. -/
theorem BlockCoordinate.lookaheadCertificateHolds_implies_tailMassLowerBound_succ
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    C.rawCoefficient (requestedBlocks + (lookaheadBlocks + 1)) <
      C.blockBase ^ (lookaheadBlocks + 1) * (C.blockBase - C.remainderK) := by
  simpa using C.lookaheadCertificateHolds_implies_tailMassLowerBound_add
    hgood requestedBlocks lookaheadBlocks 1 hcert

/-- Claim `incoming_carry_position_formula`: the incoming carry is `floor(q*k^(j+1)/(B-k))`. -/
theorem BlockCoordinate.incomingCarry_formula (C : BlockCoordinate) (j : ℕ) :
    C.incomingCarry j =
      (C.quotientQ * C.remainderK ^ (j + 1)) / (C.blockBase - C.remainderK) := by
  simp [BlockCoordinate.incomingCarry, BlockCoordinate.rawCoefficient]

/-- Arithmetic recurrence behind the infinite-tail carry quotient. -/
theorem nat_carry_recurrence_of_lt {B k a : ℕ} (hk : k < B) :
    (a + (a * k) / (B - k)) / B = a / (B - k) := by
  let D := B - k
  have hDpos : 0 < D := by omega
  let n := a / D
  let r := a % D
  let s := (r * k) / D
  have ha : a = n * D + r := by
    dsimp [n, r]
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod a D).symm
  have hrlt : r < D := by
    dsimp [r]
    exact Nat.mod_lt a hDpos
  have hB : B = D + k := by
    dsimp [D]
    omega
  have hdivak : ((n * D + r) * k) / D = n * k + s := by
    dsimp [s]
    calc
      ((n * D + r) * k) / D = (D * (n * k) + r * k) / D := by ring_nf
      _ = n * k + (r * k) / D := by rw [Nat.mul_add_div hDpos]
  rw [show a / D = n by rfl]
  have htail_le : s ≤ k := by
    dsimp [s]
    rw [Nat.div_le_iff_le_mul hDpos]
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hrk_lt : r * k < D * k := Nat.mul_lt_mul_of_pos_right hrlt hkpos
      have hdk_le : D * k ≤ k * D + D - 1 := by
        rw [Nat.mul_comm D k]
        omega
      exact le_trans (Nat.le_of_lt hrk_lt) hdk_le
  have htail_lt : r + s < D + k := by omega
  apply Nat.div_eq_of_lt_le
  · rw [ha, show (B - k) = D by rfl, hdivak, hB]
    calc
      n * (D + k) = n * D + n * k := by ring
      _ ≤ n * D + n * k + (r + s) := Nat.le_add_right _ _
      _ = n * D + r + (n * k + s) := by ring
  · rw [ha, show (B - k) = D by rfl, hdivak, hB]
    calc
      n * D + r + (n * k + s) = n * D + n * k + (r + s) := by ring
      _ < n * D + n * k + (D + k) := by
        exact Nat.add_lt_add_left htail_lt _
      _ = (n + 1) * (D + k) := by ring

/-- The canonical infinite-tail incoming carry obeys the same one-step
recurrence as finite carry propagation. -/
theorem BlockCoordinate.incomingCarry_step_recurrence
    (C : BlockCoordinate) (hgood : C.goodMode) (j : ℕ) :
    C.incomingCarry j =
      (C.rawCoefficient (j + 1) + C.incomingCarry (j + 1)) / C.blockBase := by
  unfold BlockCoordinate.incomingCarry
  rw [show C.rawCoefficient (j + 1 + 1) = C.rawCoefficient (j + 1) * C.remainderK by
    rw [show j + 1 + 1 = (j + 1) + 1 by omega]
    exact C.rawCoefficient_succ (j + 1)]
  exact (nat_carry_recurrence_of_lt (C.remainderK_lt_blockBase hgood)).symm

/-- Adjacent entries in a positive-length raw trace expose the carry shift:
the incoming carry at index `i` is the outgoing carry of index `i+1`. -/
theorem BlockCoordinate.traceRawWord_carryIn_eq_next_carryOut_of_succ_length
    (C : BlockCoordinate) (hgood : C.goodMode) (length i : ℕ) (hi : i < length) :
    ((C.traceRawWord hgood (length + 1))[i]'(by rw [C.traceRawWord_length]; omega)).carryIn =
      ((C.traceRawWord hgood (length + 1))[i + 1]'(by rw [C.traceRawWord_length]; omega)).carryOut := by
  have hmap := C.traceRawWord_map_carryIn_eq_tail_map_carryOut_append_zero_of_pos hgood length
  have hget := congrArg (fun xs => xs[i]?) hmap
  simp [C.traceRawWord_length, hi, Nat.lt_of_lt_of_le hi (Nat.le_succ _)] at hget
  exact hget

/-- The rightmost raw-trace step has zero incoming carry, because finite
normalization starts with no suffix carry. -/
theorem BlockCoordinate.traceRawWord_last_carryIn_eq_zero
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    ((C.traceRawWord hgood (length + 1))[length]'(by rw [C.traceRawWord_length]; omega)).carryIn =
      0 := by
  have hmap := C.traceRawWord_map_carryIn_eq_tail_map_carryOut_append_zero_of_pos hgood length
  have hget := congrArg (fun xs => xs[length]?) hmap
  simp [C.traceRawWord_length] at hget
  exact hget

theorem BlockCoordinate.traceRawWord_coefficient_eq_rawCoefficient
    (C : BlockCoordinate) (hgood : C.goodMode) (length i : ℕ) (hi : i < length) :
    ((C.traceRawWord hgood length)[i]'(by rw [C.traceRawWord_length]; exact hi)).coefficient =
      C.rawCoefficient i := by
  have hmap := C.traceRawWord_map_coefficient hgood length
  have hget := congrArg (fun xs => xs[i]?) hmap
  simp [BlockCoordinate.rawCoefficientWord, C.traceRawWord_length, hi] at hget
  exact hget

theorem BlockCoordinate.traceRawWord_isLeftmost_eq_false_of_pos
    (C : BlockCoordinate) (hgood : C.goodMode) (length i : ℕ) (hi : i < length) :
    ((C.traceRawWord hgood (length + 1))[i + 1]'(by rw [C.traceRawWord_length]; omega)).isLeftmost =
      false := by
  have hmap := C.traceRawWord_map_isLeftmost_of_pos hgood length
  have hget := congrArg (fun xs => xs[i + 1]?) hmap
  simp [C.traceRawWord_length, hi] at hget
  exact hget

theorem BlockCoordinate.traceRawWord_carryOut_eq_div_of_pos_index
    (C : BlockCoordinate) (hgood : C.goodMode) (length i : ℕ) (hi : i < length) :
    ((C.traceRawWord hgood (length + 1))[i + 1]'(by rw [C.traceRawWord_length]; omega)).carryOut =
      (((C.traceRawWord hgood (length + 1))[i + 1]'(by rw [C.traceRawWord_length]; omega)).coefficient +
        ((C.traceRawWord hgood (length + 1))[i + 1]'(by rw [C.traceRawWord_length]; omega)).carryIn) /
        C.blockBase := by
  exact (C.carryTransducer hgood).mem_traceBlocks_nonleft_carryOut_eq_div
    (by
      rw [← BlockCoordinate.traceRawWord]
      exact List.getElem_mem _)
    (C.traceRawWord_isLeftmost_eq_false_of_pos hgood length i hi)

theorem BlockCoordinate.traceRawWord_blockValue_eq_mod_of_pos_index
    (C : BlockCoordinate) (hgood : C.goodMode) (length i : ℕ) (hi : i < length) :
    ((C.traceRawWord hgood (length + 1))[i + 1]'(by rw [C.traceRawWord_length]; omega)).blockValue =
      (((C.traceRawWord hgood (length + 1))[i + 1]'(by rw [C.traceRawWord_length]; omega)).coefficient +
        ((C.traceRawWord hgood (length + 1))[i + 1]'(by rw [C.traceRawWord_length]; omega)).carryIn) %
        C.blockBase := by
  exact (C.carryTransducer hgood).mem_traceBlocks_nonleft_blockValue_eq_mod
    (by
      rw [← BlockCoordinate.traceRawWord]
      exact List.getElem_mem _)
    (C.traceRawWord_isLeftmost_eq_false_of_pos hgood length i hi)

theorem BlockCoordinate.traceRawWord_carryIn_eq_next_carryOut
    (C : BlockCoordinate) (hgood : C.goodMode) (length i : ℕ) (hi : i + 1 < length) :
    ((C.traceRawWord hgood length)[i]'(by rw [C.traceRawWord_length]; omega)).carryIn =
      ((C.traceRawWord hgood length)[i + 1]'(by rw [C.traceRawWord_length]; omega)).carryOut := by
  cases length with
  | zero =>
      omega
  | succ last =>
      exact C.traceRawWord_carryIn_eq_next_carryOut_of_succ_length hgood last i (by omega)

theorem BlockCoordinate.traceRawWord_carryOut_eq_div_of_pos
    (C : BlockCoordinate) (hgood : C.goodMode) (length i : ℕ)
    (hi : i < length) (hpos : 0 < i) :
    ((C.traceRawWord hgood length)[i]'(by rw [C.traceRawWord_length]; exact hi)).carryOut =
      (((C.traceRawWord hgood length)[i]'(by rw [C.traceRawWord_length]; exact hi)).coefficient +
        ((C.traceRawWord hgood length)[i]'(by rw [C.traceRawWord_length]; exact hi)).carryIn) /
        C.blockBase := by
  cases i with
  | zero =>
      omega
  | succ p =>
      cases length with
      | zero =>
          omega
      | succ last =>
          exact C.traceRawWord_carryOut_eq_div_of_pos_index hgood last p (by omega)

theorem BlockCoordinate.traceRawWord_blockValue_eq_mod_of_pos
    (C : BlockCoordinate) (hgood : C.goodMode) (length i : ℕ)
    (hi : i < length) (hpos : 0 < i) :
    ((C.traceRawWord hgood length)[i]'(by rw [C.traceRawWord_length]; exact hi)).blockValue =
      (((C.traceRawWord hgood length)[i]'(by rw [C.traceRawWord_length]; exact hi)).coefficient +
        ((C.traceRawWord hgood length)[i]'(by rw [C.traceRawWord_length]; exact hi)).carryIn) %
        C.blockBase := by
  cases i with
  | zero =>
      omega
  | succ p =>
      cases length with
      | zero =>
          omega
      | succ last =>
          exact C.traceRawWord_blockValue_eq_mod_of_pos_index hgood last p (by omega)

/-- Every finite carry entering a visible raw-trace position is bounded above
by the canonical infinite-tail incoming carry at the same position. -/
theorem BlockCoordinate.traceRawWord_carryIn_le_incomingCarry
    (C : BlockCoordinate) (hgood : C.goodMode) (length i : ℕ)
    (hi : i < (C.traceRawWord hgood length).length) :
    ((C.traceRawWord hgood length)[i]'hi).carryIn ≤ C.incomingCarry i := by
  rw [C.traceRawWord_length] at hi
  cases length with
  | zero =>
      omega
  | succ last =>
      have hi_le : i ≤ last := by omega
      let P : ℕ → Prop := fun t =>
        ∀ ht : t ≤ last,
          ((C.traceRawWord hgood (last + 1))[t]'(by rw [C.traceRawWord_length]; omega)).carryIn ≤
            C.incomingCarry t
      have hP : P i := by
        refine Nat.decreasingInduction' (m := i) (n := last) (P := P) ?step hi_le ?base
        · intro k hk _ ih hk_le
          dsimp [P] at ih
          have ihnext :
              ((C.traceRawWord hgood (last + 1))[k + 1]'(by rw [C.traceRawWord_length]; omega)).carryIn ≤
                C.incomingCarry (k + 1) := ih (by omega)
          calc
            ((C.traceRawWord hgood (last + 1))[k]'(by rw [C.traceRawWord_length]; omega)).carryIn
                = ((C.traceRawWord hgood (last + 1))[k + 1]'(by rw [C.traceRawWord_length]; omega)).carryOut := by
                    exact C.traceRawWord_carryIn_eq_next_carryOut_of_succ_length hgood last k hk
            _ = (((C.traceRawWord hgood (last + 1))[k + 1]'(by rw [C.traceRawWord_length]; omega)).coefficient +
                  ((C.traceRawWord hgood (last + 1))[k + 1]'(by rw [C.traceRawWord_length]; omega)).carryIn) /
                  C.blockBase := by
                    exact C.traceRawWord_carryOut_eq_div_of_pos_index hgood last k hk
            _ = (C.rawCoefficient (k + 1) +
                  ((C.traceRawWord hgood (last + 1))[k + 1]'(by rw [C.traceRawWord_length]; omega)).carryIn) /
                  C.blockBase := by
                    rw [C.traceRawWord_coefficient_eq_rawCoefficient hgood (last + 1) (k + 1) (by omega)]
            _ ≤ (C.rawCoefficient (k + 1) + C.incomingCarry (k + 1)) / C.blockBase := by
                    exact Nat.div_le_div_right (Nat.add_le_add_left ihnext _)
            _ = C.incomingCarry k := by
                    rw [← C.incomingCarry_step_recurrence hgood k]
        · intro ht
          rw [C.traceRawWord_last_carryIn_eq_zero hgood last]
          exact Nat.zero_le _
      simpa [P] using hP hi_le

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

/-- Incoming carry vanishes exactly when the next raw coefficient stays below
the gap threshold `B - k`. -/
theorem BlockCoordinate.incomingCarry_eq_zero_iff
    (C : BlockCoordinate) (hgood : C.goodMode) (j : ℕ) :
    C.incomingCarry j = 0 ↔ C.rawCoefficient (j + 1) < C.blockBase - C.remainderK := by
  constructor
  · intro hzero
    by_contra hge
    have hcarry_pos : 0 < C.incomingCarry j :=
      (C.incomingCarry_pos_iff hgood j).2 (Nat.not_lt.mp hge)
    omega
  · intro hlt
    have hnot_pos : ¬ 0 < C.incomingCarry j := by
      intro hcarry_pos
      exact not_lt_of_ge ((C.incomingCarry_pos_iff hgood j).1 hcarry_pos) hlt
    exact Nat.eq_zero_of_not_pos hnot_pos

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

/-- The adjacent local-overflow boundary is exactly the least index where the
next raw coefficient reaches the block base. -/
theorem BlockCoordinate.isLocalOverflowBoundary_iff
    (C : BlockCoordinate) (j : ℕ) :
    C.isLocalOverflowBoundary j ↔
      C.rawCoefficient j < C.blockBase ∧
        C.blockBase ≤ C.rawCoefficient (j + 1) := by
  simp [BlockCoordinate.isLocalOverflowBoundary, isGeometricThresholdBoundary,
    BlockCoordinate.rawCoefficient]

/-- The next raw coefficient produces a local overflow exactly when its
block-base quotient is positive. -/
theorem BlockCoordinate.localOverflowQuotient_pos_iff
    (C : BlockCoordinate) (hgood : C.goodMode) (j : ℕ) :
    0 < C.rawCoefficient (j + 1) / C.blockBase ↔
      C.blockBase ≤ C.rawCoefficient (j + 1) := by
  have hbase_pos : 0 < C.blockBase := C.blockBase_pos_of_goodMode hgood
  constructor
  · intro hoverflow
    by_contra hlt
    have hzero : C.rawCoefficient (j + 1) / C.blockBase = 0 := by
      exact Nat.div_eq_of_lt (lt_of_not_ge hlt)
    omega
  · intro hthreshold
    exact Nat.div_pos hthreshold hbase_pos

/-- A raw coefficient still fits in one block exactly when its block-base
quotient is zero. -/
theorem BlockCoordinate.rawCoefficient_div_blockBase_eq_zero_iff
    (C : BlockCoordinate) (hgood : C.goodMode) (j : ℕ) :
    C.rawCoefficient j / C.blockBase = 0 ↔
      C.rawCoefficient j < C.blockBase := by
  constructor
  · intro hzero
    by_contra hlt
    have hoverflow :
        0 < C.rawCoefficient j / C.blockBase :=
      Nat.div_pos (Nat.not_lt.mp hlt) (C.blockBase_pos_of_goodMode hgood)
    exact (show ¬ 0 < C.rawCoefficient j / C.blockBase by simp [hzero]) hoverflow
  · intro hlt
    exact Nat.div_eq_of_lt hlt

/-- The adjacent local-overflow boundary can be read as positivity of the next
raw coefficient's block-base overflow quotient. -/
theorem BlockCoordinate.isLocalOverflowBoundary_iff_overflowQuotient
    (C : BlockCoordinate) (hgood : C.goodMode) (j : ℕ) :
    C.isLocalOverflowBoundary j ↔
      C.rawCoefficient j < C.blockBase ∧
        0 < C.rawCoefficient (j + 1) / C.blockBase := by
  rw [C.isLocalOverflowBoundary_iff, C.localOverflowQuotient_pos_iff hgood]

/-- The adjacent local-overflow boundary can also be read entirely through
block-base quotients: the current raw coefficient still has zero overflow
quotient, while the next one has a positive overflow quotient. -/
theorem BlockCoordinate.isLocalOverflowBoundary_iff_overflowQuotients
    (C : BlockCoordinate) (hgood : C.goodMode) (j : ℕ) :
    C.isLocalOverflowBoundary j ↔
      C.rawCoefficient j / C.blockBase = 0 ∧
        0 < C.rawCoefficient (j + 1) / C.blockBase := by
  rw [C.isLocalOverflowBoundary_iff_overflowQuotient hgood,
    C.rawCoefficient_div_blockBase_eq_zero_iff hgood]

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

/-- A sufficient criterion for the lower endpoint of the interval law: if the
core stream is still below the threshold at index `a - s`, then the shift is
exactly the lower endpoint `s`. -/
theorem geometricThreshold_shift_lower_endpoint
    {threshold qActual qCore k r s a c : ℕ}
    (hk : 1 < k)
    (hactual : isGeometricThresholdBoundary threshold qActual k a)
    (hcore : isGeometricThresholdBoundary threshold qCore k c)
    (hqCore : qCore = qActual * r)
    (hr_lower : k ^ s ≤ r)
    (hs_le : s ≤ a)
    (hlower : qCore * k ^ (a - s) < threshold) :
    a - c = s := by
  have hcandidate :
      isGeometricThresholdBoundary threshold qCore k (a - s) := by
    constructor
    · exact hlower
    · calc
        threshold ≤ qActual * k ^ (a + 1) := hactual.2
        _ = (qActual * k ^ s) * k ^ ((a - s) + 1) := by
            have hexp : a + 1 = s + ((a - s) + 1) := by omega
            rw [hexp, pow_add]
            ac_rfl
        _ ≤ (qActual * r) * k ^ ((a - s) + 1) := by
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hr_lower)
        _ = qCore * k ^ ((a - s) + 1) := by rw [hqCore]
  have hcore_le : c ≤ a - s := by
    exact geometricThresholdBoundary_index_le_of_upper hk hcore hcandidate.2
  have hcore_ge : a - s ≤ c := by
    exact geometricThresholdBoundary_le_index_of_lower_lt hk hcore hcandidate.1
  omega

/-- A sufficient criterion for the upper endpoint of the interval law: if the
core stream has already reached the threshold at index `a - s`, then the shift
is exactly the upper endpoint `s + 1`. -/
theorem geometricThreshold_shift_upper_endpoint
    {threshold qActual qCore k r s a c : ℕ}
    (hk : 1 < k)
    (hqActual : 0 < qActual)
    (hactual : isGeometricThresholdBoundary threshold qActual k a)
    (hcore : isGeometricThresholdBoundary threshold qCore k c)
    (hqCore : qCore = qActual * r)
    (hr_upper : r < k ^ (s + 1))
    (hroom : s + 1 ≤ a)
    (hupper : threshold ≤ qCore * k ^ (a - s)) :
    a - c = s + 1 := by
  have hcandidate :
      isGeometricThresholdBoundary threshold qCore k (a - (s + 1)) := by
    constructor
    · calc
        qCore * k ^ (a - (s + 1))
            = (qActual * r) * k ^ (a - (s + 1)) := by rw [hqCore]
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
    · have hexp : (a - (s + 1)) + 1 = a - s := by omega
      simpa [hexp] using hupper
  have hcore_le : c ≤ a - (s + 1) := by
    exact geometricThresholdBoundary_index_le_of_upper hk hcore hcandidate.2
  have hcore_ge : a - (s + 1) ≤ c := by
    exact geometricThresholdBoundary_le_index_of_lower_lt hk hcore hcandidate.1
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

/-- A sufficient criterion for the lower endpoint of the incoming-carry shift
law. -/
theorem BlockCoordinate.firstIncomingCarryPosition_shift_lower
    {actual core : BlockCoordinate} {r s a c : ℕ}
    (hsharedB : actual.blockBase = core.blockBase)
    (hsharedK : actual.remainderK = core.remainderK)
    (hactual : actual.isFirstIncomingCarryPosition a)
    (hcore : core.isFirstIncomingCarryPosition c)
    (hk : 1 < actual.remainderK)
    (hqCore : core.quotientQ = actual.quotientQ * r)
    (hr_lower : actual.remainderK ^ s ≤ r)
    (hs_le : s ≤ a)
    (hlower :
      core.quotientQ * actual.remainderK ^ (a - s) <
        actual.blockBase - actual.remainderK) :
    a - c = s := by
  have hactual' :
      isGeometricThresholdBoundary (actual.blockBase - actual.remainderK)
        actual.quotientQ actual.remainderK a := by
    simpa [BlockCoordinate.isFirstIncomingCarryPosition] using hactual
  have hcore' :
      isGeometricThresholdBoundary (actual.blockBase - actual.remainderK)
        core.quotientQ actual.remainderK c := by
    simpa [BlockCoordinate.isFirstIncomingCarryPosition, hsharedB, hsharedK] using hcore
  exact geometricThreshold_shift_lower_endpoint hk hactual' hcore' hqCore hr_lower hs_le hlower

/-- A sufficient criterion for the upper endpoint of the incoming-carry shift
law. -/
theorem BlockCoordinate.firstIncomingCarryPosition_shift_upper
    {actual core : BlockCoordinate} {r s a c : ℕ}
    (hsharedB : actual.blockBase = core.blockBase)
    (hsharedK : actual.remainderK = core.remainderK)
    (hactual : actual.isFirstIncomingCarryPosition a)
    (hcore : core.isFirstIncomingCarryPosition c)
    (hk : 1 < actual.remainderK)
    (hqActual : 0 < actual.quotientQ)
    (hqCore : core.quotientQ = actual.quotientQ * r)
    (hr_upper : r < actual.remainderK ^ (s + 1))
    (hroom : s + 1 ≤ a)
    (hupper :
      actual.blockBase - actual.remainderK ≤
        core.quotientQ * actual.remainderK ^ (a - s)) :
    a - c = s + 1 := by
  have hactual' :
      isGeometricThresholdBoundary (actual.blockBase - actual.remainderK)
        actual.quotientQ actual.remainderK a := by
    simpa [BlockCoordinate.isFirstIncomingCarryPosition] using hactual
  have hcore' :
      isGeometricThresholdBoundary (actual.blockBase - actual.remainderK)
        core.quotientQ actual.remainderK c := by
    simpa [BlockCoordinate.isFirstIncomingCarryPosition, hsharedB, hsharedK] using hcore
  exact geometricThreshold_shift_upper_endpoint hk hqActual hactual' hcore' hqCore hr_upper hroom hupper

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

/-- A sufficient criterion for the lower endpoint of the local-overflow shift
law. -/
theorem BlockCoordinate.localOverflowBoundary_shift_lower
    {actual core : BlockCoordinate} {r s a c : ℕ}
    (hsharedB : actual.blockBase = core.blockBase)
    (hsharedK : actual.remainderK = core.remainderK)
    (hactual : actual.isLocalOverflowBoundary a)
    (hcore : core.isLocalOverflowBoundary c)
    (hk : 1 < actual.remainderK)
    (hqCore : core.quotientQ = actual.quotientQ * r)
    (hr_lower : actual.remainderK ^ s ≤ r)
    (hs_le : s ≤ a)
    (hlower :
      core.quotientQ * actual.remainderK ^ (a - s) < actual.blockBase) :
    a - c = s := by
  have hactual' :
      isGeometricThresholdBoundary actual.blockBase actual.quotientQ actual.remainderK a := by
    simpa [BlockCoordinate.isLocalOverflowBoundary] using hactual
  have hcore' :
      isGeometricThresholdBoundary actual.blockBase core.quotientQ actual.remainderK c := by
    simpa [BlockCoordinate.isLocalOverflowBoundary, hsharedB, hsharedK] using hcore
  exact geometricThreshold_shift_lower_endpoint hk hactual' hcore' hqCore hr_lower hs_le hlower

/-- A sufficient criterion for the upper endpoint of the local-overflow shift
law. -/
theorem BlockCoordinate.localOverflowBoundary_shift_upper
    {actual core : BlockCoordinate} {r s a c : ℕ}
    (hsharedB : actual.blockBase = core.blockBase)
    (hsharedK : actual.remainderK = core.remainderK)
    (hactual : actual.isLocalOverflowBoundary a)
    (hcore : core.isLocalOverflowBoundary c)
    (hk : 1 < actual.remainderK)
    (hqActual : 0 < actual.quotientQ)
    (hqCore : core.quotientQ = actual.quotientQ * r)
    (hr_upper : r < actual.remainderK ^ (s + 1))
    (hroom : s + 1 ≤ a)
    (hupper :
      actual.blockBase ≤ core.quotientQ * actual.remainderK ^ (a - s)) :
    a - c = s + 1 := by
  have hactual' :
      isGeometricThresholdBoundary actual.blockBase actual.quotientQ actual.remainderK a := by
    simpa [BlockCoordinate.isLocalOverflowBoundary] using hactual
  have hcore' :
      isGeometricThresholdBoundary actual.blockBase core.quotientQ actual.remainderK c := by
    simpa [BlockCoordinate.isLocalOverflowBoundary, hsharedB, hsharedK] using hcore
  exact geometricThreshold_shift_upper_endpoint hk hqActual hactual' hcore' hqCore hr_upper hroom hupper

end QRTour
