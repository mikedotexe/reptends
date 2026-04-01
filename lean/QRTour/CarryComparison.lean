/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.CompositeVisibility
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.Enum
import Mathlib.Data.List.Zip

/-!
# Finite Carry/Long-Division Comparison

This module packages the finite comparison surface between:

- the carry-normalized raw coefficient window produced from `q * k^j`, and
- the emitted long-division block window produced from remainder states.

The point here is exact finite alignment, not the still-open global
factorization claim.
-/

namespace QRTour

namespace List

theorem rdrop_eq_take_of_length_eq {α : Type*} {l : List α} {n k : ℕ}
    (hlen : l.length = n + k) :
    l.rdrop k = l.take n := by
  have hdrop : (l.drop n).length = k := by
    rw [List.length_drop, hlen]
    omega
  calc
    l.rdrop k = (l.take n ++ l.drop n).rdrop k := by rw [List.take_append_drop]
    _ = (l.take n ++ l.drop n).rdrop ((l.drop n).length) := by rw [hdrop]
    _ = l.take n := by rw [List.rdrop_append_length]

theorem map_rdrop {α β : Type*} (f : α → β) (l : List α) (n : ℕ) :
    (l.rdrop n).map f = (l.map f).rdrop n := by
  simp [List.rdrop_eq_reverse_drop_reverse, List.map_reverse]

theorem drop_rdrop_eq_rdrop_drop_of_length_eq {α : Type*} {l : List α} {s n k : ℕ}
    (hlen : l.length = s + n + k) :
    (l.rdrop k).drop s = (l.drop s).rdrop k := by
  have hk : k ≤ (l.drop s).length := by
    rw [List.length_drop, hlen]
    omega
  calc
    (l.rdrop k).drop s = ((l.take s ++ l.drop s).rdrop k).drop s := by
        rw [List.take_append_drop]
    _ = (l.take s ++ (l.drop s).rdrop k).drop s := by
        rw [List.rdrop_append_of_le_length _ hk]
    _ = (l.drop s).rdrop k := by
        have hs : (l.take s).length = s := by
          rw [List.length_take, hlen]
          omega
        rw [List.drop_append, hs]
        simp

def FunctionalOnFst {α β : Type*} (pairs : List (α × β)) : Prop :=
  ∀ a ∈ pairs, ∀ b ∈ pairs, a.1 = b.1 → a.2 = b.2

instance instDecidableFunctionalOnFst {α β : Type*} [DecidableEq α] [DecidableEq β]
    (pairs : List (α × β)) : Decidable (FunctionalOnFst pairs) := by
  unfold FunctionalOnFst
  infer_instance

theorem functionalOnFst_iff_getElem {α β : Type*} {pairs : List (α × β)} :
    FunctionalOnFst pairs ↔
      ∀ i (hi : i < pairs.length) j (hj : j < pairs.length),
        (pairs[i]'hi).1 = (pairs[j]'hj).1 →
          (pairs[i]'hi).2 = (pairs[j]'hj).2 := by
  unfold FunctionalOnFst
  constructor
  · intro h i hi j hj heq
    exact h _ (List.getElem_mem _) _ (List.getElem_mem _) heq
  · intro h a ha b hb hab
    rcases List.mem_iff_getElem.mp ha with ⟨i, hi, rfl⟩
    rcases List.mem_iff_getElem.mp hb with ⟨j, hj, rfl⟩
    exact h i hi j hj hab

end List

theorem CarryTransducer.traceReversedAux_take_map_carryIn_append
    (T : CarryTransducer) (coefficients suffix : List ℕ) (carryIn : ℕ) :
    ((T.traceReversedAux (coefficients ++ suffix) carryIn).take coefficients.length).map
        CarryTraceStep.carryIn =
      (T.traceReversedAux coefficients carryIn).map CarryTraceStep.carryIn := by
  induction coefficients generalizing carryIn with
  | nil =>
      simp [CarryTransducer.traceReversedAux]
  | cons coefficient tail ih =>
      cases tail with
      | nil =>
          cases suffix with
          | nil =>
              simp [CarryTransducer.traceReversedAux, CarryTransducer.mkTraceStep]
          | cons next rest =>
              simp [CarryTransducer.traceReversedAux, CarryTransducer.mkTraceStep]
      | cons next rest =>
          simp [CarryTransducer.traceReversedAux, List.map_take]
          simpa [List.map_take] using ih ((coefficient + carryIn) / T.blockBase)

theorem CarryTransducer.traceReversed_take_map_carryIn_append
    (T : CarryTransducer) (coefficients suffix : List ℕ) :
    ((T.traceReversed (coefficients ++ suffix)).take coefficients.length).map
        CarryTraceStep.carryIn =
      (T.traceReversed coefficients).map CarryTraceStep.carryIn := by
  simpa [CarryTransducer.traceReversed] using
    T.traceReversedAux_take_map_carryIn_append coefficients suffix 0

theorem CarryTransducer.traceBlocks_map_carryIn_drop_prefix_of_append
    (T : CarryTransducer) (leading coefficients : List ℕ) :
    ((T.traceBlocks (leading ++ coefficients)).map CarryTraceStep.carryIn).drop leading.length =
      (T.traceBlocks coefficients).map CarryTraceStep.carryIn := by
  have hdrop_rtake :
      ((T.traceBlocks (leading ++ coefficients)).map CarryTraceStep.carryIn).drop leading.length =
        ((T.traceBlocks (leading ++ coefficients)).map CarryTraceStep.carryIn).rtake
          coefficients.length := by
    unfold List.rtake
    rw [List.length_map, CarryTransducer.traceBlocks_length]
    simp
  calc
    ((T.traceBlocks (leading ++ coefficients)).map CarryTraceStep.carryIn).drop leading.length
      = ((T.traceBlocks (leading ++ coefficients)).map CarryTraceStep.carryIn).rtake
          coefficients.length := hdrop_rtake
    _ = List.reverse
          ((((T.traceBlocks (leading ++ coefficients)).map CarryTraceStep.carryIn).reverse).take
            coefficients.length) := by
          rw [List.rtake_eq_reverse_take_reverse]
    _ = List.reverse
          (((T.traceReversed (coefficients.reverse ++ leading.reverse)).map
              CarryTraceStep.carryIn).take coefficients.length) := by
          simp [CarryTransducer.traceBlocks, List.reverse_append, List.map_reverse]
    _ = List.reverse ((T.traceReversed coefficients.reverse).map CarryTraceStep.carryIn) := by
          simpa [List.length_reverse, List.map_take] using
            congrArg List.reverse
              (T.traceReversed_take_map_carryIn_append coefficients.reverse leading.reverse)
    _ = (T.traceBlocks coefficients).map CarryTraceStep.carryIn := by
          simp [CarryTransducer.traceBlocks, List.map_reverse]

/-- The visible prefix of the carried raw trace after dropping the lookahead tail. -/
def BlockCoordinate.visibleCarryTrace
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) : List CarryTraceStep :=
  (C.traceRawWord hgood (requestedBlocks + lookaheadBlocks)).rdrop lookaheadBlocks

/-- The visible prefix of the carried normalized word after dropping the lookahead tail. -/
def BlockCoordinate.visibleCarryWord
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) : List ℕ :=
  (C.normalizedRawWord hgood (requestedBlocks + lookaheadBlocks)).rdrop lookaheadBlocks

theorem BlockCoordinate.visibleCarryTrace_length
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).length = requestedBlocks := by
  unfold BlockCoordinate.visibleCarryTrace
  rw [List.rdrop_eq_take_of_length_eq]
  · rw [List.length_take, C.traceRawWord_length]
    rw [Nat.min_eq_left (Nat.le_add_right requestedBlocks lookaheadBlocks)]
  · rw [C.traceRawWord_length]

theorem BlockCoordinate.visibleCarryWord_length
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryWord hgood requestedBlocks lookaheadBlocks).length = requestedBlocks := by
  unfold BlockCoordinate.visibleCarryWord
  rw [List.rdrop_eq_take_of_length_eq]
  · rw [List.length_take, C.normalizedRawWord_length]
    rw [Nat.min_eq_left (Nat.le_add_right requestedBlocks lookaheadBlocks)]
  · rw [C.normalizedRawWord_length]

theorem BlockCoordinate.visibleCarryTrace_map_coefficient
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.coefficient =
      (C.rawCoefficientWord (requestedBlocks + lookaheadBlocks)).rdrop lookaheadBlocks := by
  unfold BlockCoordinate.visibleCarryTrace
  rw [List.map_rdrop]
  exact congrArg (fun word => word.rdrop lookaheadBlocks)
    (C.traceRawWord_map_coefficient hgood (requestedBlocks + lookaheadBlocks))

theorem BlockCoordinate.visibleCarryTrace_map_coefficient_prefix
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.coefficient =
      C.rawCoefficientWord requestedBlocks := by
  rw [C.visibleCarryTrace_map_coefficient]
  unfold BlockCoordinate.rawCoefficientWord
  rw [List.rdrop_eq_take_of_length_eq
    (l := (List.range (requestedBlocks + lookaheadBlocks)).map C.rawCoefficient)
    (n := requestedBlocks) (k := lookaheadBlocks)]
  · rw [← List.map_take]
    simp [List.take_range]
  · simp

theorem BlockCoordinate.visibleCarryTrace_map_carryIn
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.carryIn =
      ((C.traceRawWord hgood (requestedBlocks + lookaheadBlocks)).map CarryTraceStep.carryIn).rdrop
        lookaheadBlocks := by
  unfold BlockCoordinate.visibleCarryTrace
  rw [List.map_rdrop]

theorem BlockCoordinate.visibleCarryTrace_map_carryOut
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.carryOut =
      ((C.traceRawWord hgood (requestedBlocks + lookaheadBlocks)).map CarryTraceStep.carryOut).rdrop
        lookaheadBlocks := by
  unfold BlockCoordinate.visibleCarryTrace
  rw [List.map_rdrop]

theorem BlockCoordinate.visibleCarryTrace_map_blockValue
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.blockValue =
      C.visibleCarryWord hgood requestedBlocks lookaheadBlocks := by
  unfold BlockCoordinate.visibleCarryTrace BlockCoordinate.visibleCarryWord
  rw [List.map_rdrop]
  exact congrArg (fun word => word.rdrop lookaheadBlocks)
    (C.traceRawWord_map_blockValue hgood (requestedBlocks + lookaheadBlocks))

theorem BlockCoordinate.mem_visibleCarryTrace
    (C : BlockCoordinate) (hgood : C.goodMode)
    {requestedBlocks lookaheadBlocks : ℕ} {step : CarryTraceStep}
    (hstep : step ∈ C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks) :
    step ∈ C.traceRawWord hgood (requestedBlocks + lookaheadBlocks) := by
  unfold BlockCoordinate.visibleCarryTrace at hstep
  rw [List.rdrop_eq_take_of_length_eq (by rw [C.traceRawWord_length])] at hstep
  exact List.mem_of_mem_take hstep

theorem BlockCoordinate.evalBlocks_visibleCarryWord_eq_truncatedVisiblePrefixValue
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.carryTransducer hgood).evalBlocks (C.visibleCarryWord hgood requestedBlocks lookaheadBlocks) =
      C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks := by
  have hb : 2 ≤ C.blockBase := Nat.succ_le_of_lt (C.blockBase_gt_one_of_goodMode hgood)
  calc
    (C.carryTransducer hgood).evalBlocks (C.visibleCarryWord hgood requestedBlocks lookaheadBlocks)
      = Nat.ofDigits C.blockBase (C.visibleCarryWord hgood requestedBlocks lookaheadBlocks).reverse := by
          simpa [BlockCoordinate.carryTransducer] using
            (C.carryTransducer hgood).evalBlocks_eq_ofDigits_reverse
              (C.visibleCarryWord hgood requestedBlocks lookaheadBlocks)
    _ = Nat.ofDigits C.blockBase
          ((C.normalizedRawWord hgood (requestedBlocks + lookaheadBlocks)).reverse.drop lookaheadBlocks) := by
          unfold BlockCoordinate.visibleCarryWord
          rw [List.rdrop_eq_reverse_drop_reverse]
          simp
    _ = C.bodyTerm (requestedBlocks + lookaheadBlocks) / C.blockBase ^ lookaheadBlocks := by
          rw [← C.digits_bodyTerm_eq_normalizedRawWord_reverse hgood hmod
            (requestedBlocks + lookaheadBlocks)]
          exact (Nat.self_div_pow_eq_ofDigits_drop lookaheadBlocks
            (C.bodyTerm (requestedBlocks + lookaheadBlocks)) hb).symm
    _ = C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks := rfl

theorem BlockCoordinate.mem_visibleCarryWord_lt_blockBase
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    {requestedBlocks lookaheadBlocks digit : ℕ}
    (hmem : digit ∈ C.visibleCarryWord hgood requestedBlocks lookaheadBlocks) :
    digit < C.blockBase := by
  unfold BlockCoordinate.visibleCarryWord at hmem
  rw [List.rdrop_eq_take_of_length_eq (by rw [C.normalizedRawWord_length])] at hmem
  have hmem_full : digit ∈ C.normalizedRawWord hgood (requestedBlocks + lookaheadBlocks) := by
    exact List.mem_of_mem_take hmem
  cases hlen : requestedBlocks + lookaheadBlocks with
  | zero =>
      have hlen' : (C.normalizedRawWord hgood (requestedBlocks + lookaheadBlocks)).length = 0 := by
        have hlen' := C.normalizedRawWord_length hgood (requestedBlocks + lookaheadBlocks)
        rw [hlen] at hlen'
        simpa [hlen] using hlen'
      have hnil : C.normalizedRawWord hgood (requestedBlocks + lookaheadBlocks) = [] := by
        exact List.eq_nil_of_length_eq_zero hlen'
      rw [hnil] at hmem_full
      simp at hmem_full
  | succ length =>
      have hmem_full' : digit ∈ C.normalizedRawWord hgood (length + 1) := by
        simpa [hlen] using hmem_full
      exact C.mem_normalizedRawWord_lt_blockBase hgood hmod hmem_full'

theorem BlockCoordinate.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (requestedBlocks lookaheadBlocks : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    C.visibleCarryWord hgood requestedBlocks lookaheadBlocks =
      C.emittedBlockWord requestedBlocks := by
  have hprefix :
      C.emittedPrefixValue requestedBlocks =
        C.truncatedVisiblePrefixValue requestedBlocks lookaheadBlocks :=
    (C.emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_lookaheadCertificate
      hgood requestedBlocks lookaheadBlocks).2 hcert
  have hvalue :
      (C.carryTransducer hgood).evalBlocks (C.visibleCarryWord hgood requestedBlocks lookaheadBlocks) =
        (C.carryTransducer hgood).evalBlocks (C.emittedBlockWord requestedBlocks) := by
    rw [C.evalBlocks_visibleCarryWord_eq_truncatedVisiblePrefixValue hgood hmod,
      C.evalBlocks_emittedBlockWord_eq_emittedPrefixValue hgood hmod, hprefix]
  have hb : 1 < C.blockBase := C.blockBase_gt_one_of_goodMode hgood
  have hrev :
      (C.visibleCarryWord hgood requestedBlocks lookaheadBlocks).reverse =
        (C.emittedBlockWord requestedBlocks).reverse := by
    apply Nat.ofDigits_inj_of_len_eq hb
    · rw [List.length_reverse, List.length_reverse, C.visibleCarryWord_length]
      simp [BlockCoordinate.emittedBlockWord]
    · intro digit hmem
      exact C.mem_visibleCarryWord_lt_blockBase hgood hmod (by
        simpa using List.mem_reverse.mp hmem)
    · intro digit hmem
      have hmem' : digit ∈ C.emittedBlockWord requestedBlocks := by
        simpa using List.mem_reverse.mp hmem
      rw [BlockCoordinate.emittedBlockWord] at hmem'
      rcases List.mem_map.mp hmem' with ⟨j, _, rfl⟩
      exact C.emittedBlock_lt_blockBase hgood j
    · calc
      Nat.ofDigits C.blockBase (C.visibleCarryWord hgood requestedBlocks lookaheadBlocks).reverse
        = (C.carryTransducer hgood).evalBlocks
            (C.visibleCarryWord hgood requestedBlocks lookaheadBlocks) := by
              symm
              simpa [BlockCoordinate.carryTransducer] using
                (C.carryTransducer hgood).evalBlocks_eq_ofDigits_reverse
                  (C.visibleCarryWord hgood requestedBlocks lookaheadBlocks)
      _ = (C.carryTransducer hgood).evalBlocks (C.emittedBlockWord requestedBlocks) := hvalue
      _ = Nat.ofDigits C.blockBase (C.emittedBlockWord requestedBlocks).reverse := by
            simpa [BlockCoordinate.carryTransducer] using
              (C.carryTransducer hgood).evalBlocks_eq_ofDigits_reverse
                (C.emittedBlockWord requestedBlocks)
  simpa using congrArg List.reverse hrev

theorem BlockCoordinate.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate_add
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (requestedBlocks lookaheadBlocks extraLookahead : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    C.visibleCarryWord hgood requestedBlocks (lookaheadBlocks + extraLookahead) =
      C.emittedBlockWord requestedBlocks := by
  apply C.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate hgood hmod
  exact C.lookaheadCertificateHolds_of_lookaheadCertificate_add
    hgood requestedBlocks lookaheadBlocks extraLookahead hcert

/-- In the exact `k^s` same-core regime, a certified stripped-core window gives
an exact visible carry/output agreement theorem for the shifted actual
denominator. This remains a finite-window theorem only. -/
theorem actualCoordinate_visibleCarryWord_eq_emittedBlockWord_of_core_lookaheadCertificate_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (actualCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hcert :
      (strippedCoordinate base n stride hn).lookaheadCertificateHolds
        requestedBlocks lookaheadBlocks) :
    (actualCoordinate base n stride hn).visibleCarryWord hgood (requestedBlocks + s) lookaheadBlocks =
      (actualCoordinate base n stride hn).emittedBlockWord (requestedBlocks + s) := by
  let actual := actualCoordinate base n stride hn
  have hcertActual :
      actual.lookaheadCertificateHolds (requestedBlocks + s) lookaheadBlocks :=
    sameCoreCompatible_lookaheadCertificateHolds_of_core_lookaheadCertificate_add_exact
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hgood hcompat hfactor hcert
  exact actual.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate
    hgood hmod (requestedBlocks + s) lookaheadBlocks hcertActual

/-- In the exact `k^s` same-core regime, the core tail-versus-gap-modulus
inequality is enough to certify visible carry/output agreement for the shifted
actual denominator. This is the gap-arithmetic form of the same finite-window
comparison theorem. -/
theorem actualCoordinate_visibleCarryWord_eq_emittedBlockWord_of_core_tail_lt_gapModulus_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (actualCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (htail :
      (strippedCoordinate base n stride hn).remainderK ^ (requestedBlocks + lookaheadBlocks) <
        (strippedCoordinate base n stride hn).lookaheadGapNumerator
          requestedBlocks lookaheadBlocks *
          (strippedCoordinate base n stride hn).modulus) :
    (actualCoordinate base n stride hn).visibleCarryWord hgood (requestedBlocks + s) lookaheadBlocks =
      (actualCoordinate base n stride hn).emittedBlockWord (requestedBlocks + s) := by
  let actual := actualCoordinate base n stride hn
  have htailActual :
      actual.remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) <
        actual.lookaheadGapNumerator (requestedBlocks + s) lookaheadBlocks * actual.modulus :=
    (sameCoreCompatible_tail_lt_gapModulus_iff_add_exact
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hcompat hfactor).2 htail
  have hcertActual :
      actual.lookaheadCertificateHolds (requestedBlocks + s) lookaheadBlocks := by
    rw [actual.lookaheadCertificateHolds_iff_tail_lt_gapModulus
      hgood (requestedBlocks + s) lookaheadBlocks]
    exact htailActual
  exact actual.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate
    hgood hmod (requestedBlocks + s) lookaheadBlocks hcertActual

/-- Reverse exact same-core transport form for the finite carried visible word. -/
theorem strippedCoordinate_visibleCarryWord_eq_emittedBlockWord_of_actual_lookaheadCertificate_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (strippedCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hcert :
      (actualCoordinate base n stride hn).lookaheadCertificateHolds
        (requestedBlocks + s) lookaheadBlocks) :
    (strippedCoordinate base n stride hn).visibleCarryWord
        (strippedCoordinate_goodMode_of_actual_goodMode hn hgood) requestedBlocks lookaheadBlocks =
      (strippedCoordinate base n stride hn).emittedBlockWord requestedBlocks := by
  let core := strippedCoordinate base n stride hn
  have hcoreGood : core.goodMode := strippedCoordinate_goodMode_of_actual_goodMode hn hgood
  have hcertCore :
      core.lookaheadCertificateHolds requestedBlocks lookaheadBlocks :=
    sameCoreCompatible_core_lookaheadCertificateHolds_of_actual_lookaheadCertificate_add_exact
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hgood hcompat hfactor hcert
  exact core.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate
    hcoreGood hmod requestedBlocks lookaheadBlocks hcertCore

/-- Reverse exact same-core transport form in the gap-arithmetic language:
the shifted actual tail-versus-gap-modulus inequality certifies the stripped
core visible carry/output agreement on the unshifted window. -/
theorem strippedCoordinate_visibleCarryWord_eq_emittedBlockWord_of_actual_tail_lt_gapModulus_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (strippedCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (htail :
      (actualCoordinate base n stride hn).remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) <
        (actualCoordinate base n stride hn).lookaheadGapNumerator
          (requestedBlocks + s) lookaheadBlocks *
          (actualCoordinate base n stride hn).modulus) :
    (strippedCoordinate base n stride hn).visibleCarryWord
        (strippedCoordinate_goodMode_of_actual_goodMode hn hgood) requestedBlocks lookaheadBlocks =
      (strippedCoordinate base n stride hn).emittedBlockWord requestedBlocks := by
  let core := strippedCoordinate base n stride hn
  have hcoreGood : core.goodMode := strippedCoordinate_goodMode_of_actual_goodMode hn hgood
  have htailCore :
      core.remainderK ^ (requestedBlocks + lookaheadBlocks) <
        core.lookaheadGapNumerator requestedBlocks lookaheadBlocks * core.modulus :=
    (sameCoreCompatible_tail_lt_gapModulus_iff_add_exact
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hcompat hfactor).1 htail
  have hcertCore :
      core.lookaheadCertificateHolds requestedBlocks lookaheadBlocks := by
    rw [core.lookaheadCertificateHolds_iff_tail_lt_gapModulus
      hcoreGood requestedBlocks lookaheadBlocks]
    exact htailCore
  exact core.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate
    hcoreGood hmod requestedBlocks lookaheadBlocks hcertCore

/-- The aligned visible carry/remainder pairs for one finite window. -/
def BlockCoordinate.visibleCarryPairs
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    List (CarryTraceStep × RemainderTraceStep) :=
  (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).zip (C.remainderTrace requestedBlocks)

theorem BlockCoordinate.visibleCarryPairs_length
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).length = requestedBlocks := by
  unfold BlockCoordinate.visibleCarryPairs
  rw [List.length_zip, C.visibleCarryTrace_length, C.remainderTrace_length, min_self]

theorem BlockCoordinate.visibleCarryPairs_unzip
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    List.unzip (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks) =
      (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks, C.remainderTrace requestedBlocks) := by
  unfold BlockCoordinate.visibleCarryPairs
  exact List.unzip_zip (by rw [C.visibleCarryTrace_length, C.remainderTrace_length])

theorem BlockCoordinate.visibleCarryPairs_map_carryStep
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map Prod.fst =
      C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks := by
  have hfst := congrArg Prod.fst (C.visibleCarryPairs_unzip hgood requestedBlocks lookaheadBlocks)
  simpa using hfst

theorem BlockCoordinate.visibleCarryPairs_map_remainderStep
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map Prod.snd =
      C.remainderTrace requestedBlocks := by
  have hsnd := congrArg Prod.snd (C.visibleCarryPairs_unzip hgood requestedBlocks lookaheadBlocks)
  simpa using hsnd

theorem BlockCoordinate.visibleCarryPairs_map_coefficient
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.1.coefficient) =
      C.rawCoefficientWord requestedBlocks := by
  calc
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.1.coefficient)
      = ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map Prod.fst).map
          CarryTraceStep.coefficient := by
            simp
    _ = (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.coefficient := by
          rw [C.visibleCarryPairs_map_carryStep]
    _ = C.rawCoefficientWord requestedBlocks :=
          C.visibleCarryTrace_map_coefficient_prefix hgood requestedBlocks lookaheadBlocks

theorem BlockCoordinate.visibleCarryPairs_map_carryIn
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.1.carryIn) =
      (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.carryIn := by
  calc
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.1.carryIn)
      = ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map Prod.fst).map
          CarryTraceStep.carryIn := by
            simp
    _ = (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.carryIn := by
          rw [C.visibleCarryPairs_map_carryStep]

theorem BlockCoordinate.visibleCarryPairs_map_carryOut
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.1.carryOut) =
      (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.carryOut := by
  calc
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.1.carryOut)
      = ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map Prod.fst).map
          CarryTraceStep.carryOut := by
            simp
    _ = (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.carryOut := by
          rw [C.visibleCarryPairs_map_carryStep]

theorem BlockCoordinate.visibleCarryPairs_map_remainderIn
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.2.remainderIn) =
      (List.range requestedBlocks).map C.longDivisionRemainder := by
  calc
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.2.remainderIn)
      = ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map Prod.snd).map
          RemainderTraceStep.remainderIn := by
            simp
    _ = (C.remainderTrace requestedBlocks).map RemainderTraceStep.remainderIn := by
          rw [C.visibleCarryPairs_map_remainderStep]
    _ = (List.range requestedBlocks).map C.longDivisionRemainder :=
          C.remainderTrace_map_remainderIn requestedBlocks

theorem BlockCoordinate.visibleCarryPairs_map_remainderOut
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.2.remainderOut) =
      (List.range requestedBlocks).map (fun j => C.longDivisionRemainder (j + 1)) := by
  calc
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.2.remainderOut)
      = ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map Prod.snd).map
          RemainderTraceStep.remainderOut := by
            simp
    _ = (C.remainderTrace requestedBlocks).map RemainderTraceStep.remainderOut := by
          rw [C.visibleCarryPairs_map_remainderStep]
    _ = (List.range requestedBlocks).map (fun j => C.longDivisionRemainder (j + 1)) :=
          C.remainderTrace_map_remainderOut requestedBlocks

theorem BlockCoordinate.visibleCarryPairs_map_carryBlockValue
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.1.blockValue) =
      C.visibleCarryWord hgood requestedBlocks lookaheadBlocks := by
  calc
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.1.blockValue)
      = ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map Prod.fst).map
          CarryTraceStep.blockValue := by
            simp
    _ = (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.blockValue := by
          rw [C.visibleCarryPairs_map_carryStep]
    _ = C.visibleCarryWord hgood requestedBlocks lookaheadBlocks :=
          C.visibleCarryTrace_map_blockValue hgood requestedBlocks lookaheadBlocks

theorem BlockCoordinate.visibleCarryPairs_map_remainderBlockValue
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.2.blockValue) =
      C.emittedBlockWord requestedBlocks := by
  calc
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.2.blockValue)
      = ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map Prod.snd).map
          RemainderTraceStep.blockValue := by
            simp
    _ = (C.remainderTrace requestedBlocks).map RemainderTraceStep.blockValue := by
          rw [C.visibleCarryPairs_map_remainderStep]
    _ = C.emittedBlockWord requestedBlocks := C.remainderTrace_map_blockValue requestedBlocks

theorem BlockCoordinate.visibleCarryPairs_output_agreement_of_lookaheadCertificate
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (requestedBlocks lookaheadBlocks : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.1.blockValue) =
      (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map (fun pair => pair.2.blockValue) := by
  rw [C.visibleCarryPairs_map_carryBlockValue, C.visibleCarryPairs_map_remainderBlockValue]
  exact C.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate
    hgood hmod requestedBlocks lookaheadBlocks hcert

theorem BlockCoordinate.visibleCarryPairs_output_agreement_of_lookaheadCertificate_add
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (requestedBlocks lookaheadBlocks extraLookahead : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    (C.visibleCarryPairs hgood requestedBlocks (lookaheadBlocks + extraLookahead)).map
        (fun pair => pair.1.blockValue) =
      (C.visibleCarryPairs hgood requestedBlocks (lookaheadBlocks + extraLookahead)).map
        (fun pair => pair.2.blockValue) := by
  rw [C.visibleCarryPairs_map_carryBlockValue, C.visibleCarryPairs_map_remainderBlockValue]
  exact C.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate_add
    hgood hmod requestedBlocks lookaheadBlocks extraLookahead hcert

/-- Exact same-core transport form for finite carried/remainder output
agreement on the shifted actual denominator. -/
theorem actualCoordinate_visibleCarryPairs_output_agreement_of_core_lookaheadCertificate_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (actualCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hcert :
      (strippedCoordinate base n stride hn).lookaheadCertificateHolds
        requestedBlocks lookaheadBlocks) :
    ((actualCoordinate base n stride hn).visibleCarryPairs hgood (requestedBlocks + s) lookaheadBlocks).map
        (fun pair => pair.1.blockValue) =
      ((actualCoordinate base n stride hn).visibleCarryPairs hgood (requestedBlocks + s) lookaheadBlocks).map
        (fun pair => pair.2.blockValue) := by
  let actual := actualCoordinate base n stride hn
  rw [actual.visibleCarryPairs_map_carryBlockValue, actual.visibleCarryPairs_map_remainderBlockValue]
  exact actualCoordinate_visibleCarryWord_eq_emittedBlockWord_of_core_lookaheadCertificate_add_exact
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hgood hmod hcompat hfactor hcert

/-- Gap-arithmetic transport form for finite carried/remainder output
agreement on the shifted actual denominator. This stays below the open
global visibility boundary. -/
theorem actualCoordinate_visibleCarryPairs_output_agreement_of_core_tail_lt_gapModulus_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (actualCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (htail :
      (strippedCoordinate base n stride hn).remainderK ^ (requestedBlocks + lookaheadBlocks) <
        (strippedCoordinate base n stride hn).lookaheadGapNumerator
          requestedBlocks lookaheadBlocks *
          (strippedCoordinate base n stride hn).modulus) :
    ((actualCoordinate base n stride hn).visibleCarryPairs hgood (requestedBlocks + s) lookaheadBlocks).map
        (fun pair => pair.1.blockValue) =
      ((actualCoordinate base n stride hn).visibleCarryPairs hgood (requestedBlocks + s) lookaheadBlocks).map
        (fun pair => pair.2.blockValue) := by
  let actual := actualCoordinate base n stride hn
  rw [actual.visibleCarryPairs_map_carryBlockValue, actual.visibleCarryPairs_map_remainderBlockValue]
  exact actualCoordinate_visibleCarryWord_eq_emittedBlockWord_of_core_tail_lt_gapModulus_add_exact
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hgood hmod hcompat hfactor htail

/-- Reverse gap-arithmetic transport form for finite carried/remainder output
agreement on the stripped core. This packages the unshifted side of the same
finite-window comparison theorem. -/
theorem strippedCoordinate_visibleCarryPairs_output_agreement_of_actual_tail_lt_gapModulus_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (strippedCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (htail :
      (actualCoordinate base n stride hn).remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) <
        (actualCoordinate base n stride hn).lookaheadGapNumerator
          (requestedBlocks + s) lookaheadBlocks *
          (actualCoordinate base n stride hn).modulus) :
    ((strippedCoordinate base n stride hn).visibleCarryPairs
        (strippedCoordinate_goodMode_of_actual_goodMode hn hgood) requestedBlocks lookaheadBlocks).map
        (fun pair => pair.1.blockValue) =
      ((strippedCoordinate base n stride hn).visibleCarryPairs
        (strippedCoordinate_goodMode_of_actual_goodMode hn hgood) requestedBlocks lookaheadBlocks).map
        (fun pair => pair.2.blockValue) := by
  let core := strippedCoordinate base n stride hn
  let hcoreGood := strippedCoordinate_goodMode_of_actual_goodMode hn hgood
  rw [core.visibleCarryPairs_map_carryBlockValue, core.visibleCarryPairs_map_remainderBlockValue]
  exact strippedCoordinate_visibleCarryWord_eq_emittedBlockWord_of_actual_tail_lt_gapModulus_add_exact
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hgood hmod hcompat hfactor htail

theorem BlockCoordinate.visibleCarryPairs_output_agreement_pointwise_of_lookaheadCertificate
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (requestedBlocks lookaheadBlocks : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks)
    (i : ℕ) (hi : i < (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).length) :
    ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks)[i]'hi).1.blockValue =
      ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks)[i]'hi).2.blockValue := by
  let pairs := C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks
  have hmap :
      (pairs.map (fun pair => pair.1.blockValue))[i]? =
        (pairs.map (fun pair => pair.2.blockValue))[i]? := by
    simpa [pairs] using congrArg
      (fun l => l[i]?)
      (C.visibleCarryPairs_output_agreement_of_lookaheadCertificate
        hgood hmod requestedBlocks lookaheadBlocks hcert)
  have hsome :
      some ((pairs[i]'hi).1.blockValue) = some ((pairs[i]'hi).2.blockValue) := by
    simpa [pairs, List.getElem?_eq_getElem hi] using hmap
  exact Option.some.inj hsome

/-- Pointwise gap-arithmetic transport form for finite carried/remainder output
agreement on the shifted actual denominator. -/
theorem actualCoordinate_visibleCarryPairs_output_agreement_pointwise_of_core_tail_lt_gapModulus_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (actualCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (htail :
      (strippedCoordinate base n stride hn).remainderK ^ (requestedBlocks + lookaheadBlocks) <
        (strippedCoordinate base n stride hn).lookaheadGapNumerator
          requestedBlocks lookaheadBlocks *
          (strippedCoordinate base n stride hn).modulus)
    (i : ℕ)
    (hi :
      i < ((actualCoordinate base n stride hn).visibleCarryPairs hgood
        (requestedBlocks + s) lookaheadBlocks).length) :
    (((actualCoordinate base n stride hn).visibleCarryPairs hgood
        (requestedBlocks + s) lookaheadBlocks)[i]'hi).1.blockValue =
      (((actualCoordinate base n stride hn).visibleCarryPairs hgood
        (requestedBlocks + s) lookaheadBlocks)[i]'hi).2.blockValue := by
  let actual := actualCoordinate base n stride hn
  have htailActual :
      actual.remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) <
        actual.lookaheadGapNumerator (requestedBlocks + s) lookaheadBlocks * actual.modulus :=
    (sameCoreCompatible_tail_lt_gapModulus_iff_add_exact
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hcompat hfactor).2 htail
  have hcertActual :
      actual.lookaheadCertificateHolds (requestedBlocks + s) lookaheadBlocks := by
    rw [actual.lookaheadCertificateHolds_iff_tail_lt_gapModulus
      hgood (requestedBlocks + s) lookaheadBlocks]
    exact htailActual
  exact actual.visibleCarryPairs_output_agreement_pointwise_of_lookaheadCertificate
    hgood hmod (requestedBlocks + s) lookaheadBlocks hcertActual i hi

/-- Reverse pointwise gap-arithmetic transport form for finite
carried/remainder output agreement on the stripped core. -/
theorem strippedCoordinate_visibleCarryPairs_output_agreement_pointwise_of_actual_tail_lt_gapModulus_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (strippedCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (htail :
      (actualCoordinate base n stride hn).remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) <
        (actualCoordinate base n stride hn).lookaheadGapNumerator
          (requestedBlocks + s) lookaheadBlocks *
          (actualCoordinate base n stride hn).modulus)
    (i : ℕ)
    (hi :
      i < ((strippedCoordinate base n stride hn).visibleCarryPairs
        (strippedCoordinate_goodMode_of_actual_goodMode hn hgood)
        requestedBlocks lookaheadBlocks).length) :
    (((strippedCoordinate base n stride hn).visibleCarryPairs
        (strippedCoordinate_goodMode_of_actual_goodMode hn hgood)
        requestedBlocks lookaheadBlocks)[i]'hi).1.blockValue =
      (((strippedCoordinate base n stride hn).visibleCarryPairs
        (strippedCoordinate_goodMode_of_actual_goodMode hn hgood)
        requestedBlocks lookaheadBlocks)[i]'hi).2.blockValue := by
  let core := strippedCoordinate base n stride hn
  let hcoreGood := strippedCoordinate_goodMode_of_actual_goodMode hn hgood
  have htailCore :
      core.remainderK ^ (requestedBlocks + lookaheadBlocks) <
        core.lookaheadGapNumerator requestedBlocks lookaheadBlocks * core.modulus :=
    (sameCoreCompatible_tail_lt_gapModulus_iff_add_exact
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hcompat hfactor).1 htail
  have hcertCore :
      core.lookaheadCertificateHolds requestedBlocks lookaheadBlocks := by
    rw [core.lookaheadCertificateHolds_iff_tail_lt_gapModulus
      hcoreGood requestedBlocks lookaheadBlocks]
    exact htailCore
  exact core.visibleCarryPairs_output_agreement_pointwise_of_lookaheadCertificate
    hcoreGood hmod requestedBlocks lookaheadBlocks hcertCore i hi

theorem BlockCoordinate.visibleCarryPairs_carry_balance
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (i : ℕ) (hi : i < (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).length) :
    ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks)[i]'hi).1.coefficient +
        ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks)[i]'hi).1.carryIn =
      ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks)[i]'hi).1.blockValue +
        C.blockBase * ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks)[i]'hi).1.carryOut := by
  let pairs := C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks
  have hpairsLen : pairs.length = requestedBlocks := by
    simpa [pairs] using C.visibleCarryPairs_length hgood requestedBlocks lookaheadBlocks
  have hiRequested : i < requestedBlocks := by
    rw [← hpairsLen]
    exact hi
  have hiTrace : i < (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).length := by
    rw [C.visibleCarryTrace_length]
    exact hiRequested
  have hstep_eq :
      ((pairs[i]'hi).1) = (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks)[i]'hiTrace := by
    have hmap :
        (pairs.map Prod.fst)[i]? =
          (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks)[i]? := by
      simpa [pairs] using congrArg
        (fun l => l[i]?) (C.visibleCarryPairs_map_carryStep hgood requestedBlocks lookaheadBlocks)
    have hsome :
        some ((pairs[i]'hi).1) =
          some ((C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks)[i]'hiTrace) := by
      simpa [pairs, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiTrace] using hmap
    exact Option.some.inj hsome
  have hmemVisible :
      ((pairs[i]'hi).1) ∈ C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks := by
    rw [hstep_eq]
    exact List.getElem_mem _
  have hmemTrace :
      ((pairs[i]'hi).1) ∈ C.traceRawWord hgood (requestedBlocks + lookaheadBlocks) :=
    C.mem_visibleCarryTrace hgood hmemVisible
  simpa [pairs] using C.mem_traceRawWord_value hgood hmemTrace

theorem BlockCoordinate.visibleCarryPairs_remainder_balance
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (i : ℕ) (hi : i < (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).length) :
    C.blockBase * ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks)[i]'hi).2.remainderIn =
      ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks)[i]'hi).2.blockValue * C.modulus +
        ((C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks)[i]'hi).2.remainderOut := by
  let pairs := C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks
  have hpairsLen : pairs.length = requestedBlocks := by
    simpa [pairs] using C.visibleCarryPairs_length hgood requestedBlocks lookaheadBlocks
  have hiRequested : i < requestedBlocks := by
    rw [← hpairsLen]
    exact hi
  have hiTrace : i < (C.remainderTrace requestedBlocks).length := by
    rw [C.remainderTrace_length]
    exact hiRequested
  have hstep_eq :
      ((pairs[i]'hi).2) = (C.remainderTrace requestedBlocks)[i]'hiTrace := by
    have hmap :
        (pairs.map Prod.snd)[i]? =
          (C.remainderTrace requestedBlocks)[i]? := by
      simpa [pairs] using congrArg
        (fun l => l[i]?) (C.visibleCarryPairs_map_remainderStep hgood requestedBlocks lookaheadBlocks)
    have hsome :
        some ((pairs[i]'hi).2) =
          some ((C.remainderTrace requestedBlocks)[i]'hiTrace) := by
      simpa [pairs, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiTrace] using hmap
    exact Option.some.inj hsome
  have hindex :
      (C.remainderTrace requestedBlocks)[i]'hiTrace = C.remainderTraceStep i := by
    simp [BlockCoordinate.remainderTrace]
  calc
    C.blockBase * ((pairs[i]'hi).2).remainderIn =
      C.blockBase * (C.remainderTraceStep i).remainderIn := by rw [hstep_eq, hindex]
    _ = (C.remainderTraceStep i).blockValue * C.modulus + (C.remainderTraceStep i).remainderOut :=
      C.remainderTraceStep_value i
    _ = ((pairs[i]'hi).2).blockValue * C.modulus + ((pairs[i]'hi).2).remainderOut := by
      rw [hstep_eq, hindex]

/-- Extract the observed remainder-to-carry state relation on one finite window. -/
def BlockCoordinate.remainderToCarryPairs
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) : List (ℕ × ℕ) :=
  (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map
    (fun pair => (pair.2.remainderIn, pair.1.carryIn))

/-- Extract the observed carry-to-remainder state relation on one finite window. -/
def BlockCoordinate.carryToRemainderPairs
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) : List (ℕ × ℕ) :=
  (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).map
    (fun pair => (pair.1.carryIn, pair.2.remainderIn))

/-- One aligned visible-window comparison record. -/
structure StateAlignment where
  position : ℕ
  coefficient : ℕ
  carryIn : ℕ
  carryOut : ℕ
  remainderIn : ℕ
  remainderOut : ℕ
  carryBlockValue : ℕ
  remainderBlockValue : ℕ
deriving Repr, DecidableEq

/-- Convert an indexed visible carry/remainder pair into a named alignment record. -/
def StateAlignment.ofZipIdxEntry
    (entry : (CarryTraceStep × RemainderTraceStep) × ℕ) : StateAlignment :=
  let ((carryStep, remainderStep), position) := entry
  {
    position := position
    coefficient := carryStep.coefficient
    carryIn := carryStep.carryIn
    carryOut := carryStep.carryOut
    remainderIn := remainderStep.remainderIn
    remainderOut := remainderStep.remainderOut
    carryBlockValue := carryStep.blockValue
    remainderBlockValue := remainderStep.blockValue
  }

/-- Indexed alignment records for the visible carry/remainder comparison window. -/
def BlockCoordinate.stateAlignments
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) : List StateAlignment :=
  (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).zipIdx.map StateAlignment.ofZipIdxEntry

theorem BlockCoordinate.stateAlignments_length
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length = requestedBlocks := by
  simp [BlockCoordinate.stateAlignments, C.visibleCarryPairs_length]

theorem BlockCoordinate.stateAlignments_map_position
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.position =
      List.range requestedBlocks := by
  apply List.ext_getElem
  · rw [List.length_map, C.stateAlignments_length, List.length_range]
  · intro i hleft hright
    simp [BlockCoordinate.stateAlignments, StateAlignment.ofZipIdxEntry]

theorem BlockCoordinate.stateAlignments_map_coefficient
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.coefficient =
      C.rawCoefficientWord requestedBlocks := by
  apply List.ext_getElem
  · rw [List.length_map, C.stateAlignments_length, C.rawCoefficientWord_length]
  · intro i hleft hright
    have hmap :
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.coefficient)[i]? =
          (C.rawCoefficientWord requestedBlocks)[i]? := by
      simpa [BlockCoordinate.stateAlignments, StateAlignment.ofZipIdxEntry] using congrArg
        (fun l => l[i]?) (C.visibleCarryPairs_map_coefficient hgood requestedBlocks lookaheadBlocks)
    simpa [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] using hmap

theorem BlockCoordinate.stateAlignments_map_carryIn
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.carryIn =
      (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.carryIn := by
  apply List.ext_getElem
  · rw [List.length_map, C.stateAlignments_length, List.length_map, C.visibleCarryTrace_length]
  · intro i hleft hright
    have hmap :
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.carryIn)[i]? =
          ((C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.carryIn)[i]? := by
      simpa [BlockCoordinate.stateAlignments, StateAlignment.ofZipIdxEntry] using congrArg
        (fun l => l[i]?) (C.visibleCarryPairs_map_carryIn hgood requestedBlocks lookaheadBlocks)
    simpa [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] using hmap

theorem BlockCoordinate.stateAlignments_map_carryOut
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.carryOut =
      (C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.carryOut := by
  apply List.ext_getElem
  · rw [List.length_map, C.stateAlignments_length, List.length_map, C.visibleCarryTrace_length]
  · intro i hleft hright
    have hmap :
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.carryOut)[i]? =
          ((C.visibleCarryTrace hgood requestedBlocks lookaheadBlocks).map CarryTraceStep.carryOut)[i]? := by
      simpa [BlockCoordinate.stateAlignments, StateAlignment.ofZipIdxEntry] using congrArg
        (fun l => l[i]?) (C.visibleCarryPairs_map_carryOut hgood requestedBlocks lookaheadBlocks)
    simpa [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] using hmap

theorem BlockCoordinate.stateAlignments_map_remainderIn
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.remainderIn =
      (List.range requestedBlocks).map C.longDivisionRemainder := by
  apply List.ext_getElem
  · rw [List.length_map, C.stateAlignments_length, List.length_map, List.length_range]
  · intro i hleft hright
    have hmap :
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.remainderIn)[i]? =
          ((List.range requestedBlocks).map C.longDivisionRemainder)[i]? := by
      simpa [BlockCoordinate.stateAlignments, StateAlignment.ofZipIdxEntry] using congrArg
        (fun l => l[i]?) (C.visibleCarryPairs_map_remainderIn hgood requestedBlocks lookaheadBlocks)
    simpa [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] using hmap

theorem BlockCoordinate.stateAlignments_map_remainderOut
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.remainderOut =
      (List.range requestedBlocks).map (fun j => C.longDivisionRemainder (j + 1)) := by
  apply List.ext_getElem
  · rw [List.length_map, C.stateAlignments_length, List.length_map, List.length_range]
  · intro i hleft hright
    have hmap :
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.remainderOut)[i]? =
          ((List.range requestedBlocks).map (fun j => C.longDivisionRemainder (j + 1)))[i]? := by
      simpa [BlockCoordinate.stateAlignments, StateAlignment.ofZipIdxEntry] using congrArg
        (fun l => l[i]?) (C.visibleCarryPairs_map_remainderOut hgood requestedBlocks lookaheadBlocks)
    simpa [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] using hmap

theorem BlockCoordinate.stateAlignments_map_carryBlockValue
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.carryBlockValue =
      C.visibleCarryWord hgood requestedBlocks lookaheadBlocks := by
  apply List.ext_getElem
  · rw [List.length_map, C.stateAlignments_length, C.visibleCarryWord_length]
  · intro i hleft hright
    have hmap :
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.carryBlockValue)[i]? =
          (C.visibleCarryWord hgood requestedBlocks lookaheadBlocks)[i]? := by
      simpa [BlockCoordinate.stateAlignments, StateAlignment.ofZipIdxEntry] using congrArg
        (fun l => l[i]?) (C.visibleCarryPairs_map_carryBlockValue hgood requestedBlocks lookaheadBlocks)
    simpa [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] using hmap

theorem BlockCoordinate.stateAlignments_map_remainderBlockValue
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.remainderBlockValue =
      C.emittedBlockWord requestedBlocks := by
  apply List.ext_getElem
  · rw [List.length_map, C.stateAlignments_length]
    simp [BlockCoordinate.emittedBlockWord]
  · intro i hleft hright
    have hmap :
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.remainderBlockValue)[i]? =
          (C.emittedBlockWord requestedBlocks)[i]? := by
      simpa [BlockCoordinate.stateAlignments, StateAlignment.ofZipIdxEntry] using congrArg
        (fun l => l[i]?) (C.visibleCarryPairs_map_remainderBlockValue hgood requestedBlocks lookaheadBlocks)
    simpa [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] using hmap

theorem BlockCoordinate.stateAlignments_map_remainderToCarryPairs
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.carryIn)) =
      C.remainderToCarryPairs hgood requestedBlocks lookaheadBlocks := by
  apply List.ext_getElem
  · simp [BlockCoordinate.stateAlignments, BlockCoordinate.remainderToCarryPairs,
      C.visibleCarryPairs_length]
  · intro i hleft hright
    simp [BlockCoordinate.stateAlignments, BlockCoordinate.remainderToCarryPairs,
      StateAlignment.ofZipIdxEntry]

theorem BlockCoordinate.stateAlignments_map_carryToRemainderPairs
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map
        (fun alignment => (alignment.carryIn, alignment.remainderIn)) =
      C.carryToRemainderPairs hgood requestedBlocks lookaheadBlocks := by
  apply List.ext_getElem
  · simp [BlockCoordinate.stateAlignments, BlockCoordinate.carryToRemainderPairs,
      C.visibleCarryPairs_length]
  · intro i hleft hright
    simp [BlockCoordinate.stateAlignments, BlockCoordinate.carryToRemainderPairs,
      StateAlignment.ofZipIdxEntry]

def BlockCoordinate.remainderToCarryFunctional
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) : Prop :=
  ∀ i (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
      j (hj : j < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length),
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderIn →
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryIn

def BlockCoordinate.carryToRemainderFunctional
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) : Prop :=
  ∀ i (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
      j (hj : j < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length),
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryIn →
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderIn

theorem BlockCoordinate.remainderToCarryFunctional_iff_functionalOnFst_pairs
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    C.remainderToCarryFunctional hgood requestedBlocks lookaheadBlocks ↔
      List.FunctionalOnFst (C.remainderToCarryPairs hgood requestedBlocks lookaheadBlocks) := by
  constructor
  · intro h
    rw [← C.stateAlignments_map_remainderToCarryPairs, List.functionalOnFst_iff_getElem]
    intro i hi j hj heq
    simpa using h i (by simpa using hi) j (by simpa using hj) (by simpa using heq)
  · intro h
    rw [← C.stateAlignments_map_remainderToCarryPairs, List.functionalOnFst_iff_getElem] at h
    intro i hi j hj heq
    have hpair :
        ((List.map (fun alignment => (alignment.remainderIn, alignment.carryIn))
            (C.stateAlignments hgood requestedBlocks lookaheadBlocks))[i]'(by simpa using hi)).2 =
          ((List.map (fun alignment => (alignment.remainderIn, alignment.carryIn))
            (C.stateAlignments hgood requestedBlocks lookaheadBlocks))[j]'(by simpa using hj)).2 :=
      h i (by simpa using hi) j (by simpa using hj) (by simpa using heq)
    simpa using hpair

theorem BlockCoordinate.carryToRemainderFunctional_iff_functionalOnFst_pairs
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) :
    C.carryToRemainderFunctional hgood requestedBlocks lookaheadBlocks ↔
      List.FunctionalOnFst (C.carryToRemainderPairs hgood requestedBlocks lookaheadBlocks) := by
  constructor
  · intro h
    rw [← C.stateAlignments_map_carryToRemainderPairs, List.functionalOnFst_iff_getElem]
    intro i hi j hj heq
    simpa using h i (by simpa using hi) j (by simpa using hj) (by simpa using heq)
  · intro h
    rw [← C.stateAlignments_map_carryToRemainderPairs, List.functionalOnFst_iff_getElem] at h
    intro i hi j hj heq
    have hpair :
        ((List.map (fun alignment => (alignment.carryIn, alignment.remainderIn))
            (C.stateAlignments hgood requestedBlocks lookaheadBlocks))[i]'(by simpa using hi)).2 =
          ((List.map (fun alignment => (alignment.carryIn, alignment.remainderIn))
            (C.stateAlignments hgood requestedBlocks lookaheadBlocks))[j]'(by simpa using hj)).2 :=
      h i (by simpa using hi) j (by simpa using hj) (by simpa using heq)
    simpa using hpair

theorem BlockCoordinate.stateAlignments_output_agreement_of_lookaheadCertificate
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (requestedBlocks lookaheadBlocks : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks) :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.carryBlockValue =
      (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.remainderBlockValue := by
  rw [C.stateAlignments_map_carryBlockValue, C.stateAlignments_map_remainderBlockValue]
  exact C.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate
    hgood hmod requestedBlocks lookaheadBlocks hcert

theorem BlockCoordinate.stateAlignments_output_agreement_pointwise_of_lookaheadCertificate
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (requestedBlocks lookaheadBlocks : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length) :
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue =
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderBlockValue := by
  have hmap :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.carryBlockValue)[i]? =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.remainderBlockValue)[i]? := by
    simpa using congrArg
      (fun l => l[i]?)
      (C.stateAlignments_output_agreement_of_lookaheadCertificate
        hgood hmod requestedBlocks lookaheadBlocks hcert)
  have hsome :
      some ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue =
        some ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderBlockValue := by
    simpa [List.getElem?_eq_getElem hi] using hmap
  exact Option.some.inj hsome

theorem BlockCoordinate.stateAlignments_carry_balance
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length) :
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).coefficient +
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryIn =
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue +
        C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryOut := by
  have hpairs : i < (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).length := by
    simpa [BlockCoordinate.stateAlignments] using hi
  simpa [BlockCoordinate.stateAlignments, StateAlignment.ofZipIdxEntry] using
    C.visibleCarryPairs_carry_balance hgood requestedBlocks lookaheadBlocks i hpairs

theorem BlockCoordinate.stateAlignments_remainder_balance
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length) :
    C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn =
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderBlockValue * C.modulus +
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderOut := by
  have hpairs : i < (C.visibleCarryPairs hgood requestedBlocks lookaheadBlocks).length := by
    simpa [BlockCoordinate.stateAlignments] using hi
  simpa [BlockCoordinate.stateAlignments, StateAlignment.ofZipIdxEntry] using
    C.visibleCarryPairs_remainder_balance hgood requestedBlocks lookaheadBlocks i hpairs

theorem BlockCoordinate.stateAlignments_remainderIn_eq_longDivisionRemainder
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length) :
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn =
      C.longDivisionRemainder i := by
  have hiRequested : i < requestedBlocks := by
    rw [← C.stateAlignments_length hgood requestedBlocks lookaheadBlocks]
    exact hi
  have hmap :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.remainderIn)[i]? =
        ((List.range requestedBlocks).map C.longDivisionRemainder)[i]? := by
    simpa using congrArg
      (fun l => l[i]?) (C.stateAlignments_map_remainderIn hgood requestedBlocks lookaheadBlocks)
  simpa [List.getElem?_eq_getElem hi, hiRequested] using hmap

theorem BlockCoordinate.stateAlignments_remainderOut_eq_longDivisionRemainder_succ
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length) :
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderOut =
      C.longDivisionRemainder (i + 1) := by
  have hiRequested : i < requestedBlocks := by
    rw [← C.stateAlignments_length hgood requestedBlocks lookaheadBlocks]
    exact hi
  have hmap :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.remainderOut)[i]? =
        ((List.range requestedBlocks).map (fun j => C.longDivisionRemainder (j + 1)))[i]? := by
    simpa using congrArg
      (fun l => l[i]?) (C.stateAlignments_map_remainderOut hgood requestedBlocks lookaheadBlocks)
  simpa [List.getElem?_eq_getElem hi, hiRequested] using hmap

theorem BlockCoordinate.stateAlignments_remainderBlockValue_eq_emittedBlock
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length) :
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderBlockValue =
      C.emittedBlock i := by
  have hiRequested : i < requestedBlocks := by
    rw [← C.stateAlignments_length hgood requestedBlocks lookaheadBlocks]
    exact hi
  have hmap :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.remainderBlockValue)[i]? =
        (C.emittedBlockWord requestedBlocks)[i]? := by
    simpa using congrArg
      (fun l => l[i]?) (C.stateAlignments_map_remainderBlockValue hgood requestedBlocks lookaheadBlocks)
  simpa [BlockCoordinate.emittedBlockWord, List.getElem?_eq_getElem hi, hiRequested] using hmap

theorem BlockCoordinate.stateAlignments_remainderBlockValue_eq_div
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length) :
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderBlockValue =
      (C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn) /
        C.modulus := by
  rw [C.stateAlignments_remainderBlockValue_eq_emittedBlock hgood requestedBlocks lookaheadBlocks i hi,
    BlockCoordinate.emittedBlock, C.stateAlignments_remainderIn_eq_longDivisionRemainder
      hgood requestedBlocks lookaheadBlocks i hi]

theorem BlockCoordinate.stateAlignments_remainderOut_eq_mod
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length) :
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderOut =
      (C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn) %
        C.modulus := by
  rw [C.stateAlignments_remainderOut_eq_longDivisionRemainder_succ
      hgood requestedBlocks lookaheadBlocks i hi,
    BlockCoordinate.longDivisionRemainder,
    C.stateAlignments_remainderIn_eq_longDivisionRemainder hgood requestedBlocks lookaheadBlocks i hi]

theorem BlockCoordinate.stateAlignments_same_remainderIn_implies_same_remainderBlockValue
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (j : ℕ) (hj : j < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (hstate :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderIn) :
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderBlockValue =
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderBlockValue := by
  rw [C.stateAlignments_remainderBlockValue_eq_div hgood requestedBlocks lookaheadBlocks i hi,
    C.stateAlignments_remainderBlockValue_eq_div hgood requestedBlocks lookaheadBlocks j hj, hstate]

theorem BlockCoordinate.stateAlignments_same_remainderIn_implies_same_remainderOut
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (j : ℕ) (hj : j < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (hstate :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderIn) :
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderOut =
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderOut := by
  rw [C.stateAlignments_remainderOut_eq_mod hgood requestedBlocks lookaheadBlocks i hi,
    C.stateAlignments_remainderOut_eq_mod hgood requestedBlocks lookaheadBlocks j hj, hstate]

theorem BlockCoordinate.stateAlignments_carryBlockValue_eq_remainderBlockValue_of_lookaheadCertificate
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (requestedBlocks lookaheadBlocks : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length) :
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue =
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderBlockValue := by
  exact C.stateAlignments_output_agreement_pointwise_of_lookaheadCertificate
    hgood hmod requestedBlocks lookaheadBlocks hcert i hi

theorem BlockCoordinate.stateAlignments_same_remainderIn_implies_same_carryBlockValue_of_lookaheadCertificate
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (requestedBlocks lookaheadBlocks : ℕ)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (j : ℕ) (hj : j < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (hstate :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderIn) :
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue =
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryBlockValue := by
  calc
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue =
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderBlockValue :=
        C.stateAlignments_carryBlockValue_eq_remainderBlockValue_of_lookaheadCertificate
          hgood hmod requestedBlocks lookaheadBlocks hcert i hi
    _ = ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderBlockValue :=
        C.stateAlignments_same_remainderIn_implies_same_remainderBlockValue
          hgood requestedBlocks lookaheadBlocks i hi j hj hstate
    _ = ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryBlockValue := by
        symm
        exact C.stateAlignments_carryBlockValue_eq_remainderBlockValue_of_lookaheadCertificate
          hgood hmod requestedBlocks lookaheadBlocks hcert j hj

theorem BlockCoordinate.stateAlignments_remainderToCarry_transition_compatible_of_functional
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (requestedBlocks lookaheadBlocks : ℕ)
    (hfunc : C.remainderToCarryFunctional hgood requestedBlocks lookaheadBlocks)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (j : ℕ) (hj : j < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (hstate :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderIn)
    (hcoeff :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).coefficient =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).coefficient) :
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryIn ∧
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderBlockValue =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderBlockValue ∧
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryBlockValue ∧
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderOut =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderOut ∧
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryOut =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryOut := by
  have hcarryIn :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryIn :=
    hfunc i hi j hj hstate
  have hremBlock :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderBlockValue =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderBlockValue :=
    C.stateAlignments_same_remainderIn_implies_same_remainderBlockValue
      hgood requestedBlocks lookaheadBlocks i hi j hj hstate
  have hcarryBlock :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryBlockValue :=
    C.stateAlignments_same_remainderIn_implies_same_carryBlockValue_of_lookaheadCertificate
      hgood hmod requestedBlocks lookaheadBlocks hcert i hi j hj hstate
  have hremOut :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderOut =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderOut :=
    C.stateAlignments_same_remainderIn_implies_same_remainderOut
      hgood requestedBlocks lookaheadBlocks i hi j hj hstate
  have hcarryOut :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryOut =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryOut := by
    have hsum :
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue +
            C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryOut =
          ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue +
            C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryOut := by
      calc
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue +
            C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryOut =
          ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).coefficient +
            ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryIn := by
              symm
              exact C.stateAlignments_carry_balance hgood requestedBlocks lookaheadBlocks i hi
        _ =
          ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).coefficient +
            ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryIn := by
              rw [hcoeff, hcarryIn]
        _ =
          ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryBlockValue +
            C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryOut :=
              C.stateAlignments_carry_balance hgood requestedBlocks lookaheadBlocks j hj
        _ =
          ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue +
            C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryOut := by
              rw [hcarryBlock]
    have hmul :
        C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryOut =
          C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryOut :=
      Nat.add_left_cancel hsum
    exact Nat.eq_of_mul_eq_mul_left (C.blockBase_pos_of_goodMode hgood) hmul
  exact ⟨hcarryIn, hremBlock, hcarryBlock, hremOut, hcarryOut⟩

theorem BlockCoordinate.stateAlignments_carryToRemainder_transition_compatible_of_functional
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (requestedBlocks lookaheadBlocks : ℕ)
    (hfunc : C.carryToRemainderFunctional hgood requestedBlocks lookaheadBlocks)
    (hcert : C.lookaheadCertificateHolds requestedBlocks lookaheadBlocks)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (j : ℕ) (hj : j < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (hcarry :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryIn)
    (hcoeff :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).coefficient =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).coefficient) :
    ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderIn ∧
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderBlockValue =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderBlockValue ∧
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryBlockValue ∧
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderOut =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderOut ∧
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryOut =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryOut := by
  have hstate :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderIn :=
    hfunc i hi j hj hcarry
  have hremBlock :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderBlockValue =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderBlockValue :=
    C.stateAlignments_same_remainderIn_implies_same_remainderBlockValue
      hgood requestedBlocks lookaheadBlocks i hi j hj hstate
  have hcarryBlock :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryBlockValue :=
    C.stateAlignments_same_remainderIn_implies_same_carryBlockValue_of_lookaheadCertificate
      hgood hmod requestedBlocks lookaheadBlocks hcert i hi j hj hstate
  have hremOut :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderOut =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderOut :=
    C.stateAlignments_same_remainderIn_implies_same_remainderOut
      hgood requestedBlocks lookaheadBlocks i hi j hj hstate
  have hcarryOut :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryOut =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryOut := by
    have hsum :
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue +
            C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryOut =
          ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue +
            C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryOut := by
      calc
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue +
            C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryOut =
          ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).coefficient +
            ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryIn := by
              symm
              exact C.stateAlignments_carry_balance hgood requestedBlocks lookaheadBlocks i hi
        _ =
          ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).coefficient +
            ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryIn := by
              rw [hcoeff, hcarry]
        _ =
          ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryBlockValue +
            C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryOut :=
              C.stateAlignments_carry_balance hgood requestedBlocks lookaheadBlocks j hj
        _ =
          ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue +
            C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryOut := by
              rw [hcarryBlock]
    have hmul :
        C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryOut =
          C.blockBase * ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryOut :=
      Nat.add_left_cancel hsum
    exact Nat.eq_of_mul_eq_mul_left (C.blockBase_pos_of_goodMode hgood) hmul
  exact ⟨hstate, hremBlock, hcarryBlock, hremOut, hcarryOut⟩

theorem BlockCoordinate.not_remainderToCarryFunctional_of_conflict
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (j : ℕ) (hj : j < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (hstate :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderIn)
    (hcarry :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryIn ≠
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryIn) :
    ¬ C.remainderToCarryFunctional hgood requestedBlocks lookaheadBlocks := by
  intro hfunc
  exact hcarry (hfunc i hi j hj hstate)

theorem BlockCoordinate.not_carryToRemainderFunctional_of_conflict
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (j : ℕ) (hj : j < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (hcarry :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryIn)
    (hstate :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn ≠
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderIn) :
    ¬ C.carryToRemainderFunctional hgood requestedBlocks lookaheadBlocks := by
  intro hfunc
  exact hstate (hfunc i hi j hj hcarry)

theorem BlockCoordinate.blockBase_pow_mod_eq_remainderK_pow_mod
    (C : BlockCoordinate) (length : ℕ) :
    C.blockBase ^ length % C.modulus = C.remainderK ^ length % C.modulus := by
  induction length with
  | zero =>
      simp [BlockCoordinate.remainderK]
  | succ length ih =>
      calc
        C.blockBase ^ (length + 1) % C.modulus
          = ((C.blockBase ^ length % C.modulus) * (C.blockBase % C.modulus)) % C.modulus := by
              rw [pow_succ, Nat.mul_mod]
        _ = ((C.remainderK ^ length % C.modulus) * (C.blockBase % C.modulus)) % C.modulus := by
              rw [ih]
        _ = ((C.remainderK ^ length % C.modulus) * (C.remainderK % C.modulus)) % C.modulus := by
              simp [BlockCoordinate.remainderK]
        _ = ((C.remainderK ^ length % C.modulus) * C.remainderK) % C.modulus := by
              rw [Nat.mod_eq_of_lt C.remainderK_lt_modulus]
        _ = (C.remainderK ^ length * C.remainderK) % C.modulus := by
              symm
              rw [Nat.mul_mod, Nat.mod_eq_of_lt C.remainderK_lt_modulus]
        _ = C.remainderK ^ (length + 1) % C.modulus := by
              rw [pow_succ]

theorem actualCoordinate_rawCoefficientWord_eq_prefix_append_core_add_exact
    {base n stride s length : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (actualCoordinate base n stride hn).rawCoefficientWord (s + length) =
      (actualCoordinate base n stride hn).rawCoefficientWord s ++
        (strippedCoordinate base n stride hn).rawCoefficientWord length := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  induction length with
  | zero =>
      simp [BlockCoordinate.rawCoefficientWord]
  | succ length ih =>
      calc
        actual.rawCoefficientWord (s + (length + 1))
          = actual.rawCoefficientWord (s + length) ++ [actual.rawCoefficient (s + length)] := by
              rw [show s + (length + 1) = (s + length) + 1 by omega]
              simpa [actual] using actual.rawCoefficientWord_succ (s + length)
        _ = actual.rawCoefficientWord s ++ core.rawCoefficientWord length ++
              [actual.rawCoefficient (s + length)] := by
              rw [ih]
        _ = actual.rawCoefficientWord s ++ core.rawCoefficientWord length ++
              [core.rawCoefficient length] := by
              rw [show s + length = length + s by omega]
              rw [sameCoreCompatible_rawCoefficient_shift_exact
                (base := base) (n := n) (stride := stride) (s := s)
                (j := length) (hn := hn) hcompat hfactor]
        _ = actual.rawCoefficientWord s ++ core.rawCoefficientWord (length + 1) := by
              rw [core.rawCoefficientWord_succ]
              simp [List.append_assoc]

theorem actualCoordinate_traceRawWord_map_carryIn_drop_prefix_add_exact
    {base n stride s length : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (((actualCoordinate base n stride hn).traceRawWord hgood (s + length)).map
        CarryTraceStep.carryIn).drop s =
      ((strippedCoordinate base n stride hn).traceRawWord
          (sameCoreCompatible_goodMode_of_actual_goodMode
            (base := base) (n := n) (stride := stride) (hn := hn) hgood) length).map
        CarryTraceStep.carryIn := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  let hcoreGood :=
    sameCoreCompatible_goodMode_of_actual_goodMode
      (base := base) (n := n) (stride := stride) (hn := hn) hgood
  have hraw :
      actual.rawCoefficientWord (s + length) =
        actual.rawCoefficientWord s ++ core.rawCoefficientWord length := by
    simpa [actual, core] using
      actualCoordinate_rawCoefficientWord_eq_prefix_append_core_add_exact
        (base := base) (n := n) (stride := stride) (s := s) (length := length)
        (hn := hn) hcompat hfactor
  have hblockBase : actual.blockBase = core.blockBase := by
    rfl
  have hcarryDrop :
      List.drop (actual.rawCoefficientWord s).length
        (List.map CarryTraceStep.carryIn
          ((actual.carryTransducer hgood).traceBlocks
            (actual.rawCoefficientWord s ++ core.rawCoefficientWord length))) =
        List.map CarryTraceStep.carryIn
          ((actual.carryTransducer hgood).traceBlocks (core.rawCoefficientWord length)) := by
    simpa using
      (actual.carryTransducer hgood).traceBlocks_map_carryIn_drop_prefix_of_append
        (actual.rawCoefficientWord s) (core.rawCoefficientWord length)
  calc
    ((actual.traceRawWord hgood (s + length)).map CarryTraceStep.carryIn).drop s
      = (((actual.carryTransducer hgood).traceBlocks
            (actual.rawCoefficientWord s ++ core.rawCoefficientWord length)).map
          CarryTraceStep.carryIn).drop s := by
            simp [actual, BlockCoordinate.traceRawWord, hraw]
    _ = ((actual.carryTransducer hgood).traceBlocks (core.rawCoefficientWord length)).map
          CarryTraceStep.carryIn := by
            simpa [actual.rawCoefficientWord_length] using hcarryDrop
    _ = ((core.traceRawWord hcoreGood length).map CarryTraceStep.carryIn) := by
          simp [hblockBase, core, BlockCoordinate.traceRawWord, BlockCoordinate.carryTransducer]

theorem actualCoordinate_visibleCarryTrace_map_carryIn_drop_prefix_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (((actualCoordinate base n stride hn).visibleCarryTrace hgood
          (requestedBlocks + s) lookaheadBlocks).map CarryTraceStep.carryIn).drop s =
      ((strippedCoordinate base n stride hn).visibleCarryTrace
          (sameCoreCompatible_goodMode_of_actual_goodMode
            (base := base) (n := n) (stride := stride) (hn := hn) hgood)
          requestedBlocks lookaheadBlocks).map CarryTraceStep.carryIn := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  let hcoreGood :=
    sameCoreCompatible_goodMode_of_actual_goodMode
      (base := base) (n := n) (stride := stride) (hn := hn) hgood
  let actualCarryIns :=
    ((actual.traceRawWord hgood (s + (requestedBlocks + lookaheadBlocks))).map
      CarryTraceStep.carryIn)
  let coreCarryIns :=
    ((core.traceRawWord hcoreGood (requestedBlocks + lookaheadBlocks)).map
      CarryTraceStep.carryIn)
  have htrace :
      actualCarryIns.drop s = coreCarryIns := by
    simpa [actualCarryIns, coreCarryIns, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      actualCoordinate_traceRawWord_map_carryIn_drop_prefix_add_exact
        (base := base) (n := n) (stride := stride) (s := s)
        (length := requestedBlocks + lookaheadBlocks) (hn := hn) hgood hcompat hfactor
  calc
    (((actual.visibleCarryTrace hgood (requestedBlocks + s) lookaheadBlocks).map
          CarryTraceStep.carryIn).drop s)
      = (actualCarryIns.rdrop lookaheadBlocks).drop s := by
          simp [actualCarryIns, actual, BlockCoordinate.visibleCarryTrace_map_carryIn,
            Nat.add_left_comm, Nat.add_comm]
    _ = (actualCarryIns.drop s).rdrop lookaheadBlocks := by
          apply List.drop_rdrop_eq_rdrop_drop_of_length_eq (n := requestedBlocks)
          simp [actualCarryIns, List.length_map, actual.traceRawWord_length,
            Nat.add_left_comm, Nat.add_comm]
    _ = coreCarryIns.rdrop lookaheadBlocks := by
          rw [htrace]
    _ = ((core.visibleCarryTrace hcoreGood requestedBlocks lookaheadBlocks).map
          CarryTraceStep.carryIn) := by
          simp [coreCarryIns, core, BlockCoordinate.visibleCarryTrace_map_carryIn]

theorem actualCoordinate_longDivisionRemainder_add_exact
    {base n stride s j : ℕ} {hn : 0 < n}
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s) :
    (actualCoordinate base n stride hn).longDivisionRemainder (j + s) =
      (actualCoordinate base n stride hn).remainderK ^ s *
        (strippedCoordinate base n stride hn).longDivisionRemainder j := by
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
      _ = actual.remainderK ^ s * core.modulus := by
          rw [hfactor]
  have hcorePow :
      core.remainderK ^ j % core.modulus = core.longDivisionRemainder j := by
    rw [← core.blockBase_pow_mod_eq_remainderK_pow_mod, core.longDivisionRemainder_eq_pow_mod]
  calc
    actual.longDivisionRemainder (j + s)
      = actual.blockBase ^ (j + s) % actual.modulus := by
          rw [actual.longDivisionRemainder_eq_pow_mod]
    _ = actual.remainderK ^ (j + s) % actual.modulus := by
          rw [actual.blockBase_pow_mod_eq_remainderK_pow_mod]
    _ = (actual.remainderK ^ s * actual.remainderK ^ j) % actual.modulus := by
          rw [show j + s = s + j by omega, Nat.pow_add, Nat.mul_comm]
    _ = actual.remainderK ^ s * (actual.remainderK ^ j % core.modulus) := by
          rw [hmod, Nat.mul_mod_mul_left]
    _ = actual.remainderK ^ s * (core.remainderK ^ j % core.modulus) := by
          rw [← hsharedK]
    _ = actual.remainderK ^ s * core.longDivisionRemainder j := by
          rw [hcorePow]

theorem actualCoordinate_longDivisionRemainder_prefix_eq_pow
    {base n stride s i : ℕ} {hn : 0 < n}
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hi : i < s) :
    (actualCoordinate base n stride hn).longDivisionRemainder i =
      (actualCoordinate base n stride hn).remainderK ^ i := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  have hmod :
      actual.modulus = actual.remainderK ^ s * core.modulus := by
    calc
      actual.modulus = basePrimeSupportFactor base n * core.modulus := by
        simpa [actual, core, strippedPeriodModulus] using
          (basePrimeSupportFactor_mul_strippedPeriodModulus base n).symm
      _ = actual.remainderK ^ s * core.modulus := by
          rw [hfactor]
  have hpow_lt_shift : actual.remainderK ^ i < actual.remainderK ^ s := by
    exact Nat.pow_lt_pow_right hk hi
  have hpow_le_mod : actual.remainderK ^ s ≤ actual.modulus := by
    rw [hmod]
    exact Nat.le_mul_of_pos_right _ (strippedPeriodModulus_pos hn)
  have hpow_lt_mod : actual.remainderK ^ i < actual.modulus :=
    lt_of_lt_of_le hpow_lt_shift hpow_le_mod
  calc
    actual.longDivisionRemainder i = actual.blockBase ^ i % actual.modulus := by
      rw [actual.longDivisionRemainder_eq_pow_mod]
    _ = actual.remainderK ^ i % actual.modulus := by
      rw [actual.blockBase_pow_mod_eq_remainderK_pow_mod]
    _ = actual.remainderK ^ i := Nat.mod_eq_of_lt hpow_lt_mod

theorem actualCoordinate_stateAlignments_carryIn_shift_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (j : ℕ)
    (hjActual :
      j + s < ((actualCoordinate base n stride hn).stateAlignments hgood
        (requestedBlocks + s) lookaheadBlocks).length)
    (hjCore :
      j < ((strippedCoordinate base n stride hn).stateAlignments
        (sameCoreCompatible_goodMode_of_actual_goodMode
          (base := base) (n := n) (stride := stride) (hn := hn) hgood)
        requestedBlocks lookaheadBlocks).length) :
    (((actualCoordinate base n stride hn).stateAlignments hgood
        (requestedBlocks + s) lookaheadBlocks)[j + s]'hjActual).carryIn =
      (((strippedCoordinate base n stride hn).stateAlignments
          (sameCoreCompatible_goodMode_of_actual_goodMode
            (base := base) (n := n) (stride := stride) (hn := hn) hgood)
          requestedBlocks lookaheadBlocks)[j]'hjCore).carryIn := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  let hcoreGood :=
    sameCoreCompatible_goodMode_of_actual_goodMode
      (base := base) (n := n) (stride := stride) (hn := hn) hgood
  let actualCarryStates :=
    (actual.stateAlignments hgood (requestedBlocks + s) lookaheadBlocks).map StateAlignment.carryIn
  let coreCarryStates :=
    (core.stateAlignments hcoreGood requestedBlocks lookaheadBlocks).map StateAlignment.carryIn
  have hmap :
      actualCarryStates.drop s = coreCarryStates := by
    simpa [actualCarryStates, coreCarryStates, actual.stateAlignments_map_carryIn,
      core.stateAlignments_map_carryIn] using
      actualCoordinate_visibleCarryTrace_map_carryIn_drop_prefix_add_exact
        (base := base) (n := n) (stride := stride) (s := s)
        (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
        (hn := hn) hgood hcompat hfactor
  have hjCoreCarry : j < coreCarryStates.length := by
    simpa [coreCarryStates] using hjCore
  have hjDrop : j < (actualCarryStates.drop s).length := by
    simpa [hmap] using hjCoreCarry
  have hget :
      (actualCarryStates.drop s)[j]'hjDrop = coreCarryStates[j]'hjCoreCarry := by
    have hopt :
        (actualCarryStates.drop s)[j]? = coreCarryStates[j]? := by
      simpa using congrArg (fun l => l[j]?) hmap
    exact Option.some.inj (by
      simpa [List.getElem?_eq_getElem hjDrop, List.getElem?_eq_getElem hjCoreCarry] using hopt)
  have hdropEq :
      (actualCarryStates.drop s)[j]'hjDrop =
        actualCarryStates[j + s]'(by simpa [actualCarryStates] using hjActual) := by
    have hdropEq' :
        (actualCarryStates.drop s)[j]'hjDrop =
          actualCarryStates[s + j]'(by simpa [actualCarryStates, Nat.add_comm] using hjActual) := by
      exact List.getElem_drop (xs := actualCarryStates) (i := s) (j := j) (h := hjDrop)
    have hindexEq :
        actualCarryStates[s + j]'(by simpa [actualCarryStates, Nat.add_comm] using hjActual) =
          actualCarryStates[j + s]'(by simpa [actualCarryStates] using hjActual) := by
      exact getElem_congr (c := actualCarryStates) (d := actualCarryStates) rfl
        (Nat.add_comm s j) (w := by simpa [actualCarryStates, Nat.add_comm] using hjActual)
    exact hdropEq'.trans hindexEq
  calc
    ((actual.stateAlignments hgood (requestedBlocks + s) lookaheadBlocks)[j + s]'hjActual).carryIn
      = actualCarryStates[j + s]'(by simpa [actualCarryStates] using hjActual) := by
          simp [actualCarryStates]
    _ = (actualCarryStates.drop s)[j]'hjDrop := hdropEq.symm
    _ = coreCarryStates[j]'hjCoreCarry := hget
    _ = ((core.stateAlignments hcoreGood requestedBlocks lookaheadBlocks)[j]'hjCore).carryIn := by
          simp [coreCarryStates]

theorem actualCoordinate_stateAlignments_remainderIn_shift_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (j : ℕ)
    (hjActual :
      j + s < ((actualCoordinate base n stride hn).stateAlignments hgood
        (requestedBlocks + s) lookaheadBlocks).length)
    (hjCore :
      j < ((strippedCoordinate base n stride hn).stateAlignments
        (sameCoreCompatible_goodMode_of_actual_goodMode
          (base := base) (n := n) (stride := stride) (hn := hn) hgood)
        requestedBlocks lookaheadBlocks).length) :
    (((actualCoordinate base n stride hn).stateAlignments hgood
        (requestedBlocks + s) lookaheadBlocks)[j + s]'hjActual).remainderIn =
      (actualCoordinate base n stride hn).remainderK ^ s *
        (((strippedCoordinate base n stride hn).stateAlignments
            (sameCoreCompatible_goodMode_of_actual_goodMode
              (base := base) (n := n) (stride := stride) (hn := hn) hgood)
            requestedBlocks lookaheadBlocks)[j]'hjCore).remainderIn := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  let hcoreGood :=
    sameCoreCompatible_goodMode_of_actual_goodMode
      (base := base) (n := n) (stride := stride) (hn := hn) hgood
  calc
    ((actual.stateAlignments hgood (requestedBlocks + s) lookaheadBlocks)[j + s]'hjActual).remainderIn
      = actual.longDivisionRemainder (j + s) := by
          exact actual.stateAlignments_remainderIn_eq_longDivisionRemainder
            hgood (requestedBlocks + s) lookaheadBlocks (j + s) hjActual
    _ = actual.remainderK ^ s * core.longDivisionRemainder j := by
          exact actualCoordinate_longDivisionRemainder_add_exact
            (base := base) (n := n) (stride := stride) (s := s) (j := j) (hn := hn)
            hcompat hfactor
    _ = actual.remainderK ^ s *
          ((core.stateAlignments hcoreGood requestedBlocks lookaheadBlocks)[j]'hjCore).remainderIn := by
          rw [core.stateAlignments_remainderIn_eq_longDivisionRemainder
            hcoreGood requestedBlocks lookaheadBlocks j hjCore]

/-- Exact same-core transport of the observed remainder-to-carry functional
criterion itself. This is a finite-window support theorem beneath the open
global carry/visibility boundary. -/
theorem actualCoordinate_stateAlignments_remainderToCarryFunctional_of_core_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hcoreGood : (strippedCoordinate base n stride hn).goodMode)
    (hfunc :
      (strippedCoordinate base n stride hn).remainderToCarryFunctional
        hcoreGood requestedBlocks lookaheadBlocks) :
    (actualCoordinate base n stride hn).remainderToCarryFunctional
      hgood (requestedBlocks + s) lookaheadBlocks := by
  let actual := actualCoordinate base n stride hn
  let core := strippedCoordinate base n stride hn
  let hcoreGood' :=
    sameCoreCompatible_goodMode_of_actual_goodMode
      (base := base) (n := n) (stride := stride) (hn := hn) hgood
  have hfunc' :
      core.remainderToCarryFunctional hcoreGood' requestedBlocks lookaheadBlocks := by
    simpa [core] using hfunc
  have hkpos : 0 < actual.remainderK := lt_trans Nat.zero_lt_one hk
  intro i hi j hj hstate
  by_cases hi_lt : i < s
  · by_cases hj_lt : j < s
    · rw [actual.stateAlignments_remainderIn_eq_longDivisionRemainder
          hgood (requestedBlocks + s) lookaheadBlocks i hi,
        actual.stateAlignments_remainderIn_eq_longDivisionRemainder
          hgood (requestedBlocks + s) lookaheadBlocks j hj,
        actualCoordinate_longDivisionRemainder_prefix_eq_pow
          (base := base) (n := n) (stride := stride) (s := s) (i := i) (hn := hn)
          hk hfactor hi_lt,
        actualCoordinate_longDivisionRemainder_prefix_eq_pow
          (base := base) (n := n) (stride := stride) (s := s) (i := j) (hn := hn)
          hk hfactor hj_lt] at hstate
      have hij :
          i = j := Nat.pow_right_injective (Nat.succ_le_of_lt hk) hstate
      subst hij
      simp
    · exfalso
      have hs_le_j : s ≤ j := Nat.le_of_not_gt hj_lt
      rw [actual.stateAlignments_remainderIn_eq_longDivisionRemainder
          hgood (requestedBlocks + s) lookaheadBlocks i hi,
        actual.stateAlignments_remainderIn_eq_longDivisionRemainder
          hgood (requestedBlocks + s) lookaheadBlocks j hj,
        actualCoordinate_longDivisionRemainder_prefix_eq_pow
          (base := base) (n := n) (stride := stride) (s := s) (i := i) (hn := hn)
          hk hfactor hi_lt] at hstate
      have hjShift :
          actual.longDivisionRemainder j =
            actual.remainderK ^ s * core.longDivisionRemainder (j - s) := by
        rw [show j = (j - s) + s by omega]
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          actualCoordinate_longDivisionRemainder_add_exact
            (base := base) (n := n) (stride := stride) (s := s) (j := j - s) (hn := hn)
            hcompat hfactor
      rw [hjShift] at hstate
      have hpow_lt_shift : actual.remainderK ^ i < actual.remainderK ^ s :=
        Nat.pow_lt_pow_right hk hi_lt
      have hfactor_le : actual.remainderK ^ s ≤ actual.remainderK ^ i := by
        exact Nat.le_of_dvd (pow_pos hkpos i) ⟨core.longDivisionRemainder (j - s), hstate⟩
      exact (not_le_of_gt hpow_lt_shift) hfactor_le
  · by_cases hj_lt : j < s
    · exfalso
      have hs_le_i : s ≤ i := Nat.le_of_not_gt hi_lt
      rw [actual.stateAlignments_remainderIn_eq_longDivisionRemainder
          hgood (requestedBlocks + s) lookaheadBlocks i hi,
        actual.stateAlignments_remainderIn_eq_longDivisionRemainder
          hgood (requestedBlocks + s) lookaheadBlocks j hj,
        actualCoordinate_longDivisionRemainder_prefix_eq_pow
          (base := base) (n := n) (stride := stride) (s := s) (i := j) (hn := hn)
          hk hfactor hj_lt] at hstate
      have hiShift :
          actual.longDivisionRemainder i =
            actual.remainderK ^ s * core.longDivisionRemainder (i - s) := by
        rw [show i = (i - s) + s by omega]
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          actualCoordinate_longDivisionRemainder_add_exact
            (base := base) (n := n) (stride := stride) (s := s) (j := i - s) (hn := hn)
            hcompat hfactor
      rw [hiShift] at hstate
      have hpow_lt_shift : actual.remainderK ^ j < actual.remainderK ^ s :=
        Nat.pow_lt_pow_right hk hj_lt
      have hfactor_le : actual.remainderK ^ s ≤ actual.remainderK ^ j := by
        exact Nat.le_of_dvd (pow_pos hkpos j) ⟨core.longDivisionRemainder (i - s), hstate.symm⟩
      exact (not_le_of_gt hpow_lt_shift) hfactor_le
    · have hiCore : i - s < requestedBlocks := by
        rw [actual.stateAlignments_length hgood (requestedBlocks + s) lookaheadBlocks] at hi
        omega
      have hjCore : j - s < requestedBlocks := by
        rw [actual.stateAlignments_length hgood (requestedBlocks + s) lookaheadBlocks] at hj
        omega
      have hiRemShift :
          ((actual.stateAlignments hgood (requestedBlocks + s) lookaheadBlocks)[i]'hi).remainderIn =
            actual.remainderK ^ s *
              ((core.stateAlignments hcoreGood' requestedBlocks lookaheadBlocks)[i - s]'(by
                rw [core.stateAlignments_length]
                exact hiCore)).remainderIn := by
        have hiActualShift :
            (i - s) + s < (actual.stateAlignments hgood (requestedBlocks + s) lookaheadBlocks).length := by
          simpa [show (i - s) + s = i by omega] using hi
        simpa [show (i - s) + s = i by omega] using
          actualCoordinate_stateAlignments_remainderIn_shift_exact
            (base := base) (n := n) (stride := stride) (s := s)
            (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
            (hn := hn) hgood hcompat hfactor (i - s) hiActualShift (by
              rw [core.stateAlignments_length]
              exact hiCore)
      have hjRemShift :
          ((actual.stateAlignments hgood (requestedBlocks + s) lookaheadBlocks)[j]'hj).remainderIn =
            actual.remainderK ^ s *
              ((core.stateAlignments hcoreGood' requestedBlocks lookaheadBlocks)[j - s]'(by
                rw [core.stateAlignments_length]
                exact hjCore)).remainderIn := by
        have hjActualShift :
            (j - s) + s < (actual.stateAlignments hgood (requestedBlocks + s) lookaheadBlocks).length := by
          simpa [show (j - s) + s = j by omega] using hj
        simpa [show (j - s) + s = j by omega] using
          actualCoordinate_stateAlignments_remainderIn_shift_exact
            (base := base) (n := n) (stride := stride) (s := s)
            (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
            (hn := hn) hgood hcompat hfactor (j - s) hjActualShift (by
              rw [core.stateAlignments_length]
              exact hjCore)
      rw [hiRemShift, hjRemShift] at hstate
      have hcoreState :
          ((core.stateAlignments hcoreGood' requestedBlocks lookaheadBlocks)[i - s]'(by
            rw [core.stateAlignments_length]
            exact hiCore)).remainderIn =
            ((core.stateAlignments hcoreGood' requestedBlocks lookaheadBlocks)[j - s]'(by
              rw [core.stateAlignments_length]
              exact hjCore)).remainderIn :=
        Nat.eq_of_mul_eq_mul_left (pow_pos hkpos s) hstate
      have hcoreCarry :
          ((core.stateAlignments hcoreGood' requestedBlocks lookaheadBlocks)[i - s]'(by
            rw [core.stateAlignments_length]
            exact hiCore)).carryIn =
            ((core.stateAlignments hcoreGood' requestedBlocks lookaheadBlocks)[j - s]'(by
              rw [core.stateAlignments_length]
              exact hjCore)).carryIn :=
        hfunc' (i - s) (by
            rw [core.stateAlignments_length]
            exact hiCore)
          (j - s) (by
            rw [core.stateAlignments_length]
            exact hjCore) hcoreState
      have hiCarryShift :
          ((actual.stateAlignments hgood (requestedBlocks + s) lookaheadBlocks)[i]'hi).carryIn =
            ((core.stateAlignments hcoreGood' requestedBlocks lookaheadBlocks)[i - s]'(by
              rw [core.stateAlignments_length]
              exact hiCore)).carryIn := by
        have hiActualShift :
            (i - s) + s < (actual.stateAlignments hgood (requestedBlocks + s) lookaheadBlocks).length := by
          simpa [show (i - s) + s = i by omega] using hi
        simpa [show (i - s) + s = i by omega] using
          actualCoordinate_stateAlignments_carryIn_shift_exact
            (base := base) (n := n) (stride := stride) (s := s)
            (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
            (hn := hn) hgood hcompat hfactor (i - s) hiActualShift (by
              rw [core.stateAlignments_length]
              exact hiCore)
      have hjCarryShift :
          ((actual.stateAlignments hgood (requestedBlocks + s) lookaheadBlocks)[j]'hj).carryIn =
            ((core.stateAlignments hcoreGood' requestedBlocks lookaheadBlocks)[j - s]'(by
              rw [core.stateAlignments_length]
              exact hjCore)).carryIn := by
        have hjActualShift :
            (j - s) + s < (actual.stateAlignments hgood (requestedBlocks + s) lookaheadBlocks).length := by
          simpa [show (j - s) + s = j by omega] using hj
        simpa [show (j - s) + s = j by omega] using
          actualCoordinate_stateAlignments_carryIn_shift_exact
            (base := base) (n := n) (stride := stride) (s := s)
            (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
            (hn := hn) hgood hcompat hfactor (j - s) hjActualShift (by
              rw [core.stateAlignments_length]
              exact hjCore)
      calc
        ((actual.stateAlignments hgood (requestedBlocks + s) lookaheadBlocks)[i]'hi).carryIn
          = ((core.stateAlignments hcoreGood' requestedBlocks lookaheadBlocks)[i - s]'(by
              rw [core.stateAlignments_length]
              exact hiCore)).carryIn := hiCarryShift
        _ = ((core.stateAlignments hcoreGood' requestedBlocks lookaheadBlocks)[j - s]'(by
              rw [core.stateAlignments_length]
              exact hjCore)).carryIn := hcoreCarry
        _ = ((actual.stateAlignments hgood (requestedBlocks + s) lookaheadBlocks)[j]'hj).carryIn := by
              symm
              exact hjCarryShift

theorem actualCoordinate_stateAlignments_remainderToCarryFunctional_of_core_remainderKPow_lt_modulus_add
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hk : 1 < (actualCoordinate base n stride hn).remainderK)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (_hpow :
      (strippedCoordinate base n stride hn).remainderK ^ (requestedBlocks + lookaheadBlocks) <
        (strippedCoordinate base n stride hn).modulus)
    (hcoreGood : (strippedCoordinate base n stride hn).goodMode)
    (hfunc :
      (strippedCoordinate base n stride hn).remainderToCarryFunctional
        hcoreGood requestedBlocks lookaheadBlocks) :
    (actualCoordinate base n stride hn).remainderToCarryFunctional
      hgood (requestedBlocks + s) lookaheadBlocks := by
  exact actualCoordinate_stateAlignments_remainderToCarryFunctional_of_core_add_exact
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hgood hk hcompat hfactor hcoreGood hfunc

/-- Exact same-core transport form for finite aligned state-output agreement on
the shifted actual denominator. This remains a finite-window theorem only. -/
theorem actualCoordinate_stateAlignments_output_agreement_of_core_lookaheadCertificate_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (actualCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hcert :
      (strippedCoordinate base n stride hn).lookaheadCertificateHolds
        requestedBlocks lookaheadBlocks) :
    ((actualCoordinate base n stride hn).stateAlignments hgood (requestedBlocks + s) lookaheadBlocks).map
        StateAlignment.carryBlockValue =
      ((actualCoordinate base n stride hn).stateAlignments hgood (requestedBlocks + s) lookaheadBlocks).map
        StateAlignment.remainderBlockValue := by
  let actual := actualCoordinate base n stride hn
  rw [actual.stateAlignments_map_carryBlockValue, actual.stateAlignments_map_remainderBlockValue]
  exact actualCoordinate_visibleCarryWord_eq_emittedBlockWord_of_core_lookaheadCertificate_add_exact
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hgood hmod hcompat hfactor hcert

/-- Gap-arithmetic transport form for finite aligned state-output agreement on
the shifted actual denominator. This remains a finite-window theorem only. -/
theorem actualCoordinate_stateAlignments_output_agreement_of_core_tail_lt_gapModulus_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (actualCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (htail :
      (strippedCoordinate base n stride hn).remainderK ^ (requestedBlocks + lookaheadBlocks) <
        (strippedCoordinate base n stride hn).lookaheadGapNumerator
          requestedBlocks lookaheadBlocks *
          (strippedCoordinate base n stride hn).modulus) :
    ((actualCoordinate base n stride hn).stateAlignments hgood (requestedBlocks + s) lookaheadBlocks).map
        StateAlignment.carryBlockValue =
      ((actualCoordinate base n stride hn).stateAlignments hgood (requestedBlocks + s) lookaheadBlocks).map
        StateAlignment.remainderBlockValue := by
  let actual := actualCoordinate base n stride hn
  rw [actual.stateAlignments_map_carryBlockValue, actual.stateAlignments_map_remainderBlockValue]
  exact actualCoordinate_visibleCarryWord_eq_emittedBlockWord_of_core_tail_lt_gapModulus_add_exact
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hgood hmod hcompat hfactor htail

/-- Reverse gap-arithmetic transport form for finite aligned state-output
agreement on the stripped core. This packages the unshifted side of the same
finite-window theorem. -/
theorem strippedCoordinate_stateAlignments_output_agreement_of_actual_tail_lt_gapModulus_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (strippedCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (htail :
      (actualCoordinate base n stride hn).remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) <
        (actualCoordinate base n stride hn).lookaheadGapNumerator
          (requestedBlocks + s) lookaheadBlocks *
          (actualCoordinate base n stride hn).modulus) :
    ((strippedCoordinate base n stride hn).stateAlignments
        (strippedCoordinate_goodMode_of_actual_goodMode hn hgood)
        requestedBlocks lookaheadBlocks).map StateAlignment.carryBlockValue =
      ((strippedCoordinate base n stride hn).stateAlignments
        (strippedCoordinate_goodMode_of_actual_goodMode hn hgood)
        requestedBlocks lookaheadBlocks).map StateAlignment.remainderBlockValue := by
  let core := strippedCoordinate base n stride hn
  let hcoreGood := strippedCoordinate_goodMode_of_actual_goodMode hn hgood
  rw [core.stateAlignments_map_carryBlockValue, core.stateAlignments_map_remainderBlockValue]
  exact strippedCoordinate_visibleCarryWord_eq_emittedBlockWord_of_actual_tail_lt_gapModulus_add_exact
    (base := base) (n := n) (stride := stride) (s := s)
    (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
    (hn := hn) hgood hmod hcompat hfactor htail

/-- Pointwise gap-arithmetic transport form for finite aligned state-output
agreement on the shifted actual denominator. -/
theorem actualCoordinate_stateAlignments_output_agreement_pointwise_of_core_tail_lt_gapModulus_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (actualCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (htail :
      (strippedCoordinate base n stride hn).remainderK ^ (requestedBlocks + lookaheadBlocks) <
        (strippedCoordinate base n stride hn).lookaheadGapNumerator
          requestedBlocks lookaheadBlocks *
          (strippedCoordinate base n stride hn).modulus)
    (i : ℕ)
    (hi :
      i < ((actualCoordinate base n stride hn).stateAlignments hgood
        (requestedBlocks + s) lookaheadBlocks).length) :
    (((actualCoordinate base n stride hn).stateAlignments hgood
        (requestedBlocks + s) lookaheadBlocks)[i]'hi).carryBlockValue =
      (((actualCoordinate base n stride hn).stateAlignments hgood
        (requestedBlocks + s) lookaheadBlocks)[i]'hi).remainderBlockValue := by
  let actual := actualCoordinate base n stride hn
  have htailActual :
      actual.remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) <
        actual.lookaheadGapNumerator (requestedBlocks + s) lookaheadBlocks * actual.modulus :=
    (sameCoreCompatible_tail_lt_gapModulus_iff_add_exact
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hcompat hfactor).2 htail
  have hcertActual :
      actual.lookaheadCertificateHolds (requestedBlocks + s) lookaheadBlocks := by
    rw [actual.lookaheadCertificateHolds_iff_tail_lt_gapModulus
      hgood (requestedBlocks + s) lookaheadBlocks]
    exact htailActual
  exact actual.stateAlignments_output_agreement_pointwise_of_lookaheadCertificate
    hgood hmod (requestedBlocks + s) lookaheadBlocks hcertActual i hi

/-- Reverse pointwise gap-arithmetic transport form for finite aligned
state-output agreement on the stripped core. -/
theorem strippedCoordinate_stateAlignments_output_agreement_pointwise_of_actual_tail_lt_gapModulus_add_exact
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (strippedCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (htail :
      (actualCoordinate base n stride hn).remainderK ^ ((requestedBlocks + s) + lookaheadBlocks) <
        (actualCoordinate base n stride hn).lookaheadGapNumerator
          (requestedBlocks + s) lookaheadBlocks *
          (actualCoordinate base n stride hn).modulus)
    (i : ℕ)
    (hi :
      i < ((strippedCoordinate base n stride hn).stateAlignments
        (strippedCoordinate_goodMode_of_actual_goodMode hn hgood)
        requestedBlocks lookaheadBlocks).length) :
    (((strippedCoordinate base n stride hn).stateAlignments
        (strippedCoordinate_goodMode_of_actual_goodMode hn hgood)
        requestedBlocks lookaheadBlocks)[i]'hi).carryBlockValue =
      (((strippedCoordinate base n stride hn).stateAlignments
        (strippedCoordinate_goodMode_of_actual_goodMode hn hgood)
        requestedBlocks lookaheadBlocks)[i]'hi).remainderBlockValue := by
  let core := strippedCoordinate base n stride hn
  let hcoreGood := strippedCoordinate_goodMode_of_actual_goodMode hn hgood
  have htailCore :
      core.remainderK ^ (requestedBlocks + lookaheadBlocks) <
        core.lookaheadGapNumerator requestedBlocks lookaheadBlocks * core.modulus :=
    (sameCoreCompatible_tail_lt_gapModulus_iff_add_exact
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hcompat hfactor).1 htail
  have hcertCore :
      core.lookaheadCertificateHolds requestedBlocks lookaheadBlocks := by
    rw [core.lookaheadCertificateHolds_iff_tail_lt_gapModulus
      hcoreGood requestedBlocks lookaheadBlocks]
    exact htailCore
  exact core.stateAlignments_output_agreement_pointwise_of_lookaheadCertificate
    hcoreGood hmod requestedBlocks lookaheadBlocks hcertCore i hi

/-- In the exact `k^s` same-core regime, the coarse stripped-core condition
`k^(n+L) < modulus` is already enough to upgrade an observed
remainder-to-carry functional relation on the shifted actual window into the
full finite transition-compatibility package. This remains a finite-window
theorem only. -/
theorem actualCoordinate_stateAlignments_remainderToCarry_transition_compatible_of_core_remainderKPow_lt_modulus_add
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (actualCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hpow :
      (strippedCoordinate base n stride hn).remainderK ^ (requestedBlocks + lookaheadBlocks) <
        (strippedCoordinate base n stride hn).modulus)
    (hfunc :
      (actualCoordinate base n stride hn).remainderToCarryFunctional
        hgood (requestedBlocks + s) lookaheadBlocks)
    (i : ℕ)
    (hi :
      i < ((actualCoordinate base n stride hn).stateAlignments hgood
        (requestedBlocks + s) lookaheadBlocks).length)
    (j : ℕ)
    (hj :
      j < ((actualCoordinate base n stride hn).stateAlignments hgood
        (requestedBlocks + s) lookaheadBlocks).length)
    (hstate :
      (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[i]'hi).remainderIn =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).remainderIn)
    (hcoeff :
      (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[i]'hi).coefficient =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).coefficient) :
    (((actualCoordinate base n stride hn).stateAlignments hgood
        (requestedBlocks + s) lookaheadBlocks)[i]'hi).carryIn =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).carryIn ∧
      (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[i]'hi).remainderBlockValue =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).remainderBlockValue ∧
      (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[i]'hi).carryBlockValue =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).carryBlockValue ∧
      (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[i]'hi).remainderOut =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).remainderOut ∧
      (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[i]'hi).carryOut =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).carryOut := by
  let actual := actualCoordinate base n stride hn
  have hcertActual :
      actual.lookaheadCertificateHolds (requestedBlocks + s) lookaheadBlocks :=
    sameCoreCompatible_lookaheadCertificateHolds_of_core_remainderKPow_lt_modulus_add
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hgood hcompat hfactor hpow
  exact actual.stateAlignments_remainderToCarry_transition_compatible_of_functional
    hgood hmod (requestedBlocks + s) lookaheadBlocks hfunc hcertActual i hi j hj hstate hcoeff

/-- Reverse-direction finite transition compatibility under the same exact
same-core coarse condition. -/
theorem actualCoordinate_stateAlignments_carryToRemainder_transition_compatible_of_core_remainderKPow_lt_modulus_add
    {base n stride s requestedBlocks lookaheadBlocks : ℕ} {hn : 0 < n}
    (hgood : (actualCoordinate base n stride hn).goodMode)
    (hmod : 1 < (actualCoordinate base n stride hn).modulus)
    (hcompat : sameCoreCompatible base n stride hn)
    (hfactor : basePrimeSupportFactor base n =
      (actualCoordinate base n stride hn).remainderK ^ s)
    (hpow :
      (strippedCoordinate base n stride hn).remainderK ^ (requestedBlocks + lookaheadBlocks) <
        (strippedCoordinate base n stride hn).modulus)
    (hfunc :
      (actualCoordinate base n stride hn).carryToRemainderFunctional
        hgood (requestedBlocks + s) lookaheadBlocks)
    (i : ℕ)
    (hi :
      i < ((actualCoordinate base n stride hn).stateAlignments hgood
        (requestedBlocks + s) lookaheadBlocks).length)
    (j : ℕ)
    (hj :
      j < ((actualCoordinate base n stride hn).stateAlignments hgood
        (requestedBlocks + s) lookaheadBlocks).length)
    (hcarry :
      (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[i]'hi).carryIn =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).carryIn)
    (hcoeff :
      (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[i]'hi).coefficient =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).coefficient) :
    (((actualCoordinate base n stride hn).stateAlignments hgood
        (requestedBlocks + s) lookaheadBlocks)[i]'hi).remainderIn =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).remainderIn ∧
      (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[i]'hi).remainderBlockValue =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).remainderBlockValue ∧
      (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[i]'hi).carryBlockValue =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).carryBlockValue ∧
      (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[i]'hi).remainderOut =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).remainderOut ∧
      (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[i]'hi).carryOut =
        (((actualCoordinate base n stride hn).stateAlignments hgood
          (requestedBlocks + s) lookaheadBlocks)[j]'hj).carryOut := by
  let actual := actualCoordinate base n stride hn
  have hcertActual :
      actual.lookaheadCertificateHolds (requestedBlocks + s) lookaheadBlocks :=
    sameCoreCompatible_lookaheadCertificateHolds_of_core_remainderKPow_lt_modulus_add
      (base := base) (n := n) (stride := stride) (s := s)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := hn) hgood hcompat hfactor hpow
  exact actual.stateAlignments_carryToRemainder_transition_compatible_of_functional
    hgood hmod (requestedBlocks + s) lookaheadBlocks hfunc hcertActual i hi j hj hcarry hcoeff

section Examples

def twentyOneStride6 : BlockCoordinate where
  base := 10
  modulus := 21
  stride := 6
  modulus_pos := by native_decide

def composite996Stride3 : BlockCoordinate :=
  actualCoordinate 10 996 3 (by native_decide)

theorem twentyOneStride6_goodMode : twentyOneStride6.goodMode := by
  unfold twentyOneStride6 BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

theorem prime97Stride2_goodMode : prime97Stride2.goodMode := by
  unfold prime97Stride2 BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

theorem composite996Stride3_goodMode : composite996Stride3.goodMode := by
  unfold composite996Stride3 actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

example :
    prime37Stride3.lookaheadGapNumerator 6 0 = 1 := by
  native_decide

example :
    prime97Stride2.lookaheadGapNumerator 6 1 = 71 := by
  native_decide

example :
    prime37Stride3.lookaheadCertificateHolds 6 0 := by
  unfold BlockCoordinate.lookaheadCertificateHolds BlockCoordinate.lookaheadGapNumerator
  native_decide

example :
    prime97Stride2.lookaheadCertificateHolds 6 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds BlockCoordinate.lookaheadGapNumerator
  native_decide

example :
    prime97Stride2.lookaheadCertificateHolds 6 3 := by
  have hgood : prime97Stride2.goodMode := by
    unfold prime97Stride2 BlockCoordinate.goodMode BlockCoordinate.blockBase
    native_decide
  exact prime97Stride2.lookaheadCertificateHolds_of_lookaheadCertificate_add
    hgood 6 1 2 (by
      unfold BlockCoordinate.lookaheadCertificateHolds BlockCoordinate.lookaheadGapNumerator
      native_decide)

example :
    prime37Stride3.visibleCarryWord (by
      show 37 < 10 ^ 3
      native_decide) 6 0 = prime37Stride3.emittedBlockWord 6 := by
  native_decide

example :
    prime97Stride2.visibleCarryWord (by
      show 97 < 10 ^ 2
      native_decide) 6 1 = prime97Stride2.emittedBlockWord 6 := by
  native_decide

example :
    prime97Stride2.visibleCarryWord (by
      show 97 < 10 ^ 2
      native_decide) 6 3 = prime97Stride2.emittedBlockWord 6 := by
  have hgood : prime97Stride2.goodMode := by
    unfold prime97Stride2 BlockCoordinate.goodMode BlockCoordinate.blockBase
    native_decide
  exact prime97Stride2.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate_add
    hgood (by native_decide) 6 1 2 (by
      unfold BlockCoordinate.lookaheadCertificateHolds BlockCoordinate.lookaheadGapNumerator
      native_decide)

example :
    twentyOneStride6.visibleCarryWord twentyOneStride6_goodMode 8 0 =
      twentyOneStride6.emittedBlockWord 8 := by
  native_decide

example :
    twentyOneStride6.remainderToCarryFunctional twentyOneStride6_goodMode 8 0 := by
  rw [twentyOneStride6.remainderToCarryFunctional_iff_functionalOnFst_pairs]
  native_decide

example :
    twentyOneStride6.carryToRemainderFunctional twentyOneStride6_goodMode 8 0 := by
  rw [twentyOneStride6.carryToRemainderFunctional_iff_functionalOnFst_pairs]
  native_decide

example :
    prime97Stride2.visibleCarryWord prime97Stride2_goodMode 8 2 =
      prime97Stride2.emittedBlockWord 8 := by
  native_decide

example :
    prime97Stride2.remainderToCarryFunctional prime97Stride2_goodMode 8 2 := by
  rw [prime97Stride2.remainderToCarryFunctional_iff_functionalOnFst_pairs]
  native_decide

example :
    ¬ prime97Stride2.carryToRemainderFunctional prime97Stride2_goodMode 8 2 := by
  rw [prime97Stride2.carryToRemainderFunctional_iff_functionalOnFst_pairs]
  native_decide

example :
    composite996Stride3.visibleCarryWord composite996Stride3_goodMode 8 1 =
      composite996Stride3.emittedBlockWord 8 := by
  native_decide

example :
    composite996Stride3.remainderToCarryFunctional composite996Stride3_goodMode 8 1 := by
  rw [composite996Stride3.remainderToCarryFunctional_iff_functionalOnFst_pairs]
  native_decide

example :
    (actualCoordinate 10 996 3 (by native_decide)).remainderToCarryFunctional
      composite996Stride3_goodMode 4 0 := by
  have hcoreGood :
      (strippedCoordinate 10 996 3 (by native_decide)).goodMode :=
    sameCoreCompatible_goodMode_of_actual_goodMode
      (base := 10) (n := 996) (stride := 3) (hn := by native_decide)
      composite996Stride3_goodMode
  have hcoreFunc :
      (strippedCoordinate 10 996 3 (by native_decide)).remainderToCarryFunctional
        (sameCoreCompatible_goodMode_of_actual_goodMode
          (base := 10) (n := 996) (stride := 3) (hn := by native_decide)
          composite996Stride3_goodMode) 3 0 := by
    refine
      (BlockCoordinate.remainderToCarryFunctional_iff_functionalOnFst_pairs
        (strippedCoordinate 10 996 3 (by native_decide))
        (sameCoreCompatible_goodMode_of_actual_goodMode
          (base := 10) (n := 996) (stride := 3) (hn := by native_decide)
          composite996Stride3_goodMode) 3 0).2 ?_
    native_decide
  exact actualCoordinate_stateAlignments_remainderToCarryFunctional_of_core_add_exact
    (base := 10) (n := 996) (stride := 3) (s := 1)
    (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
    composite996Stride3_goodMode
    (by native_decide)
    (by
      unfold sameCoreCompatible actualCoordinate
      native_decide)
    (by native_decide)
    hcoreGood
    hcoreFunc

example :
    let actual := actualCoordinate 10 996 3 (by native_decide)
    ((actual.stateAlignments composite996Stride3_goodMode 4 0)[2]'(by native_decide)).carryIn =
        ((actual.stateAlignments composite996Stride3_goodMode 4 0)[2]'(by native_decide)).carryIn ∧
      ((actual.stateAlignments composite996Stride3_goodMode 4 0)[2]'(by native_decide)).remainderBlockValue =
        ((actual.stateAlignments composite996Stride3_goodMode 4 0)[2]'(by native_decide)).remainderBlockValue ∧
      ((actual.stateAlignments composite996Stride3_goodMode 4 0)[2]'(by native_decide)).carryBlockValue =
        ((actual.stateAlignments composite996Stride3_goodMode 4 0)[2]'(by native_decide)).carryBlockValue ∧
      ((actual.stateAlignments composite996Stride3_goodMode 4 0)[2]'(by native_decide)).remainderOut =
        ((actual.stateAlignments composite996Stride3_goodMode 4 0)[2]'(by native_decide)).remainderOut ∧
      ((actual.stateAlignments composite996Stride3_goodMode 4 0)[2]'(by native_decide)).carryOut =
        ((actual.stateAlignments composite996Stride3_goodMode 4 0)[2]'(by native_decide)).carryOut := by
  dsimp
  exact actualCoordinate_stateAlignments_remainderToCarry_transition_compatible_of_core_remainderKPow_lt_modulus_add
    (base := 10) (n := 996) (stride := 3) (s := 1)
    (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
    composite996Stride3_goodMode
    (by native_decide)
    (by
      unfold sameCoreCompatible actualCoordinate
      native_decide)
    (by native_decide)
    (by native_decide)
    (by
      have hcoreGood :
          (strippedCoordinate 10 996 3 (by native_decide)).goodMode :=
        sameCoreCompatible_goodMode_of_actual_goodMode
          (base := 10) (n := 996) (stride := 3) (hn := by native_decide)
          composite996Stride3_goodMode
      have hcoreFunc :
          (strippedCoordinate 10 996 3 (by native_decide)).remainderToCarryFunctional
            (sameCoreCompatible_goodMode_of_actual_goodMode
              (base := 10) (n := 996) (stride := 3) (hn := by native_decide)
              composite996Stride3_goodMode) 3 0 := by
        refine
          (BlockCoordinate.remainderToCarryFunctional_iff_functionalOnFst_pairs
            (strippedCoordinate 10 996 3 (by native_decide))
            (sameCoreCompatible_goodMode_of_actual_goodMode
              (base := 10) (n := 996) (stride := 3) (hn := by native_decide)
              composite996Stride3_goodMode) 3 0).2 ?_
        native_decide
      exact actualCoordinate_stateAlignments_remainderToCarryFunctional_of_core_remainderKPow_lt_modulus_add
        (base := 10) (n := 996) (stride := 3) (s := 1)
        (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
        composite996Stride3_goodMode
        (by native_decide)
        (by
          unfold sameCoreCompatible actualCoordinate
          native_decide)
        (by native_decide)
        (by native_decide)
        hcoreGood
        hcoreFunc)
    2 (by native_decide) 2 (by native_decide) rfl rfl

example :
    ¬ composite996Stride3.carryToRemainderFunctional composite996Stride3_goodMode 8 1 := by
  rw [composite996Stride3.carryToRemainderFunctional_iff_functionalOnFst_pairs]
  native_decide

end Examples

end QRTour
