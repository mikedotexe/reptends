/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.OrbitWeave
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Zip
import Mathlib.Tactic

/-!
# Finite Carry-Propagated Block Normalization

This module formalizes the finite carry-normalization recursion behind the
Python `CarryTransducer`. The input word is a finite list of raw block
coefficients in most-significant-to-least-significant order. Internally, the
recursion runs on the reversed word because carries move from right to left.
-/

namespace QRTour

/-- A finite-window carry transducer for one block base `B`. -/
structure CarryTransducer where
  blockBase : ℕ
  blockBase_gt_one : 1 < blockBase

theorem CarryTransducer.blockBase_pos (T : CarryTransducer) : 0 < T.blockBase :=
  lt_trans Nat.one_pos T.blockBase_gt_one

/-- One normalization step for a coefficient and incoming carry. -/
def CarryTransducer.step
    (T : CarryTransducer) (coefficient carryIn : ℕ) (isLeftmost : Bool) : ℕ × ℕ :=
  let total := coefficient + carryIn
  if isLeftmost then
    (total, 0)
  else
    (total % T.blockBase, total / T.blockBase)

@[simp] theorem CarryTransducer.step_leftmost
    (T : CarryTransducer) (coefficient carryIn : ℕ) :
    T.step coefficient carryIn true = (coefficient + carryIn, 0) := by
  simp [CarryTransducer.step]

@[simp] theorem CarryTransducer.step_nonleft
    (T : CarryTransducer) (coefficient carryIn : ℕ) :
    T.step coefficient carryIn false =
      ((coefficient + carryIn) % T.blockBase, (coefficient + carryIn) / T.blockBase) := by
  simp [CarryTransducer.step]

/-- On a non-leftmost block, Euclidean division splits total mass into block plus carry. -/
theorem CarryTransducer.step_nonleft_value
    (T : CarryTransducer) (coefficient carryIn : ℕ) :
    coefficient + carryIn =
      (T.step coefficient carryIn false).1 + T.blockBase * (T.step coefficient carryIn false).2 := by
  rw [T.step_nonleft]
  simpa [Nat.mul_comm] using (Nat.mod_add_div (coefficient + carryIn) T.blockBase).symm

/-- Non-leftmost normalized blocks stay below the block base. -/
theorem CarryTransducer.step_nonleft_block_lt
    (T : CarryTransducer) (coefficient carryIn : ℕ) :
    (T.step coefficient carryIn false).1 < T.blockBase := by
  rw [T.step_nonleft]
  exact Nat.mod_lt _ T.blockBase_pos

/-- Normalize a least-significant-first coefficient word with an incoming carry. -/
def CarryTransducer.normalizeReversedAux
    (T : CarryTransducer) : List ℕ → ℕ → List ℕ
  | [], _ => []
  | [coefficient], carryIn => [coefficient + carryIn]
  | coefficient :: next :: tail, carryIn =>
      let total := coefficient + carryIn
      (total % T.blockBase) :: T.normalizeReversedAux (next :: tail) (total / T.blockBase)

/-- Normalize a least-significant-first coefficient word. -/
def CarryTransducer.normalizeReversed
    (T : CarryTransducer) (coefficients : List ℕ) : List ℕ :=
  T.normalizeReversedAux coefficients 0

/-- Normalize a coefficient word listed from most to least significant block. -/
def CarryTransducer.normalizeBlocks
    (T : CarryTransducer) (coefficients : List ℕ) : List ℕ :=
  (T.normalizeReversed coefficients.reverse).reverse

/-- One recorded transition in a finite carry-normalization run. -/
structure CarryTraceStep where
  coefficient : ℕ
  carryIn : ℕ
  blockValue : ℕ
  carryOut : ℕ
  isLeftmost : Bool
deriving Repr, DecidableEq

/-- Package one transducer step as explicit trace data. -/
def CarryTransducer.mkTraceStep
    (T : CarryTransducer) (coefficient carryIn : ℕ) (isLeftmost : Bool) : CarryTraceStep :=
  let result := T.step coefficient carryIn isLeftmost
  {
    coefficient := coefficient
    carryIn := carryIn
    blockValue := result.1
    carryOut := result.2
    isLeftmost := isLeftmost
  }

@[simp] theorem CarryTransducer.mkTraceStep_coefficient
    (T : CarryTransducer) (coefficient carryIn : ℕ) (isLeftmost : Bool) :
    (T.mkTraceStep coefficient carryIn isLeftmost).coefficient = coefficient := rfl

@[simp] theorem CarryTransducer.mkTraceStep_carryIn
    (T : CarryTransducer) (coefficient carryIn : ℕ) (isLeftmost : Bool) :
    (T.mkTraceStep coefficient carryIn isLeftmost).carryIn = carryIn := rfl

@[simp] theorem CarryTransducer.mkTraceStep_isLeftmost
    (T : CarryTransducer) (coefficient carryIn : ℕ) (isLeftmost : Bool) :
    (T.mkTraceStep coefficient carryIn isLeftmost).isLeftmost = isLeftmost := rfl

@[simp] theorem CarryTransducer.mkTraceStep_blockValue
    (T : CarryTransducer) (coefficient carryIn : ℕ) (isLeftmost : Bool) :
    (T.mkTraceStep coefficient carryIn isLeftmost).blockValue =
      (T.step coefficient carryIn isLeftmost).1 := rfl

@[simp] theorem CarryTransducer.mkTraceStep_carryOut
    (T : CarryTransducer) (coefficient carryIn : ℕ) (isLeftmost : Bool) :
    (T.mkTraceStep coefficient carryIn isLeftmost).carryOut =
      (T.step coefficient carryIn isLeftmost).2 := rfl

/-- A least-significant-first traced carry-normalization run with an incoming carry. -/
def CarryTransducer.traceReversedAux
    (T : CarryTransducer) : List ℕ → ℕ → List CarryTraceStep
  | [], _ => []
  | [coefficient], carryIn => [T.mkTraceStep coefficient carryIn true]
  | coefficient :: next :: tail, carryIn =>
      let step := T.mkTraceStep coefficient carryIn false
      step :: T.traceReversedAux (next :: tail) step.carryOut

/-- A least-significant-first traced carry-normalization run. -/
def CarryTransducer.traceReversed
    (T : CarryTransducer) (coefficients : List ℕ) : List CarryTraceStep :=
  T.traceReversedAux coefficients 0

/-- A most-significant-first traced carry-normalization run. -/
def CarryTransducer.traceBlocks
    (T : CarryTransducer) (coefficients : List ℕ) : List CarryTraceStep :=
  (T.traceReversed coefficients.reverse).reverse

theorem CarryTransducer.traceReversedAux_length
    (T : CarryTransducer) (coefficients : List ℕ) (carryIn : ℕ) :
    (T.traceReversedAux coefficients carryIn).length = coefficients.length := by
  induction coefficients generalizing carryIn with
  | nil =>
      simp [CarryTransducer.traceReversedAux]
  | cons coefficient tail ih =>
      cases tail with
      | nil =>
          simp [CarryTransducer.traceReversedAux]
      | cons next rest =>
          simp [CarryTransducer.traceReversedAux, ih]

theorem CarryTransducer.traceReversed_length
    (T : CarryTransducer) (coefficients : List ℕ) :
    (T.traceReversed coefficients).length = coefficients.length := by
  simpa [CarryTransducer.traceReversed] using T.traceReversedAux_length coefficients 0

theorem CarryTransducer.traceBlocks_length
    (T : CarryTransducer) (coefficients : List ℕ) :
    (T.traceBlocks coefficients).length = coefficients.length := by
  simp [CarryTransducer.traceBlocks, T.traceReversed_length]

theorem CarryTransducer.traceReversedAux_map_blockValue
    (T : CarryTransducer) (coefficients : List ℕ) (carryIn : ℕ) :
    (T.traceReversedAux coefficients carryIn).map CarryTraceStep.blockValue =
      T.normalizeReversedAux coefficients carryIn := by
  induction coefficients generalizing carryIn with
  | nil =>
      simp [CarryTransducer.traceReversedAux, CarryTransducer.normalizeReversedAux]
  | cons coefficient tail ih =>
      cases tail with
      | nil =>
          simp [CarryTransducer.traceReversedAux, CarryTransducer.normalizeReversedAux,
            CarryTransducer.mkTraceStep, CarryTransducer.step]
      | cons next rest =>
          simp [CarryTransducer.traceReversedAux, CarryTransducer.normalizeReversedAux,
            CarryTransducer.mkTraceStep, ih]

theorem CarryTransducer.traceReversed_map_blockValue
    (T : CarryTransducer) (coefficients : List ℕ) :
    (T.traceReversed coefficients).map CarryTraceStep.blockValue = T.normalizeReversed coefficients := by
  simpa [CarryTransducer.traceReversed] using T.traceReversedAux_map_blockValue coefficients 0

theorem CarryTransducer.traceBlocks_map_blockValue
    (T : CarryTransducer) (coefficients : List ℕ) :
    (T.traceBlocks coefficients).map CarryTraceStep.blockValue = T.normalizeBlocks coefficients := by
  simp [CarryTransducer.traceBlocks, CarryTransducer.normalizeBlocks,
    T.traceReversed_map_blockValue]

theorem CarryTransducer.traceReversedAux_map_coefficient
    (T : CarryTransducer) (coefficients : List ℕ) (carryIn : ℕ) :
    (T.traceReversedAux coefficients carryIn).map CarryTraceStep.coefficient = coefficients := by
  induction coefficients generalizing carryIn with
  | nil =>
      simp [CarryTransducer.traceReversedAux]
  | cons coefficient tail ih =>
      cases tail with
      | nil =>
          simp [CarryTransducer.traceReversedAux, CarryTransducer.mkTraceStep]
      | cons next rest =>
          simp [CarryTransducer.traceReversedAux, CarryTransducer.mkTraceStep, ih]

theorem CarryTransducer.traceReversed_map_coefficient
    (T : CarryTransducer) (coefficients : List ℕ) :
    (T.traceReversed coefficients).map CarryTraceStep.coefficient = coefficients := by
  simpa [CarryTransducer.traceReversed] using T.traceReversedAux_map_coefficient coefficients 0

theorem CarryTransducer.traceBlocks_map_coefficient
    (T : CarryTransducer) (coefficients : List ℕ) :
    (T.traceBlocks coefficients).map CarryTraceStep.coefficient = coefficients := by
  simp [CarryTransducer.traceBlocks, T.traceReversed_map_coefficient]

theorem CarryTransducer.traceReversedAux_map_isLeftmost_of_ne_nil
    (T : CarryTransducer) (coefficients : List ℕ) (carryIn : ℕ)
    (hcoeff : coefficients ≠ []) :
    (T.traceReversedAux coefficients carryIn).map CarryTraceStep.isLeftmost =
      List.replicate (coefficients.length - 1) false ++ [true] := by
  induction coefficients generalizing carryIn with
  | nil =>
      contradiction
  | cons coefficient tail ih =>
      cases tail with
      | nil =>
          simp [CarryTransducer.traceReversedAux, CarryTransducer.mkTraceStep]
      | cons next rest =>
          have htail : next :: rest ≠ [] := by simp
          specialize ih ((coefficient + carryIn) / T.blockBase) htail
          simp [CarryTransducer.traceReversedAux, CarryTransducer.mkTraceStep, ih,
            List.replicate]

theorem CarryTransducer.traceReversed_map_isLeftmost_of_ne_nil
    (T : CarryTransducer) (coefficients : List ℕ) (hcoeff : coefficients ≠ []) :
    (T.traceReversed coefficients).map CarryTraceStep.isLeftmost =
      List.replicate (coefficients.length - 1) false ++ [true] := by
  simpa [CarryTransducer.traceReversed] using
    T.traceReversedAux_map_isLeftmost_of_ne_nil coefficients 0 hcoeff

theorem CarryTransducer.traceBlocks_map_isLeftmost_of_ne_nil
    (T : CarryTransducer) (coefficients : List ℕ) (hcoeff : coefficients ≠ []) :
    (T.traceBlocks coefficients).map CarryTraceStep.isLeftmost =
      true :: List.replicate (coefficients.length - 1) false := by
  have hrev : coefficients.reverse ≠ [] := by
    intro hnil
    apply hcoeff
    simpa using congrArg List.reverse hnil
  have hmap :=
    T.traceReversed_map_isLeftmost_of_ne_nil coefficients.reverse hrev
  simpa [CarryTransducer.traceBlocks] using congrArg List.reverse hmap

theorem CarryTransducer.mem_traceReversedAux_value
    (T : CarryTransducer) {coefficients : List ℕ} {carryIn : ℕ} {step : CarryTraceStep}
    (hstep : step ∈ T.traceReversedAux coefficients carryIn) :
    step.coefficient + step.carryIn = step.blockValue + T.blockBase * step.carryOut := by
  induction coefficients generalizing carryIn with
  | nil =>
      simp [CarryTransducer.traceReversedAux] at hstep
  | cons coefficient tail ih =>
      cases tail with
      | nil =>
          simp [CarryTransducer.traceReversedAux, CarryTransducer.mkTraceStep,
            CarryTransducer.step] at hstep
          rcases hstep with rfl
          simp
      | cons next rest =>
          simp [CarryTransducer.traceReversedAux] at hstep
          rcases hstep with rfl | htail
          · exact T.step_nonleft_value coefficient carryIn
          · exact ih htail

theorem CarryTransducer.mem_traceReversedAux_leftmost_carryOut_zero
    (T : CarryTransducer) {coefficients : List ℕ} {carryIn : ℕ} {step : CarryTraceStep}
    (hstep : step ∈ T.traceReversedAux coefficients carryIn)
    (hleft : step.isLeftmost = true) :
    step.carryOut = 0 := by
  induction coefficients generalizing carryIn step with
  | nil =>
      simp [CarryTransducer.traceReversedAux] at hstep
  | cons coefficient tail ih =>
      cases tail with
      | nil =>
          simp [CarryTransducer.traceReversedAux, CarryTransducer.mkTraceStep,
            CarryTransducer.step] at hstep
          rcases hstep with rfl
          simp
      | cons next rest =>
          simp [CarryTransducer.traceReversedAux, CarryTransducer.mkTraceStep] at hstep
          rcases hstep with rfl | htail
          · simp at hleft
          · exact ih htail hleft

theorem CarryTransducer.mem_traceReversedAux_nonleft_block_lt
    (T : CarryTransducer) {coefficients : List ℕ} {carryIn : ℕ} {step : CarryTraceStep}
    (hstep : step ∈ T.traceReversedAux coefficients carryIn)
    (hleft : step.isLeftmost = false) :
    step.blockValue < T.blockBase := by
  induction coefficients generalizing carryIn step with
  | nil =>
      simp [CarryTransducer.traceReversedAux] at hstep
  | cons coefficient tail ih =>
      cases tail with
      | nil =>
          simp [CarryTransducer.traceReversedAux, CarryTransducer.mkTraceStep,
            CarryTransducer.step] at hstep
          rcases hstep with rfl
          simp at hleft
      | cons next rest =>
          simp [CarryTransducer.traceReversedAux, CarryTransducer.mkTraceStep] at hstep
          rcases hstep with rfl | htail
          · exact T.step_nonleft_block_lt coefficient carryIn
          · exact ih htail hleft

theorem CarryTransducer.mem_traceBlocks_nonleft_block_lt
    (T : CarryTransducer) {coefficients : List ℕ} {step : CarryTraceStep}
    (hstep : step ∈ T.traceBlocks coefficients)
    (hleft : step.isLeftmost = false) :
    step.blockValue < T.blockBase := by
  have hrev : step ∈ T.traceReversed coefficients.reverse := by
    have : step ∈ (T.traceReversed coefficients.reverse).reverse := by
      simpa [CarryTransducer.traceBlocks] using hstep
    exact List.mem_reverse.mp this
  simpa [CarryTransducer.traceReversed] using
    T.mem_traceReversedAux_nonleft_block_lt hrev hleft

theorem CarryTransducer.mem_traceBlocks_value
    (T : CarryTransducer) {coefficients : List ℕ} {step : CarryTraceStep}
    (hstep : step ∈ T.traceBlocks coefficients) :
    step.coefficient + step.carryIn = step.blockValue + T.blockBase * step.carryOut := by
  have hrev : step ∈ T.traceReversed coefficients.reverse := by
    have : step ∈ (T.traceReversed coefficients.reverse).reverse := by
      simpa [CarryTransducer.traceBlocks] using hstep
    exact List.mem_reverse.mp this
  simpa [CarryTransducer.traceReversed] using
    T.mem_traceReversedAux_value hrev

/-- Evaluate a least-significant-first block word as a base-`B` numeral. -/
def CarryTransducer.evalReversed (T : CarryTransducer) : List ℕ → ℕ
  | [] => 0
  | coefficient :: tail => coefficient + T.blockBase * T.evalReversed tail

/-- Evaluate a most-significant-first block word as a base-`B` numeral. -/
def CarryTransducer.evalBlocks
    (T : CarryTransducer) (blocks : List ℕ) : ℕ :=
  T.evalReversed blocks.reverse

theorem CarryTransducer.evalReversed_eq_ofDigits
    (T : CarryTransducer) (blocks : List ℕ) :
    T.evalReversed blocks = Nat.ofDigits T.blockBase blocks := by
  induction blocks with
  | nil =>
      rfl
  | cons block tail ih =>
      simp [CarryTransducer.evalReversed, Nat.ofDigits, ih]

theorem CarryTransducer.evalBlocks_eq_ofDigits_reverse
    (T : CarryTransducer) (blocks : List ℕ) :
    T.evalBlocks blocks = Nat.ofDigits T.blockBase blocks.reverse := by
  simpa [CarryTransducer.evalBlocks] using T.evalReversed_eq_ofDigits blocks.reverse

theorem CarryTransducer.evalBlocks_cons
    (T : CarryTransducer) (block : ℕ) (blocks : List ℕ) :
    T.evalBlocks (block :: blocks) = T.evalBlocks blocks + T.blockBase ^ blocks.length * block := by
  rw [T.evalBlocks_eq_ofDigits_reverse, Nat.ofDigits_reverse_cons, ← T.evalBlocks_eq_ofDigits_reverse]

theorem CarryTransducer.evalBlocks_append_singleton
    (T : CarryTransducer) (blocks : List ℕ) (block : ℕ) :
    T.evalBlocks (blocks ++ [block]) = T.blockBase * T.evalBlocks blocks + block := by
  unfold CarryTransducer.evalBlocks
  simp [CarryTransducer.evalReversed, Nat.add_comm]

/-- A finite block word normalizes exactly when it equals the transducer output. -/
def CarryTransducer.Normalizes
    (T : CarryTransducer) (coefficients blocks : List ℕ) : Prop :=
  blocks = T.normalizeBlocks coefficients

theorem CarryTransducer.normalizeBlocks_normalizes
    (T : CarryTransducer) (coefficients : List ℕ) :
    T.Normalizes coefficients (T.normalizeBlocks coefficients) := by
  rfl

/-- The finite normalization map is deterministic. -/
theorem CarryTransducer.normalizes_deterministic
    (T : CarryTransducer) (coefficients blocks₁ blocks₂ : List ℕ)
    (h₁ : T.Normalizes coefficients blocks₁)
    (h₂ : T.Normalizes coefficients blocks₂) :
    blocks₁ = blocks₂ := by
  simpa [CarryTransducer.Normalizes] using h₁.trans h₂.symm

theorem CarryTransducer.normalizeReversedAux_length
    (T : CarryTransducer) (coefficients : List ℕ) (carryIn : ℕ) :
    (T.normalizeReversedAux coefficients carryIn).length = coefficients.length := by
  induction coefficients generalizing carryIn with
  | nil =>
      simp [CarryTransducer.normalizeReversedAux]
  | cons coefficient tail ih =>
      cases tail with
      | nil =>
          simp [CarryTransducer.normalizeReversedAux]
      | cons next rest =>
          simp [CarryTransducer.normalizeReversedAux, ih]

theorem CarryTransducer.normalizeReversed_length
    (T : CarryTransducer) (coefficients : List ℕ) :
    (T.normalizeReversed coefficients).length = coefficients.length := by
  simpa [CarryTransducer.normalizeReversed] using
    T.normalizeReversedAux_length coefficients 0

theorem CarryTransducer.normalizeBlocks_length
    (T : CarryTransducer) (coefficients : List ℕ) :
    (T.normalizeBlocks coefficients).length = coefficients.length := by
  simp [CarryTransducer.normalizeBlocks, T.normalizeReversed_length]

/-- The reversed normalization recursion preserves the exact base-`B` value. -/
theorem CarryTransducer.normalizeReversedAux_preserves_value
    (T : CarryTransducer) (coefficients : List ℕ) (carryIn : ℕ)
    (hcoefficients : coefficients ≠ []) :
    T.evalReversed (T.normalizeReversedAux coefficients carryIn) =
      carryIn + T.evalReversed coefficients := by
  induction coefficients generalizing carryIn with
  | nil =>
      contradiction
  | cons coefficient tail ih =>
      cases tail with
      | nil =>
          simp [CarryTransducer.normalizeReversedAux, CarryTransducer.evalReversed, Nat.add_comm]
      | cons next rest =>
          have htail : next :: rest ≠ [] := by simp
          specialize ih ((coefficient + carryIn) / T.blockBase) htail
          simp [CarryTransducer.normalizeReversedAux, CarryTransducer.evalReversed, ih]
          have hsplit :
              (coefficient + carryIn) % T.blockBase +
                  T.blockBase * ((coefficient + carryIn) / T.blockBase) =
                coefficient + carryIn := by
            simpa [Nat.mul_comm] using Nat.mod_add_div (coefficient + carryIn) T.blockBase
          rw [Nat.mul_add]
          calc
            (coefficient + carryIn) % T.blockBase +
                (T.blockBase * ((coefficient + carryIn) / T.blockBase) +
                  T.blockBase * (next + T.blockBase * T.evalReversed rest))
                =
                  ((coefficient + carryIn) % T.blockBase +
                    T.blockBase * ((coefficient + carryIn) / T.blockBase)) +
                    T.blockBase * (next + T.blockBase * T.evalReversed rest) := by
                      ac_rfl
            _ = coefficient + carryIn + T.blockBase * (next + T.blockBase * T.evalReversed rest) := by
              rw [hsplit]
          omega

/-- Finite normalization preserves the exact value of a reversed coefficient word. -/
theorem CarryTransducer.normalizeReversed_preserves_value
    (T : CarryTransducer) (coefficients : List ℕ) :
    T.evalReversed (T.normalizeReversed coefficients) = T.evalReversed coefficients := by
  cases coefficients with
  | nil =>
      simp [CarryTransducer.normalizeReversed, CarryTransducer.normalizeReversedAux,
        CarryTransducer.evalReversed]
  | cons coefficient tail =>
      simpa [CarryTransducer.normalizeReversed] using
        T.normalizeReversedAux_preserves_value (coefficient :: tail) 0 (by simp)

/-- Finite normalization preserves the exact value of a block word. -/
theorem CarryTransducer.normalizeBlocks_preserves_value
    (T : CarryTransducer) (coefficients : List ℕ) :
    T.evalBlocks (T.normalizeBlocks coefficients) = T.evalBlocks coefficients := by
  simpa [CarryTransducer.evalBlocks, CarryTransducer.normalizeBlocks] using
    T.normalizeReversed_preserves_value coefficients.reverse

/-- The finite raw coefficient word `q, qk, qk^2, ...`. -/
def BlockCoordinate.rawCoefficientWord (C : BlockCoordinate) (length : ℕ) : List ℕ :=
  (List.range length).map C.rawCoefficient

theorem BlockCoordinate.rawCoefficientWord_succ
    (C : BlockCoordinate) (length : ℕ) :
    C.rawCoefficientWord (length + 1) = C.rawCoefficientWord length ++ [C.rawCoefficient length] := by
  simp [BlockCoordinate.rawCoefficientWord, List.range_succ]

theorem BlockCoordinate.rawCoefficientWord_length
    (C : BlockCoordinate) (length : ℕ) :
    (C.rawCoefficientWord length).length = length := by
  simp [BlockCoordinate.rawCoefficientWord]

theorem BlockCoordinate.blockBase_gt_one_of_goodMode
    (C : BlockCoordinate) (hgood : C.goodMode) :
    1 < C.blockBase := by
  unfold BlockCoordinate.goodMode at hgood
  exact lt_of_le_of_lt (Nat.succ_le_of_lt C.modulus_pos) hgood

theorem BlockCoordinate.bodyTerm_succ
    (C : BlockCoordinate) (length : ℕ) :
    C.bodyTerm (length + 1) = C.blockBase * C.bodyTerm length + C.rawCoefficient length := by
  have hk : C.remainderK ≤ C.blockBase := Nat.mod_le _ _
  have hpow : C.remainderK ^ length ≤ C.blockBase ^ length := Nat.pow_le_pow_left hk length
  have hmul : C.remainderK ^ length * C.remainderK ≤ C.blockBase ^ length * C.blockBase := by
    exact Nat.mul_le_mul hpow hk
  apply Nat.eq_of_mul_eq_mul_right C.modulus_pos
  rw [Nat.add_mul, C.bodyTerm_mul_modulus_eq (length + 1), Nat.mul_assoc,
    C.bodyTerm_mul_modulus_eq length]
  unfold BlockCoordinate.rawCoefficient
  rw [Nat.mul_right_comm, Nat.mul_assoc, ← Nat.mul_assoc,
    C.quotientQ_mul_modulus_eq_blockBase_sub_remainderK]
  rw [pow_succ, pow_succ]
  rw [Nat.sub_eq_iff_eq_add hmul]
  symm
  calc
    C.blockBase * (C.blockBase ^ length - C.remainderK ^ length) +
        (C.blockBase - C.remainderK) * C.remainderK ^ length +
        C.remainderK ^ length * C.remainderK
        = C.blockBase * (C.blockBase ^ length - C.remainderK ^ length) +
            ((C.blockBase - C.remainderK) * C.remainderK ^ length +
              C.remainderK * C.remainderK ^ length) := by
            rw [Nat.mul_comm (C.remainderK ^ length) C.remainderK]
            ac_rfl
    _ = C.blockBase * (C.blockBase ^ length - C.remainderK ^ length) +
          ((C.blockBase - C.remainderK) + C.remainderK) * C.remainderK ^ length := by
            rw [← Nat.add_mul]
    _ = C.blockBase * (C.blockBase ^ length - C.remainderK ^ length) +
          C.blockBase * C.remainderK ^ length := by
            rw [Nat.sub_add_cancel hk]
    _ = C.blockBase * ((C.blockBase ^ length - C.remainderK ^ length) +
          C.remainderK ^ length) := by
            rw [← Nat.mul_add]
    _ = C.blockBase * C.blockBase ^ length := by
            rw [Nat.sub_add_cancel hpow]
    _ = C.blockBase ^ length * C.blockBase := by rw [Nat.mul_comm]

/-- The carry transducer attached to a good block coordinate. -/
def BlockCoordinate.carryTransducer
    (C : BlockCoordinate) (hgood : C.goodMode) : CarryTransducer where
  blockBase := C.blockBase
  blockBase_gt_one := C.blockBase_gt_one_of_goodMode hgood

/-- The finite carry-normalized raw coefficient word for one block coordinate. -/
def BlockCoordinate.normalizedRawWord
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) : List ℕ :=
  (C.carryTransducer hgood).normalizeBlocks (C.rawCoefficientWord length)

/-- The traced finite carry run on the raw coefficient word of a block coordinate. -/
def BlockCoordinate.traceRawWord
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) : List CarryTraceStep :=
  (C.carryTransducer hgood).traceBlocks (C.rawCoefficientWord length)

theorem BlockCoordinate.normalizedRawWord_length
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.normalizedRawWord hgood length).length = length := by
  simp [BlockCoordinate.normalizedRawWord, C.rawCoefficientWord_length,
    CarryTransducer.normalizeBlocks_length]

theorem BlockCoordinate.normalizedRawWord_preserves_value
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.carryTransducer hgood).evalBlocks (C.normalizedRawWord hgood length) =
      (C.carryTransducer hgood).evalBlocks (C.rawCoefficientWord length) := by
  simpa [BlockCoordinate.normalizedRawWord] using
    (C.carryTransducer hgood).normalizeBlocks_preserves_value (C.rawCoefficientWord length)

theorem BlockCoordinate.evalBlocks_rawCoefficientWord_eq_bodyTerm
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.carryTransducer hgood).evalBlocks (C.rawCoefficientWord length) = C.bodyTerm length := by
  induction length with
  | zero =>
      simp [BlockCoordinate.rawCoefficientWord, BlockCoordinate.bodyTerm,
        CarryTransducer.evalBlocks, CarryTransducer.evalReversed]
  | succ length ih =>
      rw [C.rawCoefficientWord_succ, (C.carryTransducer hgood).evalBlocks_append_singleton]
      rw [ih]
      simpa [BlockCoordinate.carryTransducer] using (C.bodyTerm_succ length).symm

theorem BlockCoordinate.evalBlocks_normalizedRawWord_eq_bodyTerm
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.carryTransducer hgood).evalBlocks (C.normalizedRawWord hgood length) = C.bodyTerm length := by
  rw [C.normalizedRawWord_preserves_value hgood length]
  exact C.evalBlocks_rawCoefficientWord_eq_bodyTerm hgood length

theorem BlockCoordinate.blockBase_pow_le_bodyTerm_succ
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    C.blockBase ^ length ≤ C.bodyTerm (length + 1) := by
  induction length with
  | zero =>
      have hq : 1 ≤ C.quotientQ := Nat.succ_le_of_lt (C.quotientQ_pos_of_goodMode hgood)
      calc
        C.blockBase ^ 0 = 1 := by simp
        _ ≤ C.quotientQ := hq
        _ = C.bodyTerm 1 := by
            rw [show (1 : ℕ) = 0 + 1 by rfl, C.bodyTerm_succ 0]
            have hzero : C.bodyTerm 0 = 0 := by simp [BlockCoordinate.bodyTerm]
            rw [hzero]
            simp [BlockCoordinate.rawCoefficient]
  | succ length ih =>
      calc
        C.blockBase ^ (length + 1) = C.blockBase * C.blockBase ^ length := by rw [pow_succ']
        _ ≤ C.blockBase * C.bodyTerm (length + 1) := Nat.mul_le_mul_left _ ih
        _ ≤ C.blockBase * C.bodyTerm (length + 1) + C.rawCoefficient (length + 1) :=
            Nat.le_add_right _ _
        _ = C.bodyTerm (length + 2) := by rw [(C.bodyTerm_succ (length + 1)).symm]

theorem BlockCoordinate.bodyTerm_lt_blockBase_pow
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus) (length : ℕ) :
    C.bodyTerm length < C.blockBase ^ length := by
  rw [BlockCoordinate.bodyTerm]
  refine (Nat.div_lt_iff_lt_mul C.modulus_pos).2 ?_
  have hnum_le : C.blockBase ^ length - C.remainderK ^ length ≤ C.blockBase ^ length := Nat.sub_le _ _
  have hpow_pos : 0 < C.blockBase ^ length := by
    exact Nat.pow_pos (C.blockBase_pos_of_goodMode hgood)
  have hpow_lt : C.blockBase ^ length < C.modulus * C.blockBase ^ length := by
    simpa [one_mul] using Nat.mul_lt_mul_of_pos_right hmod hpow_pos
  simpa [Nat.mul_comm] using lt_of_le_of_lt hnum_le hpow_lt

theorem BlockCoordinate.bodyTerm_digits_length_succ
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus) (length : ℕ) :
    (Nat.digits C.blockBase (C.bodyTerm (length + 1))).length = length + 1 := by
  have hb : 1 < C.blockBase := C.blockBase_gt_one_of_goodMode hgood
  have hupper : C.bodyTerm (length + 1) < C.blockBase ^ (length + 1) :=
    C.bodyTerm_lt_blockBase_pow hgood hmod (length + 1)
  have hlower : C.blockBase ^ length ≤ C.bodyTerm (length + 1) :=
    C.blockBase_pow_le_bodyTerm_succ hgood length
  have hle : (Nat.digits C.blockBase (C.bodyTerm (length + 1))).length ≤ length + 1 :=
    (Nat.digits_length_le_iff hb (C.bodyTerm (length + 1))).2 hupper
  have hlt : length < (Nat.digits C.blockBase (C.bodyTerm (length + 1))).length :=
    (Nat.lt_digits_length_iff hb (C.bodyTerm (length + 1))).2 hlower
  omega

theorem BlockCoordinate.traceRawWord_length
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.traceRawWord hgood length).length = length := by
  simp [BlockCoordinate.traceRawWord, C.rawCoefficientWord_length,
    CarryTransducer.traceBlocks_length]

theorem BlockCoordinate.traceRawWord_map_isLeftmost_of_pos
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.traceRawWord hgood (length + 1)).map CarryTraceStep.isLeftmost =
      true :: List.replicate length false := by
  have hcoeff : C.rawCoefficientWord (length + 1) ≠ [] := by
    simp [BlockCoordinate.rawCoefficientWord]
  simpa [BlockCoordinate.traceRawWord, C.rawCoefficientWord_length] using
    (C.carryTransducer hgood).traceBlocks_map_isLeftmost_of_ne_nil
      (C.rawCoefficientWord (length + 1)) hcoeff

theorem BlockCoordinate.mem_traceRawWord_tail_block_lt
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) {step : CarryTraceStep}
    (hstep : step ∈ (C.traceRawWord hgood (length + 1)).tail) :
    step.blockValue < C.blockBase := by
  cases htrace : C.traceRawWord hgood (length + 1) with
  | nil =>
      have hlen := C.traceRawWord_length hgood (length + 1)
      simp [htrace] at hlen
  | cons head tail =>
      have hmap :
          (head :: tail).map CarryTraceStep.isLeftmost = true :: List.replicate length false := by
        simpa [htrace] using C.traceRawWord_map_isLeftmost_of_pos hgood length
      have htailmap : tail.map CarryTraceStep.isLeftmost = List.replicate length false := by
        simpa using congrArg List.tail hmap
      rw [htrace] at hstep
      have hstep_full : step ∈ head :: tail := List.mem_cons_of_mem _ hstep
      have hisLeft : step.isLeftmost = false := by
        have hisLeft_mem : step.isLeftmost ∈ List.replicate length false := by
          rw [← htailmap]
          exact List.mem_map.2 ⟨step, hstep, rfl⟩
        exact List.eq_of_mem_replicate hisLeft_mem
      have hstep_trace : step ∈ C.traceRawWord hgood (length + 1) := by
        simpa [htrace] using hstep_full
      exact (C.carryTransducer hgood).mem_traceBlocks_nonleft_block_lt hstep_trace hisLeft

theorem BlockCoordinate.mem_normalizedRawWord_lt_blockBase
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    {length digit : ℕ} (hmem : digit ∈ C.normalizedRawWord hgood (length + 1)) :
    digit < C.blockBase := by
  obtain ⟨leading, tail, hword⟩ :
      ∃ leading tail, C.normalizedRawWord hgood (length + 1) = leading :: tail := by
    cases hlist : C.normalizedRawWord hgood (length + 1) with
    | nil =>
        have hlen := C.normalizedRawWord_length hgood (length + 1)
        simp [hlist] at hlen
    | cons leading tail =>
        exact ⟨leading, tail, by simp⟩
  rw [hword] at hmem
  simp at hmem
  rcases hmem with rfl | hmemtail
  ·
    have htail_len : tail.length = length := by
      have hlen := C.normalizedRawWord_length hgood (length + 1)
      rw [hword] at hlen
      simpa using Nat.succ.inj hlen
    have hvalue :
        (C.carryTransducer hgood).evalBlocks (digit :: tail) = C.bodyTerm (length + 1) := by
      simpa [hword] using C.evalBlocks_normalizedRawWord_eq_bodyTerm hgood (length + 1)
    have hupper : C.bodyTerm (length + 1) < C.blockBase ^ (length + 1) :=
      C.bodyTerm_lt_blockBase_pow hgood hmod (length + 1)
    by_contra hhead
    have hhead_ge : C.blockBase ≤ digit := Nat.le_of_not_lt hhead
    have hlower :
        C.blockBase ^ (length + 1) ≤ (C.carryTransducer hgood).evalBlocks (digit :: tail) := by
      calc
        C.blockBase ^ (length + 1) = C.blockBase * C.blockBase ^ length := by rw [pow_succ']
        _ = C.blockBase ^ length * C.blockBase := by rw [Nat.mul_comm]
        _ ≤ C.blockBase ^ length * digit := Nat.mul_le_mul_left _ hhead_ge
        _ = C.blockBase ^ tail.length * digit := by rw [htail_len]
        _ ≤ (C.carryTransducer hgood).evalBlocks tail + C.blockBase ^ tail.length * digit :=
          Nat.le_add_left _ _
        _ = (C.carryTransducer hgood).evalBlocks (digit :: tail) := by
          simpa [BlockCoordinate.carryTransducer] using
            ((C.carryTransducer hgood).evalBlocks_cons digit tail).symm
    exact (Nat.not_lt_of_ge (hvalue ▸ hlower)) hupper
  · have htailmap :
        (C.traceRawWord hgood (length + 1)).tail.map CarryTraceStep.blockValue = tail := by
      have hnorm :
          (C.carryTransducer hgood).normalizeBlocks (C.rawCoefficientWord (length + 1)) = leading :: tail := by
        simpa [BlockCoordinate.normalizedRawWord] using hword
      have hmap :
          (C.traceRawWord hgood (length + 1)).map CarryTraceStep.blockValue = leading :: tail := by
        rw [BlockCoordinate.traceRawWord, (C.carryTransducer hgood).traceBlocks_map_blockValue,
          hnorm]
      simpa using congrArg List.tail hmap
    rw [← htailmap] at hmemtail
    rcases List.mem_map.mp hmemtail with ⟨step, hstep, rfl⟩
    exact C.mem_traceRawWord_tail_block_lt hgood length hstep

theorem BlockCoordinate.digits_bodyTerm_eq_normalizedRawWord_reverse
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus) (length : ℕ) :
    Nat.digits C.blockBase (C.bodyTerm length) = (C.normalizedRawWord hgood length).reverse := by
  cases length with
  | zero =>
      simp [BlockCoordinate.bodyTerm, BlockCoordinate.normalizedRawWord,
        BlockCoordinate.rawCoefficientWord, CarryTransducer.normalizeBlocks,
        CarryTransducer.normalizeReversed, CarryTransducer.normalizeReversedAux]
  | succ length =>
      have hb : 1 < C.blockBase := C.blockBase_gt_one_of_goodMode hgood
      apply Nat.ofDigits_inj_of_len_eq hb
      · rw [C.bodyTerm_digits_length_succ hgood hmod length]
        simp [C.normalizedRawWord_length]
      · intro digit hmem
        exact Nat.digits_lt_base hb hmem
      · intro digit hmem
        have hmem' : digit ∈ C.normalizedRawWord hgood (length + 1) := by
          simpa using List.mem_reverse.mp hmem
        exact C.mem_normalizedRawWord_lt_blockBase hgood hmod hmem'
      · calc
          Nat.ofDigits C.blockBase (Nat.digits C.blockBase (C.bodyTerm (length + 1)))
              = C.bodyTerm (length + 1) := Nat.ofDigits_digits _ _
          _ = (C.carryTransducer hgood).evalBlocks (C.normalizedRawWord hgood (length + 1)) := by
              symm
              exact C.evalBlocks_normalizedRawWord_eq_bodyTerm hgood (length + 1)
          _ = Nat.ofDigits C.blockBase (C.normalizedRawWord hgood (length + 1)).reverse := by
              simpa [BlockCoordinate.carryTransducer] using
                (C.carryTransducer hgood).evalBlocks_eq_ofDigits_reverse
                  (C.normalizedRawWord hgood (length + 1))

theorem BlockCoordinate.traceRawWord_map_coefficient
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.traceRawWord hgood length).map CarryTraceStep.coefficient = C.rawCoefficientWord length := by
  simpa [BlockCoordinate.traceRawWord] using
    (C.carryTransducer hgood).traceBlocks_map_coefficient (C.rawCoefficientWord length)

theorem BlockCoordinate.traceRawWord_map_blockValue
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.traceRawWord hgood length).map CarryTraceStep.blockValue = C.normalizedRawWord hgood length := by
  simpa [BlockCoordinate.traceRawWord, BlockCoordinate.normalizedRawWord] using
    (C.carryTransducer hgood).traceBlocks_map_blockValue (C.rawCoefficientWord length)

theorem BlockCoordinate.mem_traceRawWord_value
    (C : BlockCoordinate) (hgood : C.goodMode) {length : ℕ} {step : CarryTraceStep}
    (hstep : step ∈ C.traceRawWord hgood length) :
    step.coefficient + step.carryIn = step.blockValue + C.blockBase * step.carryOut := by
  simpa [BlockCoordinate.traceRawWord, BlockCoordinate.carryTransducer] using
    (C.carryTransducer hgood).mem_traceBlocks_value hstep

/-- One emitted long-division step in block coordinates. -/
structure RemainderTraceStep where
  remainderIn : ℕ
  blockValue : ℕ
  remainderOut : ℕ
deriving Repr, DecidableEq

/-- The actual long-division remainder state after `j` block steps. -/
def BlockCoordinate.longDivisionRemainder (C : BlockCoordinate) : ℕ → ℕ
  | 0 => 1 % C.modulus
  | j + 1 => (C.blockBase * C.longDivisionRemainder j) % C.modulus

/-- The actual displayed block emitted at position `j`. -/
def BlockCoordinate.emittedBlock (C : BlockCoordinate) (j : ℕ) : ℕ :=
  (C.blockBase * C.longDivisionRemainder j) / C.modulus

/-- The first `length` emitted long-division blocks. -/
def BlockCoordinate.emittedBlockWord (C : BlockCoordinate) (length : ℕ) : List ℕ :=
  (List.range length).map C.emittedBlock

/-- The integer whose base-`B` digits are the first `length` emitted blocks. -/
def BlockCoordinate.emittedPrefixValue (C : BlockCoordinate) (length : ℕ) : ℕ :=
  C.blockBase ^ length / C.modulus

/-- One recorded emitted long-division step. -/
def BlockCoordinate.remainderTraceStep (C : BlockCoordinate) (j : ℕ) : RemainderTraceStep :=
  {
    remainderIn := C.longDivisionRemainder j
    blockValue := C.emittedBlock j
    remainderOut := C.longDivisionRemainder (j + 1)
  }

/-- The first `length` emitted long-division steps. -/
def BlockCoordinate.remainderTrace (C : BlockCoordinate) (length : ℕ) : List RemainderTraceStep :=
  (List.range length).map C.remainderTraceStep

theorem BlockCoordinate.longDivisionRemainder_eq_pow_mod
    (C : BlockCoordinate) (length : ℕ) :
    C.longDivisionRemainder length = C.blockBase ^ length % C.modulus := by
  induction length with
  | zero =>
      simp [BlockCoordinate.longDivisionRemainder]
  | succ length ih =>
      rw [BlockCoordinate.longDivisionRemainder, ih, pow_succ]
      rw [mul_comm (C.blockBase ^ length) C.blockBase]
      rw [Nat.mul_mod C.blockBase (C.blockBase ^ length % C.modulus) C.modulus,
        Nat.mod_mod_of_dvd (C.blockBase ^ length) (dvd_refl C.modulus), ← Nat.mul_mod]

theorem BlockCoordinate.longDivisionRemainder_lt_modulus
    (C : BlockCoordinate) (length : ℕ) :
    C.longDivisionRemainder length < C.modulus := by
  rw [C.longDivisionRemainder_eq_pow_mod]
  exact Nat.mod_lt _ C.modulus_pos

theorem BlockCoordinate.emittedBlock_lt_blockBase
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    C.emittedBlock length < C.blockBase := by
  unfold BlockCoordinate.emittedBlock
  have hremainder_lt : C.longDivisionRemainder length < C.modulus :=
    C.longDivisionRemainder_lt_modulus length
  have hprod_lt :
      C.blockBase * C.longDivisionRemainder length < C.blockBase * C.modulus := by
    exact Nat.mul_lt_mul_of_pos_left hremainder_lt (C.blockBase_pos_of_goodMode hgood)
  rw [Nat.div_lt_iff_lt_mul C.modulus_pos]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hprod_lt

theorem BlockCoordinate.emittedBlock_zero_eq_quotientQ
    (C : BlockCoordinate) (hmod : 1 < C.modulus) :
    C.emittedBlock 0 = C.quotientQ := by
  unfold BlockCoordinate.emittedBlock BlockCoordinate.quotientQ BlockCoordinate.longDivisionRemainder
  rw [Nat.mod_eq_of_lt hmod]
  simp

theorem BlockCoordinate.emittedBlockWord_succ
    (C : BlockCoordinate) (length : ℕ) :
    C.emittedBlockWord (length + 1) = C.emittedBlockWord length ++ [C.emittedBlock length] := by
  simp [BlockCoordinate.emittedBlockWord, List.range_succ]

theorem BlockCoordinate.remainderTrace_length
    (C : BlockCoordinate) (length : ℕ) :
    (C.remainderTrace length).length = length := by
  simp [BlockCoordinate.remainderTrace]

theorem BlockCoordinate.remainderTrace_map_blockValue
    (C : BlockCoordinate) (length : ℕ) :
    (C.remainderTrace length).map RemainderTraceStep.blockValue = C.emittedBlockWord length := by
  simp [BlockCoordinate.remainderTrace, BlockCoordinate.emittedBlockWord,
    BlockCoordinate.remainderTraceStep, Function.comp]

theorem BlockCoordinate.remainderTrace_map_remainderIn
    (C : BlockCoordinate) (length : ℕ) :
    (C.remainderTrace length).map RemainderTraceStep.remainderIn =
      (List.range length).map C.longDivisionRemainder := by
  simp [BlockCoordinate.remainderTrace, BlockCoordinate.remainderTraceStep, Function.comp]

theorem BlockCoordinate.remainderTrace_map_remainderOut
    (C : BlockCoordinate) (length : ℕ) :
    (C.remainderTrace length).map RemainderTraceStep.remainderOut =
      (List.range length).map (fun j => C.longDivisionRemainder (j + 1)) := by
  simp [BlockCoordinate.remainderTrace, BlockCoordinate.remainderTraceStep, Function.comp]

theorem BlockCoordinate.remainderTraceStep_value
    (C : BlockCoordinate) (length : ℕ) :
    C.blockBase * (C.remainderTraceStep length).remainderIn =
      (C.remainderTraceStep length).blockValue * C.modulus +
        (C.remainderTraceStep length).remainderOut := by
  unfold BlockCoordinate.remainderTraceStep BlockCoordinate.emittedBlock
  simpa using (Nat.div_add_mod' (C.blockBase * C.longDivisionRemainder length) C.modulus).symm

theorem BlockCoordinate.emittedPrefixValue_succ
    (C : BlockCoordinate) (length : ℕ) :
    C.emittedPrefixValue (length + 1) =
      C.blockBase * C.emittedPrefixValue length + C.emittedBlock length := by
  unfold BlockCoordinate.emittedPrefixValue BlockCoordinate.emittedBlock
  have hdecomp :
      C.blockBase ^ length =
        (C.blockBase ^ length / C.modulus) * C.modulus + C.longDivisionRemainder length := by
    rw [C.longDivisionRemainder_eq_pow_mod]
    exact (Nat.div_add_mod' (C.blockBase ^ length) C.modulus).symm
  have hdvd :
      C.modulus ∣ C.blockBase * (C.blockBase ^ length / C.modulus * C.modulus) := by
    refine ⟨C.blockBase * (C.blockBase ^ length / C.modulus), ?_⟩
    ac_rfl
  conv_lhs =>
    rw [pow_succ', hdecomp, Nat.mul_add]
  rw [Nat.add_div_of_dvd_right hdvd]
  exact congrArg
    (fun t => t + (C.blockBase * C.longDivisionRemainder length) / C.modulus)
    (by simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (Nat.mul_div_right (C.blockBase * (C.blockBase ^ length / C.modulus)) C.modulus_pos))

theorem BlockCoordinate.evalBlocks_emittedBlockWord_eq_emittedPrefixValue
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus) (length : ℕ) :
    (C.carryTransducer hgood).evalBlocks (C.emittedBlockWord length) = C.emittedPrefixValue length := by
  induction length with
  | zero =>
      simp [BlockCoordinate.emittedBlockWord, BlockCoordinate.emittedPrefixValue,
        CarryTransducer.evalBlocks, CarryTransducer.evalReversed, Nat.div_eq_of_lt hmod]
  | succ length ih =>
      rw [C.emittedBlockWord_succ, (C.carryTransducer hgood).evalBlocks_append_singleton, ih]
      simpa [BlockCoordinate.carryTransducer] using (C.emittedPrefixValue_succ length).symm

theorem BlockCoordinate.blockBase_pow_le_emittedPrefixValue_succ
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus) (length : ℕ) :
    C.blockBase ^ length ≤ C.emittedPrefixValue (length + 1) := by
  induction length with
  | zero =>
      have hq : 1 ≤ C.quotientQ := Nat.succ_le_of_lt (C.quotientQ_pos_of_goodMode hgood)
      have hzero : C.emittedPrefixValue 0 = 0 := by
        simp [BlockCoordinate.emittedPrefixValue, Nat.div_eq_of_lt hmod]
      calc
        C.blockBase ^ 0 = 1 := by simp
        _ ≤ C.quotientQ := hq
        _ = C.emittedPrefixValue 1 := by
            rw [show (1 : ℕ) = 0 + 1 by rfl, C.emittedPrefixValue_succ 0,
              C.emittedBlock_zero_eq_quotientQ hmod]
            rw [hzero]
            simp
  | succ length ih =>
      calc
        C.blockBase ^ (length + 1) = C.blockBase * C.blockBase ^ length := by rw [pow_succ']
        _ ≤ C.blockBase * C.emittedPrefixValue (length + 1) := Nat.mul_le_mul_left _ ih
        _ ≤ C.blockBase * C.emittedPrefixValue (length + 1) + C.emittedBlock (length + 1) :=
          Nat.le_add_right _ _
        _ = C.emittedPrefixValue (length + 2) := by rw [(C.emittedPrefixValue_succ (length + 1)).symm]

theorem BlockCoordinate.emittedPrefixValue_lt_blockBase_pow
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus) (length : ℕ) :
    C.emittedPrefixValue length < C.blockBase ^ length := by
  unfold BlockCoordinate.emittedPrefixValue
  refine (Nat.div_lt_iff_lt_mul C.modulus_pos).2 ?_
  have hpow_pos : 0 < C.blockBase ^ length := by
    exact Nat.pow_pos (C.blockBase_pos_of_goodMode hgood)
  have hpow_lt : C.blockBase ^ length < C.modulus * C.blockBase ^ length := by
    simpa [one_mul] using Nat.mul_lt_mul_of_pos_right hmod hpow_pos
  simpa [Nat.mul_comm] using hpow_lt

theorem BlockCoordinate.emittedPrefixValue_digits_length_succ
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus) (length : ℕ) :
    (Nat.digits C.blockBase (C.emittedPrefixValue (length + 1))).length = length + 1 := by
  have hb : 1 < C.blockBase := C.blockBase_gt_one_of_goodMode hgood
  have hupper : C.emittedPrefixValue (length + 1) < C.blockBase ^ (length + 1) :=
    C.emittedPrefixValue_lt_blockBase_pow hgood hmod (length + 1)
  have hlower : C.blockBase ^ length ≤ C.emittedPrefixValue (length + 1) :=
    C.blockBase_pow_le_emittedPrefixValue_succ hgood hmod length
  have hle : (Nat.digits C.blockBase (C.emittedPrefixValue (length + 1))).length ≤ length + 1 :=
    (Nat.digits_length_le_iff hb (C.emittedPrefixValue (length + 1))).2 hupper
  have hlt : length < (Nat.digits C.blockBase (C.emittedPrefixValue (length + 1))).length :=
    (Nat.lt_digits_length_iff hb (C.emittedPrefixValue (length + 1))).2 hlower
  omega

theorem BlockCoordinate.digits_emittedPrefixValue_eq_emittedBlockWord_reverse
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus) (length : ℕ) :
    Nat.digits C.blockBase (C.emittedPrefixValue length) = (C.emittedBlockWord length).reverse := by
  cases length with
  | zero =>
      simp [BlockCoordinate.emittedPrefixValue, BlockCoordinate.emittedBlockWord,
        Nat.div_eq_of_lt hmod]
  | succ length =>
      have hb : 1 < C.blockBase := C.blockBase_gt_one_of_goodMode hgood
      apply Nat.ofDigits_inj_of_len_eq hb
      · rw [C.emittedPrefixValue_digits_length_succ hgood hmod length]
        simp [BlockCoordinate.emittedBlockWord]
      · intro digit hmem
        exact Nat.digits_lt_base hb hmem
      · intro digit hmem
        have hmem' : digit ∈ C.emittedBlockWord (length + 1) := by
          simpa using List.mem_reverse.mp hmem
        rw [BlockCoordinate.emittedBlockWord] at hmem'
        rcases List.mem_map.mp hmem' with ⟨j, _, rfl⟩
        exact C.emittedBlock_lt_blockBase hgood j
      · calc
          Nat.ofDigits C.blockBase (Nat.digits C.blockBase (C.emittedPrefixValue (length + 1)))
              = C.emittedPrefixValue (length + 1) := Nat.ofDigits_digits _ _
          _ = (C.carryTransducer hgood).evalBlocks (C.emittedBlockWord (length + 1)) := by
              symm
              exact C.evalBlocks_emittedBlockWord_eq_emittedPrefixValue hgood hmod (length + 1)
          _ = Nat.ofDigits C.blockBase (C.emittedBlockWord (length + 1)).reverse := by
              simpa [BlockCoordinate.carryTransducer] using
                (C.carryTransducer hgood).evalBlocks_eq_ofDigits_reverse
                  (C.emittedBlockWord (length + 1))

theorem BlockCoordinate.emittedPrefixValue_eq_bodyTerm_add_remainderKPowDivModulus
    (C : BlockCoordinate) (length : ℕ) :
    C.emittedPrefixValue length = C.bodyTerm length + C.remainderK ^ length / C.modulus := by
  unfold BlockCoordinate.emittedPrefixValue BlockCoordinate.bodyTerm
  have hk : C.remainderK ^ length ≤ C.blockBase ^ length := by
    exact Nat.pow_le_pow_left (Nat.mod_le _ _) length
  calc
    C.blockBase ^ length / C.modulus
      = ((C.blockBase ^ length - C.remainderK ^ length) + C.remainderK ^ length) / C.modulus := by
          rw [Nat.sub_add_cancel hk]
    _ = (C.blockBase ^ length - C.remainderK ^ length) / C.modulus + C.remainderK ^ length / C.modulus := by
          exact Nat.add_div_of_dvd_right (C.modulus_dvd_blockBase_pow_sub_remainderK_pow length)
    _ = C.bodyTerm length + C.remainderK ^ length / C.modulus := by
          rfl

theorem BlockCoordinate.emittedPrefixValue_eq_bodyTerm_of_remainderK_pow_lt_modulus
    (C : BlockCoordinate) (length : ℕ) (hsmall : C.remainderK ^ length < C.modulus) :
    C.emittedPrefixValue length = C.bodyTerm length := by
  rw [C.emittedPrefixValue_eq_bodyTerm_add_remainderKPowDivModulus]
  simp [Nat.div_eq_of_lt hsmall]

theorem BlockCoordinate.normalizedRawWord_eq_emittedBlockWord_of_remainderK_pow_lt_modulus
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (length : ℕ) (hsmall : C.remainderK ^ length < C.modulus) :
    C.normalizedRawWord hgood length = C.emittedBlockWord length := by
  have hdigits :
      Nat.digits C.blockBase (C.bodyTerm length) =
        Nat.digits C.blockBase (C.emittedPrefixValue length) := by
    rw [C.emittedPrefixValue_eq_bodyTerm_of_remainderK_pow_lt_modulus length hsmall]
  rw [C.digits_bodyTerm_eq_normalizedRawWord_reverse hgood hmod,
    C.digits_emittedPrefixValue_eq_emittedBlockWord_reverse hgood hmod] at hdigits
  simpa using congrArg List.reverse hdigits

/-- Finite-window carry/remainder comparison pairs. -/
def BlockCoordinate.carryRemainderPairs
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    List (CarryTraceStep × RemainderTraceStep) :=
  (C.traceRawWord hgood length).zip (C.remainderTrace length)

theorem BlockCoordinate.carryRemainderPairs_length
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.carryRemainderPairs hgood length).length = length := by
  unfold BlockCoordinate.carryRemainderPairs
  rw [List.length_zip, C.traceRawWord_length, C.remainderTrace_length, min_self]

theorem BlockCoordinate.carryRemainderPairs_unzip
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    List.unzip (C.carryRemainderPairs hgood length) =
      (C.traceRawWord hgood length, C.remainderTrace length) := by
  unfold BlockCoordinate.carryRemainderPairs
  exact List.unzip_zip (by rw [C.traceRawWord_length, C.remainderTrace_length])

theorem BlockCoordinate.carryRemainderPairs_map_carryStep
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.carryRemainderPairs hgood length).map Prod.fst = C.traceRawWord hgood length := by
  have hfst := congrArg Prod.fst (C.carryRemainderPairs_unzip hgood length)
  simpa using hfst

theorem BlockCoordinate.carryRemainderPairs_map_remainderStep
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.carryRemainderPairs hgood length).map Prod.snd = C.remainderTrace length := by
  have hsnd := congrArg Prod.snd (C.carryRemainderPairs_unzip hgood length)
  simpa using hsnd

theorem BlockCoordinate.carryRemainderPairs_map_coefficient
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.carryRemainderPairs hgood length).map (fun pair => pair.1.coefficient) =
      C.rawCoefficientWord length := by
  calc
    (C.carryRemainderPairs hgood length).map (fun pair => pair.1.coefficient)
      = ((C.carryRemainderPairs hgood length).map Prod.fst).map CarryTraceStep.coefficient := by
          simp
    _ = (C.traceRawWord hgood length).map CarryTraceStep.coefficient := by
          rw [C.carryRemainderPairs_map_carryStep]
    _ = C.rawCoefficientWord length := C.traceRawWord_map_coefficient hgood length

theorem BlockCoordinate.carryRemainderPairs_map_carryIn
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.carryRemainderPairs hgood length).map (fun pair => pair.1.carryIn) =
      (C.traceRawWord hgood length).map CarryTraceStep.carryIn := by
  calc
    (C.carryRemainderPairs hgood length).map (fun pair => pair.1.carryIn)
      = ((C.carryRemainderPairs hgood length).map Prod.fst).map CarryTraceStep.carryIn := by
          simp
    _ = (C.traceRawWord hgood length).map CarryTraceStep.carryIn := by
          rw [C.carryRemainderPairs_map_carryStep]

theorem BlockCoordinate.carryRemainderPairs_map_carryBlockValue
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.carryRemainderPairs hgood length).map (fun pair => pair.1.blockValue) =
      C.normalizedRawWord hgood length := by
  calc
    (C.carryRemainderPairs hgood length).map (fun pair => pair.1.blockValue)
      = ((C.carryRemainderPairs hgood length).map Prod.fst).map CarryTraceStep.blockValue := by
          simp
    _ = (C.traceRawWord hgood length).map CarryTraceStep.blockValue := by
          rw [C.carryRemainderPairs_map_carryStep]
    _ = C.normalizedRawWord hgood length := C.traceRawWord_map_blockValue hgood length

theorem BlockCoordinate.carryRemainderPairs_map_carryOut
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.carryRemainderPairs hgood length).map (fun pair => pair.1.carryOut) =
      (C.traceRawWord hgood length).map CarryTraceStep.carryOut := by
  calc
    (C.carryRemainderPairs hgood length).map (fun pair => pair.1.carryOut)
      = ((C.carryRemainderPairs hgood length).map Prod.fst).map CarryTraceStep.carryOut := by
          simp
    _ = (C.traceRawWord hgood length).map CarryTraceStep.carryOut := by
          rw [C.carryRemainderPairs_map_carryStep]

theorem BlockCoordinate.carryRemainderPairs_map_remainderIn
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.carryRemainderPairs hgood length).map (fun pair => pair.2.remainderIn) =
      (List.range length).map C.longDivisionRemainder := by
  calc
    (C.carryRemainderPairs hgood length).map (fun pair => pair.2.remainderIn)
      = ((C.carryRemainderPairs hgood length).map Prod.snd).map RemainderTraceStep.remainderIn := by
          simp
    _ = (C.remainderTrace length).map RemainderTraceStep.remainderIn := by
          rw [C.carryRemainderPairs_map_remainderStep]
    _ = (List.range length).map C.longDivisionRemainder := C.remainderTrace_map_remainderIn length

theorem BlockCoordinate.carryRemainderPairs_map_remainderBlockValue
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.carryRemainderPairs hgood length).map (fun pair => pair.2.blockValue) =
      C.emittedBlockWord length := by
  calc
    (C.carryRemainderPairs hgood length).map (fun pair => pair.2.blockValue)
      = ((C.carryRemainderPairs hgood length).map Prod.snd).map RemainderTraceStep.blockValue := by
          simp
    _ = (C.remainderTrace length).map RemainderTraceStep.blockValue := by
          rw [C.carryRemainderPairs_map_remainderStep]
    _ = C.emittedBlockWord length := C.remainderTrace_map_blockValue length

theorem BlockCoordinate.carryRemainderPairs_map_remainderOut
    (C : BlockCoordinate) (hgood : C.goodMode) (length : ℕ) :
    (C.carryRemainderPairs hgood length).map (fun pair => pair.2.remainderOut) =
      (List.range length).map (fun j => C.longDivisionRemainder (j + 1)) := by
  calc
    (C.carryRemainderPairs hgood length).map (fun pair => pair.2.remainderOut)
      = ((C.carryRemainderPairs hgood length).map Prod.snd).map RemainderTraceStep.remainderOut := by
          simp
    _ = (C.remainderTrace length).map RemainderTraceStep.remainderOut := by
          rw [C.carryRemainderPairs_map_remainderStep]
    _ = (List.range length).map (fun j => C.longDivisionRemainder (j + 1)) :=
          C.remainderTrace_map_remainderOut length

theorem BlockCoordinate.carryRemainderPairs_output_agreement_of_remainderK_pow_lt_modulus
    (C : BlockCoordinate) (hgood : C.goodMode) (hmod : 1 < C.modulus)
    (length : ℕ) (hsmall : C.remainderK ^ length < C.modulus) :
    (C.carryRemainderPairs hgood length).map (fun pair => pair.1.blockValue) =
      (C.carryRemainderPairs hgood length).map (fun pair => pair.2.blockValue) := by
  rw [C.carryRemainderPairs_map_carryBlockValue, C.carryRemainderPairs_map_remainderBlockValue]
  exact C.normalizedRawWord_eq_emittedBlockWord_of_remainderK_pow_lt_modulus hgood hmod length hsmall

section Examples

example : prime97Stride2.rawCoefficientWord 6 = [1, 3, 9, 27, 81, 243] := by native_decide
example : prime37Stride3.rawCoefficientWord 4 = [27, 27, 27, 27] := by native_decide
example :
    prime37Stride3.normalizedRawWord (by
      show 37 < 10 ^ 3
      native_decide) 4 = [27, 27, 27, 27] := by
  native_decide
example :
    (prime97Stride2.traceRawWord (by
      show 97 < 10 ^ 2
      native_decide) 6).map CarryTraceStep.blockValue = [1, 3, 9, 27, 83, 43] := by
  native_decide
example : prime97Stride2.emittedBlockWord 6 = [1, 3, 9, 27, 83, 50] := by native_decide

end Examples

end QRTour
