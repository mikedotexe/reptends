/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.CarryComparison

/-!
# Restricted Orbit-to-Carry Factorization

This module packages a deliberately modest finite-window notion beneath the
open claim `carry_dfa_factorization`.

For one fixed block coordinate and one fixed visible comparison window, the
aligned state records already let us ask whether the observed remainder orbit
defines a functional map into carry states. We record that as a finite graph
criterion:

- `remainderIn ↦ (carryIn, carryOut)` for the forward orbit-to-carry direction
- `carryIn ↦ (remainderIn, remainderOut)` for the reverse direction

The forward interface is the positive candidate surface. The reverse interface
is included because the canonical `97` and `996` windows fail there, and those
failures are the honest obstruction story beneath the still-open global claim.
-/

namespace QRTour

/-- The observed finite step graph from remainder states to carry states on one
visible comparison window. -/
def BlockCoordinate.remainderToCarryStepGraph
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) : List (ℕ × (ℕ × ℕ)) :=
  (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map
    (fun alignment => (alignment.remainderIn, (alignment.carryIn, alignment.carryOut)))

/-- The observed finite step graph from carry states back to remainder states
on one visible comparison window. -/
def BlockCoordinate.carryToRemainderStepGraph
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) : List (ℕ × (ℕ × ℕ)) :=
  (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map
    (fun alignment => (alignment.carryIn, (alignment.remainderIn, alignment.remainderOut)))

/-- A restricted remainder-to-carry morphism on one fixed visible window.

This is intentionally finite-window and coordinate-level: the aligned outputs
agree, and the observed remainder states determine the carry step data on that
window. -/
structure RestrictedRemainderToCarryMorphism
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) where
  outputAgreement :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.carryBlockValue =
      (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.remainderBlockValue
  stepFunctional :
    List.FunctionalOnFst (C.remainderToCarryStepGraph hgood requestedBlocks lookaheadBlocks)

/-- The reverse finite-window interface. We do not treat this as the primary
theorem candidate, but it is the right surface for the canonical obstructions. -/
structure RestrictedCarryToRemainderMorphism
    (C : BlockCoordinate) (hgood : C.goodMode)
    (requestedBlocks lookaheadBlocks : ℕ) where
  outputAgreement :
    (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.carryBlockValue =
      (C.stateAlignments hgood requestedBlocks lookaheadBlocks).map StateAlignment.remainderBlockValue
  stepFunctional :
    List.FunctionalOnFst (C.carryToRemainderStepGraph hgood requestedBlocks lookaheadBlocks)

theorem RestrictedRemainderToCarryMorphism.same_remainderIn_implies_same_step
    {C : BlockCoordinate} {hgood : C.goodMode}
    {requestedBlocks lookaheadBlocks : ℕ}
    (M : RestrictedRemainderToCarryMorphism C hgood requestedBlocks lookaheadBlocks)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (j : ℕ) (hj : j < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (hstate :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderIn) :
    (((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryIn,
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryOut) =
      (((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryIn,
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryOut) := by
  exact
    C.stateAlignments_same_remainderIn_implies_same_projection_of_functionalOnFst
      hgood requestedBlocks lookaheadBlocks
      (fun alignment => (alignment.carryIn, alignment.carryOut))
      (by simpa [BlockCoordinate.remainderToCarryStepGraph] using M.stepFunctional)
      i hi j hj hstate

theorem RestrictedRemainderToCarryMorphism.remainderToCarryFunctional
    {C : BlockCoordinate} {hgood : C.goodMode}
    {requestedBlocks lookaheadBlocks : ℕ}
    (M : RestrictedRemainderToCarryMorphism C hgood requestedBlocks lookaheadBlocks) :
    C.remainderToCarryFunctional hgood requestedBlocks lookaheadBlocks := by
  intro i hi j hj hstate
  exact congrArg Prod.fst (M.same_remainderIn_implies_same_step i hi j hj hstate)

theorem RestrictedCarryToRemainderMorphism.same_carryIn_implies_same_step
    {C : BlockCoordinate} {hgood : C.goodMode}
    {requestedBlocks lookaheadBlocks : ℕ}
    (M : RestrictedCarryToRemainderMorphism C hgood requestedBlocks lookaheadBlocks)
    (i : ℕ) (hi : i < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (j : ℕ) (hj : j < (C.stateAlignments hgood requestedBlocks lookaheadBlocks).length)
    (hcarry :
      ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).carryIn =
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).carryIn) :
    (((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderIn,
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[i]'hi).remainderOut) =
      (((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderIn,
        ((C.stateAlignments hgood requestedBlocks lookaheadBlocks)[j]'hj).remainderOut) := by
  exact
    C.stateAlignments_same_carryIn_implies_same_projection_of_functionalOnFst
      hgood requestedBlocks lookaheadBlocks
      (fun alignment => (alignment.remainderIn, alignment.remainderOut))
      (by simpa [BlockCoordinate.carryToRemainderStepGraph] using M.stepFunctional)
      i hi j hj hcarry

theorem RestrictedCarryToRemainderMorphism.carryToRemainderFunctional
    {C : BlockCoordinate} {hgood : C.goodMode}
    {requestedBlocks lookaheadBlocks : ℕ}
    (M : RestrictedCarryToRemainderMorphism C hgood requestedBlocks lookaheadBlocks) :
    C.carryToRemainderFunctional hgood requestedBlocks lookaheadBlocks := by
  intro i hi j hj hcarry
  exact congrArg Prod.fst (M.same_carryIn_implies_same_step i hi j hj hcarry)

/-! ## Canonical finite-window witnesses -/

/-- The canonical `21` window is the trivial relabeling case: the forward
finite-window remainder-to-carry morphism exists on `8/0`. -/
def twentyOneStride6_remainderToCarryMorphism_8_0 :
    RestrictedRemainderToCarryMorphism twentyOneStride6 twentyOneStride6_goodMode 8 0 where
  outputAgreement := by
    native_decide
  stepFunctional := by
    native_decide

/-- On the same `21` window, the reverse finite-window map also exists. This is
the one-state relabeling witness. -/
def twentyOneStride6_carryToRemainderMorphism_8_0 :
    RestrictedCarryToRemainderMorphism twentyOneStride6 twentyOneStride6_goodMode 8 0 where
  outputAgreement := by
    native_decide
  stepFunctional := by
    native_decide

/-- The canonical `97` quotient-only witness: on the `8/2` window, the
remainder orbit still determines the carry step data. -/
def prime97Stride2_remainderToCarryMorphism_8_2 :
    RestrictedRemainderToCarryMorphism prime97Stride2 prime97Stride2_goodMode 8 2 where
  outputAgreement := by
    native_decide
  stepFunctional := by
    native_decide

/-- But the same `97` window does not support the reverse finite-window map. -/
theorem prime97Stride2_not_carryToRemainderMorphism_8_2 :
    ¬ RestrictedCarryToRemainderMorphism prime97Stride2 prime97Stride2_goodMode 8 2 := by
  intro M
  have hnot : ¬ prime97Stride2.carryToRemainderFunctional prime97Stride2_goodMode 8 2 := by
    rw [prime97Stride2.carryToRemainderFunctional_iff_functionalOnFst_pairs]
    native_decide
  exact hnot M.carryToRemainderFunctional

/-- The canonical `996` window still admits the forward finite-window map on
the larger quotient-only selector witness `8/1`. -/
def composite996Stride3_remainderToCarryMorphism_8_1 :
    RestrictedRemainderToCarryMorphism composite996Stride3 composite996Stride3_goodMode 8 1 where
  outputAgreement := by
    native_decide
  stepFunctional := by
    native_decide

/-- On the same larger `996` window, the reverse map still fails. This is the
quotient-only obstruction in the composite/preperiod setting. -/
theorem composite996Stride3_not_carryToRemainderMorphism_8_1 :
    ¬ RestrictedCarryToRemainderMorphism composite996Stride3 composite996Stride3_goodMode 8 1 := by
  intro M
  have hnot : ¬ composite996Stride3.carryToRemainderFunctional composite996Stride3_goodMode 8 1 := by
    rw [composite996Stride3.carryToRemainderFunctional_iff_functionalOnFst_pairs]
    native_decide
  exact hnot M.carryToRemainderFunctional

/-- The stripped core `249` still supports the reverse map on the exact
one-block `1/0` window used in the same-core obstruction story. -/
def composite996Core249Stride3_carryToRemainderMorphism_1_0 :
    RestrictedCarryToRemainderMorphism
      composite996Core249Stride3 composite996Core249Stride3_goodMode 1 0 where
  outputAgreement := by
    native_decide
  stepFunctional := by
    native_decide

/-- The shifted actual `996` window already loses the reverse map on `2/0`. -/
theorem composite996Stride3_not_carryToRemainderMorphism_2_0 :
    ¬ RestrictedCarryToRemainderMorphism composite996Stride3 composite996Stride3_goodMode 2 0 := by
  intro M
  have hnot : ¬ composite996Stride3.carryToRemainderFunctional composite996Stride3_goodMode 2 0 := by
    exact composite996Stride3_not_carryToRemainderFunctional_two_zero
  exact hnot M.carryToRemainderFunctional

/-- The exact `996 over 249` same-core pair is therefore a direct obstruction:
the stripped core has a reverse `1/0` morphism, while the shifted actual
window already fails on `2/0`. -/
theorem composite996_sameCore_carryToRemainder_counterexample :
    RestrictedCarryToRemainderMorphism
        composite996Core249Stride3 composite996Core249Stride3_goodMode 1 0 ∧
      ¬ RestrictedCarryToRemainderMorphism
        composite996Stride3 composite996Stride3_goodMode 2 0 := by
  exact ⟨composite996Core249Stride3_carryToRemainderMorphism_1_0,
    composite996Stride3_not_carryToRemainderMorphism_2_0⟩

end QRTour
