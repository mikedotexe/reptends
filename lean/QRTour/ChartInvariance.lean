/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.Factorization
import GeometricStack.Positional

/-!
# Finite Chart-Invariance Vocabulary

This module gives the Visibility Geometry / Instrument Atlas language a small
Lean landing pad. It does not prove a global chart-invariance theorem. Instead,
it defines finite signatures and the four elementary classifications used by
the empirical `chart-invariance` search surface:

- clean chart invariance,
- absorption-stable signal,
- clean chart distortion, and
- absorption-shift distortion.

The definitions are deliberately finite and syntactic. They make it possible to
state future theorem targets about base/block instruments without promoting the
open `small_k_visibility_threshold` or `carry_dfa_factorization` frontiers.
-/

namespace QRTour

/-- Finite visibility classes used by the empirical Visibility Optics and
chart-invariance search surfaces. These are labels for bounded observations,
not theorem-level global regimes. -/
inductive VisibilitySignalClass where
  | transparentWindow
  | earlyCarryIntrusion
  | visibleStateCompression
  | hiddenGraphObstruction
  | sameCoreDrift
  deriving DecidableEq, Repr

/-- Optional finite state-map regime labels, matching the bounded
carry/remainder comparison surfaces. These are finite annotations, not a global
factorization theorem. -/
inductive StateMapFactorizationRegime where
  | stateRelabeling
  | quotientCandidateOnly
  deriving DecidableEq, Repr

/-- Optional finite state-map obstruction labels used by selected chart
observations. -/
inductive StateMapObstructionClass where
  | stateRelabeling
  | visiblePreimageCompression
  | hiddenGraphObstruction
  deriving DecidableEq, Repr

/-- A finite signature for one base/block chart on one observed denominator.

The fields are intentionally the small common vocabulary needed for
chart-invariance classification:

- `base`: the radix of the chart,
- `blockWidth`: the block length,
- `blockBase`: the resulting block base,
- `periodicModulus`: the stripped periodic modulus seen by the chart, and
- `signalClass`: the finite-window visibility class observed in that chart.
-/
structure ChartSignature where
  base : ℕ
  blockWidth : ℕ
  blockBase : ℕ
  periodicModulus : ℕ
  signalClass : VisibilitySignalClass
  deriving DecidableEq, Repr

/-- A finite chart observation carries the row-level evidence behind a chart
signature.

This is still bounded data: it records the selected denominator, base/block
coordinate, Euclidean `B = qN + k` fields, finite raw-prefix and carry
positions, optional state-map labels, and the finite signal class assigned to
that observed window. The theorem-level boundary remains unchanged: these
fields do not assert a global visibility or carry-factorization theorem. -/
structure ChartObservation where
  denominator : ℕ
  base : ℕ
  blockWidth : ℕ
  blockBase : ℕ
  quotientQ : ℕ
  remainderK : ℕ
  periodicModulus : ℕ
  requestedBlocks : ℕ
  rawPrefixAgreementLength : ℕ
  firstIncomingCarryPosition : Option ℕ
  firstLocalOverflowPosition : Option ℕ
  stateMapRegime : Option StateMapFactorizationRegime
  obstructionClass : Option StateMapObstructionClass
  signalClass : VisibilitySignalClass
  deriving DecidableEq, Repr

namespace ChartObservation

/-- Project a finite observation to the smaller chart signature used for
chart-pair classification. -/
def toSignature (observation : ChartObservation) : ChartSignature :=
  { base := observation.base
    blockWidth := observation.blockWidth
    blockBase := observation.blockBase
    periodicModulus := observation.periodicModulus
    signalClass := observation.signalClass }

/-- Build a finite observation from a denominator and a selected base/block
instrument. The arithmetic coordinate fields are computed, while the finite
visibility/state labels remain supplied observations. -/
def ofDenominator
    (base n blockWidth requestedBlocks rawPrefixAgreementLength : ℕ)
    (firstIncomingCarryPosition firstLocalOverflowPosition : Option ℕ)
    (stateMapRegime : Option StateMapFactorizationRegime)
    (obstructionClass : Option StateMapObstructionClass)
    (signalClass : VisibilitySignalClass) : ChartObservation :=
  { denominator := n
    base := base
    blockWidth := blockWidth
    blockBase := base ^ blockWidth
    quotientQ := (base ^ blockWidth) / n
    remainderK := (base ^ blockWidth) % n
    periodicModulus := strippedPeriodModulus base n
    requestedBlocks := requestedBlocks
    rawPrefixAgreementLength := rawPrefixAgreementLength
    firstIncomingCarryPosition := firstIncomingCarryPosition
    firstLocalOverflowPosition := firstLocalOverflowPosition
    stateMapRegime := stateMapRegime
    obstructionClass := obstructionClass
    signalClass := signalClass }

/-- Finite evidence for a fully transparent requested window. -/
def hasTransparentWindowEvidence (observation : ChartObservation) : Bool :=
  decide (observation.requestedBlocks ≤ observation.rawPrefixAgreementLength)

/-- Finite evidence that an incoming carry reaches a visible position before
the local raw coefficient overflows. If no local overflow appears in the
observed window, any incoming carry counts as earlier than local overflow. -/
def hasEarlyCarryIntrusionEvidence (observation : ChartObservation) : Bool :=
  match observation.firstIncomingCarryPosition with
  | none => false
  | some incoming =>
      match observation.firstLocalOverflowPosition with
      | none => true
      | some overflow => decide (incoming < overflow)

/-- Whether the finite observation carries a state-map signal annotation whose
derivation belongs to the carry-factorization boundary rather than the simple
raw-prefix/carry-position classifier. -/
def hasStateMapSignalAnnotation (observation : ChartObservation) : Bool :=
  match observation.obstructionClass with
  | some .visiblePreimageCompression => true
  | some .hiddenGraphObstruction => true
  | _ => false

/-- Conservative finite classifier derived only from row fields already present
on `ChartObservation`.

State-map compression and hidden-obstruction labels intentionally return
`none`: those are finite annotations beneath the open
`carry_dfa_factorization` boundary, not classes derived by this simple
raw-prefix/carry-position classifier. -/
def derivedSignalClass? (observation : ChartObservation) :
    Option VisibilitySignalClass :=
  if observation.hasStateMapSignalAnnotation then
    none
  else if observation.hasTransparentWindowEvidence then
    some .transparentWindow
  else if observation.hasEarlyCarryIntrusionEvidence then
    some .earlyCarryIntrusion
  else
    none

/-- Whether the conservative derived class agrees with the supplied finite
signal label. Unsupported state-map labels therefore return `false`. -/
def derivedSignalAgrees (observation : ChartObservation) : Bool :=
  observation.derivedSignalClass? == some observation.signalClass

/-- Count finite observations satisfying a decidable Boolean predicate. -/
def countBy (predicate : ChartObservation → Bool) :
    List ChartObservation → ℕ
  | [] => 0
  | observation :: observations =>
      (if predicate observation then 1 else 0) + countBy predicate observations

@[simp] theorem toSignature_base (observation : ChartObservation) :
    observation.toSignature.base = observation.base := rfl

@[simp] theorem toSignature_blockWidth (observation : ChartObservation) :
    observation.toSignature.blockWidth = observation.blockWidth := rfl

@[simp] theorem toSignature_blockBase (observation : ChartObservation) :
    observation.toSignature.blockBase = observation.blockBase := rfl

@[simp] theorem toSignature_periodicModulus (observation : ChartObservation) :
    observation.toSignature.periodicModulus = observation.periodicModulus := rfl

@[simp] theorem toSignature_signalClass (observation : ChartObservation) :
    observation.toSignature.signalClass = observation.signalClass := rfl

@[simp] theorem ofDenominator_denominator
    (base n blockWidth requestedBlocks rawPrefixAgreementLength : ℕ)
    (firstIncomingCarryPosition firstLocalOverflowPosition : Option ℕ)
    (stateMapRegime : Option StateMapFactorizationRegime)
    (obstructionClass : Option StateMapObstructionClass)
    (signalClass : VisibilitySignalClass) :
    (ofDenominator base n blockWidth requestedBlocks rawPrefixAgreementLength
      firstIncomingCarryPosition firstLocalOverflowPosition stateMapRegime
      obstructionClass signalClass).denominator = n := rfl

@[simp] theorem ofDenominator_blockBase
    (base n blockWidth requestedBlocks rawPrefixAgreementLength : ℕ)
    (firstIncomingCarryPosition firstLocalOverflowPosition : Option ℕ)
    (stateMapRegime : Option StateMapFactorizationRegime)
    (obstructionClass : Option StateMapObstructionClass)
    (signalClass : VisibilitySignalClass) :
    (ofDenominator base n blockWidth requestedBlocks rawPrefixAgreementLength
      firstIncomingCarryPosition firstLocalOverflowPosition stateMapRegime
      obstructionClass signalClass).blockBase = base ^ blockWidth := rfl

@[simp] theorem ofDenominator_quotientQ
    (base n blockWidth requestedBlocks rawPrefixAgreementLength : ℕ)
    (firstIncomingCarryPosition firstLocalOverflowPosition : Option ℕ)
    (stateMapRegime : Option StateMapFactorizationRegime)
    (obstructionClass : Option StateMapObstructionClass)
    (signalClass : VisibilitySignalClass) :
    (ofDenominator base n blockWidth requestedBlocks rawPrefixAgreementLength
      firstIncomingCarryPosition firstLocalOverflowPosition stateMapRegime
      obstructionClass signalClass).quotientQ = (base ^ blockWidth) / n := rfl

@[simp] theorem ofDenominator_remainderK
    (base n blockWidth requestedBlocks rawPrefixAgreementLength : ℕ)
    (firstIncomingCarryPosition firstLocalOverflowPosition : Option ℕ)
    (stateMapRegime : Option StateMapFactorizationRegime)
    (obstructionClass : Option StateMapObstructionClass)
    (signalClass : VisibilitySignalClass) :
    (ofDenominator base n blockWidth requestedBlocks rawPrefixAgreementLength
      firstIncomingCarryPosition firstLocalOverflowPosition stateMapRegime
      obstructionClass signalClass).remainderK = (base ^ blockWidth) % n := rfl

@[simp] theorem ofDenominator_periodicModulus
    (base n blockWidth requestedBlocks rawPrefixAgreementLength : ℕ)
    (firstIncomingCarryPosition firstLocalOverflowPosition : Option ℕ)
    (stateMapRegime : Option StateMapFactorizationRegime)
    (obstructionClass : Option StateMapObstructionClass)
    (signalClass : VisibilitySignalClass) :
    (ofDenominator base n blockWidth requestedBlocks rawPrefixAgreementLength
      firstIncomingCarryPosition firstLocalOverflowPosition stateMapRegime
      obstructionClass signalClass).periodicModulus = strippedPeriodModulus base n := rfl

end ChartObservation

/-- Two chart signatures see the same stripped periodic core. -/
def SamePeriodicCore (σ τ : ChartSignature) : Prop :=
  σ.periodicModulus = τ.periodicModulus

/-- Two chart signatures have the same finite-window visibility label. -/
def SameSignalClass (σ τ : ChartSignature) : Prop :=
  σ.signalClass = τ.signalClass

instance instDecidableSamePeriodicCore (σ τ : ChartSignature) :
    Decidable (SamePeriodicCore σ τ) := by
  unfold SamePeriodicCore
  infer_instance

instance instDecidableSameSignalClass (σ τ : ChartSignature) :
    Decidable (SameSignalClass σ τ) := by
  unfold SameSignalClass
  infer_instance

namespace ChartSignature

/-- A finite chart signature from an already chosen block coordinate.

This version records the coordinate modulus directly. Use `ofDenominator` when
the chart should record the stripped periodic modulus after base-supported
factors have been absorbed. -/
def ofBlockCoordinate (C : BlockCoordinate)
    (signalClass : VisibilitySignalClass) : ChartSignature :=
  { base := C.base
    blockWidth := C.stride
    blockBase := C.blockBase
    periodicModulus := C.modulus
    signalClass := signalClass }

@[simp] theorem ofBlockCoordinate_base
    (C : BlockCoordinate) (signalClass : VisibilitySignalClass) :
    (ofBlockCoordinate C signalClass).base = C.base := rfl

@[simp] theorem ofBlockCoordinate_blockWidth
    (C : BlockCoordinate) (signalClass : VisibilitySignalClass) :
    (ofBlockCoordinate C signalClass).blockWidth = C.stride := rfl

@[simp] theorem ofBlockCoordinate_blockBase
    (C : BlockCoordinate) (signalClass : VisibilitySignalClass) :
    (ofBlockCoordinate C signalClass).blockBase = C.blockBase := rfl

@[simp] theorem ofBlockCoordinate_periodicModulus
    (C : BlockCoordinate) (signalClass : VisibilitySignalClass) :
    (ofBlockCoordinate C signalClass).periodicModulus = C.modulus := rfl

@[simp] theorem ofBlockCoordinate_signalClass
    (C : BlockCoordinate) (signalClass : VisibilitySignalClass) :
    (ofBlockCoordinate C signalClass).signalClass = signalClass := rfl

/-- A finite chart signature from a denominator and a base/block instrument.

The periodic modulus field uses `strippedPeriodModulus`, matching the empirical
chart-invariance and Instrument Atlas surfaces: base-supported factors belong
to the instrument/preperiod layer, while this field records the periodic core
seen after that absorption. -/
def ofDenominator (base n blockWidth : ℕ)
    (signalClass : VisibilitySignalClass) : ChartSignature :=
  { base := base
    blockWidth := blockWidth
    blockBase := base ^ blockWidth
    periodicModulus := strippedPeriodModulus base n
    signalClass := signalClass }

@[simp] theorem ofDenominator_base
    (base n blockWidth : ℕ) (signalClass : VisibilitySignalClass) :
    (ofDenominator base n blockWidth signalClass).base = base := rfl

@[simp] theorem ofDenominator_blockWidth
    (base n blockWidth : ℕ) (signalClass : VisibilitySignalClass) :
    (ofDenominator base n blockWidth signalClass).blockWidth = blockWidth := rfl

@[simp] theorem ofDenominator_blockBase
    (base n blockWidth : ℕ) (signalClass : VisibilitySignalClass) :
    (ofDenominator base n blockWidth signalClass).blockBase = base ^ blockWidth := rfl

@[simp] theorem ofDenominator_periodicModulus
    (base n blockWidth : ℕ) (signalClass : VisibilitySignalClass) :
    (ofDenominator base n blockWidth signalClass).periodicModulus =
      strippedPeriodModulus base n := rfl

@[simp] theorem ofDenominator_signalClass
    (base n blockWidth : ℕ) (signalClass : VisibilitySignalClass) :
    (ofDenominator base n blockWidth signalClass).signalClass = signalClass := rfl

theorem samePeriodicCore_ofDenominator_iff
    {baseLeft nLeft blockWidthLeft baseRight nRight blockWidthRight : ℕ}
    {signalClassLeft signalClassRight : VisibilitySignalClass} :
    SamePeriodicCore
        (ofDenominator baseLeft nLeft blockWidthLeft signalClassLeft)
        (ofDenominator baseRight nRight blockWidthRight signalClassRight) ↔
      strippedPeriodModulus baseLeft nLeft =
        strippedPeriodModulus baseRight nRight := by
  rfl

theorem sameSignalClass_ofDenominator_iff
    {baseLeft nLeft blockWidthLeft baseRight nRight blockWidthRight : ℕ}
    {signalClassLeft signalClassRight : VisibilitySignalClass} :
    SameSignalClass
        (ofDenominator baseLeft nLeft blockWidthLeft signalClassLeft)
        (ofDenominator baseRight nRight blockWidthRight signalClassRight) ↔
      signalClassLeft = signalClassRight := by
  rfl

end ChartSignature

theorem ChartObservation.toSignature_ofDenominator
    (base n blockWidth requestedBlocks rawPrefixAgreementLength : ℕ)
    (firstIncomingCarryPosition firstLocalOverflowPosition : Option ℕ)
    (stateMapRegime : Option StateMapFactorizationRegime)
    (obstructionClass : Option StateMapObstructionClass)
    (signalClass : VisibilitySignalClass) :
    (ChartObservation.ofDenominator base n blockWidth requestedBlocks
      rawPrefixAgreementLength firstIncomingCarryPosition firstLocalOverflowPosition
      stateMapRegime obstructionClass signalClass).toSignature =
        ChartSignature.ofDenominator base n blockWidth signalClass := rfl

/-- The clean invariant case: same periodic core and same finite-window signal. -/
def CleanChartInvariant (σ τ : ChartSignature) : Prop :=
  SamePeriodicCore σ τ ∧ SameSignalClass σ τ

/-- The signal survives even though the stripped periodic core changes. -/
def AbsorptionStableSignal (σ τ : ChartSignature) : Prop :=
  ¬ SamePeriodicCore σ τ ∧ SameSignalClass σ τ

/-- Clean distortion: the periodic core is fixed, but the visibility signal changes. -/
def CleanChartDistortion (σ τ : ChartSignature) : Prop :=
  SamePeriodicCore σ τ ∧ ¬ SameSignalClass σ τ

/-- Distortion with absorption: both the periodic core and the signal change. -/
def AbsorptionShiftDistortion (σ τ : ChartSignature) : Prop :=
  ¬ SamePeriodicCore σ τ ∧ ¬ SameSignalClass σ τ

instance instDecidableCleanChartInvariant (σ τ : ChartSignature) :
    Decidable (CleanChartInvariant σ τ) := by
  unfold CleanChartInvariant
  infer_instance

instance instDecidableAbsorptionStableSignal (σ τ : ChartSignature) :
    Decidable (AbsorptionStableSignal σ τ) := by
  unfold AbsorptionStableSignal
  infer_instance

instance instDecidableCleanChartDistortion (σ τ : ChartSignature) :
    Decidable (CleanChartDistortion σ τ) := by
  unfold CleanChartDistortion
  infer_instance

instance instDecidableAbsorptionShiftDistortion (σ τ : ChartSignature) :
    Decidable (AbsorptionShiftDistortion σ τ) := by
  unfold AbsorptionShiftDistortion
  infer_instance

/-- The four-way finite chart classification. -/
inductive ChartInvarianceClass where
  | cleanChartInvariant
  | absorptionStableSignal
  | cleanChartDistortion
  | absorptionShiftDistortion
  deriving DecidableEq, Repr

namespace ChartInvarianceClass

/-- Whether a finite chart class preserves the signal class. -/
def isInvariant : ChartInvarianceClass → Bool
  | cleanChartInvariant => true
  | absorptionStableSignal => true
  | cleanChartDistortion => false
  | absorptionShiftDistortion => false

/-- Whether a finite chart class changes the signal class. -/
def isDistortion : ChartInvarianceClass → Bool
  | cleanChartInvariant => false
  | absorptionStableSignal => false
  | cleanChartDistortion => true
  | absorptionShiftDistortion => true

/-- Whether a finite chart class preserves the stripped periodic core. -/
def isCleanCore : ChartInvarianceClass → Bool
  | cleanChartInvariant => true
  | absorptionStableSignal => false
  | cleanChartDistortion => true
  | absorptionShiftDistortion => false

/-- Whether a finite chart class changes the stripped periodic core. -/
def isAbsorptionShift : ChartInvarianceClass → Bool
  | cleanChartInvariant => false
  | absorptionStableSignal => true
  | cleanChartDistortion => false
  | absorptionShiftDistortion => true

/-- Classify two finite chart signatures by whether their periodic cores and
finite-window signal classes agree. -/
def ofSignatures (σ τ : ChartSignature) : ChartInvarianceClass :=
  if SamePeriodicCore σ τ then
    if SameSignalClass σ τ then
      cleanChartInvariant
    else
      cleanChartDistortion
  else
    if SameSignalClass σ τ then
      absorptionStableSignal
    else
      absorptionShiftDistortion

theorem ofSignatures_eq_cleanChartInvariant_iff
    (σ τ : ChartSignature) :
    ofSignatures σ τ = cleanChartInvariant ↔ CleanChartInvariant σ τ := by
  unfold ofSignatures CleanChartInvariant
  by_cases hcore : SamePeriodicCore σ τ
  · by_cases hsignal : SameSignalClass σ τ
    · simp [hcore, hsignal]
    · simp [hcore, hsignal]
  · by_cases hsignal : SameSignalClass σ τ
    · simp [hcore, hsignal]
    · simp [hcore, hsignal]

theorem ofSignatures_eq_absorptionStableSignal_iff
    (σ τ : ChartSignature) :
    ofSignatures σ τ = absorptionStableSignal ↔ AbsorptionStableSignal σ τ := by
  unfold ofSignatures AbsorptionStableSignal
  by_cases hcore : SamePeriodicCore σ τ
  · by_cases hsignal : SameSignalClass σ τ
    · simp [hcore, hsignal]
    · simp [hcore, hsignal]
  · by_cases hsignal : SameSignalClass σ τ
    · simp [hcore, hsignal]
    · simp [hcore, hsignal]

theorem ofSignatures_eq_cleanChartDistortion_iff
    (σ τ : ChartSignature) :
    ofSignatures σ τ = cleanChartDistortion ↔ CleanChartDistortion σ τ := by
  unfold ofSignatures CleanChartDistortion
  by_cases hcore : SamePeriodicCore σ τ
  · by_cases hsignal : SameSignalClass σ τ
    · simp [hcore, hsignal]
    · simp [hcore, hsignal]
  · by_cases hsignal : SameSignalClass σ τ
    · simp [hcore, hsignal]
    · simp [hcore, hsignal]

theorem ofSignatures_eq_absorptionShiftDistortion_iff
    (σ τ : ChartSignature) :
    ofSignatures σ τ = absorptionShiftDistortion ↔ AbsorptionShiftDistortion σ τ := by
  unfold ofSignatures AbsorptionShiftDistortion
  by_cases hcore : SamePeriodicCore σ τ
  · by_cases hsignal : SameSignalClass σ τ
    · simp [hcore, hsignal]
    · simp [hcore, hsignal]
  · by_cases hsignal : SameSignalClass σ τ
    · simp [hcore, hsignal]
    · simp [hcore, hsignal]

end ChartInvarianceClass

/-- A finite witness that two selected chart signatures have a certified chart
classification.

This is the right Lean shape for empirical chart-pair examples: the witness
records the chosen finite signatures and proves only that the syntactic
four-way classifier assigns the stated finite class. It does not prove that the
signal labels themselves are globally derived visibility regimes. -/
structure ChartPairWitness where
  left : ChartSignature
  right : ChartSignature
  classification : ChartInvarianceClass
  certified : ChartInvarianceClass.ofSignatures left right = classification

namespace ChartPairWitness

/-- Package any two finite signatures with their computed classification. -/
def ofSignatures (left right : ChartSignature) : ChartPairWitness :=
  { left := left
    right := right
    classification := ChartInvarianceClass.ofSignatures left right
    certified := rfl }

@[simp] theorem ofSignatures_left (left right : ChartSignature) :
    (ofSignatures left right).left = left := rfl

@[simp] theorem ofSignatures_right (left right : ChartSignature) :
    (ofSignatures left right).right = right := rfl

@[simp] theorem ofSignatures_classification (left right : ChartSignature) :
    (ofSignatures left right).classification =
      ChartInvarianceClass.ofSignatures left right := rfl

/-- The base pair represented by this finite witness. -/
def hasBasePair (W : ChartPairWitness) (leftBase rightBase : ℕ) : Bool :=
  W.left.base == leftBase && W.right.base == rightBase

/-- Whether this witness has the selected finite chart classification. -/
def hasClassification (W : ChartPairWitness) (classification : ChartInvarianceClass) :
    Bool :=
  W.classification == classification

/-- Whether this witness preserves the finite signal class. -/
def isInvariant (W : ChartPairWitness) : Bool :=
  W.classification.isInvariant

/-- Whether this witness changes the finite signal class. -/
def isDistortion (W : ChartPairWitness) : Bool :=
  W.classification.isDistortion

/-- Whether this witness preserves the stripped periodic core. -/
def isCleanCore (W : ChartPairWitness) : Bool :=
  W.classification.isCleanCore

/-- Whether this witness changes the stripped periodic core. -/
def isAbsorptionShift (W : ChartPairWitness) : Bool :=
  W.classification.isAbsorptionShift

theorem cleanChartInvariant_of_classification_eq
    (W : ChartPairWitness)
    (h : W.classification = ChartInvarianceClass.cleanChartInvariant) :
    CleanChartInvariant W.left W.right := by
  have hclass :
      ChartInvarianceClass.ofSignatures W.left W.right =
        ChartInvarianceClass.cleanChartInvariant := by
    simpa [h] using W.certified
  exact
    (ChartInvarianceClass.ofSignatures_eq_cleanChartInvariant_iff W.left W.right).mp hclass

theorem absorptionStableSignal_of_classification_eq
    (W : ChartPairWitness)
    (h : W.classification = ChartInvarianceClass.absorptionStableSignal) :
    AbsorptionStableSignal W.left W.right := by
  have hclass :
      ChartInvarianceClass.ofSignatures W.left W.right =
        ChartInvarianceClass.absorptionStableSignal := by
    simpa [h] using W.certified
  exact
    (ChartInvarianceClass.ofSignatures_eq_absorptionStableSignal_iff W.left W.right).mp hclass

theorem cleanChartDistortion_of_classification_eq
    (W : ChartPairWitness)
    (h : W.classification = ChartInvarianceClass.cleanChartDistortion) :
    CleanChartDistortion W.left W.right := by
  have hclass :
      ChartInvarianceClass.ofSignatures W.left W.right =
        ChartInvarianceClass.cleanChartDistortion := by
    simpa [h] using W.certified
  exact
    (ChartInvarianceClass.ofSignatures_eq_cleanChartDistortion_iff W.left W.right).mp hclass

theorem absorptionShiftDistortion_of_classification_eq
    (W : ChartPairWitness)
    (h : W.classification = ChartInvarianceClass.absorptionShiftDistortion) :
    AbsorptionShiftDistortion W.left W.right := by
  have hclass :
      ChartInvarianceClass.ofSignatures W.left W.right =
        ChartInvarianceClass.absorptionShiftDistortion := by
    simpa [h] using W.certified
  exact
    (ChartInvarianceClass.ofSignatures_eq_absorptionShiftDistortion_iff W.left W.right).mp hclass

end ChartPairWitness

/-- Count finite witnesses satisfying a decidable Boolean predicate. This keeps
the compact example audit independent of any larger search machinery. -/
def countWitnessesBy (predicate : ChartPairWitness → Bool) :
    List ChartPairWitness → ℕ
  | [] => 0
  | witness :: witnesses =>
      (if predicate witness then 1 else 0) + countWitnessesBy predicate witnesses

def countWitnessesForBasePair
    (leftBase rightBase : ℕ) (witnesses : List ChartPairWitness) : ℕ :=
  countWitnessesBy
    (fun witness => witness.hasBasePair leftBase rightBase)
    witnesses

def countWitnessesForBasePairWithClass
    (leftBase rightBase : ℕ) (classification : ChartInvarianceClass)
    (witnesses : List ChartPairWitness) : ℕ :=
  countWitnessesBy
    (fun witness =>
      witness.hasBasePair leftBase rightBase &&
        witness.hasClassification classification)
    witnesses

def countInvariantWitnessesForBasePair
    (leftBase rightBase : ℕ) (witnesses : List ChartPairWitness) : ℕ :=
  countWitnessesBy
    (fun witness => witness.hasBasePair leftBase rightBase && witness.isInvariant)
    witnesses

def countDistortionWitnessesForBasePair
    (leftBase rightBase : ℕ) (witnesses : List ChartPairWitness) : ℕ :=
  countWitnessesBy
    (fun witness => witness.hasBasePair leftBase rightBase && witness.isDistortion)
    witnesses

theorem chart_classification_exhaustive (σ τ : ChartSignature) :
    CleanChartInvariant σ τ ∨
      AbsorptionStableSignal σ τ ∨
      CleanChartDistortion σ τ ∨
      AbsorptionShiftDistortion σ τ := by
  by_cases hcore : SamePeriodicCore σ τ
  · by_cases hsignal : SameSignalClass σ τ
    · exact Or.inl ⟨hcore, hsignal⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hcore, hsignal⟩))
  · by_cases hsignal : SameSignalClass σ τ
    · exact Or.inr (Or.inl ⟨hcore, hsignal⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hcore, hsignal⟩))

theorem cleanChartInvariant_samePeriodicCore
    {σ τ : ChartSignature} (h : CleanChartInvariant σ τ) :
    SamePeriodicCore σ τ :=
  h.1

theorem cleanChartInvariant_sameSignalClass
    {σ τ : ChartSignature} (h : CleanChartInvariant σ τ) :
    SameSignalClass σ τ :=
  h.2

theorem absorptionStableSignal_not_samePeriodicCore
    {σ τ : ChartSignature} (h : AbsorptionStableSignal σ τ) :
    ¬ SamePeriodicCore σ τ :=
  h.1

theorem absorptionStableSignal_sameSignalClass
    {σ τ : ChartSignature} (h : AbsorptionStableSignal σ τ) :
    SameSignalClass σ τ :=
  h.2

theorem cleanChartDistortion_samePeriodicCore
    {σ τ : ChartSignature} (h : CleanChartDistortion σ τ) :
    SamePeriodicCore σ τ :=
  h.1

theorem cleanChartDistortion_not_sameSignalClass
    {σ τ : ChartSignature} (h : CleanChartDistortion σ τ) :
    ¬ SameSignalClass σ τ :=
  h.2

theorem absorptionShiftDistortion_not_samePeriodicCore
    {σ τ : ChartSignature} (h : AbsorptionShiftDistortion σ τ) :
    ¬ SamePeriodicCore σ τ :=
  h.1

theorem absorptionShiftDistortion_not_sameSignalClass
    {σ τ : ChartSignature} (h : AbsorptionShiftDistortion σ τ) :
    ¬ SameSignalClass σ τ :=
  h.2

theorem cleanChartInvariant_not_cleanChartDistortion
    {σ τ : ChartSignature} (h : CleanChartInvariant σ τ) :
    ¬ CleanChartDistortion σ τ := by
  intro hdistort
  exact hdistort.2 h.2

theorem cleanChartDistortion_not_cleanChartInvariant
    {σ τ : ChartSignature} (h : CleanChartDistortion σ τ) :
    ¬ CleanChartInvariant σ τ := by
  intro hinvariant
  exact h.2 hinvariant.2

theorem absorptionStableSignal_not_absorptionShiftDistortion
    {σ τ : ChartSignature} (h : AbsorptionStableSignal σ τ) :
    ¬ AbsorptionShiftDistortion σ τ := by
  intro hdistort
  exact hdistort.2 h.2

theorem absorptionShiftDistortion_not_absorptionStableSignal
    {σ τ : ChartSignature} (h : AbsorptionShiftDistortion σ τ) :
    ¬ AbsorptionStableSignal σ τ := by
  intro hstable
  exact h.2 hstable.2

theorem cleanChartInvariant_not_absorptionStableSignal
    {σ τ : ChartSignature} (h : CleanChartInvariant σ τ) :
    ¬ AbsorptionStableSignal σ τ := by
  intro hstable
  exact hstable.1 h.1

theorem absorptionStableSignal_not_cleanChartInvariant
    {σ τ : ChartSignature} (h : AbsorptionStableSignal σ τ) :
    ¬ CleanChartInvariant σ τ := by
  intro hinvariant
  exact h.1 hinvariant.1

theorem cleanChartDistortion_not_absorptionShiftDistortion
    {σ τ : ChartSignature} (h : CleanChartDistortion σ τ) :
    ¬ AbsorptionShiftDistortion σ τ := by
  intro habsorb
  exact habsorb.1 h.1

theorem absorptionShiftDistortion_not_cleanChartDistortion
    {σ τ : ChartSignature} (h : AbsorptionShiftDistortion σ τ) :
    ¬ CleanChartDistortion σ τ := by
  intro hdistort
  exact h.1 hdistort.1

/-!
## Concrete finite signatures

These examples certify the four chart classes that the empirical
`chart-invariance` CLI currently surfaces on the compact `(10, 12, 30)` pass.
They are finite signature checks, not proofs that the signal labels are
base-independent theorem regimes.
-/

namespace ChartInvarianceExamples

def n21Base10Observation : ChartObservation :=
  ChartObservation.ofDenominator
    10 21 6 8 8 none none
    (some .stateRelabeling) (some .stateRelabeling) .transparentWindow

def n21Base10 : ChartSignature :=
  n21Base10Observation.toSignature

def n21Base12Observation : ChartObservation :=
  ChartObservation.ofDenominator
    12 21 6 8 1 (some 1) (some 2)
    none none .earlyCarryIntrusion

def n21Base12 : ChartSignature :=
  n21Base12Observation.toSignature

def n21Base30Observation : ChartObservation :=
  ChartObservation.ofDenominator
    30 21 6 8 1 (some 1) (some 2)
    none none .earlyCarryIntrusion

def n21Base30 : ChartSignature :=
  n21Base30Observation.toSignature

def n97Base10Observation : ChartObservation :=
  ChartObservation.ofDenominator
    10 97 2 8 4 (some 4) (some 5)
    (some .quotientCandidateOnly) (some .visiblePreimageCompression)
    .visibleStateCompression

def n97Base10 : ChartSignature :=
  n97Base10Observation.toSignature

def n97Base12Observation : ChartObservation :=
  ChartObservation.ofDenominator
    12 97 2 8 1 (some 1) (some 2)
    none none .earlyCarryIntrusion

def n97Base12 : ChartSignature :=
  n97Base12Observation.toSignature

def n97Base30Observation : ChartObservation :=
  ChartObservation.ofDenominator
    30 97 2 8 1 (some 1) (some 2)
    (some .quotientCandidateOnly) (some .hiddenGraphObstruction)
    .hiddenGraphObstruction

def n97Base30 : ChartSignature :=
  n97Base30Observation.toSignature

def n249Base10Observation : ChartObservation :=
  ChartObservation.ofDenominator
    10 249 3 8 3 (some 3) (some 4)
    none none .earlyCarryIntrusion

def n249Base10 : ChartSignature :=
  n249Base10Observation.toSignature

def n249Base12Observation : ChartObservation :=
  ChartObservation.ofDenominator
    12 249 3 8 1 (some 1) (some 2)
    none none .earlyCarryIntrusion

def n249Base12 : ChartSignature :=
  n249Base12Observation.toSignature

def n249Base30Observation : ChartObservation :=
  ChartObservation.ofDenominator
    30 249 3 8 1 (some 1) (some 2)
    none none .earlyCarryIntrusion

def n249Base30 : ChartSignature :=
  n249Base30Observation.toSignature

def n996Base10Observation : ChartObservation :=
  ChartObservation.ofDenominator
    10 996 3 8 4 (some 4) (some 5)
    none none .earlyCarryIntrusion

def n996Base10 : ChartSignature :=
  n996Base10Observation.toSignature

def n996Base12Observation : ChartObservation :=
  ChartObservation.ofDenominator
    12 996 3 8 1 (some 1) (some 2)
    none none .earlyCarryIntrusion

def n996Base12 : ChartSignature :=
  n996Base12Observation.toSignature

def n996Base30Observation : ChartObservation :=
  ChartObservation.ofDenominator
    30 996 3 8 1 (some 1) (some 2)
    none none .earlyCarryIntrusion

def n996Base30 : ChartSignature :=
  n996Base30Observation.toSignature

def compactObservations : List ChartObservation :=
  [ n21Base10Observation
  , n21Base12Observation
  , n21Base30Observation
  , n97Base10Observation
  , n97Base12Observation
  , n97Base30Observation
  , n249Base10Observation
  , n249Base12Observation
  , n249Base30Observation
  , n996Base10Observation
  , n996Base12Observation
  , n996Base30Observation
  ]

def compactObservationSignatures : List ChartSignature :=
  compactObservations.map ChartObservation.toSignature

theorem compactObservations_length :
    compactObservations.length = 12 := rfl

theorem compactObservationSignatures_length :
    compactObservationSignatures.length = 12 := rfl

theorem n21Base10Observation_derivedSignalClass_eq :
    n21Base10Observation.derivedSignalClass? = some .transparentWindow := by
  native_decide

theorem n21Base12Observation_derivedSignalClass_eq :
    n21Base12Observation.derivedSignalClass? = some .earlyCarryIntrusion := by
  native_decide

theorem n21Base30Observation_derivedSignalClass_eq :
    n21Base30Observation.derivedSignalClass? = some .earlyCarryIntrusion := by
  native_decide

theorem n97Base10Observation_derivedSignalClass_eq_none :
    n97Base10Observation.derivedSignalClass? = none := by
  native_decide

theorem n97Base12Observation_derivedSignalClass_eq :
    n97Base12Observation.derivedSignalClass? = some .earlyCarryIntrusion := by
  native_decide

theorem n97Base30Observation_derivedSignalClass_eq_none :
    n97Base30Observation.derivedSignalClass? = none := by
  native_decide

theorem n249Base10Observation_derivedSignalClass_eq :
    n249Base10Observation.derivedSignalClass? = some .earlyCarryIntrusion := by
  native_decide

theorem n249Base12Observation_derivedSignalClass_eq :
    n249Base12Observation.derivedSignalClass? = some .earlyCarryIntrusion := by
  native_decide

theorem n249Base30Observation_derivedSignalClass_eq :
    n249Base30Observation.derivedSignalClass? = some .earlyCarryIntrusion := by
  native_decide

theorem n996Base10Observation_derivedSignalClass_eq :
    n996Base10Observation.derivedSignalClass? = some .earlyCarryIntrusion := by
  native_decide

theorem n996Base12Observation_derivedSignalClass_eq :
    n996Base12Observation.derivedSignalClass? = some .earlyCarryIntrusion := by
  native_decide

theorem n996Base30Observation_derivedSignalClass_eq :
    n996Base30Observation.derivedSignalClass? = some .earlyCarryIntrusion := by
  native_decide

theorem compactObservations_derivedSignalAgreement_count :
    ChartObservation.countBy
      ChartObservation.derivedSignalAgrees compactObservations = 10 := by
  native_decide

theorem n21Base10Observation_fields :
    n21Base10Observation.blockBase = 1000000 ∧
      n21Base10Observation.quotientQ = 47619 ∧
      n21Base10Observation.remainderK = 1 ∧
      n21Base10Observation.rawPrefixAgreementLength = 8 ∧
      n21Base10Observation.firstIncomingCarryPosition = none ∧
      n21Base10Observation.firstLocalOverflowPosition = none := by
  native_decide

theorem n21Base30Observation_fields :
    n21Base30Observation.blockBase = 729000000 ∧
      n21Base30Observation.quotientQ = 34714285 ∧
      n21Base30Observation.remainderK = 15 ∧
      n21Base30Observation.rawPrefixAgreementLength = 1 ∧
      n21Base30Observation.firstIncomingCarryPosition = some 1 ∧
      n21Base30Observation.firstLocalOverflowPosition = some 2 := by
  native_decide

theorem n97Base10Observation_fields :
    n97Base10Observation.blockBase = 100 ∧
      n97Base10Observation.quotientQ = 1 ∧
      n97Base10Observation.remainderK = 3 ∧
      n97Base10Observation.rawPrefixAgreementLength = 4 ∧
      n97Base10Observation.firstIncomingCarryPosition = some 4 ∧
      n97Base10Observation.firstLocalOverflowPosition = some 5 ∧
      n97Base10Observation.stateMapRegime = some .quotientCandidateOnly ∧
      n97Base10Observation.obstructionClass = some .visiblePreimageCompression := by
  native_decide

theorem n97Base30Observation_fields :
    n97Base30Observation.blockBase = 900 ∧
      n97Base30Observation.quotientQ = 9 ∧
      n97Base30Observation.remainderK = 27 ∧
      n97Base30Observation.rawPrefixAgreementLength = 1 ∧
      n97Base30Observation.firstIncomingCarryPosition = some 1 ∧
      n97Base30Observation.firstLocalOverflowPosition = some 2 ∧
      n97Base30Observation.stateMapRegime = some .quotientCandidateOnly ∧
      n97Base30Observation.obstructionClass = some .hiddenGraphObstruction := by
  native_decide

theorem n249Base10Observation_fields :
    n249Base10Observation.blockBase = 1000 ∧
      n249Base10Observation.quotientQ = 4 ∧
      n249Base10Observation.remainderK = 4 ∧
      n249Base10Observation.rawPrefixAgreementLength = 3 ∧
      n249Base10Observation.firstIncomingCarryPosition = some 3 ∧
      n249Base10Observation.firstLocalOverflowPosition = some 4 := by
  native_decide

theorem n249Base30Observation_fields :
    n249Base30Observation.blockBase = 27000 ∧
      n249Base30Observation.quotientQ = 108 ∧
      n249Base30Observation.remainderK = 108 ∧
      n249Base30Observation.rawPrefixAgreementLength = 1 ∧
      n249Base30Observation.firstIncomingCarryPosition = some 1 ∧
      n249Base30Observation.firstLocalOverflowPosition = some 2 := by
  native_decide

theorem n996Base10Observation_fields :
    n996Base10Observation.blockBase = 1000 ∧
      n996Base10Observation.quotientQ = 1 ∧
      n996Base10Observation.remainderK = 4 ∧
      n996Base10Observation.rawPrefixAgreementLength = 4 ∧
      n996Base10Observation.firstIncomingCarryPosition = some 4 ∧
      n996Base10Observation.firstLocalOverflowPosition = some 5 := by
  native_decide

theorem n996Base30Observation_fields :
    n996Base30Observation.blockBase = 27000 ∧
      n996Base30Observation.quotientQ = 27 ∧
      n996Base30Observation.remainderK = 108 ∧
      n996Base30Observation.rawPrefixAgreementLength = 1 ∧
      n996Base30Observation.firstIncomingCarryPosition = some 1 ∧
      n996Base30Observation.firstLocalOverflowPosition = some 2 := by
  native_decide

theorem n21Base10_periodicModulus_eq :
    n21Base10.periodicModulus = 21 := by
  native_decide

theorem n21Base30_periodicModulus_eq :
    n21Base30.periodicModulus = 7 := by
  native_decide

theorem n97Base10_periodicModulus_eq :
    n97Base10.periodicModulus = 97 := by
  native_decide

theorem n97Base12_periodicModulus_eq :
    n97Base12.periodicModulus = 97 := by
  native_decide

theorem n97Base30_periodicModulus_eq :
    n97Base30.periodicModulus = 97 := by
  native_decide

theorem n249Base10_periodicModulus_eq :
    n249Base10.periodicModulus = 249 := by
  native_decide

theorem n249Base12_periodicModulus_eq :
    n249Base12.periodicModulus = 83 := by
  native_decide

theorem n249Base30_periodicModulus_eq :
    n249Base30.periodicModulus = 83 := by
  native_decide

theorem n996Base10_periodicModulus_eq :
    n996Base10.periodicModulus = 249 := by
  native_decide

theorem n996Base12_periodicModulus_eq :
    n996Base12.periodicModulus = 83 := by
  native_decide

theorem n996Base30_periodicModulus_eq :
    n996Base30.periodicModulus = 83 := by
  native_decide

def n21Base10Base12Witness : ChartPairWitness :=
  { left := n21Base10
    right := n21Base12
    classification := .absorptionShiftDistortion
    certified := by native_decide }

def n21Base10Base30Witness : ChartPairWitness :=
  { left := n21Base10
    right := n21Base30
    classification := .absorptionShiftDistortion
    certified := by native_decide }

def n21Base12Base30Witness : ChartPairWitness :=
  { left := n21Base12
    right := n21Base30
    classification := .cleanChartInvariant
    certified := by native_decide }

def n97Base10Base12Witness : ChartPairWitness :=
  { left := n97Base10
    right := n97Base12
    classification := .cleanChartDistortion
    certified := by native_decide }

def n97Base10Base30Witness : ChartPairWitness :=
  { left := n97Base10
    right := n97Base30
    classification := .cleanChartDistortion
    certified := by native_decide }

def n97Base12Base30Witness : ChartPairWitness :=
  { left := n97Base12
    right := n97Base30
    classification := .cleanChartDistortion
    certified := by native_decide }

def n249Base10Base12Witness : ChartPairWitness :=
  { left := n249Base10
    right := n249Base12
    classification := .absorptionStableSignal
    certified := by native_decide }

def n249Base10Base30Witness : ChartPairWitness :=
  { left := n249Base10
    right := n249Base30
    classification := .absorptionStableSignal
    certified := by native_decide }

def n249Base12Base30Witness : ChartPairWitness :=
  { left := n249Base12
    right := n249Base30
    classification := .cleanChartInvariant
    certified := by native_decide }

def n996Base10Base12Witness : ChartPairWitness :=
  { left := n996Base10
    right := n996Base12
    classification := .absorptionStableSignal
    certified := by native_decide }

def n996Base10Base30Witness : ChartPairWitness :=
  { left := n996Base10
    right := n996Base30
    classification := .absorptionStableSignal
    certified := by native_decide }

def n996Base12Base30Witness : ChartPairWitness :=
  { left := n996Base12
    right := n996Base30
    classification := .cleanChartInvariant
    certified := by native_decide }

def compactBasePairWitnesses : List ChartPairWitness :=
  [ n21Base10Base12Witness
  , n21Base10Base30Witness
  , n21Base12Base30Witness
  , n97Base10Base12Witness
  , n97Base10Base30Witness
  , n97Base12Base30Witness
  , n249Base10Base12Witness
  , n249Base10Base30Witness
  , n249Base12Base30Witness
  , n996Base10Base12Witness
  , n996Base10Base30Witness
  , n996Base12Base30Witness
  ]

theorem compactBasePairWitnesses_length :
    compactBasePairWitnesses.length = 12 := rfl

theorem compactBasePairWitnesses_10_12_count :
    countWitnessesForBasePair 10 12 compactBasePairWitnesses = 4 := by
  native_decide

theorem compactBasePairWitnesses_10_30_count :
    countWitnessesForBasePair 10 30 compactBasePairWitnesses = 4 := by
  native_decide

theorem compactBasePairWitnesses_12_30_count :
    countWitnessesForBasePair 12 30 compactBasePairWitnesses = 4 := by
  native_decide

theorem compactBasePairWitnesses_10_12_invariant_count :
    countInvariantWitnessesForBasePair 10 12 compactBasePairWitnesses = 2 := by
  native_decide

theorem compactBasePairWitnesses_10_30_invariant_count :
    countInvariantWitnessesForBasePair 10 30 compactBasePairWitnesses = 2 := by
  native_decide

theorem compactBasePairWitnesses_12_30_invariant_count :
    countInvariantWitnessesForBasePair 12 30 compactBasePairWitnesses = 3 := by
  native_decide

theorem compactBasePairWitnesses_10_12_distortion_count :
    countDistortionWitnessesForBasePair 10 12 compactBasePairWitnesses = 2 := by
  native_decide

theorem compactBasePairWitnesses_10_30_distortion_count :
    countDistortionWitnessesForBasePair 10 30 compactBasePairWitnesses = 2 := by
  native_decide

theorem compactBasePairWitnesses_12_30_distortion_count :
    countDistortionWitnessesForBasePair 12 30 compactBasePairWitnesses = 1 := by
  native_decide

theorem compactBasePairWitnesses_10_12_clean_invariant_count :
    countWitnessesForBasePairWithClass
      10 12 .cleanChartInvariant compactBasePairWitnesses = 0 := by
  native_decide

theorem compactBasePairWitnesses_10_30_clean_invariant_count :
    countWitnessesForBasePairWithClass
      10 30 .cleanChartInvariant compactBasePairWitnesses = 0 := by
  native_decide

theorem compactBasePairWitnesses_12_30_clean_invariant_count :
    countWitnessesForBasePairWithClass
      12 30 .cleanChartInvariant compactBasePairWitnesses = 3 := by
  native_decide

theorem compactBasePairWitnesses_10_12_absorption_stable_count :
    countWitnessesForBasePairWithClass
      10 12 .absorptionStableSignal compactBasePairWitnesses = 2 := by
  native_decide

theorem compactBasePairWitnesses_10_30_absorption_stable_count :
    countWitnessesForBasePairWithClass
      10 30 .absorptionStableSignal compactBasePairWitnesses = 2 := by
  native_decide

theorem compactBasePairWitnesses_12_30_absorption_stable_count :
    countWitnessesForBasePairWithClass
      12 30 .absorptionStableSignal compactBasePairWitnesses = 0 := by
  native_decide

theorem compactBasePairWitnesses_10_12_clean_distortion_count :
    countWitnessesForBasePairWithClass
      10 12 .cleanChartDistortion compactBasePairWitnesses = 1 := by
  native_decide

theorem compactBasePairWitnesses_10_30_clean_distortion_count :
    countWitnessesForBasePairWithClass
      10 30 .cleanChartDistortion compactBasePairWitnesses = 1 := by
  native_decide

theorem compactBasePairWitnesses_12_30_clean_distortion_count :
    countWitnessesForBasePairWithClass
      12 30 .cleanChartDistortion compactBasePairWitnesses = 1 := by
  native_decide

theorem compactBasePairWitnesses_10_12_absorption_shift_count :
    countWitnessesForBasePairWithClass
      10 12 .absorptionShiftDistortion compactBasePairWitnesses = 1 := by
  native_decide

theorem compactBasePairWitnesses_10_30_absorption_shift_count :
    countWitnessesForBasePairWithClass
      10 30 .absorptionShiftDistortion compactBasePairWitnesses = 1 := by
  native_decide

theorem compactBasePairWitnesses_12_30_absorption_shift_count :
    countWitnessesForBasePairWithClass
      12 30 .absorptionShiftDistortion compactBasePairWitnesses = 0 := by
  native_decide

theorem compactBasePairWitnesses_clean_invariant_total :
    countWitnessesBy
      (fun witness => witness.hasClassification .cleanChartInvariant)
      compactBasePairWitnesses = 3 := by
  native_decide

theorem compactBasePairWitnesses_absorption_stable_total :
    countWitnessesBy
      (fun witness => witness.hasClassification .absorptionStableSignal)
      compactBasePairWitnesses = 4 := by
  native_decide

theorem compactBasePairWitnesses_clean_distortion_total :
    countWitnessesBy
      (fun witness => witness.hasClassification .cleanChartDistortion)
      compactBasePairWitnesses = 3 := by
  native_decide

theorem compactBasePairWitnesses_absorption_shift_total :
    countWitnessesBy
      (fun witness => witness.hasClassification .absorptionShiftDistortion)
      compactBasePairWitnesses = 2 := by
  native_decide

theorem n21_base12_base30_cleanChartInvariant :
    CleanChartInvariant n21Base12 n21Base30 :=
  ChartPairWitness.cleanChartInvariant_of_classification_eq
    n21Base12Base30Witness rfl

theorem n21_base12_base30_class :
    ChartInvarianceClass.ofSignatures n21Base12 n21Base30 =
      ChartInvarianceClass.cleanChartInvariant := by
  simpa [n21Base12Base30Witness] using n21Base12Base30Witness.certified

theorem n249_base10_base30_absorptionStableSignal :
    AbsorptionStableSignal n249Base10 n249Base30 :=
  ChartPairWitness.absorptionStableSignal_of_classification_eq
    n249Base10Base30Witness rfl

theorem n249_base10_base30_class :
    ChartInvarianceClass.ofSignatures n249Base10 n249Base30 =
      ChartInvarianceClass.absorptionStableSignal := by
  simpa [n249Base10Base30Witness] using n249Base10Base30Witness.certified

theorem n97_base10_base30_cleanChartDistortion :
    CleanChartDistortion n97Base10 n97Base30 :=
  ChartPairWitness.cleanChartDistortion_of_classification_eq
    n97Base10Base30Witness rfl

theorem n97_base10_base30_class :
    ChartInvarianceClass.ofSignatures n97Base10 n97Base30 =
      ChartInvarianceClass.cleanChartDistortion := by
  simpa [n97Base10Base30Witness] using n97Base10Base30Witness.certified

theorem n21_base10_base30_absorptionShiftDistortion :
    AbsorptionShiftDistortion n21Base10 n21Base30 :=
  ChartPairWitness.absorptionShiftDistortion_of_classification_eq
    n21Base10Base30Witness rfl

theorem n21_base10_base30_class :
    ChartInvarianceClass.ofSignatures n21Base10 n21Base30 =
      ChartInvarianceClass.absorptionShiftDistortion := by
  simpa [n21Base10Base30Witness] using n21Base10Base30Witness.certified

theorem n97_base12_base30_cleanChartDistortion :
    CleanChartDistortion n97Base12 n97Base30 :=
  ChartPairWitness.cleanChartDistortion_of_classification_eq
    n97Base12Base30Witness rfl

theorem n249_base12_base30_cleanChartInvariant :
    CleanChartInvariant n249Base12 n249Base30 :=
  ChartPairWitness.cleanChartInvariant_of_classification_eq
    n249Base12Base30Witness rfl

theorem n996_base10_base30_absorptionStableSignal :
    AbsorptionStableSignal n996Base10 n996Base30 :=
  ChartPairWitness.absorptionStableSignal_of_classification_eq
    n996Base10Base30Witness rfl

theorem n996_base12_base30_cleanChartInvariant :
    CleanChartInvariant n996Base12 n996Base30 :=
  ChartPairWitness.cleanChartInvariant_of_classification_eq
    n996Base12Base30Witness rfl

end ChartInvarianceExamples

end QRTour
