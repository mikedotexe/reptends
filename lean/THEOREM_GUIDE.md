# Lean Theorem Guide

Use [docs/PROOF_STATUS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/PROOF_STATUS_ATLAS.md) as the public status source of truth. This note is the Lean-facing module and theorem index for the current formal surface.

## Atlas-Backed Claim Carriers

| Claim ID | Atlas Status | Lean module(s) | Main theorem names |
|----------|--------------|----------------|--------------------|
| `series_q_weighted_identity` | `reproved-here` | [QRTour/OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean) | `partialSumQ_eq_finite`, `one_div_modulus_eq_quotientQ_div_gap`, `series_q_weighted_identity` |
| `positive_q_good_modes` | `reproved-here` | [QRTour/OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean) | `quotientQ_eq_gap_div_modulus`, `positive_q_good_modes` |
| `digit_periodicity` | `reproved-here` | [QRTour/Digits.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Digits.lean) | `digit_remainder_eq`, `digit_periodic`, `reptendPeriod_dvd_pred`, `digit_as_overflow` |
| `signed_bridge_recurrence` | `reproved-here` | [QRTour/SignedBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/SignedBridge.lean) | `SignedBridge.remainder_k_step`, `SignedBridge.remainder_2k_step`, `Bridge.toSignedBridge` |
| `bridge_block_value_periodicity` | `reproved-here` | [QRTour/PAdicBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/PAdicBridge.lean) | `blockValue`, `Bridge.blockValue_eq_pow`, `bridgeOrder`, `Bridge.blockValue_periodic` |
| `incoming_carry_position_formula` | `reproved-here` | [QRTour/Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean) | `incomingCarry_formula`, `incomingCarry_pos_iff`, `isFirstIncomingCarryPosition_iff`, `emittedPrefixValue_eq_truncatedVisiblePrefixValue_iff_lookaheadCertificate` |
| `same_core_threshold_shift_interval` | `reproved-here` | [QRTour/Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [QRTour/CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean) | `geometricThreshold_shift_interval`, `geometricThreshold_shift_exact`, `firstIncomingCarryPosition_shift_interval`, `localOverflowBoundary_shift_interval`, `sameCoreCompatible_iff_quotientQ_scaling`, `sameCoreCompatible_of_goodMode_and_blockBase_lt_modulus_add_stripped`, `sameCoreCompatible_rawCoefficient_eq`, `sameCoreCompatible_lookaheadCertificateHolds_iff_add_exact`, `classifyThresholdShiftEndpoint`, `sameCoreCompatible_firstIncomingCarryPosition_endpoint_exact`, `sameCoreCompatible_firstIncomingCarryPosition_endpoint_lower_of_scaledRawCoefficient_lt_gap`, `sameCoreCompatible_firstIncomingCarryPosition_endpoint_upper_of_gap_le_scaledRawCoefficient`, `sameCoreCompatible_localOverflowBoundary_endpoint_exact`, `sameCoreCompatible_localOverflowBoundary_endpoint_lower_of_scaledRawCoefficient_lt_blockBase`, `sameCoreCompatible_localOverflowBoundary_endpoint_upper_of_blockBase_le_scaledRawCoefficient`, `strippedCoordinate_firstIncomingCarryPosition_shift_interval`, `strippedCoordinate_localOverflowBoundary_shift_interval` |
| `qr_stride_classification` | `reproved-here` | [QRTour/QuadraticResidues.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/QuadraticResidues.lean) | `pow_isQRGenerator_iff`, `qrGenerator_pow_count_eq_totient`, `base_qrGenerator_pow_count_eq_totient` |
| `crt_period_lcm` | `classical` with Lean backing in repo evidence | [QRTour/CompositePeriod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositePeriod.lean) | `orderOf_unitsChineseRemainder`, `orderOf_unitsEquivPrimePowers`, `orderOf_pi` |
| `preperiod_from_base_factors` | `classical` with Lean backing in repo evidence | [QRTour/Preperiod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Preperiod.lean), [QRTour/CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean) | `preperiodPrimeSteps_le_iff`, `preperiodSteps_le_of_local_bounds`, `basePrimeSupportFactor_dvd_base_pow_preperiodSteps`, `basePrimeSupportFactor_dvd`, `basePrimeSupportFactor_mul_strippedPeriodModulus` |

## Open Claims With Lean Boundary Work

These claims remain `open`, but Lean now covers an exact supporting layer beneath them.

| Claim ID | Current Lean boundary |
|----------|-----------------------|
| `small_k_visibility_threshold` | [QRTour/Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean) formalizes the exact fixed-window gap certificate, the necessary tail-mass lower bound, and monotone transport of visible-prefix agreement to larger lookahead windows; [QRTour/CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean) now packages exact same-core transport of the first visible mismatch boundary, the raw tail-mass lower-bound inequality, the shifted coarse `k^(n+L) < modulus` sufficient condition, and the exact fixed-window certificate itself between the stripped core at `(n, L)` and the actual denominator at `(n + s, L)` in the exact `k`-power regime; [QRTour/CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean) now consumes both the generic and exact same-core certificate transport layers to reprove finite carry/remainder visible-word agreement on those shifted windows. |
| `carry_dfa_factorization` | [QRTour/CarryTransducer.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryTransducer.lean) and [QRTour/CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean) now cover finite normalization, traced runs, aligned finite state records, observed finite remainder/carry state-pair projections, pointwise local carry-balance and remainder-balance equations, exact finite-window functional criteria for the observed state-pair lists, finite transition-compatibility theorems under those criteria, explicit finite conflict lemmas refuting the criteria when the observed pair list disagrees, and finite aligned outputs, but no global factorization, minimization, or canonical morphism theorem. |

## Module Status Index

This audit table is generated from [lean_module_index.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/lean_module_index.json).

<!-- LEAN_MODULE_INDEX_START -->
| Module | Current role | Promotion decision | Associated claim IDs |
|--------|--------------|--------------------|----------------------|
| [QRTour/Basic.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Basic.lean) | foundational arithmetic and divisibility helper layer | keep as foundational infrastructure | none |
| [QRTour/RemainderOrbit.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/RemainderOrbit.lean) | prime-tour remainder-orbit semantics and period support | keep as public support surface | `qr_stride_classification`, `digit_periodicity` |
| [QRTour/Bridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Bridge.lean) | exact bridge-coordinate recurrence layer | keep as public support surface | `signed_bridge_recurrence`, `bridge_block_value_periodicity` |
| [QRTour/CosetStructure.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CosetStructure.lean) | QR and NQR subgroup-translation structure | keep as public support surface | `qr_stride_classification` |
| [QRTour/QuadraticResidues.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/QuadraticResidues.lean) | atlas-backed QR stride classification carrier | keep as public theorem surface | `qr_stride_classification` |
| [QRTour/OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean) | atlas-backed q-weighted series and body/correction algebra core | keep as public theorem surface | `series_q_weighted_identity`, `positive_q_good_modes` |
| [QRTour/Digits.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Digits.lean) | digit and remainder Euclidean equation plus digit periodicity | keep as public theorem surface | `digit_periodicity` |
| [QRTour/PrimitiveRoots.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/PrimitiveRoots.lean) | general generator hierarchy above the QR-specific public surface | leave as supporting infrastructure for now | none |
| [QRTour/BridgeQuality.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/BridgeQuality.lean) | exploratory bridge-deficit and quality layer | leave as supporting infrastructure for now | none |
| [QRTour/SignedBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/SignedBridge.lean) | signed plus/minus bridge recurrence package with sign cancellation | keep as public theorem surface | `signed_bridge_recurrence` |
| [QRTour/PAdicBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/PAdicBridge.lean) | bridge block-value geometricity and periodicity layer | keep as public theorem surface | `bridge_block_value_periodicity` |
| [QRTour/CompositePeriod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositePeriod.lean) | CRT order and composite period theorem carrier | keep as public theorem surface | `crt_period_lcm` |
| [QRTour/Preperiod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Preperiod.lean) | valuation and base-factor preperiod theorem carrier | keep as public theorem surface | `preperiod_from_base_factors` |
| [QRTour/Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean) | incoming-carry theorem surface and exact fixed-window lookahead certificate layer | keep as public theorem surface with open-boundary support | `incoming_carry_position_formula`, `same_core_threshold_shift_interval`, `small_k_visibility_threshold` |
| [QRTour/CarryTransducer.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryTransducer.lean) | finite carry normalization and traced transducer core | keep as public support surface under the open carry boundary | `carry_window_transducer`, `carry_dfa_factorization` |
| [QRTour/CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean) | explicit finite carry and remainder comparison layer | keep as public support surface under the open carry boundary | `carry_window_transducer`, `small_k_visibility_threshold`, `carry_dfa_factorization` |
| [QRTour/CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean) | same-core family packaging, endpoint labels, and coordinate-selection layer | keep as public support surface tied to exact same-core laws | `preperiod_from_base_factors`, `same_core_threshold_shift_interval`, `small_k_visibility_threshold` |
| [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) | worked Lean acceptance examples and theorem smoke tests | keep as public example surface, not atlas-backed | none |
| [GeometricStack.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/GeometricStack.lean) | companion overflow and decomposition library family | keep as specialized companion infrastructure | none |
<!-- LEAN_MODULE_INDEX_END -->

## Next Lean Frontier

The immediate frontier is no longer “make carry/visibility exact.” That part is now in Lean. The next honest frontier splits into three lanes:

- theorem frontier:
  strengthen same-core visibility and fixed-window carry/visibility arithmetic beyond the current quotient-scaling, scaled-raw-coefficient endpoint criteria, and exact certificate layer, while keeping `small_k_visibility_threshold` and `carry_dfa_factorization` explicitly `open`
- promotion audit:
  decide whether any of `PrimitiveRoots`, `BridgeQuality`, or the remaining bridge-specialized support modules deserve their own atlas claim IDs, and classify the rest explicitly as public support or infrastructure
- theorem-witness tooling:
  extend the now-generated [THEOREM_WITNESS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/THEOREM_WITNESS_ATLAS.md) into search outputs, site-facing data, and targeted research exports so the formal surface and the open-claim surface are easier to inspect and publish without hand-maintained drift
