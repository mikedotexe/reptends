/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.RemainderOrbit
import QRTour.PrimitiveRoots
import QRTour.Digits
import QRTour.Bridge
import QRTour.SignedBridge
import QRTour.PAdicBridge
import QRTour.CompositePeriod
import QRTour.Visibility
import QRTour.CarryComparison

/-!
# Worked Examples: prime 19, prime 97, composite 21, composite 249, and same-core composite 996 over 249

This module packages the five canonical Lean witness families used across the
repo's current theorem surface:

- the prime tuple `(base=10, p=19, ord_p(base)=18)`, where the Euclidean digit
  step and full decimal reptend period are both small enough to inspect directly
- the prime tuple `(base=10, p=97, stride=2, B=100, q=1, k=3)`, where
  `ord₉₇(3) = 48 = (97-1)/2` makes `3` a quadratic-residue generator
- the composite tuple `(base=10, N=21=3·7, ord_3(base)=1, ord_7(base)=6)`,
  where the CRT least-common-multiple law is small enough to inspect
  componentwise
- the composite tuple `(base=10, N=249, stride=3, B=1000, q=4, k=4)`, where
  the positive quotient `q` makes the good-mode boundary visible beyond the
  special `q = 1` bridge case
- the same-core composite tuple `(base=10, N=996, core=249, stride=3,
  B=1000, q=1, k=4)`, where the base-prime support factor is exactly `k^1`

The first namespace gives the canonical small prime witness for decimal digit
periodicity. The second namespace gives the canonical prime witness for the QR
tour, signed bridge recurrence, block-value periodicity, q-weighted series,
incoming-carry and local-overflow boundaries, and a finite carry-window
agreement witness. The third namespace gives the canonical small composite
witness for the CRT period theorem. The fourth namespace packages the standard
positive-`q` composite witness for the good-mode positivity, q-weighted
series, incoming-carry boundaries, and a short finite carry-window witness
with zero lookahead. The fifth namespace packages the standard same-core
composite witness for shifted visibility and finite carry-comparison
transport.

## Proof-System Framing

Use the shared public proof-system legend here as on the theorem guide and Lean
umbrella surfaces. `Examples.lean` is a registry-backed worked-example surface,
not an atlas-backed claim carrier, so its theorem entry points should still be
framed explicitly relative to the exact/open boundary.

<!-- PROOF_SYSTEM_LEGEND_START -->
- `Lean-formalized`: proved in the Lean tree and suitable for theorem-level citation in the current public surface.
- `Agda-locally-proved`: discharged inside the Agda pedagogical companion surface without relying on Agda postulates.
- `Agda-postulated but Lean-backed`: still explicit as an Agda postulate, but closed by Lean or an atlas-backed Lean-backed claim in this repo.
- `empirical`: implemented and regression-tested here, but not promoted to theorem status.
- `open`: tracked as an unresolved claim boundary or interface question, not an established result.
<!-- PROOF_SYSTEM_LEGEND_END -->

## Registry-Backed Worked-Example Index

This table is generated from
[lean_worked_examples.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/lean_worked_examples.json)
so the public `Examples.lean` entry-point surface stays aligned with the
theorem guide and theorem-witness registry.

<!-- EXAMPLES_WORKED_EXAMPLE_INDEX_START -->
| Lean example namespace | Atlas claim IDs | Example theorem entry points | Current role | Witness-atlas entry points |
|------------------------|-----------------|------------------------------|--------------|----------------------------|
| [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Prime19` | `digit_periodicity` | `reptendPeriod_eq_eighteen`, `digit_remainder_step_zero`, `digit_periodic_decimal` | Canonical small prime witness surface for the decimal tuple `(base=10, p=19, ord_p(base)=18)`, exposing both the first Euclidean digit step and the full decimal reptend period beneath the digit-periodicity public statement. | `digit_periodicity_prime19_base10` |
| [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Prime97` | `qr_stride_classification`, `signed_bridge_recurrence`, `bridge_block_value_periodicity`, `series_q_weighted_identity`, `incoming_carry_position_formula`, `carry_window_transducer` | `k_is_qr_generator`, `signedBridge_remainder_k_step`, `signedBridge_remainder_2k_step`, `bridge_blockValue_eq_pow`, `bridgeOrder_eq_forty_eight`, `bridge_blockValue_periodic`, `coordinate_series_q_weighted_identity`, `coordinate_partialSumQ_four_eq_finite`, `coordinate_bodyTerm_four_eq_polynomial`, `coordinate_bodyTerm_five_recurrence`, `coordinate_firstIncomingCarryPosition`, `coordinate_isFirstIncomingCarryPosition_iff`, `coordinate_incomingCarry_three_eq_zero`, `coordinate_incomingCarry_four_eq_two`, `coordinate_overflowQuotient_four_eq_zero`, `coordinate_localOverflowBoundary`, `coordinate_isLocalOverflowBoundary_iff`, `coordinate_lookaheadCertificate_six_one`, `coordinate_visibleCarryWord_eq_emittedBlockWord_six_one`, `coordinate_lookaheadCertificate_six_three`, `coordinate_visibleCarryWord_six_one_eq_six_three`, `coordinate_visibleCarryWord_eq_emittedBlockWord_six_three`, `coordinate_visibleCarryWord_six_three_eq_blocks`, `coordinate_stateAlignments_output_agreement_six_three`, `coordinate_stateAlignments_output_agreement_pointwise_six_three` | Canonical prime witness surface for the decimal tuple `(base=10, p=97, stride=2, B=100, q=1, k=3)` beneath the QR-tour, signed-bridge recurrence, block-value periodicity, q-weighted series, incoming-carry, and finite carry-window public statements, with the clean decimal minus-bridge recurrence `r[n+2] = 3*r[n]`, the sign-cancelled `r[n+4] = 3^2*r[n]` specialization, the stride-2 block-value period `48`, the exact q-weighted series specialization and four-term exact finite prefix identity both made explicit in the clean `q = 1` bridge case, the four-block body term exposing raw coefficients `1, 3, 9, 27`, the next recurrence appending the next raw coefficient `81`, the first incoming-carry boundary characterized exactly by `j = 4`, zero carry just before that boundary, carry `2` at the boundary itself, the pre-overflow quotient still vanishing at block `4`, the adjacent local-overflow boundary also characterized exactly by `j = 4`, so block `5` is the first raw overflow, one block of lookahead already certifies the six-block carried window, the larger `(requestedBlocks=6, lookahead=3)` witness preserves that same visible prefix, and the stabilized six-block carried word `[1, 3, 9, 27, 83, 50]` is made explicit on the worked-example surface, with aligned carry/remainder output agreement exposed at both the whole-window and pointwise levels. | `qr_stride_classification_prime97_stride2`, `signed_bridge_recurrence_prime97_stride2`, `bridge_block_value_periodicity_prime97_stride2`, `series_q_weighted_identity_prime97_stride2`, `incoming_carry_position_formula_prime97_stride2`, `carry_window_transducer_prime97_window6` |
| [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Composite21` | `crt_period_lcm` | `order_of_decimalUnitMod3`, `order_of_decimalUnitMod7`, `decimalUnit_order_eq_lcm_component_orders`, `order_of_decimalUnitMod21` | Canonical small composite witness surface for the tuple `(base=10, N=21=3·7, ord_3(base)=1, ord_7(base)=6)` beneath the CRT period public statement, exposing both local component orders and the exact pairwise CRT least-common-multiple equation before collapsing the global decimal order to `6`. | `crt_period_lcm_mod21_base10` |
| [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Composite249` | `positive_q_good_modes`, `series_q_weighted_identity`, `incoming_carry_position_formula`, `carry_window_transducer` | `coordinate_goodMode`, `coordinate_quotientQ_eq_four`, `coordinate_remainderK_eq_four`, `coordinate_positive_q_good_modes`, `coordinate_series_q_weighted_identity`, `coordinate_partialSumQ_four_eq_finite`, `coordinate_bodyTerm_four_eq_polynomial`, `coordinate_bodyTerm_five_recurrence`, `coordinate_firstIncomingCarryPosition`, `coordinate_isFirstIncomingCarryPosition_iff`, `coordinate_incomingCarry_two_eq_zero`, `coordinate_incomingCarry_three_eq_one`, `coordinate_localOverflowBoundary`, `coordinate_isLocalOverflowBoundary_iff`, `coordinate_firstVisibleMismatchPosition_eq_three`, `coordinate_lookaheadCertificate_three_zero`, `coordinate_visibleCarryWord_eq_emittedBlockWord_three_zero`, `coordinate_visibleCarryWord_three_zero_eq_blocks`, `coordinate_stateAlignments_output_agreement_three_zero`, `coordinate_stateAlignments_output_agreement_pointwise_three_zero` | Canonical positive-q composite witness for the tuple `(base=10, N=249, stride=3, B=1000, q=4, k=4)` beneath the good-mode positivity, q-weighted series, incoming-carry, and finite carry-window public statements, with the exact q-weighted series specialization and the four-term finite partial-sum closed form made explicit, the four-block body term exposing raw coefficients `4, 16, 64, 256`, the next recurrence appending the overflowing coefficient `1024`, the first incoming-carry boundary characterized exactly by `j = 3`, zero carry just before that boundary, carry `1` at the boundary itself, the adjacent local-overflow boundary also characterized exactly by `j = 3`, so block `4` is the first raw overflow, and the carry-free `(requestedBlocks=3, lookahead=0)` window already satisfies the exact lookahead certificate, stabilizes at `[4, 16, 64]`, and exposes aligned carry/remainder output agreement at both the whole-window and pointwise levels outside the special `q = 1` case. | `positive_q_good_modes_n249_stride3`, `series_q_weighted_identity_n249_stride3`, `incoming_carry_position_formula_n249_stride3`, `carry_window_transducer_n249_window3` |
| [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Composite996` | `preperiod_from_base_factors`, `same_core_threshold_shift_interval`, `carry_window_transducer` | `preperiodSteps_eq_two`, `basePrimeSupportFactor_eq_four`, `strippedPeriodModulus_eq_249`, `sameCore_remainderK_eq`, `sameCore_basePrimeSupportFactor_eq_remainderK_pow_one`, `sameCore_denominator_eq_249_mul_remainderK_pow_one`, `sameCore_denominator_eq_249_mul_coreRemainderK_pow_one`, `sameCore_quotientQ_scaling`, `sameCore_quotientQ_scaling_eq_remainderK_pow_one`, `sameCore_firstIncomingCarryPosition_shift_exact`, `sameCore_localOverflowBoundary_shift_exact`, `sameCore_localOverflowBoundary_via_overflowQuotient`, `core249_firstVisibleMismatchPosition_eq_three`, `actual996_firstVisibleMismatchPosition_eq_four`, `sameCore_firstVisibleMismatchPosition_shift_exact`, `sameCore_lookaheadCertificateHolds_iff_add_exact`, `sameCore_tailMassLowerBound_iff_add_exact`, `actual996_tailMassLowerBound_of_core_lookaheadCertificate_exact`, `core249_tailMassLowerBound_of_actual_lookaheadCertificate_exact`, `actual996_visibleCarryWord_eq_emittedBlockWord_of_core_lookaheadCertificate`, `actual996_visibleCarryPairs_output_agreement_of_core_lookaheadCertificate`, `actual996_visibleCarryPairs_output_agreement_pointwise_of_core_lookaheadCertificate`, `actual996_visibleCarryPairs_carry_balance`, `actual996_visibleCarryPairs_remainder_balance`, `core249_visibleCarryWord_eq_emittedBlockWord_of_actual_lookaheadCertificate`, `core249_visibleCarryPairs_output_agreement_of_actual_lookaheadCertificate`, `core249_visibleCarryPairs_output_agreement_pointwise_of_actual_lookaheadCertificate`, `core249_visibleCarryPairs_carry_balance`, `core249_visibleCarryPairs_remainder_balance`, `actual996_stateAlignments_output_agreement_of_core_lookaheadCertificate`, `actual996_stateAlignments_output_agreement_pointwise_of_core_lookaheadCertificate`, `core249_stateAlignments_output_agreement_of_actual_lookaheadCertificate`, `core249_stateAlignments_output_agreement_pointwise_of_actual_lookaheadCertificate`, `actual996_visibleCarryWord_eq_emittedBlockWord`, `actual996_visibleCarryWord_four_zero_eq_blocks`, `actual996_visibleCarryPairs_output_agreement`, `actual996_visibleCarryPairs_output_agreement_pointwise`, `actual996_stateAlignments_output_agreement`, `actual996_stateAlignments_output_agreement_pointwise`, `actual996_stateAlignments_coefficient_shift_exact`, `actual996_stateAlignments_carryIn_shift_exact`, `actual996_stateAlignments_carryOut_shift_exact`, `actual996_stateAlignments_remainderIn_shift_exact`, `actual996_stateAlignments_carryBlockValue_shift_exact`, `actual996_stateAlignments_remainderBlockValue_shift_exact`, `actual996_stateAlignments_remainderOut_shift_exact`, `core249_visibleCarryWord_eq_emittedBlockWord`, `core249_visibleCarryWord_three_zero_eq_blocks`, `sameCore_visibleCarryWord_shift_exact`, `core249_visibleCarryPairs_output_agreement`, `core249_visibleCarryPairs_output_agreement_pointwise`, `core249_stateAlignments_output_agreement`, `core249_stateAlignments_output_agreement_pointwise`, `actual996_stateAlignments_remainderToCarryStepFunctional`, `core249_carryToRemainderFunctional_one_zero`, `actual996_carryToRemainder_conflict_two_zero`, `sameCore_carryToRemainderTransport_counterexample`, `actual996_not_carryToRemainderFunctional`, `actual996_stateAlignments_remainderToCarry_transition_compatible`, `actual996_quotientOnly_profile`, `core249_remainderToCarryFunctional`, `core249_stateAlignments_remainderToCarry_transition_compatible`, `core249_not_carryToRemainderFunctional` | Canonical same-core composite witness surface for the tuple `(base=10, N=996, core=249, stride=3, B=1000, q=1, k=4)` beneath the preperiod, same-core visibility, and finite carry-comparison public statements, including the exact base-prime support factor identity `basePrimeSupportFactor 10 996 = 4`, the induced product decomposition `996 = 4 * 249`, the exact stripped periodic core identity `strippedPeriodModulus 10 996 = 249`, the exact shared remainder identity `k_core = k_actual = 4`, the exact `k^1` specialization `basePrimeSupportFactor 10 996 = k_actual^1 = k_core^1`, the exact same-core denominator identity `996 = 249 * k^1`, exposed as both `996 = 249 * k_actual^1` and `996 = 249 * k_core^1`, the exact quotient-scaling identities `q_core = q_actual * 4` and `q_core = q_actual * k^1`, the stripped-core and actual first visible-mismatch positions made explicit as `3` and `4`, the exact one-block shift of the first incoming-carry, local-overflow, and first visible-mismatch boundaries, the exact overflow-quotient view of the same-core local-overflow boundary on blocks `3/4` for the stripped core and `4/5` for the actual denominator, the exact fixed-window lookahead-certificate transport between the stripped-core and shifted actual windows, the exact raw tail-mass lower-bound equivalence on the canonical `3/0 -> 4/0` window pair together with paired forward and reverse exact-certificate tail-mass lower-bound implications on that same window pair, paired forward and reverse exact-certificate visible-word, pair-output, and aligned-output implications on that same window pair, with the pair-output and aligned-output layers exposed at both whole-window and pointwise levels plus pointwise pair-balance arithmetic on both canonical windows, forward visible carry, pair-output, and state-output agreement on the shifted actual `4/0` window, including the concrete stabilized visible word `[1, 4, 16, 64]`, the concrete stripped-core visible word `[4, 16, 64]`, and the exact one-block visible-word shift `[1, 4, 16, 64] = 1 :: [4, 16, 64]` on the canonical `4/0 -> 3/0` window pair, coarse whole-window and pointwise pair-output and state-alignment wrappers plus exact one-block same-core shift of aligned raw coefficients, carry states, carried block values, carry outputs, remainder inputs, remainder block values, and next-step remainder states on the canonical `3/0 -> 4/0` window pair, reverse visible, pair-output, and state-output agreement on the unshifted stripped-core `3/0` window at both whole-window and pointwise levels plus transported remainder-to-carry functionality, reverse transition compatibility, and stripped-core carry-to-remainder failure on that unshifted stripped-core window, the explicit stripped-core `1/0` carry-to-remainder functional witness, the shifted-actual `2/0` carry-to-remainder conflict, an explicit one-block `1/0 -> 2/0` counterexample to forward same-core carry-to-remainder transport, the forward-only state-map asymmetry and remainder-to-carry transition compatibility on the shifted actual window, and the larger-window quotient-only profile on the actual `8/1` selector-family window. | `preperiod_from_base_factors_n996_base10`, `same_core_threshold_shift_interval_996_over_249`, `carry_window_transducer_same_core_996_window4` |
<!-- EXAMPLES_WORKED_EXAMPLE_INDEX_END -->

## Same-Core Open Boundary Reminder

This short registry-backed note keeps the concrete `996 over 249` example
surface aligned with the theorem guide and witness atlas: exact same-core shift
and finite carry-comparison theorems are exposed here, while the broader
minimal-lookahead and global carry-factorization claims remain explicitly open.

<!-- EXAMPLES_OPEN_BOUNDARY_NOTE_START -->
- `small_k_visibility_threshold` remains `open`: on `QRTour.Composite996`, `sameCore_firstIncomingCarryPosition_shift_exact`, `sameCore_localOverflowBoundary_shift_exact`, `sameCore_firstVisibleMismatchPosition_shift_exact`, and `sameCore_lookaheadCertificateHolds_iff_add_exact` package the exact one-block same-core shift and the exact fixed-window lookahead-certificate transport, but do not claim a sharp minimal-lookahead or global visibility formula. The related atlas entry is `same_core_threshold_shift_interval_996_over_249`.
- `carry_dfa_factorization` remains `open`: on `QRTour.Composite996`, `actual996_stateAlignments_remainderToCarryStepFunctional`, `core249_carryToRemainderFunctional_one_zero`, `actual996_carryToRemainder_conflict_two_zero`, `sameCore_carryToRemainderTransport_counterexample`, `actual996_not_carryToRemainderFunctional`, `actual996_stateAlignments_remainderToCarry_transition_compatible`, `actual996_quotientOnly_profile`, `core249_remainderToCarryFunctional`, `core249_stateAlignments_remainderToCarry_transition_compatible`, and `core249_not_carryToRemainderFunctional` prove exact finite same-core functionality and asymmetry on selected windows, surface the stripped-core `1/0` functional witness and the shifted-actual `2/0` conflict explicitly, explicitly refute forward same-core `carryToRemainderFunctional` transport on the exact `1/0 -> 2/0` pair, but do not promote a global canonical factorization theorem. The related atlas entry is `carry_dfa_factorization_target_249_498_996_same_core`.
<!-- EXAMPLES_OPEN_BOUNDARY_NOTE_END -->

## Prime 19 Results

* `QRTour.Prime19.reptendPeriod_eq_eighteen` - the decimal reptend period of
  `1/19` is exactly `18`
* `QRTour.Prime19.digit_remainder_step_zero` - the first Euclidean digit step
  is `10*1 = 0*19 + 10`
* `QRTour.Prime19.digit_periodic_decimal` - the decimal digits repeat after
  that exact `18`-step period

## Prime 97 Results

* `QRTour.Prime97.k_eq_three` and `QRTour.Prime97.k_is_qr_generator` -
  `10² ≡ 3 (mod 97)`, and that remainder `3` is the canonical QR generator
  for the stride-2 decimal witness
* `QRTour.Prime97.order_of_three` - `ord₉₇(3) = 48`
* `QRTour.Prime97.qr_tour` - application of the QR tour theorem
* `QRTour.Prime97.signedBridge_remainder_k_step` and
  `QRTour.Prime97.signedBridge_remainder_2k_step` - the canonical signed bridge
  recurrence entry points specialized to the clean decimal minus-bridge case
* `QRTour.Prime97.bridge_blockValue_eq_pow`,
  `QRTour.Prime97.bridgeOrder_eq_forty_eight`, and
  `QRTour.Prime97.bridge_blockValue_periodic` - the block values at stride-2
  positions are exactly powers of `3`, with period `48`
* `QRTour.Prime97.coordinate_series_q_weighted_identity` and
  `QRTour.Prime97.coordinate_partialSumQ_four_eq_finite` - the canonical
  coordinate witnesses both the infinite q-weighted series identity and the
  four-term exact finite prefix identity in the clean `q = 1` bridge case
* `QRTour.Prime97.coordinate_bodyTerm_four_eq_polynomial` and
  `QRTour.Prime97.coordinate_bodyTerm_five_recurrence` - the four-block body
  term already exposes raw coefficients `1, 3, 9, 27`, and the next
  recurrence appends the next raw coefficient `81`
* `QRTour.Prime97.coordinate_firstIncomingCarryPosition`,
  `QRTour.Prime97.coordinate_isFirstIncomingCarryPosition_iff`,
  `QRTour.Prime97.coordinate_incomingCarry_three_eq_zero`, and
  `QRTour.Prime97.coordinate_incomingCarry_four_eq_two` - the first incoming
  carry occurs exactly at block `4`, with zero carry just before the boundary
  and carry `2` at the boundary itself
* `QRTour.Prime97.coordinate_overflowQuotient_four_eq_zero`,
  `QRTour.Prime97.coordinate_localOverflowBoundary`, and
  `QRTour.Prime97.coordinate_isLocalOverflowBoundary_iff` - just before the
  local-overflow boundary, the raw coefficient still has zero overflow
  quotient, and the adjacent local-overflow boundary also occurs exactly at
  block `4`, so block `5` is the first raw overflow
* `QRTour.Prime97.coordinate_lookaheadCertificate_six_one`,
  `QRTour.Prime97.coordinate_visibleCarryWord_eq_emittedBlockWord_six_one`,
  `QRTour.Prime97.coordinate_lookaheadCertificate_six_three`,
  `QRTour.Prime97.coordinate_visibleCarryWord_six_one_eq_six_three`,
  `QRTour.Prime97.coordinate_visibleCarryWord_eq_emittedBlockWord_six_three`,
  `QRTour.Prime97.coordinate_visibleCarryWord_six_three_eq_blocks`, and
  `QRTour.Prime97.coordinate_stateAlignments_output_agreement_six_three`, and
  `QRTour.Prime97.coordinate_stateAlignments_output_agreement_pointwise_six_three` -
  on the canonical `(requestedBlocks=6)` prime-`97` witness, one block of
  lookahead already certifies the visible carried word and the larger
  `(lookahead=3)` window preserves that same six-block prefix, the visible
  carried word already agrees with the emitted six-block word on both
  certified windows, that stabilized word is concretely
  `[1, 3, 9, 27, 83, 50]`, and the aligned carry/remainder outputs agree at
  both the whole-window and pointwise levels on the larger stabilized window

## Composite 21 Results

* `QRTour.Composite21.order_of_decimalUnitMod3` and
  `QRTour.Composite21.order_of_decimalUnitMod7` - the decimal base has local
  orders `1` and `6` modulo `3` and `7`
* `QRTour.Composite21.decimalUnit_order_eq_lcm_component_orders` - the global
  decimal order modulo `21` is exactly the least common multiple of those
  local orders via the pairwise CRT theorem
* `QRTour.Composite21.order_of_decimalUnitMod21` - concretely,
  `ord_21(10) = 6 = lcm(1, 6)`

## Composite 249 Results

* `QRTour.Composite249.coordinate_goodMode` - `249 < 10^3`, so this decimal
  block coordinate is a good mode
* `QRTour.Composite249.coordinate_quotientQ_eq_four` and
  `QRTour.Composite249.coordinate_remainderK_eq_four` - the Euclidean data in
  `1000 = 4*249 + 4`
* `QRTour.Composite249.coordinate_positive_q_good_modes` - the canonical
  positive-`q` witness beneath the good-mode positivity theorem
* `QRTour.Composite249.coordinate_series_q_weighted_identity` and
  `QRTour.Composite249.coordinate_partialSumQ_four_eq_finite` - the same
  coordinate witnesses both the infinite q-weighted series identity and the
  four-term exact finite prefix identity outside the special `q = 1` bridge
  case
* `QRTour.Composite249.coordinate_bodyTerm_four_eq_polynomial` and
  `QRTour.Composite249.coordinate_bodyTerm_five_recurrence` - the finite body
  term already exposes the raw coefficients `4, 16, 64, 256`, and the next
  recurrence appends the overflowing coefficient `1024` before carry
  normalization
* `QRTour.Composite249.coordinate_firstIncomingCarryPosition`,
  `QRTour.Composite249.coordinate_isFirstIncomingCarryPosition_iff`,
  `QRTour.Composite249.coordinate_incomingCarry_two_eq_zero`, and
  `QRTour.Composite249.coordinate_incomingCarry_three_eq_one` - the first
  incoming carry occurs exactly at block `3`, with zero carry just before the
  boundary and carry `1` at the boundary itself
* `QRTour.Composite249.coordinate_localOverflowBoundary`,
  `QRTour.Composite249.coordinate_isLocalOverflowBoundary_iff`, and
  `QRTour.Composite249.coordinate_firstVisibleMismatchPosition_eq_three` - the
  adjacent local-overflow boundary is also exactly `3`, so block `4` is the
  first raw overflow and the first visible mismatch is still `3`
* `QRTour.Composite249.coordinate_lookaheadCertificate_three_zero`,
  `QRTour.Composite249.coordinate_visibleCarryWord_eq_emittedBlockWord_three_zero`,
  `QRTour.Composite249.coordinate_visibleCarryWord_three_zero_eq_blocks`, and
  `QRTour.Composite249.coordinate_stateAlignments_output_agreement_three_zero`,
  and
  `QRTour.Composite249.coordinate_stateAlignments_output_agreement_pointwise_three_zero`
  - on the carry-free `(requestedBlocks=3, lookahead=0)` window, zero
  lookahead already certifies the stabilized visible word `[4, 16, 64]`, and
  the aligned carry/remainder outputs agree at both the whole-window and
  pointwise levels

## Same-Core 996 over 249 Results

* `QRTour.Composite996.preperiodSteps_eq_two`,
  `QRTour.Composite996.basePrimeSupportFactor_eq_four`,
  `QRTour.Composite996.strippedPeriodModulus_eq_249`,
  `QRTour.Composite996.sameCore_remainderK_eq`, and
  `QRTour.Composite996.sameCore_basePrimeSupportFactor_eq_remainderK_pow_one`,
  `QRTour.Composite996.sameCore_denominator_eq_249_mul_remainderK_pow_one`,
  `QRTour.Composite996.sameCore_denominator_eq_249_mul_coreRemainderK_pow_one`,
  and
  `QRTour.Composite996.sameCore_quotientQ_scaling`, and
  `QRTour.Composite996.sameCore_quotientQ_scaling_eq_remainderK_pow_one` - the
  canonical decimal preperiod, base-prime support factor, stripped-core data,
  exact shared remainder identity `k_core = k_actual = 4`, the exact `k^1`
  specialization `basePrimeSupportFactor 10 996 = k_core^1 = k_actual^1`,
  the exact same-core denominator identity `996 = 249 * k^1`, exposed as both
  `996 = 249 * k_actual^1` and `996 = 249 * k_core^1`, and exact
  quotient-scaling identities `q_core = q_actual * 4 = q_actual * k^1`,
  including the exact product decomposition `996 = 4 * 249`
* `QRTour.Composite996.actual996_sameCore` - the actual denominator and stripped
  periodic core form a same-core family
* `QRTour.Composite996.sameCore_firstIncomingCarryPosition_shift_exact` - the
  first incoming-carry boundary shifts by exactly one block
* `QRTour.Composite996.sameCore_localOverflowBoundary_shift_exact` - the local
  overflow boundary also shifts by exactly one block
* `QRTour.Composite996.sameCore_localOverflowBoundary_via_overflowQuotient` -
  that same local-overflow shift is also exposed concretely through the
  overflow-quotient inequalities on blocks `3/4` for the stripped core and
  `4/5` for the actual denominator
* `QRTour.Composite996.core249_firstVisibleMismatchPosition_eq_three` and
  `QRTour.Composite996.actual996_firstVisibleMismatchPosition_eq_four` - the
  stripped core and actual denominator then have concrete first visible
  mismatch positions `3` and `4`
* `QRTour.Composite996.sameCore_firstVisibleMismatchPosition_shift_exact` - the
  first visible mismatch boundary then follows by the same exact one-block shift
* `QRTour.Composite996.sameCore_lookaheadCertificateHolds_iff_add_exact` - the
  exact fixed-window lookahead certificate transports between the stripped-core
  window `(n, L)` and the shifted actual window `(n+1, L)`
* `QRTour.Composite996.sameCore_tailMassLowerBound_iff_add_exact` - on the
  canonical `3/0 -> 4/0` same-core window pair, the raw tail-mass lower-bound
  inequality itself is equivalent between the shifted actual denominator and
  the stripped core
* `QRTour.Composite996.actual996_tailMassLowerBound_of_core_lookaheadCertificate_exact`
  and
  `QRTour.Composite996.core249_tailMassLowerBound_of_actual_lookaheadCertificate_exact`
  - on the canonical `3/0 -> 4/0` same-core window pair, the exact
  certificate transport also yields forward and reverse raw tail-mass
  lower-bound implications
* `QRTour.Composite996.actual996_visibleCarryWord_eq_emittedBlockWord_of_core_lookaheadCertificate`
  and
  `QRTour.Composite996.actual996_visibleCarryPairs_output_agreement_of_core_lookaheadCertificate`,
  `QRTour.Composite996.actual996_visibleCarryPairs_output_agreement_pointwise_of_core_lookaheadCertificate`,
  `QRTour.Composite996.actual996_visibleCarryPairs_carry_balance`,
  `QRTour.Composite996.actual996_visibleCarryPairs_remainder_balance`,
  `QRTour.Composite996.core249_visibleCarryWord_eq_emittedBlockWord_of_actual_lookaheadCertificate`,
  `QRTour.Composite996.core249_visibleCarryPairs_output_agreement_of_actual_lookaheadCertificate`,
  `QRTour.Composite996.core249_visibleCarryPairs_output_agreement_pointwise_of_actual_lookaheadCertificate`,
  `QRTour.Composite996.core249_visibleCarryPairs_carry_balance`, and
  `QRTour.Composite996.core249_visibleCarryPairs_remainder_balance`
  - on the canonical `3/0 -> 4/0` same-core window pair, the exact
  certificate transport already yields forward and reverse visible-word and
  pair-output agreement implications, and both the shifted actual `4/0` window
  and the stripped-core `3/0` window now also expose the pointwise carry- and
  remainder-balance equations for each visible pair
* `QRTour.Composite996.actual996_stateAlignments_output_agreement_of_core_lookaheadCertificate`
  and
  `QRTour.Composite996.actual996_stateAlignments_output_agreement_pointwise_of_core_lookaheadCertificate`,
  `QRTour.Composite996.core249_stateAlignments_output_agreement_of_actual_lookaheadCertificate`,
  and
  `QRTour.Composite996.core249_stateAlignments_output_agreement_pointwise_of_actual_lookaheadCertificate`
  - on that same canonical window pair, the exact certificate transport also
  yields forward and reverse aligned-output agreement implications, both at
  the whole-window and pointwise levels
* `QRTour.Composite996.actual996_visibleCarryWord_eq_emittedBlockWord` - the
  shifted actual window satisfies visible carry/output agreement under the
  coarse stripped-core inequality
* `QRTour.Composite996.actual996_visibleCarryWord_four_zero_eq_blocks` - the
  same shifted actual `4/0` window concretely stabilizes at the visible
  four-block word `[1, 4, 16, 64]`
* `QRTour.Composite996.actual996_visibleCarryPairs_output_agreement`,
  `QRTour.Composite996.actual996_visibleCarryPairs_output_agreement_pointwise`,
  `QRTour.Composite996.actual996_stateAlignments_output_agreement`, and
  `QRTour.Composite996.actual996_stateAlignments_output_agreement_pointwise`
  - the same coarse condition also certifies pair-output and aligned
  carry/remainder output agreement on the shifted actual window, both at the
  whole-window and pointwise levels
* `QRTour.Composite996.actual996_stateAlignments_coefficient_shift_exact`,
  `QRTour.Composite996.actual996_stateAlignments_carryIn_shift_exact`,
  `QRTour.Composite996.actual996_stateAlignments_carryOut_shift_exact`,
  `QRTour.Composite996.actual996_stateAlignments_remainderIn_shift_exact`,
  `QRTour.Composite996.actual996_stateAlignments_carryBlockValue_shift_exact`,
  `QRTour.Composite996.actual996_stateAlignments_remainderBlockValue_shift_exact`,
  and `QRTour.Composite996.actual996_stateAlignments_remainderOut_shift_exact`
  - on the canonical `3/0 -> 4/0` same-core window pair, the shifted actual
  raw coefficients, carry states, carried block values, and carry outputs
  match the stripped core one block later, the aligned current and next-step
  remainder states are exactly scaled by the shared remainder `k = 4`, and the
  aligned emitted block values still match pointwise
* `QRTour.Composite996.core249_visibleCarryWord_eq_emittedBlockWord` - the
  reverse same-core wrapper certifies visible-word agreement on the unshifted
  stripped-core window under the shifted actual inequality
* `QRTour.Composite996.core249_visibleCarryWord_three_zero_eq_blocks` and
  `QRTour.Composite996.sameCore_visibleCarryWord_shift_exact` - the stripped
  core `3/0` window concretely stabilizes at `[4, 16, 64]`, and the shifted
  actual `4/0` visible word is exactly `1 ::` that stripped-core word on the
  canonical one-block same-core shift
* `QRTour.Composite996.core249_visibleCarryPairs_output_agreement`,
  `QRTour.Composite996.core249_visibleCarryPairs_output_agreement_pointwise`,
  `QRTour.Composite996.core249_stateAlignments_output_agreement`, and
  `QRTour.Composite996.core249_stateAlignments_output_agreement_pointwise`
  - the reverse same-core wrapper also certifies pair-output and aligned
  carry/remainder output agreement on the stripped-core window, again at both
  the whole-window and pointwise levels
* `QRTour.Composite996.actual996_stateAlignments_remainderToCarryStepFunctional`
  - the shifted actual window also yields a functional observed map from
  remainder states to `(carryIn, carryOut)` pairs
* `QRTour.Composite996.core249_carryToRemainderFunctional_one_zero`,
  `QRTour.Composite996.actual996_carryToRemainder_conflict_two_zero`, and
  `QRTour.Composite996.sameCore_carryToRemainderTransport_counterexample` -
  on the exact one-block same-core pair `1/0 -> 2/0`, the stripped core is
  carry-to-remainder functional, the shifted actual denominator already shows
  a direct `carryIn = 0` conflict between two distinct remainder states, and
  the combined counterexample therefore rules out forward same-core
  `carryToRemainderFunctional` transport
* `QRTour.Composite996.actual996_not_carryToRemainderFunctional` - on that
  same shifted actual window, the reverse observed map already fails, so the
  example stays visibly asymmetric beneath the open carry-factorization claim
* `QRTour.Composite996.actual996_stateAlignments_remainderToCarry_transition_compatible`
  - matching remainder states and raw coefficients on the shifted actual
  window force matching carry state, block values, and next-step outputs
* `QRTour.Composite996.actual996_quotientOnly_profile` - on the larger
  `(requestedBlocks=8, lookaheadBlocks=1)` selector-family window, the same
  composite example is still quotient-only: remainder-to-carry is functional,
  but carry-to-remainder is not
* `QRTour.Composite996.core249_remainderToCarryFunctional` and
  `QRTour.Composite996.core249_stateAlignments_remainderToCarry_transition_compatible`
  - the reverse same-core wrapper transports observed remainder-to-carry
  functionality and the matching finite transition-compatibility witness back
  to the stripped core
* `QRTour.Composite996.core249_not_carryToRemainderFunctional` - the dual
  carry-to-remainder map still fails there
-/

namespace QRTour.Prime19

/-! ### Prime 19 -/

/-- 19 is prime. -/
instance : Fact (Nat.Prime 19) := ⟨by native_decide⟩

/-- Decimal base `10` is coprime to `19`. -/
theorem base_coprime : Nat.Coprime 10 19 := by native_decide

/-- Decimal base `10` as a unit in `ZMod 19`. -/
def decimalUnit : (ZMod 19)ˣ := Units.mk0 (10 : ZMod 19) (by decide)

/-- Decimal base `10` has multiplicative order `18` mod `19`. -/
theorem order_of_decimalUnit : orderOf decimalUnit = 18 := by
  rw [orderOf_eq_iff (by decide : 0 < 18)]
  constructor
  · native_decide
  · intro m hm hm_pos
    interval_cases m <;> native_decide

/-- The decimal reptend period of `1/19` is exactly `18`. -/
theorem reptendPeriod_eq_eighteen : reptendPeriod 19 10 base_coprime = 18 := by
  unfold reptendPeriod
  simpa [decimalUnit] using order_of_decimalUnit

/-- The first decimal digit step is the Euclidean equation `10*1 = 0*19 + 10`. -/
theorem digit_remainder_step_zero :
    scaledRemainder 19 10 0 = digit 19 10 0 * 19 + (remainder (p := 19) 10 1).val := by
  simpa using digit_remainder_eq (p := 19) 10 0

/-- The decimal digits of `1/19` repeat after `18` positions. -/
theorem digit_periodic_decimal (n : ℕ) : digit 19 10 (n + 18) = digit 19 10 n := by
  simpa [reptendPeriod_eq_eighteen] using digit_periodic (p := 19) 10 base_coprime n

end QRTour.Prime19

namespace QRTour.Prime97

/-! ### Prime 97 -/

/-- 97 is prime. -/
instance : Fact (Nat.Prime 97) := ⟨by native_decide⟩

/-- 97 ≠ 2 (it's an odd prime). -/
theorem p_ne_two : (97 : ℕ) ≠ 2 := by decide

/-! ### Base-Stride Configuration -/

/-- The base-stride configuration for p=97, B=10, m=2. -/
def bs : BaseStride 97 where
  B := 10
  m := 2
  hB_coprime := by native_decide
  hm_pos := by decide

/-! ### Computational Verifications -/

/-- 10² mod 97 = 3 -/
example : (10 : ZMod 97) ^ 2 = 3 := by native_decide

/-- k = 3 as an element of ZMod 97 -/
theorem k_eq_three : (bs.k : ZMod 97) = 3 := by native_decide

/-- half 97 = 48 -/
example : half 97 = 48 := by native_decide

/-- 3^48 = 1 in (ZMod 97)ˣ -/
theorem three_pow_48_eq_one : (3 : ZMod 97) ^ 48 = 1 := by native_decide

/-- The first few remainders in the stride-2 sequence -/
example : strideRemainder bs 0 = 1 := by native_decide  -- 10^0 = 1
example : strideRemainder bs 1 = 3 := by native_decide  -- 10^2 = 100 ≡ 3
example : strideRemainder bs 2 = 9 := by native_decide  -- 10^4 ≡ 3² = 9
example : strideRemainder bs 3 = 27 := by native_decide -- 10^6 ≡ 3³ = 27
example : strideRemainder bs 4 = 81 := by native_decide -- 10^8 ≡ 3⁴ = 81

/-! ### Order of 3

Proving that ord₉₇(3) = 48 is the key fact.

We certify it by showing `3^48 = 1` and then ruling out every smaller positive
exponent with a finite case split.
-/

/-- 3 has order 48 in (ZMod 97)ˣ.

This is verified by checking:
1. 3^48 = 1 (so orderOf 3 | 48)
2. 3^k ≠ 1 for all proper divisors k of 48
-/
theorem order_of_three : orderOf (Units.mk0 (3 : ZMod 97) (by decide)) = 48 := by
  rw [orderOf_eq_iff (by decide : 0 < 48)]
  constructor
  · native_decide  -- 3^48 = 1
  · intro m hm hm_pos
    -- For m < 48 with m > 0, we need 3^m ≠ 1
    -- The only values we need to check are divisors of 48: 1, 2, 3, 4, 6, 8, 12, 16, 24
    interval_cases m <;> native_decide

/-! ### 3 is a Quadratic Residue

3 is a QR mod 97 because it's a power of 10, which is itself a QR.
-/

/-- 10² ≡ 3 (mod 97), so 3 is a quadratic residue.

We compute 10² = 100 ≡ 3 (mod 97).  -/
theorem three_is_square : IsSquare (3 : ZMod 97) := by
  use 10
  native_decide

/-! ### 3 is a QR Generator -/

/-- 3 (or rather, Units.mk0 3 _) is a QR generator for p = 97.

This means:
1. 3 is a quadratic residue mod 97
2. ord₉₇(3) = 48 = (97-1)/2
-/
theorem k_is_qr_generator : QRGenerator bs.k := by
  constructor
  · -- 3 is a QR
    rw [k_eq_three]
    exact three_is_square
  · -- orderOf = 48 = half 97
    have h : bs.k = Units.mk0 (3 : ZMod 97) (by decide) := by
      ext
      exact k_eq_three
    rw [h, order_of_three]
    native_decide

/-! ### The Main Theorem Applied -/

/-- The QR tour theorem for p = 97:
Every quadratic residue mod 97 appears as strideRemainder bs j for some j < 48. -/
theorem qr_tour : ∀ a : (ZMod 97)ˣ, IsSquare (a : ZMod 97) →
    ∃ j : ℕ, j < 48 ∧ strideRemainder bs j = a :=
  qr_tour_cover bs p_ne_two k_is_qr_generator

/-! ### Explicit Enumeration

We can explicitly list the 48 quadratic residues by computing 3^j for j = 0..47.
-/

/-- The 48 quadratic residues mod 97, in the order visited by the QR tour. -/
def qrList : List (ZMod 97) :=
  List.map (fun j => strideRemainder bs j) (List.range 48)

/-! ### Primitive Root: 5 is a Full Generator

5 is a primitive root mod 97, meaning ord₉₇(5) = 96 = 97 - 1.
Its powers enumerate ALL nonzero residues mod 97.
-/

/-- 5 is nonzero in ZMod 97. -/
theorem five_ne_zero : (5 : ZMod 97) ≠ 0 := by decide

/-- 5 as a unit in (ZMod 97)ˣ. -/
def five_unit : (ZMod 97)ˣ := Units.mk0 5 five_ne_zero

/-- 5^96 = 1 in ZMod 97. -/
example : (5 : ZMod 97) ^ 96 = 1 := by native_decide

/-- 5 has order 96 = p - 1 in (ZMod 97)ˣ, making it a primitive root. -/
theorem order_of_five : orderOf five_unit = 96 := by
  rw [orderOf_eq_iff (by decide : 0 < 96)]
  constructor
  · native_decide  -- 5^96 = 1
  · intro m hm hm_pos
    -- For m < 96 with m > 0, we need 5^m ≠ 1
    -- Divisors of 96: 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48
    interval_cases m <;> native_decide

/-- 5 is a full generator (primitive root) of (ZMod 97)ˣ. -/
theorem five_is_full_generator : FullGenerator five_unit where
  order_eq := order_of_five

/-- At the `FullGenerator` level, a power of `5` is QR-generating exactly when
its exponent is even and the halved exponent is coprime to `48 = (97-1)/2`. -/
theorem five_pow_is_qr_generator_iff (m : ℕ) :
    QRGenerator (five_unit ^ m) ↔ Even m ∧ Nat.Coprime (half 97) (m / 2) := by
  simpa using
    full_generator_pow_isQRGenerator_iff
      (p := 97) p_ne_two five_unit five_is_full_generator m

/-- 5² = 25 mod 97, which is a QR generator (has order 48). -/
theorem five_sq_is_qr_generator : QRGenerator (five_unit ^ 2) := by
  exact (five_pow_is_qr_generator_iff 2).2 (by native_decide)

/-- Exactly `φ((97-1)/2)` powers of the primitive root `5` are QR generators. -/
theorem five_qr_generator_pow_count :
    Finset.card ((Finset.range (97 - 1)).filter (fun m => QRGenerator (five_unit ^ m))) =
      Nat.totient (half 97) := by
  simpa using
    full_generator_qrGenerator_pow_count_eq_totient
      (p := 97) p_ne_two five_unit five_is_full_generator

/-- Concretely, the powers of `5` yield exactly `16` QR generators mod `97`. -/
example :
    Finset.card ((Finset.range 96).filter (fun m => QRGenerator (five_unit ^ m))) = 16 := by
  rw [show (96 : ℕ) = 97 - 1 by decide]
  rw [five_qr_generator_pow_count]
  native_decide

/-! ### Bridge Prime: 97 = 10² - 3

97 is a "bridge prime" because 97 = 100 - 3 = 10² - 3.
This means 10² ≡ 3 (mod 97), giving beautiful block structure in the reptend.
-/

/-- 97 = 10² - 3 is a bridge prime configuration. -/
theorem bridge_97_demo : Bridge 10 97 2 3 := bridge_97

/-- The same bridge packaged as the canonical signed-bridge witness. -/
def signedBridge : SignedBridge 10 97 2 .minus 3 := bridge_97_demo.toSignedBridge

/-- Block-starting remainders form powers of 3:
r[0] = 1 = 3⁰, r[2] = 3¹, r[4] = 3², etc. -/
example : @remainder 97 _ 10 0 = 3 ^ 0 := by native_decide
example : @remainder 97 _ 10 2 = 3 ^ 1 := by native_decide
example : @remainder 97 _ 10 4 = 3 ^ 2 := by native_decide
example : @remainder 97 _ 10 6 = 3 ^ 3 := by native_decide

/-- The k-step recurrence: r[n+2] = 3 × r[n] for any n.
This is the bridge property in action! -/
example : @remainder 97 _ 10 (0 + 2) = 3 * @remainder 97 _ 10 0 := by native_decide
example : @remainder 97 _ 10 (5 + 2) = 3 * @remainder 97 _ 10 5 := by native_decide
example : @remainder 97 _ 10 (10 + 2) = 3 * @remainder 97 _ 10 10 := by native_decide

/-- The canonical signed-bridge recurrence for the 97 witness. -/
theorem signedBridge_remainder_k_step (n : ℕ) :
    @remainder 97 _ 10 (n + 2) = (3 : ZMod 97) * @remainder 97 _ 10 n := by
  simpa [signedBridge, SignedBridge.multiplier, BridgeSign.toInt] using
    signedBridge.remainder_k_step n

/-- After two stride steps, the sign cancels and the 97 witness advances by `3²`. -/
theorem signedBridge_remainder_2k_step (n : ℕ) :
    @remainder 97 _ 10 (n + 4) = (3 : ZMod 97) ^ 2 * @remainder 97 _ 10 n := by
  simpa [signedBridge] using signedBridge.remainder_2k_step n

/-- The stride-2 block values in the canonical 97 witness are exactly powers of `3`. -/
theorem bridge_blockValue_eq_pow (j : ℕ) :
    blockValue (p := 97) 10 2 j = (3 : ZMod 97) ^ j := by
  simpa [bridge_97_demo] using bridge_97_demo.blockValue_eq_pow j

/-- The block-value period for the canonical 97 bridge is exactly `48`. -/
theorem bridgeOrder_eq_forty_eight : bridgeOrder bridge_97_demo = 48 := by
  change orderOf (Units.mk0 (3 : ZMod 97) bridge_97_demo.d_ne_zero) = 48
  have hunit :
      Units.mk0 (3 : ZMod 97) bridge_97_demo.d_ne_zero =
        Units.mk0 (3 : ZMod 97) (by decide) := by
    ext
    rfl
  rw [hunit, order_of_three]

/-- The stride-2 block values repeat with period `48`. -/
theorem bridge_blockValue_periodic (j : ℕ) :
    blockValue (p := 97) 10 2 (j + 48) = blockValue (p := 97) 10 2 j := by
  simpa [bridgeOrder_eq_forty_eight] using bridge_97_demo.blockValue_periodic j

/-! ### Exact Block Coordinate Witness

The same canonical tuple `(base=10, N=97, stride=2, B=100, q=1, k=3)` also
serves as the standard Lean witness for the q-weighted series layer, the exact
finite prefix identity in the `q = 1` bridge case, and the first incoming-carry
boundary.
-/

/-- The canonical block coordinate `(base=10, N=97, stride=2)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 97
  stride := 2
  modulus_pos := by decide

/-- The canonical 97 block coordinate is a good mode: `97 < 10^2`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The block base for the canonical coordinate is `100`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 100 := by
  native_decide

/-- The quotient in `100 = q*97 + k` is `q = 1`. -/
theorem coordinate_quotientQ_eq_one : coordinate.quotientQ = 1 := by
  native_decide

/-- The remainder in `100 = q*97 + k` is `k = 3`. -/
theorem coordinate_remainderK_eq_three : coordinate.remainderK = 3 := by
  native_decide

/-- The canonical 97 coordinate witnesses the exact q-weighted series identity. -/
theorem coordinate_series_q_weighted_identity :
    HasSum (fun j : ℕ => coordinate.seriesTermR j) ((1 : ℝ) / 97) := by
  simpa [coordinate] using coordinate.series_q_weighted_identity coordinate_goodMode

/-- The first four q-weighted terms already satisfy the exact finite closed
form `(100^4 - 3^4) / (97 * 100^4)` in the `q = 1` bridge case. -/
theorem coordinate_partialSumQ_four_eq_finite :
    coordinate.partialSumQ 4 =
      (((100 : ℚ) ^ 4 - (3 : ℚ) ^ 4) / ((97 : ℚ) * (100 : ℚ) ^ 4)) := by
  simpa [coordinate, BlockCoordinate.blockBase, BlockCoordinate.remainderK] using
    coordinate.partialSumQ_eq_finite coordinate_goodMode 4

/-! ### Finite Body-Term Witnesses

The canonical tuple `(base=10, N=97, stride=2)` also exercises the finite
`OrbitWeave` support layer: the body term is both the base-`100` polynomial in
the raw coefficients and a one-step recurrence that shifts by `100` and
appends the next raw coefficient.
-/

/-- The four-block body term is the base-`100` polynomial with raw
coefficients `1, 3, 9, 27`. -/
theorem coordinate_bodyTerm_four_eq_polynomial :
    coordinate.bodyTerm 4 = 1 * 100 ^ 3 + 3 * 100 ^ 2 + 9 * 100 + 27 := by
  rw [coordinate.bodyTerm_eq_sum_rawCoefficients 4]
  native_decide

/-- Extending the finite body term by one block shifts by `100` and appends
the next raw coefficient `81`. -/
theorem coordinate_bodyTerm_five_recurrence :
    coordinate.bodyTerm 5 = 100 * coordinate.bodyTerm 4 + 81 := by
  rw [coordinate.bodyTerm_recurrence 4]
  native_decide

/-- The first incoming carry occurs at block `4` for the canonical 97 coordinate. -/
theorem coordinate_firstIncomingCarryPosition :
    coordinate.isFirstIncomingCarryPosition 4 := by
  change 1 * 3 ^ 4 < 100 - 3 ∧ 100 - 3 ≤ 1 * 3 ^ (4 + 1)
  native_decide

/-- The canonical 97 coordinate has a unique first incoming-carry boundary,
and it occurs exactly at block `4`. -/
theorem coordinate_isFirstIncomingCarryPosition_iff (j : ℕ) :
    coordinate.isFirstIncomingCarryPosition j ↔ j = 4 := by
  constructor
  · intro hj
    have hk : 1 < coordinate.remainderK := by
      rw [coordinate_remainderK_eq_three]
      decide
    exact coordinate.isFirstIncomingCarryPosition_unique hk hj coordinate_firstIncomingCarryPosition
  · intro hj
    simpa [hj] using coordinate_firstIncomingCarryPosition

/-- Just before that threshold, the incoming carry is still zero. -/
theorem coordinate_incomingCarry_three_eq_zero : coordinate.incomingCarry 3 = 0 := by
  rw [coordinate.incomingCarry_eq_zero_iff coordinate_goodMode 3]
  native_decide

/-- At the first incoming-carry boundary, the next raw coefficient contributes carry `2`. -/
theorem coordinate_incomingCarry_four_eq_two : coordinate.incomingCarry 4 = 2 := by
  native_decide

/-- Just before the first local-overflow boundary, the current raw coefficient
still has zero block-base overflow quotient. -/
theorem coordinate_overflowQuotient_four_eq_zero :
    coordinate.rawCoefficient 4 / coordinate.blockBase = 0 := by
  rw [coordinate.rawCoefficient_div_blockBase_eq_zero_iff coordinate_goodMode 4]
  native_decide

/-- The adjacent local-overflow boundary in the canonical 97 coordinate is at
`4`, so block `5` is the first raw coefficient that overflows `100`. -/
theorem coordinate_localOverflowBoundary :
    coordinate.isLocalOverflowBoundary 4 := by
  rw [coordinate.isLocalOverflowBoundary_iff_overflowQuotients coordinate_goodMode 4]
  constructor
  · exact coordinate_overflowQuotient_four_eq_zero
  · native_decide

/-- The canonical 97 coordinate has a unique local-overflow boundary, and it
occurs exactly at block `4`. -/
theorem coordinate_isLocalOverflowBoundary_iff (j : ℕ) :
    coordinate.isLocalOverflowBoundary j ↔ j = 4 := by
  constructor
  · intro hj
    have hk : 1 < coordinate.remainderK := by
      rw [coordinate_remainderK_eq_three]
      decide
    exact coordinate.isLocalOverflowBoundary_unique hk hj coordinate_localOverflowBoundary
  · intro hj
    simpa [hj] using coordinate_localOverflowBoundary

/-! ### Finite Carry-Window Witness

The same canonical `97` coordinate also packages the finite-window carried-word
agreement witness behind `carry_window_transducer`.
-/

/-- On the six-block `97` witness, one block of lookahead already certifies
stabilized visible output. -/
theorem coordinate_lookaheadCertificate_six_one :
    coordinate.lookaheadCertificateHolds 6 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds BlockCoordinate.lookaheadGapNumerator
    coordinate
  native_decide

/-- On the same six-block `97` witness, three blocks of lookahead also certify
stabilized visible output. -/
theorem coordinate_lookaheadCertificate_six_three :
    coordinate.lookaheadCertificateHolds 6 3 := by
  exact coordinate.lookaheadCertificateHolds_of_lookaheadCertificate_add
    coordinate_goodMode 6 1 2 coordinate_lookaheadCertificate_six_one

/-- On the smaller `6/1` prime-`97` window, the visible carried word already
agrees with the emitted six-block word. -/
theorem coordinate_visibleCarryWord_eq_emittedBlockWord_six_one :
    coordinate.visibleCarryWord coordinate_goodMode 6 1 = coordinate.emittedBlockWord 6 := by
  exact coordinate.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate
    coordinate_goodMode (by native_decide) 6 1 coordinate_lookaheadCertificate_six_one

/-- Once the `6/1` prime-`97` window is certified, the larger `6/3` lookahead
window carries the same visible six-block prefix. -/
theorem coordinate_visibleCarryWord_six_one_eq_six_three :
    coordinate.visibleCarryWord coordinate_goodMode 6 1 =
      coordinate.visibleCarryWord coordinate_goodMode 6 3 := by
  exact coordinate.visibleCarryWord_eq_of_lookaheadCertificate_le
    coordinate_goodMode (by native_decide) 6 1 3 (by native_decide)
      coordinate_lookaheadCertificate_six_one

/-- On that same finite window, the visible carried word agrees with the
emitted six-block word. -/
theorem coordinate_visibleCarryWord_eq_emittedBlockWord_six_three :
    coordinate.visibleCarryWord coordinate_goodMode 6 3 = coordinate.emittedBlockWord 6 := by
  exact coordinate.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate
    coordinate_goodMode (by native_decide) 6 3 coordinate_lookaheadCertificate_six_three

/-- Concretely, the stabilized visible six-block word is
`[1, 3, 9, 27, 83, 50]`. -/
theorem coordinate_visibleCarryWord_six_three_eq_blocks :
    coordinate.visibleCarryWord coordinate_goodMode 6 3 = [1, 3, 9, 27, 83, 50] := by
  rw [coordinate_visibleCarryWord_eq_emittedBlockWord_six_three]
  native_decide

/-- The aligned carry-trace and remainder-trace outputs agree on the same
stabilized six-block prime-`97` window. -/
theorem coordinate_stateAlignments_output_agreement_six_three :
    (coordinate.stateAlignments coordinate_goodMode 6 3).map StateAlignment.carryBlockValue =
      (coordinate.stateAlignments coordinate_goodMode 6 3).map StateAlignment.remainderBlockValue := by
  exact coordinate.stateAlignments_output_agreement_of_lookaheadCertificate
    coordinate_goodMode (by native_decide) 6 3 coordinate_lookaheadCertificate_six_three

/-- On the same stabilized six-block prime-`97` window, each aligned carry
block value matches the corresponding remainder block value pointwise. -/
theorem coordinate_stateAlignments_output_agreement_pointwise_six_three
    (i : ℕ)
    (hi : i < (coordinate.stateAlignments coordinate_goodMode 6 3).length) :
    ((coordinate.stateAlignments coordinate_goodMode 6 3)[i]'hi).carryBlockValue =
      ((coordinate.stateAlignments coordinate_goodMode 6 3)[i]'hi).remainderBlockValue := by
  exact coordinate.stateAlignments_output_agreement_pointwise_of_lookaheadCertificate
    coordinate_goodMode (by native_decide) 6 3 coordinate_lookaheadCertificate_six_three i hi

/-! ### Digit Examples

The reptend digits of 1/97 in base 10.
-/

/-- First few digits of 1/97 in decimal. -/
example : digit 97 10 0 = 0 := by native_decide  -- First digit is 0 (1 × 10 = 10 < 97)
example : digit 97 10 1 = 1 := by native_decide  -- 10 × 10 = 100, 100/97 = 1
example : digit 97 10 2 = 0 := by native_decide  -- 3 × 10 = 30 < 97
example : digit 97 10 3 = 3 := by native_decide  -- 30 × 10 = 300, 300/97 = 3

end QRTour.Prime97

namespace QRTour.Composite21

/-! ### Composite 21 -/

/-- Decimal base `10` as a unit in `ZMod 3`. -/
def decimalUnitMod3 : (ZMod 3)ˣ := ZMod.unitOfCoprime 10 (by native_decide : Nat.Coprime 10 3)

/-- Decimal base `10` as a unit in `ZMod 7`. -/
def decimalUnitMod7 : (ZMod 7)ˣ := ZMod.unitOfCoprime 10 (by native_decide : Nat.Coprime 10 7)

/-- Decimal base `10` as a unit in `ZMod 21`. -/
def decimalUnitMod21 : (ZMod 21)ˣ := ZMod.unitOfCoprime 10 (by native_decide : Nat.Coprime 10 21)

/-- Modulo `3`, the decimal base is literally the unit `1`. -/
theorem decimalUnitMod3_eq_one : decimalUnitMod3 = 1 := by
  ext
  native_decide

/-- The decimal base has local order `1` modulo `3`. -/
theorem order_of_decimalUnitMod3 : orderOf decimalUnitMod3 = 1 := by
  simp [decimalUnitMod3_eq_one]

/-- The decimal base has local order `6` modulo `7`. -/
theorem order_of_decimalUnitMod7 : orderOf decimalUnitMod7 = 6 := by
  rw [orderOf_eq_iff (by decide : 0 < 6)]
  constructor
  · native_decide
  · intro m hm hm_pos
    interval_cases m <;> native_decide

/-- Under CRT, the decimal base maps to its local `mod 3` and `mod 7` units. -/
theorem decimalUnit_components :
    unitsChineseRemainder (by decide : Nat.Coprime 3 7) decimalUnitMod21 =
      (decimalUnitMod3, decimalUnitMod7) := by
  ext <;> simp [unitsChineseRemainder, decimalUnitMod3, decimalUnitMod7, decimalUnitMod21]
  all_goals native_decide

/-- Under pairwise CRT, the global decimal order modulo `21` is the lcm of the local orders. -/
theorem decimalUnit_order_eq_lcm_component_orders :
    orderOf decimalUnitMod21 = Nat.lcm (orderOf decimalUnitMod3) (orderOf decimalUnitMod7) := by
  calc
    orderOf decimalUnitMod21 =
        orderOf (unitsChineseRemainder (by decide : Nat.Coprime 3 7) decimalUnitMod21) := by
      symm
      exact MulEquiv.orderOf_eq (unitsChineseRemainder (by decide : Nat.Coprime 3 7)) decimalUnitMod21
    _ = Nat.lcm (orderOf decimalUnitMod3) (orderOf decimalUnitMod7) := by
      rw [decimalUnit_components]
      exact Prod.orderOf_mk

/-- Concretely, the decimal base has order `6` modulo `21`. -/
theorem order_of_decimalUnitMod21 : orderOf decimalUnitMod21 = 6 := by
  simpa [order_of_decimalUnitMod3, order_of_decimalUnitMod7] using
    decimalUnit_order_eq_lcm_component_orders

end QRTour.Composite21

namespace QRTour.Composite249

/-! ### Positive-q Composite Example

This packages the canonical positive-`q` witness `(base=10, N=249, stride=3)`.
Here `10^3 = 4*249 + 4`, so the quotient and remainder coordinates are both
`4`, and the coordinate is a good mode because `249 < 10^3`.
-/

/-- The canonical positive-`q` block coordinate `(base=10, N=249, stride=3)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 249
  stride := 3
  modulus_pos := by decide

/-- The canonical 249 coordinate is a good mode: `249 < 10^3`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The block base for the canonical coordinate is `1000`. -/
theorem coordinate_blockBase_eq_thousand : coordinate.blockBase = 1000 := by
  native_decide

/-- The quotient in `1000 = q*249 + k` is `q = 4`. -/
theorem coordinate_quotientQ_eq_four : coordinate.quotientQ = 4 := by
  native_decide

/-- The remainder in `1000 = q*249 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- The canonical 249 coordinate witnesses the positive-`q` good-mode boundary. -/
theorem coordinate_positive_q_good_modes :
    0 < (coordinate.blockBase - coordinate.remainderK) / coordinate.modulus := by
  simpa [coordinate] using coordinate.positive_q_good_modes coordinate_goodMode

/-- The canonical 249 coordinate also witnesses the exact q-weighted series
identity with positive quotient `q = 4`. -/
theorem coordinate_series_q_weighted_identity :
    HasSum (fun j : ℕ => coordinate.seriesTermR j) ((1 : ℝ) / 249) := by
  simpa [coordinate] using coordinate.series_q_weighted_identity coordinate_goodMode

/-- The first four q-weighted terms already satisfy the exact finite closed
form `(1000^4 - 4^4) / (249 * 1000^4)`. -/
theorem coordinate_partialSumQ_four_eq_finite :
    coordinate.partialSumQ 4 =
      (((1000 : ℚ) ^ 4 - (4 : ℚ) ^ 4) / ((249 : ℚ) * (1000 : ℚ) ^ 4)) := by
  simpa [coordinate, BlockCoordinate.blockBase, BlockCoordinate.remainderK] using
    coordinate.partialSumQ_eq_finite coordinate_goodMode 4

/-- The four-block body term is the base-`1000` polynomial with raw
coefficients `4, 16, 64, 256`. -/
theorem coordinate_bodyTerm_four_eq_polynomial :
    coordinate.bodyTerm 4 = 4 * 1000 ^ 3 + 16 * 1000 ^ 2 + 64 * 1000 + 256 := by
  rw [coordinate.bodyTerm_eq_sum_rawCoefficients 4]
  native_decide

/-- Extending the finite body term by one block shifts by `1000` and appends
the next raw coefficient `1024`, which is already above the block base. -/
theorem coordinate_bodyTerm_five_recurrence :
    coordinate.bodyTerm 5 = 1000 * coordinate.bodyTerm 4 + 1024 := by
  rw [coordinate.bodyTerm_recurrence 4]
  native_decide

/-- The canonical 249 coordinate first receives incoming carry at block `3`. -/
theorem coordinate_firstIncomingCarryPosition :
    coordinate.isFirstIncomingCarryPosition 3 := by
  change 4 * 4 ^ 3 < 1000 - 4 ∧ 1000 - 4 ≤ 4 * 4 ^ (3 + 1)
  native_decide

/-- Just before that threshold, the incoming carry is still zero. -/
theorem coordinate_incomingCarry_two_eq_zero : coordinate.incomingCarry 2 = 0 := by
  rw [coordinate.incomingCarry_eq_zero_iff coordinate_goodMode 2]
  native_decide

/-- At the first incoming-carry boundary, the next raw coefficient contributes carry `1`. -/
theorem coordinate_incomingCarry_three_eq_one : coordinate.incomingCarry 3 = 1 := by
  native_decide

/-- The canonical positive-`q` example has a unique first incoming-carry
boundary, and it occurs exactly at block `3`. -/
theorem coordinate_isFirstIncomingCarryPosition_iff (j : ℕ) :
    coordinate.isFirstIncomingCarryPosition j ↔ j = 3 := by
  constructor
  · intro hj
    have hk : 1 < coordinate.remainderK := by
      rw [coordinate_remainderK_eq_four]
      decide
    exact coordinate.isFirstIncomingCarryPosition_unique hk hj coordinate_firstIncomingCarryPosition
  · intro hj
    simpa [hj] using coordinate_firstIncomingCarryPosition

/-! ### Finite Carry-Window Witness

The same canonical `249` coordinate also packages a short finite-window
agreement witness behind `carry_window_transducer`.
-/

/-- On the carry-free three-block `249` witness, zero lookahead already
certifies stabilized visible output. -/
theorem coordinate_lookaheadCertificate_three_zero :
    coordinate.lookaheadCertificateHolds 3 0 := by
  rw [coordinate.lookaheadCertificateHolds_zero_iff_remainderK_pow_lt_modulus
    coordinate_goodMode 3]
  native_decide

/-- On that same finite window, the visible carried word agrees with the
emitted three-block word. -/
theorem coordinate_visibleCarryWord_eq_emittedBlockWord_three_zero :
    coordinate.visibleCarryWord coordinate_goodMode 3 0 = coordinate.emittedBlockWord 3 := by
  exact coordinate.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate
    coordinate_goodMode (by native_decide) 3 0 coordinate_lookaheadCertificate_three_zero

/-- Concretely, the stabilized visible three-block word is `[4, 16, 64]`. -/
theorem coordinate_visibleCarryWord_three_zero_eq_blocks :
    coordinate.visibleCarryWord coordinate_goodMode 3 0 = [4, 16, 64] := by
  rw [coordinate_visibleCarryWord_eq_emittedBlockWord_three_zero]
  native_decide

/-- The aligned carry-trace and remainder-trace outputs agree on the same
stabilized three-block composite-`249` window. -/
theorem coordinate_stateAlignments_output_agreement_three_zero :
    (coordinate.stateAlignments coordinate_goodMode 3 0).map StateAlignment.carryBlockValue =
      (coordinate.stateAlignments coordinate_goodMode 3 0).map StateAlignment.remainderBlockValue := by
  exact coordinate.stateAlignments_output_agreement_of_lookaheadCertificate
    coordinate_goodMode (by native_decide) 3 0 coordinate_lookaheadCertificate_three_zero

/-- On the same stabilized three-block `249` window, each aligned carry output
matches the corresponding remainder output pointwise. -/
theorem coordinate_stateAlignments_output_agreement_pointwise_three_zero
    (i : ℕ) (hi : i < (coordinate.stateAlignments coordinate_goodMode 3 0).length) :
    ((coordinate.stateAlignments coordinate_goodMode 3 0)[i]'hi).carryBlockValue =
      ((coordinate.stateAlignments coordinate_goodMode 3 0)[i]'hi).remainderBlockValue := by
  exact coordinate.stateAlignments_output_agreement_pointwise_of_lookaheadCertificate
    coordinate_goodMode (by native_decide) 3 0 coordinate_lookaheadCertificate_three_zero i hi

/-- Just before the first local-overflow boundary, the current raw coefficient
still has zero block-base overflow quotient. -/
theorem coordinate_overflowQuotient_three_eq_zero :
    coordinate.rawCoefficient 3 / coordinate.blockBase = 0 := by
  rw [coordinate.rawCoefficient_div_blockBase_eq_zero_iff coordinate_goodMode 3]
  native_decide

/-- The adjacent local-overflow boundary in the canonical 249 coordinate is at
`3`, so block `4` is the first raw coefficient that overflows `1000`. -/
theorem coordinate_localOverflowBoundary :
    coordinate.isLocalOverflowBoundary 3 := by
  rw [coordinate.isLocalOverflowBoundary_iff_overflowQuotients coordinate_goodMode 3]
  constructor
  · exact coordinate_overflowQuotient_three_eq_zero
  · native_decide

/-- The canonical positive-`q` example has a unique local-overflow boundary,
and it occurs exactly at block `3`. -/
theorem coordinate_isLocalOverflowBoundary_iff (j : ℕ) :
    coordinate.isLocalOverflowBoundary j ↔ j = 3 := by
  constructor
  · intro hj
    have hk : 1 < coordinate.remainderK := by
      rw [coordinate_remainderK_eq_four]
      decide
    exact coordinate.isLocalOverflowBoundary_unique hk hj coordinate_localOverflowBoundary
  · intro hj
    simpa [hj] using coordinate_localOverflowBoundary

/-- The incoming-carry boundary and adjacent local-overflow boundary coincide,
so the first visible mismatch in the canonical 249 coordinate is already at
block `3`. -/
theorem coordinate_firstVisibleMismatchPosition_eq_three :
    firstVisibleMismatchPosition 3 3 = 3 := by
  exact firstVisibleMismatchPosition_self 3

end QRTour.Composite249

namespace QRTour.Composite996

/-! ### Same-Core Composite Example

This packages the canonical same-core family `(base=10, N=996, stride=3)`,
whose stripped periodic core is `249`. In this family the remainder
`k = 10^3 mod 249 = 4`, and the base-prime support factor is exactly `4 = k^1`,
so the actual denominator and the stripped core differ by a one-block shift.
-/

/-- The actual coordinate `(base=10, N=996, stride=3)`. -/
def actual996Stride3 : BlockCoordinate :=
  actualCoordinate 10 996 3 (by native_decide)

/-- The stripped periodic core coordinate `(base=10, M=249, stride=3)`. -/
def core249Stride3 : BlockCoordinate :=
  strippedCoordinate 10 996 3 (by native_decide)

/-- The actual denominator is in good mode because `996 < 10^3`. -/
theorem actual996Stride3_goodMode : actual996Stride3.goodMode := by
  unfold actual996Stride3 actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The actual denominator and the stripped periodic core form a same-core family. -/
theorem actual996_sameCore : sameCoreCompatible 10 996 3 (by native_decide) := by
  exact sameCoreCompatible_of_goodMode_and_blockBase_lt_modulus_add_stripped
    (base := 10) (n := 996) (stride := 3) (hn := by native_decide)
    actual996Stride3_goodMode
    (by native_decide)
    (by native_decide)

/-- The stripped periodic core inherits good mode from the actual denominator. -/
theorem core249Stride3_goodMode : core249Stride3.goodMode := by
  simpa [core249Stride3] using
    sameCoreCompatible_goodMode_of_actual_goodMode
      (base := 10) (n := 996) (stride := 3) (hn := by native_decide)
      actual996Stride3_goodMode

/-- The decimal denominator `996` has preperiod `2`. -/
theorem preperiodSteps_eq_two : preperiodSteps 10 996 = 2 := by
  native_decide

/-- The base-supported factor in `996` is exactly `4 = 2^2`. -/
theorem basePrimeSupportFactor_eq_four : basePrimeSupportFactor 10 996 = 4 := by
  native_decide

/-- Stripping that base-supported factor leaves the purely periodic core `249`. -/
theorem strippedPeriodModulus_eq_249 : strippedPeriodModulus 10 996 = 249 := by
  native_decide

/-- In the same-core `996 over 249` family, the stripped periodic core and the
actual denominator share the same remainder `k = 4`. -/
theorem sameCore_remainderK_eq :
    core249Stride3.remainderK = actual996Stride3.remainderK := by
  simpa [actual996Stride3, core249Stride3] using
    (sameCoreCompatible_remainderK_eq
      (base := 10) (n := 996) (stride := 3) (hn := by native_decide)
      actual996_sameCore)

/-- In this exact `k^1` same-core family, the base-prime support factor is the
shared remainder `k` raised to the one-block shift power. -/
theorem sameCore_basePrimeSupportFactor_eq_remainderK_pow_one :
    basePrimeSupportFactor 10 996 = actual996Stride3.remainderK ^ 1 := by
  calc
    basePrimeSupportFactor 10 996 = core249Stride3.remainderK ^ 1 := by
      rw [basePrimeSupportFactor_eq_four, show core249Stride3.remainderK = 4 by native_decide]
      native_decide
    _ = actual996Stride3.remainderK ^ 1 := by
      rw [sameCore_remainderK_eq]

/-- In this exact `k^1` same-core family, the actual denominator factors as
the stripped periodic core `249` times the shared remainder `k` to the
one-block shift power. -/
theorem sameCore_denominator_eq_249_mul_remainderK_pow_one :
    996 = 249 * actual996Stride3.remainderK ^ 1 := by
  calc
    996 = basePrimeSupportFactor 10 996 * strippedPeriodModulus 10 996 := by
      symm
      exact basePrimeSupportFactor_mul_strippedPeriodModulus 10 996
    _ = actual996Stride3.remainderK ^ 1 * strippedPeriodModulus 10 996 := by
      rw [sameCore_basePrimeSupportFactor_eq_remainderK_pow_one]
    _ = strippedPeriodModulus 10 996 * actual996Stride3.remainderK ^ 1 := by
      rw [Nat.mul_comm]
    _ = 249 * actual996Stride3.remainderK ^ 1 := by
      rw [strippedPeriodModulus_eq_249]

/-- In this exact `k^1` same-core family, the same denominator identity can be
read equally through the stripped-core remainder presentation. -/
theorem sameCore_denominator_eq_249_mul_coreRemainderK_pow_one :
    996 = 249 * core249Stride3.remainderK ^ 1 := by
  calc
    996 = 249 * actual996Stride3.remainderK ^ 1 := by
      exact sameCore_denominator_eq_249_mul_remainderK_pow_one
    _ = 249 * core249Stride3.remainderK ^ 1 := by
      rw [← sameCore_remainderK_eq]

/-- In this exact `k^1` same-core family, the stripped-core quotient is the
actual quotient scaled by the base-prime support factor `4`. -/
theorem sameCore_quotientQ_scaling :
    core249Stride3.quotientQ = actual996Stride3.quotientQ * basePrimeSupportFactor 10 996 := by
  simpa [actual996Stride3, core249Stride3] using
    (sameCoreCompatible_quotientQ_eq
      (base := 10) (n := 996) (stride := 3) (hn := by native_decide)
      actual996_sameCore)

/-- In this exact `k^1` same-core family, the stripped-core quotient is the
actual quotient scaled by the shared remainder `k` to the one-block shift
power. -/
theorem sameCore_quotientQ_scaling_eq_remainderK_pow_one :
    core249Stride3.quotientQ = actual996Stride3.quotientQ * actual996Stride3.remainderK ^ 1 := by
  calc
    core249Stride3.quotientQ =
        actual996Stride3.quotientQ * basePrimeSupportFactor 10 996 := by
      exact sameCore_quotientQ_scaling
    _ = actual996Stride3.quotientQ * actual996Stride3.remainderK ^ 1 := by
      rw [sameCore_basePrimeSupportFactor_eq_remainderK_pow_one]

/-- The actual denominator first receives incoming carry at block `4`. -/
theorem actual996_firstIncomingCarryPosition :
    actual996Stride3.isFirstIncomingCarryPosition 4 := by
  unfold actual996Stride3 actualCoordinate BlockCoordinate.isFirstIncomingCarryPosition
    isGeometricThresholdBoundary BlockCoordinate.quotientQ BlockCoordinate.remainderK
    BlockCoordinate.blockBase
  native_decide

/-- The stripped periodic core first receives incoming carry one block earlier, at block `3`. -/
theorem core249_firstIncomingCarryPosition :
    core249Stride3.isFirstIncomingCarryPosition 3 := by
  unfold core249Stride3 strippedCoordinate strippedPeriodModulus
    BlockCoordinate.isFirstIncomingCarryPosition isGeometricThresholdBoundary
    BlockCoordinate.quotientQ BlockCoordinate.remainderK BlockCoordinate.blockBase
  native_decide

/-- Since `basePrimeSupportFactor 10 996 = 4 = k^1`, the first incoming-carry
boundary shifts by exactly one block between the stripped core and the actual
denominator. -/
theorem sameCore_firstIncomingCarryPosition_shift_exact :
    4 - 3 = 1 := by
  exact sameCoreCompatible_firstIncomingCarryPosition_shift_exact
    (base := 10) (n := 996) (stride := 3) (s := 1) (a := 4) (c := 3)
    (hn := by native_decide)
    actual996_sameCore
    actual996_firstIncomingCarryPosition
    core249_firstIncomingCarryPosition
    (by native_decide)
    (by native_decide)
    (by native_decide)

/-- Just before the first local-overflow boundary, the actual denominator's
current raw coefficient still has zero block-base overflow quotient. -/
theorem actual996_overflowQuotient_four_eq_zero :
    actual996Stride3.rawCoefficient 4 / actual996Stride3.blockBase = 0 := by
  rw [actual996Stride3.rawCoefficient_div_blockBase_eq_zero_iff actual996Stride3_goodMode 4]
  native_decide

/-- The actual denominator hits its first local-overflow boundary at block `4`. -/
theorem actual996_localOverflowBoundary :
    actual996Stride3.isLocalOverflowBoundary 4 := by
  rw [actual996Stride3.isLocalOverflowBoundary_iff_overflowQuotients actual996Stride3_goodMode 4]
  constructor
  · exact actual996_overflowQuotient_four_eq_zero
  · native_decide

/-- Just before the first local-overflow boundary, the stripped core's current
raw coefficient still has zero block-base overflow quotient. -/
theorem core249_overflowQuotient_three_eq_zero :
    core249Stride3.rawCoefficient 3 / core249Stride3.blockBase = 0 := by
  rw [core249Stride3.rawCoefficient_div_blockBase_eq_zero_iff core249Stride3_goodMode 3]
  native_decide

/-- The stripped periodic core hits its first local-overflow boundary at block `3`. -/
theorem core249_localOverflowBoundary :
    core249Stride3.isLocalOverflowBoundary 3 := by
  rw [core249Stride3.isLocalOverflowBoundary_iff_overflowQuotients core249Stride3_goodMode 3]
  constructor
  · exact core249_overflowQuotient_three_eq_zero
  · native_decide

/-- Since `basePrimeSupportFactor 10 996 = 4 = k^1`, the local-overflow
boundary also shifts by exactly one block between the stripped core and the
actual denominator. -/
theorem sameCore_localOverflowBoundary_shift_exact :
    4 - 3 = 1 := by
  exact sameCoreCompatible_localOverflowBoundary_shift_exact
    (base := 10) (n := 996) (stride := 3) (s := 1) (a := 4) (c := 3)
    (hn := by decide)
    actual996_sameCore
    actual996_localOverflowBoundary
    core249_localOverflowBoundary
    (by native_decide)
    (by native_decide)
    (by decide)

/-- Because both stripped-core boundaries occur at `3`, the stripped-core
first visible mismatch position is also exactly `3`. -/
theorem core249_firstVisibleMismatchPosition_eq_three :
    firstVisibleMismatchPosition 3 3 = 3 := by
  exact firstVisibleMismatchPosition_self 3

/-- Because both actual-denominator boundaries occur at `4`, the actual
first visible mismatch position is also exactly `4`. -/
theorem actual996_firstVisibleMismatchPosition_eq_four :
    firstVisibleMismatchPosition 4 4 = 4 := by
  exact firstVisibleMismatchPosition_self 4

/-- In the same exact `k^1` regime, the first visible mismatch boundary also
shifts by exactly one block. -/
theorem sameCore_firstVisibleMismatchPosition_shift_exact :
    firstVisibleMismatchPosition 4 4 - firstVisibleMismatchPosition 3 3 = 1 := by
  exact sameCoreCompatible_firstVisibleMismatchPosition_shift_exact
    (base := 10) (n := 996) (stride := 3) (s := 1)
    (incomingActual := 4) (incomingCore := 3)
    (overflowActual := 4) (overflowCore := 3)
    (hn := by native_decide)
    actual996_sameCore
    actual996_firstIncomingCarryPosition
    core249_firstIncomingCarryPosition
    actual996_localOverflowBoundary
    core249_localOverflowBoundary
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by native_decide)

/-- In the exact `k^1` same-core regime, the fixed-window lookahead
certificate transports exactly between the stripped-core window `(n, L)` and
the shifted actual window `(n+1, L)`. -/
theorem sameCore_lookaheadCertificateHolds_iff_add_exact
    (requestedBlocks lookaheadBlocks : ℕ) :
    actual996Stride3.lookaheadCertificateHolds (requestedBlocks + 1) lookaheadBlocks ↔
      core249Stride3.lookaheadCertificateHolds requestedBlocks lookaheadBlocks := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    (sameCoreCompatible_lookaheadCertificateHolds_iff_add_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := requestedBlocks) (lookaheadBlocks := lookaheadBlocks)
      (hn := by native_decide)
      hgood
      actual996_sameCore
      (by native_decide))

/-- On the canonical `3/0 -> 4/0` same-core window pair, the raw tail-mass
lower-bound inequality itself transports exactly between the shifted actual
denominator and the stripped core. -/
theorem sameCore_tailMassLowerBound_iff_add_exact :
    actual996Stride3.rawCoefficient 4 <
      actual996Stride3.blockBase ^ 0 *
        (actual996Stride3.blockBase - actual996Stride3.remainderK) ↔
      core249Stride3.rawCoefficient 3 <
        core249Stride3.blockBase ^ 0 *
          (core249Stride3.blockBase - core249Stride3.remainderK) := by
  simpa [actual996Stride3, core249Stride3] using
    sameCoreCompatible_tailMassLowerBound_iff_add_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      actual996_sameCore
      (by native_decide)

/-- On the canonical `3/0 -> 4/0` same-core window pair, an exact stripped-core
lookahead certificate also transports the raw tail-mass lower-bound inequality
to the shifted actual denominator. -/
theorem actual996_tailMassLowerBound_of_core_lookaheadCertificate
    (hcert : core249Stride3.lookaheadCertificateHolds 3 0) :
    actual996Stride3.rawCoefficient 4 <
      actual996Stride3.blockBase ^ 0 *
        (actual996Stride3.blockBase - actual996Stride3.remainderK) := by
  simpa [actual996Stride3, core249Stride3] using
    sameCoreCompatible_tailMassLowerBound_of_core_lookaheadCertificate_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      actual996_sameCore
      (by native_decide)
      hcert

/-- Exact-named forward same-core tail-mass implication on the canonical
`3/0 -> 4/0` window pair. -/
theorem actual996_tailMassLowerBound_of_core_lookaheadCertificate_exact
    (hcert : core249Stride3.lookaheadCertificateHolds 3 0) :
    actual996Stride3.rawCoefficient 4 <
      actual996Stride3.blockBase ^ 0 *
        (actual996Stride3.blockBase - actual996Stride3.remainderK) := by
  exact actual996_tailMassLowerBound_of_core_lookaheadCertificate hcert

/-- On that same canonical `3/0 -> 4/0` window pair, an exact shifted-actual
lookahead certificate transports the raw tail-mass lower-bound inequality back
to the stripped core. -/
theorem core249_tailMassLowerBound_of_actual_lookaheadCertificate
    (hcert : actual996Stride3.lookaheadCertificateHolds 4 0) :
    core249Stride3.rawCoefficient 3 <
      core249Stride3.blockBase ^ 0 *
        (core249Stride3.blockBase - core249Stride3.remainderK) := by
  simpa [actual996Stride3, core249Stride3] using
    sameCoreCompatible_tailMassLowerBound_of_actual_lookaheadCertificate_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      actual996_sameCore
      (by native_decide)
      hcert

/-- Exact-named reverse same-core tail-mass implication on the canonical
`3/0 -> 4/0` window pair. -/
theorem core249_tailMassLowerBound_of_actual_lookaheadCertificate_exact
    (hcert : actual996Stride3.lookaheadCertificateHolds 4 0) :
    core249Stride3.rawCoefficient 3 <
      core249Stride3.blockBase ^ 0 *
        (core249Stride3.blockBase - core249Stride3.remainderK) := by
  exact core249_tailMassLowerBound_of_actual_lookaheadCertificate hcert

/-- On the canonical `3/0 -> 4/0` same-core window pair, an exact stripped-core
lookahead certificate already transports to visible carry/output agreement on
the shifted actual denominator. -/
theorem actual996_visibleCarryWord_eq_emittedBlockWord_of_core_lookaheadCertificate
    (hcert : core249Stride3.lookaheadCertificateHolds 3 0) :
    actual996Stride3.visibleCarryWord actual996Stride3_goodMode 4 0 =
      actual996Stride3.emittedBlockWord 4 := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    actualCoordinate_visibleCarryWord_eq_emittedBlockWord_of_core_lookaheadCertificate_add_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      hcert

/-- On the canonical `3/0 -> 4/0` same-core window pair, the same exact
stripped-core lookahead certificate also transports to finite carry/remainder
pair output agreement on the shifted actual denominator. -/
theorem actual996_visibleCarryPairs_output_agreement_of_core_lookaheadCertificate
    (hcert : core249Stride3.lookaheadCertificateHolds 3 0) :
    (actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0).map
        (fun pair => pair.1.blockValue) =
      (actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0).map
        (fun pair => pair.2.blockValue) := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    actualCoordinate_visibleCarryPairs_output_agreement_of_core_lookaheadCertificate_add_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      hcert

/-- On the canonical shifted actual `4/0` window, the exact stripped-core
lookahead certificate also forces pointwise pair-output agreement. -/
theorem actual996_visibleCarryPairs_output_agreement_pointwise_of_core_lookaheadCertificate
    (hcert : core249Stride3.lookaheadCertificateHolds 3 0)
    (i : ℕ)
    (hi : i < (actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0).length) :
    ((actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0)[i]'hi).1.blockValue =
      ((actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0)[i]'hi).2.blockValue := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    actualCoordinate_visibleCarryPairs_output_agreement_pointwise_of_core_lookaheadCertificate_add_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      hcert
      i
      hi

/-- On the shifted actual `4/0` window, each visible carry/remainder pair
still satisfies the carry-balance equation
`coefficient + carryIn = blockValue + B * carryOut`. -/
theorem actual996_visibleCarryPairs_carry_balance
    (i : ℕ)
    (hi : i < (actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0).length) :
    ((actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0)[i]'hi).1.coefficient +
        ((actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0)[i]'hi).1.carryIn =
      ((actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0)[i]'hi).1.blockValue +
        actual996Stride3.blockBase *
          ((actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0)[i]'hi).1.carryOut := by
  simpa using
    actual996Stride3.visibleCarryPairs_carry_balance actual996Stride3_goodMode 4 0 i hi

/-- On the shifted actual `4/0` window, each visible carry/remainder pair
also satisfies the remainder-balance equation
`B * remainderIn = blockValue * modulus + remainderOut`. -/
theorem actual996_visibleCarryPairs_remainder_balance
    (i : ℕ)
    (hi : i < (actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0).length) :
    actual996Stride3.blockBase *
        ((actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0)[i]'hi).2.remainderIn =
      ((actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0)[i]'hi).2.blockValue *
          actual996Stride3.modulus +
        ((actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0)[i]'hi).2.remainderOut := by
  simpa using
    actual996Stride3.visibleCarryPairs_remainder_balance actual996Stride3_goodMode 4 0 i hi

/-- On the canonical `3/0 -> 4/0` same-core window pair, the same exact
stripped-core lookahead certificate also transports to aligned state-output
agreement on the shifted actual denominator. -/
theorem actual996_stateAlignments_output_agreement_of_core_lookaheadCertificate
    (hcert : core249Stride3.lookaheadCertificateHolds 3 0) :
    (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).map
        StateAlignment.carryBlockValue =
      (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).map
        StateAlignment.remainderBlockValue := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    actualCoordinate_stateAlignments_output_agreement_of_core_lookaheadCertificate_add_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      hcert

/-- On the canonical shifted actual `4/0` window, the exact stripped-core
lookahead certificate also forces pointwise aligned output agreement. -/
theorem actual996_stateAlignments_output_agreement_pointwise_of_core_lookaheadCertificate
    (hcert : core249Stride3.lookaheadCertificateHolds 3 0)
    (i : ℕ)
    (hi : i < (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).length) :
    ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[i]'hi).carryBlockValue =
      ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[i]'hi).remainderBlockValue := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    actualCoordinate_stateAlignments_output_agreement_pointwise_of_core_lookaheadCertificate_add_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      hcert
      i
      hi

/-- On the shifted actual window, the traced incoming carries are exactly the
next step's outgoing carries, ending with the terminal leftmost carry `0`. -/
theorem actual996_traceRawWord_carryIn_eq_tail_carryOut :
    (actual996Stride3.traceRawWord actual996Stride3_goodMode 4).map CarryTraceStep.carryIn =
      ((actual996Stride3.traceRawWord actual996Stride3_goodMode 4).tail.map
        CarryTraceStep.carryOut) ++ [0] := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3] using
    BlockCoordinate.traceRawWord_map_carryIn_eq_tail_map_carryOut_append_zero_of_pos
      (C := actualCoordinate 10 996 3 (by native_decide)) hgood 3

/-- The coarse stripped-core inequality `k^(n+L) < modulus` already certifies
visible carry/output agreement on the shifted actual denominator. -/
theorem actual996_visibleCarryWord_eq_emittedBlockWord :
    actual996Stride3.visibleCarryWord actual996Stride3_goodMode 4 0 =
      actual996Stride3.emittedBlockWord 4 := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3] using
    actualCoordinate_visibleCarryWord_eq_emittedBlockWord_of_core_remainderKPow_lt_modulus_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      (by native_decide)

/-- Concretely, the shifted actual stabilized four-block carried word is
`[1, 4, 16, 64]`. -/
theorem actual996_visibleCarryWord_four_zero_eq_blocks :
    actual996Stride3.visibleCarryWord actual996Stride3_goodMode 4 0 =
      [1, 4, 16, 64] := by
  rw [actual996_visibleCarryWord_eq_emittedBlockWord]
  native_decide

/-- The same coarse same-core condition also certifies finite carry/remainder
pair output agreement on the shifted actual window. -/
theorem actual996_visibleCarryPairs_output_agreement :
    (actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0).map
        (fun pair => pair.1.blockValue) =
      (actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0).map
        (fun pair => pair.2.blockValue) := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3] using
    actualCoordinate_visibleCarryPairs_output_agreement_of_core_remainderKPow_lt_modulus_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      (by native_decide)

/-- On the shifted actual `4/0` window, the same coarse stripped-core
inequality also forces pointwise pair-output agreement. -/
theorem actual996_visibleCarryPairs_output_agreement_pointwise
    (i : ℕ)
    (hi : i < (actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0).length) :
    ((actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0)[i]'hi).1.blockValue =
      ((actual996Stride3.visibleCarryPairs actual996Stride3_goodMode 4 0)[i]'hi).2.blockValue := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3] using
    actualCoordinate_visibleCarryPairs_output_agreement_pointwise_of_core_remainderKPow_lt_modulus_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      (by native_decide)
      i
      hi

/-- The same coarse stripped-core inequality also certifies aligned
carry/remainder output agreement on the shifted actual state-alignment
window. -/
theorem actual996_stateAlignments_output_agreement :
    (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).map
        StateAlignment.carryBlockValue =
      (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).map
        StateAlignment.remainderBlockValue := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3] using
    actualCoordinate_stateAlignments_output_agreement_of_core_remainderKPow_lt_modulus_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      (by native_decide)

/-- On the shifted actual `4/0` window, the same coarse stripped-core
inequality also forces pointwise aligned output agreement. -/
theorem actual996_stateAlignments_output_agreement_pointwise
    (i : ℕ)
    (hi : i < (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).length) :
    ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[i]'hi).carryBlockValue =
      ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[i]'hi).remainderBlockValue := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3] using
    actualCoordinate_stateAlignments_output_agreement_pointwise_of_core_remainderKPow_lt_modulus_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      (by native_decide)
      i
      hi

/-- On the canonical `3/0 -> 4/0` same-core window pair, the shifted actual
raw coefficients align pointwise with the stripped core. -/
theorem actual996_stateAlignments_coefficient_shift_exact
    (j : ℕ)
    (hjActual : j + 1 < (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).length)
    (hjCore : j < (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).length) :
    ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j + 1]'hjActual).coefficient =
      ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hjCore).coefficient := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    actualCoordinate_stateAlignments_coefficient_shift_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      actual996_sameCore
      (by native_decide)
      j
      hjActual
      hjCore

/-- On the canonical `3/0 -> 4/0` same-core window pair, the shifted actual
carry states align pointwise with the stripped core. -/
theorem actual996_stateAlignments_carryIn_shift_exact
    (j : ℕ)
    (hjActual : j + 1 < (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).length)
    (hjCore : j < (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).length) :
    ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j + 1]'hjActual).carryIn =
      ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hjCore).carryIn := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    actualCoordinate_stateAlignments_carryIn_shift_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      actual996_sameCore
      (by native_decide)
      j
      hjActual
      hjCore

/-- On the same canonical `3/0 -> 4/0` window pair, the shifted actual
outgoing carries also align pointwise with the stripped core. -/
theorem actual996_stateAlignments_carryOut_shift_exact
    (j : ℕ)
    (hjActual : j + 1 < (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).length)
    (hjCore : j < (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).length) :
    ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j + 1]'hjActual).carryOut =
      ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hjCore).carryOut := by
  have hj : j < 3 := by
    simpa [core249Stride3] using hjCore
  interval_cases j
  · simpa using
      (show ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[1]'(by native_decide)).carryOut =
          ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[0]'(by native_decide)).carryOut by
        native_decide)
  · simpa using
      (show ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[2]'(by native_decide)).carryOut =
          ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[1]'(by native_decide)).carryOut by
        native_decide)
  · simpa using
      (show ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[3]'(by native_decide)).carryOut =
          ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[2]'(by native_decide)).carryOut by
        native_decide)

/-- On the same canonical `3/0 -> 4/0` window pair, the shifted actual
current remainder states are exactly `k = 4` times the stripped-core
remainder states. -/
theorem actual996_stateAlignments_remainderIn_shift_exact
    (j : ℕ)
    (hjActual : j + 1 < (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).length)
    (hjCore : j < (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).length) :
    ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j + 1]'hjActual).remainderIn =
      actual996Stride3.remainderK *
        ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hjCore).remainderIn := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa only [pow_one, actual996Stride3, core249Stride3] using
    actualCoordinate_stateAlignments_remainderIn_shift_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      actual996_sameCore
      (by native_decide)
      j
      hjActual
      hjCore

/-- On the canonical `3/0 -> 4/0` same-core window pair, the shifted actual
emitted blocks align pointwise with the stripped core. -/
theorem actual996_stateAlignments_remainderBlockValue_shift_exact
    (j : ℕ)
    (hjActual : j + 1 < (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).length)
    (hjCore : j < (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).length) :
    ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j + 1]'hjActual).remainderBlockValue =
      ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hjCore).remainderBlockValue := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    actualCoordinate_stateAlignments_remainderBlockValue_shift_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      actual996_sameCore
      (by native_decide)
      j
      hjActual
      hjCore

/-- On the same canonical `3/0 -> 4/0` window pair, the shifted actual carried
block values also align pointwise with the stripped core. -/
theorem actual996_stateAlignments_carryBlockValue_shift_exact
    (j : ℕ)
    (hjActual : j + 1 < (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).length)
    (hjCore : j < (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).length) :
    ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j + 1]'hjActual).carryBlockValue =
      ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hjCore).carryBlockValue := by
  have hj : j < 3 := by
    simpa [core249Stride3] using hjCore
  interval_cases j
  · simpa using
      (show ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[1]'(by native_decide)).carryBlockValue =
          ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[0]'(by native_decide)).carryBlockValue by
        native_decide)
  · simpa using
      (show ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[2]'(by native_decide)).carryBlockValue =
          ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[1]'(by native_decide)).carryBlockValue by
        native_decide)
  · simpa using
      (show ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[3]'(by native_decide)).carryBlockValue =
          ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[2]'(by native_decide)).carryBlockValue by
        native_decide)

/-- On the same canonical `3/0 -> 4/0` window pair, the shifted actual
next-step remainders are exactly `k = 4` times the stripped-core remainders. -/
theorem actual996_stateAlignments_remainderOut_shift_exact
    (j : ℕ)
    (hjActual : j + 1 < (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).length)
    (hjCore : j < (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).length) :
    ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j + 1]'hjActual).remainderOut =
      actual996Stride3.remainderK *
        ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hjCore).remainderOut := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa only [pow_one, actual996Stride3, core249Stride3] using
    actualCoordinate_stateAlignments_remainderOut_shift_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      actual996_sameCore
      (by native_decide)
      j
      hjActual
      hjCore

/-- On the shifted actual window, the same-core transport already makes the
observed map `remainderIn ↦ (carryIn, carryOut)` functional. This packages the
finite state-step witness beneath the open carry-factorization boundary. -/
theorem actual996_stateAlignments_remainderToCarryStepFunctional :
    List.FunctionalOnFst
      ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).map
        (fun alignment => (alignment.remainderIn, (alignment.carryIn, alignment.carryOut)))) := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  have hcoreGood :
      (strippedCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [core249Stride3] using core249Stride3_goodMode
  have hcoreFunc :
      core249Stride3.remainderToCarryFunctional core249Stride3_goodMode 3 0 := by
    rw [core249Stride3.remainderToCarryFunctional_iff_functionalOnFst_pairs]
    native_decide
  have hfunc :
      actual996Stride3.remainderToCarryFunctional actual996Stride3_goodMode 4 0 := by
    simpa [actual996Stride3] using
      actualCoordinate_stateAlignments_remainderToCarryFunctional_of_core_remainderKPow_lt_modulus_add
        (base := 10) (n := 996) (stride := 3) (s := 1)
        (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
        hgood
        (by native_decide)
        actual996_sameCore
        (by native_decide)
        (by native_decide)
        hcoreGood
        (by simpa [core249Stride3] using hcoreFunc)
  exact
    actual996Stride3.stateAlignments_remainderToCarryStepFunctional_of_functional_and_remainderK_pow_lt_modulus
      actual996Stride3_goodMode
      (by native_decide)
      4
      0
      hfunc
      (by native_decide)

/-- On the stripped-core one-block `1/0` window, the observed map
`carryIn ↦ remainderIn` is still functional. This isolates the positive
carry-to-remainder witness used on the core side of the canonical same-core
counterexample. -/
theorem core249_carryToRemainderFunctional_one_zero :
    core249Stride3.carryToRemainderFunctional core249Stride3_goodMode 1 0 := by
  simpa [actual996Stride3, core249Stride3] using
    (composite996_sameCore_carryToRemainderTransport_counterexample.1)

/-- On the shifted actual `2/0` window for `996`, the first two aligned states
already exhibit the low-level carry-to-remainder conflict: they share incoming
carry `0`, but their remainders differ. This is the concrete obstruction
beneath the same-core carry-factorization boundary. -/
theorem actual996_carryToRemainder_conflict_two_zero :
    ((actual996Stride3.stateAlignments actual996Stride3_goodMode 2 0)[0]'(by native_decide)).carryIn =
        ((actual996Stride3.stateAlignments actual996Stride3_goodMode 2 0)[1]'(by native_decide)).carryIn ∧
      ((actual996Stride3.stateAlignments actual996Stride3_goodMode 2 0)[0]'(by native_decide)).remainderIn ≠
        ((actual996Stride3.stateAlignments actual996Stride3_goodMode 2 0)[1]'(by native_decide)).remainderIn := by
  simpa [actual996Stride3] using composite996Stride3_carryToRemainder_conflict_two_zero

/-- Even in the exact `k^1` same-core regime, forward carry-to-remainder
functionality does not transport automatically: the stripped core is already
functional on the one-block `1/0` window, while the shifted actual denominator
fails on the corresponding `2/0` window. This keeps the open carry-factorization
boundary honest on the canonical `996 over 249` family. -/
theorem sameCore_carryToRemainderTransport_counterexample :
    core249Stride3.carryToRemainderFunctional core249Stride3_goodMode 1 0 ∧
      ¬ actual996Stride3.carryToRemainderFunctional actual996Stride3_goodMode 2 0 := by
  refine ⟨core249_carryToRemainderFunctional_one_zero, ?_⟩
  simpa [actual996Stride3] using composite996Stride3_not_carryToRemainderFunctional_two_zero

/-- On the same shifted actual window, the reverse observed map
`carryIn ↦ remainderIn` already fails to be functional. This keeps the
canonical `996 over 249` witness honest about the asymmetry between the two
finite state maps beneath the open carry-factorization boundary. -/
theorem actual996_not_carryToRemainderFunctional :
    ¬ actual996Stride3.carryToRemainderFunctional actual996Stride3_goodMode 4 0 := by
  rw [actual996Stride3.carryToRemainderFunctional_iff_functionalOnFst_pairs]
  native_decide

/-- On the shifted actual window, matching `remainderIn` and raw coefficient
forces matching carry state, block values, and next-step outputs. This is the
concrete `996 over 249` transition-compatibility witness beneath the open
carry-factorization boundary. -/
theorem actual996_stateAlignments_remainderToCarry_transition_compatible
    (i : ℕ)
    (hi : i < (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).length)
    (j : ℕ)
    (hj : j < (actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0).length)
    (hstate :
      ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[i]'hi).remainderIn =
        ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j]'hj).remainderIn)
    (hcoeff :
      ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[i]'hi).coefficient =
        ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j]'hj).coefficient) :
    ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[i]'hi).carryIn =
        ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j]'hj).carryIn ∧
      ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[i]'hi).remainderBlockValue =
        ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j]'hj).remainderBlockValue ∧
      ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[i]'hi).carryBlockValue =
        ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j]'hj).carryBlockValue ∧
      ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[i]'hi).remainderOut =
        ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j]'hj).remainderOut ∧
      ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[i]'hi).carryOut =
        ((actual996Stride3.stateAlignments actual996Stride3_goodMode 4 0)[j]'hj).carryOut := by
  have hfunc :
      actual996Stride3.remainderToCarryFunctional actual996Stride3_goodMode 4 0 := by
    rw [actual996Stride3.remainderToCarryFunctional_iff_functionalOnFst_pairs]
    native_decide
  simpa [actual996Stride3] using
    actualCoordinate_stateAlignments_remainderToCarry_transition_compatible_of_core_remainderKPow_lt_modulus_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      actual996Stride3_goodMode
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      (by native_decide)
      hfunc
      i hi j hj hstate hcoeff

/-- On the larger selector-family profile `(requestedBlocks=8,
lookaheadBlocks=1)`, the same-core denominator `996` is still quotient-only:
the observed `remainderIn ↦ carryIn` map is functional, but the reverse
`carryIn ↦ remainderIn` map is not. This stays strictly below the open global
`carry_dfa_factorization` claim and only records the finite profile used by
the public same-core counterexample family. -/
theorem actual996_quotientOnly_profile :
    actual996Stride3.remainderToCarryFunctional actual996Stride3_goodMode 8 1 ∧
      ¬ actual996Stride3.carryToRemainderFunctional actual996Stride3_goodMode 8 1 := by
  constructor
  · rw [actual996Stride3.remainderToCarryFunctional_iff_functionalOnFst_pairs]
    native_decide
  · rw [actual996Stride3.carryToRemainderFunctional_iff_functionalOnFst_pairs]
    native_decide

/-- On the canonical `4/0 -> 3/0` same-core window pair, an exact shifted-actual
lookahead certificate already transports back to visible carry/output agreement
on the stripped core. -/
theorem core249_visibleCarryWord_eq_emittedBlockWord_of_actual_lookaheadCertificate
    (hcert : actual996Stride3.lookaheadCertificateHolds 4 0) :
    core249Stride3.visibleCarryWord core249Stride3_goodMode 3 0 =
      core249Stride3.emittedBlockWord 3 := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    strippedCoordinate_visibleCarryWord_eq_emittedBlockWord_of_actual_lookaheadCertificate_add_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      hcert

/-- On the canonical `4/0 -> 3/0` same-core window pair, the exact shifted-actual
lookahead certificate also transports back to finite carry/remainder pair
output agreement on the stripped core. -/
theorem core249_visibleCarryPairs_output_agreement_of_actual_lookaheadCertificate
    (hcert : actual996Stride3.lookaheadCertificateHolds 4 0) :
    (core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0).map
        (fun pair => pair.1.blockValue) =
      (core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0).map
        (fun pair => pair.2.blockValue) := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    strippedCoordinate_visibleCarryPairs_output_agreement_of_actual_lookaheadCertificate_add_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      hcert

/-- On the canonical stripped-core `3/0` window, the exact shifted-actual
lookahead certificate also forces pointwise pair-output agreement. -/
theorem core249_visibleCarryPairs_output_agreement_pointwise_of_actual_lookaheadCertificate
    (hcert : actual996Stride3.lookaheadCertificateHolds 4 0)
    (i : ℕ)
    (hi : i < (core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0).length) :
    ((core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0)[i]'hi).1.blockValue =
      ((core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0)[i]'hi).2.blockValue := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    strippedCoordinate_visibleCarryPairs_output_agreement_pointwise_of_actual_lookaheadCertificate_add_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      hcert
      i
      hi

/-- On the unshifted stripped-core `3/0` window, each visible carry/remainder
pair still satisfies the carry-balance equation
`coefficient + carryIn = blockValue + B * carryOut`. -/
theorem core249_visibleCarryPairs_carry_balance
    (i : ℕ)
    (hi : i < (core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0).length) :
    ((core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0)[i]'hi).1.coefficient +
        ((core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0)[i]'hi).1.carryIn =
      ((core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0)[i]'hi).1.blockValue +
        core249Stride3.blockBase *
          ((core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0)[i]'hi).1.carryOut := by
  simpa using
    core249Stride3.visibleCarryPairs_carry_balance core249Stride3_goodMode 3 0 i hi

/-- On the unshifted stripped-core `3/0` window, each visible carry/remainder
pair also satisfies the remainder-balance equation
`B * remainderIn = blockValue * modulus + remainderOut`. -/
theorem core249_visibleCarryPairs_remainder_balance
    (i : ℕ)
    (hi : i < (core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0).length) :
    core249Stride3.blockBase *
        ((core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0)[i]'hi).2.remainderIn =
      ((core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0)[i]'hi).2.blockValue *
          core249Stride3.modulus +
        ((core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0)[i]'hi).2.remainderOut := by
  simpa using
    core249Stride3.visibleCarryPairs_remainder_balance core249Stride3_goodMode 3 0 i hi

/-- On the canonical `4/0 -> 3/0` same-core window pair, the exact shifted-actual
lookahead certificate also transports back to aligned state-output agreement
on the stripped core. -/
theorem core249_stateAlignments_output_agreement_of_actual_lookaheadCertificate
    (hcert : actual996Stride3.lookaheadCertificateHolds 4 0) :
    (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).map
        StateAlignment.carryBlockValue =
      (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).map
        StateAlignment.remainderBlockValue := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    strippedCoordinate_stateAlignments_output_agreement_of_actual_lookaheadCertificate_add_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      hcert

/-- On the canonical stripped-core `3/0` window, the exact shifted-actual
lookahead certificate also forces pointwise aligned output agreement. -/
theorem core249_stateAlignments_output_agreement_pointwise_of_actual_lookaheadCertificate
    (hcert : actual996Stride3.lookaheadCertificateHolds 4 0)
    (i : ℕ)
    (hi : i < (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).length) :
    ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[i]'hi).carryBlockValue =
      ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[i]'hi).remainderBlockValue := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [actual996Stride3, core249Stride3] using
    strippedCoordinate_stateAlignments_output_agreement_pointwise_of_actual_lookaheadCertificate_add_exact
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      hcert
      i
      hi

/-- The reverse coarse wrapper certifies the unshifted stripped-core window
from the shifted actual inequality. -/
theorem core249_visibleCarryWord_eq_emittedBlockWord :
    core249Stride3.visibleCarryWord core249Stride3_goodMode 3 0 =
      core249Stride3.emittedBlockWord 3 := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [core249Stride3] using
    strippedCoordinate_visibleCarryWord_eq_emittedBlockWord_of_actual_remainderKPow_lt_modulus_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      (by native_decide)

/-- Concretely, the stripped-core stabilized three-block carried word is
`[4, 16, 64]`. -/
theorem core249_visibleCarryWord_three_zero_eq_blocks :
    core249Stride3.visibleCarryWord core249Stride3_goodMode 3 0 =
      [4, 16, 64] := by
  rw [core249_visibleCarryWord_eq_emittedBlockWord]
  native_decide

/-- On the canonical `3/0 -> 4/0` same-core window pair, the shifted actual
visible word is exactly one leading block followed by the stripped-core visible
word. -/
theorem sameCore_visibleCarryWord_shift_exact :
    actual996Stride3.visibleCarryWord actual996Stride3_goodMode 4 0 =
      1 :: core249Stride3.visibleCarryWord core249Stride3_goodMode 3 0 := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  have hcert : core249Stride3.lookaheadCertificateHolds 3 0 := by
    simpa [core249Stride3, QRTour.Composite249.coordinate, strippedCoordinate,
      strippedPeriodModulus_eq_249] using
        QRTour.Composite249.coordinate_lookaheadCertificate_three_zero
  have hshift :
      actual996Stride3.visibleCarryWord actual996Stride3_goodMode 4 0 =
        actual996Stride3.emittedBlockWord 1 ++
          core249Stride3.visibleCarryWord core249Stride3_goodMode 3 0 := by
    simpa [actual996Stride3, core249Stride3] using
      actualCoordinate_visibleCarryWord_shift_exact_of_core_lookaheadCertificate_add_exact
        (base := 10) (n := 996) (stride := 3) (s := 1)
        (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
        hgood
        (by native_decide)
        (by native_decide)
        actual996_sameCore
        (by native_decide)
        hcert
  calc
    actual996Stride3.visibleCarryWord actual996Stride3_goodMode 4 0
      = actual996Stride3.emittedBlockWord 1 ++
          core249Stride3.visibleCarryWord core249Stride3_goodMode 3 0 := hshift
    _ = 1 :: core249Stride3.visibleCarryWord core249Stride3_goodMode 3 0 := by
          native_decide

/-- The reverse same-core coarse wrapper also certifies pair-output agreement
on the stripped-core visible carry/remainder window. -/
theorem core249_visibleCarryPairs_output_agreement :
    (core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0).map
        (fun pair => pair.1.blockValue) =
      (core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0).map
        (fun pair => pair.2.blockValue) := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [core249Stride3] using
    strippedCoordinate_visibleCarryPairs_output_agreement_of_actual_remainderKPow_lt_modulus_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      (by native_decide)

/-- On the unshifted stripped-core `3/0` window, the same shifted-actual coarse
inequality also forces pointwise pair-output agreement. -/
theorem core249_visibleCarryPairs_output_agreement_pointwise
    (i : ℕ)
    (hi : i < (core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0).length) :
    ((core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0)[i]'hi).1.blockValue =
      ((core249Stride3.visibleCarryPairs core249Stride3_goodMode 3 0)[i]'hi).2.blockValue := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [core249Stride3] using
    strippedCoordinate_visibleCarryPairs_output_agreement_pointwise_of_actual_remainderKPow_lt_modulus_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      (by native_decide)
      i
      hi

/-- The reverse same-core coarse wrapper also certifies aligned carry/remainder
output agreement on the stripped-core state-alignment window. -/
theorem core249_stateAlignments_output_agreement :
    (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).map
        StateAlignment.carryBlockValue =
      (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).map
        StateAlignment.remainderBlockValue := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [core249Stride3] using
    strippedCoordinate_stateAlignments_output_agreement_of_actual_remainderKPow_lt_modulus_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      (by native_decide)

/-- On the unshifted stripped-core `3/0` window, the same shifted-actual coarse
inequality also forces pointwise aligned output agreement. -/
theorem core249_stateAlignments_output_agreement_pointwise
    (i : ℕ)
    (hi : i < (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).length) :
    ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[i]'hi).carryBlockValue =
      ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[i]'hi).remainderBlockValue := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  simpa [core249Stride3] using
    strippedCoordinate_stateAlignments_output_agreement_pointwise_of_actual_remainderKPow_lt_modulus_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      (by native_decide)
      i
      hi

/-- The reverse same-core wrapper also transports the observed
remainder-to-carry functional criterion back to the stripped core. -/
theorem core249_remainderToCarryFunctional :
    core249Stride3.remainderToCarryFunctional core249Stride3_goodMode 3 0 := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  have hfuncConcrete :
      actual996Stride3.remainderToCarryFunctional actual996Stride3_goodMode 4 0 := by
    rw [actual996Stride3.remainderToCarryFunctional_iff_functionalOnFst_pairs]
    native_decide
  have hfunc :
      (actualCoordinate 10 996 3 (by native_decide)).remainderToCarryFunctional hgood 4 0 := by
    simpa [actual996Stride3] using hfuncConcrete
  simpa [core249Stride3] using
    strippedCoordinate_stateAlignments_remainderToCarryFunctional_of_actual_remainderKPow_lt_modulus_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      actual996_sameCore
      (by native_decide)
      (by native_decide)
      hfunc

/-- The reverse same-core wrapper also transports the observed
remainder-to-carry transition-compatibility witness back to the stripped core
on the unshifted window. -/
theorem core249_stateAlignments_remainderToCarry_transition_compatible
    (i : ℕ)
    (hi : i < (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).length)
    (j : ℕ)
    (hj : j < (core249Stride3.stateAlignments core249Stride3_goodMode 3 0).length)
    (hstate :
      ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[i]'hi).remainderIn =
        ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hj).remainderIn)
    (hcoeff :
      ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[i]'hi).coefficient =
        ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hj).coefficient) :
    ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[i]'hi).carryIn =
        ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hj).carryIn ∧
      ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[i]'hi).remainderBlockValue =
        ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hj).remainderBlockValue ∧
      ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[i]'hi).carryBlockValue =
        ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hj).carryBlockValue ∧
      ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[i]'hi).remainderOut =
        ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hj).remainderOut ∧
      ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[i]'hi).carryOut =
        ((core249Stride3.stateAlignments core249Stride3_goodMode 3 0)[j]'hj).carryOut := by
  have hgood :
      (actualCoordinate 10 996 3 (by native_decide)).goodMode := by
    simpa [actual996Stride3] using actual996Stride3_goodMode
  have hfuncConcrete :
      actual996Stride3.remainderToCarryFunctional actual996Stride3_goodMode 4 0 := by
    rw [actual996Stride3.remainderToCarryFunctional_iff_functionalOnFst_pairs]
    native_decide
  have hfunc :
      (actualCoordinate 10 996 3 (by native_decide)).remainderToCarryFunctional hgood 4 0 := by
    simpa [actual996Stride3] using hfuncConcrete
  simpa [core249Stride3] using
    strippedCoordinate_stateAlignments_remainderToCarry_transition_compatible_of_actual_remainderKPow_lt_modulus_add
      (base := 10) (n := 996) (stride := 3) (s := 1)
      (requestedBlocks := 3) (lookaheadBlocks := 0) (hn := by native_decide)
      hgood
      (by native_decide)
      actual996_sameCore
      (by native_decide)
      (by native_decide)
      hfunc
      i hi j hj hstate hcoeff

/-- On the same stripped-core window, the dual carry-to-remainder criterion
already fails. This keeps the concrete example honest about the asymmetry
between the two observed finite state maps. -/
theorem core249_not_carryToRemainderFunctional :
    ¬ core249Stride3.carryToRemainderFunctional core249Stride3_goodMode 3 0 := by
  rw [core249Stride3.carryToRemainderFunctional_iff_functionalOnFst_pairs]
  native_decide

/-- The same-core local-overflow boundary is visible on both sides through the
overflow-quotient interface: the stripped core overflows at block `3`, the
actual denominator at block `4`, and the exact `k^1` regime shifts the
boundary by exactly one block. -/
theorem sameCore_localOverflowBoundary_via_overflowQuotient :
    (core249Stride3.rawCoefficient 3 < core249Stride3.blockBase ∧
      0 < core249Stride3.rawCoefficient 4 / core249Stride3.blockBase) ∧
    (actual996Stride3.rawCoefficient 4 < actual996Stride3.blockBase ∧
      0 < actual996Stride3.rawCoefficient 5 / actual996Stride3.blockBase) ∧
    4 - 3 = 1 := by
  have hcore : core249Stride3.isLocalOverflowBoundary 3 := core249_localOverflowBoundary
  have hactual : actual996Stride3.isLocalOverflowBoundary 4 := actual996_localOverflowBoundary
  have hcoreView :
      core249Stride3.rawCoefficient 3 < core249Stride3.blockBase ∧
        0 < core249Stride3.rawCoefficient 4 / core249Stride3.blockBase := by
    exact (core249Stride3.isLocalOverflowBoundary_iff_overflowQuotient
      core249Stride3_goodMode 3).1 hcore
  have hactualView :
      actual996Stride3.rawCoefficient 4 < actual996Stride3.blockBase ∧
        0 < actual996Stride3.rawCoefficient 5 / actual996Stride3.blockBase := by
    exact (actual996Stride3.isLocalOverflowBoundary_iff_overflowQuotient
      actual996Stride3_goodMode 4).1 hactual
  have hshift : 4 - 3 = 1 :=
    sameCore_localOverflowBoundary_shift_exact
  exact ⟨hcoreView, hactualView, hshift⟩

end QRTour.Composite996
