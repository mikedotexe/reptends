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
# Worked Examples: prime 19, prime 97, composite 21, composite 249, and same-core composite 996 over 249, plus empirical obstruction and reconstruction hooks

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

It also packages `QRTour.FutureBase10N98` as a finite positive reconstruction
hook. Separately, it packages `QRTour.Composite68`,
`QRTour.Composite68Base30`,
`QRTour.FutureBase10N17`, `QRTour.FutureBase10N34`,
`QRTour.FutureBase30N13`, `QRTour.FutureBase30N26`, and the
scaffolded `QRTour.FutureBase30N7` / `QRTour.FutureBase30N14` /
`QRTour.FutureBase30N28` / `QRTour.FutureBase12N10` /
`QRTour.FutureBase10N102` / `QRTour.FutureBase7N5` /
`QRTour.FutureBase12N5` / `QRTour.FutureBase30N34` /
`QRTour.FutureBase30N374` / `QRTour.FutureBase30N748` /
`QRTour.FutureBase7N93` / `QRTour.FutureBase10N39` /
`QRTour.FutureBase10N78` / `QRTour.FutureBase10N96` /
`QRTour.FutureBase12N35` / `QRTour.FutureBase12N31` finite examples as empirical/open-boundary
obstruction hooks. Those namespaces record concrete certified finite windows
where output agreement hides a repeated remainder state with incompatible raw
coefficients; they do not promote `small_k_visibility_threshold` or
`carry_dfa_factorization`.

`QRTour.Shape17K4` packages the finite Shape17/K4 shift witness tying the
base-10 `N = 17` shifted `[0,4]` conflict to the base-10 `N = 34` and
`N = 68` Composite68-style `[1,5]` windows. It is a finite comparison hook,
not a global same-core classification theorem.

`QRTour.Shape13K4` packages the finite Shape13/K4 mod-stable carry-loss shift
witness tying the base-30 `N = 13` `[0,6]` conflict to the base-30 `N = 26`
`[1,7]` window. It is a finite comparison hook and a named same-core
carried-output criterion instantiation, not a global observability theorem.

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

/-! ### Positive Reconstruction Exemplar

The default observability-program atlas classifies the prime-`97` `8/2`
window as a positive reconstruction candidate: the observed finite
`remainderIn` state determines the raw coefficient on this window. The first
theorem keeps the older list-functional surface explicit; the second translates
it through the generic `FactorsThrough` bridge used by the observability lens.
-/

/-- On the default prime-`97` observability window, the observed `remainderIn`
states are exactly the first eight powers of the remainder `3`, reduced modulo
`97`. -/
theorem coordinate_stateAlignments_remainderIn_window_eight_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 2).map
      (fun alignment => alignment.remainderIn)) = [1, 3, 9, 27, 81, 49, 50, 53] := by
  have h0 : coordinate.longDivisionRemainder 0 = 1 := by rfl
  have h1 : coordinate.longDivisionRemainder 1 = 3 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h2 : coordinate.longDivisionRemainder 2 = 9 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h3 : coordinate.longDivisionRemainder 3 = 27 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h4 : coordinate.longDivisionRemainder 4 = 81 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h5 : coordinate.longDivisionRemainder 5 = 49 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h6 : coordinate.longDivisionRemainder 6 = 50 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h7 : coordinate.longDivisionRemainder 7 = 53 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  exact coordinate.stateAlignments_remainderIn_window_eight_eq_of_longDivisionRemainders
    coordinate_goodMode 2 h0 h1 h2 h3 h4 h5 h6 h7

/-- On the default prime-`97` observability window, the observed `remainderIn`
states are pairwise distinct. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 2).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_window_eq
    coordinate_goodMode 8 2
    coordinate_stateAlignments_remainderIn_window_eight_two
    (by norm_num)

/-- On the default prime-`97` observability window, the finite
`remainderIn ↦ raw coefficient` map is functional by finite injective readout. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderIn_nodup
      coordinate_goodMode 8 2 coordinate_stateAlignments_remainderIn_nodup_eight_two

/-- Positive reconstruction exemplar for prime `97`: on the finite `8/2`
state-alignment window, the raw coefficient factors through the observed
`remainderIn` state. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderIn_nodup
      coordinate_goodMode 8 2
      coordinate_stateAlignments_remainderIn_nodup_eight_two

/-! ### Digit Examples

The reptend digits of 1/97 in base 10.
-/

/-- First few digits of 1/97 in decimal. -/
example : digit 97 10 0 = 0 := by native_decide  -- First digit is 0 (1 × 10 = 10 < 97)
example : digit 97 10 1 = 1 := by native_decide  -- 10 × 10 = 100, 100/97 = 1
example : digit 97 10 2 = 0 := by native_decide  -- 3 × 10 = 30 < 97
example : digit 97 10 3 = 3 := by native_decide  -- 30 × 10 = 300, 300/97 = 3

end QRTour.Prime97

namespace QRTour.FutureBase10N98

/-! ### Positive reconstruction example: base 10, N = 98

This packages the smallest-gap positive reconstruction candidate currently
emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (10, 98, 2, 100, 1, 2, 1, 44)`.
It is a finite `8/1` proof hook only; it does not add a registry claim,
theorem-witness record, atlas status change, or global factorization theorem.
-/

/-- The candidate coordinate `(base=10, N=98, stride=2)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 98
  stride := 2
  modulus_pos := by decide

/-- The base-supported preperiod has length one for denominator `98`. -/
theorem denominator_preperiodSteps_eq_one : preperiodSteps 10 98 = 1 := by
  native_decide

/-- Stripping the base-supported factor leaves periodic modulus `49`. -/
theorem denominator_strippedPeriodModulus_eq_forty_nine :
    strippedPeriodModulus 10 98 = 49 := by
  native_decide

/-- The coordinate is a good mode: `98 < 100`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `100`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 100 := by
  native_decide

/-- The quotient in `100 = q*98 + k` is `q = 1`. -/
theorem coordinate_quotientQ_eq_one : coordinate.quotientQ = 1 := by
  native_decide

/-- The remainder in `100 = q*98 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `44`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 44 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-10 `98` candidate window, the observed `remainderIn` states are
exactly the first eight powers of the remainder `2`, reduced modulo `98`. -/
theorem coordinate_stateAlignments_remainderIn_window_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)) = [1, 2, 4, 8, 16, 32, 64, 30] := by
  have h0 : coordinate.longDivisionRemainder 0 = 1 := by rfl
  have h1 : coordinate.longDivisionRemainder 1 = 2 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h2 : coordinate.longDivisionRemainder 2 = 4 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h3 : coordinate.longDivisionRemainder 3 = 8 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h4 : coordinate.longDivisionRemainder 4 = 16 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h5 : coordinate.longDivisionRemainder 5 = 32 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h6 : coordinate.longDivisionRemainder 6 = 64 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h7 : coordinate.longDivisionRemainder 7 = 30 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  exact coordinate.stateAlignments_remainderIn_window_eight_eq_of_longDivisionRemainders
    coordinate_goodMode 1 h0 h1 h2 h3 h4 h5 h6 h7

/-- On the base-10 `98` candidate window, the observed `remainderIn` states are
pairwise distinct. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_window_eq
    coordinate_goodMode 8 1
    coordinate_stateAlignments_remainderIn_window_eight_one
    (by norm_num)

/-- On the base-10 `98` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by finite injective readout. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderIn_nodup
      coordinate_goodMode 8 1 coordinate_stateAlignments_remainderIn_nodup_eight_one

/-- Positive reconstruction exemplar for denominator `98`: on the finite `8/1`
state-alignment window, the raw coefficient factors through the observed
`remainderIn` state. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderIn_nodup
      coordinate_goodMode 8 1
      coordinate_stateAlignments_remainderIn_nodup_eight_one

end QRTour.FutureBase10N98

namespace QRTour.FutureBase12N142

/-! ### Positive Reconstruction Candidate: base 12, N = 142

This packages the first remaining empirical positive reconstruction candidate
emitted by the observability program atlas after the base-10 `98` hook:
`(base, N, m, B, q, k, L, gap) = (12, 142, 2, 144, 1, 2, 1, 32)`.
It is a finite `8/1` proof hook only; it does not add a registry claim,
theorem-witness record, atlas status change, or global factorization theorem.
-/

/-- The candidate coordinate `(base=12, N=142, stride=2)`. -/
def coordinate : BlockCoordinate where
  base := 12
  modulus := 142
  stride := 2
  modulus_pos := by decide

/-- The base-supported preperiod has length one for denominator `142` in base `12`. -/
theorem denominator_preperiodSteps_eq_one : preperiodSteps 12 142 = 1 := by
  native_decide

/-- Stripping the base-supported factor leaves periodic modulus `71`. -/
theorem denominator_strippedPeriodModulus_eq_seventy_one :
    strippedPeriodModulus 12 142 = 71 := by
  native_decide

/-- The coordinate is a good mode: `142 < 144`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `144`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 144 := by
  native_decide

/-- The quotient in `144 = q*142 + k` is `q = 1`. -/
theorem coordinate_quotientQ_eq_one : coordinate.quotientQ = 1 := by
  native_decide

/-- The remainder in `144 = q*142 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `32`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 32 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-12 `142` candidate window, the observed `remainderIn` states
are exactly the first eight powers of the remainder `2`, reduced modulo `142`. -/
theorem coordinate_stateAlignments_remainderIn_window_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)) = [1, 2, 4, 8, 16, 32, 64, 128] := by
  have h0 : coordinate.longDivisionRemainder 0 = 1 := by rfl
  have h1 : coordinate.longDivisionRemainder 1 = 2 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h2 : coordinate.longDivisionRemainder 2 = 4 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h3 : coordinate.longDivisionRemainder 3 = 8 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h4 : coordinate.longDivisionRemainder 4 = 16 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h5 : coordinate.longDivisionRemainder 5 = 32 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h6 : coordinate.longDivisionRemainder 6 = 64 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h7 : coordinate.longDivisionRemainder 7 = 128 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  exact coordinate.stateAlignments_remainderIn_window_eight_eq_of_longDivisionRemainders
    coordinate_goodMode 1 h0 h1 h2 h3 h4 h5 h6 h7

/-- On the base-12 `142` candidate window, the observed `remainderIn` states
are pairwise distinct. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_window_eq
    coordinate_goodMode 8 1
    coordinate_stateAlignments_remainderIn_window_eight_one
    (by norm_num)

/-- On the base-12 `142` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by finite injective readout. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderIn_nodup
      coordinate_goodMode 8 1 coordinate_stateAlignments_remainderIn_nodup_eight_one

/-- Positive reconstruction exemplar for denominator `142`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderIn_nodup
      coordinate_goodMode 8 1
      coordinate_stateAlignments_remainderIn_nodup_eight_one

end QRTour.FutureBase12N142

namespace QRTour.FutureBase7N47

/-! ### Positive Reconstruction Candidate: base 7, N = 47

This packages the next empirical positive reconstruction candidate emitted by
the observability program atlas after the base-12 `142` hook:
`(base, N, m, B, q, k, L, gap) = (7, 47, 2, 49, 1, 2, 1, 38)`.
It is a finite `8/1` proof hook only; it does not add a registry claim,
theorem-witness record, atlas status change, or global factorization theorem.
-/

/-- The candidate coordinate `(base=7, N=47, stride=2)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 47
  stride := 2
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `47` in base `7`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 7 47 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `47`. -/
theorem denominator_strippedPeriodModulus_eq_forty_seven :
    strippedPeriodModulus 7 47 = 47 := by
  native_decide

/-- The coordinate is a good mode: `47 < 49`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `49`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 49 := by
  native_decide

/-- The quotient in `49 = q*47 + k` is `q = 1`. -/
theorem coordinate_quotientQ_eq_one : coordinate.quotientQ = 1 := by
  native_decide

/-- The remainder in `49 = q*47 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `38`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 38 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-7 `47` candidate window, the observed `remainderIn` states
are exactly the first eight powers of the remainder `2`, reduced modulo `47`. -/
theorem coordinate_stateAlignments_remainderIn_window_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)) = [1, 2, 4, 8, 16, 32, 17, 34] := by
  have h0 : coordinate.longDivisionRemainder 0 = 1 := by rfl
  have h1 : coordinate.longDivisionRemainder 1 = 2 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h2 : coordinate.longDivisionRemainder 2 = 4 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h3 : coordinate.longDivisionRemainder 3 = 8 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h4 : coordinate.longDivisionRemainder 4 = 16 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h5 : coordinate.longDivisionRemainder 5 = 32 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h6 : coordinate.longDivisionRemainder 6 = 17 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h7 : coordinate.longDivisionRemainder 7 = 34 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  exact coordinate.stateAlignments_remainderIn_window_eight_eq_of_longDivisionRemainders
    coordinate_goodMode 1 h0 h1 h2 h3 h4 h5 h6 h7

/-- On the base-7 `47` candidate window, the observed `remainderIn` states are
pairwise distinct. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_window_eq
    coordinate_goodMode 8 1
    coordinate_stateAlignments_remainderIn_window_eight_one
    (by norm_num)

/-- On the base-7 `47` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by finite injective readout. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderIn_nodup
      coordinate_goodMode 8 1 coordinate_stateAlignments_remainderIn_nodup_eight_one

/-- Positive reconstruction exemplar for denominator `47`: on the finite `8/1`
state-alignment window, the raw coefficient factors through the observed
`remainderIn` state. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderIn_nodup
      coordinate_goodMode 8 1
      coordinate_stateAlignments_remainderIn_nodup_eight_one

end QRTour.FutureBase7N47

namespace QRTour.FutureBase12N71

/-! ### Positive Reconstruction Candidate: base 12, N = 71

This packages the next empirical positive reconstruction candidate emitted by
the observability program atlas after the base-7 `47` hook:
`(base, N, m, B, q, k, L, gap) = (12, 71, 2, 144, 2, 2, 1, 64)`.
It is a finite `8/1` proof hook only; it does not add a registry claim,
theorem-witness record, atlas status change, or global factorization theorem.
-/

/-- The candidate coordinate `(base=12, N=71, stride=2)`. -/
def coordinate : BlockCoordinate where
  base := 12
  modulus := 71
  stride := 2
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `71` in base `12`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 12 71 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `71`. -/
theorem denominator_strippedPeriodModulus_eq_seventy_one :
    strippedPeriodModulus 12 71 = 71 := by
  native_decide

/-- The coordinate is a good mode: `71 < 144`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `144`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 144 := by
  native_decide

/-- The quotient in `144 = q*71 + k` is `q = 2`. -/
theorem coordinate_quotientQ_eq_two : coordinate.quotientQ = 2 := by
  native_decide

/-- The remainder in `144 = q*71 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `64`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 64 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-12 `71` candidate window, the observed `remainderIn` states
are exactly the first eight powers of the remainder `2`, reduced modulo `71`. -/
theorem coordinate_stateAlignments_remainderIn_window_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)) = [1, 2, 4, 8, 16, 32, 64, 57] := by
  have h0 : coordinate.longDivisionRemainder 0 = 1 := by rfl
  have h1 : coordinate.longDivisionRemainder 1 = 2 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h2 : coordinate.longDivisionRemainder 2 = 4 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h3 : coordinate.longDivisionRemainder 3 = 8 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h4 : coordinate.longDivisionRemainder 4 = 16 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h5 : coordinate.longDivisionRemainder 5 = 32 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h6 : coordinate.longDivisionRemainder 6 = 64 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h7 : coordinate.longDivisionRemainder 7 = 57 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  exact coordinate.stateAlignments_remainderIn_window_eight_eq_of_longDivisionRemainders
    coordinate_goodMode 1 h0 h1 h2 h3 h4 h5 h6 h7

/-- On the base-12 `71` candidate window, the observed `remainderIn` states
are pairwise distinct. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_window_eq
    coordinate_goodMode 8 1
    coordinate_stateAlignments_remainderIn_window_eight_one
    (by norm_num)

/-- On the base-12 `71` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by finite injective readout. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderIn_nodup
      coordinate_goodMode 8 1 coordinate_stateAlignments_remainderIn_nodup_eight_one

/-- Positive reconstruction exemplar for denominator `71`: on the finite `8/1`
state-alignment window, the raw coefficient factors through the observed
`remainderIn` state. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderIn_nodup
      coordinate_goodMode 8 1
      coordinate_stateAlignments_remainderIn_nodup_eight_one

end QRTour.FutureBase12N71

namespace QRTour.FutureBase10N49

/-! ### Positive Reconstruction Candidate: base 10, N = 49

This packages the next empirical positive reconstruction candidate emitted by
the observability program atlas after the base-12 `71` hook:
`(base, N, m, B, q, k, L, gap) = (10, 49, 2, 100, 2, 2, 1, 88)`.
It is a finite `8/1` proof hook only; it does not add a registry claim,
theorem-witness record, atlas status change, or global factorization theorem.
-/

/-- The candidate coordinate `(base=10, N=49, stride=2)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 49
  stride := 2
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `49` in base `10`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 10 49 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `49`. -/
theorem denominator_strippedPeriodModulus_eq_forty_nine :
    strippedPeriodModulus 10 49 = 49 := by
  native_decide

/-- The coordinate is a good mode: `49 < 100`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `100`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 100 := by
  native_decide

/-- The quotient in `100 = q*49 + k` is `q = 2`. -/
theorem coordinate_quotientQ_eq_two : coordinate.quotientQ = 2 := by
  native_decide

/-- The remainder in `100 = q*49 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `88`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 88 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-10 `49` candidate window, the observed `remainderIn` states
are exactly the first eight powers of the remainder `2`, reduced modulo `49`. -/
theorem coordinate_stateAlignments_remainderIn_window_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)) = [1, 2, 4, 8, 16, 32, 15, 30] := by
  have h0 : coordinate.longDivisionRemainder 0 = 1 := by rfl
  have h1 : coordinate.longDivisionRemainder 1 = 2 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h2 : coordinate.longDivisionRemainder 2 = 4 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h3 : coordinate.longDivisionRemainder 3 = 8 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h4 : coordinate.longDivisionRemainder 4 = 16 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h5 : coordinate.longDivisionRemainder 5 = 32 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h6 : coordinate.longDivisionRemainder 6 = 15 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h7 : coordinate.longDivisionRemainder 7 = 30 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  exact coordinate.stateAlignments_remainderIn_window_eight_eq_of_longDivisionRemainders
    coordinate_goodMode 1 h0 h1 h2 h3 h4 h5 h6 h7

/-- On the base-10 `49` candidate window, the observed `remainderIn` states
are pairwise distinct. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_window_eq
    coordinate_goodMode 8 1
    coordinate_stateAlignments_remainderIn_window_eight_one
    (by norm_num)

/-- On the base-10 `49` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by finite injective readout. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderIn_nodup
      coordinate_goodMode 8 1 coordinate_stateAlignments_remainderIn_nodup_eight_one

/-- Positive reconstruction exemplar for denominator `49`: on the finite `8/1`
state-alignment window, the raw coefficient factors through the observed
`remainderIn` state. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderIn_nodup
      coordinate_goodMode 8 1
      coordinate_stateAlignments_remainderIn_nodup_eight_one

end QRTour.FutureBase10N49

namespace QRTour.FutureBase30N299

/-! ### Positive Reconstruction Candidate: base 30, N = 299

This packages the next empirical positive reconstruction candidate emitted by
the observability program atlas after the base-10 `49` hook:
`(base, N, m, B, q, k, L, gap) = (30, 299, 2, 900, 3, 3, 1, 117)`.
It is a finite `8/1` proof hook only; it does not add a registry claim,
theorem-witness record, atlas status change, or global factorization theorem.
-/

/-- The candidate coordinate `(base=30, N=299, stride=2)`. -/
def coordinate : BlockCoordinate where
  base := 30
  modulus := 299
  stride := 2
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `299` in base `30`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 30 299 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `299`. -/
theorem denominator_strippedPeriodModulus_eq_two_hundred_ninety_nine :
    strippedPeriodModulus 30 299 = 299 := by
  native_decide

/-- The coordinate is a good mode: `299 < 900`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `900`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 900 := by
  native_decide

/-- The quotient in `900 = q*299 + k` is `q = 3`. -/
theorem coordinate_quotientQ_eq_three : coordinate.quotientQ = 3 := by
  native_decide

/-- The remainder in `900 = q*299 + k` is `k = 3`. -/
theorem coordinate_remainderK_eq_three : coordinate.remainderK = 3 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `117`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 117 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-30 `299` candidate window, the observed `remainderIn` states
are exactly the first eight powers of the remainder `3`, reduced modulo `299`. -/
theorem coordinate_stateAlignments_remainderIn_window_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)) = [1, 3, 9, 27, 81, 243, 131, 94] := by
  have h0 : coordinate.longDivisionRemainder 0 = 1 := by rfl
  have h1 : coordinate.longDivisionRemainder 1 = 3 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h2 : coordinate.longDivisionRemainder 2 = 9 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h3 : coordinate.longDivisionRemainder 3 = 27 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h4 : coordinate.longDivisionRemainder 4 = 81 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h5 : coordinate.longDivisionRemainder 5 = 243 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h6 : coordinate.longDivisionRemainder 6 = 131 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  have h7 : coordinate.longDivisionRemainder 7 = 94 := by
    rw [coordinate.longDivisionRemainder_eq_pow_mod]
    norm_num [coordinate, BlockCoordinate.blockBase]
  exact coordinate.stateAlignments_remainderIn_window_eight_eq_of_longDivisionRemainders
    coordinate_goodMode 1 h0 h1 h2 h3 h4 h5 h6 h7

/-- On the base-30 `299` candidate window, the observed `remainderIn` states
are pairwise distinct. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_window_eq
    coordinate_goodMode 8 1
    coordinate_stateAlignments_remainderIn_window_eight_one
    (by norm_num)

/-- On the base-30 `299` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by finite injective readout. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderIn_nodup
      coordinate_goodMode 8 1 coordinate_stateAlignments_remainderIn_nodup_eight_one

/-- Positive reconstruction exemplar for denominator `299`: on the finite `8/1`
state-alignment window, the raw coefficient factors through the observed
`remainderIn` state. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderIn_nodup
      coordinate_goodMode 8 1
      coordinate_stateAlignments_remainderIn_nodup_eight_one

end QRTour.FutureBase30N299

namespace QRTour.FutureBase7N170

/-! ### Positive Reconstruction Candidate: base 7, N = 170

This packages the first empirical positive reconstruction candidate emitted by
the observability program atlas after the base-30 `299` hook:
`(base, N, m, B, q, k, L, gap) = (7, 170, 3, 343, 2, 3, 1, 255)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=7, N=170, stride=3)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 170
  stride := 3
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `170` in base `7`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 7 170 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `170`. -/
theorem denominator_strippedPeriodModulus_eq_one_hundred_seventy :
    strippedPeriodModulus 7 170 = 170 := by
  native_decide

/-- The coordinate is a good mode: `170 < 343`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `343`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 343 := by
  native_decide

/-- The quotient in `343 = q*170 + k` is `q = 2`. -/
theorem coordinate_quotientQ_eq_two : coordinate.quotientQ = 2 := by
  native_decide

/-- The remainder in `343 = q*170 + k` is `k = 3`. -/
theorem coordinate_remainderK_eq_three : coordinate.remainderK = 3 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `255`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 255 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-7 `170` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 3, 9, 27, 81, 73, 49, 147] := by
  native_decide

/-- The base-7 `170` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-7 `170` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-7 `170` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `170`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase7N170

namespace QRTour.Base7K3PositiveReconstruction

/-! ### Base-7, remainder-k = 3 positive reconstruction family

This packages the first family-level response to the P1 positive reconstruction
frontier. The observability program atlas identifies `(base, N, m, B, q, k, L,
gap) = (7, 340, 3, 343, 1, 3, 1, 299)` as the first unpinned
power-residue no-collision seed after the source-pinned `N = 170` hook.

Rather than adding another copied finite source pin, this namespace proves an
explicit divisor-family criterion for the shared `(base, B, k) = (7, 343, 3)`
coordinate family. It remains finite-window support only: no registry claim,
theorem-witness record, atlas status change, `small_k_visibility_threshold`
closure, or `carry_dfa_factorization` closure is added.
-/

/-- The base-7, stride-3 moduli in the `B = 343`, `k = 3` divisor family whose
eight-entry power-residue window is collision-free. Smaller divisors of
`B-k = 340`, such as `4`, `5`, `10`, and `20`, fail this finite criterion. -/
def moduli : List ℕ := [17, 34, 68, 85, 170, 340]

/-- Explicit no-collision criterion for the base-7, stride-3 divisor family:
for the listed moduli, the first eight full-modulus power residues
`3^j % N` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 7) (hstride : C.stride = 3)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with hmod | hmod | hmod | hmod | hmod | hmod
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide

/-- The base-7, stride-3 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 7) (hstride : C.stride = 3)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-7, stride-3 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 7) (hstride : C.stride = 3)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The source-pinned `N = 170` hook and the first unpinned `N = 340` seed sit
inside the same explicit no-collision divisor family. -/
theorem n170_n340_powerResidues_nodup_eight_pair :
    ((List.range 8).map
      (fun j => FutureBase7N170.coordinate.remainderK ^ j %
        FutureBase7N170.coordinate.modulus)).Nodup ∧
    ((List.range 8).map (fun j => 3 ^ j % 340)).Nodup := by
  constructor
  · exact FutureBase7N170.coordinate_remainderK_powerResidues_nodup_eight
  · native_decide

end QRTour.Base7K3PositiveReconstruction

namespace QRTour.Base30K3PositiveReconstruction

/-! ### Base-30, remainder-k = 3 positive reconstruction family

The observability program atlas next exposes `(base, N, m, B, q, k, L, gap) =
(30, 897, 2, 900, 1, 3, 1, 639)` as the first source-unpinned and
family-uncovered power-residue no-collision row after the source-pinned
`N = 299` hook.

This namespace proves the finite same-base/block-remainder response for the
shared `(base, B, k) = (30, 900, 3)` divisor family. It remains finite-window
support only: no registry claim, theorem-witness record, atlas status change,
`small_k_visibility_threshold` closure, or `carry_dfa_factorization` closure is
added.
-/

/-- The base-30, stride-2 moduli in the `B = 900`, `k = 3` divisor family whose
eight-entry power-residue window is collision-free. Divisors of `B-k = 897`
such as `1`, `3`, `13`, and `39` fail this finite criterion. -/
def moduli : List ℕ := [23, 69, 299, 897]

/-- Explicit no-collision criterion for the base-30, stride-2 divisor family:
for the listed moduli, the first eight full-modulus power residues
`3^j % N` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 30) (hstride : C.stride = 2)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with hmod | hmod | hmod | hmod
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide

/-- The base-30, stride-2 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 30) (hstride : C.stride = 2)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-30, stride-2 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 30) (hstride : C.stride = 2)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The source-pinned `N = 299` hook and the first uncovered `N = 897` seed
sit inside the same explicit no-collision divisor family. -/
theorem n299_n897_powerResidues_nodup_eight_pair :
    ((List.range 8).map
      (fun j => FutureBase30N299.coordinate.remainderK ^ j %
        FutureBase30N299.coordinate.modulus)).Nodup ∧
    ((List.range 8).map (fun j => 3 ^ j % 897)).Nodup := by
  constructor
  · exact
      remainderK_powerResidues_nodup_eight_of_mem
        FutureBase30N299.coordinate rfl rfl (by simp [moduli, FutureBase30N299.coordinate])
  · native_decide

end QRTour.Base30K3PositiveReconstruction

namespace QRTour.Base10K4PositiveReconstruction

/-! ### Base-10, remainder-k = 4 positive reconstruction family

The observability program atlas next exposes `(base, N, m, B, q, k, L, gap) =
(10, 498, 3, 1000, 2, 4, 1, 928)` as the first source-unpinned and
family-uncovered power-residue no-collision row after the source-pinned
`N = 996` hook.

This namespace proves the finite same-base/block-remainder response for the
shared `(base, B, k) = (10, 1000, 4)` divisor family. It remains finite-window
support only: no registry claim, theorem-witness record, atlas status change,
`small_k_visibility_threshold` closure, or `carry_dfa_factorization` closure is
added.
-/

/-- The base-10, stride-3 moduli in the `B = 1000`, `k = 4` divisor family
whose eight-entry power-residue window is collision-free. Divisors of
`B-k = 996` such as `1`, `2`, `3`, `4`, `6`, and `12` fail this finite
criterion. -/
def moduli : List ℕ := [83, 166, 249, 332, 498, 996]

/-- Explicit no-collision criterion for the base-10, stride-3 divisor family:
for the listed moduli, the first eight full-modulus power residues
`4^j % N` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 10) (hstride : C.stride = 3)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with hmod | hmod | hmod | hmod | hmod | hmod
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide

/-- The base-10, stride-3 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 10) (hstride : C.stride = 3)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-10, stride-3 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 10) (hstride : C.stride = 3)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The first uncovered `N = 498` seed and the source-pinned `N = 996` hook
sit inside the same explicit no-collision divisor family. -/
theorem n498_n996_powerResidues_nodup_eight_pair :
    ((List.range 8).map (fun j => 4 ^ j % 498)).Nodup ∧
    ((List.range 8).map (fun j => 4 ^ j % 996)).Nodup := by
  constructor <;> native_decide

end QRTour.Base10K4PositiveReconstruction

namespace QRTour.Base10Stride4K4PositiveReconstruction

/-! ### Base-10, stride-4, remainder-k = 4 positive reconstruction family

The observability program atlas next exposes `(base, N, m, B, q, k, L, gap) =
(10, 714, 4, 10000, 14, 4, 1, 2496)` as the first source-unpinned and
family-uncovered power-residue no-collision row after the source-pinned
`N = 294` hook.

This namespace proves the finite same-base/block-remainder response for the
shared `(base, B, k) = (10, 10000, 4)` divisor family. It remains finite-window
support only: no registry claim, theorem-witness record, atlas status change,
`small_k_visibility_threshold` closure, or `carry_dfa_factorization` closure is
added.
-/

/-- The base-10, stride-4 moduli in the `B = 10000`, `k = 4` divisor family
whose eight-entry power-residue window is collision-free. Divisors of
`B-k = 9996` such as `6`, `7`, `12`, `14`, `17`, and `34` fail this finite
criterion. -/
def moduli : List ℕ := [49, 98, 119, 147, 196, 238, 294, 357, 476, 588, 714, 833]

/-- Explicit no-collision criterion for the base-10, stride-4 divisor family:
for the listed moduli, the first eight full-modulus power residues
`4^j % N` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 10) (hstride : C.stride = 4)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with
    hmod | hmod | hmod | hmod | hmod | hmod |
    hmod | hmod | hmod | hmod | hmod | hmod
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide

/-- The base-10, stride-4 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 10) (hstride : C.stride = 4)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-10, stride-4 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 10) (hstride : C.stride = 4)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The source-pinned `N = 294` hook and the first uncovered `N = 714` seed
sit inside the same explicit no-collision divisor family. -/
theorem n294_n714_powerResidues_nodup_eight_pair :
    ((List.range 8).map (fun j => 4 ^ j % 294)).Nodup ∧
    ((List.range 8).map (fun j => 4 ^ j % 714)).Nodup := by
  constructor <;> native_decide

end QRTour.Base10Stride4K4PositiveReconstruction

namespace QRTour.Base10Stride5K6PositiveReconstruction

/-! ### Base-10, stride-5, remainder-k = 6 positive reconstruction family

The observability program atlas next exposes `(base, N, m, B, q, k, L, gap) =
(10, 289, 5, 100000, 346, 6, 1, 52864)` as the first source-unpinned and
family-uncovered power-residue no-collision row after the source-pinned
`N = 578` hook.

This namespace proves the finite same-base/block-remainder response for the
shared `(base, B, k) = (10, 100000, 6)` divisor family. It remains
finite-window support only: no registry claim, theorem-witness record, atlas
status change, `small_k_visibility_threshold` closure, or
`carry_dfa_factorization` closure is added.
-/

/-- The base-10, stride-5 moduli in the `B = 100000`, `k = 6` divisor family
whose eight-entry power-residue window is collision-free. Divisors of
`B-k = 99994`, namely `1` and `2`, fail this finite criterion. -/
def moduli : List ℕ :=
  [17, 34, 173, 289, 346, 578, 2941, 5882, 49997, 99994]

/-- Explicit no-collision criterion for the base-10, stride-5 divisor family:
for the listed moduli, the first eight full-modulus power residues
`6^j % N` are pairwise distinct. -/
theorem powerResidues_nodup_eight_of_mem
    {N : ℕ} (hmod : N ∈ moduli) :
    ((List.range 8).map (fun j => 6 ^ j % N)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with
    hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide

/-- Explicit no-collision criterion for the base-10, stride-5 divisor family:
for the listed coordinate moduli, the first eight full-modulus power residues
`C.remainderK^j % C.modulus` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 10) (hstride : C.stride = 5)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  have hmod' := hmod
  have hrem : C.remainderK = 6 := by
    simp [moduli] at hmod'
    rcases hmod' with
      hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod'
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
  rw [hrem]
  exact powerResidues_nodup_eight_of_mem hmod

/-- The base-10, stride-5 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 10) (hstride : C.stride = 5)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-10, stride-5 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 10) (hstride : C.stride = 5)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The first uncovered `N = 289` seed and the source-pinned `N = 578` hook
sit inside the same explicit no-collision divisor family. -/
theorem n289_n578_powerResidues_nodup_eight_pair :
    ((List.range 8).map (fun j => 6 ^ j % 289)).Nodup ∧
    ((List.range 8).map (fun j => 6 ^ j % 578)).Nodup := by
  constructor <;> native_decide

end QRTour.Base10Stride5K6PositiveReconstruction

namespace QRTour.Base10Stride5K4PositiveReconstruction

/-! ### Base-10, stride-5, remainder-k = 4 positive reconstruction family

The observability program atlas next exposes `(base, N, m, B, q, k, L, gap) =
(10, 641, 5, 100000, 156, 4, 1, 76384)` as the first source-unpinned and
family-uncovered power-residue no-collision row after the base-12 stride-5
`k = 3` family theorem.

This namespace proves the finite same-base/block-remainder response for the
shared `(base, B, k) = (10, 100000, 4)` divisor family. It remains
finite-window support only: no registry claim, theorem-witness record, atlas
status change, `small_k_visibility_threshold` closure, or
`carry_dfa_factorization` closure is added.
-/

/-- The base-10, stride-5 moduli in the `B = 100000`, `k = 4` divisor family
whose eight-entry power-residue window is collision-free. Good divisors of
`B-k = 99996`, namely `6, 12, 13, 26, 39, 52, 78, 156`, fail this finite
criterion; divisors `1, 2, 3, 4` are not good coordinates. -/
def moduli : List ℕ :=
  [641, 1282, 1923, 2564, 3846, 7692, 8333, 16666, 24999, 33332, 49998, 99996]

/-- Explicit no-collision criterion for the base-10, stride-5 divisor family:
for the listed moduli, the first eight full-modulus power residues
`4^j % N` are pairwise distinct. -/
theorem powerResidues_nodup_eight_of_mem
    {N : ℕ} (hmod : N ∈ moduli) :
    ((List.range 8).map (fun j => 4 ^ j % N)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with
    hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod
  all_goals
    rw [hmod]
    native_decide

/-- Explicit no-collision criterion for the base-10, stride-5 divisor family:
for the listed coordinate moduli, the first eight full-modulus power residues
`C.remainderK^j % C.modulus` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 10) (hstride : C.stride = 5)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  have hmod' := hmod
  have hrem : C.remainderK = 4 := by
    simp [moduli] at hmod'
    rcases hmod' with
      hmod' | hmod' | hmod' | hmod' | hmod' | hmod' |
      hmod' | hmod' | hmod' | hmod' | hmod' | hmod'
    all_goals
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
  rw [hrem]
  exact powerResidues_nodup_eight_of_mem hmod

/-- The base-10, stride-5 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 10) (hstride : C.stride = 5)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-10, stride-5 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 10) (hstride : C.stride = 5)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The first uncovered `N = 641` seed and the paired `N = 1282` member sit
inside the same explicit no-collision divisor family. -/
theorem n641_n1282_powerResidues_nodup_eight_pair :
    ((List.range 8).map (fun j => 4 ^ j % 641)).Nodup ∧
    ((List.range 8).map (fun j => 4 ^ j % 1282)).Nodup := by
  constructor <;> native_decide

end QRTour.Base10Stride5K4PositiveReconstruction

namespace QRTour.Base12Stride5K3PositiveReconstruction

/-! ### Base-12, stride-5, remainder-k = 3 positive reconstruction family

The observability program atlas next exposes `(base, N, m, B, q, k, L, gap) =
(12, 289, 5, 248832, 861, 3, 1, 74115)` as the first source-unpinned and
family-uncovered power-residue no-collision row after the no-wrap
`N = 149` hook.

This namespace proves the finite same-base/block-remainder response for the
shared `(base, B, k) = (12, 248832, 3)` divisor family. It remains
finite-window support only: no registry claim, theorem-witness record, atlas
status change, `small_k_visibility_threshold` closure, or
`carry_dfa_factorization` closure is added.
-/

/-- The base-12, stride-5 moduli in the `B = 248832`, `k = 3` divisor family
whose eight-entry power-residue window is collision-free. Divisors of
`B-k = 248829`, namely `7` and `21`, fail this finite criterion. -/
def moduli : List ℕ :=
  [17, 41, 51, 119, 123, 287, 289, 357, 697, 861, 867, 2023, 2091,
    4879, 6069, 11849, 14637, 35547, 82943, 248829]

/-- Explicit no-collision criterion for the base-12, stride-5 divisor family:
for the listed moduli, the first eight full-modulus power residues
`3^j % N` are pairwise distinct. -/
theorem powerResidues_nodup_eight_of_mem
    {N : ℕ} (hmod : N ∈ moduli) :
    ((List.range 8).map (fun j => 3 ^ j % N)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with
    hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod |
    hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod
  all_goals
    rw [hmod]
    native_decide

/-- Explicit no-collision criterion for the base-12, stride-5 divisor family:
for the listed coordinate moduli, the first eight full-modulus power residues
`C.remainderK^j % C.modulus` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 12) (hstride : C.stride = 5)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  have hmod' := hmod
  have hrem : C.remainderK = 3 := by
    simp [moduli] at hmod'
    rcases hmod' with
      hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' |
      hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod'
    all_goals
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
  rw [hrem]
  exact powerResidues_nodup_eight_of_mem hmod

/-- The base-12, stride-5 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 12) (hstride : C.stride = 5)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-12, stride-5 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 12) (hstride : C.stride = 5)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The first uncovered `N = 289` seed and the paired `N = 861` member sit
inside the same explicit no-collision divisor family. -/
theorem n289_n861_powerResidues_nodup_eight_pair :
    ((List.range 8).map (fun j => 3 ^ j % 289)).Nodup ∧
    ((List.range 8).map (fun j => 3 ^ j % 861)).Nodup := by
  constructor <;> native_decide

end QRTour.Base12Stride5K3PositiveReconstruction

namespace QRTour.Base12K3PositiveReconstruction

/-! ### Base-12, remainder-k = 3 positive reconstruction family

The observability program atlas next exposes `(base, N, m, B, q, k, L, gap) =
(12, 75, 3, 1728, 23, 3, 1, 1161)` as the first source-unpinned and
family-uncovered power-residue no-collision row after the source-pinned
`N = 575` hook.

This namespace proves the finite same-base/block-remainder response for the
shared `(base, B, k) = (12, 1728, 3)` divisor family. It remains finite-window
support only: no registry claim, theorem-witness record, atlas status change,
`small_k_visibility_threshold` closure, or `carry_dfa_factorization` closure is
added.
-/

/-- The base-12, stride-3 moduli in the `B = 1728`, `k = 3` divisor family
whose eight-entry power-residue window is collision-free. Divisors of
`B-k = 1725` such as `1`, `3`, `5`, and `15` fail this finite criterion. -/
def moduli : List ℕ := [23, 25, 69, 75, 115, 345, 575, 1725]

/-- Explicit no-collision criterion for the base-12, stride-3 divisor family:
for the listed moduli, the first eight full-modulus power residues
`3^j % N` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 12) (hstride : C.stride = 3)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide

/-- The base-12, stride-3 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 12) (hstride : C.stride = 3)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-12, stride-3 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 12) (hstride : C.stride = 3)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The first uncovered `N = 75` seed and the source-pinned `N = 575` hook
sit inside the same explicit no-collision divisor family. -/
theorem n75_n575_powerResidues_nodup_eight_pair :
    ((List.range 8).map (fun j => 3 ^ j % 75)).Nodup ∧
    ((List.range 8).map (fun j => 3 ^ j % 575)).Nodup := by
  constructor <;> native_decide

end QRTour.Base12K3PositiveReconstruction

namespace QRTour.FutureBase10N997

/-! ### Positive Reconstruction Candidate: base 10, N = 997

This packages the first source-unpinned and family-uncovered
power-residue no-collision row emitted by the observability program atlas after
the base-7, stride-3 divisor-family criterion:
`(base, N, m, B, q, k, L, gap) = (10, 997, 3, 1000, 1, 3, 1, 439)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=10, N=997, stride=3)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 997
  stride := 3
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `997` in base `10`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 10 997 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `997`. -/
theorem denominator_strippedPeriodModulus_eq_nine_hundred_ninety_seven :
    strippedPeriodModulus 10 997 = 997 := by
  native_decide

/-- The coordinate is a good mode: `997 < 1000`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `1000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 1000 := by
  native_decide

/-- The quotient in `1000 = q*997 + k` is `q = 1`. -/
theorem coordinate_quotientQ_eq_one : coordinate.quotientQ = 1 := by
  native_decide

/-- The remainder in `1000 = q*997 + k` is `k = 3`. -/
theorem coordinate_remainderK_eq_three : coordinate.remainderK = 3 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `439`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 439 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-10 `997` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 3, 9, 27, 81, 243, 729, 193] := by
  native_decide

/-- The base-10 `997` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-10 `997` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-10 `997` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `997`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase10N997

namespace QRTour.FutureBase12N575

/-! ### Positive Reconstruction Candidate: base 12, N = 575

This packages the first source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas after
the base-10, stride-3 `k = 4` divisor-family criterion:
`(base, N, m, B, q, k, L, gap) = (12, 575, 3, 1728, 3, 3, 1, 1053)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=12, N=575, stride=3)`. -/
def coordinate : BlockCoordinate where
  base := 12
  modulus := 575
  stride := 3
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `575` in base `12`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 12 575 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `575`. -/
theorem denominator_strippedPeriodModulus_eq_five_hundred_seventy_five :
    strippedPeriodModulus 12 575 = 575 := by
  native_decide

/-- The coordinate is a good mode: `575 < 1728`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `1728`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 1728 := by
  native_decide

/-- The quotient in `1728 = q*575 + k` is `q = 3`. -/
theorem coordinate_quotientQ_eq_three : coordinate.quotientQ = 3 := by
  native_decide

/-- The remainder in `1728 = q*575 + k` is `k = 3`. -/
theorem coordinate_remainderK_eq_three : coordinate.remainderK = 3 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `1053`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 1053 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-12 `575` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 3, 9, 27, 81, 243, 154, 462] := by
  native_decide

/-- The base-12 `575` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-12 `575` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-12 `575` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `575`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase12N575

namespace QRTour.FutureBase7N1199

/-! ### Positive Reconstruction Candidate: base 7, N = 1199

This packages the first source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas after
the base-12, stride-3 `k = 3` divisor-family criterion:
`(base, N, m, B, q, k, L, gap) = (7, 1199, 4, 2401, 2, 3, 1, 1284)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=7, N=1199, stride=4)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 1199
  stride := 4
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `1199` in base `7`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 7 1199 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `1199`. -/
theorem denominator_strippedPeriodModulus_eq_one_thousand_one_hundred_ninety_nine :
    strippedPeriodModulus 7 1199 = 1199 := by
  native_decide

/-- The coordinate is a good mode: `1199 < 2401`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `2401`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 2401 := by
  native_decide

/-- The quotient in `2401 = q*1199 + k` is `q = 2`. -/
theorem coordinate_quotientQ_eq_two : coordinate.quotientQ = 2 := by
  native_decide

/-- The remainder in `2401 = q*1199 + k` is `k = 3`. -/
theorem coordinate_remainderK_eq_three : coordinate.remainderK = 3 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `1284`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 1284 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-7 `1199` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 3, 9, 27, 81, 243, 729, 988] := by
  native_decide

/-- The base-7 `1199` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-7 `1199` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-7 `1199` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `1199`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase7N1199

namespace QRTour.FutureBase10N294

/-! ### Positive Reconstruction Candidate: base 10, N = 294

This packages the first source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas after
the base-7 denominator-`1199` hook:
`(base, N, m, B, q, k, L, gap) = (10, 294, 4, 10000, 34, 4, 1, 1776)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=10, N=294, stride=4)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 294
  stride := 4
  modulus_pos := by decide

/-- The base-supported preperiod has length one for denominator `294` in base `10`. -/
theorem denominator_preperiodSteps_eq_one : preperiodSteps 10 294 = 1 := by
  native_decide

/-- Stripping the base-supported factor leaves periodic modulus `147`. -/
theorem denominator_strippedPeriodModulus_eq_one_hundred_forty_seven :
    strippedPeriodModulus 10 294 = 147 := by
  native_decide

/-- The coordinate is a good mode: `294 < 10000`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `10000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 10000 := by
  native_decide

/-- The quotient in `10000 = q*294 + k` is `q = 34`. -/
theorem coordinate_quotientQ_eq_thirty_four : coordinate.quotientQ = 34 := by
  native_decide

/-- The remainder in `10000 = q*294 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `1776`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 1776 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-10 `294` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 4, 16, 64, 256, 142, 274, 214] := by
  native_decide

/-- The base-10 `294` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-10 `294` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-10 `294` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `294`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase10N294

namespace QRTour.Base7Stride4K3PositiveReconstruction

/-! ### Base-7, stride-4, remainder-k = 3 positive reconstruction family

The observability program atlas next exposes `(base, N, m, B, q, k, L, gap) =
(7, 109, 4, 2401, 22, 3, 1, 2119)` as the first source-unpinned and
family-uncovered power-residue no-collision row after the source-pinned
`N = 1199` hook.

This namespace proves the finite same-base/block-remainder response for the
shared `(base, B, k) = (7, 2401, 3)` divisor family. It remains finite-window
support only: no registry claim, theorem-witness record, atlas status change,
`small_k_visibility_threshold` closure, or `carry_dfa_factorization` closure is
added.
-/

/-- The base-7, stride-4 moduli in the `B = 2401`, `k = 3` divisor family whose
eight-entry power-residue window is collision-free. Smaller divisors of
`B-k = 2398`, such as `1`, `2`, `11`, and `22`, fail this finite criterion. -/
def moduli : List ℕ := [109, 218, 1199, 2398]

/-- Explicit no-collision criterion for the base-7, stride-4 divisor family:
for the listed moduli, the first eight full-modulus power residues
`3^j % N` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 7) (hstride : C.stride = 4)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with hmod | hmod | hmod | hmod
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide

/-- The base-7, stride-4 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 7) (hstride : C.stride = 4)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-7, stride-4 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 7) (hstride : C.stride = 4)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The first uncovered `N = 109` seed and the source-pinned `N = 1199` hook sit
inside the same explicit no-collision divisor family. -/
theorem n109_n1199_powerResidues_nodup_eight_pair :
    ((List.range 8).map (fun j => 3 ^ j % 109)).Nodup ∧
    ((List.range 8).map
      (fun j => FutureBase7N1199.coordinate.remainderK ^ j %
        FutureBase7N1199.coordinate.modulus)).Nodup := by
  constructor
  · native_decide
  · exact FutureBase7N1199.coordinate_remainderK_powerResidues_nodup_eight

end QRTour.Base7Stride4K3PositiveReconstruction

namespace QRTour.FutureBase7N46

/-! ### Positive Reconstruction Candidate: base 7, N = 46

This packages the previously source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (7, 46, 2, 49, 1, 3, 2, 2171)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/2` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=7, N=46, stride=2)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 46
  stride := 2
  modulus_pos := by decide

/-- The coordinate is a good mode: `46 < 49`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `49`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 49 := by
  native_decide

/-- The quotient in `49 = q*46 + k` is `q = 1`. -/
theorem coordinate_quotientQ_eq_one : coordinate.quotientQ = 1 := by
  native_decide

/-- The remainder in `49 = q*46 + k` is `k = 3`. -/
theorem coordinate_remainderK_eq_three : coordinate.remainderK = 3 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `2171`. -/
theorem coordinate_lookaheadGapNumerator_eight_two :
    coordinate.lookaheadGapNumerator 8 2 = 2171 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Two blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_two :
    coordinate.lookaheadCertificateHolds 8 2 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-7 `46` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 3, 9, 27, 35, 13, 39, 25] := by
  native_decide

/-- The base-7 `46` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-7 `46` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 2).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 2
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-7 `46` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 2
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `46`: on the finite
`8/2` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 2
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase7N46

namespace QRTour.FutureBase12N47

/-! ### Positive Reconstruction Candidate: base 12, N = 47

This packages the previously source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (12, 47, 2, 144, 3, 3, 2, 9639)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/2` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=12, N=47, stride=2)`. -/
def coordinate : BlockCoordinate where
  base := 12
  modulus := 47
  stride := 2
  modulus_pos := by decide

/-- The coordinate is a good mode: `47 < 144`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `144`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 144 := by
  native_decide

/-- The quotient in `144 = q*47 + k` is `q = 3`. -/
theorem coordinate_quotientQ_eq_three : coordinate.quotientQ = 3 := by
  native_decide

/-- The remainder in `144 = q*47 + k` is `k = 3`. -/
theorem coordinate_remainderK_eq_three : coordinate.remainderK = 3 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `9639`. -/
theorem coordinate_lookaheadGapNumerator_eight_two :
    coordinate.lookaheadGapNumerator 8 2 = 9639 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Two blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_two :
    coordinate.lookaheadCertificateHolds 8 2 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-12 `47` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 3, 9, 27, 34, 8, 24, 25] := by
  native_decide

/-- The base-12 `47` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-12 `47` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 2).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 2
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-12 `47` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 2
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `47`: on the finite
`8/2` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 2
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase12N47

namespace QRTour.Base12Stride2K3PositiveReconstruction

/-! ### Base-12, stride-2, remainder-k = 3 positive reconstruction family

The observability program atlas next exposes `(base, N, m, B, q, k, L, gap) =
(12, 141, 2, 144, 1, 3, 2, 10125)` as the first source-unpinned and
theorem-uncovered power-residue no-collision row after the source-pinned
`N = 47` hook.

This namespace proves the finite same-base/block-remainder response for the
shared `(base, B, k) = (12, 144, 3)` divisor family. It remains finite-window
support only: no registry claim, theorem-witness record, atlas status change,
`small_k_visibility_threshold` closure, or `carry_dfa_factorization` closure is
added.
-/

/-- The base-12, stride-2 moduli in the `B = 144`, `k = 3` divisor family whose
eight-entry power-residue window is collision-free. The smaller divisors `1`
and `3` of `B-k = 141` fail this finite criterion. -/
def moduli : List ℕ := [47, 141]

/-- Explicit no-collision criterion for the base-12, stride-2 divisor family:
for the listed coordinate moduli, the first eight full-modulus power residues
`C.remainderK^j % C.modulus` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 12) (hstride : C.stride = 2)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with hmod | hmod
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 3 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide

/-- The base-12, stride-2 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 12) (hstride : C.stride = 2)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-12, stride-2 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 12) (hstride : C.stride = 2)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The source-pinned `N = 47` hook and the first uncovered `N = 141` seed sit
inside the same explicit no-collision divisor family. -/
theorem n47_n141_powerResidues_nodup_eight_pair :
    ((List.range 8).map
      (fun j => FutureBase12N47.coordinate.remainderK ^ j %
        FutureBase12N47.coordinate.modulus)).Nodup ∧
    ((List.range 8).map (fun j => 3 ^ j % 141)).Nodup := by
  constructor
  · exact FutureBase12N47.coordinate_remainderK_powerResidues_nodup_eight
  · native_decide

end QRTour.Base12Stride2K3PositiveReconstruction

namespace QRTour.FutureBase7N141

/-! ### Positive Reconstruction Candidate: base 7, N = 141

This packages the previous source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (7, 141, 4, 2401, 17, 4, 1, 2353)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=7, N=141, stride=4)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 141
  stride := 4
  modulus_pos := by decide

/-- The coordinate is a good mode: `141 < 2401`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `2401`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 2401 := by
  native_decide

/-- The quotient in `2401 = q*141 + k` is `q = 17`. -/
theorem coordinate_quotientQ_eq_seventeen : coordinate.quotientQ = 17 := by
  native_decide

/-- The remainder in `2401 = q*141 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `2353`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 2353 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-7 `141` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 4, 16, 64, 115, 37, 7, 28] := by
  native_decide

/-- The base-7 `141` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-7 `141` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-7 `141` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `141`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase7N141

namespace QRTour.FutureBase12N146

/-! ### Positive Reconstruction Candidate: base 12, N = 146

This packages the current source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (12, 146, 4, 20736, 142, 4, 1, 4352)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=12, N=146, stride=4)`. -/
def coordinate : BlockCoordinate where
  base := 12
  modulus := 146
  stride := 4
  modulus_pos := by decide

/-- The base-supported preperiod has length one for denominator `146` in base `12`. -/
theorem denominator_preperiodSteps_eq_one : preperiodSteps 12 146 = 1 := by
  native_decide

/-- Stripping the base-supported factor leaves periodic modulus `73`. -/
theorem denominator_strippedPeriodModulus_eq_seventy_three :
    strippedPeriodModulus 12 146 = 73 := by
  native_decide

/-- The coordinate is a good mode: `146 < 20736`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `20736`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 20736 := by
  native_decide

/-- The quotient in `20736 = q*146 + k` is `q = 142`. -/
theorem coordinate_quotientQ_eq_one_hundred_forty_two : coordinate.quotientQ = 142 := by
  native_decide

/-- The remainder in `20736 = q*146 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `4352`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 4352 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-12 `146` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 4, 16, 64, 110, 2, 8, 32] := by
  native_decide

/-- The base-12 `146` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-12 `146` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-12 `146` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `146`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase12N146

namespace QRTour.Base12Stride4K4PositiveReconstruction

/-! ### Base-12, stride-4, remainder-k = 4 positive reconstruction family

The observability program atlas next exposes `(base, N, m, B, q, k, L, gap) =
(12, 73, 4, 20736, 284, 4, 1, 8704)` as the first source-unpinned and
theorem-uncovered power-residue no-collision row after the source-pinned
`N = 146` hook.

This namespace proves the finite same-base/block-remainder response for the
shared `(base, B, k) = (12, 20736, 4)` divisor family. It remains finite-window
support only: no registry claim, theorem-witness record, atlas status change,
`small_k_visibility_threshold` closure, or `carry_dfa_factorization` closure is
added.
-/

/-- The base-12, stride-4 moduli in the `B = 20736`, `k = 4` divisor family
whose eight-entry power-residue window is collision-free. The small divisors
`1`, `2`, and `4` of `B-k = 20732` fail this finite criterion. -/
def moduli : List ℕ := [71, 73, 142, 146, 284, 292, 5183, 10366, 20732]

/-- Explicit no-collision criterion for the base-12, stride-4 divisor family:
for the listed coordinate moduli, the first eight full-modulus power residues
`C.remainderK^j % C.modulus` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 12) (hstride : C.stride = 4)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with
    hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide
  · have hrem : C.remainderK = 4 := by
      simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod]
    rw [hrem, hmod]
    native_decide

/-- The base-12, stride-4 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 12) (hstride : C.stride = 4)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-12, stride-4 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 12) (hstride : C.stride = 4)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The first uncovered `N = 73` seed and the source-pinned `N = 146` hook sit
inside the same explicit no-collision divisor family. -/
theorem n73_n146_powerResidues_nodup_eight_pair :
    ((List.range 8).map (fun j => 4 ^ j % 73)).Nodup ∧
    ((List.range 8).map
      (fun j => FutureBase12N146.coordinate.remainderK ^ j %
        FutureBase12N146.coordinate.modulus)).Nodup := by
  constructor
  · native_decide
  · exact FutureBase12N146.coordinate_remainderK_powerResidues_nodup_eight

end QRTour.Base12Stride4K4PositiveReconstruction

namespace QRTour.FutureBase10N769

/-! ### Positive Reconstruction Candidate: base 10, N = 769

This packages the current source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (10, 769, 4, 10000, 13, 3, 1, 4707)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=10, N=769, stride=4)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 769
  stride := 4
  modulus_pos := by decide

/-- The base-supported preperiod is zero for denominator `769` in base `10`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 10 769 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `769`. -/
theorem denominator_strippedPeriodModulus_eq_seven_hundred_sixty_nine :
    strippedPeriodModulus 10 769 = 769 := by
  native_decide

/-- The coordinate is a good mode: `769 < 10000`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `10000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 10000 := by
  native_decide

/-- The quotient in `10000 = q*769 + k` is `q = 13`. -/
theorem coordinate_quotientQ_eq_thirteen : coordinate.quotientQ = 13 := by
  native_decide

/-- The remainder in `10000 = q*769 + k` is `k = 3`. -/
theorem coordinate_remainderK_eq_three : coordinate.remainderK = 3 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `4707`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 4707 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-10 `769` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 3, 9, 27, 81, 243, 729, 649] := by
  native_decide

/-- The base-10 `769` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-10 `769` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-10 `769` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `769`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase10N769

namespace QRTour.FutureBase7N345

/-! ### Positive Reconstruction Candidate: base 7, N = 345

This packages the current source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (7, 345, 6, 117649, 341, 4, 1, 5534)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=7, N=345, stride=6)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 345
  stride := 6
  modulus_pos := by decide

/-- The base-supported preperiod is zero for denominator `345` in base `7`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 7 345 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `345`. -/
theorem denominator_strippedPeriodModulus_eq_three_hundred_forty_five :
    strippedPeriodModulus 7 345 = 345 := by
  native_decide

/-- The coordinate is a good mode: `345 < 117649`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `117649`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 117649 := by
  native_decide

/-- The quotient in `117649 = q*345 + k` is `q = 341`. -/
theorem coordinate_quotientQ_eq_three_hundred_forty_one : coordinate.quotientQ = 341 := by
  native_decide

/-- The remainder in `117649 = q*345 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `5534`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 5534 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-7 `345` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 4, 16, 64, 256, 334, 301, 169] := by
  native_decide

/-- The base-7 `345` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-7 `345` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-7 `345` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `345`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase7N345

namespace QRTour.Base7Stride6K4PositiveReconstruction

/-! ### Base-7, stride-6, remainder-k = 4 positive reconstruction family

The observability program atlas next exposes `(base, N, m, B, q, k, L, gap) =
(7, 465, 6, 117649, 253, 4, 1, 7901)` as the first source-unpinned and
family-uncovered power-residue no-collision row after the source-pinned
`N = 345` hook.

This namespace proves the finite same-base/block-remainder response for the
shared `(base, B, k) = (7, 117649, 4)` divisor family. It remains finite-window
support only: no registry claim, theorem-witness record, atlas status change,
`small_k_visibility_threshold` closure, or `carry_dfa_factorization` closure is
added.
-/

/-- The base-7, stride-6 moduli in the `B = 117649`, `k = 4` divisor family
whose eight-entry power-residue window is collision-free. Divisors of
`B-k = 117645` such as `1`, `3`, `5`, `11`, `15`, `31`, `33`, `93`, `341`,
and `1023` fail this finite criterion. -/
def moduli : List ℕ :=
  [23, 55, 69, 115, 155, 165, 253, 345, 465, 713, 759, 1265, 1705, 2139, 3565,
    3795, 5115, 7843, 10695, 23529, 39215, 117645]

/-- Explicit no-collision criterion for the base-7, stride-6 divisor family:
for the listed moduli, the first eight full-modulus power residues
`4^j % N` are pairwise distinct. -/
theorem powerResidues_nodup_eight_of_mem
    {N : ℕ} (hmod : N ∈ moduli) :
    ((List.range 8).map (fun j => 4 ^ j % N)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with
    hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod |
    hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod | hmod |
    hmod | hmod
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide

/-- Explicit no-collision criterion for the base-7, stride-6 divisor family:
for the listed coordinate moduli, the first eight full-modulus power residues
`C.remainderK^j % C.modulus` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 7) (hstride : C.stride = 6)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  have hmod' := hmod
  have hrem : C.remainderK = 4 := by
    simp [moduli] at hmod'
    rcases hmod' with
      hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' |
      hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' | hmod' |
      hmod' | hmod' | hmod' | hmod'
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
  rw [hrem]
  exact powerResidues_nodup_eight_of_mem hmod

/-- The base-7, stride-6 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 7) (hstride : C.stride = 6)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-7, stride-6 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 7) (hstride : C.stride = 6)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The source-pinned `N = 345` hook and the first uncovered `N = 465` seed sit
inside the same explicit no-collision divisor family. -/
theorem n345_n465_powerResidues_nodup_eight_pair :
    ((List.range 8).map
      (fun j => FutureBase7N345.coordinate.remainderK ^ j %
        FutureBase7N345.coordinate.modulus)).Nodup ∧
    ((List.range 8).map (fun j => 4 ^ j % 465)).Nodup := by
  constructor
  · exact FutureBase7N345.coordinate_remainderK_powerResidues_nodup_eight
  · native_decide

end QRTour.Base7Stride6K4PositiveReconstruction

namespace QRTour.FutureBase7N542

/-! ### Positive Reconstruction Candidate: base 7, N = 542

This packages the current source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (7, 542, 5, 16807, 31, 5, 1, 8472)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=7, N=542, stride=5)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 542
  stride := 5
  modulus_pos := by decide

/-- The base-supported preperiod is zero for denominator `542` in base `7`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 7 542 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `542`. -/
theorem denominator_strippedPeriodModulus_eq_five_hundred_forty_two :
    strippedPeriodModulus 7 542 = 542 := by
  native_decide

/-- The coordinate is a good mode: `542 < 16807`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `16807`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 16807 := by
  native_decide

/-- The quotient in `16807 = q*542 + k` is `q = 31`. -/
theorem coordinate_quotientQ_eq_thirty_one : coordinate.quotientQ = 31 := by
  native_decide

/-- The remainder in `16807 = q*542 + k` is `k = 5`. -/
theorem coordinate_remainderK_eq_five : coordinate.remainderK = 5 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `8472`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 8472 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-7 `542` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 5, 25, 125, 83, 415, 449, 77] := by
  native_decide

/-- The base-7 `542` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-7 `542` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-7 `542` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `542`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase7N542

namespace QRTour.FutureBase30N794

/-! ### Positive Reconstruction Candidate: base 30, N = 794

This packages the current source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (30, 794, 3, 27000, 34, 4, 1, 12776)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=30, N=794, stride=3)`. -/
def coordinate : BlockCoordinate where
  base := 30
  modulus := 794
  stride := 3
  modulus_pos := by decide

/-- The base-supported preperiod has length one for denominator `794` in base `30`. -/
theorem denominator_preperiodSteps_eq_one : preperiodSteps 30 794 = 1 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `397`. -/
theorem denominator_strippedPeriodModulus_eq_three_hundred_ninety_seven :
    strippedPeriodModulus 30 794 = 397 := by
  native_decide

/-- The coordinate is a good mode: `794 < 27000`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `27000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 27000 := by
  native_decide

/-- The quotient in `27000 = q*794 + k` is `q = 34`. -/
theorem coordinate_quotientQ_eq_thirty_four : coordinate.quotientQ = 34 := by
  native_decide

/-- The remainder in `27000 = q*794 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `12776`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 12776 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-30 `794` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 4, 16, 64, 256, 230, 126, 504] := by
  native_decide

/-- The base-30 `794` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-30 `794` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-30 `794` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `794`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase30N794

namespace QRTour.Base30Stride3K4PositiveReconstruction

/-! ### Base-30, stride-3, remainder-k = 4 positive reconstruction family

The observability program atlas next exposes `(base, N, m, B, q, k, L, gap) =
(30, 397, 3, 27000, 68, 4, 1, 25552)` as the first source-unpinned and
family-uncovered power-residue no-collision row after the source-pinned
`N = 794` hook.

This namespace proves the finite same-base/block-remainder response for the
shared `(base, B, k) = (30, 27000, 4)` divisor family. It remains finite-window
support only: no registry claim, theorem-witness record, atlas status change,
`small_k_visibility_threshold` closure, or `carry_dfa_factorization` closure is
added.
-/

/-- The base-30, stride-3 moduli in the `B = 27000`, `k = 4` divisor family
whose eight-entry power-residue window is collision-free. Divisors of
`B-k = 26996` such as `1`, `2`, `4`, `17`, `34`, and `68` fail this finite
criterion. -/
def moduli : List ℕ := [397, 794, 1588, 6749, 13498, 26996]

/-- Explicit no-collision criterion for the base-30, stride-3 divisor family:
for the listed moduli, the first eight full-modulus power residues
`4^j % N` are pairwise distinct. -/
theorem powerResidues_nodup_eight_of_mem
    {N : ℕ} (hmod : N ∈ moduli) :
    ((List.range 8).map (fun j => 4 ^ j % N)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with hmod | hmod | hmod | hmod | hmod | hmod
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide

/-- Explicit no-collision criterion for the base-30, stride-3 divisor family:
for the listed coordinate moduli, the first eight full-modulus power residues
`C.remainderK^j % C.modulus` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 30) (hstride : C.stride = 3)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  have hmod' := hmod
  have hrem : C.remainderK = 4 := by
    simp [moduli] at hmod'
    rcases hmod' with hmod' | hmod' | hmod' | hmod' | hmod' | hmod'
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
  rw [hrem]
  exact powerResidues_nodup_eight_of_mem hmod

/-- The base-30, stride-3 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 30) (hstride : C.stride = 3)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-30, stride-3 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 30) (hstride : C.stride = 3)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The first uncovered `N = 397` seed and the source-pinned `N = 794` hook
sit inside the same explicit no-collision divisor family. -/
theorem n397_n794_powerResidues_nodup_eight_pair :
    ((List.range 8).map (fun j => 4 ^ j % 397)).Nodup ∧
    ((List.range 8).map
      (fun j => FutureBase30N794.coordinate.remainderK ^ j %
        FutureBase30N794.coordinate.modulus)).Nodup := by
  constructor
  · native_decide
  · exact FutureBase30N794.coordinate_remainderK_powerResidues_nodup_eight

end QRTour.Base30Stride3K4PositiveReconstruction

namespace QRTour.FutureBase10N578

/-! ### Positive Reconstruction Candidate: base 10, N = 578

This packages the previous source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (10, 578, 5, 100000, 173, 6, 1, 26432)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=10, N=578, stride=5)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 578
  stride := 5
  modulus_pos := by decide

/-- The base-supported preperiod has length one for denominator `578` in base `10`. -/
theorem denominator_preperiodSteps_eq_one : preperiodSteps 10 578 = 1 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `289`. -/
theorem denominator_strippedPeriodModulus_eq_two_hundred_eighty_nine :
    strippedPeriodModulus 10 578 = 289 := by
  native_decide

/-- The coordinate is a good mode: `578 < 100000`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `100000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 100000 := by
  native_decide

/-- The quotient in `100000 = q*578 + k` is `q = 173`. -/
theorem coordinate_quotientQ_eq_one_hundred_seventy_three :
    coordinate.quotientQ = 173 := by
  native_decide

/-- The remainder in `100000 = q*578 + k` is `k = 6`. -/
theorem coordinate_remainderK_eq_six : coordinate.remainderK = 6 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `26432`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 26432 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-10 `578` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 6, 36, 216, 140, 262, 416, 184] := by
  native_decide

/-- The base-10 `578` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-10 `578` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-10 `578` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `578`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase10N578

namespace QRTour.FutureBase10N277

/-! ### Positive Reconstruction Candidate: base 10, N = 277

This packages the previous source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (10, 277, 5, 100000, 361, 3, 1, 31479)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=10, N=277, stride=5)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 277
  stride := 5
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `277` in base `10`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 10 277 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `277`. -/
theorem denominator_strippedPeriodModulus_eq_two_hundred_seventy_seven :
    strippedPeriodModulus 10 277 = 277 := by
  native_decide

/-- The coordinate is a good mode: `277 < 100000`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `100000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 100000 := by
  native_decide

/-- The quotient in `100000 = q*277 + k` is `q = 361`. -/
theorem coordinate_quotientQ_eq_three_hundred_sixty_one :
    coordinate.quotientQ = 361 := by
  native_decide

/-- The remainder in `100000 = q*277 + k` is `k = 3`. -/
theorem coordinate_remainderK_eq_three : coordinate.remainderK = 3 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `31479`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 31479 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-10 `277` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 3, 9, 27, 81, 243, 175, 248] := by
  native_decide

/-- The base-10 `277` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-10 `277` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-10 `277` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `277`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase10N277

namespace QRTour.FutureBase7N669

/-! ### Positive Reconstruction Candidate: base 7, N = 669

This packages the previous source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (7, 669, 7, 823543, 1231, 4, 1, 32398)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=7, N=669, stride=7)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 669
  stride := 7
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `669` in base `7`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 7 669 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `669`. -/
theorem denominator_strippedPeriodModulus_eq_six_hundred_sixty_nine :
    strippedPeriodModulus 7 669 = 669 := by
  native_decide

/-- The coordinate is a good mode: `669 < 823543`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `823543`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 823543 := by
  native_decide

/-- The quotient in `823543 = q*669 + k` is `q = 1231`. -/
theorem coordinate_quotientQ_eq_one_thousand_two_hundred_thirty_one :
    coordinate.quotientQ = 1231 := by
  native_decide

/-- The remainder in `823543 = q*669 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `32398`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 32398 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-7 `669` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 4, 16, 64, 256, 355, 82, 328] := by
  native_decide

/-- The base-7 `669` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-7 `669` candidate window, the observed `remainderIn` states are
pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-7 `669` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `669`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase7N669

namespace QRTour.FutureBase7N71

/-! ### Positive Reconstruction Candidate: base 7, N = 71

This packages the previous source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (7, 71, 6, 117649, 1657, 2, 1, 46404)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=7, N=71, stride=6)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 71
  stride := 6
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `71` in base `7`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 7 71 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `71`. -/
theorem denominator_strippedPeriodModulus_eq_seventy_one :
    strippedPeriodModulus 7 71 = 71 := by
  native_decide

/-- The coordinate is a good mode: `71 < 117649`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `117649`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 117649 := by
  native_decide

/-- The quotient in `117649 = q*71 + k` is `q = 1657`. -/
theorem coordinate_quotientQ_eq_one_thousand_six_hundred_fifty_seven :
    coordinate.quotientQ = 1657 := by
  native_decide

/-- The remainder in `117649 = q*71 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `46404`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 46404 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-7 `71` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 2, 4, 8, 16, 32, 64, 57] := by
  native_decide

/-- The base-7 `71` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-7 `71` candidate window, the observed `remainderIn` states are
pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-7 `71` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `71`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase7N71

namespace QRTour.FutureBase7N118

/-! ### Positive Reconstruction Candidate: base 7, N = 118

This packages the previous source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (7, 118, 6, 117649, 997, 3, 1, 47027)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=7, N=118, stride=6)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 118
  stride := 6
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `118` in base `7`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 7 118 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `118`. -/
theorem denominator_strippedPeriodModulus_eq_one_hundred_eighteen :
    strippedPeriodModulus 7 118 = 118 := by
  native_decide

/-- The coordinate is a good mode: `118 < 117649`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `117649`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 117649 := by
  native_decide

/-- The quotient in `117649 = q*118 + k` is `q = 997`. -/
theorem coordinate_quotientQ_eq_nine_hundred_ninety_seven :
    coordinate.quotientQ = 997 := by
  native_decide

/-- The remainder in `117649 = q*118 + k` is `k = 3`. -/
theorem coordinate_remainderK_eq_three : coordinate.remainderK = 3 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `47027`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 47027 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-7 `118` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 3, 9, 27, 81, 7, 21, 63] := by
  native_decide

/-- The base-7 `118` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-7 `118` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-7 `118` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `118`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase7N118

namespace QRTour.Base7Stride6K3PositiveReconstruction

/-! ### Base-7, stride-6, remainder-k = 3 positive reconstruction family

The observability program atlas next exposes `(base, N, m, B, q, k, L, gap) =
(7, 997, 6, 117649, 118, 3, 1, 49345)` as the first source-unpinned and
family-uncovered power-residue no-collision row after the source-pinned
`N = 118` hook.

This namespace proves the finite same-base/block-remainder response for the
shared `(base, B, k) = (7, 117649, 3)` divisor family. It remains
finite-window support only: no registry claim, theorem-witness record, atlas
status change, `small_k_visibility_threshold` closure, or
`carry_dfa_factorization` closure is added.
-/

/-- The base-7, stride-6 moduli in the `B = 117649`, `k = 3` divisor family
whose eight-entry power-residue window is collision-free. Divisors of
`B-k = 117646`, namely `1` and `2`, fail this finite criterion. -/
def moduli : List ℕ := [59, 118, 997, 1994, 58823, 117646]

/-- Explicit no-collision criterion for the base-7, stride-6 divisor family:
for the listed moduli, the first eight full-modulus power residues
`3^j % N` are pairwise distinct. -/
theorem powerResidues_nodup_eight_of_mem
    {N : ℕ} (hmod : N ∈ moduli) :
    ((List.range 8).map (fun j => 3 ^ j % N)).Nodup := by
  simp [moduli] at hmod
  rcases hmod with hmod | hmod | hmod | hmod | hmod | hmod
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide
  · rw [hmod]
    native_decide

/-- Explicit no-collision criterion for the base-7, stride-6 divisor family:
for the listed coordinate moduli, the first eight full-modulus power residues
`C.remainderK^j % C.modulus` are pairwise distinct. -/
theorem remainderK_powerResidues_nodup_eight_of_mem
    (C : BlockCoordinate) (hbase : C.base = 7) (hstride : C.stride = 6)
    (hmod : C.modulus ∈ moduli) :
    ((List.range 8).map
      (fun j => C.remainderK ^ j % C.modulus)).Nodup := by
  have hmod' := hmod
  have hrem : C.remainderK = 3 := by
    simp [moduli] at hmod'
    rcases hmod' with hmod' | hmod' | hmod' | hmod' | hmod' | hmod'
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
    · simp [BlockCoordinate.remainderK, BlockCoordinate.blockBase, hbase, hstride, hmod']
  rw [hrem]
  exact powerResidues_nodup_eight_of_mem hmod

/-- The base-7, stride-6 divisor-family no-collision criterion gives
functional finite raw-coefficient reconstruction on every `8/L`
state-alignment window for a good coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFunctional_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 7) (hstride : C.stride = 6)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    List.FunctionalOnFst
      ((C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact C.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The base-7, stride-6 divisor-family no-collision criterion gives finite
factor-through reconstruction on every `8/L` state-alignment window for a good
coordinate in the listed family. -/
theorem stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem
    (C : BlockCoordinate) (hgood : C.goodMode)
    (hbase : C.base = 7) (hstride : C.stride = 6)
    (hmod : C.modulus ∈ moduli)
    (lookaheadBlocks : ℕ) :
    let pairs :=
      (C.stateAlignments hgood 8 lookaheadBlocks).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact C.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
    hgood 8 lookaheadBlocks
    (remainderK_powerResidues_nodup_eight_of_mem C hbase hstride hmod)

/-- The source-pinned `N = 118` hook and the first uncovered `N = 997` seed sit
inside the same explicit no-collision divisor family. -/
theorem n118_n997_powerResidues_nodup_eight_pair :
    ((List.range 8).map
      (fun j => FutureBase7N118.coordinate.remainderK ^ j %
        FutureBase7N118.coordinate.modulus)).Nodup ∧
    ((List.range 8).map (fun j => 3 ^ j % 997)).Nodup := by
  constructor
  · exact FutureBase7N118.coordinate_remainderK_powerResidues_nodup_eight
  · native_decide

end QRTour.Base7Stride6K3PositiveReconstruction

namespace QRTour.FutureBase7N113

/-! ### Positive Reconstruction Candidate: base 7, N = 113

This packages the previous source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (7, 113, 3, 343, 3, 4, 2, 13444)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/2` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=7, N=113, stride=3)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 113
  stride := 3
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `113` in base `7`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 7 113 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `113`. -/
theorem denominator_strippedPeriodModulus_eq_one_hundred_thirteen :
    strippedPeriodModulus 7 113 = 113 := by
  native_decide

/-- The coordinate is a good mode: `113 < 343`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `343`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 343 := by
  native_decide

/-- The quotient in `343 = q*113 + k` is `q = 3`. -/
theorem coordinate_quotientQ_eq_three : coordinate.quotientQ = 3 := by
  native_decide

/-- The remainder in `343 = q*113 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `13444`. -/
theorem coordinate_lookaheadGapNumerator_eight_two :
    coordinate.lookaheadGapNumerator 8 2 = 13444 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Two blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_two :
    coordinate.lookaheadCertificateHolds 8 2 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-7 `113` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 4, 16, 64, 30, 7, 28, 112] := by
  native_decide

/-- The base-7 `113` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-7 `113` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 2).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 2
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-7 `113` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 2
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `113`: on the finite
`8/2` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 2
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase7N113

namespace QRTour.FutureBase12N691

/-! ### Positive Reconstruction Candidate: base 12, N = 691

This packages the current source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (12, 691, 4, 20736, 30, 6, 1, 20736)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=12, N=691, stride=4)`. -/
def coordinate : BlockCoordinate where
  base := 12
  modulus := 691
  stride := 4
  modulus_pos := by decide

/-- The base-supported preperiod has length zero for denominator `691` in base `12`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 12 691 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `691`. -/
theorem denominator_strippedPeriodModulus_eq_six_hundred_ninety_one :
    strippedPeriodModulus 12 691 = 691 := by
  native_decide

/-- The coordinate is a good mode: `691 < 20736`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `20736`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 20736 := by
  native_decide

/-- The quotient in `20736 = q*691 + k` is `q = 30`. -/
theorem coordinate_quotientQ_eq_thirty : coordinate.quotientQ = 30 := by
  native_decide

/-- The remainder in `20736 = q*691 + k` is `k = 6`. -/
theorem coordinate_remainderK_eq_six : coordinate.remainderK = 6 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `20736`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 20736 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-12 `691` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 6, 36, 216, 605, 175, 359, 81] := by
  native_decide

/-- The base-12 `691` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-12 `691` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-12 `691` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `691`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase12N691

namespace QRTour.FutureBase12N226

/-! ### Positive Reconstruction Candidate: base 12, N = 226

This packages the current source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (12, 226, 5, 248832, 1101, 6, 1, 62208)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/1` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=12, N=226, stride=5)`. -/
def coordinate : BlockCoordinate where
  base := 12
  modulus := 226
  stride := 5
  modulus_pos := by decide

/-- The base-supported preperiod has length one for denominator `226` in base `12`. -/
theorem denominator_preperiodSteps_eq_one : preperiodSteps 12 226 = 1 := by
  native_decide

/-- Stripping the base-supported factor leaves periodic modulus `113`. -/
theorem denominator_strippedPeriodModulus_eq_one_hundred_thirteen :
    strippedPeriodModulus 12 226 = 113 := by
  native_decide

/-- The coordinate is a good mode: `226 < 248832`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `248832`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 248832 := by
  native_decide

/-- The quotient in `248832 = q*226 + k` is `q = 1101`. -/
theorem coordinate_quotientQ_eq_one_thousand_one_hundred_one :
    coordinate.quotientQ = 1101 := by
  native_decide

/-- The remainder in `248832 = q*226 + k` is `k = 6`. -/
theorem coordinate_remainderK_eq_six : coordinate.remainderK = 6 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `62208`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 62208 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-12 `226` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 6, 36, 216, 166, 92, 100, 148] := by
  native_decide

/-- The base-12 `226` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-12 `226` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 1
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-12 `226` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `226`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 1
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase12N226

namespace QRTour.FutureBase7N338

/-! ### Positive Reconstruction Candidate: base 7, N = 338

This packages the current source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (7, 338, 3, 343, 1, 5, 2, 64744)`.
It uses the finite power-residue no-collision criterion on `(k^j % N)`, and
remains a finite `8/2` proof hook only: no registry claim, theorem-witness
record, atlas status change, or global factorization theorem is added.
-/

/-- The candidate coordinate `(base=7, N=338, stride=3)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 338
  stride := 3
  modulus_pos := by decide

/-- Denominator `338` has no base-supported preperiod in base `7`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 7 338 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `338`. -/
theorem denominator_strippedPeriodModulus_eq_three_hundred_thirty_eight :
    strippedPeriodModulus 7 338 = 338 := by
  native_decide

/-- The coordinate is a good mode: `338 < 343`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `343`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 343 := by
  native_decide

/-- The quotient in `343 = q*338 + k` is `q = 1`. -/
theorem coordinate_quotientQ_eq_one : coordinate.quotientQ = 1 := by
  native_decide

/-- The remainder in `343 = q*338 + k` is `k = 5`. -/
theorem coordinate_remainderK_eq_five : coordinate.remainderK = 5 := by
  native_decide

/-- On the candidate window, the exact lookahead gap numerator is `64744`. -/
theorem coordinate_lookaheadGapNumerator_eight_two :
    coordinate.lookaheadGapNumerator 8 2 = 64744 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Two blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_two :
    coordinate.lookaheadCertificateHolds 8 2 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-7 `338` candidate window, the first eight power residues
`k^j % N` are explicit. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 5, 25, 125, 287, 83, 77, 47] := by
  native_decide

/-- The base-7 `338` candidate has no collision in its eight-entry
power-residue window. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  rw [coordinate_remainderK_powerResidues_window_eight]
  norm_num

/-- On the base-7 `338` candidate window, the observed `remainderIn` states
are pairwise distinct by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 2).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup
    coordinate_goodMode 8 2
    coordinate_remainderK_powerResidues_nodup_eight

/-- On the base-7 `338` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the power-residue
no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 2
      coordinate_remainderK_powerResidues_nodup_eight

/-- Positive reconstruction exemplar for denominator `338`: on the finite
`8/2` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the power-residue no-collision criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup
      coordinate_goodMode 8 2
      coordinate_remainderK_powerResidues_nodup_eight

end QRTour.FutureBase7N338

namespace QRTour.FutureBase12N149

/-! ### Positive Reconstruction Candidate: base 12, N = 149

This packages the current source-unpinned and family-uncovered standalone
power-residue no-collision row emitted by the observability program atlas:
`(base, N, m, B, q, k, L, gap) = (12, 149, 5, 248832, 1670, 2, 1, 70144)`.
It uses the sharper finite no-wrap criterion: the first eight powers
`2^j` are already below `149`, so the residue window is collision-free before
any modular wrap occurs. This remains a finite `8/1` proof hook only: no
registry claim, theorem-witness record, atlas status change, or global
factorization theorem is added.
-/

/-- The candidate coordinate `(base=12, N=149, stride=5)`. -/
def coordinate : BlockCoordinate where
  base := 12
  modulus := 149
  stride := 5
  modulus_pos := by decide

/-- Denominator `149` has no base-supported preperiod in base `12`. -/
theorem denominator_preperiodSteps_eq_zero : preperiodSteps 12 149 = 0 := by
  native_decide

/-- Stripping base-supported factors leaves periodic modulus `149`. -/
theorem denominator_strippedPeriodModulus_eq_one_hundred_forty_nine :
    strippedPeriodModulus 12 149 = 149 := by
  native_decide

/-- The coordinate is a good mode: `149 < 248832`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `248832`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 248832 := by
  native_decide

/-- The quotient in `248832 = q*149 + k` is `q = 1670`. -/
theorem coordinate_quotientQ_eq_one_thousand_six_hundred_seventy :
    coordinate.quotientQ = 1670 := by
  native_decide

/-- The remainder in `248832 = q*149 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- The remainder `k = 2` is greater than one, so powers of `k` are strictly
increasing in the exponent. -/
theorem coordinate_one_lt_remainderK : 1 < coordinate.remainderK := by
  rw [coordinate_remainderK_eq_two]
  norm_num

/-- On the candidate window, the exact lookahead gap numerator is `70144`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 70144 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- On the base-12 `149` candidate window, the first eight powers of
`k = 2` have not wrapped modulo `149`. -/
theorem coordinate_remainderK_pow_lt_modulus_eight :
    ∀ j ∈ List.range 8, coordinate.remainderK ^ j < coordinate.modulus := by
  intro j hj
  have hjlt : j < 8 := by
    simpa using List.mem_range.mp hj
  interval_cases j <;> native_decide

/-- On the base-12 `149` candidate window, the first eight power residues
`k^j % N` are explicit and are exactly the unwrapped powers. -/
theorem coordinate_remainderK_powerResidues_window_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)) =
        [1, 2, 4, 8, 16, 32, 64, 128] := by
  native_decide

/-- The base-12 `149` candidate has no collision in its eight-entry
power-residue window by the no-wrap criterion. -/
theorem coordinate_remainderK_powerResidues_nodup_eight :
    ((List.range 8).map
      (fun j => coordinate.remainderK ^ j % coordinate.modulus)).Nodup := by
  exact coordinate.remainderK_powerResidues_nodup_of_remainderK_pow_lt_modulus
    8 coordinate_one_lt_remainderK coordinate_remainderK_pow_lt_modulus_eight

/-- On the base-12 `149` candidate window, the observed `remainderIn` states
are pairwise distinct by the no-wrap power-residue criterion. -/
theorem coordinate_stateAlignments_remainderIn_nodup_eight_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact coordinate.stateAlignments_remainderIn_nodup_of_remainderK_pow_lt_modulus
    coordinate_goodMode 8 1
    coordinate_one_lt_remainderK
    coordinate_remainderK_pow_lt_modulus_eight

/-- On the base-12 `149` candidate window, the finite
`remainderIn ↦ raw coefficient` map is functional by the no-wrap
power-residue criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_pow_lt_modulus
      coordinate_goodMode 8 1
      coordinate_one_lt_remainderK
      coordinate_remainderK_pow_lt_modulus_eight

/-- Positive reconstruction exemplar for denominator `149`: on the finite
`8/1` state-alignment window, the raw coefficient factors through the observed
`remainderIn` state by the no-wrap power-residue criterion. -/
theorem coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_pow_lt_modulus
      coordinate_goodMode 8 1
      coordinate_one_lt_remainderK
      coordinate_remainderK_pow_lt_modulus_eight

end QRTour.FutureBase12N149

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

namespace QRTour.Composite68

/-! ### Empirical Obstruction Hook: 68

This packages the current first base-10 certified positive-lookahead
coefficient-functionality obstruction. It is a worked-example hook beneath the
open visibility/factorization boundary, not a new atlas claim.
-/

/-- The obstruction coordinate `(base=10, N=68, stride=4)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 68
  stride := 4
  modulus_pos := by decide

/-- The obstruction coordinate is a good mode: `68 < 10^4`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The block base for the obstruction coordinate is `10000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 10000 := by
  native_decide

/-- The obstruction coordinate lands in the congruence family `B ≡ 4 (mod 68)`. -/
theorem coordinate_blockBase_mod_68_eq_four : coordinate.blockBase % 68 = 4 := by
  native_decide

/-- The quotient in `10000 = q*68 + k` is `q = 147`. -/
theorem coordinate_quotientQ_eq_147 : coordinate.quotientQ = 147 := by
  native_decide

/-- The quotient lies past the one-lookahead certificate threshold `q ≥ 75`. -/
theorem coordinate_quotientQ_ge_seventy_five : 75 ≤ coordinate.quotientQ := by
  native_decide

/-- The remainder in `10000 = q*68 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- The canonical incoming carry at position `1` vanishes throughout the
congruence-family arithmetic, and in particular on this coordinate. -/
theorem coordinate_incomingCarry_one_eq_zero : coordinate.incomingCarry 1 = 0 := by
  exact coordinate.incomingCarry_one_eq_zero_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
    coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four

/-- The canonical incoming carry at position `5` is `60` on this coordinate. -/
theorem coordinate_incomingCarry_five_eq_sixty : coordinate.incomingCarry 5 = 60 := by
  exact coordinate.incomingCarry_five_eq_sixty_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
    coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four

/-- The arithmetic incoming-carry layer already explains the hidden output:
positions `1` and `5` emit the same block after adding their canonical incoming
carries and reducing modulo the block base. -/
theorem coordinate_incomingCarry_hiddenOutput_one_five :
    (coordinate.rawCoefficient 1 + coordinate.incomingCarry 1) % coordinate.blockBase =
      (coordinate.rawCoefficient 5 + coordinate.incomingCarry 5) % coordinate.blockBase := by
  exact coordinate.incomingCarry_hiddenOutput_one_five_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
    coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four

/-- On the obstruction window, the exact lookahead gap numerator is `6208`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 6208 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  exact
    coordinate.lookaheadCertificateHolds_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_ge_seventy_five
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four
      coordinate_quotientQ_ge_seventy_five

/-- The same obstruction coordinate also satisfies the two-lookahead family
certificate. -/
theorem coordinate_lookaheadCertificate_eight_two :
    coordinate.lookaheadCertificateHolds 8 2 := by
  exact
    coordinate.lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_ge_three
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four
      (by native_decide)

/-- Three blocks of lookahead certify every good member of the `N = 68`,
`B ≡ 4 (mod 68)` family, and therefore this coordinate. -/
theorem coordinate_lookaheadCertificate_eight_three :
    coordinate.lookaheadCertificateHolds 8 3 := by
  exact
    coordinate.lookaheadCertificateHolds_eight_three_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four

/-- The certified obstruction window still has finite output agreement. -/
theorem coordinate_visibleCarryWord_eq_emittedBlockWord_eight_one :
    coordinate.visibleCarryWord coordinate_goodMode 8 1 = coordinate.emittedBlockWord 8 := by
  exact coordinate.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate
    coordinate_goodMode (by native_decide) 8 1 coordinate_lookaheadCertificate_eight_one

/-- Positions `1` and `5` share the same observed remainder state `4`. -/
theorem coordinate_conflict_remainder_state_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).remainderIn = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).remainderIn = 4 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `588` and `150528`. -/
theorem coordinate_conflict_coefficients_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).coefficient = 588 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).coefficient = 150528 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `60`. -/
theorem coordinate_conflict_carry_states_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryIn = 60 := by
  native_decide

/-- On the certified `8/1` trace, the finite carry state at position `1`
matches the canonical incoming-carry formula. -/
theorem coordinate_stateAlignments_carryIn_one_eq_incomingCarry_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryIn =
      coordinate.incomingCarry 1 := by
  simpa using
    (coordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four).1

/-- On the certified `8/1` trace, the finite carry state at position `5`
matches the canonical incoming-carry formula. -/
theorem coordinate_stateAlignments_carryIn_five_eq_incomingCarry_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryIn =
      coordinate.incomingCarry 5 := by
  simpa using
    (coordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four).2

/-- The certified finite trace realizes the canonical incoming carries at the
two obstruction positions. -/
theorem coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryIn =
        coordinate.incomingCarry 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryIn =
        coordinate.incomingCarry 5 := by
  simpa using
    coordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four

/-- Even without positive lookahead, the eight-block finite trace already
realizes the canonical incoming carries at the two obstruction positions. This
is a carry-state certificate only; it is not the certified output-agreement
window used by the obstruction hook. -/
theorem coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry_eight_zero :
    ((coordinate.stateAlignments coordinate_goodMode 8 0)[1]'(by native_decide)).carryIn =
        coordinate.incomingCarry 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 0)[5]'(by native_decide)).carryIn =
        coordinate.incomingCarry 5 := by
  simpa using
    coordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_zero_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four

/-- The displayed carried block is hidden: both conflicting positions emit `588`. -/
theorem coordinate_conflict_carried_blocks_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryBlockValue = 588 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryBlockValue = 588 := by
  native_decide

/-- The obstruction-first family theorem specializes to the certified `8/1`
window for the base-10 `Composite68` coordinate. -/
theorem coordinate_stateAlignments_one_five_hiddenCoefficientConflict_eight_one :
    let row1 := (coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)
    let row5 := (coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)
    row1.remainderIn = row5.remainderIn ∧
      row1.coefficient ≠ row5.coefficient ∧
      row1.carryIn = coordinate.incomingCarry 1 ∧
      row5.carryIn = coordinate.incomingCarry 5 ∧
      row1.carryBlockValue = row5.carryBlockValue ∧
      ¬ List.FunctionalOnFst
        ((coordinate.stateAlignments coordinate_goodMode 8 1).map
          (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  simpa using
    coordinate.stateAlignments_one_five_hiddenCoefficientConflict_eight_any_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode 1 (by rfl) coordinate_blockBase_mod_68_eq_four

/-- The certified obstruction wrapper identifies the hidden carried outputs
with the emitted remainder blocks on the base-10 `Composite68` `8/1` window. -/
theorem coordinate_stateAlignments_one_five_certifiedVisibilityObstruction_eight_one :
    let row1 := (coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)
    let row5 := (coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)
    (row1.remainderIn = row5.remainderIn ∧
      row1.coefficient ≠ row5.coefficient ∧
      row1.carryIn = coordinate.incomingCarry 1 ∧
      row5.carryIn = coordinate.incomingCarry 5 ∧
      row1.carryBlockValue = row5.carryBlockValue ∧
      ¬ List.FunctionalOnFst
        ((coordinate.stateAlignments coordinate_goodMode 8 1).map
          (fun alignment => (alignment.remainderIn, alignment.coefficient)))) ∧
      row1.carryBlockValue = row1.remainderBlockValue ∧
      row5.carryBlockValue = row5.remainderBlockValue := by
  simpa using
    coordinate.stateAlignments_one_five_certifiedVisibilityObstruction_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode 1 coordinate_lookaheadCertificate_eight_one
      (by rfl) coordinate_blockBase_mod_68_eq_four

/-- The compact cross-base certified-conflict record specializes to the
base-10 `Composite68` `8/1` window. -/
theorem coordinate_stateAlignments_one_five_certifiedConflict_eight_one :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 1 5
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    coordinate.stateAlignments_one_five_certifiedConflict_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode 1 coordinate_lookaheadCertificate_eight_one
      (by rfl) coordinate_blockBase_mod_68_eq_four

/-- Proof-style exemplar for the recommended obstruction-record path:
family wrapper -> record -> projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord :
      coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 1 5
        (by rw [coordinate.stateAlignments_length]; decide)
        (by rw [coordinate.stateAlignments_length]; decide) :=
    coordinate.stateAlignments_one_five_certifiedConflict_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode 1 coordinate_lookaheadCertificate_eight_one
      (by rfl) coordinate_blockBase_mod_68_eq_four
  exact hrecord.not_remainderToCoefficientFunctional

/-- Proof-style exemplar for the factor-through obstruction path:
family wrapper -> record -> factor-through projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_eight_one :
    ¬ FactorsThrough
      (fun side : Bool =>
        if side then
          ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by
            rw [coordinate.stateAlignments_length]
            decide)).remainderIn
        else
          ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by
            rw [coordinate.stateAlignments_length]
            decide)).remainderIn)
      (fun side : Bool =>
        if side then
          ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by
            rw [coordinate.stateAlignments_length]
            decide)).coefficient
        else
          ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by
            rw [coordinate.stateAlignments_length]
            decide)).coefficient) := by
  have hrecord :
      coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 1 5
        (by rw [coordinate.stateAlignments_length]; decide)
        (by rw [coordinate.stateAlignments_length]; decide) :=
    coordinate.stateAlignments_one_five_certifiedConflict_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode 1 coordinate_lookaheadCertificate_eight_one
      (by rfl) coordinate_blockBase_mod_68_eq_four
  exact hrecord.not_remainderToCoefficientFactorsThrough

/-- Proof-style exemplar for the full finite-window factor-through obstruction:
window nonfunctionality -> state-alignment factor-through corollary. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_fullWindow_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    ¬ FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_not_remainderToCoefficientFactorsThrough_of_not_remainderToCoefficientFunctional
      coordinate_goodMode 8 1
      coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one

/-- The selector-certified family theorem specializes to the concrete first
branch on this worked example: the minimal certified lookahead is `1`, and
that minimal window still exposes the certified hidden coefficient conflict. -/
theorem coordinate_minimalLookaheadCertificate_selector_certifiedVisibilityObstruction_eight_one :
    coordinate.isMinimalLookaheadCertificate 8 1 ∧
      coordinate.stateAlignmentsOneFiveCertifiedVisibilityObstruction coordinate_goodMode 1 := by
  have hselector :=
    coordinate.minimalLookaheadCertificate_eight_selector_certifiedVisibilityObstruction_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four
  simpa [coordinate_quotientQ_eq_147] using hselector

/-- The observed repeated remainder state hides incompatible raw coefficients,
so the finite remainder-to-coefficient map is not functional on this certified
window. This is a finite obstruction hook only; it does not close either open
global claim. -/
theorem coordinate_not_coefficientFunctional_eight_one :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate_stateAlignments_one_five_certifiedConflict_eight_one.not_remainderToCoefficientFunctional

end QRTour.Composite68

namespace QRTour.Composite68Base30

/-! ### Empirical Obstruction Hook: 68 in base 30

This packages the base-30 member of the same hidden-output obstruction shape
as `QRTour.Composite68`. It is a finite worked-example hook only; it does not
promote a new atlas claim or close either open frontier claim.
-/

/-- The obstruction coordinate `(base=30, N=68, stride=3)`. -/
def coordinate : BlockCoordinate where
  base := 30
  modulus := 68
  stride := 3
  modulus_pos := by decide

/-- The obstruction coordinate is a good mode: `68 < 30^3`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The block base for the obstruction coordinate is `27000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 27000 := by
  native_decide

/-- The base-30 obstruction coordinate also lands in `B ≡ 4 (mod 68)`. -/
theorem coordinate_blockBase_mod_68_eq_four : coordinate.blockBase % 68 = 4 := by
  native_decide

/-- The quotient in `27000 = q*68 + k` is `q = 397`. -/
theorem coordinate_quotientQ_eq_397 : coordinate.quotientQ = 397 := by
  native_decide

/-- The quotient lies past the one-lookahead certificate threshold `q ≥ 75`. -/
theorem coordinate_quotientQ_ge_seventy_five : 75 ≤ coordinate.quotientQ := by
  native_decide

/-- The quotient is positive, so this is a good-mode coordinate. -/
theorem coordinate_quotientQ_pos : 0 < coordinate.quotientQ := by
  native_decide

/-- The remainder in `27000 = q*68 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- The canonical incoming carry at position `1` vanishes throughout the
congruence-family arithmetic, and in particular on this coordinate. -/
theorem coordinate_incomingCarry_one_eq_zero : coordinate.incomingCarry 1 = 0 := by
  exact coordinate.incomingCarry_one_eq_zero_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
    coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four

/-- The canonical incoming carry at position `5` is `60` on this coordinate. -/
theorem coordinate_incomingCarry_five_eq_sixty : coordinate.incomingCarry 5 = 60 := by
  exact coordinate.incomingCarry_five_eq_sixty_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
    coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four

/-- The arithmetic incoming-carry layer already explains the hidden output:
positions `1` and `5` emit the same block after adding their canonical incoming
carries and reducing modulo the block base. -/
theorem coordinate_incomingCarry_hiddenOutput_one_five :
    (coordinate.rawCoefficient 1 + coordinate.incomingCarry 1) % coordinate.blockBase =
      (coordinate.rawCoefficient 5 + coordinate.incomingCarry 5) % coordinate.blockBase := by
  exact coordinate.incomingCarry_hiddenOutput_one_five_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
    coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four

/-- On the obstruction window, the exact lookahead gap numerator is `10208`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 10208 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  exact
    coordinate.lookaheadCertificateHolds_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_ge_seventy_five
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four
      coordinate_quotientQ_ge_seventy_five

/-- The same base-30 obstruction coordinate also satisfies the two-lookahead
family certificate. -/
theorem coordinate_lookaheadCertificate_eight_two :
    coordinate.lookaheadCertificateHolds 8 2 := by
  exact
    coordinate.lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_ge_three
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four
      (by native_decide)

/-- Three blocks of lookahead certify every good member of the `N = 68`,
`B ≡ 4 (mod 68)` family, and therefore this base-30 coordinate. -/
theorem coordinate_lookaheadCertificate_eight_three :
    coordinate.lookaheadCertificateHolds 8 3 := by
  exact
    coordinate.lookaheadCertificateHolds_eight_three_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four

/-- The certified base-30 obstruction window still has finite output agreement. -/
theorem coordinate_visibleCarryWord_eq_emittedBlockWord_eight_one :
    coordinate.visibleCarryWord coordinate_goodMode 8 1 = coordinate.emittedBlockWord 8 := by
  exact coordinate.visibleCarryWord_eq_emittedBlockWord_of_lookaheadCertificate
    coordinate_goodMode (by native_decide) 8 1 coordinate_lookaheadCertificate_eight_one

/-- Positions `1` and `5` share the same observed remainder state `4`. -/
theorem coordinate_conflict_remainder_state_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).remainderIn = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).remainderIn = 4 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `1588` and `406528`. -/
theorem coordinate_conflict_coefficients_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).coefficient = 1588 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).coefficient = 406528 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `60`. -/
theorem coordinate_conflict_carry_states_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryIn = 60 := by
  native_decide

/-- On the certified `8/1` trace, the finite carry state at position `1`
matches the canonical incoming-carry formula. -/
theorem coordinate_stateAlignments_carryIn_one_eq_incomingCarry_one :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryIn =
      coordinate.incomingCarry 1 := by
  simpa using
    (coordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four).1

/-- On the certified `8/1` trace, the finite carry state at position `5`
matches the canonical incoming-carry formula. -/
theorem coordinate_stateAlignments_carryIn_five_eq_incomingCarry_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryIn =
      coordinate.incomingCarry 5 := by
  simpa using
    (coordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four).2

/-- The certified finite trace realizes the canonical incoming carries at the
two obstruction positions. -/
theorem coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryIn =
        coordinate.incomingCarry 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryIn =
        coordinate.incomingCarry 5 := by
  simpa using
    coordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four

/-- Even without positive lookahead, the eight-block finite trace already
realizes the canonical incoming carries at the two obstruction positions. This
is a carry-state certificate only; it is not the certified output-agreement
window used by the obstruction hook. -/
theorem coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry_eight_zero :
    ((coordinate.stateAlignments coordinate_goodMode 8 0)[1]'(by native_decide)).carryIn =
        coordinate.incomingCarry 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 0)[5]'(by native_decide)).carryIn =
        coordinate.incomingCarry 5 := by
  simpa using
    coordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_zero_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four

/-- The displayed carried block is hidden: both conflicting positions emit `1588`. -/
theorem coordinate_conflict_carried_blocks_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryBlockValue = 1588 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryBlockValue = 1588 := by
  native_decide

/-- The obstruction-first family theorem specializes to the certified `8/1`
window for the base-30 `Composite68` coordinate. -/
theorem coordinate_stateAlignments_one_five_hiddenCoefficientConflict_eight_one :
    let row1 := (coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)
    let row5 := (coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)
    row1.remainderIn = row5.remainderIn ∧
      row1.coefficient ≠ row5.coefficient ∧
      row1.carryIn = coordinate.incomingCarry 1 ∧
      row5.carryIn = coordinate.incomingCarry 5 ∧
      row1.carryBlockValue = row5.carryBlockValue ∧
      ¬ List.FunctionalOnFst
        ((coordinate.stateAlignments coordinate_goodMode 8 1).map
          (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  simpa using
    coordinate.stateAlignments_one_five_hiddenCoefficientConflict_eight_any_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode 1 (by rfl) coordinate_blockBase_mod_68_eq_four

/-- The certified obstruction wrapper identifies the hidden carried outputs
with the emitted remainder blocks on the base-30 `Composite68` `8/1` window. -/
theorem coordinate_stateAlignments_one_five_certifiedVisibilityObstruction_eight_one :
    let row1 := (coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)
    let row5 := (coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)
    (row1.remainderIn = row5.remainderIn ∧
      row1.coefficient ≠ row5.coefficient ∧
      row1.carryIn = coordinate.incomingCarry 1 ∧
      row5.carryIn = coordinate.incomingCarry 5 ∧
      row1.carryBlockValue = row5.carryBlockValue ∧
      ¬ List.FunctionalOnFst
        ((coordinate.stateAlignments coordinate_goodMode 8 1).map
          (fun alignment => (alignment.remainderIn, alignment.coefficient)))) ∧
      row1.carryBlockValue = row1.remainderBlockValue ∧
      row5.carryBlockValue = row5.remainderBlockValue := by
  simpa using
    coordinate.stateAlignments_one_five_certifiedVisibilityObstruction_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode 1 coordinate_lookaheadCertificate_eight_one
      (by rfl) coordinate_blockBase_mod_68_eq_four

/-- The compact cross-base certified-conflict record specializes to the
base-30 `Composite68` `8/1` window. -/
theorem coordinate_stateAlignments_one_five_certifiedConflict_eight_one :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 1 5
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    coordinate.stateAlignments_one_five_certifiedConflict_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode 1 coordinate_lookaheadCertificate_eight_one
      (by rfl) coordinate_blockBase_mod_68_eq_four

/-- Proof-style exemplar for the recommended obstruction-record path:
family wrapper -> record -> projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord :
      coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 1 5
        (by rw [coordinate.stateAlignments_length]; decide)
        (by rw [coordinate.stateAlignments_length]; decide) :=
    coordinate.stateAlignments_one_five_certifiedConflict_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode 1 coordinate_lookaheadCertificate_eight_one
      (by rfl) coordinate_blockBase_mod_68_eq_four
  exact hrecord.not_remainderToCoefficientFunctional

/-- Proof-style exemplar for the factor-through obstruction path:
family wrapper -> record -> factor-through projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_eight_one :
    ¬ FactorsThrough
      (fun side : Bool =>
        if side then
          ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by
            rw [coordinate.stateAlignments_length]
            decide)).remainderIn
        else
          ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by
            rw [coordinate.stateAlignments_length]
            decide)).remainderIn)
      (fun side : Bool =>
        if side then
          ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by
            rw [coordinate.stateAlignments_length]
            decide)).coefficient
        else
          ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by
            rw [coordinate.stateAlignments_length]
            decide)).coefficient) := by
  have hrecord :
      coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 1 5
        (by rw [coordinate.stateAlignments_length]; decide)
        (by rw [coordinate.stateAlignments_length]; decide) :=
    coordinate.stateAlignments_one_five_certifiedConflict_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode 1 coordinate_lookaheadCertificate_eight_one
      (by rfl) coordinate_blockBase_mod_68_eq_four
  exact hrecord.not_remainderToCoefficientFactorsThrough

/-- Proof-style exemplar for the full finite-window factor-through obstruction:
window nonfunctionality -> state-alignment factor-through corollary. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_fullWindow_eight_one :
    let pairs :=
      (coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    ¬ FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    coordinate.stateAlignments_not_remainderToCoefficientFactorsThrough_of_not_remainderToCoefficientFunctional
      coordinate_goodMode 8 1
      coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one

/-- The selector-certified family theorem specializes to the concrete first
branch on this base-30 worked example: the minimal certified lookahead is `1`,
and that minimal window still exposes the certified hidden coefficient
conflict. -/
theorem coordinate_minimalLookaheadCertificate_selector_certifiedVisibilityObstruction_eight_one :
    coordinate.isMinimalLookaheadCertificate 8 1 ∧
      coordinate.stateAlignmentsOneFiveCertifiedVisibilityObstruction coordinate_goodMode 1 := by
  have hselector :=
    coordinate.minimalLookaheadCertificate_eight_selector_certifiedVisibilityObstruction_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four
      coordinate_goodMode (by rfl) coordinate_blockBase_mod_68_eq_four
  simpa [coordinate_quotientQ_eq_397] using hselector

/-- The base-30 member has the same finite remainder-to-coefficient obstruction
shape as the base-10 `Composite68` hook. -/
theorem coordinate_not_coefficientFunctional_eight_one :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    coordinate_stateAlignments_one_five_certifiedConflict_eight_one.not_remainderToCoefficientFunctional

end QRTour.Composite68Base30

namespace QRTour.FutureBase10N17

/-! ### Shape17/K4 shifted periodic-core example: base 10, N = 17

This packages the shifted `N = 17` member of the first emitted
Shape17/K4 observability family. It is a finite worked-example hook only: it
proves the record-shaped obstruction on the certified `8/2` window and leaves
global same-core classification, `small_k_visibility_threshold`, and
`carry_dfa_factorization` open.
-/

/-- The shifted Shape17/K4 coordinate `(base=10, N=17, stride=4)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 17
  stride := 4
  modulus_pos := by decide

/-- The shifted Shape17/K4 coordinate is a good mode: `17 < 10000`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `10000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 10000 := by
  native_decide

/-- The quotient in `10000 = q*17 + k` is `q = 588`. -/
theorem coordinate_quotientQ_eq_five_hundred_eighty_eight :
    coordinate.quotientQ = 588 := by
  native_decide

/-- The remainder in `10000 = q*17 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the shifted Shape17/K4 window, the exact lookahead gap numerator is
`94179328`. -/
theorem coordinate_lookaheadGapNumerator_eight_two :
    coordinate.lookaheadGapNumerator 8 2 = 94179328 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Two blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_two :
    coordinate.lookaheadCertificateHolds 8 2 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `0` and `4` share the same observed remainder state `1`. -/
theorem coordinate_conflict_remainder_state_zero_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[0]'(by native_decide)).remainderIn = 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[4]'(by native_decide)).remainderIn = 1 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `588` and
`150528`. -/
theorem coordinate_conflict_coefficients_zero_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[0]'(by native_decide)).coefficient = 588 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[4]'(by native_decide)).coefficient = 150528 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `60`. -/
theorem coordinate_conflict_carry_states_zero_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[0]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[4]'(by native_decide)).carryIn = 60 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit
`588`. -/
theorem coordinate_conflict_carried_blocks_zero_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[0]'(by native_decide)).carryBlockValue = 588 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[4]'(by native_decide)).carryBlockValue = 588 := by
  native_decide

/-- The shifted Shape17/K4 finite obstruction record for the base-10 `N = 17`
`8/2` window. -/
theorem coordinate_stateAlignments_zero_four_certifiedConflict_eight_two :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 2 0 4
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_two :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_four_certifiedConflict_eight_two
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base10_n17_m4_blocks8_L2`. -/
theorem base10_n17_m4_blocks8_L2_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_four_certifiedConflict_eight_two
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase10N17

namespace QRTour.FutureBase10N34

/-! ### Shape17/K4 doubled periodic-core example: base 10, N = 34

This packages the doubled `N = 34` member of the first emitted Shape17/K4
observability family. It is a finite worked-example hook only and does not add
registry, theorem-witness, atlas, or global factorization claims.
-/

/-- The doubled Shape17/K4 coordinate `(base=10, N=34, stride=4)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 34
  stride := 4
  modulus_pos := by decide

/-- The doubled Shape17/K4 coordinate is a good mode: `34 < 10000`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `10000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 10000 := by
  native_decide

/-- The quotient in `10000 = q*34 + k` is `q = 294`. -/
theorem coordinate_quotientQ_eq_two_hundred_ninety_four :
    coordinate.quotientQ = 294 := by
  native_decide

/-- The remainder in `10000 = q*34 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the doubled Shape17/K4 window, the exact lookahead gap numerator is
`47089664`. -/
theorem coordinate_lookaheadGapNumerator_eight_two :
    coordinate.lookaheadGapNumerator 8 2 = 47089664 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Two blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_two :
    coordinate.lookaheadCertificateHolds 8 2 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `1` and `5` share the same observed remainder state `4`. -/
theorem coordinate_conflict_remainder_state_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[1]'(by native_decide)).remainderIn = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[5]'(by native_decide)).remainderIn = 4 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `1176` and
`301056`. -/
theorem coordinate_conflict_coefficients_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[1]'(by native_decide)).coefficient = 1176 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[5]'(by native_decide)).coefficient = 301056 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `120`. -/
theorem coordinate_conflict_carry_states_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[1]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[5]'(by native_decide)).carryIn = 120 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit
`1176`. -/
theorem coordinate_conflict_carried_blocks_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[1]'(by native_decide)).carryBlockValue = 1176 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[5]'(by native_decide)).carryBlockValue = 1176 := by
  native_decide

/-- The doubled Shape17/K4 finite obstruction record for the base-10 `N = 34`
`8/2` window. -/
theorem coordinate_stateAlignments_one_five_certifiedConflict_eight_two :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 2 1 5
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_two :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_five_certifiedConflict_eight_two
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base10_n34_m4_blocks8_L2`. -/
theorem base10_n34_m4_blocks8_L2_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_five_certifiedConflict_eight_two
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase10N34

namespace QRTour.Shape17K4

/-! ### Finite Shape17/K4 shift witness

This namespace compares the concrete state-alignment rows behind the first
emitted Shape17/K4 source-symmetry family. It proves a finite shift-and-scale
payload only: the `N = 17` conflict is seen on `[0,4]`, while the `N = 34`
and base-10 `N = 68` windows see the corresponding payload on `[1,5]`.
-/

/-- Left row of the shifted base-10 `N = 17` conflict. -/
def base10N17Left : StateAlignment :=
  (FutureBase10N17.coordinate.stateAlignments
    FutureBase10N17.coordinate_goodMode 8 2)[0]'(by native_decide)

/-- Right row of the shifted base-10 `N = 17` conflict. -/
def base10N17Right : StateAlignment :=
  (FutureBase10N17.coordinate.stateAlignments
    FutureBase10N17.coordinate_goodMode 8 2)[4]'(by native_decide)

/-- Left row of the doubled base-10 `N = 34` conflict. -/
def base10N34Left : StateAlignment :=
  (FutureBase10N34.coordinate.stateAlignments
    FutureBase10N34.coordinate_goodMode 8 2)[1]'(by native_decide)

/-- Right row of the doubled base-10 `N = 34` conflict. -/
def base10N34Right : StateAlignment :=
  (FutureBase10N34.coordinate.stateAlignments
    FutureBase10N34.coordinate_goodMode 8 2)[5]'(by native_decide)

/-- Left row of the base-10 `N = 68` Composite68 conflict. -/
def base10N68Left : StateAlignment :=
  (Composite68.coordinate.stateAlignments
    Composite68.coordinate_goodMode 8 1)[1]'(by native_decide)

/-- Right row of the base-10 `N = 68` Composite68 conflict. -/
def base10N68Right : StateAlignment :=
  (Composite68.coordinate.stateAlignments
    Composite68.coordinate_goodMode 8 1)[5]'(by native_decide)

/-- The shifted base-10 `N = 17` conflict has the same coefficient, carry, and
hidden carried-output payload as the base-10 `N = 68` Composite68 conflict,
but one position earlier and with observed remainder state `1` instead of
`4`. -/
theorem base10_core17_to_composite68_conflict_shift_exact :
    base10N68Left.position = base10N17Left.position + 1 ∧
      base10N68Right.position = base10N17Right.position + 1 ∧
      base10N17Left.coefficient = base10N68Left.coefficient ∧
      base10N17Right.coefficient = base10N68Right.coefficient ∧
      base10N17Left.carryIn = base10N68Left.carryIn ∧
      base10N17Right.carryIn = base10N68Right.carryIn ∧
      base10N17Left.carryBlockValue = base10N68Left.carryBlockValue ∧
      base10N17Right.carryBlockValue = base10N68Right.carryBlockValue ∧
      base10N17Left.remainderIn = 1 ∧
      base10N17Right.remainderIn = 1 ∧
      base10N68Left.remainderIn = 4 ∧
      base10N68Right.remainderIn = 4 := by
  native_decide

/-- The doubled base-10 `N = 34` conflict moves to the Composite68-style
`[1,5]` window and scales the `N = 17` coefficient, carry, and carried-output
payload by two. -/
theorem base10_core17_to_double34_conflict_shift_scaled :
    base10N34Left.position = base10N17Left.position + 1 ∧
      base10N34Right.position = base10N17Right.position + 1 ∧
      base10N34Left.coefficient = 2 * base10N17Left.coefficient ∧
      base10N34Right.coefficient = 2 * base10N17Right.coefficient ∧
      base10N34Left.carryIn = 2 * base10N17Left.carryIn ∧
      base10N34Right.carryIn = 2 * base10N17Right.carryIn ∧
      base10N34Left.carryBlockValue = 2 * base10N17Left.carryBlockValue ∧
      base10N34Right.carryBlockValue = 2 * base10N17Right.carryBlockValue ∧
      base10N17Left.remainderIn = 1 ∧
      base10N17Right.remainderIn = 1 ∧
      base10N34Left.remainderIn = 4 ∧
      base10N34Right.remainderIn = 4 := by
  native_decide

/-- Arithmetic same-core criterion for the `17 -> 68` Shape17/K4 member: the
base-supported factor is exactly `k`, so the hidden canonical carried-output
equality at core positions `[0,4]` transports to actual positions `[1,5]`
without scaling. -/
theorem base10_n68_sameCore_scale_one_hiddenCarryBlockValue_shift :
    (actualCoordinate 10 68 4 (by decide)).canonicalCarryBlockValue 1 =
      (actualCoordinate 10 68 4 (by decide)).canonicalCarryBlockValue 5 := by
  exact
    sameCoreCompatible_hiddenCarryBlockValue_shift_scaled_one
      (base := 10) (n := 68) (stride := 4) (scale := 1)
      (left := 0) (right := 4) (hn := by decide)
      (by
        unfold actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
        native_decide)
      (by
        unfold sameCoreCompatible actualCoordinate strippedPeriodModulus
          BlockCoordinate.remainderK BlockCoordinate.blockBase
        native_decide)
      (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)

/-- Arithmetic same-core criterion for the `17 -> 34` Shape17/K4 member: the
base-supported factor is half of `k`, so the hidden canonical carried-output
equality at core positions `[0,4]` transports to actual positions `[1,5]`
with scale two, provided the scaled quotient and block remainders remain below
their moduli. -/
theorem base10_n34_sameCore_scale_two_hiddenCarryBlockValue_shift :
    (actualCoordinate 10 34 4 (by decide)).canonicalCarryBlockValue 1 =
      (actualCoordinate 10 34 4 (by decide)).canonicalCarryBlockValue 5 := by
  exact
    sameCoreCompatible_hiddenCarryBlockValue_shift_scaled_one
      (base := 10) (n := 34) (stride := 4) (scale := 2)
      (left := 0) (right := 4) (hn := by decide)
      (by
        unfold actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
        native_decide)
      (by
        unfold sameCoreCompatible actualCoordinate strippedPeriodModulus
          BlockCoordinate.remainderK BlockCoordinate.blockBase
        native_decide)
      (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)

/-- Arithmetic same-core criterion for the base-30 `17 -> 68` Shape17/K4
member: the base-supported factor is exactly `k`, so the hidden canonical
carried-output equality transports from core positions `[0,4]` to actual
positions `[1,5]` without scaling. -/
theorem base30_n68_sameCore_scale_one_hiddenCarryBlockValue_shift :
    (actualCoordinate 30 68 3 (by decide)).canonicalCarryBlockValue 1 =
      (actualCoordinate 30 68 3 (by decide)).canonicalCarryBlockValue 5 := by
  exact
    sameCoreCompatible_hiddenCarryBlockValue_shift_scaled_one
      (base := 30) (n := 68) (stride := 3) (scale := 1)
      (left := 0) (right := 4) (hn := by decide)
      (by
        unfold actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
        native_decide)
      (by
        unfold sameCoreCompatible actualCoordinate strippedPeriodModulus
          BlockCoordinate.remainderK BlockCoordinate.blockBase
        native_decide)
      (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)

/-- Arithmetic same-core criterion for the base-30 `17 -> 34` Shape17/K4
member: the base-supported factor is half of `k`, so the hidden canonical
carried-output equality transports from core positions `[0,4]` to actual
positions `[1,5]` with scale two. -/
theorem base30_n34_sameCore_scale_two_hiddenCarryBlockValue_shift :
    (actualCoordinate 30 34 3 (by decide)).canonicalCarryBlockValue 1 =
      (actualCoordinate 30 34 3 (by decide)).canonicalCarryBlockValue 5 := by
  exact
    sameCoreCompatible_hiddenCarryBlockValue_shift_scaled_one
      (base := 30) (n := 34) (stride := 3) (scale := 2)
      (left := 0) (right := 4) (hn := by decide)
      (by
        unfold actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
        native_decide)
      (by
        unfold sameCoreCompatible actualCoordinate strippedPeriodModulus
          BlockCoordinate.remainderK BlockCoordinate.blockBase
        native_decide)
      (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)

end QRTour.Shape17K4

namespace QRTour.FutureBase30N13

/-! ### Shape13/K4 source-core example: base 30, N = 13

This packages the source-core member of the first mod-stable carry-loss
observability family. It proves the record-shaped obstruction on the certified
`8/5` window and is used by `QRTour.Shape13K4` as the finite source row for the
base-30 `13 -> 26` shift. This remains a worked finite package only.
-/

/-- The Shape13/K4 source-core coordinate `(base=30, N=13, stride=1)`. -/
def coordinate : BlockCoordinate where
  base := 30
  modulus := 13
  stride := 1
  modulus_pos := by decide

/-- The source-core coordinate is a good mode: `13 < 30`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `30`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 30 := by
  native_decide

/-- The quotient in `30 = q*13 + k` is `q = 2`. -/
theorem coordinate_quotientQ_eq_two : coordinate.quotientQ = 2 := by
  native_decide

/-- The remainder in `30 = q*13 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the source-core window, the exact lookahead gap numerator is `23854528`. -/
theorem coordinate_lookaheadGapNumerator_eight_five :
    coordinate.lookaheadGapNumerator 8 5 = 23854528 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Five blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_five :
    coordinate.lookaheadCertificateHolds 8 5 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `0` and `6` share the same observed remainder state `1`. -/
theorem coordinate_conflict_remainder_state_zero_six :
    ((coordinate.stateAlignments coordinate_goodMode 8 5)[0]'(by native_decide)).remainderIn = 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 5)[6]'(by native_decide)).remainderIn = 1 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `2` and `8192`. -/
theorem coordinate_conflict_coefficients_zero_six :
    ((coordinate.stateAlignments coordinate_goodMode 8 5)[0]'(by native_decide)).coefficient = 2 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 5)[6]'(by native_decide)).coefficient = 8192 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `1260`. -/
theorem coordinate_conflict_carry_states_zero_six :
    ((coordinate.stateAlignments coordinate_goodMode 8 5)[0]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 5)[6]'(by native_decide)).carryIn = 1260 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit `2`. -/
theorem coordinate_conflict_carried_blocks_zero_six :
    ((coordinate.stateAlignments coordinate_goodMode 8 5)[0]'(by native_decide)).carryBlockValue = 2 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 5)[6]'(by native_decide)).carryBlockValue = 2 := by
  native_decide

/-- The source-core canonical carried-output equality at positions `0` and `6`. -/
theorem coordinate_canonicalCarryBlockValue_zero_six :
    coordinate.canonicalCarryBlockValue 0 =
      coordinate.canonicalCarryBlockValue 6 := by
  native_decide

/-- The finite obstruction record for the base-30 `N = 13` source-core `8/5`
window. -/
theorem coordinate_stateAlignments_zero_six_certifiedConflict_eight_five :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 5 0 6
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_five :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 5).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_six_certifiedConflict_eight_five
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base30_n13_m1_blocks8_L5`. -/
theorem base30_n13_m1_blocks8_L5_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 5).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_six_certifiedConflict_eight_five
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase30N13

namespace QRTour.FutureBase30N26

/-! ### Shape13/K4 shifted example: base 30, N = 26

This packages the shifted member of the first mod-stable carry-loss
observability family. It proves the record-shaped obstruction on the certified
`8/5` window and is paired with `QRTour.FutureBase30N13` in
`QRTour.Shape13K4`.
-/

/-- The Shape13/K4 shifted coordinate `(base=30, N=26, stride=1)`. -/
def coordinate : BlockCoordinate where
  base := 30
  modulus := 26
  stride := 1
  modulus_pos := by decide

/-- The shifted coordinate is a good mode: `26 < 30`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `30`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 30 := by
  native_decide

/-- The quotient in `30 = q*26 + k` is `q = 1`. -/
theorem coordinate_quotientQ_eq_one : coordinate.quotientQ = 1 := by
  native_decide

/-- The remainder in `30 = q*26 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the shifted window, the exact lookahead gap numerator is `11927264`. -/
theorem coordinate_lookaheadGapNumerator_eight_five :
    coordinate.lookaheadGapNumerator 8 5 = 11927264 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Five blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_five :
    coordinate.lookaheadCertificateHolds 8 5 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `1` and `7` share the same observed remainder state `4`. -/
theorem coordinate_conflict_remainder_state_one_seven :
    ((coordinate.stateAlignments coordinate_goodMode 8 5)[1]'(by native_decide)).remainderIn = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 5)[7]'(by native_decide)).remainderIn = 4 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `4` and `16384`. -/
theorem coordinate_conflict_coefficients_one_seven :
    ((coordinate.stateAlignments coordinate_goodMode 8 5)[1]'(by native_decide)).coefficient = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 5)[7]'(by native_decide)).coefficient = 16384 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `2520`. -/
theorem coordinate_conflict_carry_states_one_seven :
    ((coordinate.stateAlignments coordinate_goodMode 8 5)[1]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 5)[7]'(by native_decide)).carryIn = 2520 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit `4`. -/
theorem coordinate_conflict_carried_blocks_one_seven :
    ((coordinate.stateAlignments coordinate_goodMode 8 5)[1]'(by native_decide)).carryBlockValue = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 5)[7]'(by native_decide)).carryBlockValue = 4 := by
  native_decide

/-- The finite obstruction record for the base-30 `N = 26` shifted `8/5`
window. -/
theorem coordinate_stateAlignments_one_seven_certifiedConflict_eight_five :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 5 1 7
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_five :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 5).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_seven_certifiedConflict_eight_five
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base30_n26_m1_blocks8_L5`. -/
theorem base30_n26_m1_blocks8_L5_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 5).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_seven_certifiedConflict_eight_five
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase30N26

namespace QRTour.Shape13K4

/-! ### Finite Shape13/K4 mod-stable carry-loss shift witness

This namespace compares the concrete state-alignment rows behind the first
mod-stable carry-loss source-shape family. It proves a finite shift-and-scale
payload only: the base-30 `N = 13` conflict is seen on `[0,6]`, while the
base-30 `N = 26` window sees the corresponding payload on `[1,7]`.
-/

/-- Left row of the base-30 `N = 13` source-core conflict. -/
def base30N13Left : StateAlignment :=
  (FutureBase30N13.coordinate.stateAlignments
    FutureBase30N13.coordinate_goodMode 8 5)[0]'(by native_decide)

/-- Right row of the base-30 `N = 13` source-core conflict. -/
def base30N13Right : StateAlignment :=
  (FutureBase30N13.coordinate.stateAlignments
    FutureBase30N13.coordinate_goodMode 8 5)[6]'(by native_decide)

/-- Left row of the base-30 `N = 26` shifted conflict. -/
def base30N26Left : StateAlignment :=
  (FutureBase30N26.coordinate.stateAlignments
    FutureBase30N26.coordinate_goodMode 8 5)[1]'(by native_decide)

/-- Right row of the base-30 `N = 26` shifted conflict. -/
def base30N26Right : StateAlignment :=
  (FutureBase30N26.coordinate.stateAlignments
    FutureBase30N26.coordinate_goodMode 8 5)[7]'(by native_decide)

/-- The base-30 `N = 26` conflict shifts the base-30 `N = 13` source-core
window one position to the right and scales the coefficient, carry, and
carried-output payload by two. -/
theorem base30_core13_to_double26_conflict_shift_scaled :
    base30N26Left.position = base30N13Left.position + 1 ∧
      base30N26Right.position = base30N13Right.position + 1 ∧
      base30N26Left.coefficient = 2 * base30N13Left.coefficient ∧
      base30N26Right.coefficient = 2 * base30N13Right.coefficient ∧
      base30N26Left.carryIn = 2 * base30N13Left.carryIn ∧
      base30N26Right.carryIn = 2 * base30N13Right.carryIn ∧
      base30N26Left.carryBlockValue = 2 * base30N13Left.carryBlockValue ∧
      base30N26Right.carryBlockValue = 2 * base30N13Right.carryBlockValue ∧
      base30N13Left.remainderIn = 1 ∧
      base30N13Right.remainderIn = 1 ∧
      base30N26Left.remainderIn = 4 ∧
      base30N26Right.remainderIn = 4 := by
  native_decide

/-- Bundled Shape13/K4 scale-two hypotheses for the proof-covered base-30
`13 -> 26` member. This is the Lean landing pad for the exported
`shape13_k4_hyp_*` booleans. -/
theorem base30_n26_scaleTwoHiddenCarryBlockValueHypotheses :
    SameCoreScaleTwoHiddenCarryBlockValueHypotheses
      30 26 1 0 6 (by decide) := by
  exact
    { goodMode := by
        unfold actualCoordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
        native_decide
      sameCoreCompatible_hyp := by
        unfold sameCoreCompatible actualCoordinate strippedPeriodModulus
          BlockCoordinate.remainderK BlockCoordinate.blockBase
        native_decide
      basePrimeSupportFactor_times_two_eq_k := by native_decide
      left_scaled_quotient_remainder_lt_gap := by native_decide
      right_scaled_quotient_remainder_lt_gap := by native_decide
      left_scaled_block_remainder_lt_blockBase := by native_decide
      right_scaled_block_remainder_lt_blockBase := by native_decide
      source_core_hidden_carryBlockValue := by native_decide }

/-- Arithmetic same-core criterion for the base-30 `13 -> 26` Shape13/K4
member: the base-supported factor is half of `k`, so the hidden canonical
carried-output equality at core positions `[0,6]` transports to actual
positions `[1,7]` with scale two. -/
theorem base30_n26_sameCore_scale_two_hiddenCarryBlockValue_shift :
    (actualCoordinate 30 26 1 (by decide)).canonicalCarryBlockValue 1 =
      (actualCoordinate 30 26 1 (by decide)).canonicalCarryBlockValue 7 := by
  exact
    sameCoreCompatible_hiddenCarryBlockValue_shift_scale_two_of_exportedHypotheses
      (base := 30) (n := 26) (stride := 1)
      (left := 0) (right := 6) (hn := by decide)
      base30_n26_scaleTwoHiddenCarryBlockValueHypotheses

/-- Compact wrapper for the default proof-covered base-30 Shape13/K4 shift
payload and the same-core carried-output criterion. -/
theorem base30_default_modStableCarryLoss_shift_pair :
    base30N26Left.carryBlockValue = 2 * base30N13Left.carryBlockValue ∧
      base30N26Right.carryBlockValue = 2 * base30N13Right.carryBlockValue ∧
      (actualCoordinate 30 26 1 (by decide)).canonicalCarryBlockValue 1 =
        (actualCoordinate 30 26 1 (by decide)).canonicalCarryBlockValue 7 := by
  exact
    ⟨base30_core13_to_double26_conflict_shift_scaled.2.2.2.2.2.2.1,
      base30_core13_to_double26_conflict_shift_scaled.2.2.2.2.2.2.2.1,
      base30_n26_sameCore_scale_two_hiddenCarryBlockValue_shift⟩

end QRTour.Shape13K4

namespace QRTour.FutureBase30N7

/-! ### Scaffolded finite obstruction example: base 30, N = 7

This packages the first non-`Composite68` scaffold candidate emitted by the
Certificate Workbench. It is a finite worked-example hook only: it proves the
record-shaped obstruction on the certified `8/2` window, but it does not add a
registry claim, theorem-witness record, atlas status change, or global
factorization theorem.
-/

/-- The scaffold coordinate `(base=30, N=7, stride=1)`. -/
def coordinate : BlockCoordinate where
  base := 30
  modulus := 7
  stride := 1
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `7 < 30`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `30`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 30 := by
  native_decide

/-- The quotient in `30 = q*7 + k` is `q = 4`. -/
theorem coordinate_quotientQ_eq_four : coordinate.quotientQ = 4 := by
  native_decide

/-- The remainder in `30 = q*7 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `532`. -/
theorem coordinate_lookaheadGapNumerator_eight_two :
    coordinate.lookaheadGapNumerator 8 2 = 532 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Two blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_two :
    coordinate.lookaheadCertificateHolds 8 2 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `0` and `3` share the same observed remainder state `1`. -/
theorem coordinate_conflict_remainder_state_zero_three :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[0]'(by native_decide)).remainderIn = 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[3]'(by native_decide)).remainderIn = 1 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `4` and `32`. -/
theorem coordinate_conflict_coefficients_zero_three :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[0]'(by native_decide)).coefficient = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[3]'(by native_decide)).coefficient = 32 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `2`. -/
theorem coordinate_conflict_carry_states_zero_three :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[0]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[3]'(by native_decide)).carryIn = 2 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit `4`. -/
theorem coordinate_conflict_carried_blocks_zero_three :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[0]'(by native_decide)).carryBlockValue = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[3]'(by native_decide)).carryBlockValue = 4 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-30 `N = 7` `8/2`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_zero_three_certifiedConflict_eight_two :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 2 0 3
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_two :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_three_certifiedConflict_eight_two
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base30_n7_m1_blocks8_L2`. -/
theorem base30_n7_m1_blocks8_L2_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_three_certifiedConflict_eight_two
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase30N7

namespace QRTour.FutureBase30N14

/-! ### Scaffolded finite obstruction example: base 30, N = 14

This packages the next scaffold candidate emitted after
`QRTour.FutureBase30N7` became source-ready. It is a finite worked-example hook
only: it proves the record-shaped obstruction on the certified `8/2` window,
but it does not add a registry claim, theorem-witness record, atlas status
change, or global factorization theorem.
-/

/-- The scaffold coordinate `(base=30, N=14, stride=1)`. -/
def coordinate : BlockCoordinate where
  base := 30
  modulus := 14
  stride := 1
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `14 < 30`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `30`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 30 := by
  native_decide

/-- The quotient in `30 = q*14 + k` is `q = 2`. -/
theorem coordinate_quotientQ_eq_two : coordinate.quotientQ = 2 := by
  native_decide

/-- The remainder in `30 = q*14 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `716`. -/
theorem coordinate_lookaheadGapNumerator_eight_two :
    coordinate.lookaheadGapNumerator 8 2 = 716 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Two blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_two :
    coordinate.lookaheadCertificateHolds 8 2 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `1` and `4` share the same observed remainder state `2`. -/
theorem coordinate_conflict_remainder_state_one_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[1]'(by native_decide)).remainderIn = 2 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[4]'(by native_decide)).remainderIn = 2 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `4` and `32`. -/
theorem coordinate_conflict_coefficients_one_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[1]'(by native_decide)).coefficient = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[4]'(by native_decide)).coefficient = 32 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `2`. -/
theorem coordinate_conflict_carry_states_one_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[1]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[4]'(by native_decide)).carryIn = 2 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit `4`. -/
theorem coordinate_conflict_carried_blocks_one_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[1]'(by native_decide)).carryBlockValue = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[4]'(by native_decide)).carryBlockValue = 4 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-30 `N = 14` `8/2`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_one_four_certifiedConflict_eight_two :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 2 1 4
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_two :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_four_certifiedConflict_eight_two
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base30_n14_m1_blocks8_L2`. -/
theorem base30_n14_m1_blocks8_L2_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_four_certifiedConflict_eight_two
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase30N14

namespace QRTour.FutureBase30N28

/-! ### Scaffolded finite obstruction example: base 30, N = 28

This packages the next scaffold candidate emitted after
`QRTour.FutureBase30N14` became source-ready. It is a finite worked-example hook
only: it proves the record-shaped obstruction on the certified `8/2` window,
but it does not add a registry claim, theorem-witness record, atlas status
change, or global factorization theorem.
-/

/-- The scaffold coordinate `(base=30, N=28, stride=1)`. -/
def coordinate : BlockCoordinate where
  base := 30
  modulus := 28
  stride := 1
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `28 < 30`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `30`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 30 := by
  native_decide

/-- The quotient in `30 = q*28 + k` is `q = 1`. -/
theorem coordinate_quotientQ_eq_one : coordinate.quotientQ = 1 := by
  native_decide

/-- The remainder in `30 = q*28 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `808`. -/
theorem coordinate_lookaheadGapNumerator_eight_two :
    coordinate.lookaheadGapNumerator 8 2 = 808 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Two blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_two :
    coordinate.lookaheadCertificateHolds 8 2 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `2` and `5` share the same observed remainder state `4`. -/
theorem coordinate_conflict_remainder_state_two_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[2]'(by native_decide)).remainderIn = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[5]'(by native_decide)).remainderIn = 4 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `4` and `32`. -/
theorem coordinate_conflict_coefficients_two_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[2]'(by native_decide)).coefficient = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[5]'(by native_decide)).coefficient = 32 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `2`. -/
theorem coordinate_conflict_carry_states_two_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[2]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[5]'(by native_decide)).carryIn = 2 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit `4`. -/
theorem coordinate_conflict_carried_blocks_two_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[2]'(by native_decide)).carryBlockValue = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[5]'(by native_decide)).carryBlockValue = 4 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-30 `N = 28` `8/2`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_two_five_certifiedConflict_eight_two :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 2 2 5
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_two :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_two_five_certifiedConflict_eight_two
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base30_n28_m1_blocks8_L2`. -/
theorem base30_n28_m1_blocks8_L2_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_two_five_certifiedConflict_eight_two
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase30N28

namespace QRTour.FutureBase12N10

/-! ### Scaffolded finite obstruction example: base 12, N = 10

This packages the next scaffold candidate emitted after
`QRTour.FutureBase30N28` became source-ready. It is a finite worked-example hook
only: it proves the record-shaped obstruction on the certified `8/3` window,
but it does not add a registry claim, theorem-witness record, atlas status
change, or global factorization theorem.
-/

/-- The scaffold coordinate `(base=12, N=10, stride=1)`. -/
def coordinate : BlockCoordinate where
  base := 12
  modulus := 10
  stride := 1
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `10 < 12`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `12`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 12 := by
  native_decide

/-- The quotient in `12 = q*10 + k` is `q = 1`. -/
theorem coordinate_quotientQ_eq_one : coordinate.quotientQ = 1 := by
  native_decide

/-- The remainder in `12 = q*10 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `896`. -/
theorem coordinate_lookaheadGapNumerator_eight_three :
    coordinate.lookaheadGapNumerator 8 3 = 896 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Three blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_three :
    coordinate.lookaheadCertificateHolds 8 3 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `1` and `5` share the same observed remainder state `2`. -/
theorem coordinate_conflict_remainder_state_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 3)[1]'(by native_decide)).remainderIn = 2 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 3)[5]'(by native_decide)).remainderIn = 2 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `2` and `32`. -/
theorem coordinate_conflict_coefficients_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 3)[1]'(by native_decide)).coefficient = 2 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 3)[5]'(by native_decide)).coefficient = 32 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `6`. -/
theorem coordinate_conflict_carry_states_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 3)[1]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 3)[5]'(by native_decide)).carryIn = 6 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit `2`. -/
theorem coordinate_conflict_carried_blocks_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 3)[1]'(by native_decide)).carryBlockValue = 2 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 3)[5]'(by native_decide)).carryBlockValue = 2 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-12 `N = 10` `8/3`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_one_five_certifiedConflict_eight_three :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 3 1 5
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_three :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 3).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_five_certifiedConflict_eight_three
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base12_n10_m1_blocks8_L3`. -/
theorem base12_n10_m1_blocks8_L3_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 3).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_five_certifiedConflict_eight_three
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase12N10

namespace QRTour.FutureBase10N102

/-! ### Scaffolded finite obstruction example: base 10, N = 102

This packages the next scaffold candidate emitted after
`QRTour.FutureBase12N10` became source-ready. It is a finite worked-example hook
only: it proves the record-shaped obstruction on the certified `8/1` window,
but it does not add a registry claim, theorem-witness record, atlas status
change, or global factorization theorem.
-/

/-- The scaffold coordinate `(base=10, N=102, stride=4)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 102
  stride := 4
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `102 < 10000`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `10000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 10000 := by
  native_decide

/-- The quotient in `10000 = q*102 + k` is `q = 98`. -/
theorem coordinate_quotientQ_eq_ninety_eight : coordinate.quotientQ = 98 := by
  native_decide

/-- The remainder in `10000 = q*102 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `7472`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 7472 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `1` and `5` share the same observed remainder state `4`. -/
theorem coordinate_conflict_remainder_state_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).remainderIn = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).remainderIn = 4 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `392` and
`100352`. -/
theorem coordinate_conflict_coefficients_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).coefficient = 392 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).coefficient = 100352 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `40`. -/
theorem coordinate_conflict_carry_states_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryIn = 40 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit
`392`. -/
theorem coordinate_conflict_carried_blocks_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryBlockValue = 392 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryBlockValue = 392 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-10 `N = 102` `8/1`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_one_five_certifiedConflict_eight_one :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 1 5
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_five_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base10_n102_m4_blocks8_L1`. -/
theorem base10_n102_m4_blocks8_L1_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_five_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase10N102

namespace QRTour.FutureBase7N5

/-! ### Scaffolded finite obstruction example: base 7, N = 5

This packages the next scaffold candidate emitted after
`QRTour.FutureBase10N102` became source-ready. It is a finite worked-example
hook only: it proves the record-shaped obstruction on the certified `8/5`
window, but it does not add a registry claim, theorem-witness record, atlas
status change, or global factorization theorem.
-/

/-- The scaffold coordinate `(base=7, N=5, stride=1)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 5
  stride := 1
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `5 < 7`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `7`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 7 := by
  native_decide

/-- The quotient in `7 = q*5 + k` is `q = 1`. -/
theorem coordinate_quotientQ_eq_one : coordinate.quotientQ = 1 := by
  native_decide

/-- The remainder in `7 = q*5 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `15084`. -/
theorem coordinate_lookaheadGapNumerator_eight_five :
    coordinate.lookaheadGapNumerator 8 5 = 15084 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Five blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_five :
    coordinate.lookaheadCertificateHolds 8 5 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `0` and `4` share the same observed remainder state `1`. -/
theorem coordinate_conflict_remainder_state_zero_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 5)[0]'(by native_decide)).remainderIn = 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 5)[4]'(by native_decide)).remainderIn = 1 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `1` and `16`. -/
theorem coordinate_conflict_coefficients_zero_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 5)[0]'(by native_decide)).coefficient = 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 5)[4]'(by native_decide)).coefficient = 16 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `6`. -/
theorem coordinate_conflict_carry_states_zero_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 5)[0]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 5)[4]'(by native_decide)).carryIn = 6 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit `1`. -/
theorem coordinate_conflict_carried_blocks_zero_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 5)[0]'(by native_decide)).carryBlockValue = 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 5)[4]'(by native_decide)).carryBlockValue = 1 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-7 `N = 5` `8/5`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_zero_four_certifiedConflict_eight_five :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 5 0 4
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_five :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 5).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_four_certifiedConflict_eight_five
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base7_n5_m1_blocks8_L5`. -/
theorem base7_n5_m1_blocks8_L5_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 5).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_four_certifiedConflict_eight_five
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase7N5

namespace QRTour.FutureBase12N5

/-! ### Scaffolded finite obstruction example: base 12, N = 5

This packages the next scaffold candidate emitted after
`QRTour.FutureBase7N5` became source-ready. It is a finite worked-example hook
only: it proves the record-shaped obstruction on the certified `8/4` window,
but it does not add a registry claim, theorem-witness record, atlas status
change, or global factorization theorem.
-/

/-- The scaffold coordinate `(base=12, N=5, stride=1)`. -/
def coordinate : BlockCoordinate where
  base := 12
  modulus := 5
  stride := 1
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `5 < 12`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `12`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 12 := by
  native_decide

/-- The quotient in `12 = q*5 + k` is `q = 2`. -/
theorem coordinate_quotientQ_eq_two : coordinate.quotientQ = 2 := by
  native_decide

/-- The remainder in `12 = q*5 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `17408`. -/
theorem coordinate_lookaheadGapNumerator_eight_four :
    coordinate.lookaheadGapNumerator 8 4 = 17408 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Four blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_four :
    coordinate.lookaheadCertificateHolds 8 4 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `0` and `4` share the same observed remainder state `1`. -/
theorem coordinate_conflict_remainder_state_zero_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 4)[0]'(by native_decide)).remainderIn = 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 4)[4]'(by native_decide)).remainderIn = 1 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `2` and `32`. -/
theorem coordinate_conflict_coefficients_zero_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 4)[0]'(by native_decide)).coefficient = 2 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 4)[4]'(by native_decide)).coefficient = 32 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `6`. -/
theorem coordinate_conflict_carry_states_zero_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 4)[0]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 4)[4]'(by native_decide)).carryIn = 6 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit `2`. -/
theorem coordinate_conflict_carried_blocks_zero_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 4)[0]'(by native_decide)).carryBlockValue = 2 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 4)[4]'(by native_decide)).carryBlockValue = 2 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-12 `N = 5` `8/4`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_zero_four_certifiedConflict_eight_four :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 4 0 4
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_four :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 4).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_four_certifiedConflict_eight_four
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base12_n5_m1_blocks8_L4`. -/
theorem base12_n5_m1_blocks8_L4_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 4).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_four_certifiedConflict_eight_four
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase12N5

namespace QRTour.FutureBase30N34

/-! ### Scaffolded finite obstruction example: base 30, N = 34

This packages the next scaffold candidate emitted after
`QRTour.FutureBase12N5` became source-ready. It is a finite worked-example hook
only: it proves the record-shaped obstruction on the certified `8/1` window,
but it does not add a registry claim, theorem-witness record, atlas status
change, or global factorization theorem.
-/

/-- The scaffold coordinate `(base=30, N=34, stride=3)`. -/
def coordinate : BlockCoordinate where
  base := 30
  modulus := 34
  stride := 3
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `34 < 27000`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `27000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 27000 := by
  native_decide

/-- The quotient in `27000 = q*34 + k` is `q = 794`. -/
theorem coordinate_quotientQ_eq_seven_hundred_ninety_four :
    coordinate.quotientQ = 794 := by
  native_decide

/-- The remainder in `27000 = q*34 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `20416`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 20416 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `1` and `5` share the same observed remainder state `4`. -/
theorem coordinate_conflict_remainder_state_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).remainderIn = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).remainderIn = 4 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `3176` and
`813056`. -/
theorem coordinate_conflict_coefficients_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).coefficient = 3176 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).coefficient = 813056 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `120`. -/
theorem coordinate_conflict_carry_states_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryIn = 120 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit
`3176`. -/
theorem coordinate_conflict_carried_blocks_one_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryBlockValue = 3176 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryBlockValue = 3176 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-30 `N = 34` `8/1`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_one_five_certifiedConflict_eight_one :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 1 5
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_five_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base30_n34_m3_blocks8_L1`. -/
theorem base30_n34_m3_blocks8_L1_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_five_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase30N34

namespace QRTour.FutureBase10N374

/-! ### Shape187/K188 canonical criterion example: base 10, N = 374

This packages the smallest base-10 Shape187/K188 same-position scaling
candidate through the exported-hypothesis bundle. It proves the canonical
hidden carried-output equality and pins the certified `8/2` finite conflict
record.
-/

/-- The scaffold coordinate `(base=10, N=374, stride=16)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 374
  stride := 16
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `374 < 10^16`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `10^16`. -/
theorem coordinate_blockBase_eq :
    coordinate.blockBase = 10000000000000000 := by
  native_decide

/-- The quotient in `10^16 = q*374 + k` is
`q = 26737967914438`. -/
theorem coordinate_quotientQ_eq :
    coordinate.quotientQ = 26737967914438 := by
  native_decide

/-- The remainder in `10^16 = q*374 + k` is `k = 188`. -/
theorem coordinate_remainderK_eq_one_hundred_eighty_eight :
    coordinate.remainderK = 188 := by
  native_decide

/-- The Shape187/K188 same-position remainder is idempotent modulo `374`. -/
theorem coordinate_remainderK_idempotent :
    coordinate.remainderK * coordinate.remainderK % coordinate.modulus =
      coordinate.remainderK := by
  native_decide

/-- Bundled Shape187/K188 same-position scaling hypotheses for the base-10
`N = 374` member. This is the Lean landing pad for the exported
`same_position_hyp_*` booleans. -/
theorem coordinate_samePositionScalingHiddenCarryBlockValueHypotheses :
    coordinate.SamePositionScalingHiddenCarryBlockValueHypotheses 187 2 := by
  exact
    { goodMode := coordinate_goodMode
      modulus_eq_multiplier_mul_core := by native_decide
      remainderK_eq_core_plus_one := by native_decide
      multiplier_dvd_remainderK := by native_decide }

/-- The exported-hypothesis bundle proves the canonical hidden carried-output
equality at positions `1` and `2`. -/
theorem coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two :
    coordinate.canonicalCarryBlockValue 1 =
      coordinate.canonicalCarryBlockValue 2 := by
  exact
    coordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses
      coordinate_samePositionScalingHiddenCarryBlockValueHypotheses

/-- On the scaffold window, the exact lookahead gap numerator is the default
Shape187/K188 base-10 `N = 374` value. -/
theorem coordinate_lookaheadGapNumerator_eight_two :
    coordinate.lookaheadGapNumerator 8 2 =
      49732620321003086063324378955776 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Two blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_two :
    coordinate.lookaheadCertificateHolds 8 2 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `1` and `2` share the same observed remainder state `188`. -/
theorem coordinate_conflict_remainder_state_one_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[1]'(by native_decide)).remainderIn = 188 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[2]'(by native_decide)).remainderIn = 188 := by
  native_decide

/-- The same two positions have incompatible raw coefficients. -/
theorem coordinate_conflict_coefficients_one_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[1]'(by native_decide)).coefficient =
        5026737967914344 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[2]'(by native_decide)).coefficient =
        945026737967896672 := by
  native_decide

/-- The conflicting positions receive incoming carry states `94` and `17766`. -/
theorem coordinate_conflict_carry_states_one_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[1]'(by native_decide)).carryIn = 94 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[2]'(by native_decide)).carryIn = 17766 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit
`5026737967914438`. -/
theorem coordinate_conflict_carried_blocks_one_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 2)[1]'(by native_decide)).carryBlockValue =
        5026737967914438 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 2)[2]'(by native_decide)).carryBlockValue =
        5026737967914438 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-10 `N = 374` `8/2`
window. -/
theorem coordinate_stateAlignments_one_two_certifiedConflict_eight_two :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 2 1 2
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_two :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 2).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_two_certifiedConflict_eight_two
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase10N374

namespace QRTour.FutureBase12N374

/-! ### Shape187/K188 canonical criterion example: base 12, N = 374

This packages the sibling base-12 Shape187/K188 same-position scaling
candidate through the exported-hypothesis bundle. It proves the canonical
hidden carried-output equality only; a finite certified conflict record can be
added separately if this row becomes the next finite package target.
-/

/-- The scaffold coordinate `(base=12, N=374, stride=16)`. -/
def coordinate : BlockCoordinate where
  base := 12
  modulus := 374
  stride := 16
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `374 < 12^16`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `12^16`. -/
theorem coordinate_blockBase_eq :
    coordinate.blockBase = 184884258895036416 := by
  native_decide

/-- The quotient in `12^16 = q*374 + k` is
`q = 494342938222022`. -/
theorem coordinate_quotientQ_eq :
    coordinate.quotientQ = 494342938222022 := by
  native_decide

/-- The remainder in `12^16 = q*374 + k` is `k = 188`. -/
theorem coordinate_remainderK_eq_one_hundred_eighty_eight :
    coordinate.remainderK = 188 := by
  native_decide

/-- The Shape187/K188 same-position remainder is idempotent modulo `374`. -/
theorem coordinate_remainderK_idempotent :
    coordinate.remainderK * coordinate.remainderK % coordinate.modulus =
      coordinate.remainderK := by
  native_decide

/-- Bundled Shape187/K188 same-position scaling hypotheses for the base-12
`N = 374` member. This is the Lean landing pad for the exported
`same_position_hyp_*` booleans. -/
theorem coordinate_samePositionScalingHiddenCarryBlockValueHypotheses :
    coordinate.SamePositionScalingHiddenCarryBlockValueHypotheses 187 2 := by
  exact
    { goodMode := coordinate_goodMode
      modulus_eq_multiplier_mul_core := by native_decide
      remainderK_eq_core_plus_one := by native_decide
      multiplier_dvd_remainderK := by native_decide }

/-- The exported-hypothesis bundle proves the canonical hidden carried-output
equality at positions `1` and `2`. -/
theorem coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two :
    coordinate.canonicalCarryBlockValue 1 =
      coordinate.canonicalCarryBlockValue 2 := by
  exact
    coordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses
      coordinate_samePositionScalingHiddenCarryBlockValueHypotheses

end QRTour.FutureBase12N374

namespace QRTour.FutureBase30N374

/-! ### Scaffolded same-position obstruction example: base 30, N = 374

This packages the first Shape187/K188 same-position scaling candidate. The
generic idempotent-remainder theorem proves the canonical hidden carried-output
equality, and the finite record below pins the certified `8/1` state-alignment
obstruction. This remains a worked finite package, not a registry claim,
theorem-witness promotion, atlas status change, or global factorization result.
-/

/-- The scaffold coordinate `(base=30, N=374, stride=20)`. -/
def coordinate : BlockCoordinate where
  base := 30
  modulus := 374
  stride := 20
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `374 < 30^20`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `30^20`. -/
theorem coordinate_blockBase_eq :
    coordinate.blockBase = 348678440100000000000000000000 := by
  native_decide

/-- The quotient in `30^20 = q*374 + k` is
`q = 932295294385026737967914438`. -/
theorem coordinate_quotientQ_eq :
    coordinate.quotientQ = 932295294385026737967914438 := by
  native_decide

/-- The remainder in `30^20 = q*374 + k` is `k = 188`. -/
theorem coordinate_remainderK_eq_one_hundred_eighty_eight :
    coordinate.remainderK = 188 := by
  native_decide

/-- The Shape187/K188 same-position remainder is idempotent modulo `374`. -/
theorem coordinate_remainderK_idempotent :
    coordinate.remainderK * coordinate.remainderK % coordinate.modulus =
      coordinate.remainderK := by
  native_decide

/-- Bundled Shape187/K188 same-position scaling hypotheses for the base-30
`N = 374` member. This is the Lean landing pad for the exported
`same_position_hyp_*` booleans. -/
theorem coordinate_samePositionScalingHiddenCarryBlockValueHypotheses :
    coordinate.SamePositionScalingHiddenCarryBlockValueHypotheses 187 2 := by
  exact
    { goodMode := coordinate_goodMode
      modulus_eq_multiplier_mul_core := by native_decide
      remainderK_eq_core_plus_one := by native_decide
      multiplier_dvd_remainderK := by native_decide }

/-- The generic idempotent-remainder lemma proves the canonical hidden
carried-output equality at positions `1` and `2`. -/
theorem coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two :
    coordinate.canonicalCarryBlockValue 1 =
      coordinate.canonicalCarryBlockValue 2 := by
  exact
    coordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses
      coordinate_samePositionScalingHiddenCarryBlockValueHypotheses

/-- On the scaffold window, the exact lookahead gap numerator is the default
Shape187/K188 base-30 `N = 374` value. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 =
      173406924756399393953853079552 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `1` and `2` share the same observed remainder state `188`. -/
theorem coordinate_conflict_remainder_state_one_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).remainderIn = 188 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[2]'(by native_decide)).remainderIn = 188 := by
  native_decide

/-- The same two positions have incompatible raw coefficients. -/
theorem coordinate_conflict_coefficients_one_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).coefficient =
        175271515344385026737967914344 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[2]'(by native_decide)).coefficient =
        32951044884744385026737967896672 := by
  native_decide

/-- The conflicting positions receive incoming carry states `94` and `17766`. -/
theorem coordinate_conflict_carry_states_one_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryIn = 94 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[2]'(by native_decide)).carryIn = 17766 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit
`175271515344385026737967914438`. -/
theorem coordinate_conflict_carried_blocks_one_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryBlockValue =
        175271515344385026737967914438 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[2]'(by native_decide)).carryBlockValue =
        175271515344385026737967914438 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-30 `N = 374` `8/1`
window. This is the first source-ready package for Shape187/K188. -/
theorem coordinate_stateAlignments_one_two_certifiedConflict_eight_one :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 1 2
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_two_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base30_n374_m20_blocks8_L1`. -/
theorem base30_n374_m20_blocks8_L1_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_two_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase30N374

namespace QRTour.FutureBase30N748

/-! ### Scaffolded same-position obstruction example: base 30, N = 748

This packages the second default Shape187/K188 same-position scaling candidate
over base `30`. The generic idempotent-remainder theorem proves the canonical
hidden carried-output equality, and the finite record below pins the certified
`8/1` state-alignment obstruction. This remains a worked finite package, not a
registry claim, theorem-witness promotion, atlas status change, or global
factorization result.
-/

/-- The scaffold coordinate `(base=30, N=748, stride=20)`. -/
def coordinate : BlockCoordinate where
  base := 30
  modulus := 748
  stride := 20
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `748 < 30^20`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `30^20`. -/
theorem coordinate_blockBase_eq :
    coordinate.blockBase = 348678440100000000000000000000 := by
  native_decide

/-- The quotient in `30^20 = q*748 + k` is
`q = 466147647192513368983957219`. -/
theorem coordinate_quotientQ_eq :
    coordinate.quotientQ = 466147647192513368983957219 := by
  native_decide

/-- The remainder in `30^20 = q*748 + k` is `k = 188`. -/
theorem coordinate_remainderK_eq_one_hundred_eighty_eight :
    coordinate.remainderK = 188 := by
  native_decide

/-- The Shape187/K188 same-position remainder is idempotent modulo `748`. -/
theorem coordinate_remainderK_idempotent :
    coordinate.remainderK * coordinate.remainderK % coordinate.modulus =
      coordinate.remainderK := by
  native_decide

/-- Bundled Shape187/K188 same-position scaling hypotheses for the base-30
`N = 748` member. This is the Lean landing pad for the exported
`same_position_hyp_*` booleans. -/
theorem coordinate_samePositionScalingHiddenCarryBlockValueHypotheses :
    coordinate.SamePositionScalingHiddenCarryBlockValueHypotheses 187 4 := by
  exact
    { goodMode := coordinate_goodMode
      modulus_eq_multiplier_mul_core := by native_decide
      remainderK_eq_core_plus_one := by native_decide
      multiplier_dvd_remainderK := by native_decide }

/-- The generic idempotent-remainder lemma proves the canonical hidden
carried-output equality at positions `1` and `2`. -/
theorem coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two :
    coordinate.canonicalCarryBlockValue 1 =
      coordinate.canonicalCarryBlockValue 2 := by
  exact
    coordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses
      coordinate_samePositionScalingHiddenCarryBlockValueHypotheses

/-- On the scaffold window, the exact lookahead gap numerator is the default
Shape187/K188 base-30 `N = 748` value. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 =
      261042682428199696976926539776 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `1` and `2` share the same observed remainder state `188`. -/
theorem coordinate_conflict_remainder_state_one_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).remainderIn = 188 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[2]'(by native_decide)).remainderIn = 188 := by
  native_decide

/-- The same two positions have incompatible raw coefficients. -/
theorem coordinate_conflict_coefficients_one_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).coefficient =
        87635757672192513368983957172 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[2]'(by native_decide)).coefficient =
        16475522442372192513368983948336 := by
  native_decide

/-- The conflicting positions receive incoming carry states `47` and `8883`. -/
theorem coordinate_conflict_carry_states_one_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryIn = 47 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[2]'(by native_decide)).carryIn = 8883 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit
`87635757672192513368983957219`. -/
theorem coordinate_conflict_carried_blocks_one_two :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryBlockValue =
        87635757672192513368983957219 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[2]'(by native_decide)).carryBlockValue =
        87635757672192513368983957219 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-30 `N = 748` `8/1`
window. This is the second source-ready base-30 package for Shape187/K188. -/
theorem coordinate_stateAlignments_one_two_certifiedConflict_eight_one :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 1 2
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_two_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base30_n748_m20_blocks8_L1`. -/
theorem base30_n748_m20_blocks8_L1_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_two_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase30N748

namespace QRTour.Shape187K188

/-! ### Base-30 Shape187/K188 same-position wrapper

This namespace records the current proof-covered base-30 Shape187/K188 seed
pair. It packages named instantiations only; base-10 and base-12 rows remain
exported theorem candidates until they receive their own Lean hooks or a
genuinely uniform family theorem.
-/

/-- The base-30 `N = 374` Shape187/K188 member satisfies the canonical
same-position hidden carried-output criterion. -/
theorem base30_n374_samePositionIdempotent_hiddenCarryBlockValue_one_two :
    FutureBase30N374.coordinate.canonicalCarryBlockValue 1 =
      FutureBase30N374.coordinate.canonicalCarryBlockValue 2 := by
  exact FutureBase30N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two

/-- The base-30 `N = 748` Shape187/K188 member satisfies the canonical
same-position hidden carried-output criterion. -/
theorem base30_n748_samePositionIdempotent_hiddenCarryBlockValue_one_two :
    FutureBase30N748.coordinate.canonicalCarryBlockValue 1 =
      FutureBase30N748.coordinate.canonicalCarryBlockValue 2 := by
  exact FutureBase30N748.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two

/-- Compact wrapper for the two default proof-covered base-30 Shape187/K188
same-position carried-output seeds. -/
theorem base30_default_samePositionIdempotent_hiddenCarryBlockValue_one_two_pair :
    FutureBase30N374.coordinate.canonicalCarryBlockValue 1 =
        FutureBase30N374.coordinate.canonicalCarryBlockValue 2 ∧
      FutureBase30N748.coordinate.canonicalCarryBlockValue 1 =
        FutureBase30N748.coordinate.canonicalCarryBlockValue 2 := by
  exact ⟨base30_n374_samePositionIdempotent_hiddenCarryBlockValue_one_two,
    base30_n748_samePositionIdempotent_hiddenCarryBlockValue_one_two⟩

end QRTour.Shape187K188

namespace QRTour.FutureBase7N93

/-! ### Scaffolded finite obstruction example: base 7, N = 93

This packages the next scaffold candidate emitted after
the base-30 Shape187/K188 seeds became source-ready. It is a finite
worked-example hook only: it proves the record-shaped obstruction on the
certified `8/1` window, but it does not add a registry claim, theorem-witness
record, atlas status change, or global factorization theorem.
-/

/-- The scaffold coordinate `(base=7, N=93, stride=6)`. -/
def coordinate : BlockCoordinate where
  base := 7
  modulus := 93
  stride := 6
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `93 < 117649`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `117649`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 117649 := by
  native_decide

/-- The quotient in `117649 = q*93 + k` is `q = 1265`. -/
theorem coordinate_quotientQ_eq_twelve_hundred_sixty_five :
    coordinate.quotientQ = 1265 := by
  native_decide

/-- The remainder in `117649 = q*93 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `39505`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 39505 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `0` and `5` share the same observed remainder state `1`. -/
theorem coordinate_conflict_remainder_state_zero_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[0]'(by native_decide)).remainderIn = 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).remainderIn = 1 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `1265` and
`1295360`. -/
theorem coordinate_conflict_coefficients_zero_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[0]'(by native_decide)).coefficient = 1265 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).coefficient = 1295360 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `44`. -/
theorem coordinate_conflict_carry_states_zero_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[0]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryIn = 44 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit
`1265`. -/
theorem coordinate_conflict_carried_blocks_zero_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[0]'(by native_decide)).carryBlockValue = 1265 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryBlockValue = 1265 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-7 `N = 93` `8/1`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_zero_five_certifiedConflict_eight_one :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 0 5
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_five_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base7_n93_m6_blocks8_L1`. -/
theorem base7_n93_m6_blocks8_L1_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_five_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase7N93

namespace QRTour.FutureBase10N39

/-! ### Scaffolded finite obstruction example: base 10, N = 39

This packages the next scaffold candidate emitted after
`QRTour.FutureBase7N93` became source-ready. It is a finite worked-example hook
only: it proves the record-shaped obstruction on the certified `8/1` window,
but it does not add a registry claim, theorem-witness record, atlas status
change, or global factorization theorem.
-/

/-- The scaffold coordinate `(base=10, N=39, stride=5)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 39
  stride := 5
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `39 < 100000`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `100000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 100000 := by
  native_decide

/-- The quotient in `100000 = q*39 + k` is `q = 2564`. -/
theorem coordinate_quotientQ_eq_two_thousand_five_hundred_sixty_four :
    coordinate.quotientQ = 2564 := by
  native_decide

/-- The remainder in `100000 = q*39 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `65696`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 65696 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `0` and `6` share the same observed remainder state `1`. -/
theorem coordinate_conflict_remainder_state_zero_six :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[0]'(by native_decide)).remainderIn = 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[6]'(by native_decide)).remainderIn = 1 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `2564` and
`10502144`. -/
theorem coordinate_conflict_coefficients_zero_six :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[0]'(by native_decide)).coefficient = 2564 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[6]'(by native_decide)).coefficient = 10502144 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `420`. -/
theorem coordinate_conflict_carry_states_zero_six :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[0]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[6]'(by native_decide)).carryIn = 420 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit
`2564`. -/
theorem coordinate_conflict_carried_blocks_zero_six :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[0]'(by native_decide)).carryBlockValue = 2564 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[6]'(by native_decide)).carryBlockValue = 2564 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-10 `N = 39` `8/1`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_zero_six_certifiedConflict_eight_one :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 0 6
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_six_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base10_n39_m5_blocks8_L1`. -/
theorem base10_n39_m5_blocks8_L1_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_six_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase10N39

namespace QRTour.FutureBase10N78

/-! ### Scaffolded finite obstruction example: base 10, N = 78

This packages the next scaffold candidate emitted after
`QRTour.FutureBase10N39` became source-ready. It is a finite worked-example hook
only: it proves the record-shaped obstruction on the certified `8/1` window,
but it does not add a registry claim, theorem-witness record, atlas status
change, or global factorization theorem.
-/

/-- The scaffold coordinate `(base=10, N=78, stride=5)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 78
  stride := 5
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `78 < 100000`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `100000`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 100000 := by
  native_decide

/-- The quotient in `100000 = q*78 + k` is `q = 1282`. -/
theorem coordinate_quotientQ_eq_twelve_hundred_eighty_two :
    coordinate.quotientQ = 1282 := by
  native_decide

/-- The remainder in `100000 = q*78 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `82848`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 82848 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `1` and `7` share the same observed remainder state `4`. -/
theorem coordinate_conflict_remainder_state_one_seven :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).remainderIn = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[7]'(by native_decide)).remainderIn = 4 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `5128` and
`21004288`. -/
theorem coordinate_conflict_coefficients_one_seven :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).coefficient = 5128 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[7]'(by native_decide)).coefficient = 21004288 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `840`. -/
theorem coordinate_conflict_carry_states_one_seven :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[7]'(by native_decide)).carryIn = 840 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit
`5128`. -/
theorem coordinate_conflict_carried_blocks_one_seven :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[1]'(by native_decide)).carryBlockValue = 5128 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[7]'(by native_decide)).carryBlockValue = 5128 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-10 `N = 78` `8/1`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_one_seven_certifiedConflict_eight_one :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 1 7
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_seven_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base10_n78_m5_blocks8_L1`. -/
theorem base10_n78_m5_blocks8_L1_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_one_seven_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase10N78

namespace QRTour.FutureBase10N96

/-! ### Scaffolded finite obstruction example: base 10, N = 96

This packages the next scaffold candidate emitted after
`QRTour.FutureBase10N78` became source-ready. It is a finite worked-example hook
only: it proves the record-shaped obstruction on the certified `8/3` window,
but it does not add a registry claim, theorem-witness record, atlas status
change, or global factorization theorem.
-/

/-- The scaffold coordinate `(base=10, N=96, stride=2)`. -/
def coordinate : BlockCoordinate where
  base := 10
  modulus := 96
  stride := 2
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `96 < 100`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `100`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 100 := by
  native_decide

/-- The quotient in `100 = q*96 + k` is `q = 1`. -/
theorem coordinate_quotientQ_eq_one : coordinate.quotientQ = 1 := by
  native_decide

/-- The remainder in `100 = q*96 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `377024`. -/
theorem coordinate_lookaheadGapNumerator_eight_three :
    coordinate.lookaheadGapNumerator 8 3 = 377024 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Three blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_three :
    coordinate.lookaheadCertificateHolds 8 3 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `3` and `4` share the same observed remainder state `64`. -/
theorem coordinate_conflict_remainder_state_three_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 3)[3]'(by native_decide)).remainderIn = 64 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 3)[4]'(by native_decide)).remainderIn = 64 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `64` and `256`. -/
theorem coordinate_conflict_coefficients_three_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 3)[3]'(by native_decide)).coefficient = 64 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 3)[4]'(by native_decide)).coefficient = 256 := by
  native_decide

/-- The conflicting positions receive incoming carry states `2` and `10`. -/
theorem coordinate_conflict_carry_states_three_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 3)[3]'(by native_decide)).carryIn = 2 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 3)[4]'(by native_decide)).carryIn = 10 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit
`66`. -/
theorem coordinate_conflict_carried_blocks_three_four :
    ((coordinate.stateAlignments coordinate_goodMode 8 3)[3]'(by native_decide)).carryBlockValue = 66 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 3)[4]'(by native_decide)).carryBlockValue = 66 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-10 `N = 96` `8/3`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_three_four_certifiedConflict_eight_three :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 3 3 4
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_three :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 3).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_three_four_certifiedConflict_eight_three
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base10_n96_m2_blocks8_L3`. -/
theorem base10_n96_m2_blocks8_L3_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 3).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_three_four_certifiedConflict_eight_three
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase10N96

namespace QRTour.FutureBase12N35

/-! ### Scaffolded finite obstruction example: base 12, N = 35

This packages the next scaffold candidate emitted after
`QRTour.FutureBase10N96` became source-ready. It is a finite worked-example hook
only: it proves the record-shaped obstruction on the certified `8/3` window,
but it does not add a registry claim, theorem-witness record, atlas status
change, or global factorization theorem.
-/

/-- The scaffold coordinate `(base=12, N=35, stride=2)`. -/
def coordinate : BlockCoordinate where
  base := 12
  modulus := 35
  stride := 2
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `35 < 144`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `144`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 144 := by
  native_decide

/-- The quotient in `144 = q*35 + k` is `q = 4`. -/
theorem coordinate_quotientQ_eq_four : coordinate.quotientQ = 4 := by
  native_decide

/-- The remainder in `144 = q*35 + k` is `k = 4`. -/
theorem coordinate_remainderK_eq_four : coordinate.remainderK = 4 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `1740800`. -/
theorem coordinate_lookaheadGapNumerator_eight_three :
    coordinate.lookaheadGapNumerator 8 3 = 1740800 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- Three blocks of lookahead certify the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_three :
    coordinate.lookaheadCertificateHolds 8 3 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `0` and `6` share the same observed remainder state `1`. -/
theorem coordinate_conflict_remainder_state_zero_six :
    ((coordinate.stateAlignments coordinate_goodMode 8 3)[0]'(by native_decide)).remainderIn = 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 3)[6]'(by native_decide)).remainderIn = 1 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `4` and
`16384`. -/
theorem coordinate_conflict_coefficients_zero_six :
    ((coordinate.stateAlignments coordinate_goodMode 8 3)[0]'(by native_decide)).coefficient = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 3)[6]'(by native_decide)).coefficient = 16384 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `468`. -/
theorem coordinate_conflict_carry_states_zero_six :
    ((coordinate.stateAlignments coordinate_goodMode 8 3)[0]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 3)[6]'(by native_decide)).carryIn = 468 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit
`4`. -/
theorem coordinate_conflict_carried_blocks_zero_six :
    ((coordinate.stateAlignments coordinate_goodMode 8 3)[0]'(by native_decide)).carryBlockValue = 4 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 3)[6]'(by native_decide)).carryBlockValue = 4 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-12 `N = 35` `8/3`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_zero_six_certifiedConflict_eight_three :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 3 0 6
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_three :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 3).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_six_certifiedConflict_eight_three
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base12_n35_m2_blocks8_L3`. -/
theorem base12_n35_m2_blocks8_L3_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 3).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_six_certifiedConflict_eight_three
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase12N35

namespace QRTour.FutureBase12N31

/-! ### Scaffolded finite obstruction example: base 12, N = 31

This packages the next scaffold candidate emitted after
`QRTour.FutureBase12N35` became source-ready. It is a finite worked-example hook
only: it proves the record-shaped obstruction on the certified `8/1` window,
but it does not add a registry claim, theorem-witness record, atlas status
change, or global factorization theorem.
-/

/-- The scaffold coordinate `(base=12, N=31, stride=6)`. -/
def coordinate : BlockCoordinate where
  base := 12
  modulus := 31
  stride := 6
  modulus_pos := by decide

/-- The scaffold coordinate is a good mode: `31 < 2985984`. -/
theorem coordinate_goodMode : coordinate.goodMode := by
  unfold coordinate BlockCoordinate.goodMode BlockCoordinate.blockBase
  native_decide

/-- The selected block base is `2985984`. -/
theorem coordinate_blockBase_eq : coordinate.blockBase = 2985984 := by
  native_decide

/-- The quotient in `2985984 = q*31 + k` is `q = 96322`. -/
theorem coordinate_quotientQ_eq_ninety_six_thousand_three_hundred_twenty_two :
    coordinate.quotientQ = 96322 := by
  native_decide

/-- The remainder in `2985984 = q*31 + k` is `k = 2`. -/
theorem coordinate_remainderK_eq_two : coordinate.remainderK = 2 := by
  native_decide

/-- On the scaffold window, the exact lookahead gap numerator is `2215424`. -/
theorem coordinate_lookaheadGapNumerator_eight_one :
    coordinate.lookaheadGapNumerator 8 1 = 2215424 := by
  unfold coordinate BlockCoordinate.lookaheadGapNumerator
  native_decide

/-- One block of lookahead certifies the eight-block finite window. -/
theorem coordinate_lookaheadCertificate_eight_one :
    coordinate.lookaheadCertificateHolds 8 1 := by
  unfold BlockCoordinate.lookaheadCertificateHolds
  native_decide

/-- Positions `0` and `5` share the same observed remainder state `1`. -/
theorem coordinate_conflict_remainder_state_zero_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[0]'(by native_decide)).remainderIn = 1 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).remainderIn = 1 := by
  native_decide

/-- The same two positions have incompatible raw coefficients `96322` and
`3082304`. -/
theorem coordinate_conflict_coefficients_zero_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[0]'(by native_decide)).coefficient = 96322 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).coefficient = 3082304 := by
  native_decide

/-- The conflicting positions receive incoming carry states `0` and `2`. -/
theorem coordinate_conflict_carry_states_zero_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[0]'(by native_decide)).carryIn = 0 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryIn = 2 := by
  native_decide

/-- The displayed carried block is hidden: both conflicting positions emit
`96322`. -/
theorem coordinate_conflict_carried_blocks_zero_five :
    ((coordinate.stateAlignments coordinate_goodMode 8 1)[0]'(by native_decide)).carryBlockValue = 96322 ∧
      ((coordinate.stateAlignments coordinate_goodMode 8 1)[5]'(by native_decide)).carryBlockValue = 96322 := by
  native_decide

/-- The scaffolded finite obstruction record for the base-12 `N = 31` `8/1`
window. This is the record theorem named by the certificate mapping recipe. -/
theorem coordinate_stateAlignments_zero_five_certifiedConflict_eight_one :
    coordinate.StateAlignmentCertifiedConflict coordinate_goodMode 8 1 0 5
      (by rw [coordinate.stateAlignments_length]; decide)
      (by rw [coordinate.stateAlignments_length]; decide) := by
  exact
    { remainderIn_eq := by native_decide
      coefficient_ne := by native_decide
      left_carryIn_eq_incomingCarry := by native_decide
      right_carryIn_eq_incomingCarry := by native_decide
      carryBlockValue_eq := by native_decide
      remainderToCoefficient_not_functional := by native_decide
      left_carryBlockValue_eq_remainderBlockValue := by native_decide
      right_carryBlockValue_eq_remainderBlockValue := by native_decide }

/-- Proof-style exemplar for the generated projection stub: record theorem ->
projection accessor. -/
theorem coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_five_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

/-- Copyable scaffold projection generated from
`base12_n31_m6_blocks8_L1`. -/
theorem base12_n31_m6_blocks8_L1_not_remainderToCoefficientFunctional :
    ¬ List.FunctionalOnFst
      ((coordinate.stateAlignments coordinate_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  have hrecord := coordinate_stateAlignments_zero_five_certifiedConflict_eight_one
  exact hrecord.not_remainderToCoefficientFunctional

end QRTour.FutureBase12N31

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

/-! ### Positive Reconstruction Exemplar

The same `8/1` selector-family window used to expose the finite quotient-only
profile also gives a positive reconstruction witness for the raw coefficient:
`remainderIn` determines the raw coefficient on this finite window, even
though the reverse carry-to-remainder map remains obstructed.
-/

/-- On the default same-core `996` observability window, the observed
`remainderIn` states are exactly the first eight powers of the remainder `4`,
reduced modulo `996`. -/
theorem actual996_stateAlignments_remainderIn_window_eight_one :
    ((actual996Stride3.stateAlignments actual996Stride3_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)) = [1, 4, 16, 64, 256, 28, 112, 448] := by
  have h0 : actual996Stride3.longDivisionRemainder 0 = 1 := by rfl
  have h1 : actual996Stride3.longDivisionRemainder 1 = 4 := by
    rw [actual996Stride3.longDivisionRemainder_eq_pow_mod]
    norm_num [actual996Stride3, actualCoordinate, BlockCoordinate.blockBase]
  have h2 : actual996Stride3.longDivisionRemainder 2 = 16 := by
    rw [actual996Stride3.longDivisionRemainder_eq_pow_mod]
    norm_num [actual996Stride3, actualCoordinate, BlockCoordinate.blockBase]
  have h3 : actual996Stride3.longDivisionRemainder 3 = 64 := by
    rw [actual996Stride3.longDivisionRemainder_eq_pow_mod]
    norm_num [actual996Stride3, actualCoordinate, BlockCoordinate.blockBase]
  have h4 : actual996Stride3.longDivisionRemainder 4 = 256 := by
    rw [actual996Stride3.longDivisionRemainder_eq_pow_mod]
    norm_num [actual996Stride3, actualCoordinate, BlockCoordinate.blockBase]
  have h5 : actual996Stride3.longDivisionRemainder 5 = 28 := by
    rw [actual996Stride3.longDivisionRemainder_eq_pow_mod]
    norm_num [actual996Stride3, actualCoordinate, BlockCoordinate.blockBase]
  have h6 : actual996Stride3.longDivisionRemainder 6 = 112 := by
    rw [actual996Stride3.longDivisionRemainder_eq_pow_mod]
    norm_num [actual996Stride3, actualCoordinate, BlockCoordinate.blockBase]
  have h7 : actual996Stride3.longDivisionRemainder 7 = 448 := by
    rw [actual996Stride3.longDivisionRemainder_eq_pow_mod]
    norm_num [actual996Stride3, actualCoordinate, BlockCoordinate.blockBase]
  exact actual996Stride3.stateAlignments_remainderIn_window_eight_eq_of_longDivisionRemainders
    actual996Stride3_goodMode 1 h0 h1 h2 h3 h4 h5 h6 h7

/-- On the default same-core `996` observability window, the observed
`remainderIn` states are pairwise distinct. -/
theorem actual996_stateAlignments_remainderIn_nodup_eight_one :
    ((actual996Stride3.stateAlignments actual996Stride3_goodMode 8 1).map
      (fun alignment => alignment.remainderIn)).Nodup := by
  exact actual996Stride3.stateAlignments_remainderIn_nodup_of_window_eq
    actual996Stride3_goodMode 8 1
    actual996_stateAlignments_remainderIn_window_eight_one
    (by norm_num)

/-- On the default same-core `996` observability window, the finite
`remainderIn ↦ raw coefficient` map is functional by finite injective readout. -/
theorem actual996_stateAlignments_remainderToCoefficientFunctional_eight_one :
    List.FunctionalOnFst
      ((actual996Stride3.stateAlignments actual996Stride3_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))) := by
  exact
    actual996Stride3.stateAlignments_remainderToCoefficientFunctional_of_remainderIn_nodup
      actual996Stride3_goodMode 8 1 actual996_stateAlignments_remainderIn_nodup_eight_one

/-- Positive reconstruction exemplar for `996`: on the finite `8/1`
state-alignment window, the raw coefficient factors through the observed
`remainderIn` state. -/
theorem actual996_stateAlignments_remainderToCoefficientFactorsThrough_eight_one :
    let pairs :=
      (actual996Stride3.stateAlignments actual996Stride3_goodMode 8 1).map
        (fun alignment => (alignment.remainderIn, alignment.coefficient))
    FactorsThrough
      (fun p : {p : ℕ × ℕ // p ∈ pairs} =>
        (⟨p.val.1, ⟨p.val.2, p.property⟩⟩ :
          {a : ℕ // ∃ b : ℕ, (a, b) ∈ pairs}))
      (fun p : {p : ℕ × ℕ // p ∈ pairs} => p.val.2) := by
  exact
    actual996Stride3.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderIn_nodup
      actual996Stride3_goodMode 8 1
      actual996_stateAlignments_remainderIn_nodup_eight_one

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
