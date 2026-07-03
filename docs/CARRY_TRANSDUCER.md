# Carry Transducer Model

Status anchor:

<!-- CARRY_TRANSDUCER_STATUS_ANCHOR_START -->
- Claim ID `carry_window_transducer` is `implemented-here`.
- Claim ID `small_k_visibility_threshold` remains `open` and is now split into exact observables in [CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md).
- Claim ID `carry_dfa_factorization` remains `open`.
- Preferred standard label: `carry-propagated block normalization`.
<!-- CARRY_TRANSDUCER_STATUS_ANCHOR_END -->

This layer is the clean standard language for what the repo used to describe informally as “carry correction.”

## The Three Objects

For a chosen block base `B = base^m`, the repo now separates three standard objects:

1. The remainder orbit under multiplication by the base.
2. The raw coefficient stream `qk^j`.
3. The carry transducer that normalizes those coefficients into displayed blocks.

The long-division DFA and the carry transducer are not the same machine.

- The long-division DFA uses remainder states and emits displayed blocks directly.
- The carry transducer uses carry states and consumes the raw coefficient stream.
- On the finite window used by the repo, both produce the same displayed block word.
- Lean now also packages aligned finite state records carrying
  `(position, coefficient, carryIn, carryOut, remainderIn, remainderOut)` on
  those windows, together with the exact local carry-balance and
  remainder-balance equations at each aligned position, plus exact
  finite-window functional criteria for the observed remainder-to-carry and
  carry-to-remainder state-pair lists, finite transition-compatibility
  theorems under those criteria, and explicit finite conflict lemmas when the
  observed pair list violates them.

That is the implemented bridge, not yet a full canonical factorization theorem.

## Throughline Ladder

Read this note as the carry-facing slice of the repo's orbit-plus-carry
research thesis. The ladder below keeps the exact orbit layer, the exact
block-coordinate layer, the implemented finite-window carry layer, and the
remaining open frontier explicit in one place.

<!-- CARRY_TRANSDUCER_THROUGHLINE_START -->
| Ladder rung | Registry support |
|-------------|------------------|
| Exact orbit support | Claims `digit_periodicity` and `preperiod_from_base_factors`; witnesses `digit_periodicity_prime19_base10` and `preperiod_from_base_factors_n996_base10`. Remainder periodicity and stripping of base-supported factors fix the exact orbit surface before any carry-normalization claim enters. |
| Exact block-coordinate support | Claims `series_q_weighted_identity` and `positive_q_good_modes`; witnesses `series_q_weighted_identity_prime97_stride2`, `series_q_weighted_identity_n249_stride3`, and `positive_q_good_modes_n249_stride3`. The raw coefficient stream is exactly `qk^j`, and the repo only promotes positive-q coordinates once `B > M`. Counterexamples: `legacy_unweighted_series_37` and `legacy_zero_quotient_mode`. |
| Implemented finite-window carry support | Claims `incoming_carry_position_formula`, `same_core_threshold_shift_interval`, and `carry_window_transducer`; witnesses `incoming_carry_position_formula_prime97_stride2`, `incoming_carry_position_formula_n249_stride3`, `same_core_threshold_shift_interval_996_over_249`, `carry_window_transducer_prime97_window6`, `carry_window_transducer_n249_window3`, and `carry_window_transducer_same_core_996_window4`. Finite-window carry-normalized output, exact incoming-carry boundaries, and same-core shift transport are already exact on named windows. Counterexamples: `legacy_visibility_local_overflow_97` and `legacy_visibility_local_overflow_249`. |
| Obstruction / counterexample surface | Claims `carry_dfa_factorization`; witnesses `carry_dfa_factorization_target_21_97_996` and `carry_dfa_factorization_target_249_498_996_same_core`. Observed state-map failures now split into visible preimage compression, hidden graph obstruction, and selector-profile disagreement, showing why finite output agreement does not by itself promote to a state-level theorem. Counterexamples: `carry_state_relabeling_failure_97`, `carry_state_relabeling_failure_996`, `carry_selector_monotonicity_failure_21`, and `carry_selector_core_invariance_failure_996`. |
| Open factorization targets | Claims `small_k_visibility_threshold` and `carry_dfa_factorization`; witnesses `small_k_visibility_threshold_target_97_249_996`, `carry_dfa_factorization_target_21_97_996`, and `carry_dfa_factorization_target_249_498_996_same_core`. The remaining frontier is an exact visibility threshold and a canonical orbit-plus-carry factorization, both kept explicitly open. Counterexamples: `carry_selector_core_invariance_failure_996`. |
<!-- CARRY_TRANSDUCER_THROUGHLINE_END -->

## API Surface

In [transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py):

- `CarryTransducer` is the finite-window normalization machine.
- `CarryRun` stores one concrete run.
- `CarryRun.state_summary()` exposes reachable carry states and the first nonzero carry position.
- `StateGraph` and `MinimizedStateGraph` give the stable observed-graph interface used by both the carry transducer and the remainder DFA.
- `CarryRun.state_summary().graph()` builds the carry-state graph, while `CarryRun.state_summary().minimize()` gives the coarse observed minimization used by the repo.
- `remainder_dfa_run(N, block_base, steps)` builds the long-division DFA run in the same block coordinates.
- `carry_remainder_comparison(N, ...)` packages the finite-window agreement statement, the two graph objects, and the explicit open-boundary wording.
- `ObservedStateMap` now exports the full preimage-fiber profile (state-merging atlas): source fibers, target preimage fibers, visible compression targets, ambiguity records, and compact signature strings in both directions.
- `FactorizationDecisionReport` turns one comparison into a Track 17 decision object: state relabeling candidate, quotient candidate, lift candidate, theorem target, refutation target, and weaker replacement claim.
- `carry_factorization_selector_profile(...)` records how the Track 17 regime changes as the block width `m` varies.
- `state_merging_rows(...)` exports the selected-coordinate preimage-fiber profile directly, together with the visible-vs-hidden obstruction classifier, graph gaps, and short obstruction summaries.
- `state_merging_same_core_rows(...)` groups those selected profiles by stripped periodic core and records where same-core families span relabeling, hidden graph obstruction, and visible compression.
- `same_core_obstruction_phase_rows(...)` turns those same-core families into phase paths, recording first hidden and visible members, re-hiding after visibility, and hidden/visible switch counts.
- `same_core_obstruction_correlate_rows(...)` summarizes bounded empirical correlates of re-hiding versus one-way visibility, including onset kind and first hidden/visible multiplier valuations on the base-10 same-core surface.
- `quotient_obstruction_rows(...)` exports the quotient-only split directly as visible preimage compression versus hidden graph obstruction.
- `quotient_obstruction_family_rows(...)` groups same-core families by whether that visible/hidden split changes across members.
- `carry_selector_profile_rows(...)` exports the selector classification surface directly.
- `non_k_one_state_relabeling_rows(...)` isolates the selected non-`k = 1` relabeling windows.
- `same_core_selector_family_rows(...)` groups selector profiles by stripped periodic core and records where families disagree.
- `canonical_carry_dfa_examples()` returns the named `21`, `97`, `996` comparison suite used across docs, tests, and the published atlas.
- `canonical_carry_selector_case_studies()` and `canonical_carry_selector_family_studies()` promote the strongest selector findings into the published atlas as a research layer.
- `canonical_state_merging_case_studies()` and `canonical_state_merging_family_studies()` promote the canonical `21 / 97 / 89 / 996` and `249 / 498 / 996`, `17 / 34 / 68 / 85` obstruction studies into the published atlas.
- `carry_factorization_rows(...)` performs bounded Track 17 sweeps so candidate notions can be tested on concrete examples before theorem promotion.
- `carry_window_example(N, ...)` builds the combined view:
  raw coefficients, carry-normalized blocks, and long-division blocks.
  When a finite raw prefix is not enough, it automatically adds a small lookahead so the visible block window matches long division exactly.
- `orbit_carry_trace_rows(...)` exports an experimental finite trace lens for
  canonical examples such as `21 / 97 / 996`, aligning cycle index, remainder
  orbit state, raw coefficient, finite carry-window state, and displayed block
  without upgrading `carry_dfa_factorization` beyond its current open status.
- `visibility_optics_workbench_rows(...)` ranks finite-window evidence across
  carried-prefix visibility, orbit/carry trace anchors, state-map compression,
  and same-core drift. It is a probe for the **Visibility Optics workbench**,
  not a proof of global visibility or DFA factorization.

Minimal example:

```python
from bridge_reptends import carry_window_example

example = carry_window_example(97, prefer_m=2, n_blocks=8)
summary = example.run.state_summary()

print(example.raw_coefficients[:8])
print(example.carried_blocks[:8])
print(example.actual_blocks[:8])
print(summary.reachable_states)
print(summary.first_nonzero_position)
print(summary.to_dot())
```

## Experimental Orbit-Carry Trace Lens

The command below is a campfire-friendly report surface for the current thesis:

```bash
search-reptends orbit-carry-trace --base 10 --blocks 8 --members 21,97,996
```

For a broader ranked probe, use:

```bash
search-reptends visibility-optics --max 1200 --base 10 --blocks 8 --top 20
```

Read [VISIBILITY_OPTICS_WORKBENCH.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/VISIBILITY_OPTICS_WORKBENCH.md)
for the signal classes, row groups, and recommended drill-down commands.
The companion base-instrument comparison keeps base `30` as data rather than
as a new default representation:

```bash
search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20
```

The certified positive-lookahead obstruction drill-down stays empirical and
open-boundary-facing:

```bash
search-reptends visibility-coefficient-conflicts --max 1200 --base 10 --blocks 8 --top 20
```

The cross-base obstruction atlas keeps the same finite conflict rows but
compares base instruments without promoting them to claim status:

```bash
search-reptends visibility-coefficient-conflict-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

The family miner groups only recurring hidden-output conflict shapes and emits
the next Lean-theorem recommendation as empirical/open-boundary guidance:

```bash
search-reptends visibility-coefficient-conflict-families --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

Its first base-10 witness is
`(base, N, m, B, q, k, L, gap) = (10, 68, 4, 10000, 147, 4, 1, 6208)`.
On that certified positive-lookahead window, remainder state `4` appears at positions `1` and `5` with raw coefficients `588` and `150528`, incoming carry states `0` and `60`, and the same carried block value `588`. This is evidence for a concrete remainder-to-coefficient conflict, not a theorem-level closure of `small_k_visibility_threshold` or `carry_dfa_factorization`.

At the default bound, the same hidden-output shape
`periodic_modulus=17;k=4;remainder_state=4;positions=[1, 5];carry_states=[0, 60];output_hidden=true`
recurs for `N = 68` in bases `10` and `30`. The family-miner
recommendation is therefore
`classify_composite68_cross_base_hidden_output_conflict`, but this remains an
empirical theorem-candidate selector rather than a registry claim.

For a sharper `Composite68`-only base sweep, use:

```bash
search-reptends visibility-composite68-base-sweep --max-base 120 --blocks 8 --top 20
```

At that bound, the exact shape occurs for bases
`10, 30, 32, 64, 66, 72, 98, 100`; every emitted target row has
`B mod 68 = 4`. The finite Lean response to that recommendation has now
landed: the base-`30` obstruction is packaged below, and the shared finite
`k = 4`, positive-`q`, positions-`1/5` coefficient-conflict helper is generic.
Lean now also proves the repeated-state side for the `N = 68`, `k = 4`
coordinate family from `4^1 ≡ 4^5 (mod 68)`. The remaining open boundary is
arithmetic classification of which base/stride instruments land in that
`B ≡ 4 (mod 68)` family with the same certified positive-lookahead shape.

The congruence-family classifier forces every bounded coordinate with
`B = base^m > 68` and `B ≡ 4 (mod 68)` instead of relying on the selected-mode
sweep:

```bash
search-reptends visibility-composite68-congruence-family --max-base 120 --max-m 8 --blocks 8 --top 0
```

Lean now covers the finite obstruction for that whole `N = 68`,
`B ≡ 4 (mod 68)` coordinate family once the window contains positions `1` and
`5`. The command remains empirical because the certified positive-lookahead
and hidden-output rows are still bounded observations, not a closed-form
least-lookahead theorem or a `carry_dfa_factorization` result.

The **Certificate Workbench** is the tactical consolidation layer for this
frontier. It exports flat, Lean-shaped certificate rows that combine the
lookahead certificate, state-map diagnostics, first coefficient conflict when
present, current theorem-frontier status, and a recommended next Lean task:

```bash
search-reptends visibility-certificate-workbench --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

This is empirical/open-boundary tooling only. It is meant to help choose and
audit the next finite Lean package; it does not promote
`small_k_visibility_threshold`, `carry_dfa_factorization`, or any new
theorem-witness or atlas claim.

The **Observability Atlas** is a thin projection of the Certificate Workbench
onto the observability-boundary lens:

```bash
search-reptends observability-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 50
```

It reuses the workbench arithmetic and emits `observability_summary`,
`hidden_coefficient_conflict`, `visible_coefficient_conflict`,
`coefficient_functional_frontier`, and `gap_one_bridge_candidate` rows. The
observability aliases `coefficient_observability_class`,
`observability_boundary_status`, `source_symmetry_visible`,
`coefficient_information_lost`, `carry_output_hides_conflict`, and
`next_observability_task` are empirical/open-boundary observability tooling:
they mark coefficient information loss across the carry boundary without
closing `small_k_visibility_threshold`, closing `carry_dfa_factorization`, or
creating a registry, theorem-witness, or atlas-status promotion.

The **Observability Program Atlas** is the coordinator surface for the pivot:

```bash
search-reptends observability-program-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 50
```

It composes the existing observability atlas, target signatures, instrument
comparison, Shape13/17/187 classifiers, and functional-frontier rows into
`observability_program_summary`, `observability_program_lane`,
`observability_program_family`,
`observability_positive_reconstruction_candidate`, and
`observability_program_next_task` rows. Its positive reconstruction lane tracks
empirical factor-through target candidates where the finite observed
`remainder_state` determines raw coefficients, coefficients modulo `B`, carried
block values, and carry states. The first finite Lean proof hooks in that lane
are
`QRTour.Prime97.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`
and
`QRTour.Composite996.actual996_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
plus the smaller-gap base-10 denominator-`98` hook
`QRTour.FutureBase10N98.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (10, 98, 2, 100, 1, 2, 1, 44)`,
and the base-12 denominator-`142` hook
`QRTour.FutureBase12N142.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (12, 142, 2, 144, 1, 2, 1, 32)`,
and the base-7 denominator-`47` hook
`QRTour.FutureBase7N47.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (7, 47, 2, 49, 1, 2, 1, 38)`,
and the base-12 denominator-`71` hook
`QRTour.FutureBase12N71.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (12, 71, 2, 144, 2, 2, 1, 64)`,
and the base-10 denominator-`49` hook
`QRTour.FutureBase10N49.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (10, 49, 2, 100, 2, 2, 1, 88)`,
and the base-30 denominator-`299` hook
`QRTour.FutureBase30N299.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (30, 299, 2, 900, 3, 3, 1, 117)`,
and the base-7 denominator-`170` hook
`QRTour.FutureBase7N170.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (7, 170, 3, 343, 2, 3, 1, 255)`,
all obtained through
`BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderToCoefficientFunctional`,
the positive wrapper over the `List.FunctionalOnFst` / `FactorsThrough` bridge.
Program-atlas rows expose `positive_reconstruction_source_pinned`,
`positive_reconstruction_source_status`,
`positive_reconstruction_lean_support_status`,
`positive_reconstruction_functional_theorem`, and
`positive_reconstruction_factor_through_theorem` so those source-pinned finite
hooks remain separated from still-empirical reconstruction candidates.
The first mined sufficient criterion is
`finite_remainder_state_injective_on_window`: rows export
`remainder_state_window`, `raw_coefficient_window`,
`remainder_state_window_injective`,
`positive_reconstruction_arithmetic_criterion_id`, and
`positive_reconstruction_hyp_remainder_state_window_injective`. Lean now
packages this finite criterion via `List.functionalOnFst_of_map_fst_nodup`,
`BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderIn_nodup`,
and
`BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderIn_nodup`,
and the arithmetic no-collision strengthening is exported as
`finite_remainder_power_residue_no_collision`: rows expose
`remainder_power_residue_window` and
`positive_reconstruction_hyp_remainder_power_residue_window_injective`. Lean
packages that power-residue criterion via
`BlockCoordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup`,
`BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup`,
and
`BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup`,
and the smaller no-wrap sufficient criterion is exported as
`finite_remainder_power_residue_no_wrap`: rows expose
`remainder_power_unreduced_window` and
`positive_reconstruction_hyp_remainder_power_residue_no_wrap`, while Lean packages
the theorem path through
`BlockCoordinate.remainderK_powerResidues_nodup_of_remainderK_pow_lt_modulus`,
`BlockCoordinate.stateAlignments_remainderIn_nodup_of_remainderK_pow_lt_modulus`,
`BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_pow_lt_modulus`,
and
`BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_pow_lt_modulus`,
with source-pinned injective-readout witnesses
`QRTour.Prime97.coordinate_stateAlignments_remainderIn_nodup_eight_two`,
`QRTour.FutureBase10N98.coordinate_stateAlignments_remainderIn_nodup_eight_one`,
`QRTour.FutureBase12N142.coordinate_stateAlignments_remainderIn_nodup_eight_one`,
`QRTour.FutureBase7N47.coordinate_stateAlignments_remainderIn_nodup_eight_one`,
`QRTour.FutureBase12N71.coordinate_stateAlignments_remainderIn_nodup_eight_one`,
`QRTour.FutureBase10N49.coordinate_stateAlignments_remainderIn_nodup_eight_one`,
`QRTour.FutureBase30N299.coordinate_stateAlignments_remainderIn_nodup_eight_one`,
`QRTour.FutureBase7N170.coordinate_remainderK_powerResidues_nodup_eight`,
and `QRTour.Composite996.actual996_stateAlignments_remainderIn_nodup_eight_one`.
The same summary now exports the first unpinned no-collision seed:
`first_unpinned_positive_reconstruction_tuple =
[7, 340, 3, 343, 1, 3, 1, 299]`, with
`first_unpinned_positive_reconstruction_remainder_power_residue_window =
[1, 3, 9, 27, 81, 243, 49, 147]` and
`first_unpinned_positive_reconstruction_family_seed_tuples =
[[7, 170, 3, 343, 2, 3, 1, 255]]`. Lean now proves the finite base-7,
stride-3 divisor-family criterion through
`QRTour.Base7K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`
and
`QRTour.Base7K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
The recommended decision is
`use_lean_proved_family_criterion_before_source_pinning_more_examples`. The
same summary now separates the first uncovered row after source-pinned and
family-covered rows. The previous uncovered seed
`QRTour.FutureBase10N997.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
is now source-pinned. The previous base-30 sibling seed
`(30, 897, 2, 900, 1, 3, 1, 639)` is now family-covered by
`QRTour.Base30K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`
and
`QRTour.Base30K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`,
with proof-covered moduli `[23, 69, 299, 897]` and pair hook
`QRTour.Base30K3PositiveReconstruction.n299_n897_powerResidues_nodup_eight_pair`.
The previous base-10 sibling seed `[10, 498, 3, 1000, 2, 4, 1, 928]` is now
family-covered by
`QRTour.Base10K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`,
with proof-covered moduli `[83, 166, 249, 332, 498, 996]` and pair hook
`QRTour.Base10K4PositiveReconstruction.n498_n996_powerResidues_nodup_eight_pair`.
The previous standalone/order-boundary seed `[12, 575, 3, 1728, 3, 3, 1, 1053]`
with power-residue window `[1, 3, 9, 27, 81, 243, 154, 462]`
is now source-pinned as
`QRTour.FutureBase12N575.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
with sibling functional theorem
`QRTour.FutureBase12N575.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
with no-collision hook
`QRTour.FutureBase12N575.coordinate_remainderK_powerResidues_nodup_eight`.
The previous base-12 `75`/`575` sibling lane is now family-covered by
`QRTour.Base12K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`,
with proof-covered moduli `[23, 25, 69, 75, 115, 345, 575, 1725]` and pair hook
`QRTour.Base12K3PositiveReconstruction.n75_n575_powerResidues_nodup_eight_pair`.
The covered sibling seed `[12, 75, 3, 1728, 23, 3, 1, 1161]` has
power-residue window `[1, 3, 9, 27, 6, 18, 54, 12]`; divisors
`[1, 3, 5, 15]` remain outside this finite eight-entry no-collision criterion.
The previous standalone/order-boundary seed `[7, 1199, 4, 2401, 2, 3, 1, 1284]`
with power-residue window `[1, 3, 9, 27, 81, 243, 729, 988]`
is now source-pinned as
`QRTour.FutureBase7N1199.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
with sibling functional theorem
`QRTour.FutureBase7N1199.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
with no-collision hook
`QRTour.FutureBase7N1199.coordinate_remainderK_powerResidues_nodup_eight`.
The previous standalone/order-boundary seed `[10, 294, 4, 10000, 34, 4, 1, 1776]`
has `preperiod_digits = 1`, `periodic_modulus = 147`, and power-residue window
`[1, 4, 16, 64, 256, 142, 274, 214]`; it is now source-pinned as
`QRTour.FutureBase10N294.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
with sibling functional theorem
`QRTour.FutureBase10N294.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`
and no-collision hook
`QRTour.FutureBase10N294.coordinate_remainderK_powerResidues_nodup_eight`.
The previous base-7 `109`/`1199` sibling lane is now family-covered by
`QRTour.Base7Stride4K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`,
with proof-covered moduli `[109, 218, 1199, 2398]` and pair hook
`QRTour.Base7Stride4K3PositiveReconstruction.n109_n1199_powerResidues_nodup_eight_pair`.
The covered sibling seed `[7, 109, 4, 2401, 22, 3, 1, 2119]` has
power-residue window `[1, 3, 9, 27, 81, 25, 75, 7]`; divisors
`[1, 2, 11, 22]` remain outside this finite eight-entry no-collision criterion.
The previous standalone/order-boundary seed
`[7, 46, 2, 49, 1, 3, 2, 2171]`, with
power-residue window `[1, 3, 9, 27, 35, 13, 39, 25]`, is now source-pinned as
`QRTour.FutureBase7N46.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`,
with sibling functional theorem
`QRTour.FutureBase7N46.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two`
and no-collision hook
`QRTour.FutureBase7N46.coordinate_remainderK_powerResidues_nodup_eight`.
The previous standalone/order-boundary seed
`[7, 141, 4, 2401, 17, 4, 1, 2353]`, with
power-residue window `[1, 4, 16, 64, 115, 37, 7, 28]`, is now source-pinned as
`QRTour.FutureBase7N141.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
with sibling functional theorem
`QRTour.FutureBase7N141.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`
and no-collision hook
`QRTour.FutureBase7N141.coordinate_remainderK_powerResidues_nodup_eight`.
Lean now proves the base-10, stride-4, `k = 4` finite divisor-family criterion
covering the previous `[10, 714, 4, 10000, 14, 4, 1, 2496]` row, with
power-residue window `[1, 4, 16, 64, 256, 310, 526, 676]`, through
`QRTour.Base10Stride4K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base10Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base10Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
the proof-covered moduli are
`[49, 98, 119, 147, 196, 238, 294, 357, 476, 588, 714, 833]`, and the pair hook
`QRTour.Base10Stride4K4PositiveReconstruction.n294_n714_powerResidues_nodup_eight_pair`
keeps the `294`/`714` signal visible. Lean now also proves the base-12,
stride-4, `k = 4` finite divisor-family criterion covering the previous
`[12, 73, 4, 20736, 284, 4, 1, 8704]` row, with power-residue window
`[1, 4, 16, 64, 37, 2, 8, 32]`, through
`QRTour.Base12Stride4K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
the proof-covered moduli are
`[71, 73, 142, 146, 284, 292, 5183, 10366, 20732]`, and the pair hook
`QRTour.Base12Stride4K4PositiveReconstruction.n73_n146_powerResidues_nodup_eight_pair`
keeps the `73`/`146` signal visible. The source-pinned seed
`[12, 146, 4, 20736, 142, 4, 1, 4352]`, with `preperiod_digits = 1`,
`periodic_modulus = 73`, and power-residue window
`[1, 4, 16, 64, 110, 2, 8, 32]`, remains source-pinned through
`QRTour.FutureBase12N146.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase12N146.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase12N146.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous standalone/order-boundary seed `[10, 769, 4, 10000, 13, 3, 1, 4707]`,
with `preperiod_digits = 0`, `periodic_modulus = 769`, and power-residue
window `[1, 3, 9, 27, 81, 243, 729, 649]`, is now source-pinned through
`QRTour.FutureBase10N769.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase10N769.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase10N769.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous standalone/order-boundary seed `[7, 345, 6, 117649, 341, 4, 1, 5534]`,
with `preperiod_digits = 0`, `periodic_modulus = 345`, and power-residue
window `[1, 4, 16, 64, 256, 334, 301, 169]`, is now source-pinned through
`QRTour.FutureBase7N345.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N345.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase7N345.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
Lean now also proves the base-7, stride-6, `k = 4` finite divisor-family
criterion covering the previous `[7, 465, 6, 117649, 253, 4, 1, 7901]` row,
with power-residue window `[1, 4, 16, 64, 256, 94, 376, 109]`, through
`QRTour.Base7Stride6K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
the proof-covered moduli are
`[23, 55, 69, 115, 155, 165, 253, 345, 465, 713, 759, 1265, 1705, 2139, 3565, 3795, 5115, 7843, 10695, 23529, 39215, 117645]`,
and the pair hook
`QRTour.Base7Stride6K4PositiveReconstruction.n345_n465_powerResidues_nodup_eight_pair`
keeps the `345`/`465` signal visible.
The previous standalone/order-boundary row `[12, 47, 2, 144, 3, 3, 2, 9639]`,
with power-residue window `[1, 3, 9, 27, 34, 8, 24, 25]`, is now
source-pinned through
`QRTour.FutureBase12N47.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase12N47.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two`,
and
`QRTour.FutureBase12N47.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`.
Lean now also proves the base-12, stride-2, `k = 3` finite divisor-family
criterion covering the previous `[12, 141, 2, 144, 1, 3, 2, 10125]` row,
with power-residue window `[1, 3, 9, 27, 81, 102, 24, 72]`, through
`QRTour.Base12Stride2K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
the proof-covered moduli are `[47, 141]`, the pair hook
`QRTour.Base12Stride2K3PositiveReconstruction.n47_n141_powerResidues_nodup_eight_pair`
keeps the `47`/`141` signal visible, and divisors `[1, 3]` are deliberately
outside this finite eight-entry no-collision criterion.
The previous standalone/order-boundary row `[30, 794, 3, 27000, 34, 4, 1, 12776]`,
with `preperiod_digits = 1`, `periodic_modulus = 397`, and power-residue
window `[1, 4, 16, 64, 256, 230, 126, 504]`, is now source-pinned through
`QRTour.FutureBase30N794.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase30N794.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase30N794.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
Lean now also proves the base-30, stride-3, `k = 4` finite divisor-family
criterion covering the previous `[30, 397, 3, 27000, 68, 4, 1, 25552]` row,
with power-residue window `[1, 4, 16, 64, 256, 230, 126, 107]`, through
`QRTour.Base30Stride3K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
the proof-covered moduli are `[397, 794, 1588, 6749, 13498, 26996]`, the
pair hook
`QRTour.Base30Stride3K4PositiveReconstruction.n397_n794_powerResidues_nodup_eight_pair`
keeps the `397`/`794` signal visible, and divisors
`[1, 2, 4, 17, 34, 68]` are deliberately outside this finite eight-entry
no-collision criterion.
The previous standalone/order-boundary row
`[10, 578, 5, 100000, 173, 6, 1, 26432]`, with power-residue window
`[1, 6, 36, 216, 140, 262, 416, 184]`, is now source-pinned through
`QRTour.FutureBase10N578.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase10N578.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase10N578.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous `[10, 277, 5, 100000, 361, 3, 1, 31479]` row, with
power-residue window `[1, 3, 9, 27, 81, 243, 175, 248]`, is now source-pinned
through
`QRTour.FutureBase10N277.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase10N277.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase10N277.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous `[7, 669, 7, 823543, 1231, 4, 1, 32398]` row, with
power-residue window `[1, 4, 16, 64, 256, 355, 82, 328]`, is now
source-pinned through
`QRTour.FutureBase7N669.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N669.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase7N669.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous `[7, 71, 6, 117649, 1657, 2, 1, 46404]` row, with
power-residue window `[1, 2, 4, 8, 16, 32, 64, 57]`, is now source-pinned
through
`QRTour.FutureBase7N71.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N71.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase7N71.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous `[7, 118, 6, 117649, 997, 3, 1, 47027]` row, with
power-residue window `[1, 3, 9, 27, 81, 7, 21, 63]`, is now source-pinned
through
`QRTour.FutureBase7N118.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N118.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase7N118.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
Lean now also proves the base-7, stride-6, `k = 3` finite divisor-family
criterion covering the widened-atlas `[7, 997, 6, 117649, 118, 3, 1, 49345]`
row, with power-residue window `[1, 3, 9, 27, 81, 243, 729, 193]`, through
`QRTour.Base7Stride6K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base7Stride6K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base7Stride6K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
the proof-covered moduli are `[59, 118, 997, 1994, 58823, 117646]`, the pair
hook
`QRTour.Base7Stride6K3PositiveReconstruction.n118_n997_powerResidues_nodup_eight_pair`
keeps the `118`/`997` signal visible, and divisors `[1, 2]` are deliberately
outside this finite eight-entry no-collision criterion.
Lean now also proves the base-10, stride-5, `k = 6` finite divisor-family
criterion covering the previous `[10, 289, 5, 100000, 346, 6, 1, 52864]`
frontier row, with power-residue window `[1, 6, 36, 216, 140, 262, 127, 184]`,
through
`QRTour.Base10Stride5K6PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base10Stride5K6PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base10Stride5K6PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
the proof-covered moduli are `[17, 34, 173, 289, 346, 578, 2941, 5882, 49997, 99994]`,
the pair hook
`QRTour.Base10Stride5K6PositiveReconstruction.n289_n578_powerResidues_nodup_eight_pair`
keeps the `289`/`578` signal visible, and divisors `[1, 2]` are deliberately
outside this finite eight-entry no-collision criterion.
The previous `[12, 226, 5, 248832, 1101, 6, 1, 62208]` row, with
`preperiod_digits = 1`, `periodic_modulus = 113`, and power-residue window
`[1, 6, 36, 216, 166, 92, 100, 148]`, is now source-pinned through
`QRTour.FutureBase12N226.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase12N226.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase12N226.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous `[7, 338, 3, 343, 1, 5, 2, 64744]` row, with power-residue
window `[1, 5, 25, 125, 287, 83, 77, 47]`, is now source-pinned through
`QRTour.FutureBase7N338.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N338.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two`,
and
`QRTour.FutureBase7N338.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`.
The previous `[12, 149, 5, 248832, 1670, 2, 1, 70144]` row, with no-wrap
unreduced/power-residue window `[1, 2, 4, 8, 16, 32, 64, 128]`, is now
source-pinned through `QRTour.FutureBase12N149.coordinate_remainderK_pow_lt_modulus_eight`,
`QRTour.FutureBase12N149.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase12N149.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase12N149.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
Lean now also proves the base-12, stride-5, `k = 3` finite divisor-family
criterion covering the previous `[12, 289, 5, 248832, 861, 3, 1, 74115]`
row, with power-residue window `[1, 3, 9, 27, 81, 243, 151, 164]`, through
`QRTour.Base12Stride5K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base12Stride5K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base12Stride5K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
the proof-covered moduli are
`[17, 41, 51, 119, 123, 287, 289, 357, 697, 861, 867, 2023, 2091, 4879, 6069, 11849, 14637, 35547, 82943, 248829]`,
the pair hook
`QRTour.Base12Stride5K3PositiveReconstruction.n289_n861_powerResidues_nodup_eight_pair`
keeps the `289`/`861` signal visible, and divisors `[7, 21]` are deliberately
outside this finite eight-entry no-collision criterion.
Lean now also proves the base-10, stride-5, `k = 4` finite divisor-family
criterion covering the previous `[10, 641, 5, 100000, 156, 4, 1, 76384]`
row, with power-residue window `[1, 4, 16, 64, 256, 383, 250, 359]`, through
`QRTour.Base10Stride5K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base10Stride5K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base10Stride5K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
the proof-covered moduli are
`[641, 1282, 1923, 2564, 3846, 7692, 8333, 16666, 24999, 33332, 49998, 99996]`,
the pair hook
`QRTour.Base10Stride5K4PositiveReconstruction.n641_n1282_powerResidues_nodup_eight_pair`
keeps the `641`/`1282` signal visible, and good divisors
`[6, 12, 13, 26, 39, 52, 78, 156]` deliberately remain outside this finite
eight-entry no-collision criterion.
The atlas now reports
`first_uncovered_positive_reconstruction_tuple =
[10, 361, 5, 100000, 277, 3, 1, 82603]`, with
`first_uncovered_positive_reconstruction_remainder_power_residue_window =
[1, 3, 9, 27, 81, 243, 7, 21]`, source-pinned sibling seed
`[10, 277, 5, 100000, 361, 3, 1, 31479]`, and decision
`pursue_family_criterion_before_source_pinning_more_examples`; the next task is
`prove_or_reject_same_base_block_remainder_power_no_collision_family`.
The previous `[12, 691, 4, 20736, 30, 6, 1, 20736]` row, with power-residue
window `[1, 6, 36, 216, 605, 175, 359, 81]`, is now source-pinned through
`QRTour.FutureBase12N691.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase12N691.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase12N691.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous `[7, 113, 3, 343, 3, 4, 2, 13444]` row, with power-residue window
`[1, 4, 16, 64, 30, 7, 28, 112]`, is now source-pinned through
`QRTour.FutureBase7N113.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N113.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two`,
and
`QRTour.FutureBase7N113.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`.
The previous standalone/order-boundary row `[7, 542, 5, 16807, 31, 5, 1, 8472]`,
with power-residue window `[1, 5, 25, 125, 83, 415, 449, 77]`, is now
source-pinned through
`QRTour.FutureBase7N542.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N542.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase7N542.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
This is empirical/open-boundary program tooling for choosing the next Lean task,
not a theorem declaration, registry claim, theorem-witness record, atlas-status
promotion, `small_k_visibility_threshold` closure, or
`carry_dfa_factorization` closure.

The **Observability Target Split** command expands those atlas rows into one
row per factor-through target:

```bash
search-reptends observability-target-split --max 1200 --bases 7,10,12,30 --blocks 8 --top 50
```

It emits `observability_target_split_summary` and
`observability_target_split_case` rows for the fixed target IDs
`raw_coefficient_nat`, `coefficient_mod_block_base`, `carried_block_value`,
`carry_state`, `remainder_state`, and `displayed_prefix`. The first four are
pointwise finite maps from observed `remainder_state`; `remainder_state` is the
identity observation baseline; and `displayed_prefix` is a window-level certificate,
not a pointwise `FactorsThrough` map. This is empirical/open-boundary
target-split tooling only, not a theorem declaration, registry claim,
theorem-witness record, atlas-status promotion, `small_k_visibility_threshold`
closure, or `carry_dfa_factorization` closure.

The **Observability Target Signatures** command groups those case rows by the
full `observability_target_summary_signature`:

```bash
search-reptends observability-target-signatures --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

It emits `observability_target_signature_summary` and
`observability_target_signature_family` rows that separate families where raw
coefficient observability fails while carried output stays functional from
families where coefficient modulo `B` or carry state is the next visible
information-loss target. This is empirical/open-boundary target-signature
tooling only, not a theorem declaration, registry claim, theorem-witness
record, atlas-status promotion, `small_k_visibility_threshold` closure, or
`carry_dfa_factorization` closure.

The **Mod-Stable Carry-Loss** drill-down focuses on the second hidden-output
signature:

```bash
search-reptends observability-mod-stable-carry-loss --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

It emits `observability_mod_stable_carry_loss_summary` and
`observability_mod_stable_carry_loss_case` rows where `raw_coefficient_nat`
does not factor through observed `remainder_state`, `coefficient_mod_block_base`
still does, `carried_block_value` hides the raw conflict, and `carry_state`
does not factor through. The first default row is
`(base, N, m, B, q, k, L, gap) = (30, 26, 1, 30, 1, 4, 5, 11927264)`.
This is empirical/open-boundary mod-stable carry-loss tooling only, not a
theorem declaration, registry claim, theorem-witness record, atlas-status
promotion, `small_k_visibility_threshold` closure, or
`carry_dfa_factorization` closure.

The focused **Shape13/K4 mod-stable carry-loss classifier** expands the first
source shape from that drill-down:

```bash
search-reptends observability-shape13-k4-mod-stable-carry-loss --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

It emits `observability_shape13_k4_mod_stable_carry_loss_summary` plus
`observability_shape13_k4_mod_stable_carry_loss_member` rows for
`periodic_modulus=13;k=4;position_gap=6`. Under the default scan, base-`30`
`N = 13` supplies the source-core tuple
`(base, N, m, B, q, k, L, gap) = (30, 13, 1, 30, 2, 4, 5, 23854528)` on
positions `[0,6]`, while base-`30` `N = 26` supplies the shifted tuple
`(30, 26, 1, 30, 1, 4, 5, 11927264)` on positions `[1,7]`. The rows expose the
same mod-stable carry-loss profile: raw coefficient observability fails,
coefficient modulo `B` stays functional, carried output hides the raw conflict,
and carry state loses information. Lean now pins the finite pair via
`QRTour.FutureBase30N13.coordinate_stateAlignments_zero_six_certifiedConflict_eight_five`
and
`QRTour.FutureBase30N26.coordinate_stateAlignments_one_seven_certifiedConflict_eight_five`.
The wrapper
`QRTour.Shape13K4.base30_core13_to_double26_conflict_shift_scaled` proves the
one-position, scale-two finite row comparison, while
`QRTour.Shape13K4.base30_n26_scaleTwoHiddenCarryBlockValueHypotheses`
packages the exported `shape13_k4_hyp_*` booleans as
`SameCoreScaleTwoHiddenCarryBlockValueHypotheses`, and
`QRTour.Shape13K4.base30_n26_sameCore_scale_two_hiddenCarryBlockValue_shift`
instantiates
`sameCoreCompatible_hiddenCarryBlockValue_shift_scale_two_of_exportedHypotheses`
for the canonical carried-output equality at shifted positions `[1,7]`. This
remains empirical/open-boundary Shape13/K4 classifier support plus finite Lean
support only, not a registry claim, theorem-witness promotion, atlas-status
upgrade, `small_k_visibility_threshold` closure, or `carry_dfa_factorization`
closure.

The scale-two wrapper states the exact arithmetic criterion to reuse before
adding another finite Shape13 package: same-core compatibility,
`basePrimeSupportFactor * 2 = k`, the two scaled quotient-remainder bounds
below `B-k`, the two scaled block-remainder bounds below `B`, and the
source-core hidden carried-output equality.
The adapter
`sameCoreCompatible_hiddenCarryBlockValue_shift_scale_two_of_exportedHypotheses`
is the intended bridge from those exported booleans to the reusable
same-core proof path.
The row fields `shape13_k4_hyp_good_mode`,
`shape13_k4_hyp_same_core_compatible`,
`shape13_k4_hyp_base_prime_support_times_two_eq_k`,
`shape13_k4_hyp_scaled_quotient_remainders_lt_gap`,
`shape13_k4_hyp_scaled_block_remainders_lt_block_base`,
`shape13_k4_hyp_source_core_hidden_carry_block_value`,
`shape13_k4_scale_two_hypotheses_hold`, and
`shape13_k4_scale_two_failure_reason` make those checks searchable; the
current default shifted `N = 26` member satisfies them all, while the `N = 13`
source-core reference fails only `base_prime_support_times_two_ne_k`.
The summary fields `shape13_k4_scale_two_unnamed_candidate_members`,
`shape13_k4_scale_two_unnamed_candidate_tuples`, and
`shape13_k4_scale_two_candidate_mining_status` make the wider candidate search
explicit; the current status is
`no_unnamed_scale_two_ready_members_under_current_bounds`.

A wider manual probe found no additional members for bases `7,10,12,30` through
`max_n=2000`, or for bases `7,10,12,30,32,64,66,72,98,100` through
`max_n=1200`. The summary row therefore exports the stop condition
`do_not_add_new_shape13_k4_finite_package_until_wider_scan_emits_new_member`;
the scale-two-specific candidate probe found no unnamed scale-two-ready members
under those bounds, so the next empirical/open-boundary task is to mine wider
bounds or generalize the scale-two criterion beyond the base-`30` `13 -> 26`
pair.

The **Observability Instrument Compare** surface groups those rows by source
symmetry shape and then asks which base instruments hide, reveal, or shift that
same shape:

```bash
search-reptends observability-instrument-compare --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

Its `observability_source_symmetry_shape` rows use source signatures such as
`periodic_modulus=17;k=4;position_gap=4`, while
`observability_instrument_member` rows keep the concrete denominator, base,
lookahead, conflict, and Lean-readiness fields. This is still
empirical/open-boundary instrument comparison: it records where coefficient
information loss is hidden by carry-propagated block normalization, where a
future visible conflict could reveal it, and where the same source symmetry
appears in a shifted finite window. It does not close
`small_k_visibility_threshold`, close `carry_dfa_factorization`, or create a
registry, theorem-witness, or atlas-status promotion.

The focused **Shape17/K4 family classifier** expands the first emitted source
shape, `periodic_modulus=17;k=4;position_gap=4`, into the same-core ladder that
connects the shifted `N = 17` member with the `N = 34` and `N = 68`
Composite68-style members:

```bash
search-reptends observability-shape17-k4-family --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

Its `observability_shape17_k4_family_member` rows add
`same_core_multiplier`, `source_symmetry_family_role`,
`position_shift_from_canonical`, and `base_local_coefficient_scale`. Under the
default scan, `N = 17` appears as the shifted periodic-core member on
positions `[0,4]`, `N = 34` appears as the doubled Composite68-style member on
positions `[1,5]`, and the base-`10`/base-`30` `N = 68` rows remain the
Lean-ready Composite68-style anchors. This is empirical/open-boundary family
classification only; it does not close `small_k_visibility_threshold`, close
`carry_dfa_factorization`, or create a registry, theorem-witness, or
atlas-status promotion.

The **Next Source-Shape Family** selector skips the already classified
Shape17/K4 family and mines the next unresolved source symmetry shape:

```bash
search-reptends observability-next-source-shape-family --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

Under the default scan this selects
`periodic_modulus=187;k=188;position_gap=6`, with hidden carried-output
conflicts over bases `10`, `12`, and `30` at positions `[1,2]`. Its
`observability_next_source_shape_family_member` rows add
`same_core_multiplier`, `source_symmetry_family_role`,
`position_shift_from_canonical`, and `base_local_coefficient_scale` so the next
finite package or arithmetic criterion can be chosen from exported data. This
is empirical/open-boundary family mining only; the rows remain
`finite_only_hidden_conflict` until a named Lean package or criterion exists,
and they do not close `small_k_visibility_threshold`, close
`carry_dfa_factorization`, or create a registry, theorem-witness, or
atlas-status promotion.

The focused **Shape187/K188 same-position scaling classifier** expands that
next source shape into the multiplier ladder that currently separates a clean
arithmetic criterion candidate from the finite-package fallback:

```bash
search-reptends observability-shape187-k188-family --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

Under the default scan, the rows cover `N = 374 = 2*187` and
`N = 748 = 4*187` over bases `10`, `12`, and `30`. They expose the same-position
idempotent-remainder pattern `k = 188 = 187 + 1`, `k^2 ≡ k (mod N)`, conflict
positions `[1,2]`, coefficient ratio `188`, and hidden carried-output equality.
`BlockCoordinate.samePositionIdempotent_hiddenCarryBlockValue` is now the
generic Lean canonical-carry lemma for that shape. The exported-hypothesis
bridge `BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses`
proves the idempotent remainder condition from `N = multiplier * core`,
`k = core + 1`, and `multiplier | k`, then
`BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses.idempotent_remainder`
exposes that condition as a reusable projection, and
`BlockCoordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses`
reuses the canonical carried-output proof path.
`QRTour.FutureBase10N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two`,
`QRTour.FutureBase12N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two`,
`QRTour.FutureBase30N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two`
and
`QRTour.FutureBase30N748.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two`
instantiate it for the proof-covered base-`10`, base-`12`, and base-`30`
`N = 374` rows plus the base-`30` `N = 748` row.
Their bundled inputs are
`QRTour.FutureBase10N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses`,
`QRTour.FutureBase12N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses`,
`QRTour.FutureBase30N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses`
and
`QRTour.FutureBase30N748.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses`.
Rows expose this bridge explicitly with
`same_position_scaling_exported_hypothesis_record`,
`same_position_scaling_idempotent_remainder_projection`,
`same_position_scaling_exported_hypothesis_adapter`,
`same_position_scaling_intended_proof_path`, and
`same_position_scaling_named_hypothesis_instantiation`; candidate rows keep the
same intended proof path while leaving the named hypothesis instantiation empty.
Base-`10` `N = 374` now also pins the finite `8/2` record
`QRTour.FutureBase10N374.coordinate_stateAlignments_one_two_certifiedConflict_eight_two`.
Rows expose finite record coverage through
`same_position_scaling_named_finite_conflict_instantiation`.
The base-`30` namespaces pin the finite record theorems
`QRTour.FutureBase30N374.coordinate_stateAlignments_one_two_certifiedConflict_eight_one`
and
`QRTour.FutureBase30N748.coordinate_stateAlignments_one_two_certifiedConflict_eight_one`.
`QRTour.Shape187K188.base30_default_samePositionIdempotent_hiddenCarryBlockValue_one_two_pair`
packages those two canonical carried-output seeds together. Export rows use
`same_position_scaling_proved_by_arithmetic_criterion` only for those named
instantiations; the base-`10` and base-`12` `N = 748` rows remain
`same_position_scaling_criterion_candidate`. This remains finite/canonical
observability support and does not close `small_k_visibility_threshold`, close
`carry_dfa_factorization`, or create a registry, theorem-witness, or
atlas-status promotion.

The finite Lean response to that classifier now lands as a **finite Shape17/K4
shift witness** in `QRTour.Examples`:
`QRTour.FutureBase10N17.coordinate_stateAlignments_zero_four_certifiedConflict_eight_two`
proves the base-10 `N = 17` shifted `[0,4]` certified conflict,
`QRTour.FutureBase10N34.coordinate_stateAlignments_one_five_certifiedConflict_eight_two`
proves the base-10 `N = 34` doubled `[1,5]` certified conflict, and
`QRTour.Shape17K4.base10_core17_to_composite68_conflict_shift_exact` plus
`QRTour.Shape17K4.base10_core17_to_double34_conflict_shift_scaled` compare the
concrete finite rows. These theorems explain the observed `[0,4] -> [1,5]`
shift and the `N = 34` scale-two payload at the finite trace level only; they
are not a global same-core classification theorem and do not promote any open
claim boundary.

The arithmetic same-core criterion behind that finite witness is now named in
Lean as
`sameCoreCompatible_rawCoefficient_shift_scaled_one`,
`sameCoreCompatible_incomingCarry_shift_scaled_one`,
`sameCoreCompatible_canonicalCarryBlockValue_shift_scaled_one`, and
`sameCoreCompatible_hiddenCarryBlockValue_shift_scaled_one`. The criterion
characterizes the one-block shift as follows: if the base-supported factor
times a scale equals the shared remainder `k`, raw coefficients shift and
scale; incoming carries shift and scale exactly when the scaled quotient
remainder stays below `B-k`; and canonical carried-output values shift and
scale exactly when the scaled final block remainder stays below `B`. The local
iff helpers `nat_mul_div_eq_mul_div_iff_mul_mod_lt` and
`nat_mul_mod_eq_mul_mod_iff_mul_mod_lt` make those two remainder tests exact.
The
worked examples
`QRTour.Shape17K4.base10_n68_sameCore_scale_one_hiddenCarryBlockValue_shift`
and
`QRTour.Shape17K4.base10_n34_sameCore_scale_two_hiddenCarryBlockValue_shift`
instantiate that criterion for the base-`10` `17 -> 68` and `17 -> 34`
members, while
`QRTour.Shape17K4.base30_n68_sameCore_scale_one_hiddenCarryBlockValue_shift`
and
`QRTour.Shape17K4.base30_n34_sameCore_scale_two_hiddenCarryBlockValue_shift`
do the same for the base-`30` members. This is still finite same-core
arithmetic beneath the observability frontier, not a least-lookahead or global
factorization theorem.

The observability export rows now make this distinction searchable. The field
`same_core_shift_support_status` uses
`same_core_shift_proved_by_arithmetic_criterion` for the base-`10` and
base-`30` `N = 34` and `N = 68` Shape17/K4 members with named Lean criterion
instantiations,
`same_core_shift_criterion_candidate` for rows whose exported hypotheses fit
but lack an intentional named Lean hook, and `finite_only_hidden_conflict` for
hidden conflicts that are still finite records only. The accompanying
hypothesis fields record the base-supported-factor/scale equality, the scaled
quotient-remainder bound below `B-k`, and the scaled block-remainder bound
below `B`. These are search/export support for observability work, not a new
atlas claim, theorem-witness record, `small_k_visibility_threshold` closure, or
`carry_dfa_factorization` closure.

The Certificate-to-Lean fixture export narrows that workbench to source-pinned
Lean-ready obstruction records and emits JSON under schema
`certificate-lean-fixtures-v1`:

```bash
search-reptends visibility-certificate-lean-fixtures --max 1200 --bases 7,10,12,30 --blocks 8
```

V1 intentionally emits only the existing base-`10` and base-`30`
`Composite68` source hooks, pinned to theorem names already present in
[QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean)
and [THEOREM_GUIDE.md](/Users/mikepurvis/other/quadratic-residue-reptends/lean/THEOREM_GUIDE.md).
Each fixture also includes a `copyable_lean_stub` block for future finite
packages: the stub cites the pinned obstruction record and projects
`not_remainderToCoefficientFunctional` without making a new claim.
This is empirical/open-boundary certificate-to-Lean tooling, not a theorem
surface, registry promotion, theorem-witness record, or atlas claim.

The stub scaffold/lint export flattens those copyable blocks into JSON under
schema `certificate-lean-stubs-v1` and reports whether each generated stub is
internally consistent with its source fixture:

```bash
search-reptends visibility-certificate-lean-stubs --max 1200 --bases 7,10,12,30 --blocks 8
```

Use this as a handoff aid for future non-`Composite68` finite packages only
after adding an explicit source fixture mapping. It emits scaffolding and lint
status; it does not write Lean files or promote a claim.

The same command has an optional fixture-mapping lint mode for intentionally
staging a future mapping before adding it to the source-pinned fixture table.
For example:

```bash
search-reptends visibility-certificate-lean-stubs --max 120 --bases 30 --blocks 8 --candidate-base 30 --candidate-n 7 --namespace QRTour.FutureN7 --module-path lean/QRTour/Examples.lean
```

That mode emits schema `certificate-fixture-mapping-lint-v1`. A future package
should move from `scaffold_ready_pending_lean_source` to
`source_ready_existing_mapping` only after the Lean namespace, required theorem
names, and theorem-guide mentions exist.
The payload also includes a `source_pinning_recipe` block: a tiny candidate
mapping recipe giving a repeatable path from lint output to Lean theorem names.
For the first generated scaffold row, the base-`30` `N = 7` certificate
`(base, N, m, B, q, k, L, gap) = (30, 7, 1, 30, 4, 2, 2, 532)`, the recipe
points at the required theorem names, the copyable projection stub field
`proposed_mapping.copyable_lean_stub.code`, the theorem-guide mentions to add,
and the exact transition from `scaffold_ready_pending_lean_source` to
`source_ready_existing_mapping`. This is still empirical staging only: no
registry IDs, theorem-witness promotion, atlas status change, or Lean
theorem-surface claim is created by the recipe.
The shortcut mode selects that first scaffold-ready, non-source-ready candidate
without passing `--candidate-base` or `--candidate-n`:

```bash
search-reptends visibility-certificate-lean-stubs --max 120 --bases 7,10,12,30 --blocks 8 --first-scaffold-only
```

By default it derives a proposed namespace such as `QRTour.FutureBase30N7`,
`QRTour.FutureBase30N14`, `QRTour.FutureBase30N28`,
`QRTour.FutureBase12N10`, `QRTour.FutureBase10N102`,
`QRTour.FutureBase7N5`, `QRTour.FutureBase12N5`,
`QRTour.FutureBase30N34`, `QRTour.FutureBase7N93`, or
`QRTour.FutureBase10N39`, `QRTour.FutureBase10N78`, or
`QRTour.FutureBase10N96`, `QRTour.FutureBase12N35`, or
`QRTour.FutureBase12N31`; pass
`--namespace QRTour.FutureN7` with `--first-scaffold-only` when intentionally
staging a shorter package namespace.
The first generated `lean_package_plan` checklist selected
`base30_n7_m1_blocks8_L2`; that finite package has now landed as
`QRTour.FutureBase30N7` with
`QRTour.FutureBase30N7.coordinate_stateAlignments_zero_three_certifiedConflict_eight_two`,
`QRTour.FutureBase30N7.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_two`,
and
`QRTour.FutureBase30N7.base30_n7_m1_blocks8_L2_not_remainderToCoefficientFunctional`.
It records the same scaffold tuple
`(base, N, m, B, q, k, L, gap) = (30, 7, 1, 30, 4, 2, 2, 532)`, with
remainder state `1`, positions `[0, 3]`, raw coefficients `[4, 32]`, carry
states `[0, 2]`, and carried block values `[4, 4]`. This remains a finite
empirical/open-boundary obstruction hook only: it creates no registry IDs,
theorem-witness status, atlas status, `small_k_visibility_threshold`, or
`carry_dfa_factorization` promotion.

After `QRTour.FutureBase30N7` became source-ready, the shortcut advanced to
`base30_n14_m1_blocks8_L2`; that finite package has now landed as
`QRTour.FutureBase30N14` with
`QRTour.FutureBase30N14.coordinate_stateAlignments_one_four_certifiedConflict_eight_two`,
`QRTour.FutureBase30N14.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_two`,
and
`QRTour.FutureBase30N14.base30_n14_m1_blocks8_L2_not_remainderToCoefficientFunctional`.
It records
`(base, N, m, B, q, k, L, gap) = (30, 14, 1, 30, 2, 2, 2, 716)`, with
remainder state `2`, positions `[1, 4]`, raw coefficients `[4, 32]`, carry
states `[0, 2]`, and carried block values `[4, 4]`. This is the same finite
empirical/open-boundary obstruction hook status as `N = 7`; after those source
and guide mentions exist, `--first-scaffold-only` advances again to the next
scaffold-ready, non-source-ready conflict candidate.

After `QRTour.FutureBase30N14` became source-ready, the shortcut advanced to
`base30_n28_m1_blocks8_L2`; that finite package has now landed as
`QRTour.FutureBase30N28` with
`QRTour.FutureBase30N28.coordinate_stateAlignments_two_five_certifiedConflict_eight_two`,
`QRTour.FutureBase30N28.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_two`,
and
`QRTour.FutureBase30N28.base30_n28_m1_blocks8_L2_not_remainderToCoefficientFunctional`.
It records
`(base, N, m, B, q, k, L, gap) = (30, 28, 1, 30, 1, 2, 2, 808)`, with
remainder state `4`, positions `[2, 5]`, raw coefficients `[4, 32]`, carry
states `[0, 2]`, and carried block values `[4, 4]`. This is again finite
empirical/open-boundary obstruction packaging only; after those source and
guide mentions exist, the shortcut advances to the next scaffold-ready,
non-source-ready conflict candidate.

After `QRTour.FutureBase30N28` became source-ready, the shortcut advanced to
`base12_n10_m1_blocks8_L3`; that finite package has now landed as
`QRTour.FutureBase12N10` with
`QRTour.FutureBase12N10.coordinate_stateAlignments_one_five_certifiedConflict_eight_three`,
`QRTour.FutureBase12N10.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_three`,
and
`QRTour.FutureBase12N10.base12_n10_m1_blocks8_L3_not_remainderToCoefficientFunctional`.
It records
`(base, N, m, B, q, k, L, gap) = (12, 10, 1, 12, 1, 2, 3, 896)`, with
remainder state `2`, positions `[1, 5]`, raw coefficients `[2, 32]`, carry
states `[0, 6]`, and carried block values `[2, 2]`. This stays finite
empirical/open-boundary obstruction packaging only; after those source and
guide mentions exist, the shortcut advances to the next scaffold-ready,
non-source-ready conflict candidate.

After `QRTour.FutureBase12N10` became source-ready, the shortcut advanced to
`base10_n102_m4_blocks8_L1`; that finite package has now landed as
`QRTour.FutureBase10N102` with
`QRTour.FutureBase10N102.coordinate_stateAlignments_one_five_certifiedConflict_eight_one`,
`QRTour.FutureBase10N102.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase10N102.base10_n102_m4_blocks8_L1_not_remainderToCoefficientFunctional`.
It records
`(base, N, m, B, q, k, L, gap) = (10, 102, 4, 10000, 98, 4, 1, 7472)`,
with remainder state `4`, positions `[1, 5]`, raw coefficients `[392, 100352]`,
carry states `[0, 40]`, and carried block values `[392, 392]`. This stays
finite empirical/open-boundary obstruction packaging only; after those source
and guide mentions exist, the shortcut advances to the next scaffold-ready,
non-source-ready conflict candidate.

After `QRTour.FutureBase10N102` became source-ready, the shortcut advanced to
`base7_n5_m1_blocks8_L5`; that finite package has now landed as
`QRTour.FutureBase7N5` with
`QRTour.FutureBase7N5.coordinate_stateAlignments_zero_four_certifiedConflict_eight_five`,
`QRTour.FutureBase7N5.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_five`,
and
`QRTour.FutureBase7N5.base7_n5_m1_blocks8_L5_not_remainderToCoefficientFunctional`.
It records
`(base, N, m, B, q, k, L, gap) = (7, 5, 1, 7, 1, 2, 5, 15084)`, with
remainder state `1`, positions `[0, 4]`, raw coefficients `[1, 16]`, carry
states `[0, 6]`, and carried block values `[1, 1]`. This stays finite
empirical/open-boundary obstruction packaging only; after those source and
guide mentions exist, the shortcut advances to the next scaffold-ready,
non-source-ready conflict candidate.

After `QRTour.FutureBase7N5` became source-ready, the shortcut advanced to
`base12_n5_m1_blocks8_L4`; that finite package has now landed as
`QRTour.FutureBase12N5` with
`QRTour.FutureBase12N5.coordinate_stateAlignments_zero_four_certifiedConflict_eight_four`,
`QRTour.FutureBase12N5.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_four`,
and
`QRTour.FutureBase12N5.base12_n5_m1_blocks8_L4_not_remainderToCoefficientFunctional`.
It records
`(base, N, m, B, q, k, L, gap) = (12, 5, 1, 12, 2, 2, 4, 17408)`, with
remainder state `1`, positions `[0, 4]`, raw coefficients `[2, 32]`, carry
states `[0, 6]`, and carried block values `[2, 2]`. This stays finite
empirical/open-boundary obstruction packaging only; after those source and
guide mentions exist, the shortcut advances to the next scaffold-ready,
non-source-ready conflict candidate.

After `QRTour.FutureBase12N5` became source-ready, the shortcut advanced to
`base30_n34_m3_blocks8_L1`; that finite package has now landed as
`QRTour.FutureBase30N34` with
`QRTour.FutureBase30N34.coordinate_stateAlignments_one_five_certifiedConflict_eight_one`,
`QRTour.FutureBase30N34.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase30N34.base30_n34_m3_blocks8_L1_not_remainderToCoefficientFunctional`.
It records
`(base, N, m, B, q, k, L, gap) = (30, 34, 3, 27000, 794, 4, 1, 20416)`,
with remainder state `4`, positions `[1, 5]`, raw coefficients `[3176, 813056]`,
carry states `[0, 120]`, and carried block values `[3176, 3176]`. This stays
finite empirical/open-boundary obstruction packaging only; after those source
and guide mentions exist, the shortcut advances to the next scaffold-ready,
non-source-ready conflict candidate.

After `QRTour.FutureBase30N34` became source-ready, the shortcut advanced to
`base7_n93_m6_blocks8_L1`; that finite package has now landed as
`QRTour.FutureBase7N93` with
`QRTour.FutureBase7N93.coordinate_stateAlignments_zero_five_certifiedConflict_eight_one`,
`QRTour.FutureBase7N93.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase7N93.base7_n93_m6_blocks8_L1_not_remainderToCoefficientFunctional`.
It records
`(base, N, m, B, q, k, L, gap) = (7, 93, 6, 117649, 1265, 4, 1, 39505)`,
with remainder state `1`, positions `[0, 5]`, raw coefficients `[1265, 1295360]`,
carry states `[0, 44]`, and carried block values `[1265, 1265]`. This stays
finite empirical/open-boundary obstruction packaging only; after those source
and guide mentions exist, the shortcut advances to the next scaffold-ready,
non-source-ready conflict candidate.

After `QRTour.FutureBase7N93` became source-ready, the shortcut advanced to
`base10_n39_m5_blocks8_L1`; that finite package has now landed as
`QRTour.FutureBase10N39` with
`QRTour.FutureBase10N39.coordinate_stateAlignments_zero_six_certifiedConflict_eight_one`,
`QRTour.FutureBase10N39.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase10N39.base10_n39_m5_blocks8_L1_not_remainderToCoefficientFunctional`.
It records
`(base, N, m, B, q, k, L, gap) = (10, 39, 5, 100000, 2564, 4, 1, 65696)`,
with remainder state `1`, positions `[0, 6]`, raw coefficients `[2564, 10502144]`,
carry states `[0, 420]`, and carried block values `[2564, 2564]`. This stays
finite empirical/open-boundary obstruction packaging only; after those source
and guide mentions exist, the shortcut advances to the next scaffold-ready,
non-source-ready conflict candidate.

After `QRTour.FutureBase10N39` became source-ready, the shortcut advanced to
`base10_n78_m5_blocks8_L1`; that finite package has now landed as
`QRTour.FutureBase10N78` with
`QRTour.FutureBase10N78.coordinate_stateAlignments_one_seven_certifiedConflict_eight_one`,
`QRTour.FutureBase10N78.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase10N78.base10_n78_m5_blocks8_L1_not_remainderToCoefficientFunctional`.
It records
`(base, N, m, B, q, k, L, gap) = (10, 78, 5, 100000, 1282, 4, 1, 82848)`,
with remainder state `4`, positions `[1, 7]`, raw coefficients `[5128, 21004288]`,
carry states `[0, 840]`, and carried block values `[5128, 5128]`. This stays
finite empirical/open-boundary obstruction packaging only; after those source
and guide mentions exist, the shortcut advances to the next scaffold-ready,
non-source-ready conflict candidate.

After `QRTour.FutureBase10N78` became source-ready, the shortcut advanced to
`base10_n96_m2_blocks8_L3`; that finite package has now landed as
`QRTour.FutureBase10N96` with
`QRTour.FutureBase10N96.coordinate_stateAlignments_three_four_certifiedConflict_eight_three`,
`QRTour.FutureBase10N96.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_three`,
and
`QRTour.FutureBase10N96.base10_n96_m2_blocks8_L3_not_remainderToCoefficientFunctional`.
It records
`(base, N, m, B, q, k, L, gap) = (10, 96, 2, 100, 1, 4, 3, 377024)`,
with remainder state `64`, positions `[3, 4]`, raw coefficients `[64, 256]`,
carry states `[2, 10]`, and carried block values `[66, 66]`. This stays finite
empirical/open-boundary obstruction packaging only; after those source and
guide mentions exist, the shortcut advances to the next scaffold-ready,
non-source-ready conflict candidate.

After `QRTour.FutureBase10N96` became source-ready, the shortcut advanced to
`base12_n35_m2_blocks8_L3`; that finite package has now landed as
`QRTour.FutureBase12N35` with
`QRTour.FutureBase12N35.coordinate_stateAlignments_zero_six_certifiedConflict_eight_three`,
`QRTour.FutureBase12N35.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_three`,
and
`QRTour.FutureBase12N35.base12_n35_m2_blocks8_L3_not_remainderToCoefficientFunctional`.
It records
`(base, N, m, B, q, k, L, gap) = (12, 35, 2, 144, 4, 4, 3, 1740800)`,
with remainder state `1`, positions `[0, 6]`, raw coefficients `[4, 16384]`,
carry states `[0, 468]`, and carried block values `[4, 4]`. This stays finite
empirical/open-boundary obstruction packaging only; after those source and
guide mentions exist, the shortcut advances to the next scaffold-ready,
non-source-ready conflict candidate.

After `QRTour.FutureBase12N35` became source-ready, the shortcut advanced to
`base12_n31_m6_blocks8_L1`; that finite package has now landed as
`QRTour.FutureBase12N31` with
`QRTour.FutureBase12N31.coordinate_stateAlignments_zero_five_certifiedConflict_eight_one`,
`QRTour.FutureBase12N31.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase12N31.base12_n31_m6_blocks8_L1_not_remainderToCoefficientFunctional`.
It records
`(base, N, m, B, q, k, L, gap) = (12, 31, 6, 2985984, 96322, 2, 1, 2215424)`,
with remainder state `1`, positions `[0, 5]`, raw coefficients
`[96322, 3082304]`, carry states `[0, 2]`, and carried block values
`[96322, 96322]`. This stays finite empirical/open-boundary obstruction
packaging only; after those source and guide mentions exist, the shortcut
advances to the next scaffold-ready, non-source-ready conflict candidate.

The Lean worked-example hook
`QRTour.Composite68.coordinate_not_coefficientFunctional_eight_one` packages
the same finite obstruction on the certified `8/1` window. Its companion
entry points record `q = 147`, `k = 4`, lookahead gap numerator `6208`, the
shared remainder state `4`, raw coefficients `588` and `150528`, carry states
`0` and `60`, and the hidden carried block value `588`. This remains a finite
refutation hook beneath the open boundary, not a new atlas claim.

The base-`30` member is now packaged as
`QRTour.Composite68Base30.coordinate_not_coefficientFunctional_eight_one`.
It records `(base, N, m, B, q, k, L, gap) = (30, 68, 3, 27000, 397, 4, 1, 10208)`,
the same repeated remainder state `4` at positions `1` and `5`, raw coefficients `1588` and `406528`, carry states `0` and `60`, and hidden carried block value `1588`. The generic Lean helper
`BlockCoordinate.not_coefficientFunctional_one_five_of_remainderK_eq_four`
captures the shared finite obstruction pattern under `k = 4` and `q > 0`;
`BlockCoordinate.stateAlignments_remainderIn_one_eq_five_of_modulus_eq_sixty_eight`
derives the repeated observed remainder state from `modulus = 68` and `k = 4`;
and `BlockCoordinate.not_coefficientFunctional_one_five_of_modulus_eq_sixty_eight`
combines those two ingredients. The stronger congruence wrapper
`BlockCoordinate.remainderK_eq_four_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
first derives `k = 4` from `modulus = 68` and `B ≡ 4 (mod 68)`, while
`BlockCoordinate.not_coefficientFunctional_one_five_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
then calls the finite obstruction theorem. These are still finite-window
refutation lemmas, not global factorization results.

Lean now also proves the arithmetic carry-state side of the same shape.
`BlockCoordinate.incomingCarry_one_eq_zero_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
and
`BlockCoordinate.incomingCarry_five_eq_sixty_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
show that the canonical incoming carries at positions `1` and `5` are exactly
`0` and `60` throughout the good `N = 68`, `B ≡ 4 (mod 68)` coordinate family.
`BlockCoordinate.incomingCarry_hiddenOutput_one_five_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
then proves the hidden-output equality: adding those canonical incoming carries
and reducing modulo `B` emits the same block at positions `1` and `5`.
The worked examples expose this as
`QRTour.Composite68.coordinate_incomingCarry_hiddenOutput_one_five` and
`QRTour.Composite68Base30.coordinate_incomingCarry_hiddenOutput_one_five`.
They now also expose the certified finite-trace bridge through
`QRTour.Composite68.coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry`
and
`QRTour.Composite68Base30.coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry`:
on the certified `8/1` worked windows, the `stateAlignments` carry states at
positions `1` and `5` equal the canonical `incomingCarry 1` and
`incomingCarry 5` values. The reusable fixed-window theorem
`BlockCoordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
now proves that the `8/1` finite trace itself supplies the `(0, 60)` carry
certificate throughout the good `N = 68`, `B ≡ 4 (mod 68)` coordinate family.
The sharper carry-state-only theorem
`BlockCoordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_zero_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
shows that the same finite carry states are already forced on the `8/0` trace;
`QRTour.Composite68.coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry_eight_zero`
and
`QRTour.Composite68Base30.coordinate_stateAlignments_carryIn_one_five_eq_incomingCarry_eight_zero`
instantiate that zero-lookahead carry certificate on the current worked
examples. This weakens the suffix requirement for the carry-state layer only:
positive lookahead is still used for the certified output-agreement obstruction
window.
The new suffix-bound arithmetic hooks
`composite68_suffixCarry_five_eq_sixty_of_tailCarry_le_nine_hundred_sixty_three`
and
`composite68_suffixCarry_one_eq_zero_of_tailCarry_le_nine_hundred_sixty_three`
now sit behind a generic finite-carry upper-bound layer:
`BlockCoordinate.incomingCarry_step_recurrence`,
`BlockCoordinate.traceRawWord_carryIn_le_incomingCarry`,
`BlockCoordinate.visibleCarryTrace_carryIn_le_incomingCarry`, and
`BlockCoordinate.stateAlignments_carryIn_le_incomingCarry`. Together with
`BlockCoordinate.incomingCarry_seven_eq_nine_hundred_sixty_three_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`,
they prove that every finite carry entering the `4^7` block is at most `963`.
The universal suffix bound is now Lean-proved for the `N = 68`,
`B ≡ 4 (mod 68)` family, and
`BlockCoordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_eight_any_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
packages the result as an all-lookahead eight-block carry-state theorem.
The next Lean hook is now an obstruction-first finite visibility theorem:
`BlockCoordinate.stateAlignments_one_five_hiddenCoefficientConflict_eight_any_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
packages, for every good `8/L` window in that family, equal observed
`remainderIn` at positions `1` and `5`, unequal raw coefficients, canonical
incoming carries, equal hidden carried block output, and nonfunctional
remainder-to-coefficient mapping. The certified wrapper
`BlockCoordinate.stateAlignments_one_five_certifiedVisibilityObstruction_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
adds a `lookaheadCertificateHolds 8 L` hypothesis so those carried block values
are also the emitted/remainder block values at the two positions. The worked
example names
`QRTour.Composite68.coordinate_stateAlignments_one_five_hiddenCoefficientConflict_eight_one`,
`QRTour.Composite68.coordinate_stateAlignments_one_five_certifiedVisibilityObstruction_eight_one`,
`QRTour.Composite68Base30.coordinate_stateAlignments_one_five_hiddenCoefficientConflict_eight_one`,
and
`QRTour.Composite68Base30.coordinate_stateAlignments_one_five_certifiedVisibilityObstruction_eight_one`
specialize the generic theorem to the certified base-`10` and base-`30` `8/1`
windows without promoting a new atlas claim.
Lean now also proves the first exact one-lookahead certificate threshold for
that same family. The support lemma
`BlockCoordinate.truncatedVisiblePrefixRemainder_one_eq_rawCoefficient_mod_blockBase`
reduces the `8/1` suffix gap to the next raw coefficient modulo `B`, and
`BlockCoordinate.lookaheadCertificateHolds_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_ge_seventy_five`
proves that every good `N = 68`, `B ≡ 4 (mod 68)` coordinate with `q ≥ 75`
satisfies `lookaheadCertificateHolds 8 1`. The boundary theorem
`BlockCoordinate.not_lookaheadCertificateHolds_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_eq_seventy_four`
identifies the first failed one-lookahead quotient, `q = 74` and
`B = 5036`. Lean now also proves the next positive fixed-window lookahead
staircase for the same family:
`BlockCoordinate.truncatedVisiblePrefixRemainder_two_eq_rawCoefficient_suffix_mod_blockBase_sq`
and
`BlockCoordinate.truncatedVisiblePrefixRemainder_three_eq_rawCoefficient_suffix_mod_blockBase_cu`
expose the two- and three-block suffix arithmetic, while
`BlockCoordinate.lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_ge_three`
proves `q ≥ 3` implies `lookaheadCertificateHolds 8 2`, and
`BlockCoordinate.lookaheadCertificateHolds_eight_three_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
proves every good coordinate in the family satisfies
`lookaheadCertificateHolds 8 3`. The worked-example hooks
`QRTour.Composite68.coordinate_lookaheadCertificate_eight_two`,
`QRTour.Composite68.coordinate_lookaheadCertificate_eight_three`,
`QRTour.Composite68Base30.coordinate_lookaheadCertificate_eight_two`, and
`QRTour.Composite68Base30.coordinate_lookaheadCertificate_eight_three`
instantiate those slices for the base-`10` and base-`30` obstruction examples.
The negative side is now Lean-proved too:
`BlockCoordinate.not_lookaheadCertificateHolds_eight_zero_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
rules out `8/0` throughout the family,
`BlockCoordinate.not_lookaheadCertificateHolds_eight_one_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_le_seventy_four`
combines with the positive threshold as
`BlockCoordinate.lookaheadCertificateHolds_eight_one_iff_quotientQ_ge_seventy_five_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`,
and
`BlockCoordinate.not_lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_eq_one`
with
`BlockCoordinate.not_lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_eq_two`
give the exact small-quotient obstruction points. The point failures have
`8/2` gap numerators `1088` at `q = 1` and `432` at `q = 2`; together with
`BlockCoordinate.not_lookaheadCertificateHolds_eight_two_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four_and_quotientQ_le_two`
and
`BlockCoordinate.lookaheadCertificateHolds_eight_two_iff_quotientQ_ge_three_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`,
Lean now classifies the fixed `8/L` certificate staircase for `L = 0, 1, 2, 3`:
`8/0` never certifies, `8/1` certifies exactly when `q ≥ 75`, `8/2` exactly
when `q ≥ 3`, and `8/3` for every good coordinate in the family. This is a
fixed-window minimal-lookahead classification only. The generic predicate
`BlockCoordinate.isMinimalLookaheadCertificate` records that a certificate
holds at a lookahead and fails at every smaller lookahead, and the selector
theorem
`BlockCoordinate.minimalLookaheadCertificate_eight_selector_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
packages the three cases: `q ≥ 75 -> L = 1`, `3 ≤ q < 75 -> L = 2`, and
`q = 1 or q = 2 -> L = 3`. This is not a global
`small_k_visibility_threshold` theorem, not `carry_dfa_factorization`, and not
a new atlas claim.
Lean also connects that selector back to the obstruction wrapper:
`BlockCoordinate.StateAlignmentCertifiedConflict` is the reusable record-shaped
payload for certified hidden coefficient conflicts between two indexed
state-alignment rows. The specialized predicate
`BlockCoordinate.stateAlignmentsOneFiveCertifiedVisibilityObstruction` names the
positions-`1/5`, eight-block instance of that payload,
the convenience projections
`BlockCoordinate.StateAlignmentCertifiedConflict.not_remainderToCoefficientFunctional`,
`BlockCoordinate.StateAlignmentCertifiedConflict.not_remainderToCoefficientFactorsThrough`,
`BlockCoordinate.StateAlignmentCertifiedConflict.carriedOutput_eq`, and
`BlockCoordinate.StateAlignmentCertifiedConflict.output_agreement` expose
list nonfunctionality, the generic factor-through obstruction, hidden
carried-output equality, and certified output agreement without manual record
unpacking. The generic Lean predicate `FactorsThrough`, helper
`FactorsThrough.eq_of_obs_eq`, and obstruction lemma
`not_factorsThrough_of_collision` keep this in kernel/refinement language:
equal observations plus unequal raw coefficient values refute factor-through
observability. `List.functionalOnFst_iff_factorsThrough_memberSubtype` is the
finite compatibility bridge: it proves the older `List.FunctionalOnFst` row
surface is equivalent to `FactorsThrough` on the finite member subtype, using
only first-coordinate observations that actually occur in the list.
`BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_iff_factorsThrough_memberSubtype`
specializes that equivalence to the full finite `stateAlignments` window mapped
as `(remainderIn, coefficient)`.
`BlockCoordinate.stateAlignments_not_remainderToCoefficientFactorsThrough_of_not_remainderToCoefficientFunctional`
is the companion negative corollary: nonfunctionality of that concrete window
directly yields `¬ FactorsThrough` for the full finite readout. The
worked examples
`QRTour.Composite68.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_fullWindow_eight_one`
and
`QRTour.Composite68Base30.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_fullWindow_eight_one`
instantiate that full-window path on the certified base-`10` and base-`30`
`Composite68` windows, separate from the two-point record accessor. The
observability-boundary lens in
[OBSERVABILITY_BOUNDARY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/OBSERVABILITY_BOUNDARY.md)
uses this record as the finite Lean hook for coefficient information loss
across carry-propagated block normalization: the same observed remainder state
can coexist with unequal raw coefficients while the carried output agrees. That
is a working research frame, not a registry claim, theorem-witness promotion,
atlas-status change, `small_k_visibility_threshold`, or
`carry_dfa_factorization` closure.
`BlockCoordinate.stateAlignments_one_five_certifiedConflict_eight_of_lookaheadCertificate_and_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
is the compact cross-base family wrapper returning the record directly,
`BlockCoordinate.stateAlignmentsOneFiveCertifiedVisibilityObstruction_of_lookaheadCertificate`
turns any certified `8/L` window in the family into that payload, and
`BlockCoordinate.minimalLookaheadCertificate_eight_selector_certifiedVisibilityObstruction_of_modulus_eq_sixty_eight_and_blockBase_mod_eq_four`
states that the selected minimal certified lookahead still exposes the certified
hidden coefficient conflict. This is still fixed-window obstruction support,
not a global visibility or factorization result.
The worked-example wrappers
`QRTour.Composite68.coordinate_stateAlignments_one_five_certifiedConflict_eight_one`
and
`QRTour.Composite68Base30.coordinate_stateAlignments_one_five_certifiedConflict_eight_one`
share that compact record payload explicitly on the base-`10` and base-`30`
certified `8/1` windows. The selector wrappers
`QRTour.Composite68.coordinate_minimalLookaheadCertificate_selector_certifiedVisibilityObstruction_eight_one`
and
`QRTour.Composite68Base30.coordinate_minimalLookaheadCertificate_selector_certifiedVisibilityObstruction_eight_one`
specialize that selector-certified theorem to the concrete base-`10` and
base-`30` first branches: the minimal certified lookahead is `1`, and that
minimal window still exposes the certified hidden coefficient conflict.
The older reusable bridge
`BlockCoordinate.stateAlignments_carryIn_one_five_eq_incomingCarry_of_carry_states_zero_sixty`
remains available for arbitrary finite state-alignment windows containing
positions `1` and `5` whose finite carry states are externally certified as
`0` and `60`. The remaining open boundary is still output agreement and broader
factorization beyond the stated certificate: this proves finite carry-state
preservation and the finite hidden-coefficient obstruction for all extra
lookahead in the family, not `small_k_visibility_threshold` or
`carry_dfa_factorization`. The congruence-family search surface continues to
report certified positive-lookahead and hidden-output shape rows empirically.

The **Instrument Atlas** broadens that probe into base-level profiles and
working-axiom pressure rows:

```bash
search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

The guiding lens is: the reptend is the observed trace; the remainder orbit is
the source; the finite carry window is the instrument. In standard terms, the
trace lens aligns the remainder orbit, raw coefficient stream, and
carry-propagated block normalization so the displayed blocks can be read as an
observation of the orbit through positional notation.

It emits three row groups:

- `case_summary`: the block coordinate, stripped periodic modulus, period,
  lookahead, output agreement, and finite-window factorization regime.
- `trace_step`: one row per visible block, including the cycle index,
  remainder input/output, raw coefficient, carry input/output, displayed block,
  and a visibility event such as `carry_free_raw`,
  `incoming_carry_before_overflow`, or `local_overflow`.
- `state_map_summary`: the observed finite-window functional/injective status
  and signatures in both the remainder-to-carry and carry-to-remainder
  directions.

This lens is intentionally experimental. It is a way to inspect the finite
carry window over the closed remainder orbit, not a new theorem claim and not a
replacement for the open `carry_dfa_factorization` boundary.

## Small Examples

### `N = 21`

In the small-residue block coordinate `10^6 = 47619 * 21 + 1`, the raw coefficients are constant and already below the block base.

- raw coefficients: constant `47619`
- reachable carry states: only `(0,)`
- reachable remainder states in the same block coordinate: only `(1,)`
- interpretation: this is the trivial observed state-relabeling case

This is the cleanest example where the carry layer disappears completely on the
visible window. It is useful in Track 17 precisely because it is the only
canonical case where a simple one-state relabeling survives the full observed
comparison.

### `N = 97`

This is the best small example where the carry-state view adds real information.

- raw coefficients begin as `1, 3, 9, 27, 81, 243, ...`
- displayed blocks begin as `01, 03, 09, 27, 83, 50, ...`
- the first nonzero carry position is block `4`

The key point is that the raw coefficient `81` is still below `100`, but that block becomes `83` because a carry of `2` arrives from the less significant side. A raw block table alone does not make that dependency explicit; the carry-state graph does.

### `N = 89`

This is the clean hidden-obstruction case.

- the aligned finite window is bijective in both directions
- the selected profile shows no visible compression targets
- the observed carry graph and remainder graph still have different sizes

So the failure is real, but it does not live in the preimage fibers. It only
appears once the graph layer is compared to the aligned window.

### `N = 996`

This is the best example where the carry model and the composite model meet.

- the stripped periodic core is `249`
- the actual denominator still has the bridge-style coordinate `10^3 = 1 * 996 + 4`
- the carry states are nontrivial, but the displayed blocks still match the long-division output exactly through `carry_window_example(...)`

This is why `996` is a useful case study: preperiod, composite CRT structure, and carry normalization all appear in one example, while the state-level relation still looks like a quotient candidate rather than a relabeling.

## Track 17 Factorization Ladder

Track 17 now separates four candidate levels instead of one vague open claim.

1. Finite-window word agreement.
   This is implemented: on the visible window, the carry transducer and the long-division DFA emit the same displayed block word.
2. Observed state relabeling.
   This asks whether the observed carry states and remainder states are just two names for the same finite-state run.
3. Observed quotient or lift candidates.
   This asks whether the aligned window defines a functional map from remainder states to carry states, from carry states to remainder states, or both.
4. Canonical global factorization.
   This is still open: a base- and modulus-uniform theorem that long division factors canonically into orbit plus carry.

The repo now makes these distinctions explicitly through
[transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py):

- `21` is the trivial `state_relabeling` case.
- `97` and `996` are `quotient_candidate_only` cases:
  the observed remainder-to-carry map is functional, but the carry-to-remainder
  map is not, so a simple state relabeling already fails on the canonical window.

The new preimage-fiber profile (state-merging atlas) is the finite-window view
of that asymmetry. It does not claim a theorem. It now separates two exact
finite-window obstruction types:

- visible preimage compression: the collapse is already visible in the target fibers
- hidden graph obstruction: the aligned window stays bijective, but the graph layer still blocks relabeling

The newest same-core family rows add a further empirical signal: those hidden
and visible phases need not be monotone under base-supported deformation. In
families like `17 / 34 / 68 / 85 / 136`, visible compression can appear and
then re-hide back into hidden graph obstruction on later same-core members.

At the larger bounded search surface `N <= 2000`, the current classifier shows
two especially sharp empirical correlates:

- `visible_without_hidden` families are one-way visible on the selected window
- `visible_first` families re-hide later in the same-core path

That is still a dataset statement, not a theorem, but it is now exported
directly by `same_core_obstruction_correlate_rows(...)`.

## Decision Criteria

Track 17 is now decision-complete in the following sense.

## Flagship Candidate Statements

Before further search or Lean promotion, Track 17 now commits to one exact
positive candidate and one exact obstruction candidate.

`Positive candidate (restricted remainder-to-carry factorization)`:

For a fixed coprime block coordinate `C`, assume that every finite aligned
carry/remainder window for `C` satisfies all three of the currently exposed
finite criteria:

- finite-word output agreement,
- `remainderToCarryFunctional`,
- remainder-to-carry transition compatibility.

Then there exists a unique orbit-level map `φ_C` from the reachable remainder
states of the long-division DFA to the reachable carry states of the carry
transducer such that:

- `φ_C` sends each observed `remainderIn` state to the corresponding
  `carryIn` state,
- `φ_C` intertwines the remainder update with the carry update driven by the
  raw coefficient stream `qk^j`,
- the carry transducer started from `φ_C(r_0)` emits exactly the long-division
  block word on the full orbit.

This is the first positive theorem candidate for `carry_dfa_factorization`.
It is intentionally coordinate-level; it does not yet assert a base- and
modulus-uniform global factorization theorem.

Lean packages this modest surface in
[QRTour/Factorization.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Factorization.lean)
as factorization-frontier support: restricted finite-window morphisms for `21`
and `97`, plus the `996` same-core reverse obstruction, without promoting a
global factorization theorem.

`Obstruction candidate (core/output insufficiency)`:

No canonical factorization theorem for all coprime moduli can depend only on
stripped periodic core, visible output agreement, and the exact same-core shift
data already proved in Lean. In particular, in base `10` the same-core family
with core `249` has a member `249` with an observed `state_relabeling` window
at `m = 6`, while the same-core members `498` and `996` remain
`quotient_candidate_only` on the tested selector surface. Therefore any valid
global theorem must use finer arithmetic than periodic core plus visible-word
data.

The `17 -> 34` selector-family shift is the secondary obstruction family: small
multiple moves can preserve and enlarge relabeling windows rather than merely
shifting them monotonically.

What would count as a theorem:

- a proof of the positive candidate above, or
- a stronger proof that the machines are actually state-relabelings in a
  uniform class of examples.

What would count as a refutation:

- a bounded example where finite-window word agreement holds but even the
  observed remainder-to-carry quotient candidate fails, or
- a proof of the obstruction candidate above, or
- a family where any proposed state-level factorization notion changes form
  unpredictably under harmless coordinate changes.

What would count as a weaker replacement claim:

- finite-window word agreement plus an observed quotient-from-remainder-to-carry
  framework, without asserting a unique or canonical global factorization.

## Bounded Search Surface

The repo now exposes a bounded Track 17 search via:

`search-reptends carry-factorization --max 500 --blocks 8`

This exports, for each tested denominator:

- whether finite-window outputs match,
- whether a simple observed state relabeling candidate holds,
- whether the observed remainder-to-carry quotient candidate holds,
- whether the observed carry-to-remainder lift candidate holds,
- whether the example is already a counterexample to naive state relabeling.

The canonical search outcomes are:

- `21`: trivial state relabeling
- `97`: counterexample to state relabeling, but positive evidence for the quotient candidate
- `996`: the same quotient-only regime in a composite/preperiod setting

## Selector Signal

The selector itself now exposes signal, not just a chosen `m`.

For fixed `N`, the function `carry_factorization_selector_profile(...)` scans
candidate block widths and records the regime transition signature.

Canonical profiles:

- `21` in base `10`: `finite_word_only -> state_relabeling -> finite_word_only`
- `249` in base `10`: `quotient_candidate_only -> state_relabeling -> quotient_candidate_only`
- `996` in base `10`: `quotient_candidate_only` only

The repo now exposes direct family comparison objects through
`compare_carry_selector_profiles(...)`.

Current high-signal family comparisons:

- same-core loss: `249 -> 996` in base `10`
  - `249` has an isolated relabeling window at `m = 6`
  - same-core `996` loses that window entirely
- multiple-family shift: `17 -> 34` in base `10`
  - `17` has relabeling at `m = 5`
  - `34` keeps `m = 5` and gains an extra relabeling window at `m = 7`

This matters for two reasons:

- state-relabeling windows can be isolated and nonmonotone in `m`,
- the same periodic core does not determine the selector profile, since `249`
  and `996` have different Track 17 signatures,
- small multiple families can preserve, shift, enlarge, or destroy relabeling
  windows rather than behaving monotonically.

The new search surface

`search-reptends carry-factorization-selector --max 300 --blocks 8`

exports these profiles directly, so the selector can be studied as a family
object rather than only as a hidden optimization heuristic.

Two additional search surfaces now make the classification systematic:

- `search-reptends carry-selector-non-k1 --max 400 --blocks 8`
- `search-reptends carry-selector-same-core --max 400 --blocks 8`
- `search-reptends carry-selector-research --max 120 --bases 7,10,12 --blocks 8`

These are the reason selector profiles have now been promoted into the
published atlas layer: the repo has stable case studies, stable family studies,
and explicit grouped disagreement outputs rather than only local experiments.

The bounded cross-base summary used in the published atlas currently reports:

- base `7`, `N <= 120`: `26` selected non-`k = 1` relabeling windows and `14` same-core disagreement groups
- base `10`, `N <= 120`: `21` selected non-`k = 1` relabeling windows and `19` same-core disagreement groups
- base `12`, `N <= 120`: `14` selected non-`k = 1` relabeling windows and `14` same-core disagreement groups

This is enough signal to justify a published research layer while still
keeping the stronger theorem-level factorization claim open.

## Implemented Boundary vs Open Claim

What is implemented now:

- the raw coefficient stream `qk^j`,
- the carry transducer and its observed state graph,
- the remainder DFA in the same block coordinates,
- finite-window comparison reports showing that both machines emit the same displayed block word on the visible window,
- explicit observed state-map candidates in both directions,
- a decision framework separating state relabeling, quotient candidates, and the still-open global theorem,
- bounded search rows that surface counterexamples to the strongest naive state-level claim before theorem promotion.

What remains open:

- a canonical global factorization theorem identifying long division with orbit plus carry for all coprime moduli,
- uniqueness statements for that factorization beyond the current explicit examples and finite-window comparisons.
- cleaner closed forms for visibility lookahead and broader global carried-prefix behavior; that Track 16 framework now lives in [docs/CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md).

## Why This Matters

The carry transducer gives the repo a standard finite-state object for the carry layer.

- It exposes reachable carry states instead of only final digits.
- It exports a state graph that can be rendered or compared across examples.
- It makes the relation between raw coefficients and displayed blocks inspectable.

That is higher-signal than introducing more special vocabulary, because it lands on a standard automata/transducer model.
