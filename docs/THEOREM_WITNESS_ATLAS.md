# Theorem Witness Atlas

Use [docs/PROOF_STATUS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/PROOF_STATUS_ATLAS.md) as the public status source of truth. This note packages canonical theorem witnesses, empirical witnesses, and open target families by claim ID.

Machine-readable backing lives in [theorem_witnesses.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/theorem_witnesses.json), [throughlines.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/throughlines.json), and [example_atlas.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/example_atlas.json).

## Proof-System Legend

<!-- PROOF_SYSTEM_LEGEND_START -->
- `Lean-formalized`: proved in the Lean tree and suitable for theorem-level citation in the current public surface.
- `Agda-locally-proved`: discharged inside the Agda pedagogical companion surface without relying on Agda postulates.
- `Agda-postulated but Lean-backed`: still explicit as an Agda postulate, but closed by Lean or an atlas-backed Lean-backed claim in this repo.
- `empirical`: implemented and regression-tested here, but not promoted to theorem status.
- `open`: tracked as an unresolved claim boundary or interface question, not an established result.
<!-- PROOF_SYSTEM_LEGEND_END -->

## Research Thesis

This atlas treats the repo's orbit-plus-carry framing as a research thesis, not
as a promoted theorem claim.

<!-- THROUGHLINE_RESEARCH_THESIS_START -->
- Kind: `research-thesis`
- Thesis ID: `orbit_plus_carry_factorization`
- Title: Long Division as Orbit + Carry
- Headline: Long division is best understood as a remainder-orbit system plus carry-propagated block normalization.
- Status note: Exact finite-window interfaces are implemented; the global canonical factorization remains `open` under `carry_dfa_factorization`.
- Exact support claims: `digit_periodicity`, `preperiod_from_base_factors`, `series_q_weighted_identity`, `positive_q_good_modes`, `carry_window_transducer`, `incoming_carry_position_formula`, and `same_core_threshold_shift_interval`
- Open frontier claims: `small_k_visibility_threshold` and `carry_dfa_factorization`
- Canonical witness anchors: `digit_periodicity_prime19_base10`, `series_q_weighted_identity_prime97_stride2`, `series_q_weighted_identity_n249_stride3`, `carry_window_transducer_prime97_window6`, `preperiod_from_base_factors_n996_base10`, `carry_dfa_factorization_target_21_97_996`, `same_core_threshold_shift_interval_996_over_249`, and `carry_dfa_factorization_target_249_498_996_same_core`
- Obstruction records: `carry_state_relabeling_failure_97`, `carry_state_relabeling_failure_996`, `carry_selector_monotonicity_failure_21`, and `carry_selector_core_invariance_failure_996`
- Search surface `orbit_carry_frontier`: Groups the exact orbit layer, implemented carry layer, open factorization targets, and obstruction families under one exported surface. Command: `search-reptends orbit-carry-frontier --max 1200 --base 10 --blocks 8`
- Search surface `orbit_carry_trace`: Experimental finite trace lens for the canonical 21 / 97 / 996 trio, aligning remainder orbit states, raw coefficients, finite carry-window states, and displayed blocks. Command: `search-reptends orbit-carry-trace --base 10 --blocks 8 --members 21,97,996`
- Search surface `visibility_optics_workbench`: Ranks finite-window evidence for how readable the source remainder orbit is through the carry-propagated block normalization instrument. Command: `search-reptends visibility-optics --max 1200 --base 10 --blocks 8 --top 20`
- Search surface `visibility_base_compare`: Compares Visibility Optics signal classes across base instruments such as 10, 12, and 30 so base choice becomes data rather than a default. Command: `search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20`
- Search surface `instrument_atlas`: Compares base instruments by what they reveal, absorb, distort, or obstruct so working axioms can be revised against finite-window evidence. Command: `search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20`
- Search surface `chart_invariance`: Compares base-chart pairs for finite-window invariant candidates and clean distortion witnesses. Command: `search-reptends chart-invariance --max 1200 --bases 7,10,12,30 --blocks 8 --top 20`
- Search surface `carry_factorization`: Keeps the canonical 21 / 97 / 996 carry-DFA comparisons visible as bounded evidence beneath the open factorization claim. Command: `search-reptends carry-factorization --max 500 --blocks 8`
- Search surface `state_merging`: Makes the finite-window collapse/compression pattern explicit on the selected Track 17 coordinate for canonical cases like 21, 97, and 996. Command: `search-reptends state-merging --max 500 --base 10 --blocks 8`
- Search surface `quotient_obstructions`: Splits selected-coordinate quotient-only cases into visible preimage compression versus hidden graph obstruction on the base-10 Track 17 surface. Command: `search-reptends quotient-obstructions --max 500 --base 10 --blocks 8`
- Search surface `state_merging_same_core`: Tracks same-core disagreement families such as 249 / 498 / 996 and 17 / 34 / 68 / 85 through their selected preimage-fiber profiles. Command: `search-reptends state-merging-same-core --max 1200 --base 10 --blocks 8`
- Search surface `quotient_obstruction_families`: Groups same-core families by whether they span relabeling, hidden graph obstruction, and visible preimage compression on the selected coordinate. Command: `search-reptends quotient-obstruction-families --max 1200 --base 10 --blocks 8`
- Search surface `same_core_obstruction_correlates`: Summarizes empirical correlates separating re-hiding same-core families from one-way visible families at the selected bound. Command: `search-reptends same-core-obstruction-correlates --max 2000 --base 10 --blocks 8`
- Search surface `carry_selector_same_core`: Tracks same-core selector-profile disagreement families such as 249 / 498 / 996. Command: `search-reptends carry-selector-same-core --max 400 --blocks 8`
- Search surface `same_core_visibility`: Compares actual denominators to stripped periodic cores so the exact same-core shift layer stays connected to the frontier. Command: `search-reptends same-core-visibility --max 500 --base 10 --blocks 8`
<!-- THROUGHLINE_RESEARCH_THESIS_END -->

## Release Snapshot

Current registry counts:

<!-- REGISTRY_SUMMARY_START -->
- total claims: 15
- classical: 3
- reproved-here: 8
- implemented-here: 1
- empirical: 1
- open: 2
<!-- REGISTRY_SUMMARY_END -->

Current open claim IDs:

<!-- OPEN_CLAIMS_START -->
- `small_k_visibility_threshold` - Exact visibility threshold for carried prefixes
- `carry_dfa_factorization` - Canonical factorization of long division into orbit and carry
<!-- OPEN_CLAIMS_END -->

Witness kinds:

- `theorem-witness`: a canonical tuple or family supporting a `classical`, `reproved-here`, or `implemented-here` claim
- `empirical-witness`: a curated evidence family that stays explicitly below theorem status
- `open-target`: a named target family for an atlas claim that remains open

## Throughline Witness Ladder

This witness ladder is the front door for the orbit-plus-carry thesis. It
separates exact support, implemented finite-window carry support, obstruction
surface, and open targets without promoting the thesis itself to theorem
status.

The new preimage-fiber profile (state-merging atlas) sits beneath that ladder
as a bounded explanatory surface: it records finite-window collapse and
compression directly on the selected Track 17 coordinate, and now separates
visible preimage compression from hidden graph obstruction without upgrading
the open `carry_dfa_factorization` claim to theorem status.

<!-- THROUGHLINE_WITNESS_LADDER_START -->
| Ladder rung | Registry support |
|-------------|------------------|
| Exact orbit support | Claims `digit_periodicity` and `preperiod_from_base_factors`; witnesses `digit_periodicity_prime19_base10` and `preperiod_from_base_factors_n996_base10`. Remainder periodicity and stripping of base-supported factors fix the exact orbit surface before any carry-normalization claim enters. |
| Exact block-coordinate support | Claims `series_q_weighted_identity` and `positive_q_good_modes`; witnesses `series_q_weighted_identity_prime97_stride2`, `series_q_weighted_identity_n249_stride3`, and `positive_q_good_modes_n249_stride3`. The raw coefficient stream is exactly `qk^j`, and the repo only promotes positive-q coordinates once `B > M`. Counterexamples: `legacy_unweighted_series_37` and `legacy_zero_quotient_mode`. |
| Implemented finite-window carry support | Claims `incoming_carry_position_formula`, `same_core_threshold_shift_interval`, and `carry_window_transducer`; witnesses `incoming_carry_position_formula_prime97_stride2`, `incoming_carry_position_formula_n249_stride3`, `same_core_threshold_shift_interval_996_over_249`, `carry_window_transducer_prime97_window6`, `carry_window_transducer_n249_window3`, and `carry_window_transducer_same_core_996_window4`. Finite-window carry-normalized output, exact incoming-carry boundaries, and same-core shift transport are already exact on named windows. Counterexamples: `legacy_visibility_local_overflow_97` and `legacy_visibility_local_overflow_249`. |
| Obstruction / counterexample surface | Claims `carry_dfa_factorization`; witnesses `carry_dfa_factorization_target_21_97_996` and `carry_dfa_factorization_target_249_498_996_same_core`. Observed state-map failures now split into visible preimage compression, hidden graph obstruction, and selector-profile disagreement, showing why finite output agreement does not by itself promote to a state-level theorem. Counterexamples: `carry_state_relabeling_failure_97`, `carry_state_relabeling_failure_996`, `carry_selector_monotonicity_failure_21`, and `carry_selector_core_invariance_failure_996`. |
| Open factorization targets | Claims `small_k_visibility_threshold` and `carry_dfa_factorization`; witnesses `small_k_visibility_threshold_target_97_249_996`, `carry_dfa_factorization_target_21_97_996`, and `carry_dfa_factorization_target_249_498_996_same_core`. The remaining frontier is an exact visibility threshold and a canonical orbit-plus-carry factorization, both kept explicitly open. Counterexamples: `carry_selector_core_invariance_failure_996`. |
<!-- THROUGHLINE_WITNESS_LADDER_END -->

## Witness Summary

<!-- THEOREM_WITNESS_SUMMARY_START -->
- total witness records: 20
- theorem-witness: 16
- empirical-witness: 1
- open-target: 3
<!-- THEOREM_WITNESS_SUMMARY_END -->

## Same-Core Boundary Contrast

This atlas-backed contrast keeps the current same-core frontier explicit: exact visibility transport is already witnessed, while state-level carry transport remains open.

<!-- SAME_CORE_BOUNDARY_NOTE_START -->
| Surface | Atlas witness | Current boundary signal |
|---------|---------------|-------------------------|
| Exact same-core visibility transport | `same_core_threshold_shift_interval_996_over_249` | Claim `same_core_threshold_shift_interval`: The 996 over 249 family is the canonical same-core witness for the exact k-power shift law. |
| Same-core selector-family failure | `carry_dfa_factorization_target_249_498_996_same_core` | Claim `carry_dfa_factorization`: This same-core family shows that forward exact same-core carry-to-remainder transport fails even on the small `249 -> 996` shifted pair: `249` is functional on the one-block `1/0` window, `996` already fails on the corresponding `2/0` window, and the larger selector-family windows for `498` and `996` stay quotient-only. This keeps forward same-core `carryToRemainderFunctional` transport outside the current Lean claim surface. |
<!-- SAME_CORE_BOUNDARY_NOTE_END -->

## Canonical Witnesses

<!-- THEOREM_WITNESS_TABLE_START -->
| Witness ID | Claim ID | Claim Status | Kind | Canonical tuple or family | Why this witness | Lean example namespace(s) | Repo Evidence |
|------------|----------|--------------|------|---------------------------|------------------|---------------------------|---------------|
| `series_q_weighted_identity_prime97_stride2` | `series_q_weighted_identity` | `reproved-here` | `theorem-witness` | (base=10, N=97, stride=2, B=100, q=1, k=3) | Canonical q = 1 coordinate where the visible coefficients are literal powers of k. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Prime97` | [OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean), [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [test_geometric_series.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_geometric_series.py) |
| `series_q_weighted_identity_n249_stride3` | `series_q_weighted_identity` | `reproved-here` | `theorem-witness` | (base=10, N=249, stride=3, B=1000, q=4, k=4) | This positive-q composite coordinate makes the exact q*k^j / B^(j+1) identity explicit outside the special q = 1 bridge case. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Composite249` | [OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean), [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [test_geometric_series.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_geometric_series.py) |
| `power_order_formula_prime19_stride2` | `power_order_formula` | `classical` | `theorem-witness` | (base=10, p=19, ord_p(base)=18, stride=2, ord_p(base^stride)=9) | A compact prime example where ord(base^m) is visibly ord(base) divided by gcd. | - | [analysis.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/analysis.py), [test_stride_classification.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_stride_classification.py) |
| `qr_stride_classification_prime97_stride2` | `qr_stride_classification` | `reproved-here` | `theorem-witness` | (base=10, p=97, ord_p(base)=96, stride=2, ord_p(base^stride)=48) | This is the canonical decimal example where the stride order drops exactly to the QR subgroup size. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Prime97` | [QuadraticResidues.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/QuadraticResidues.lean), [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [test_stride_classification.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_stride_classification.py) |
| `digit_periodicity_prime19_base10` | `digit_periodicity` | `reproved-here` | `theorem-witness` | (base=10, p=19, ord_p(base)=18) | A small prime witness where the Euclidean digit step and full repeating period are both easy to inspect. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Prime19` | [Digits.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Digits.lean), [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [AGDA_CORRESPONDENCE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/AGDA_CORRESPONDENCE.md), [ci_checks.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/ci_checks.py) |
| `signed_bridge_recurrence_prime97_stride2` | `signed_bridge_recurrence` | `reproved-here` | `theorem-witness` | (base=10, p=97, stride=2, d=3, 10^2 ≡ +3 mod 97) | The standard 97 example witnesses the signed recurrence package in the clean decimal minus-bridge case. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Prime97` | [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [SignedBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/SignedBridge.lean), [PAdicBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/PAdicBridge.lean), [ci_checks.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/ci_checks.py) |
| `bridge_block_value_periodicity_prime97_stride2` | `bridge_block_value_periodicity` | `reproved-here` | `theorem-witness` | (base=10, p=97, stride=2, d=3, block values at 2j are 3^j mod 97) | This witnesses the block-value geometric law and its period in the cleanest decimal bridge case. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Prime97` | [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [PAdicBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/PAdicBridge.lean), [Bridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Bridge.lean), [ci_checks.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/ci_checks.py) |
| `crt_period_lcm_mod21_base10` | `crt_period_lcm` | `classical` | `theorem-witness` | (base=10, N=21=3·7, ord_3(10)=1, ord_7(10)=6, ord_21(10)=lcm(1,6)=6) | A tiny composite witness where the CRT least-common-multiple law is completely transparent. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Composite21` | [CompositePeriod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositePeriod.lean), [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [composite.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py), [test_composite_crt.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_composite_crt.py) |
| `preperiod_from_base_factors_n996_base10` | `preperiod_from_base_factors` | `classical` | `theorem-witness` | (base=10, N=996=2^2·3·83, preperiod=2, stripped core=249) | The canonical decimal composite where the preperiod is entirely explained by the base-supported factor 2^2. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Composite996` | [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [Preperiod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Preperiod.lean), [CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean), [test_composite_crt.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_composite_crt.py) |
| `carry_window_transducer_prime97_window6` | `carry_window_transducer` | `implemented-here` | `theorem-witness` | (base=10, N=97, stride=2, requestedBlocks=6, lookahead=3) | A finite 97-window witnesses deterministic carry normalization and agreement with the emitted block word. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Prime97` | [CarryTransducer.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryTransducer.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py) |
| `small_k_visibility_heuristic_family_21_37_97_249_996` | `small_k_visibility_heuristic` | `empirical` | `empirical-witness` | (base=10, N in {21, 37, 97, 249, 996}) | The published visibility cases show that small k and especially q = 1 often delay visible carry, but only as an empirical pattern. | - | [search.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/search.py), [example_atlas.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/example_atlas.json), [test_search_datasets.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_search_datasets.py) |
| `carry_window_transducer_n249_window3` | `carry_window_transducer` | `implemented-here` | `theorem-witness` | (base=10, N=249, stride=3, B=1000, q=4, k=4, requestedBlocks=3, lookahead=0) | The first three blocks of the positive-q 249 coordinate stay carry-free, so zero lookahead already certifies deterministic normalization and emitted-word agreement outside the special q = 1 case. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Composite249` | [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [CarryTransducer.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryTransducer.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py) |
| `positive_q_good_modes_n249_stride3` | `positive_q_good_modes` | `reproved-here` | `theorem-witness` | (base=10, N=249, stride=3, B=1000, q=4, k=4) | This composite coordinate is the standard positive-q witness showing why good modes require B > N. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Composite249` | [OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean), [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [test_geometric_series.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_geometric_series.py) |
| `incoming_carry_position_formula_prime97_stride2` | `incoming_carry_position_formula` | `reproved-here` | `theorem-witness` | (base=10, N=97, stride=2, B=100, q=1, k=3, first incoming carry=4) | The standard 1/97 window shows the exact incoming-carry boundary before the first local overflow. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Prime97` | [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py) |
| `incoming_carry_position_formula_n249_stride3` | `incoming_carry_position_formula` | `reproved-here` | `theorem-witness` | (base=10, N=249, stride=3, B=1000, q=4, k=4, first incoming carry=3) | This positive-q composite coordinate shows the exact incoming-carry boundary outside the special q = 1 bridge case. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Composite249` | [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py) |
| `same_core_threshold_shift_interval_996_over_249` | `same_core_threshold_shift_interval` | `reproved-here` | `theorem-witness` | (base=10, actual=996, core=249, stride=3, B=1000, k=4) | The 996 over 249 family is the canonical same-core witness for the exact k-power shift law. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Composite996` | [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean), [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py) |
| `small_k_visibility_threshold_target_97_249_996` | `small_k_visibility_threshold` | `open` | `open-target` | (base=10, requestedBlocks=8, N in {97, 249, 996}) | These cases bracket the current exact fixed-window layer while still leaving the minimal-lookahead theorem open. | - | [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py) |
| `carry_dfa_factorization_target_21_97_996` | `carry_dfa_factorization` | `open` | `open-target` | (base=10, N in {21, 97, 996}) | The canonical carry trio still separates finite output agreement from the open global factorization question. | - | [CarryTransducer.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryTransducer.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py) |
| `carry_dfa_factorization_target_249_498_996_same_core` | `carry_dfa_factorization` | `open` | `open-target` | (base=10, core=249, members in {249, 498, 996}, requestedBlocks=8) | This same-core family shows that forward exact same-core carry-to-remainder transport fails even on the small `249 -> 996` shifted pair: `249` is functional on the one-block `1/0` window, `996` already fails on the corresponding `2/0` window, and the larger selector-family windows for `498` and `996` stay quotient-only. | - | [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py) |
| `carry_window_transducer_same_core_996_window4` | `carry_window_transducer` | `implemented-here` | `theorem-witness` | (base=10, N=996, core=249, stride=3, requestedBlocks=4, lookahead=0) | The short 996 over 249 same-core shift is the canonical witness for transported remainder-to-carry functionality on the actual window. | [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) `QRTour.Composite996` | [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py) |
<!-- THEOREM_WITNESS_TABLE_END -->
