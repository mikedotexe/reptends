# Theorem Witness Atlas

Use [docs/PROOF_STATUS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/PROOF_STATUS_ATLAS.md) as the public status source of truth. This note packages canonical theorem witnesses, empirical witnesses, and open target families by claim ID.

Machine-readable backing lives in [theorem_witnesses.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/theorem_witnesses.json) and [example_atlas.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/example_atlas.json).

## Proof-System Legend

<!-- PROOF_SYSTEM_LEGEND_START -->
- `Lean-formalized`: proved in the Lean tree and suitable for theorem-level citation in the current public surface.
- `Agda-locally-proved`: discharged inside the Agda pedagogical companion surface without relying on Agda postulates.
- `Agda-postulated but Lean-backed`: still explicit as an Agda postulate, but closed by Lean or an atlas-backed Lean-backed claim in this repo.
- `empirical`: implemented and regression-tested here, but not promoted to theorem status.
- `open`: tracked as an unresolved claim boundary or interface question, not an established result.
<!-- PROOF_SYSTEM_LEGEND_END -->

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

## Witness Summary

<!-- THEOREM_WITNESS_SUMMARY_START -->
- total witness records: 17
- theorem-witness: 13
- empirical-witness: 1
- open-target: 3
<!-- THEOREM_WITNESS_SUMMARY_END -->

## Same-Core Boundary Contrast

This atlas-backed contrast keeps the current same-core frontier explicit: exact visibility transport is already witnessed, while state-level carry transport remains open.

<!-- SAME_CORE_BOUNDARY_NOTE_START -->
| Surface | Atlas witness | Current boundary signal |
|---------|---------------|-------------------------|
| Exact same-core visibility transport | `same_core_threshold_shift_interval_996_over_249` | Claim `same_core_threshold_shift_interval`: The 996 over 249 family is the canonical same-core witness for the exact k-power shift law. |
| Same-core selector-family failure | `carry_dfa_factorization_target_249_498_996_same_core` | Claim `carry_dfa_factorization`: This same-core family shows that short exact same-core transport does not yet extend to carry-to-remainder functionality: 249 has an isolated relabeling window, while 498 and 996 stay quotient-only. Therefore exact same-core `carryToRemainderFunctional` transport is not currently claimed. |
<!-- SAME_CORE_BOUNDARY_NOTE_END -->

## Canonical Witnesses

<!-- THEOREM_WITNESS_TABLE_START -->
| Witness ID | Claim ID | Claim Status | Kind | Canonical tuple or family | Why this witness | Repo Evidence |
|------------|----------|--------------|------|---------------------------|------------------|---------------|
| `series_q_weighted_identity_prime97_stride2` | `series_q_weighted_identity` | `reproved-here` | `theorem-witness` | (base=10, N=97, stride=2, B=100, q=1, k=3) | Canonical q = 1 coordinate where the visible coefficients are literal powers of k. | [OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean), [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [test_geometric_series.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_geometric_series.py) |
| `power_order_formula_prime19_stride2` | `power_order_formula` | `classical` | `theorem-witness` | (base=10, p=19, ord_p(base)=18, stride=2, ord_p(base^stride)=9) | A compact prime example where ord(base^m) is visibly ord(base) divided by gcd. | [analysis.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/analysis.py), [test_stride_classification.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_stride_classification.py) |
| `qr_stride_classification_prime97_stride2` | `qr_stride_classification` | `reproved-here` | `theorem-witness` | (base=10, p=97, ord_p(base)=96, stride=2, ord_p(base^stride)=48) | This is the canonical decimal example where the stride order drops exactly to the QR subgroup size. | [QuadraticResidues.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/QuadraticResidues.lean), [test_stride_classification.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_stride_classification.py) |
| `digit_periodicity_prime19_base10` | `digit_periodicity` | `reproved-here` | `theorem-witness` | (base=10, p=19, ord_p(base)=18) | A small prime witness where the Euclidean digit step and full repeating period are both easy to inspect. | [Digits.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Digits.lean), [AGDA_CORRESPONDENCE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/AGDA_CORRESPONDENCE.md), [ci_checks.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/ci_checks.py) |
| `signed_bridge_recurrence_prime97_stride2` | `signed_bridge_recurrence` | `reproved-here` | `theorem-witness` | (base=10, p=97, stride=2, d=3, 10^2 ≡ +3 mod 97) | The standard 97 example witnesses the signed recurrence package even before using a minus-branch example. | [SignedBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/SignedBridge.lean), [PAdicBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/PAdicBridge.lean), [ci_checks.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/ci_checks.py) |
| `bridge_block_value_periodicity_prime97_stride2` | `bridge_block_value_periodicity` | `reproved-here` | `theorem-witness` | (base=10, p=97, stride=2, d=3, block values at 2j are 3^j mod 97) | This witnesses the block-value geometric law and its period in the cleanest decimal bridge case. | [PAdicBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/PAdicBridge.lean), [Bridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Bridge.lean), [ci_checks.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/ci_checks.py) |
| `crt_period_lcm_mod21_base10` | `crt_period_lcm` | `classical` | `theorem-witness` | (base=10, N=21=3·7, ord_3(10)=1, ord_7(10)=6, ord_21(10)=lcm(1,6)=6) | A tiny composite witness where the CRT least-common-multiple law is completely transparent. | [CompositePeriod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositePeriod.lean), [composite.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py), [test_composite_crt.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_composite_crt.py) |
| `preperiod_from_base_factors_n996_base10` | `preperiod_from_base_factors` | `classical` | `theorem-witness` | (base=10, N=996=2^2·3·83, preperiod=2, stripped core=249) | The canonical decimal composite where the preperiod is entirely explained by the base-supported factor 2^2. | [Preperiod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Preperiod.lean), [CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean), [test_composite_crt.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_composite_crt.py) |
| `carry_window_transducer_prime97_window6` | `carry_window_transducer` | `implemented-here` | `theorem-witness` | (base=10, N=97, stride=2, requestedBlocks=6, lookahead=3) | A finite 97-window witnesses deterministic carry normalization and agreement with the emitted block word. | [CarryTransducer.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryTransducer.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py) |
| `small_k_visibility_heuristic_family_21_37_97_249_996` | `small_k_visibility_heuristic` | `empirical` | `empirical-witness` | (base=10, N in {21, 37, 97, 249, 996}) | The published visibility cases show that small k and especially q = 1 often delay visible carry, but only as an empirical pattern. | [search.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/search.py), [example_atlas.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/example_atlas.json), [test_search_datasets.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_search_datasets.py) |
| `positive_q_good_modes_n249_stride3` | `positive_q_good_modes` | `reproved-here` | `theorem-witness` | (base=10, N=249, stride=3, B=1000, q=4, k=4) | This composite coordinate is the standard positive-q witness showing why good modes require B > N. | [OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [test_geometric_series.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_geometric_series.py) |
| `incoming_carry_position_formula_prime97_stride2` | `incoming_carry_position_formula` | `reproved-here` | `theorem-witness` | (base=10, N=97, stride=2, B=100, q=1, k=3, first incoming carry=4) | The standard 1/97 window shows the exact incoming-carry boundary before the first local overflow. | [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean), [CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py) |
| `same_core_threshold_shift_interval_996_over_249` | `same_core_threshold_shift_interval` | `reproved-here` | `theorem-witness` | (base=10, actual=996, core=249, stride=3, B=1000, k=4) | The 996 over 249 family is the canonical same-core witness for the exact k-power shift law. | [CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean), [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py) |
| `small_k_visibility_threshold_target_97_249_996` | `small_k_visibility_threshold` | `open` | `open-target` | (base=10, requestedBlocks=8, N in {97, 249, 996}) | These cases bracket the current exact fixed-window layer while still leaving the minimal-lookahead theorem open. | [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py) |
| `carry_dfa_factorization_target_21_97_996` | `carry_dfa_factorization` | `open` | `open-target` | (base=10, N in {21, 97, 996}) | The canonical carry trio still separates finite output agreement from the open global factorization question. | [CarryTransducer.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryTransducer.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py) |
| `carry_dfa_factorization_target_249_498_996_same_core` | `carry_dfa_factorization` | `open` | `open-target` | (base=10, core=249, members in {249, 498, 996}, requestedBlocks=8) | This same-core family shows that short exact same-core transport does not yet extend to carry-to-remainder functionality: 249 has an isolated relabeling window, while 498 and 996 stay quotient-only. | [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py) |
| `carry_window_transducer_same_core_996_window4` | `carry_window_transducer` | `implemented-here` | `theorem-witness` | (base=10, N=996, core=249, stride=3, requestedBlocks=4, lookahead=0) | The short 996 over 249 same-core shift is the canonical witness for transported remainder-to-carry functionality on the actual window. | [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py) |
<!-- THEOREM_WITNESS_TABLE_END -->
