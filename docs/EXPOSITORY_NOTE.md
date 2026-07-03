# Expository Note

This note is generated from the claim registry, theorem-witness registry, vocabulary registry, and published example atlas.
Each theorem-level item is tagged by claim ID and points back to concrete evidence.

## Proof-System Legend

- `Lean-formalized`: proved in the Lean tree and suitable for theorem-level citation in the current public surface.
- `Agda-locally-proved`: discharged inside the Agda pedagogical companion surface without relying on Agda postulates.
- `Agda-postulated but Lean-backed`: still explicit as an Agda postulate, but closed by Lean or an atlas-backed Lean-backed claim in this repo.
- `empirical`: implemented and regression-tested here, but not promoted to theorem status.
- `open`: tracked as an unresolved claim boundary or interface question, not an established result.

## Release Snapshot

Use [PROOF_STATUS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/PROOF_STATUS_ATLAS.md) as the theorem-level status source of truth.
Current registry counts:

- total claims: 15
- classical: 3
- reproved-here: 8
- implemented-here: 1
- empirical: 1
- open: 2

Current open claim IDs:
- `small_k_visibility_threshold` - Exact visibility threshold for carried prefixes
- `carry_dfa_factorization` - Canonical factorization of long division into orbit and carry

## Research Thesis

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

## Theorem-Witness Surface

Use [THEOREM_WITNESS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/THEOREM_WITNESS_ATLAS.md) for the claim-linked witness registry.
- total witness records: 20
- theorem-witness: 16
- empirical-witness: 1
- open-target: 3

- `series_q_weighted_identity_prime97_stride2` -> `series_q_weighted_identity`: (base=10, N=97, stride=2, B=100, q=1, k=3)
- `same_core_threshold_shift_interval_996_over_249` -> `same_core_threshold_shift_interval`: (base=10, actual=996, core=249, stride=3, B=1000, k=4)
- `small_k_visibility_threshold_target_97_249_996` -> `small_k_visibility_threshold`: (base=10, requestedBlocks=8, N in {97, 249, 996})
- `carry_dfa_factorization_target_21_97_996` -> `carry_dfa_factorization`: (base=10, N in {21, 97, 996})

Throughline witness ladder:

| Ladder rung | Registry support |
|-------------|------------------|
| Exact orbit support | Claims `digit_periodicity` and `preperiod_from_base_factors`; witnesses `digit_periodicity_prime19_base10` and `preperiod_from_base_factors_n996_base10`. Remainder periodicity and stripping of base-supported factors fix the exact orbit surface before any carry-normalization claim enters. |
| Exact block-coordinate support | Claims `series_q_weighted_identity` and `positive_q_good_modes`; witnesses `series_q_weighted_identity_prime97_stride2`, `series_q_weighted_identity_n249_stride3`, and `positive_q_good_modes_n249_stride3`. The raw coefficient stream is exactly `qk^j`, and the repo only promotes positive-q coordinates once `B > M`. Counterexamples: `legacy_unweighted_series_37` and `legacy_zero_quotient_mode`. |
| Implemented finite-window carry support | Claims `incoming_carry_position_formula`, `same_core_threshold_shift_interval`, and `carry_window_transducer`; witnesses `incoming_carry_position_formula_prime97_stride2`, `incoming_carry_position_formula_n249_stride3`, `same_core_threshold_shift_interval_996_over_249`, `carry_window_transducer_prime97_window6`, `carry_window_transducer_n249_window3`, and `carry_window_transducer_same_core_996_window4`. Finite-window carry-normalized output, exact incoming-carry boundaries, and same-core shift transport are already exact on named windows. Counterexamples: `legacy_visibility_local_overflow_97` and `legacy_visibility_local_overflow_249`. |
| Obstruction / counterexample surface | Claims `carry_dfa_factorization`; witnesses `carry_dfa_factorization_target_21_97_996` and `carry_dfa_factorization_target_249_498_996_same_core`. Observed state-map failures now split into visible preimage compression, hidden graph obstruction, and selector-profile disagreement, showing why finite output agreement does not by itself promote to a state-level theorem. Counterexamples: `carry_state_relabeling_failure_97`, `carry_state_relabeling_failure_996`, `carry_selector_monotonicity_failure_21`, and `carry_selector_core_invariance_failure_996`. |
| Open factorization targets | Claims `small_k_visibility_threshold` and `carry_dfa_factorization`; witnesses `small_k_visibility_threshold_target_97_249_996`, `carry_dfa_factorization_target_21_97_996`, and `carry_dfa_factorization_target_249_498_996_same_core`. The remaining frontier is an exact visibility threshold and a canonical orbit-plus-carry factorization, both kept explicitly open. Counterexamples: `carry_selector_core_invariance_failure_996`. |

## Classical Background

- `series_q_weighted_identity` (reproved-here)
  Statement: For a good block coordinate with B = qM + k, 0 <= k < M, and B > M, we have 1/M = q/(B-k) = Σ_{j>=0} qk^j / B^(j+1).
  Evidence: [OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [test_geometric_series.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_geometric_series.py)
- `power_order_formula` (classical)
  Statement: If r = ord_n(a), then ord_n(a^m) = r / gcd(r, m).
  Evidence: [analysis.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/analysis.py), [test_stride_classification.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_stride_classification.py)
- `crt_period_lcm` (classical)
  Statement: If M = Π p_i^{e_i} is coprime to the base B, then ord_M(B) is the least common multiple of the local orders ord_{p_i^{e_i}}(B).
  Evidence: [CompositePeriod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositePeriod.lean), [composite.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py), [test_composite_crt.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_composite_crt.py)
- `preperiod_from_base_factors` (classical)
  Statement: For denominator N and base b = Π p_i^{f_i}, the preperiod length is max_i ceil(v_{p_i}(N)/f_i); stripping those base factors leaves the purely periodic modulus M.
  Evidence: [composite.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [Preperiod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Preperiod.lean), [CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean), [test_composite_crt.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_composite_crt.py)
- `incoming_carry_position_formula` (reproved-here)
  Statement: For a block coordinate B = qN + k with 0 < k < B, the incoming carry into block j of the raw coefficient stream qk^j equals floor(qk^(j+1)/(B-k)). Therefore the first incoming-carry position is the least j with qk^(j+1) >= B-k.
  Evidence: [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/visibility.py), [CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py)
- `same_core_threshold_shift_interval` (reproved-here)
  Statement: Fix a block coordinate with shared B and k, and compare an actual denominator to its stripped periodic core. If k^s <= (q_core / q_actual) < k^(s+1), then the incoming-carry and local-overflow thresholds, and therefore the first visible mismatch boundary, for the core occur earlier by either s or s+1 blocks. When q_core / q_actual = k^s exactly, the shift is exactly s blocks. In the non-power interval case, Lean also packages scaled-raw-coefficient sufficient criteria for the lower and upper endpoint labels at fixed boundary data and propagates aligned lower/upper labels to the first visible mismatch boundary.
  Evidence: [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean), [visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/visibility.py), [CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py)

## Formalized Results

- `qr_stride_classification` (reproved-here)
  Statement: For an odd prime p and h = (p-1)/2, the stride m is QR-generating for base B exactly when ord_p(B) / gcd(ord_p(B), m) = h. Therefore QR-generating strides exist iff ord_p(B) is h or 2h, and their count is φ(h).
  Proof status: formalized in Lean as pow_isQRGenerator_iff, pow_isQRGenerator_iff_coprime_half, qrGenerator_pow_count_eq_totient, and the base-level full-order reduction theorems culminating in base_qrGenerator_pow_count_eq_totient
  Evidence: [QuadraticResidues.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/QuadraticResidues.lean), [test_stride_classification.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_stride_classification.py)
- `digit_periodicity` (reproved-here)
  Statement: For an odd prime p and a base B coprime to p, the base-B digits of 1/p are periodic with period ord_p(B). At each step, the digit is the Euclidean quotient in B*r_n = d_n*p + r_{n+1}.
  Proof status: Lean theorems in QRTour.Digits formalize the Euclidean digit/remainder equation, the digit bound, the period defined by orderOf on units, and the exact digit periodicity theorem.
  Evidence: [Digits.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Digits.lean), [AGDA_CORRESPONDENCE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/AGDA_CORRESPONDENCE.md), [ci_checks.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/ci_checks.py)
- `signed_bridge_recurrence` (reproved-here)
  Statement: If a prime denominator satisfies B^k ≡ ±d (mod p), then the remainder orbit obeys r[n+k] = (±d)r[n]. Consequently r[n+2k] = d^2 r[n], so the sign always cancels after two stride steps.
  Proof status: Lean theorems in QRTour.SignedBridge formalize the signed k-step recurrence, the two-step sign-cancellation law, and the conversion of ordinary bridge coordinates into the minus branch of the signed package.
  Evidence: [SignedBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/SignedBridge.lean), [PAdicBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/PAdicBridge.lean), [ci_checks.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/ci_checks.py), [README.md](/Users/mikepurvis/other/quadratic-residue-reptends/README.md)
- `bridge_block_value_periodicity` (reproved-here)
  Statement: For a bridge coordinate with B^k ≡ d (mod p), the block values at positions j*k are exactly d^j in ZMod p. Therefore the block sequence is periodic with period ord_p(d).
  Proof status: Lean theorems in QRTour.PAdicBridge formalize the block-value geometric identity, define bridgeOrder as the order of d in the unit group, and prove that the block sequence repeats with period bridgeOrder.
  Evidence: [PAdicBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/PAdicBridge.lean), [Bridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Bridge.lean), [ci_checks.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/ci_checks.py), [README.md](/Users/mikepurvis/other/quadratic-residue-reptends/README.md)
- `crt_period_lcm` (classical)
  Statement: If M = Π p_i^{e_i} is coprime to the base B, then ord_M(B) is the least common multiple of the local orders ord_{p_i^{e_i}}(B).
  Proof status: formalized in Lean via the finite-product order theorem orderOf_pi and the prime-power CRT theorem orderOf_unitsEquivPrimePowers; the pairwise theorem orderOf_unitsChineseRemainder remains as the two-factor core
  Evidence: [CompositePeriod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositePeriod.lean), [composite.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py), [test_composite_crt.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_composite_crt.py)
- `preperiod_from_base_factors` (classical)
  Statement: For denominator N and base b = Π p_i^{f_i}, the preperiod length is max_i ceil(v_{p_i}(N)/f_i); stripping those base factors leaves the purely periodic modulus M.
  Proof status: Lean formalizes the local ceiling-valuation theorem, the global max-over-base-primes step count, the positivity and self-divisibility of the base-supported factor, and the divisibility of that factor into base^preperiodSteps; the stripped-modulus M statement itself remains classical/computational
  Evidence: [composite.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [Preperiod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Preperiod.lean), [CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean), [test_composite_crt.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_composite_crt.py)

## Implementation Layers

- Standard vocabulary anchors: `small-residue block coordinate`, `remainder orbit under multiplication by the base`, `carry-propagated block normalization`.
- `carry_window_transducer` (implemented-here)
  Statement: For a finite coefficient word c_0, ..., c_{L-1}, carry propagation can be modeled by a deterministic transducer whose state is the incoming carry from less significant blocks.
  Repo status: explicit Python model with state graphs, coarse minimization hooks, carry-vs-remainder comparison reports, tests, and a Lean finite-window normalization/comparison surface including exact same-core shifted transport for observed remainder/carry state-pair windows
  Evidence: [CarryTransducer.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryTransducer.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py)
- `positive_q_good_modes` (reproved-here)
  Statement: A mode m only gives a usable q-weighted block coordinate when B = base^m exceeds the periodic modulus M, so q = (B-k)/M is positive.
  Repo status: formalized in Lean and implemented in search guards
  Evidence: [OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [test_geometric_series.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_geometric_series.py)
- `small_k_visibility_heuristic` (empirical)
  Statement: Small k, and especially q = 1, tends to postpone visible carry interactions and make the early block skeleton easier to read.
  Repo status: searchable and test-backed examples only
  Evidence: [search.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/search.py), [test_search_datasets.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_search_datasets.py)

## Curated Examples

- `1/37` - Constant-coefficient bridge: small-residue block coordinate with remainder k = 1 and quotient q = 27, so the raw coefficients qk^j are the constant sequence 27
- `1/97` - Prime q=1 bridge: small-residue block coordinate with q = 1 and remainder k = 3, so the raw coefficients qk^j reduce to literal powers of k and the period is nontrivial
- `1/249` - Composite periodic core: remainder orbit under multiplication by the base splits by CRT across 3 and 83 while still admitting a readable small-residue block coordinate
- `1/996` - Composite with preperiod: strip base factors to the purely periodic modulus 249; the example shows both preperiod behavior and a q = 1 bridge-style coordinate
- `1/19` - Prime QR counterexample: generator of the QR subgroup appears at stride 2, but the exact QR-generating strides are not all even, making this a useful high-signal counterexample

Composite family case studies:
- Prime-power lifting at p = 3 (3, 9, 27, 81) - This family shows a genuinely composite phenomenon: local orders on prime powers do not simply copy the prime case. For base 10, ord_3(10) = ord_9(10) = 1, then the order grows to 3 on 27 and 9 on 81.
- Shared periodic core 249 / 996 (249, 996) - This family separates the purely periodic remainder-orbit structure from the base-factor preperiod. The pair is the clearest composite example where CRT data, preperiod length, and carry normalization can be discussed independently.

Carry / DFA case studies:
- `1/21` - Trivial state relabeling: in this block coordinate both observed finite-window functional criteria hold and both machines collapse to one state, giving the trivial relabeling regime
  Implemented boundary: finite-window output agreement between the carry-propagated block normalization and the long-division DFA
  Open boundary: canonical factorization of the entire long-division DFA into orbit plus carry is not established here
- `1/97` - Prime carry interaction: finite-window outputs match, the observed remainder-to-carry functional criterion holds, and the carry-to-remainder criterion fails, so the window is quotient-only rather than a relabeling
  Implemented boundary: finite-window output agreement between the carry-propagated block normalization and the long-division DFA
  Open boundary: canonical factorization of the entire long-division DFA into orbit plus carry is not established here
- `1/996` - Composite preperiod plus carry: the same quotient-only finite-window regime persists in a composite example with preperiod and same-core structure
  Implemented boundary: finite-window output agreement between the carry-propagated block normalization and the long-division DFA
  Open boundary: canonical factorization of the entire long-division DFA into orbit plus carry is not established here

Carry selector case studies:
- `1/21` - Isolated k = 1 relabeling window: The selector profile finite_word_only -> state_relabeling -> finite_word_only shows that trivial relabeling can appear only at one isolated block width.
  Selector summary: class isolated_k_one_relabeling, selected m 6, selected k 1, relabeling modes [6]
  Theorem candidate: Classify when selector profiles admit isolated or repeated state-relabeling windows beyond the trivial k = 1 coordinates.
  Counterexample target: Use this case to test naive claims that larger block widths, stripped cores, or output agreement alone determine the state-level regime.
- `1/249` - Isolated non-k = 1 relabeling window: This is the cleanest decimal example where the selector chooses a genuine non-k = 1 relabeling window, at m = 6 with k = 16.
  Selector summary: class isolated_non_k_one_relabeling, selected m 6, selected k 16, relabeling modes [6]
  Theorem candidate: Classify when selector profiles admit isolated or repeated state-relabeling windows beyond the trivial k = 1 coordinates.
  Counterexample target: Use this case to test naive claims that larger block widths, stripped cores, or output agreement alone determine the state-level regime.
- `1/996` - Same-core quotient-only persistence: The same-core denominator 996 never reaches a relabeling window on the tested profile, even though 249 does.
  Selector summary: class quotient_only, selected m 3, selected k 4, relabeling modes []
  Theorem candidate: Classify when selector profiles admit isolated or repeated state-relabeling windows beyond the trivial k = 1 coordinates.
  Counterexample target: Use this case to test naive claims that larger block widths, stripped cores, or output agreement alone determine the state-level regime.

Carry selector family studies:
- Non-k = 1 relabeling windows (17, 19, 29, 249) - State-relabeling is not confined to k = 1 coordinates. The selector isolates nontrivial relabeling windows at examples like 17, 19, 29, and 249 in base 10.
- Same-core relabeling loss (249, 498, 996) - The selector profile is not determined by stripped periodic core. Core 249 supports an isolated relabeling window, while same-core 498 and 996 stay quotient-only.
- Small-multiple relabeling shift and enlargement (17, 34, 68) - Small-multiple moves can preserve and enlarge relabeling windows rather than merely shifting or destroying them: 17 relabels at m = 5, 34 relabels at m = 5 and 7, and 68 loses relabeling entirely.

Carry selector cross-base summary:
- base 7 up to N <= 120: 26 selected non-k = 1 relabeling windows and 14 same-core disagreement groups.
  Publication decision: published_research_layer
- base 10 up to N <= 120: 21 selected non-k = 1 relabeling windows and 19 same-core disagreement groups.
  Publication decision: published_research_layer
- base 12 up to N <= 120: 14 selected non-k = 1 relabeling windows and 14 same-core disagreement groups.
  Publication decision: published_research_layer

Carried-prefix visibility case studies:
- `1/21` - Carry-free constant window: q is large but k = 1, so every requested raw block is already legal and no incoming carry appears.
  Exact observable summary: raw-prefix agreement 6/6, first incoming carry None, first local overflow None, lookahead 0
  Theorem candidate: Extend the exact incoming-carry boundary to useful bounds for stabilization lookahead and same-core families.
  Counterexample target: Use this case family to test and refute naive visibility rules based only on local overflow.
- `1/37` - Positive-q constant coefficient window: q > 1 and k = 1 give a constant raw coefficient stream, making this the cleanest non-bridge positive-q case.
  Exact observable summary: raw-prefix agreement 6/6, first incoming carry None, first local overflow None, lookahead 0
  Theorem candidate: Extend the exact incoming-carry boundary to useful bounds for stabilization lookahead and same-core families.
  Counterexample target: Use this case family to test and refute naive visibility rules based only on local overflow.
- `1/97` - Incoming carry before local overflow: The displayed block at position 4 changes because of incoming carry even though the local raw coefficient 81 is still below 100.
  Exact observable summary: raw-prefix agreement 4/8, first incoming carry 4, first local overflow 5, lookahead 2
  Theorem candidate: Extend the exact incoming-carry boundary to useful bounds for stabilization lookahead and same-core families.
  Counterexample target: Use this case family to test and refute naive visibility rules based only on local overflow.
- `1/249` - Positive-q carry intrusion: The positive-q case already exhibits early incoming carry, so naive q*k^j < B visibility rules fail outside q = 1 as well.
  Exact observable summary: raw-prefix agreement 3/8, first incoming carry 3, first local overflow 4, lookahead 2
  Theorem candidate: Extend the exact incoming-carry boundary to useful bounds for stabilization lookahead and same-core families.
  Counterexample target: Use this case family to test and refute naive visibility rules based only on local overflow.
- `1/996` - Shared periodic core with preperiod: This shares the periodic core of 249 but adds a decimal preperiod, separating periodic-core structure from visible-prefix behavior.
  Exact observable summary: raw-prefix agreement 4/8, first incoming carry 4, first local overflow 5, lookahead 1
  Theorem candidate: Extend the exact incoming-carry boundary to useful bounds for stabilization lookahead and same-core families.
  Counterexample target: Use this case family to test and refute naive visibility rules based only on local overflow.

Visibility family studies:
- q = 1 carried-prefix family (97, 996) - Both cases have q = 1 and small k, but one is prime-purely-periodic and the other has a decimal preperiod. Compare raw-prefix agreement length and lookahead rather than only k.
- q > 1 carried-prefix family (21, 37, 249) - These cases separate positive-q constant windows from positive-q early-carry intrusion, so q > 1 by itself is not a visibility obstruction.
- Shared periodic core with different preperiods (249, 498, 996) - This family isolates one periodic core while varying the stripped base-factor ratio. The comparison 996/249 shows the exact k-power shift law, while 498/249 shows the broader two-point interval law when the q-ratio is not itself a power of k.
- Cross-base same-core exact law (8, 56) - Base 7 supplies a non-decimal exact-law family: in the shared coordinate B = 343 and k = 7, the pair 56/8 realizes the same one-block exact shift seen in the decimal 996/249 family.
- Cross-base interval endpoints in one coordinate (5, 10, 20, 35, 70) - Base 12 exhibits all three local same-core outcomes in one shared coordinate B = 144, k = 4: 10/5 realizes the lower interval endpoint, 70/35 realizes the upper interval endpoint, and 20/5 realizes the exact k-power law.

## Open Questions

- `small_k_visibility_threshold`
  Statement: There is a sharp arithmetic criterion, in terms of q, k, B, and the period data, for the minimal stabilization lookahead and the remaining global visibility behavior beyond the now-implemented incoming-carry and raw-prefix boundary formulas.
  Evidence: [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean), [visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/visibility.py), [CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py)
- `carry_dfa_factorization`
  Statement: The long-division DFA factors canonically into a remainder-orbit system together with a carry transducer for all coprime bases and moduli.
  Evidence: [CarryTransducer.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryTransducer.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [Factorization.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Factorization.lean), [transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py), [CARRY_TRANSDUCER.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRY_TRANSDUCER.md), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py)
