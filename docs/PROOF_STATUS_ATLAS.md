# Proof-Status Atlas

This project now treats its public claims as a registry rather than free-form prose.

## Proof-System Legend

<!-- PROOF_SYSTEM_LEGEND_START -->
- `Lean-formalized`: proved in the Lean tree and suitable for theorem-level citation in the current public surface.
- `Agda-locally-proved`: discharged inside the Agda pedagogical companion surface without relying on Agda postulates.
- `Agda-postulated but Lean-backed`: still explicit as an Agda postulate, but closed by Lean or an atlas-backed Lean-backed claim in this repo.
- `empirical`: implemented and regression-tested here, but not promoted to theorem status.
- `open`: tracked as an unresolved claim boundary or interface question, not an established result.
<!-- PROOF_SYSTEM_LEGEND_END -->

## Claim Status Tags

- `classical`: standard mathematics used here as background.
- `reproved-here`: a classical result with an explicit repo proof or formal theorem.
- `implemented-here`: a standard reformulation packaged here as code.
- `empirical`: observed and tested, but not promoted to theorem status.
- `open`: tracked here as an unresolved claim or interface question, not an established result.

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

## Claim Table

<!-- CLAIM_TABLE_START -->
| Claim ID | Status | Exact Statement | Repo Evidence |
|----------|--------|-----------------|---------------|
| `series_q_weighted_identity` | `reproved-here` | For a good block coordinate with B = qM + k, 0 <= k < M, and B > M, we have 1/M = q/(B-k) = Σ_{j>=0} qk^j / B^(j+1). | [OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [test_geometric_series.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_geometric_series.py) |
| `power_order_formula` | `classical` | If r = ord_n(a), then ord_n(a^m) = r / gcd(r, m). | [analysis.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/analysis.py), [test_stride_classification.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_stride_classification.py) |
| `qr_stride_classification` | `reproved-here` | For an odd prime p and h = (p-1)/2, the stride m is QR-generating for base B exactly when ord_p(B) / gcd(ord_p(B), m) = h. Therefore QR-generating strides exist iff ord_p(B) is h or 2h, and their count is φ(h). | [QuadraticResidues.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/QuadraticResidues.lean), [test_stride_classification.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_stride_classification.py) |
| `digit_periodicity` | `reproved-here` | For an odd prime p and a base B coprime to p, the base-B digits of 1/p are periodic with period ord_p(B). At each step, the digit is the Euclidean quotient in B*r_n = d_n*p + r_{n+1}. | [Digits.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Digits.lean), [AGDA_CORRESPONDENCE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/AGDA_CORRESPONDENCE.md), [ci_checks.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/ci_checks.py) |
| `signed_bridge_recurrence` | `reproved-here` | If a prime denominator satisfies B^k ≡ ±d (mod p), then the remainder orbit obeys r[n+k] = (±d)r[n]. Consequently r[n+2k] = d^2 r[n], so the sign always cancels after two stride steps. | [SignedBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/SignedBridge.lean), [PAdicBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/PAdicBridge.lean), [ci_checks.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/ci_checks.py), [README.md](/Users/mikepurvis/other/quadratic-residue-reptends/README.md) |
| `bridge_block_value_periodicity` | `reproved-here` | For a bridge coordinate with B^k ≡ d (mod p), the block values at positions j*k are exactly d^j in ZMod p. Therefore the block sequence is periodic with period ord_p(d). | [PAdicBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/PAdicBridge.lean), [Bridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Bridge.lean), [ci_checks.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/ci_checks.py), [README.md](/Users/mikepurvis/other/quadratic-residue-reptends/README.md) |
| `crt_period_lcm` | `classical` | If M = Π p_i^{e_i} is coprime to the base B, then ord_M(B) is the least common multiple of the local orders ord_{p_i^{e_i}}(B). | [CompositePeriod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositePeriod.lean), [composite.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py), [test_composite_crt.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_composite_crt.py) |
| `preperiod_from_base_factors` | `classical` | For denominator N and base b = Π p_i^{f_i}, the preperiod length is max_i ceil(v_{p_i}(N)/f_i); stripping those base factors leaves the purely periodic modulus M. | [composite.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [Preperiod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Preperiod.lean), [CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean), [test_composite_crt.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_composite_crt.py) |
| `carry_window_transducer` | `implemented-here` | For a finite coefficient word c_0, ..., c_{L-1}, carry propagation can be modeled by a deterministic transducer whose state is the incoming carry from less significant blocks. | [CarryTransducer.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryTransducer.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py) |
| `small_k_visibility_heuristic` | `empirical` | Small k, and especially q = 1, tends to postpone visible carry interactions and make the early block skeleton easier to read. | [search.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/search.py), [test_search_datasets.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_search_datasets.py) |
| `positive_q_good_modes` | `reproved-here` | A mode m only gives a usable q-weighted block coordinate when B = base^m exceeds the periodic modulus M, so q = (B-k)/M is positive. | [OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [test_geometric_series.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_geometric_series.py) |
| `incoming_carry_position_formula` | `reproved-here` | For a block coordinate B = qN + k with 0 < k < B, the incoming carry into block j of the raw coefficient stream qk^j equals floor(qk^(j+1)/(B-k)). Therefore the first incoming-carry position is the least j with qk^(j+1) >= B-k. | [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/visibility.py), [CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py) |
| `same_core_threshold_shift_interval` | `reproved-here` | Fix a block coordinate with shared B and k, and compare an actual denominator to its stripped periodic core. If k^s <= (q_core / q_actual) < k^(s+1), then the incoming-carry and local-overflow thresholds, and therefore the first visible mismatch boundary, for the core occur earlier by either s or s+1 blocks. When q_core / q_actual = k^s exactly, the shift is exactly s blocks. In the non-power interval case, Lean also packages scaled-raw-coefficient sufficient criteria for the lower and upper endpoint labels at fixed boundary data and propagates aligned lower/upper labels to the first visible mismatch boundary. | [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean), [visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/visibility.py), [CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py) |
| `small_k_visibility_threshold` | `open` | There is a sharp arithmetic criterion, in terms of q, k, B, and the period data, for the minimal stabilization lookahead and the remaining global visibility behavior beyond the now-implemented incoming-carry and raw-prefix boundary formulas. | [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean), [visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/visibility.py), [CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py) |
| `carry_dfa_factorization` | `open` | The long-division DFA factors canonically into a remainder-orbit system together with a carry transducer for all coprime bases and moduli. | [CarryTransducer.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryTransducer.lean), [CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean), [transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py), [CARRY_TRANSDUCER.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRY_TRANSDUCER.md), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py) |
<!-- CLAIM_TABLE_END -->

<!-- PROOF_STATUS_FOOTER_START -->
Use [DISCOVERIES.md](/Users/mikepurvis/other/quadratic-residue-reptends/DISCOVERIES.md) for exploratory context and [docs/ROADMAP.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/ROADMAP.md) for implementation follow-through on these open items.

Machine-readable backing lives in [claim_registry.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/claim_registry.json).
<!-- PROOF_STATUS_FOOTER_END -->

## Track 5 Notes

<!-- PROOF_STATUS_TRACK_FIVE_NOTES_START -->
- [QRTour/QuadraticResidues.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/QuadraticResidues.lean) now formalizes the QR-generator power-count theorem `qrGenerator_pow_count_eq_totient`, which proves the `φ((p-1)/2)` count for powers of a fixed QR generator.
- The same Lean module now closes the base-level stride-count reduction via the full-order reduction lemmas and `base_qrGenerator_pow_count_eq_totient`, so the `ord_p(B) ∈ {h, 2h}` classification is now fully formalized at the theorem level.
- [QRTour/Digits.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Digits.lean) now carries the digit/remainder Euclidean equation and the exact digit periodicity theorem, so digit periodicity is no longer just implicit Lean support.
- [QRTour/SignedBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/SignedBridge.lean) now carries the signed bridge recurrence theorem, so the plus/minus bridge package and the `2k` sign-cancellation law are part of the public Lean claim surface.
- [QRTour/PAdicBridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/PAdicBridge.lean) now carries the bridge block-value periodicity claim, so the block-value geometric sequence and its `ord_p(d)` periodicity are no longer just analogy-level support.
- [QRTour/CompositePeriod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositePeriod.lean) now formalizes the finite-product order theorem `orderOf_pi`, the pairwise CRT theorem `orderOf_unitsChineseRemainder`, and the finite prime-power CRT theorem `orderOf_unitsEquivPrimePowers`.
- [QRTour/Preperiod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Preperiod.lean) now formalizes both the local valuation theorem `preperiodPrimeSteps_le_iff` and the global base-prime-support maximum `preperiodSteps`, including `preperiodSteps_le_of_local_bounds` and `basePrimeSupportFactor_dvd_base_pow_preperiodSteps`.
- [QRTour/Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean) now formalizes the exact fixed-window gap certificate, proves it is equivalent to visible-prefix agreement at fixed `(requestedBlocks, lookaheadBlocks)`, derives the necessary tail-mass lower bound beneath that certificate, and transports the certificate to larger lookahead windows once a visible prefix has stabilized.
- [QRTour/CarryComparison.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryComparison.lean) now packages aligned finite carry/remainder traces, proves certified finite output agreement under the exact fixed-window certificate, lifts the generic certificate-transport layer to larger visible windows, consumes the exact same-core `k^s` transport theorem to reprove shifted visible-word/output agreement from stripped-core certificates, and now also extracts exact finite state-alignment records with observed state-pair projections, local carry-balance and remainder-balance equations at each aligned position, exact finite-window functional criteria for the observed remainder-to-carry and carry-to-remainder state-pair lists, finite transition-compatibility theorems under those criteria, and explicit finite conflict lemmas refuting them when the observed pair list disagrees.
- [QRTour/CompositeVisibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositeVisibility.lean) now packages same-core families for actual denominators versus stripped periodic cores using the preperiod factor layer, including exact quotient-scaling, exact/lower/upper endpoint labels, scaled-raw-coefficient sufficient criteria for the non-power interval endpoints, near-denominator coordinate-selection criteria, exact same-core transport of the first visible mismatch boundary in the `k`-power regime, and exact same-core transport of the raw tail-mass lower-bound inequality, the shifted coarse `k^(n+L) < modulus` sufficient condition, and the exact fixed-window lookahead certificate itself between the stripped core at `(n, L)` and the actual denominator at `(n + s, L)`.
- The stripped-periodic-modulus statement in the composite pipeline remains classical/computational in the repo; Lean now covers the finite prime-power CRT order theorem, the max-over-base-primes preperiod step count, the stripping-factor divisibility layer, and the same-core family packaging built on top of that exact arithmetic.
<!-- PROOF_STATUS_TRACK_FIVE_NOTES_END -->
