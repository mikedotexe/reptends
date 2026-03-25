# Proof-Status Atlas

This project now treats its public claims as a registry rather than free-form prose.

Status tags:

- `classical`: standard mathematics used here as background.
- `reproved-here`: a classical result with an explicit repo proof or formal theorem.
- `implemented-here`: a standard reformulation packaged here as code.
- `empirical`: observed and tested, but not promoted to theorem status.
- `open`: tracked here as an unresolved claim or interface question, not an established result.

## Registry Summary

<!-- REGISTRY_SUMMARY_START -->
- total claims: 12
- classical: 3
- reproved-here: 5
- implemented-here: 1
- empirical: 1
- open: 2
<!-- REGISTRY_SUMMARY_END -->

<!-- CLAIM_TABLE_START -->
| Claim ID | Status | Exact Statement | Repo Evidence |
|----------|--------|-----------------|---------------|
| `series_q_weighted_identity` | `reproved-here` | For a good block coordinate with B = qM + k, 0 <= k < M, and B > M, we have 1/M = q/(B-k) = Σ_{j>=0} qk^j / B^(j+1). | [OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [test_geometric_series.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_geometric_series.py) |
| `power_order_formula` | `classical` | If r = ord_n(a), then ord_n(a^m) = r / gcd(r, m). | [analysis.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/analysis.py), [test_stride_classification.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_stride_classification.py) |
| `qr_stride_classification` | `reproved-here` | For an odd prime p and h = (p-1)/2, the stride m is QR-generating for base B exactly when ord_p(B) / gcd(ord_p(B), m) = h. Therefore QR-generating strides exist iff ord_p(B) is h or 2h, and their count is φ(h). | [QuadraticResidues.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/QuadraticResidues.lean), [test_stride_classification.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_stride_classification.py) |
| `crt_period_lcm` | `classical` | If M = Π p_i^{e_i} is coprime to the base B, then ord_M(B) is the least common multiple of the local orders ord_{p_i^{e_i}}(B). | [CompositePeriod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositePeriod.lean), [composite.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py), [test_composite_crt.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_composite_crt.py) |
| `preperiod_from_base_factors` | `classical` | For denominator N and base b = Π p_i^{f_i}, the preperiod length is max_i ceil(v_{p_i}(N)/f_i); stripping those base factors leaves the purely periodic modulus M. | [composite.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/composite.py), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [Preperiod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Preperiod.lean), [test_composite_crt.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_composite_crt.py) |
| `carry_window_transducer` | `implemented-here` | For a finite coefficient word c_0, ..., c_{L-1}, carry propagation can be modeled by a deterministic transducer whose state is the incoming carry from less significant blocks. | [CarryTransducer.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryTransducer.lean), [transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py) |
| `small_k_visibility_heuristic` | `empirical` | Small k, and especially q = 1, tends to postpone visible carry interactions and make the early block skeleton easier to read. | [search.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/search.py), [test_search_datasets.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_search_datasets.py) |
| `positive_q_good_modes` | `reproved-here` | A mode m only gives a usable q-weighted block coordinate when B = base^m exceeds the periodic modulus M, so q = (B-k)/M is positive. | [OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean), [orbit_weave.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/orbit_weave.py), [test_geometric_series.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_geometric_series.py) |
| `incoming_carry_position_formula` | `reproved-here` | For a block coordinate B = qN + k with 0 < k < B, the incoming carry into block j of the raw coefficient stream qk^j equals floor(qk^(j+1)/(B-k)). Therefore the first incoming-carry position is the least j with qk^(j+1) >= B-k. | [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/visibility.py), [CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py) |
| `same_core_threshold_shift_interval` | `reproved-here` | Fix a block coordinate with shared B and k, and compare an actual denominator to its stripped periodic core. If k^s <= (q_core / q_actual) < k^(s+1), then the incoming-carry and local-overflow thresholds for the core occur earlier by either s or s+1 blocks. When q_core / q_actual = k^s exactly, the shift is exactly s blocks. | [Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean), [visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/visibility.py), [CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py) |
| `small_k_visibility_threshold` | `open` | There is a sharp arithmetic criterion, in terms of q, k, B, and the period data, for the minimal stabilization lookahead and the remaining global visibility behavior beyond the now-implemented incoming-carry and raw-prefix boundary formulas. | [visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/visibility.py), [CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md), [test_visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_visibility.py) |
| `carry_dfa_factorization` | `open` | The long-division DFA factors canonically into a remainder-orbit system together with a carry transducer for all coprime bases and moduli. | [transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py), [CARRY_TRANSDUCER.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRY_TRANSDUCER.md), [test_carry_transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/tests/test_carry_transducer.py) |
<!-- CLAIM_TABLE_END -->

## Open Claims

These are intentionally tracked in the registry so open questions do not get mixed into theorem-level prose.

<!-- OPEN_CLAIMS_START -->
- `small_k_visibility_threshold` - Exact visibility threshold for carried prefixes
- `carry_dfa_factorization` - Canonical factorization of long division into orbit and carry
<!-- OPEN_CLAIMS_END -->

Use [DISCOVERIES.md](/Users/mikepurvis/other/quadratic-residue-reptends/DISCOVERIES.md) for exploratory context and [docs/ROADMAP.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/ROADMAP.md) for implementation follow-through on these open items.

Machine-readable backing lives in [claim_registry.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/claim_registry.json).

## Track 5 Notes

- [QuadraticResidues.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/QuadraticResidues.lean) now formalizes the QR-generator power-count theorem `qrGenerator_pow_count_eq_totient`, which proves the `φ((p-1)/2)` count for powers of a fixed QR generator.
- The same Lean module now closes the base-level stride-count reduction via the full-order reduction lemmas and `base_qrGenerator_pow_count_eq_totient`, so the `ord_p(B) ∈ {h, 2h}` classification is now fully formalized at the theorem level.
- [CompositePeriod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositePeriod.lean) now formalizes the finite-product order theorem `orderOf_pi`, the pairwise CRT theorem `orderOf_unitsChineseRemainder`, and the finite prime-power CRT theorem `orderOf_unitsEquivPrimePowers`.
- [Preperiod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Preperiod.lean) now formalizes both the local valuation theorem `preperiodPrimeSteps_le_iff` and the global base-prime-support maximum `preperiodSteps`, including `preperiodSteps_le_of_local_bounds` and `basePrimeSupportFactor_dvd_base_pow_preperiodSteps`.
- The stripped-periodic-modulus statement in the composite pipeline remains classical/computational in the repo; Lean currently covers the finite prime-power CRT order theorem and the max-over-base-primes preperiod step count with its combined divisibility consequence.
