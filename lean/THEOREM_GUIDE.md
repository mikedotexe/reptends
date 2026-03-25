# Lean Theorem Guide

Use [docs/PROOF_STATUS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/PROOF_STATUS_ATLAS.md) as the status source of truth for public claims. This note is only a Lean-facing index from current claim IDs to the modules and theorem names that carry them.

## Current Atlas-Backed Lean Surface

| Claim ID | Atlas Status | Lean module | Main theorem names |
|----------|--------------|-------------|--------------------|
| `incoming_carry_position_formula` | `reproved-here` | [QRTour/Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean) | `incomingCarry_formula`, `incomingCarry_pos_iff`, `isFirstIncomingCarryPosition_iff` |
| `same_core_threshold_shift_interval` | `reproved-here` | [QRTour/Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean) | `geometricThreshold_shift_interval`, `geometricThreshold_shift_exact`, `firstIncomingCarryPosition_shift_interval`, `localOverflowBoundary_shift_interval` |
| `series_q_weighted_identity` | `reproved-here` | [QRTour/OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean) | `partialSumQ_eq_finite`, `one_div_modulus_eq_quotientQ_div_gap`, `series_q_weighted_identity` |
| `qr_stride_classification` | `reproved-here` | [QRTour/QuadraticResidues.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/QuadraticResidues.lean) | `pow_isQRGenerator_iff`, `qrGenerator_pow_count_eq_totient`, `base_qrGenerator_pow_count_eq_totient` |
| `crt_period_lcm` | `classical` with Lean backing in repo evidence | [QRTour/CompositePeriod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CompositePeriod.lean) | `orderOf_unitsChineseRemainder`, `orderOf_unitsEquivPrimePowers`, `orderOf_pi` |
| `preperiod_from_base_factors` | `classical` with Lean backing in repo evidence | [QRTour/Preperiod.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Preperiod.lean) | `preperiodPrimeSteps_le_iff`, `preperiodSteps_le_of_local_bounds`, `basePrimeSupportFactor_dvd_base_pow_preperiodSteps` |
| `positive_q_good_modes` | `reproved-here` | [QRTour/OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean) | `quotientQ_eq_gap_div_modulus`, `positive_q_good_modes` |

## Foundational Supporting Modules

These modules are part of the current formal core even when the proof atlas tracks the higher-level claim elsewhere.

| Module | What it supplies |
|--------|------------------|
| [QRTour/OrbitWeave.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/OrbitWeave.lean) | block-coordinate arithmetic for the `q*k^j` series layer and the exact `R = W + F` body/correction decomposition |
| [QRTour/Visibility.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Visibility.lean) | incoming-carry boundaries and same-core threshold-shift laws |
| [QRTour/CarryTransducer.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CarryTransducer.lean) | finite carry-normalization recursion, traced finite runs with per-step Euclidean semantics, canonical base-`B` digits for both the carried body term `W_L` and the emitted prefix integer `B^L / N`, the exact correction identity `B^L / N = W_L + k^L / N`, and finite carry/remainder comparison projections with exact word agreement when `k^L < N` |
| [QRTour/RemainderOrbit.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/RemainderOrbit.lean) | The remainder-orbit theorem family behind the prime QR tour |
| [QRTour/Bridge.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Bridge.lean) | Exact bridge recurrences for `p = B^m - d` style examples |
| [QRTour/CosetStructure.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/CosetStructure.lean) | QR/NQR two-coset structure used by the prime tour narrative |
| [QRTour/Examples.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Examples.lean) | The canonical `(base, p, stride, ord_p(base)) = (10, 97, 2, 96)` worked example |

## Next Exact Frontier

Per [ROADMAP.md](/Users/mikepurvis/other/quadratic-residue-reptends/ROADMAP.md), the next Lean-first frontier is now the sharper remainder/DFA comparison layer on top of the newly landed finite carry-normalization core:

- keep `QRTour/CarryTransducer.lean` honest at the exact current boundary:
  canonical digits for `W_L`, canonical digits for the emitted prefix `B^L / N`,
  and explicit correction-term comparison between them
- sharpen the current exact agreement theorem `k^L < N -> normalized word = emitted word`
  into visibility-style or lookahead-style finite-window criteria
- keep the global `carry_dfa_factorization` claim marked `open` while only formalizing finite-window agreement
- after that, promote the paired carry/remainder trace surface into explicit
  state-comparison theorems before moving to the family-level composite
  integration planned in `QRTour/CompositeVisibility.lean`

That frontier is where the repo moves from the now-lean-backed orbit-weave, visibility, and finite normalization algebra into explicit finite comparisons with long-division output and then into state-level comparison surfaces, still without overreaching into the global factorization conjecture.
