# Observability Problems Ledger

Status: ranked research agenda. This document is a problem-selection tool, not a
proof-status atlas and not a registry surface. It should help decide which bold
observability questions deserve Lean work, wider search, or external feedback.

The current organizing thesis is that positional notation is an observation
instrument for arithmetic dynamics. The exact source signal comes from the
q-weighted identity

```text
1/N = q/(B-k) = Σ q*k^j / B^(j+1)
```

for a good block coordinate `B = qN + k`, `0 <= k < N`, and `B > N`. The carry
layer is the finite normalization boundary between that raw coefficient signal
and the displayed block readout.

This ledger keeps the two public global frontiers explicitly open:
`small_k_visibility_threshold` and `carry_dfa_factorization`.

## Ranking Rules

Prioritize a problem when it has all four properties:

- A precise finite factor-through statement.
- Existing export rows that can nominate examples and counterexamples.
- A small Lean theorem or theorem schema that could land before a global claim.
- A clear stop condition that prevents theorem-level overclaiming.

De-prioritize a problem when it only adds more examples without improving the
formal vocabulary, search criterion, or atlas discipline.

## P1. Positive Reconstruction Criterion

Status: `implemented-here` finite exemplars plus `empirical` family frontier.

Core question:

When do raw coefficients `qk^j` factor through the observed finite
`remainderIn` state on a requested state-alignment window?

Current evidence:

- Source-pinned finite hooks now include `47`, `49`, `71`, `97`, `98`, `142`,
  `170`, `299`, and `996`.
- The newest source-pinned hook is
  `QRTour.FutureBase7N170.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
  for `(base, N, m, B, q, k, L, gap) =
  (7, 170, 3, 343, 2, 3, 1, 255)`.
- The first unpinned emitted no-collision seed is
  `(base, N, m, B, q, k, L, gap) =
  (7, 340, 3, 343, 1, 3, 1, 299)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 49, 147]`.
  Because it shares `(base, B, k) = (7, 343, 3)` with the source-pinned
  `N = 170` hook, Lean now proves the finite divisor-family criterion, and the
  current decision is
  `use_lean_proved_family_criterion_before_source_pinning_more_examples`.
- The previous source-unpinned and family-uncovered emitted no-collision seed,
  `(base, N, m, B, q, k, L, gap) =
  (10, 997, 3, 1000, 1, 3, 1, 439)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 729, 193]`, is now
  source-pinned as
  `QRTour.FutureBase10N997.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The previous source-unpinned and family-uncovered emitted no-collision seed,
  `(30, 897, 2, 900, 1, 3, 1, 639)`, is now covered by the finite base-30
  divisor-family criterion
  `QRTour.Base30K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
  The proof-covered family moduli are `[23, 69, 299, 897]`, and the pair hook
  `QRTour.Base30K3PositiveReconstruction.n299_n897_powerResidues_nodup_eight_pair`
  keeps the original `299`/`897` signal visible.
- The previous base-10 sibling seed
  `(10, 498, 3, 1000, 2, 4, 1, 928)` is now covered by the finite base-10,
  stride-3, `k = 4` divisor-family criterion
  `QRTour.Base10K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
  `QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`, and
  `QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
  The proof-covered family moduli are `[83, 166, 249, 332, 498, 996]`, and
  `QRTour.Base10K4PositiveReconstruction.n498_n996_powerResidues_nodup_eight_pair`
  keeps the original `498`/`996` signal visible. The smaller divisors
  `[1, 2, 3, 4, 6, 12]` remain outside this finite eight-entry
  no-collision criterion.
- The previous standalone/order-boundary seed
  `(base, N, m, B, q, k, L, gap) =
  (12, 575, 3, 1728, 3, 3, 1, 1053)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 154, 462]`.
  It is now source-pinned as
  `QRTour.FutureBase12N575.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
  with sibling functional theorem
  `QRTour.FutureBase12N575.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  with no-collision witness
  `QRTour.FutureBase12N575.coordinate_remainderK_powerResidues_nodup_eight`.
- The current source-unpinned and family-uncovered emitted no-collision seed is
  `(base, N, m, B, q, k, L, gap) =
  (12, 75, 3, 1728, 23, 3, 1, 1161)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 6, 18, 54, 12]`.
  It is now covered by
  `QRTour.Base12K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
  `QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`, and
  `QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
  The proof-covered family moduli are `[23, 25, 69, 75, 115, 345, 575, 1725]`,
  and `QRTour.Base12K3PositiveReconstruction.n75_n575_powerResidues_nodup_eight_pair`
  keeps the original `75`/`575` signal visible.
- The previous standalone/order-boundary seed
  `(base, N, m, B, q, k, L, gap) =
  (7, 1199, 4, 2401, 2, 3, 1, 1284)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 729, 988]`,
  is now source-pinned as
  `QRTour.FutureBase7N1199.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
  with sibling functional theorem
  `QRTour.FutureBase7N1199.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`
  and no-collision hook
  `QRTour.FutureBase7N1199.coordinate_remainderK_powerResidues_nodup_eight`.
- The previous standalone/order-boundary seed
  `(base, N, m, B, q, k, L, gap) =
  (10, 294, 4, 10000, 34, 4, 1, 1776)`, with `preperiod_digits = 1`,
  `periodic_modulus = 147`, and
  `remainder_power_residue_window = [1, 4, 16, 64, 256, 142, 274, 214]`,
  is now source-pinned as
  `QRTour.FutureBase10N294.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
  with sibling functional theorem
  `QRTour.FutureBase10N294.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`
  and no-collision hook
  `QRTour.FutureBase10N294.coordinate_remainderK_powerResidues_nodup_eight`.
- The previous base-7 sibling seed
  `(base, N, m, B, q, k, L, gap) =
  (7, 109, 4, 2401, 22, 3, 1, 2119)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 81, 25, 75, 7]`.
  It is now covered by
  `QRTour.Base7Stride4K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
  `QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`, and
  `QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
  The proof-covered family moduli are `[109, 218, 1199, 2398]`, and
  `QRTour.Base7Stride4K3PositiveReconstruction.n109_n1199_powerResidues_nodup_eight_pair`
  keeps the original `109`/`1199` signal visible. The smaller divisors
  `[1, 2, 11, 22]` remain outside this finite eight-entry no-collision criterion.
- The previous standalone/order-boundary seed
  `(base, N, m, B, q, k, L, gap) =
  (7, 46, 2, 49, 1, 3, 2, 2171)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 35, 13, 39, 25]`.
  It is now source-pinned as
  `QRTour.FutureBase7N46.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`,
  with sibling functional theorem
  `QRTour.FutureBase7N46.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two`
  and no-collision hook
  `QRTour.FutureBase7N46.coordinate_remainderK_powerResidues_nodup_eight`.
- The previous standalone/order-boundary seed
  `(base, N, m, B, q, k, L, gap) =
  (7, 141, 4, 2401, 17, 4, 1, 2353)`, with
  `remainder_power_residue_window = [1, 4, 16, 64, 115, 37, 7, 28]`.
  It is now source-pinned as
  `QRTour.FutureBase7N141.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
  with sibling functional theorem
  `QRTour.FutureBase7N141.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`
  and no-collision hook
  `QRTour.FutureBase7N141.coordinate_remainderK_powerResidues_nodup_eight`.
- The previous source-unpinned same-base/block-remainder seed
  `(base, N, m, B, q, k, L, gap) =
  (10, 714, 4, 10000, 14, 4, 1, 2496)` is now covered by the base-10,
  stride-4, `k = 4` finite divisor-family theorem; its
  `remainder_power_residue_window = [1, 4, 16, 64, 256, 310, 526, 676]`;
  `QRTour.Base10Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
  the proof-covered moduli are
  `[49, 98, 119, 147, 196, 238, 294, 357, 476, 588, 714, 833]`, with pair hook
  `QRTour.Base10Stride4K4PositiveReconstruction.n294_n714_powerResidues_nodup_eight_pair`.
- The previous source-unpinned and family-uncovered emitted no-collision seed is
  `(base, N, m, B, q, k, L, gap) =
  (12, 73, 4, 20736, 284, 4, 1, 8704)`, with
  `remainder_power_residue_window = [1, 4, 16, 64, 37, 2, 8, 32]`.
  Lean now covers this same-base/block-remainder lane through
  `QRTour.Base12Stride4K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
  `QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
  and
  `QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
  The proof-covered moduli are `[71, 73, 142, 146, 284, 292, 5183, 10366, 20732]`,
  with pair hook
  `QRTour.Base12Stride4K4PositiveReconstruction.n73_n146_powerResidues_nodup_eight_pair`.
- The source-pinned sibling remains:
  `(base, N, m, B, q, k, L, gap) =
  (12, 146, 4, 20736, 142, 4, 1, 4352)`, with
  `remainder_power_residue_window = [1, 4, 16, 64, 110, 2, 8, 32]`.
  It has `preperiod_digits = 1` and `periodic_modulus = 73`, and is now
  source-pinned through
  `QRTour.FutureBase12N146.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase12N146.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  and
  `QRTour.FutureBase12N146.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The previous source-unpinned and family-uncovered emitted no-collision seed is
  `(base, N, m, B, q, k, L, gap) =
  (10, 769, 4, 10000, 13, 3, 1, 4707)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 729, 649]`.
  It has `preperiod_digits = 0` and `periodic_modulus = 769`, and is now
  source-pinned through
  `QRTour.FutureBase10N769.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase10N769.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  and
  `QRTour.FutureBase10N769.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The previous source-unpinned and family-uncovered emitted no-collision seed is
  `(base, N, m, B, q, k, L, gap) =
  (7, 345, 6, 117649, 341, 4, 1, 5534)`, with
  `remainder_power_residue_window = [1, 4, 16, 64, 256, 334, 301, 169]`.
  It has `preperiod_digits = 0` and `periodic_modulus = 345`, and is now
  source-pinned through
  `QRTour.FutureBase7N345.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase7N345.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  and
  `QRTour.FutureBase7N345.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The previous source-unpinned and family-uncovered emitted no-collision seed is
  `(base, N, m, B, q, k, L, gap) =
  (7, 465, 6, 117649, 253, 4, 1, 7901)`, with
  `remainder_power_residue_window = [1, 4, 16, 64, 256, 94, 376, 109]`.
  Lean now covers this same-base/block-remainder lane through
  `QRTour.Base7Stride6K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
  `QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
  and
  `QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
- The previous standalone/order-boundary emitted no-collision seed is now
  source-pinned:
  `(base, N, m, B, q, k, L, gap) =
  (7, 542, 5, 16807, 31, 5, 1, 8472)`, with
  `remainder_power_residue_window = [1, 5, 25, 125, 83, 415, 449, 77]`.
  Lean covers it through
  `QRTour.FutureBase7N542.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase7N542.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  and
  `QRTour.FutureBase7N542.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The previous standalone/order-boundary emitted no-collision seed is now
  source-pinned:
  `(base, N, m, B, q, k, L, gap) =
  (12, 47, 2, 144, 3, 3, 2, 9639)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 34, 8, 24, 25]`.
  Lean covers it through
  `QRTour.FutureBase12N47.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase12N47.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two`,
  and
  `QRTour.FutureBase12N47.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`.
- The previous same-base/block-remainder emitted no-collision seed is now
  family-covered:
  `(base, N, m, B, q, k, L, gap) =
  (12, 141, 2, 144, 1, 3, 2, 10125)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 81, 102, 24, 72]`.
  Lean covers this base-12 stride-2 `k = 3` lane through
  `QRTour.Base12Stride2K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
  `QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
  and
  `QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
  The proof-covered moduli are `[47, 141]`, and
  `QRTour.Base12Stride2K3PositiveReconstruction.n47_n141_powerResidues_nodup_eight_pair`
  keeps the `47`/`141` signal visible.
- The previous standalone/order-boundary emitted no-collision seed is now
  source-pinned:
  `(base, N, m, B, q, k, L, gap) =
  (30, 794, 3, 27000, 34, 4, 1, 12776)`, with `preperiod_digits = 1`,
  `periodic_modulus = 397`, and
  `remainder_power_residue_window = [1, 4, 16, 64, 256, 230, 126, 504]`.
  Lean covers it through
  `QRTour.FutureBase30N794.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase30N794.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  and
  `QRTour.FutureBase30N794.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The previous source-unpinned and theorem-uncovered emitted no-collision seed
  is now family-covered:
  `(base, N, m, B, q, k, L, gap) =
  (30, 397, 3, 27000, 68, 4, 1, 25552)`, with
  `remainder_power_residue_window = [1, 4, 16, 64, 256, 230, 126, 107]`.
  Lean covers it through
  `QRTour.Base30Stride3K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
  `QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
  and
  `QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
  The proof-covered moduli are `[397, 794, 1588, 6749, 13498, 26996]`, and
  `QRTour.Base30Stride3K4PositiveReconstruction.n397_n794_powerResidues_nodup_eight_pair`
  keeps the `397`/`794` signal visible, while divisors
  `[1, 2, 4, 17, 34, 68]` remain outside this finite eight-entry
  no-collision criterion.
- The previous source-unpinned and theorem-uncovered emitted no-collision seed
  is now source-pinned:
  `(base, N, m, B, q, k, L, gap) =
  (7, 113, 3, 343, 3, 4, 2, 13444)`, with
  `remainder_power_residue_window = [1, 4, 16, 64, 30, 7, 28, 112]`.
  Lean covers it through
  `QRTour.FutureBase7N113.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase7N113.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two`,
  and
  `QRTour.FutureBase7N113.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`.
- The previous source-unpinned and theorem-uncovered emitted no-collision seed
  is now source-pinned:
  `(base, N, m, B, q, k, L, gap) =
  (12, 691, 4, 20736, 30, 6, 1, 20736)`, with
  `remainder_power_residue_window = [1, 6, 36, 216, 605, 175, 359, 81]`.
  Lean covers it through
  `QRTour.FutureBase12N691.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase12N691.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  and
  `QRTour.FutureBase12N691.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The previous source-unpinned and theorem-uncovered emitted no-collision seed
  is now source-pinned:
  `(base, N, m, B, q, k, L, gap) =
  (10, 578, 5, 100000, 173, 6, 1, 26432)`, with
  `remainder_power_residue_window = [1, 6, 36, 216, 140, 262, 416, 184]`.
  Lean covers it through
  `QRTour.FutureBase10N578.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase10N578.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  and
  `QRTour.FutureBase10N578.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The previous source-unpinned and theorem-uncovered emitted no-collision seed
  is now source-pinned:
  `(base, N, m, B, q, k, L, gap) =
  (10, 277, 5, 100000, 361, 3, 1, 31479)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 175, 248]`.
  Lean covers it through
  `QRTour.FutureBase10N277.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase10N277.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  and
  `QRTour.FutureBase10N277.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The previous source-unpinned and theorem-uncovered emitted no-collision seed
  is now source-pinned:
  `(base, N, m, B, q, k, L, gap) =
  (7, 669, 7, 823543, 1231, 4, 1, 32398)`, with
  `remainder_power_residue_window = [1, 4, 16, 64, 256, 355, 82, 328]`.
  Lean covers it through
  `QRTour.FutureBase7N669.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase7N669.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  and
  `QRTour.FutureBase7N669.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The previous source-unpinned and theorem-uncovered emitted no-collision seed
  is now source-pinned:
  `(base, N, m, B, q, k, L, gap) =
  (7, 71, 6, 117649, 1657, 2, 1, 46404)`, with
  `remainder_power_residue_window = [1, 2, 4, 8, 16, 32, 64, 57]`.
  Lean covers it through
  `QRTour.FutureBase7N71.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase7N71.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  and
  `QRTour.FutureBase7N71.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The previous source-unpinned and theorem-uncovered emitted no-collision seed
  is now source-pinned:
  `(base, N, m, B, q, k, L, gap) =
  (7, 118, 6, 117649, 997, 3, 1, 47027)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 81, 7, 21, 63]`.
  Lean covers it through
  `QRTour.FutureBase7N118.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase7N118.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  and
  `QRTour.FutureBase7N118.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The widened-atlas `118`/`997` sibling lane is now family-covered:
  it covers
  `(7, 997, 6, 117649, 118, 3, 1, 49345)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 729, 193]`.
  `QRTour.Base7Stride6K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`
  proves the base-7, stride-6, `k = 3` finite divisor-family criterion for
  moduli `[59, 118, 997, 1994, 58823, 117646]`, and
  `QRTour.Base7Stride6K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`
  turns that no-collision criterion into finite factor-through reconstruction.
  The pair hook
  `QRTour.Base7Stride6K3PositiveReconstruction.n118_n997_powerResidues_nodup_eight_pair`
  keeps the concrete lane visible; divisors `[1, 2]` remain outside this
  finite eight-entry criterion.
- The base-10 stride-5 `289`/`578` sibling lane is now family-covered:
  it covers
  `(10, 289, 5, 100000, 346, 6, 1, 52864)`, with
  `remainder_power_residue_window = [1, 6, 36, 216, 140, 262, 127, 184]`.
  `QRTour.Base10Stride5K6PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`
  proves the base-10, stride-5, `k = 6` finite divisor-family criterion for
  moduli `[17, 34, 173, 289, 346, 578, 2941, 5882, 49997, 99994]`, and
  `QRTour.Base10Stride5K6PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`
  turns that no-collision criterion into finite factor-through reconstruction.
  The pair hook
  `QRTour.Base10Stride5K6PositiveReconstruction.n289_n578_powerResidues_nodup_eight_pair`
  keeps the concrete lane visible; divisors `[1, 2]` remain outside this
  finite eight-entry criterion.
- The previous source-unpinned and theorem-uncovered emitted no-collision seed
  is now source-pinned:
  `(base, N, m, B, q, k, L, gap) =
  (12, 226, 5, 248832, 1101, 6, 1, 62208)`, with
  `preperiod_digits = 1`, `periodic_modulus = 113`, and
  `remainder_power_residue_window = [1, 6, 36, 216, 166, 92, 100, 148]`.
  Lean covers it through
  `QRTour.FutureBase12N226.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase12N226.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  and
  `QRTour.FutureBase12N226.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The previous source-unpinned and theorem-uncovered emitted no-collision seed is
  `(base, N, m, B, q, k, L, gap) =
  (7, 338, 3, 343, 1, 5, 2, 64744)`, with
  `remainder_power_residue_window = [1, 5, 25, 125, 287, 83, 77, 47]`.
  Lean covers it through
  `QRTour.FutureBase7N338.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase7N338.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two`,
  and
  `QRTour.FutureBase7N338.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`.
- The previous source-unpinned and theorem-uncovered emitted no-collision seed
  has now graduated through the no-wrap sufficient criterion:
  `(base, N, m, B, q, k, L, gap) =
  (12, 149, 5, 248832, 1670, 2, 1, 70144)`, with
  `remainder_power_residue_window = [1, 2, 4, 8, 16, 32, 64, 128]`.
  Lean exposes `QRTour.FutureBase12N149.coordinate_remainderK_pow_lt_modulus_eight`,
  `QRTour.FutureBase12N149.coordinate_remainderK_powerResidues_nodup_eight`,
  `QRTour.FutureBase12N149.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
  and
  `QRTour.FutureBase12N149.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
- The previous source-unpinned and theorem-uncovered emitted no-collision seed
  is now family-covered:
  `(base, N, m, B, q, k, L, gap) =
  (12, 289, 5, 248832, 861, 3, 1, 74115)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 151, 164]`.
  Lean proves the base-12 stride-5 `k = 3` finite divisor-family criterion
  through
  `QRTour.Base12Stride5K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
  `QRTour.Base12Stride5K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
  and
  `QRTour.Base12Stride5K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
  the proof-covered moduli are
  `[17, 41, 51, 119, 123, 287, 289, 357, 697, 861, 867, 2023, 2091, 4879, 6069, 11849, 14637, 35547, 82943, 248829]`,
  with pair hook
  `QRTour.Base12Stride5K3PositiveReconstruction.n289_n861_powerResidues_nodup_eight_pair`
  and failed divisors `[7, 21]`.
- The previous source-unpinned and theorem-uncovered emitted no-collision seed
  is now family-covered:
  `(base, N, m, B, q, k, L, gap) =
  (10, 641, 5, 100000, 156, 4, 1, 76384)`, with
  `remainder_power_residue_window = [1, 4, 16, 64, 256, 383, 250, 359]`.
  Lean proves the base-10 stride-5 `k = 4` finite divisor-family criterion
  through
  `QRTour.Base10Stride5K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
  `QRTour.Base10Stride5K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
  and
  `QRTour.Base10Stride5K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
  the proof-covered moduli are
  `[641, 1282, 1923, 2564, 3846, 7692, 8333, 16666, 24999, 33332, 49998, 99996]`,
  with pair hook
  `QRTour.Base10Stride5K4PositiveReconstruction.n641_n1282_powerResidues_nodup_eight_pair`
  and failed good divisors `[6, 12, 13, 26, 39, 52, 78, 156]`.
- The current source-unpinned and theorem-uncovered emitted no-collision seed is
  `(base, N, m, B, q, k, L, gap) =
  (10, 361, 5, 100000, 277, 3, 1, 82603)`, with
  `remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 7, 21]`.
  Its source-pinned same-base/block-remainder sibling is
  `(10, 277, 5, 100000, 361, 3, 1, 31479)`, so the current default decision is
  `pursue_family_criterion_before_source_pinning_more_examples`.
- The finite power-residue no-collision criterion
  `finite_remainder_power_residue_no_collision` is now exported by the
  observability program atlas.
- The stronger finite no-wrap sufficient criterion
  `finite_remainder_power_residue_no_wrap` is also exported with
  `remainder_power_unreduced_window` and
  `positive_reconstruction_hyp_remainder_power_residue_no_wrap`.

Lean surface:

- `List.functionalOnFst_of_map_fst_nodup`
- `BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderIn_nodup`
- `BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderIn_nodup`
- `BlockCoordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup`
- `BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup`
- `BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup`
- `BlockCoordinate.remainderK_powerResidues_nodup_of_remainderK_pow_lt_modulus`
- `BlockCoordinate.stateAlignments_remainderIn_nodup_of_remainderK_pow_lt_modulus`
- `BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_pow_lt_modulus`
- `BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_pow_lt_modulus`

Export surface:

```bash
search-reptends observability-program-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 50
```

Key fields:

- `positive_reconstruction_source_pinned`
- `positive_reconstruction_factor_through_theorem`
- `finite_remainder_power_residue_no_collision`
- `remainder_power_residue_window`
- `positive_reconstruction_hyp_remainder_power_residue_window_injective`
- `first_unpinned_positive_reconstruction_tuple`
- `first_unpinned_positive_reconstruction_family_seed_tuples`
- `recommended_positive_reconstruction_decision`
- `positive_reconstruction_family_criterion_status`
- `positive_reconstruction_family_factor_through_theorem`
- `first_uncovered_positive_reconstruction_tuple`
- `first_uncovered_positive_reconstruction_decision`

Next task:

The first same-base/block-remainder family has now been proved as finite-window
support: `QRTour.Base7K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`
shows that the base-7, stride-3 moduli `[17, 34, 68, 85, 170, 340]` have a
collision-free eight-entry `k^j % N` window, and
`QRTour.Base7K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`
turns that arithmetic criterion into finite raw-coefficient reconstruction.
The atlas therefore reports
`positive_reconstruction_family_criterion_status =
lean_proved_explicit_divisor_family_criterion`. After excluding source-pinned
and family-covered rows, it now reports
`first_uncovered_positive_reconstruction_tuple =
[10, 361, 5, 100000, 277, 3, 1, 82603]` and recommends
`prove_or_reject_same_base_block_remainder_power_no_collision_family`.

Stop conditions:

- Stop adding source-pinned examples when the next proof repeats the same
  eight-entry `Nodup` argument without improving the arithmetic criterion.
- Stop theorem promotion if the criterion only proves a finite window and does
  not classify a family; keep it marked as finite-window support.

## P2. Observability Target Lattice

Status: `empirical` target split plus Lean-backed generic factor-through spine.

Core question:

Which finite signals are determined by which observations, and what implication
or separation structure exists among the targets?

Current evidence:

- The target split currently tracks `raw_coefficient_nat`,
  `coefficient_mod_block_base`, `carried_block_value`, `carry_state`,
  `remainder_state`, and `displayed_prefix`.
- Composite68 shows raw coefficient information loss that can be hidden by
  carried output.
- Shape13/K4 shows a mod-stable carry-loss pattern: coefficient modulo `B` and
  carried output can remain functional while carry-state observability fails.

Lean surface:

- `FactorsThrough`
- `FactorsThrough.eq_of_obs_eq`
- `not_factorsThrough_of_collision`
- `List.functionalOnFst_iff_factorsThrough_memberSubtype`
- `BlockCoordinate.StateAlignmentCertifiedConflict.not_remainderToCoefficientFactorsThrough`

Export surface:

```bash
search-reptends observability-target-split --max 1200 --bases 7,10,12,30 --blocks 8 --top 50
search-reptends observability-target-signatures --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

Next task:

Add a small implication/separation table to the export: for each row, report
which targets are functional, which are obstructed, and which target is the
first information-loss boundary.

Stop conditions:

- Do not describe target implications as universal until Lean proves them.
- Treat `displayed_prefix` as a window-level certificate, not a pointwise
  `FactorsThrough` map.

## P3. Base As Observation Instrument

Status: `empirical` instrument comparison with proof-backed seeds.

Core question:

How does changing the base alter what an observer can reconstruct from the same
source arithmetic?

Current evidence:

- Shape17/K4 connects `N = 17`, `N = 34`, and `N = 68` through proof-backed
  same-core shift hooks.
- Composite68 appears in base `10` and base `30`, with the same finite hidden
  coefficient conflict shape.
- Shape187/K188 has base-`30` proof-covered seeds and base-`10`/base-`12`
  candidate rows.

Lean surface:

- `QRTour.Shape17K4.base10_core17_to_composite68_conflict_shift_exact`
- `QRTour.Shape17K4.base10_core17_to_double34_conflict_shift_scaled`
- `BlockCoordinate.samePositionIdempotent_hiddenCarryBlockValue`
- `QRTour.Shape187K188.base30_default_samePositionIdempotent_hiddenCarryBlockValue_one_two_pair`

Export surface:

```bash
search-reptends observability-instrument-compare --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
search-reptends observability-shape17-k4-family --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
search-reptends observability-shape187-k188-family --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

Next task:

Group instrument-comparison rows by source symmetry shape and classify whether
each base hides, reveals, shifts, or reconstructs the signal.

Stop conditions:

- Do not infer base-invariant structure from one base's finite rows.
- Require either a named Lean instantiation or an explicit
  `same_core_shift_criterion_candidate` / `same_position_scaling_criterion_candidate`
  status before calling a family proof-ready.

## P4. Carry Normalizer As Rational Transduction

Status: `open` theory direction beneath `carry_dfa_factorization`.

Core question:

Is the right global object a one-pass DFA factorization, a rational word
function, a bimachine, or a different canonical transducer decomposition?

Current evidence:

- The finite carry transducer is implemented and Lean-backed.
- Fixed-window carry/remainder output agreement is Lean-backed under explicit
  certificates.
- Counterexamples and obstruction records show that finite output agreement is
  not enough to promote a global state-level factorization.

Lean surface:

- `QRTour.CarryTransducer`
- `QRTour.CarryComparison`
- `QRTour.Factorization`

Export surface:

```bash
search-reptends carry-factorization --max 500 --blocks 8
search-reptends observability-program-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 50
```

Next task:

Write a small comparison note that translates the current finite carry
normalizer into rational-word-function vocabulary, then decide whether the
global `carry_dfa_factorization` target should be split into one-pass and
two-directional transducer variants.

Stop conditions:

- Do not rename or close `carry_dfa_factorization` until a replacement theorem
  target is explicit and registered.
- Do not import external automata vocabulary as proof support; use it only to
  sharpen the open problem.

## P5. Quantitative Observability Margins

Status: `empirical` future lane.

Core question:

After exact functional/nonfunctional classifications are stable, can the repo
measure how much information is lost or how much lookahead is needed for
reconstruction?

Current evidence:

- Existing row builders already expose fiber signatures, exact gap numerators,
  certified lookahead blocks, and target summary signatures.
- Hidden-output conflicts and positive reconstruction rows form natural
  extremes of the same finite factor-through spectrum.

Lean surface:

- None required for V1. This should start as Python/export analysis.

Export surface:

```bash
search-reptends observability-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 50
search-reptends observability-target-signatures --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

Next task:

Add summary fields for collision count, largest fiber size, minimal certified
lookahead among matching rows, and whether the row sits on the obstruction or
positive reconstruction side of the target lattice.

Stop conditions:

- Do not convert numerical margins into theorem claims without a Lean-facing
  exact statement.
- Keep metrics clearly labeled as empirical bounded search.

## Recommended Near-Term Sequence

1. Prove or reject the first arithmetic family criterion behind
   `finite_remainder_power_residue_no_collision`.
2. Add an observability target implication/separation summary to the atlas.
3. Write the rational-transduction comparison note for the carry normalizer.
4. Only then decide whether the next Lean theorem should be reconstruction,
   Shape187/Shape13 classification, or a split of `carry_dfa_factorization`.

The center of gravity should remain: finite factor-through statements first,
family arithmetic second, global transducer claims last.
