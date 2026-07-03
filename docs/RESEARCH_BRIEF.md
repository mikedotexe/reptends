# Research Brief v0.2: Orbit, Carry, and Observability

Status: shareable research-review brief. Use
[PROOF_STATUS_ATLAS.md](PROOF_STATUS_ATLAS.md) as the claim-status source of
truth, [../lean/THEOREM_GUIDE.md](../lean/THEOREM_GUIDE.md) as the Lean-facing
theorem index, and [OBSERVABILITY_PROBLEMS.md](OBSERVABILITY_PROBLEMS.md) as the
ranked open-problem ledger.

## One-Sentence Thesis

Positional notation is an observation instrument for arithmetic dynamics: the
remainder orbit produces an exact raw coefficient signal, and carry-propagated
block normalization is the boundary where that signal becomes visible, shifted,
collapsed, reconstructed, or hidden.

## Formal Lens

Choose a block base `B = base^m` and write

```text
B = qN + k,   0 <= k < N.
```

In a good mode, meaning `B > N` so `q > 0`, the exact q-weighted identity is

```text
1/N = q/(B-k) = (q/B) * 1/(1-k/B) = Σ q*k^j / B^(j+1).
```

The source signal is therefore the raw coefficient stream `qk^j`; the displayed
base-`B` blocks are produced only after carry-propagated block normalization.
The observability question is finite and factor-through shaped:

```text
FactorsThrough(obs, signal) := exists decode, forall t,
  decode(obs(t)) = signal(t).
```

A hidden coefficient conflict is a finite collision where two positions have
the same observation but unequal raw coefficients. Output-hiding is the
stronger finite fact that the same pair still has equal carried block output.
Positive reconstruction is the dual finite fact: the raw coefficient signal
does factor through the observed finite state data.

## What Is Claimed

The project claims a disciplined, status-tagged contribution: many reptend
phenomena become clearer when the remainder orbit, raw coefficient signal, and
carry normalization instrument are separated.

Registry-backed exact support includes:

| Claim ID | Role in this brief |
|----------|--------------------|
| `series_q_weighted_identity` | proves the exact `qk^j` source signal |
| `positive_q_good_modes` | restricts "good" coordinates to `B > N` |
| `digit_periodicity` | anchors the long-division remainder orbit |
| `qr_stride_classification` | keeps prime QR structure exact and separate |
| `incoming_carry_position_formula` | gives the first carry-boundary arithmetic |
| `same_core_threshold_shift_interval` | formalizes same-core visibility shifts |
| `carry_window_transducer` | implements finite carry normalization |

The broader observability thesis is a research frame, not a new registry claim.

## Lean-Backed Evidence Map

| Lane | Representative Lean surface | Status |
|------|-----------------------------|--------|
| q-weighted block algebra | `QRTour.OrbitWeave` | Lean-backed exact support |
| fixed-window carry and visibility | `QRTour.Visibility`, `QRTour.CarryComparison` | Lean-backed finite support |
| generic finite observability vocabulary | `FactorsThrough`, `not_factorsThrough_of_collision`, `List.functionalOnFst_iff_factorsThrough_memberSubtype` | Lean-backed finite support |
| Composite68 / Shape17 obstruction | `QRTour.Composite68`, `QRTour.Composite68Base30`, `QRTour.Shape17K4` | Lean-backed finite/family-scoped support |
| Shape13 mod-stable carry-loss | `QRTour.Shape13K4` hooks and export fields | finite support plus empirical classifier |
| Shape187/K188 same-position scaling | `QRTour.FutureBase30N374`, `QRTour.FutureBase30N748`, `QRTour.Shape187K188` | Lean-backed seeds plus empirical candidates |
| positive reconstruction exemplars | `QRTour.Prime97`, `QRTour.Composite996`, `QRTour.FutureBase10N98`, `QRTour.FutureBase7N170` | Lean-backed finite exemplars |

The current positive reconstruction lane now has a reusable sufficient criterion:
`finite_remainder_power_residue_no_collision`. It says, at the finite-window
level, that if the full-modulus power-residue window
`k^j % N` is pairwise distinct for the requested state-alignment window, then
the observed `remainderIn` values are pairwise distinct and raw coefficients
factor through the observed finite state data.
The smaller sufficient criterion `finite_remainder_power_residue_no_wrap`
records the clean subcase `1 < k` and `k^j < N` over the requested window; in
that regime `k^j % N` is literally the unreduced power window, so Lean can
derive no-collision without bespoke finite list arithmetic.

The key Lean bridge names are:

- `BlockCoordinate.stateAlignments_remainderIn_nodup_of_remainderK_powerResidues_nodup`
- `BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_powerResidues_nodup`
- `BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_powerResidues_nodup`
- `BlockCoordinate.remainderK_powerResidues_nodup_of_remainderK_pow_lt_modulus`
- `BlockCoordinate.stateAlignments_remainderIn_nodup_of_remainderK_pow_lt_modulus`
- `BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderK_pow_lt_modulus`
- `BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderK_pow_lt_modulus`

The current source-pinned finite positive reconstruction hooks include
`47`, `49`, `71`, `97`, `98`, `142`, `170`, `299`, `997`, and `996`.
The `N = 170` hook is
`QRTour.FutureBase7N170.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The first unpinned emitted no-collision seed is
`(7, 340, 3, 343, 1, 3, 1, 299)`, with
`remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 49, 147]`; because it
shares `(base, B, k) = (7, 343, 3)` with the source-pinned `N = 170` hook, Lean
now proves the finite same-base/block-remainder family criterion via
`QRTour.Base7K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`
and
`QRTour.Base7K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
The previously uncovered seed `(10, 997, 3, 1000, 1, 3, 1, 439)` is now
source-pinned as
`QRTour.FutureBase10N997.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The base-30 sibling seed `(30, 897, 2, 900, 1, 3, 1, 639)` is now covered by
the finite divisor-family theorem
`QRTour.Base30K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`
and
`QRTour.Base30K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`
with proof-covered moduli `[23, 69, 299, 897]` and pair hook
`QRTour.Base30K3PositiveReconstruction.n299_n897_powerResidues_nodup_eight_pair`.
After excluding source-pinned and family-covered rows, the first uncovered
base-10 sibling seed `(10, 498, 3, 1000, 2, 4, 1, 928)` is now covered by
`QRTour.Base10K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`,
with proof-covered moduli `[83, 166, 249, 332, 498, 996]` and pair hook
`QRTour.Base10K4PositiveReconstruction.n498_n996_powerResidues_nodup_eight_pair`.
The previous base-12 sibling seed `(12, 75, 3, 1728, 23, 3, 1, 1161)` is now
covered by
`QRTour.Base12K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`,
with proof-covered moduli `[23, 25, 69, 75, 115, 345, 575, 1725]` and pair hook
`QRTour.Base12K3PositiveReconstruction.n75_n575_powerResidues_nodup_eight_pair`.
The previous standalone seed `(12, 575, 3, 1728, 3, 3, 1, 1053)` is now
source-pinned as
`QRTour.FutureBase12N575.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
with sibling functional theorem
`QRTour.FutureBase12N575.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
with no-collision hook
`QRTour.FutureBase12N575.coordinate_remainderK_powerResidues_nodup_eight`.
The previous standalone seed `(7, 1199, 4, 2401, 2, 3, 1, 1284)` is now
source-pinned as
`QRTour.FutureBase7N1199.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
with sibling functional theorem
`QRTour.FutureBase7N1199.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
with no-collision hook
`QRTour.FutureBase7N1199.coordinate_remainderK_powerResidues_nodup_eight`.
The previous standalone seed `(10, 294, 4, 10000, 34, 4, 1, 1776)` has
`preperiod_digits = 1`, `periodic_modulus = 147`, and
`remainder_power_residue_window = [1, 4, 16, 64, 256, 142, 274, 214]`; it is
now source-pinned as
`QRTour.FutureBase10N294.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
with sibling functional theorem
`QRTour.FutureBase10N294.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`
and no-collision hook
`QRTour.FutureBase10N294.coordinate_remainderK_powerResidues_nodup_eight`.
The previous base-7 sibling seed `(7, 109, 4, 2401, 22, 3, 1, 2119)` is now
family-covered by
`QRTour.Base7Stride4K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base7Stride4K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`,
with proof-covered moduli `[109, 218, 1199, 2398]` and pair hook
`QRTour.Base7Stride4K3PositiveReconstruction.n109_n1199_powerResidues_nodup_eight_pair`.
The previous standalone seed `(7, 46, 2, 49, 1, 3, 2, 2171)` is now
source-pinned as
`QRTour.FutureBase7N46.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`,
with sibling functional theorem
`QRTour.FutureBase7N46.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two`
and no-collision hook
`QRTour.FutureBase7N46.coordinate_remainderK_powerResidues_nodup_eight`.
The previous standalone seed `(7, 141, 4, 2401, 17, 4, 1, 2353)` is now
source-pinned as
`QRTour.FutureBase7N141.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
with sibling functional theorem
`QRTour.FutureBase7N141.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`
and no-collision hook
`QRTour.FutureBase7N141.coordinate_remainderK_powerResidues_nodup_eight`.
The previous uncovered power-no-collision seed
`(10, 714, 4, 10000, 14, 4, 1, 2496)` is now covered by the finite base-10,
stride-4, `k = 4` divisor-family theorem
`QRTour.Base10Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`,
with moduli `[49, 98, 119, 147, 196, 238, 294, 357, 476, 588, 714, 833]`
and pair hook
`QRTour.Base10Stride4K4PositiveReconstruction.n294_n714_powerResidues_nodup_eight_pair`.
The previous first uncovered power-no-collision seed
`(12, 73, 4, 20736, 284, 4, 1, 8704)`, with
`remainder_power_residue_window = [1, 4, 16, 64, 37, 2, 8, 32]`.
Lean now covers the same-base/block-remainder lane through
`QRTour.Base12Stride4K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`,
with proof-covered moduli `[71, 73, 142, 146, 284, 292, 5183, 10366, 20732]`
and pair hook
`QRTour.Base12Stride4K4PositiveReconstruction.n73_n146_powerResidues_nodup_eight_pair`.
The source-pinned sibling
`(12, 146, 4, 20736, 142, 4, 1, 4352)`, with
`remainder_power_residue_window = [1, 4, 16, 64, 110, 2, 8, 32]`,
`preperiod_digits = 1`, and `periodic_modulus = 73`, remains source-pinned
through `QRTour.FutureBase12N146.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase12N146.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase12N146.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous first uncovered power-no-collision seed
`(10, 769, 4, 10000, 13, 3, 1, 4707)`, with
`remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 729, 649]`,
`preperiod_digits = 0`, and `periodic_modulus = 769`, is now source-pinned
through `QRTour.FutureBase10N769.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase10N769.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase10N769.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous first uncovered power-no-collision seed
`(7, 345, 6, 117649, 341, 4, 1, 5534)`, with
`remainder_power_residue_window = [1, 4, 16, 64, 256, 334, 301, 169]`,
`preperiod_digits = 0`, and `periodic_modulus = 345`, is now source-pinned
through `QRTour.FutureBase7N345.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N345.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase7N345.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous first uncovered power-no-collision seed
`(7, 465, 6, 117649, 253, 4, 1, 7901)`, with
`remainder_power_residue_window = [1, 4, 16, 64, 256, 94, 376, 109]`.
Lean now covers this same-base/block-remainder lane through
`QRTour.Base7Stride6K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
The previous standalone/order-boundary seed
`(7, 542, 5, 16807, 31, 5, 1, 8472)`, with
`remainder_power_residue_window = [1, 5, 25, 125, 83, 415, 449, 77]`,
is now source-pinned through
`QRTour.FutureBase7N542.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N542.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase7N542.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous standalone/order-boundary seed
`(12, 47, 2, 144, 3, 3, 2, 9639)`, with
`remainder_power_residue_window = [1, 3, 9, 27, 34, 8, 24, 25]`, is now
source-pinned through
`QRTour.FutureBase12N47.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase12N47.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two`,
and
`QRTour.FutureBase12N47.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`.
Lean now also proves the base-12, stride-2, `k = 3` finite divisor-family
criterion through
`QRTour.Base12Stride2K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
the proof-covered moduli are `[47, 141]`, with pair hook
`QRTour.Base12Stride2K3PositiveReconstruction.n47_n141_powerResidues_nodup_eight_pair`.
The previous standalone/order-boundary seed
`(30, 794, 3, 27000, 34, 4, 1, 12776)`, with
`preperiod_digits = 1`, `periodic_modulus = 397`, and
`remainder_power_residue_window = [1, 4, 16, 64, 256, 230, 126, 504]`, is now
source-pinned through
`QRTour.FutureBase30N794.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase30N794.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase30N794.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
Lean now also proves the base-30, stride-3, `k = 4` finite divisor-family
criterion covering the previous
`(30, 397, 3, 27000, 68, 4, 1, 25552)` row, with
`remainder_power_residue_window = [1, 4, 16, 64, 256, 230, 126, 107]`,
through
`QRTour.Base30Stride3K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base30Stride3K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`;
the proof-covered moduli are `[397, 794, 1588, 6749, 13498, 26996]`, while
divisors `[1, 2, 4, 17, 34, 68]` remain outside this finite eight-entry
no-collision criterion. The pair hook
`QRTour.Base30Stride3K4PositiveReconstruction.n397_n794_powerResidues_nodup_eight_pair`
keeps the `397`/`794` signal visible.
The previous first uncovered power-no-collision seed
`(7, 113, 3, 343, 3, 4, 2, 13444)`, with
`remainder_power_residue_window = [1, 4, 16, 64, 30, 7, 28, 112]`, is now
source-pinned through
`QRTour.FutureBase7N113.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N113.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two`,
and
`QRTour.FutureBase7N113.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`.
The previous first uncovered power-no-collision seed
`(12, 691, 4, 20736, 30, 6, 1, 20736)`, with
`remainder_power_residue_window = [1, 6, 36, 216, 605, 175, 359, 81]`, is now
source-pinned through
`QRTour.FutureBase12N691.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase12N691.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase12N691.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous first uncovered power-no-collision seed
`(10, 578, 5, 100000, 173, 6, 1, 26432)`, with
`remainder_power_residue_window = [1, 6, 36, 216, 140, 262, 416, 184]`, is now
source-pinned through
`QRTour.FutureBase10N578.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase10N578.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase10N578.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous first uncovered seed
`(10, 277, 5, 100000, 361, 3, 1, 31479)`, with
`remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 175, 248]`, is now
source-pinned through
`QRTour.FutureBase10N277.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase10N277.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase10N277.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous first uncovered seed
`(7, 669, 7, 823543, 1231, 4, 1, 32398)`, with
`remainder_power_residue_window = [1, 4, 16, 64, 256, 355, 82, 328]`, is now
source-pinned through
`QRTour.FutureBase7N669.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N669.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase7N669.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous first uncovered seed
`(7, 71, 6, 117649, 1657, 2, 1, 46404)`, with
`remainder_power_residue_window = [1, 2, 4, 8, 16, 32, 64, 57]`, is now
source-pinned through
`QRTour.FutureBase7N71.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N71.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase7N71.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous first uncovered seed
`(7, 118, 6, 117649, 997, 3, 1, 47027)`, with
`remainder_power_residue_window = [1, 3, 9, 27, 81, 7, 21, 63]`, is now
source-pinned through
`QRTour.FutureBase7N118.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N118.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase7N118.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
Lean now also proves the base-7, stride-6, `k = 3` finite divisor-family
criterion covering the widened-atlas seed
`(7, 997, 6, 117649, 118, 3, 1, 49345)`, with
`remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 729, 193]`, through
`QRTour.Base7Stride6K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base7Stride6K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base7Stride6K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
The proof-covered moduli are `[59, 118, 997, 1994, 58823, 117646]`, and the
pair hook
`QRTour.Base7Stride6K3PositiveReconstruction.n118_n997_powerResidues_nodup_eight_pair`
keeps the `118`/`997` signal visible.
Lean now also proves the base-10, stride-5, `k = 6` finite divisor-family
criterion covering the previous seed
`(10, 289, 5, 100000, 346, 6, 1, 52864)`, with
`remainder_power_residue_window = [1, 6, 36, 216, 140, 262, 127, 184]`, through
`QRTour.Base10Stride5K6PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base10Stride5K6PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base10Stride5K6PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
The proof-covered moduli are `[17, 34, 173, 289, 346, 578, 2941, 5882, 49997, 99994]`,
and the pair hook
`QRTour.Base10Stride5K6PositiveReconstruction.n289_n578_powerResidues_nodup_eight_pair`
keeps the `289`/`578` signal visible.
The previous power-no-collision seed
`(12, 226, 5, 248832, 1101, 6, 1, 62208)`, with
`preperiod_digits = 1`, `periodic_modulus = 113`, and
`remainder_power_residue_window = [1, 6, 36, 216, 166, 92, 100, 148]`,
is now source-pinned through
`QRTour.FutureBase12N226.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase12N226.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase12N226.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous power-no-collision seed
`(7, 338, 3, 343, 1, 5, 2, 64744)`, with
`remainder_power_residue_window = [1, 5, 25, 125, 287, 83, 77, 47]`,
is now source-pinned through
`QRTour.FutureBase7N338.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N338.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two`,
and
`QRTour.FutureBase7N338.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`.
The previous first uncovered power-no-collision seed
`(12, 149, 5, 248832, 1670, 2, 1, 70144)`, with
`remainder_power_residue_window = [1, 2, 4, 8, 16, 32, 64, 128]`, is now
source-pinned through the no-wrap criterion via
`QRTour.FutureBase12N149.coordinate_remainderK_pow_lt_modulus_eight` and
`QRTour.FutureBase12N149.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous first uncovered power-no-collision seed
`(12, 289, 5, 248832, 861, 3, 1, 74115)`, with
`remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 151, 164]`, is now
family-covered by the base-12 stride-5 `k = 3` finite divisor-family theorem
`QRTour.Base12Stride5K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
The previous first uncovered power-no-collision seed
`(10, 641, 5, 100000, 156, 4, 1, 76384)`, with
`remainder_power_residue_window = [1, 4, 16, 64, 256, 383, 250, 359]`, is now
family-covered by the base-10 stride-5 `k = 4` finite divisor-family theorem
`QRTour.Base10Stride5K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
The first uncovered power-no-collision seed is now
`(10, 361, 5, 100000, 277, 3, 1, 82603)`, with
`remainder_power_residue_window = [1, 3, 9, 27, 81, 243, 7, 21]`.
It has source-pinned sibling seed `(10, 277, 5, 100000, 361, 3, 1, 31479)`,
so the program-atlas recommendation is
`prove_or_reject_same_base_block_remainder_power_no_collision_family`.

## What Remains Open

Two public frontier claims remain open and should stay open unless genuinely
closed by theorem, tests, and registry updates.

| Claim ID | Open question |
|----------|---------------|
| `small_k_visibility_threshold` | Is there a sharp arithmetic criterion for minimal stabilization lookahead and broader carried-prefix visibility beyond the fixed-window certificates already formalized? |
| `carry_dfa_factorization` | Does long division factor canonically into a remainder-orbit system and a carry transducer for all coprime bases and moduli? |

Finite output agreement, finite reconstruction, and finite obstruction records
are strong evidence and useful theorem candidates. They are not global morphism
theorems, DFA minimization theorems, or proof-status upgrades by themselves.

## Why This Looks Novel Enough To Test

The bold version is not "new facts about decimal expansions" in isolation. The
sharper thesis is that reciprocal expansions can be studied as observability
problems for arithmetic dynamical systems.

That gives the project a concrete grammar:

- **Observation**: a finite readout such as `remainderIn`, carried block value,
  carry state, displayed prefix, or a base-dependent target split.
- **Signal**: raw coefficient `qk^j`, coefficient modulo `B`, carry state, or
  another finite target.
- **Positive reconstruction**: the signal factors through the observation.
- **Obstruction**: equal observations with unequal signals.
- **Hidden output**: an obstruction that carry normalization masks at the
  carried-output level.
- **Instrument comparison**: changing the base changes the observation
  instrument, so a symmetry may be revealed, shifted, or hidden.

This is a plausible bridge to automata/numeration theory, hidden-process
identifiability, and observability language, but the external literature is
context rather than proof support for repo claims.

## Current Program Command

The coordination surface is:

```bash
search-reptends observability-program-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 50
```

It composes the observability atlas, target signatures, instrument comparison,
Shape13/17/187 family classifiers, and positive reconstruction candidates. It
is empirical/open-boundary tooling only: it creates no registry IDs,
theorem-witness promotions, proof-status upgrades, `small_k_visibility_threshold`
closure, or `carry_dfa_factorization` closure.

## Ranked Problems

The ranked problem ledger lives in
[OBSERVABILITY_PROBLEMS.md](OBSERVABILITY_PROBLEMS.md). The current recommended
order is:

1. Positive reconstruction beyond examples.
2. Observability target lattice and separations.
3. Base as observation instrument.
4. Carry normalizer as rational transduction.
5. Quantitative observability margins.

The first flagship bet should be positive reconstruction: use the power-residue
no-collision criterion to move from source-pinned finite examples toward an
arithmetic family theorem, while keeping global factorization claims open.

## Feedback Requested

Useful research-mode feedback would focus on:

1. Whether the observability-boundary framing is mathematically novel,
   standard-under-another-name, or best connected to automata/numeration theory.
2. Whether `FactorsThrough` is the right finite formal spine for both
   obstruction and reconstruction.
3. Whether the strongest next theorem should classify positive reconstruction
   via power-residue no-collision, classify one obstruction family, or reframe
   carry normalization as a rational-word-function problem.
4. Whether the target split suggests a known lattice or identifiability theory
   that the project should cite more explicitly.

Recommended review packet:

- [README.md](../README.md)
- [PROOF_STATUS_ATLAS.md](PROOF_STATUS_ATLAS.md)
- [../lean/THEOREM_GUIDE.md](../lean/THEOREM_GUIDE.md)
- [OBSERVABILITY_BOUNDARY.md](OBSERVABILITY_BOUNDARY.md)
- [OBSERVABILITY_PROBLEMS.md](OBSERVABILITY_PROBLEMS.md)
- [CARRY_TRANSDUCER.md](CARRY_TRANSDUCER.md)
