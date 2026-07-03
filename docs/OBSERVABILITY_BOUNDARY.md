# The Carry Layer as an Observability Boundary

Status: working draft.

This note captures the proposed pivot from "interesting reptend patterns" to a
more explicit observability thesis:

> Positional notation is an observation instrument for arithmetic dynamics.
> The carry-propagated block normalization layer is the boundary where source
> symmetries become visible, distorted, aliased, or hidden.

This is a research lens and planning document, not a new proof-status atlas
claim. The exact support currently comes from the existing registry claims
`series_q_weighted_identity`, `positive_q_good_modes`,
`carry_window_transducer`, `incoming_carry_position_formula`, and
`same_core_threshold_shift_interval`, together with finite Lean obstruction
records in `QRTour.Examples`. The claims `small_k_visibility_threshold` and
`carry_dfa_factorization` remain open.

## Operational Definitions

The load-bearing formal lens is factor-through observability, not metaphor.
Given a finite index set `T`, an observation map `obs : T -> Obs`, and a raw
coefficient map `coeff : T -> Coeff`, coefficient observability means that
`coeff` factors through `obs`:

```text
FactorsThrough(obs, coeff) := exists decode, forall t,
  decode(obs(t)) = coeff(t).
```

Equivalently, the kernel of the observation map must refine the kernel of the
coefficient map: if two finite positions have the same observation, then they
must have the same raw coefficient. A hidden coefficient conflict is the finite
collision pattern `obs(i) = obs(j)` together with
`coeff(i) != coeff(j)`. Output-hiding is the stronger finite carried-output
fact that the same pair also has equal carried block values after
carry-propagated block normalization.

The current Lean predicate `FactorsThrough` names that exact finite
observability condition. Its helper `FactorsThrough.eq_of_obs_eq` and generic
obstruction lemma `not_factorsThrough_of_collision` prove the small
kernel/refinement fact used throughout this lens: equal observations plus
unequal signal values refute factor-through observability.
`List.functionalOnFst_iff_factorsThrough_memberSubtype` then proves that the
older finite `List.FunctionalOnFst` surface and the factor-through vocabulary
are interchangeable on a finite row set, with the observation codomain restricted
to first-coordinates that actually occur in the list.
`BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_iff_factorsThrough_memberSubtype`
specializes that equivalence to the full `stateAlignments` window mapped as
`(remainderIn, coefficient)`, and
`BlockCoordinate.stateAlignments_not_remainderToCoefficientFactorsThrough_of_not_remainderToCoefficientFunctional`
turns nonfunctionality of that concrete window into `¬ FactorsThrough` for the
full finite readout. The worked examples
`QRTour.Composite68.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_fullWindow_eight_one`
and
`QRTour.Composite68Base30.coordinate_obstructionRecord_proofPath_not_remainderToCoefficientFactorsThrough_fullWindow_eight_one`
pin that full-window obstruction path for the base-`10` and base-`30`
`Composite68` hooks. The current Lean record `StateAlignmentCertifiedConflict`
should also be read in that exact way: its
projection
`BlockCoordinate.StateAlignmentCertifiedConflict.not_remainderToCoefficientFactorsThrough`
turns a certified two-row conflict into a finite-horizon factor-through
obstruction. It is not a global statement about all windows, and it does not
close `small_k_visibility_threshold` or `carry_dfa_factorization`.

## External Source Map

The outside literature is useful for vocabulary and attack routes, not for
promoting any repo claim by itself.

| External lane | What it contributes here | Source anchor |
|---------------|--------------------------|---------------|
| numeration normalization by finite automata | carry-propagated block normalization as a standard finite-transducer kind of question | [Frougny 1992](https://link.springer.com/article/10.1007/BF01368783) |
| rational word functions and bimachines | a future route for the still-open `carry_dfa_factorization` frontier, especially if the normalizer needs two directional passes | [Reutenauer-Schutzenberger 1991](https://epubs.siam.org/doi/abs/10.1137/0220042) |
| identifiability of functions of hidden finite processes | hidden coefficient conflicts as non-identifiability of a function of the source state through the readout | [Blackwell-Koopmans 1957](https://projecteuclid.org/journals/annals-of-mathematical-statistics/volume-28/issue-4/On-the-Identifiability-Problem-for-Functions-of-Finite-Markov-Chains/10.1214/aoms/1177706802.full) |
| observability and indistinguishability | observational indistinguishability as the standard name for same readout with different hidden state/function values | [Hermann-Krener 1977](https://www.math.ucdavis.edu/~krener/1-25/10.IEEETAC77.pdf) |
| base dependence for automata-recognizable structure | base as observation instrument rather than harmless notation | [Cobham 1969](https://link.springer.com/article/10.1007/BF01746527) |
| deterministic information loss | non-injectivity and quantization-style loss as a future quantitative version of the current exact kernel tests | [Geiger-Kubin 2017](https://link.springer.com/book/10.1007/978-3-319-59533-7) |

Use "aliasing" only as a pedagogical analogy. The formal terms are
non-injectivity, factor-through failure, kernel/refinement failure, and
observational indistinguishability.

## Steelman Queue

Bold ideas that are plausible enough to track, but not yet theorem claims:

- Prove a generic Lean factor-through obstruction lemma so future finite
  conflict records can cite one conceptual theorem before their arithmetic.
- Recast `carry_dfa_factorization` as a rational-word-function or canonical
  bimachine problem, then decide whether a one-pass DFA is the wrong target.
- Search for quantitative observability margins after the exact finite kernel
  and conflict surfaces stabilize.
- Treat base changes as instrument changes and classify which bases hide,
  reveal, or shift the same source symmetry.

The ranked version of this queue now lives in
[OBSERVABILITY_PROBLEMS.md](OBSERVABILITY_PROBLEMS.md). That ledger separates
positive reconstruction, target-lattice separations, base-as-instrument
comparisons, rational-transduction reframing, and quantitative observability
margins into explicit Lean/export surfaces and stop conditions.

## What This Changes In The Roadmap

The next search/export priority is not just finding more finite conflicts. It
is separating proof-supported arithmetic mechanisms from finite-only evidence.
The observability rows therefore export `same_core_shift_support_status`.
Rows marked `same_core_shift_proved_by_arithmetic_criterion` point to an
existing named Lean arithmetic criterion; rows marked `finite_only_hidden_conflict`
are still useful obstruction witnesses, but they should not be described as
same-core shift theorems. Rows marked `same_core_shift_criterion_candidate`
have the exported arithmetic hypotheses but still need an intentional named
Lean instantiation before they become proof-covered examples.

## Atlas-First Program

The current organizing surface is the Observability Program Atlas:

```bash
search-reptends observability-program-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 50
```

This command is a coordinator over existing empirical surfaces: the
Observability Atlas, target signatures, instrument comparison, Shape13/17/187
family classifiers, and functional-frontier rows. It emits
`observability_program_summary`, `observability_program_lane`,
`observability_program_family`,
`observability_positive_reconstruction_candidate`, and
`observability_program_next_task` rows. This is empirical/open-boundary
program-atlas tooling: it does not recompute new arithmetic and does not add
registry IDs, theorem-witness records, proof-status atlas upgrades, or closures
of `small_k_visibility_threshold` or `carry_dfa_factorization`.

The atlas-first view separates three current regimes:

- Hidden-output obstruction families: Shape17/Composite68 and Shape187/K188
  show finite factor-through failures where raw coefficient information is lost
  even though carried output can agree.
- Mod-stable / target-split loss patterns: Shape13/K4 shows that a factor-through
  target can survive after reducing coefficients modulo `B`, while carry-state
  observability still fails.
- Positive reconstruction candidates: functional-frontier rows such as `97`,
  `996`, and smaller-gap rows like `(base, N, m, B, q, k, L) =
  (10, 98, 2, 100, 1, 2, 1)` are empirical cases where raw coefficients,
  coefficients modulo `B`, carried block values, and carry states all factor
  through the observed remainder state on the finite window.

The next proof lane is positive reconstruction: prove finite exemplars where
the raw coefficient signal factors through the observed finite state data,
using
`BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderToCoefficientFunctional`,
the positive wrapper over the existing `FactorsThrough` /
`List.FunctionalOnFst` equivalence, before attempting a new global
factorization claim. The first Lean hooks in that lane are
`QRTour.Prime97.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`
and
`QRTour.Composite996.actual996_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The smaller-gap base-10 denominator-`98` candidate is now also pinned as
`QRTour.FutureBase10N98.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (10, 98, 2, 100, 1, 2, 1, 44)`.
The next graduated base-12 denominator-`142` hook is pinned as
`QRTour.FutureBase12N142.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (12, 142, 2, 144, 1, 2, 1, 32)`.
The next base-7 denominator-`47` hook is pinned as
`QRTour.FutureBase7N47.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (7, 47, 2, 49, 1, 2, 1, 38)`.
The next base-12 denominator-`71` hook is pinned as
`QRTour.FutureBase12N71.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (12, 71, 2, 144, 2, 2, 1, 64)`.
The next base-10 denominator-`49` hook is pinned as
`QRTour.FutureBase10N49.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (10, 49, 2, 100, 2, 2, 1, 88)`.
The next base-30 denominator-`299` hook is pinned as
`QRTour.FutureBase30N299.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (30, 299, 2, 900, 3, 3, 1, 117)`.
The next base-7 denominator-`170` hook is pinned as
`QRTour.FutureBase7N170.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
for `(base, N, m, B, q, k, L, gap) = (7, 170, 3, 343, 2, 3, 1, 255)`.
The program-atlas export keeps this boundary visible with
`positive_reconstruction_source_pinned`,
`positive_reconstruction_source_status`,
`positive_reconstruction_lean_support_status`,
`positive_reconstruction_functional_theorem`, and
`positive_reconstruction_factor_through_theorem` fields, separating
source-pinned finite hooks from still-empirical reconstruction candidates.
The first mined sufficient criterion is
`finite_remainder_state_injective_on_window`: rows export
`remainder_state_window`, `raw_coefficient_window`,
`remainder_state_window_injective`,
`positive_reconstruction_arithmetic_criterion_id`, and
`positive_reconstruction_hyp_remainder_state_window_injective`. Lean now proves
the finite helper path through `List.functionalOnFst_of_map_fst_nodup`,
`BlockCoordinate.stateAlignments_remainderToCoefficientFunctional_of_remainderIn_nodup`,
and
`BlockCoordinate.stateAlignments_remainderToCoefficientFactorsThrough_of_remainderIn_nodup`,
and the arithmetic no-collision refinement is exported as
`finite_remainder_power_residue_no_collision`: rows expose
`remainder_power_residue_window` and
`positive_reconstruction_hyp_remainder_power_residue_window_injective`. Lean
packages this full-modulus power-residue criterion through
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
The first unpinned no-collision seed is now exported directly as
`first_unpinned_positive_reconstruction_tuple =
[7, 340, 3, 343, 1, 3, 1, 299]`, with
`first_unpinned_positive_reconstruction_remainder_power_residue_window =
[1, 3, 9, 27, 81, 243, 49, 147]` and the source-pinned sibling list
`first_unpinned_positive_reconstruction_family_seed_tuples =
[[7, 170, 3, 343, 2, 3, 1, 255]]`. Because this shares
`(base, B, k) = (7, 343, 3)` with the `N = 170` hook, Lean now proves the
finite divisor-family criterion through
`QRTour.Base7K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`
and
`QRTour.Base7K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
The exported decision is
`use_lean_proved_family_criterion_before_source_pinning_more_examples`. The
base-30 `299`/`897` sibling is now proof-covered by
`QRTour.Base30K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`
and
`QRTour.Base30K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`,
with proof-covered moduli `[23, 69, 299, 897]` and pair hook
`QRTour.Base30K3PositiveReconstruction.n299_n897_powerResidues_nodup_eight_pair`.
The base-10 `498`/`996` sibling lane, anchored at
`[10, 498, 3, 1000, 2, 4, 1, 928]`, is now proof-covered by
`QRTour.Base10K4PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base10K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`,
with proof-covered moduli `[83, 166, 249, 332, 498, 996]` and pair hook
`QRTour.Base10K4PositiveReconstruction.n498_n996_powerResidues_nodup_eight_pair`.
The program atlas now also exports
the now source-pinned standalone hook
`[12, 575, 3, 1728, 3, 3, 1, 1053]`, with power-residue window
`[1, 3, 9, 27, 81, 243, 154, 462]`, through
`QRTour.FutureBase12N575.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`
with sibling functional theorem
`QRTour.FutureBase12N575.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
no-collision witness
`QRTour.FutureBase12N575.coordinate_remainderK_powerResidues_nodup_eight`, and
the base-12 `75`/`575` family criterion
`QRTour.Base12K3PositiveReconstruction.remainderK_powerResidues_nodup_eight_of_mem`,
`QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFunctional_eight_of_mem`,
and
`QRTour.Base12K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`
with proof-covered moduli `[23, 25, 69, 75, 115, 345, 575, 1725]` and pair hook
`QRTour.Base12K3PositiveReconstruction.n75_n575_powerResidues_nodup_eight_pair`.
The covered sibling seed `[12, 75, 3, 1728, 23, 3, 1, 1161]` has
power-residue window `[1, 3, 9, 27, 6, 18, 54, 12]`; divisors
`[1, 3, 5, 15]` remain outside this finite eight-entry no-collision criterion.
The previous standalone/order-boundary seed
`[7, 1199, 4, 2401, 2, 3, 1, 1284]`, with power-residue window
`[1, 3, 9, 27, 81, 243, 729, 988]`, is now source-pinned through
`QRTour.FutureBase7N1199.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N1199.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase7N1199.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The previous standalone/order-boundary seed
`[10, 294, 4, 10000, 34, 4, 1, 1776]` has `preperiod_digits = 1`,
`periodic_modulus = 147`, and power-residue window
`[1, 4, 16, 64, 256, 142, 274, 214]`; it is now source-pinned through
`QRTour.FutureBase10N294.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase10N294.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase10N294.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The base-7 `109`/`1199` sibling lane is now family-covered by
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
`[7, 46, 2, 49, 1, 3, 2, 2171]`, with power-residue window
`[1, 3, 9, 27, 35, 13, 39, 25]`, is now source-pinned through
`QRTour.FutureBase7N46.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N46.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_two`,
and
`QRTour.FutureBase7N46.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_two`.
The previous standalone/order-boundary seed
`[7, 141, 4, 2401, 17, 4, 1, 2353]`, with power-residue window
`[1, 4, 16, 64, 115, 37, 7, 28]`, is now source-pinned through
`QRTour.FutureBase7N141.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase7N141.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase7N141.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
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
`QRTour.Base12Stride4K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
The proof-covered moduli are
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
The previous uncovered seed
`[10, 769, 4, 10000, 13, 3, 1, 4707]`, with `preperiod_digits = 0`,
`periodic_modulus = 769`, and power-residue window
`[1, 3, 9, 27, 81, 243, 729, 649]`, is now source-pinned through
`QRTour.FutureBase10N769.coordinate_remainderK_powerResidues_nodup_eight`,
`QRTour.FutureBase10N769.coordinate_stateAlignments_remainderToCoefficientFunctional_eight_one`,
and
`QRTour.FutureBase10N769.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`.
The earlier `997` seed remains source-pinned through
`QRTour.FutureBase10N997.coordinate_stateAlignments_remainderToCoefficientFactorsThrough_eight_one`,
which keeps the standalone proof trail explicit in this working observability
ledger.
The previous standalone/order-boundary seed
`[7, 345, 6, 117649, 341, 4, 1, 5534]`, with `preperiod_digits = 0`,
`periodic_modulus = 345`, and power-residue window
`[1, 4, 16, 64, 256, 334, 301, 169]`, is now source-pinned through
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
`QRTour.Base7Stride6K4PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
The proof-covered moduli are
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
`QRTour.Base12Stride2K3PositiveReconstruction.stateAlignments_remainderToCoefficientFactorsThrough_eight_of_mem`.
The proof-covered moduli are `[47, 141]`, and the pair hook
`QRTour.Base12Stride2K3PositiveReconstruction.n47_n141_powerResidues_nodup_eight_pair`
keeps the `47`/`141` signal visible, while divisors `[1, 3]` remain outside
this finite eight-entry no-collision criterion.
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
`[1, 2, 4, 17, 34, 68]` remain outside this finite eight-entry no-collision
criterion.
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
`pursue_family_criterion_before_source_pinning_more_examples`, so the next
default task is `prove_or_reject_same_base_block_remainder_power_no_collision_family`.
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
They are finite-window support statements, not global arithmetic
classifications and not closures of `small_k_visibility_threshold` or
`carry_dfa_factorization`.

## The Reframing

The project can be read as a study of what a positional numeral system lets an
observer reconstruct from an underlying arithmetic dynamical system.

| Layer | Standard object | Observability question |
|-------|-----------------|------------------------|
| Source dynamics | remainder orbit under multiplication by the base | What is the true state evolution before display? |
| Source signal | raw coefficients `qk^j` from `B = qN + k` | What coefficient information is produced by the orbit coordinate? |
| Instrument | carry-propagated block normalization | What information does positional notation preserve, shift, collapse, or hide? |
| Readout | displayed block expansion | What can an observer infer from the visible blocks? |

The core exact identity stays unchanged: if `B = qN + k`, `0 <= k < N`, and
`B > N`, then

```text
1/N = q/(B-k) = (q/B) * 1/(1-k/B) = Σ q*k^j / B^(j+1).
```

The raw coefficient stream is therefore not a metaphor. It is the exact source
signal passed into carry-propagated block normalization.

## The Phenomenon

The new flagship phenomenon is:

> Residue-orbit symmetry can survive while coefficient observability fails.

In finite state-alignment windows, this appears as:

1. Two positions have the same observed `remainderIn`.
2. The same positions have unequal raw coefficients.
3. The carry layer emits the same carried block value anyway.
4. A displayed observer sees output agreement while coefficient information has
   already been lost.

This is the shape currently exposed by `StateAlignmentCertifiedConflict` in
Lean and by the Certificate Workbench / fixture tooling in Python.

## First Certified Anchors

These anchors are finite-window obstruction records, not global theorems.

| Namespace | Tuple `(base, N, m, B, q, k, L, gap)` | Conflict shape | Current role |
|-----------|----------------------------------------|----------------|--------------|
| `QRTour.Composite68` | `(10, 68, 4, 10000, 147, 4, 1, 6208)` | positions `1/5`, same remainder `4`, coefficients `588/150528`, carry states `0/60`, carried block `588` | family-level finite obstruction hook for `N = 68`, `B ≡ 4 (mod 68)` |
| `QRTour.Composite68Base30` | `(30, 68, 3, 27000, 397, 4, 1, 10208)` | positions `1/5`, same remainder `4`, coefficients `1588/406528`, carry states `0/60`, carried block `1588` | cross-base member of the same finite family hook |
| `QRTour.FutureBase12N31` | `(12, 31, 6, 2985984, 96322, 2, 1, 2215424)` | positions `0/5`, same remainder `1`, coefficients `96322/3082304`, carry states `0/2`, carried block `96322` | source-pinned finite scaffold example |
| `QRTour.FutureBase12N35` | `(12, 35, 2, 144, 4, 4, 3, 1740800)` | positions `0/6`, same remainder `1`, coefficients `4/16384`, carry states `0/468`, carried block `4` | source-pinned finite scaffold example |

The important pattern is not any one denominator. It is the three-way split:
same remainder-state observation, unequal source coefficient, equal displayed
carry output.

## Vocabulary Candidates

These are draft names. They should not be added to the generated vocabulary
registry until the surface stabilizes.

| Draft term | Meaning | Status |
|------------|---------|--------|
| source symmetry | repeated or structured behavior in the remainder orbit before carry normalization | working vocabulary |
| coefficient observability | whether observed finite states determine raw coefficients on a window | working vocabulary |
| hidden coefficient conflict | same observed remainder, unequal coefficients, same carried output | Lean-backed finite examples exist |
| visible coefficient conflict | same observed remainder, unequal coefficients, different carried output | empirical classifier target |
| instrument aliasing | collapse caused by the base/block/carry instrument rather than by the source orbit alone | empirical classifier target |
| base instrument | a base or block coordinate treated as an observation device | existing docs already use this informally |

Preferred wording for now:

- Use "raw coefficients `qk^j`" before "source signal."
- Use "carry-propagated block normalization" before "carry layer."
- Use "remainder orbit" before "source dynamics."
- Use "hidden coefficient conflict" only for finite windows unless a later
  theorem proves a family classification.

## What This Could Become

The bold version is an observability theory for rational expansions:

> Given the displayed block readout, determine which parts of the remainder
> orbit and raw coefficient stream are reconstructible, which are ambiguous,
> and which are provably hidden by carry normalization.

The repo is unusually well positioned for this because it already has:

- an exact orbit layer through digit periodicity, QR stride classification,
  CRT periods, and preperiod stripping
- an exact source-signal layer through the q-weighted identity
- a finite carry-normalization layer in Lean
- finite state-alignment records with functionality and conflict predicates
- empirical workbench and fixture tooling that can feed future Lean packages

## Pivot Tranches

### Tranche 1: Name the Lens

Goal: make the observability-boundary framing visible without changing claim
status.

Candidate changes:

- Keep this document as the working planning surface.
- Add a short theorem-guide hook saying the finite obstruction records are
  examples of coefficient information loss across the carry boundary.
- Add a carry-transducer note that points readers from the existing
  `StateAlignmentCertifiedConflict` record to this lens.

Stop condition:

- Stop before editing `data/claim_registry.json`, theorem-witness files, or the
  proof-status atlas. This tranche is framing, not promotion.

### Tranche 2: Observability Atlas V1

Goal: expose the phenomenon as rows, not prose.

Implemented search surface:

```bash
search-reptends observability-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 50
```

The command composes the Certificate Workbench rather than duplicating
carry/remainder arithmetic. It emits empirical/open-boundary observability
tooling only: no registry IDs, theorem-witness records, atlas-status changes,
`small_k_visibility_threshold` closure, or `carry_dfa_factorization` closure.

Row groups:

- `observability_summary`
- `hidden_coefficient_conflict`
- `visible_coefficient_conflict`
- `coefficient_functional_frontier`
- `gap_one_bridge_candidate`

Core fields:

- `base`, `n`, `m`, `B`, `q`, `k`, `period`, `preperiod_digits`
- `requested_blocks`, `certified_lookahead_blocks`, `exact_gap_numerator`
- `conflict_positions`, `conflict_remainder_state`,
  `conflict_coefficients`, `conflict_carry_states`, `conflict_block_values`
- `remainder_to_coefficient_functional`
- `coefficient_observability_class`
- `observability_boundary_status`
- `source_symmetry_visible`
- `coefficient_information_lost`
- `carry_output_hides_conflict`
- `lean_readiness`
- `next_observability_task`

The **Observability Target Split** expands those same atlas rows into explicit
factor-through target readouts:

```bash
search-reptends observability-target-split --max 1200 --bases 7,10,12,30 --blocks 8 --top 50
```

This command emits `observability_target_split_summary` followed by
`observability_target_split_case` rows. It is empirical/open-boundary
target-split tooling only; it distinguishes factor-through target surfaces but
does not add a registry ID, theorem-witness record, proof-status atlas upgrade,
`small_k_visibility_threshold` closure, or `carry_dfa_factorization` closure.

Target map:

| Target ID | Observation | Signal/readout | V1 interpretation |
|-----------|-------------|----------------|-------------------|
| `raw_coefficient_nat` | `remainder_state` | raw coefficient as a natural number | pointwise factor-through target |
| `coefficient_mod_block_base` | `remainder_state` | raw coefficient modulo `B` | pointwise factor-through target |
| `carried_block_value` | `remainder_state` | carry-normalized block value | pointwise factor-through target; can hide a raw conflict |
| `carry_state` | `remainder_state` | incoming finite carry state | pointwise factor-through target |
| `remainder_state` | `remainder_state` | source state itself | identity observation baseline |
| `displayed_prefix` | finite displayed prefix | certified visible window | window-level certificate, not a pointwise `FactorsThrough` map |

The **Observability Target Signatures** command groups atlas rows by the full
`observability_target_summary_signature`, so repeated factor-through target
profiles can be mined as families:

```bash
search-reptends observability-target-signatures --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

It emits `observability_target_signature_summary` followed by
`observability_target_signature_family` rows. The first default family has
raw coefficient observability obstructed while `carried_block_value` remains a
functional output that hides the raw coefficient conflict; another default
family keeps `raw_coefficient_nat`, `coefficient_mod_block_base`,
`carried_block_value`, and `carry_state` all functional. This is
empirical/open-boundary target-signature tooling only: it mines coefficient
information loss patterns and target-specific factor-through targets without
adding a registry ID, theorem-witness record, proof-status atlas upgrade,
`small_k_visibility_threshold` closure, or `carry_dfa_factorization` closure.

The **Mod-Stable Carry-Loss** drill-down mines the second hidden-output
signature directly:

```bash
search-reptends observability-mod-stable-carry-loss --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

It emits `observability_mod_stable_carry_loss_summary` followed by
`observability_mod_stable_carry_loss_case` rows for cases where
`raw_coefficient_nat` is obstructed, `coefficient_mod_block_base` remains
functional, `carried_block_value` hides the raw conflict, and `carry_state` is
obstructed. The first default row is
`(base, N, m, B, q, k, L, gap) = (30, 26, 1, 30, 1, 4, 5, 11927264)`.
This is empirical/open-boundary mod-stable carry-loss tooling only: it
identifies a sharper target-specific information-loss pattern but still does
not add a registry ID, theorem-witness record, proof-status atlas upgrade,
`small_k_visibility_threshold` closure, or `carry_dfa_factorization` closure.

The focused **Shape13/K4 mod-stable carry-loss classifier** expands the first
mod-stable source shape, `periodic_modulus=13;k=4;position_gap=6`, starting
from the base-`30` `N = 13` / `N = 26` pair:

```bash
search-reptends observability-shape13-k4-mod-stable-carry-loss --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

It emits `observability_shape13_k4_mod_stable_carry_loss_summary` followed by
`observability_shape13_k4_mod_stable_carry_loss_member` rows. Under the default
scan, the source-core row is
`(base, N, m, B, q, k, L, gap) = (30, 13, 1, 30, 2, 4, 5, 23854528)` with
conflict positions `[0,6]`, and the shifted member is
`(30, 26, 1, 30, 1, 4, 5, 11927264)` with positions `[1,7]`. The exported
fields record the denominator multiplier from the `N = 13` core, the
preperiod/position shift, and the fact that coefficient modulo `B` stays
functional while carry state loses information.

Lean now covers the default base-`30` Shape13/K4 pair as finite/canonical
observability support:

- `QRTour.FutureBase30N13.coordinate_stateAlignments_zero_six_certifiedConflict_eight_five`
  pins the source-core finite conflict.
- `QRTour.FutureBase30N26.coordinate_stateAlignments_one_seven_certifiedConflict_eight_five`
  pins the shifted finite conflict.
- `QRTour.Shape13K4.base30_core13_to_double26_conflict_shift_scaled`
  proves the one-position, scale-two finite row comparison.
- `QRTour.Shape13K4.base30_n26_scaleTwoHiddenCarryBlockValueHypotheses`
  packages the exported `shape13_k4_hyp_*` booleans as
  `SameCoreScaleTwoHiddenCarryBlockValueHypotheses`.
- `QRTour.Shape13K4.base30_n26_sameCore_scale_two_hiddenCarryBlockValue_shift`
  instantiates
  `sameCoreCompatible_hiddenCarryBlockValue_shift_scale_two_of_exportedHypotheses`
  for the canonical carried-output equality at shifted positions `[1,7]`.

The scale-two criterion names the exact arithmetic hypotheses needed beyond
same-core compatibility: `basePrimeSupportFactor * 2 = k`, quotient-remainder
bounds below `B-k` at both source positions, block-remainder bounds below `B`
at both source positions, and a source-core hidden carried-output equality.
That is the Lean-ready generalization target beyond the single base-`30`
`13 -> 26` witness, and the adapter theorem
`sameCoreCompatible_hiddenCarryBlockValue_shift_scale_two_of_exportedHypotheses`
is the intended proof path from exported booleans to the canonical
carried-output equality.

The member rows now export these as searchable booleans:
`shape13_k4_hyp_good_mode`, `shape13_k4_hyp_same_core_compatible`,
`shape13_k4_hyp_base_prime_support_times_two_eq_k`,
`shape13_k4_hyp_scaled_quotient_remainders_lt_gap`,
`shape13_k4_hyp_scaled_block_remainders_lt_block_base`, and
`shape13_k4_hyp_source_core_hidden_carry_block_value`, with
`shape13_k4_scale_two_hypotheses_hold` and
`shape13_k4_scale_two_failure_reason` summarizing the result. Under the
default scan, `N = 26` satisfies the full scale-two hypothesis bundle while
the `N = 13` source-core row fails only `base_prime_support_times_two_ne_k`.
The summary also exports `shape13_k4_scale_two_unnamed_candidate_members`,
`shape13_k4_scale_two_unnamed_candidate_tuples`, and
`shape13_k4_scale_two_candidate_mining_status`; the current wider candidate
probe reports
`no_unnamed_scale_two_ready_members_under_current_bounds`.

This is empirical/open-boundary Shape13/K4 mod-stable carry-loss classification
plus finite Lean support only; it is not a registry claim, theorem-witness
record, atlas-status promotion, `small_k_visibility_threshold` closure, or
`carry_dfa_factorization` closure.

Current bounded mining says this should stay narrow for now: a manual probe
found no additional members for bases `7,10,12,30` through `max_n=2000`, or for
bases `7,10,12,30,32,64,66,72,98,100` through `max_n=1200`. The export records
that as `shape13_k4_current_scan_status =
only_base30_core_and_shift_pair_under_current_bounds` and the stop condition
`do_not_add_new_shape13_k4_finite_package_until_wider_scan_emits_new_member`.
The scale-two-specific probe also found no unnamed scale-two-ready members
under those same bounds.
The next honest move is either a wider Shape13/K4 mining pass or a general
scale-two criterion beyond the single base-`30` `13 -> 26` pair.

Stop condition:

- If the new surface only duplicates Certificate Workbench rows with new names,
  stop and instead add derived columns to the workbench.

### Tranche 2B: Cross-Base Instrument Compare

Goal: compare how different base instruments hide, reveal, or shift the same
source symmetry.

Implemented search surface:

```bash
search-reptends observability-instrument-compare --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

The command composes `observability-atlas` rows and groups hidden-conflict
members by a source symmetry shape signature:

```text
periodic_modulus=<M>;k=<remainder>;position_gap=<gap>
```

The first default shape is `periodic_modulus=17;k=4;position_gap=4`, which
contains the base-`10` and base-`30` `Composite68` hidden coefficient conflict
members and a shifted base-`10` member on the same source shape. The important
new row groups are:

- `observability_instrument_summary`
- `observability_source_symmetry_shape`
- `observability_instrument_member`

The shape rows name `hidden_bases`, `visible_bases`, `shifted_bases`,
`conflict_remainder_states`, and `exact_position_signatures`. Member rows keep
the concrete base, denominator, coefficient conflict, lookahead certificate,
and Lean-readiness fields while adding `instrument_observation_status` and
`source_symmetry_shift_status`.

Stop condition:

- Treat this as empirical/open-boundary instrument comparison. It can nominate
  finite packages or family classifiers, but it does not close
  `small_k_visibility_threshold`, does not close `carry_dfa_factorization`, and
  does not create registry IDs, theorem-witness records, or atlas-status
  changes.

### Tranche 2C: First Source-Shape Family Classifier

Goal: classify the first emitted source shape before attempting a Lean family
theorem.

Implemented search surface:

```bash
search-reptends observability-shape17-k4-family --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

This focuses on `periodic_modulus=17;k=4;position_gap=4`, the first source
shape emitted by the instrument comparison. The default rows connect:

- `N = 17`, same-core multiplier `1`, shifted positions `[0,4]`
- `N = 34`, same-core multiplier `2`, Composite68-style positions `[1,5]`
- `N = 68`, same-core multiplier `4`, Composite68-style positions `[1,5]`

The member rows add `source_symmetry_family_role`, `same_core_multiplier`,
`position_shift_from_canonical`, and `base_local_coefficient_scale`. This is a
small theorem-candidate map, not a theorem: it gives the next Lean or search
pass a precise finite family to prove or reject.

Lean finite follow-up:

- `QRTour.FutureBase10N17.coordinate_stateAlignments_zero_four_certifiedConflict_eight_two`
  proves the base-10 `N = 17` shifted `[0,4]` conflict record.
- `QRTour.FutureBase10N34.coordinate_stateAlignments_one_five_certifiedConflict_eight_two`
  proves the base-10 `N = 34` doubled `[1,5]` conflict record.
- `QRTour.Shape17K4.base10_core17_to_composite68_conflict_shift_exact`
  and
  `QRTour.Shape17K4.base10_core17_to_double34_conflict_shift_scaled`
  prove the finite Shape17/K4 shift witness: the observed source-shape shift
  from `[0,4]` to `[1,5]`, and the scale-two `N = 34` payload, at the concrete
  state-alignment row level.

This Lean response proves finite trace facts, not a global same-core
classification theorem.

### Tranche 2D: Next Source-Shape Family Selector

Goal: keep mining after a focused family has no remaining criterion candidates,
without immediately hard-coding another one-off classifier.

Implemented search surface:

```bash
search-reptends observability-next-source-shape-family --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

The selector skips the already classified
`periodic_modulus=17;k=4;position_gap=4` Shape17/K4 source shape and emits the
next unresolved ranked family. Under the default scan, that is
`periodic_modulus=187;k=188;position_gap=6`, with base-`10`, base-`12`, and
base-`30` members at `N = 374` and `N = 748`, hidden carried-output conflicts
at positions `[1,2]`, and same-core multipliers `2` and `4`.

The row groups are:

- `observability_next_source_shape_family_summary`
- `observability_next_source_shape_family_member`

Member rows preserve the Certificate Workbench and Observability Atlas fields
while adding `same_core_multiplier`, `source_symmetry_family_role`,
`position_shift_from_canonical`, `base_local_coefficient_scale`, and
`next_source_shape_family_note`. The Shape187/K188 default family is currently
classified as `finite_only_hidden_conflict`: it is a finite hidden-conflict
source family, not a proved arithmetic criterion and not a Lean-ready theorem
surface.

Stop condition:

- Treat this as empirical/open-boundary family mining. It can nominate a
  finite package or a new arithmetic criterion, but it does not close
  `small_k_visibility_threshold`, does not close `carry_dfa_factorization`, and
  does not create registry IDs, theorem-witness records, or atlas-status
  changes.

### Tranche 2E: Shape187/K188 Same-Position Scaling Classifier

Goal: decide whether the next unresolved source-shape family wants a new
arithmetic criterion or a finite Lean package first.

Implemented search surface:

```bash
search-reptends observability-shape187-k188-family --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

The default rows classify
`periodic_modulus=187;k=188;position_gap=6` as a same-position scaling family,
not a one-block shifted family like Shape17/K4. The observed members are
`N = 374 = 2*187` and `N = 748 = 4*187` over bases `10`, `12`, and `30`, all at
positions `[1,2]`.

The exported criterion fields say:

- `k = 188 = periodic_modulus + 1`
- `same_core_multiplier` is `2` or `4`, both dividing `k`
- `k^2 ≡ k (mod N)`
- the raw coefficient ratio between the conflicting positions is `188`
- the finite carry states match the floor-power formula `[94,17766]` for
  `N = 374` and `[47,8883]` for `N = 748`
- the carried block output remains hidden/equal

`BlockCoordinate.samePositionIdempotent_hiddenCarryBlockValue` is now the
generic Lean canonical-carry lemma for this idempotent-remainder shape.
`BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses` is the
exported-hypothesis bridge: it turns `N = multiplier * core`,
`k = core + 1`, and `multiplier | k` into the idempotent-remainder condition,
then
`BlockCoordinate.SamePositionScalingHiddenCarryBlockValueHypotheses.idempotent_remainder`
exposes that condition as a reusable projection, and
`BlockCoordinate.samePositionScaling_hiddenCarryBlockValue_one_two_of_exportedHypotheses`
reuses the canonical carried-output proof path. The source-ready canonical
instantiations are
`QRTour.FutureBase10N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two`,
`QRTour.FutureBase12N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two`,
`QRTour.FutureBase30N374.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two`,
and
`QRTour.FutureBase30N748.coordinate_samePositionIdempotent_hiddenCarryBlockValue_one_two`.
Their bundled input records are
`QRTour.FutureBase10N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses`,
`QRTour.FutureBase12N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses`,
`QRTour.FutureBase30N374.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses`
and
`QRTour.FutureBase30N748.coordinate_samePositionScalingHiddenCarryBlockValueHypotheses`.
The export names that handoff with
`same_position_scaling_exported_hypothesis_record`,
`same_position_scaling_idempotent_remainder_projection`,
`same_position_scaling_exported_hypothesis_adapter`,
`same_position_scaling_intended_proof_path`, and
`same_position_scaling_named_hypothesis_instantiation`, so the remaining
base-`10` and base-`12` `N = 748` candidates can point at the intended Lean
proof path without being promoted to proof-covered rows.
Base-`10` `N = 374` also pins the finite `8/2` certified conflict record
`QRTour.FutureBase10N374.coordinate_stateAlignments_one_two_certifiedConflict_eight_two`.
Rows expose finite record coverage through
`same_position_scaling_named_finite_conflict_instantiation`.
The base-`30` worked namespaces pin the finite certified conflict records
`QRTour.FutureBase30N374.coordinate_stateAlignments_one_two_certifiedConflict_eight_one`
and
`QRTour.FutureBase30N748.coordinate_stateAlignments_one_two_certifiedConflict_eight_one`.
The wrapper
`QRTour.Shape187K188.base30_default_samePositionIdempotent_hiddenCarryBlockValue_one_two_pair`
packages the two proof-covered base-`30` canonical carried-output seeds
together without promoting the remaining rows.

The default export now deliberately splits the family:

- base-`30`, `N = 374` and `N = 748` are
  `same_position_scaling_proved_by_arithmetic_criterion`
- the four remaining base-`10` and base-`12` default rows are still
  `same_position_scaling_criterion_candidate`

Stop condition:

- Do not call Shape187/K188 classified globally until the remaining rows either
  receive named Lean instantiations or a genuinely uniform theorem. Until then,
  this is finite/canonical observability support below
  `small_k_visibility_threshold` and `carry_dfa_factorization`, with no registry
  ID, theorem-witness record, or atlas-status change.

Arithmetic generalization now landed:

- `sameCoreCompatible_rawCoefficient_shift_scaled_one` proves the one-block
  shifted/scaled raw-coefficient law when `basePrimeSupportFactor * scale = k`.
- `sameCoreCompatible_incomingCarry_shift_scaled_one` identifies the exact
  extra quotient-remainder condition needed for incoming carries to shift and
  scale.
- `sameCoreCompatible_canonicalCarryBlockValue_shift_scaled_one` and
  `sameCoreCompatible_hiddenCarryBlockValue_shift_scaled_one` add the final
  block-remainder condition needed to preserve hidden canonical carried-output
  equality.
- `nat_mul_div_eq_mul_div_iff_mul_mod_lt` and
  `nat_mul_mod_eq_mul_mod_iff_mul_mod_lt` make the quotient-remainder and
  block-remainder tests exact at the local arithmetic layer.
- `QRTour.Shape17K4.base10_n68_sameCore_scale_one_hiddenCarryBlockValue_shift`,
  `QRTour.Shape17K4.base10_n34_sameCore_scale_two_hiddenCarryBlockValue_shift`,
  `QRTour.Shape17K4.base30_n68_sameCore_scale_one_hiddenCarryBlockValue_shift`,
  and
  `QRTour.Shape17K4.base30_n34_sameCore_scale_two_hiddenCarryBlockValue_shift`
  instantiate the criterion for the base-`10` and base-`30` `17 -> 68` and
  `17 -> 34` source-shape members.

This characterizes the finite one-block shift mechanism without closing the
least-lookahead or global factorization frontiers.

Stop condition:

- Keep this empirical/open-boundary family classification. It does not close
  `small_k_visibility_threshold`, does not close `carry_dfa_factorization`, and
  does not create registry IDs, theorem-witness records, or atlas-status
  changes.

### Tranche 3: Lean Record Naming

Goal: make the theorem surface say what the obstruction means.

Candidate Lean move:

- Keep `StateAlignmentCertifiedConflict` as the implementation record.
- Add a thin wrapper or theorem alias with an observability-facing name, for
  example `CoefficientObservabilityObstruction`, only if it reduces copying and
  improves citation clarity.
- Add projection helpers that make the three-part shape explicit:
  same remainder, unequal coefficient, hidden carried output.

Stop condition:

- Do not create a new global theorem or claim ID. The Lean work should remain
  finite-window and example/family scoped.

### Tranche 4: Family Classifiers

Goal: identify arithmetic sources of hidden coefficient conflicts.

Candidate theorem targets:

- For fixed `N`, `B`, and `k`, classify when `k^i ≡ k^j (mod N)` gives equal
  observed remainder states at positions `i` and `j`.
- Add the raw-coefficient separation condition `q*k^i != q*k^j`.
- Add the carry-output hiding condition
  `(q*k^i + carry_i) % B = (q*k^j + carry_j) % B`.
- Start with known families such as `N = 68`, `B ≡ 4 (mod 68)`.

Stop condition:

- If the carry-output hiding condition does not simplify cleanly, keep family
  classification empirical and continue finite package harvesting.

### Tranche 5: Positive Reconstruction

Goal: balance obstruction-first work with reconstruction theorems.

Candidate questions:

- When does a finite displayed window determine the raw coefficient attached to
  an observed remainder state?
- When does remainder-to-coefficient functionality imply a finite
  orbit-to-carry morphism?
- Which base instruments reveal a symmetry that another base hides?

Stop condition:

- Do not attempt `carry_dfa_factorization` directly. First prove small finite
  reconstruction theorems with explicit hypotheses and counterexamples.

## Working Ranking For Future Tasks

1. Add one theorem-guide / carry-doc hook from `StateAlignmentCertifiedConflict`
   to this observability-boundary lens.
2. Add an empirical `observability-atlas` row builder if it can reuse the
   Certificate Workbench without duplicating arithmetic.
3. Factor a small Lean theorem or projection that names the hidden-output
   three-part shape.
4. Classify the first family-level source of hidden coefficient conflicts
   beyond `Composite68`.
5. Develop positive finite reconstruction criteria only after the obstruction
   atlas stops producing easy new examples.

## Open Boundaries

This pivot must keep the following boundaries explicit:

- `small_k_visibility_threshold` remains open.
- `carry_dfa_factorization` remains open.
- Finite output agreement is not a global morphism theorem.
- Certificate Workbench and fixture rows are empirical tooling unless backed by
  a named Lean theorem.
- Agda remains a pedagogical companion, not theorem-parity evidence.

The phrase to keep us honest:

> We are studying observability through carry normalization, not claiming that
> every observed expansion canonically factors into orbit plus carry.
