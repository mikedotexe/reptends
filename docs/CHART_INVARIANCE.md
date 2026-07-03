# Chart Invariance

## Status

Status: empirical finite-window chart comparison, not a theorem source.

Chart invariance asks when two base/block instruments preserve the same
finite-window visibility geometry. The current surface compares selected bases
on bounded examples. It finds candidate invariant pairs and distortion
witnesses; it does not prove base-independent visibility.

The open boundary remains explicit: `small_k_visibility_threshold` and
`carry_dfa_factorization` are still `open`.

## Lean Foothold

The current Lean foothold is finite and claim-free:

- [QRTour/ChartInvariance.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/ChartInvariance.lean)
  defines `VisibilitySignalClass`, `ChartSignature`,
  `CleanChartInvariant`, `AbsorptionStableSignal`,
  `CleanChartDistortion`, and `AbsorptionShiftDistortion`.
- It adds `ChartSignature.ofDenominator`, which records `base`,
  `blockWidth`, `base^blockWidth`, the stripped periodic modulus, and a finite
  signal class.
- It adds `ChartObservation`, which carries the selected denominator, `B`, `q`,
  `k`, requested window length, raw-prefix agreement length, incoming-carry and
  local-overflow positions, optional state-map labels, and the finite signal
  class.
- Each `ChartObservation` projects to a `ChartSignature`; the compact examples
  now flow through observations first rather than standalone signatures.
- `ChartObservation.derivedSignalClass?` now partially derives finite signal
  labels from row evidence: `transparentWindow` from full raw-prefix agreement
  and `earlyCarryIntrusion` from an incoming carry before local overflow.
- `visibleStateCompression` and `hiddenGraphObstruction` remain annotated
  state-map labels beneath the open `carry_dfa_factorization` boundary, so the
  partial classifier returns `none` for those rows.
- It adds `ChartPairWitness`, a finite witness object carrying a left chart,
  a right chart, and the certified classifier output for that selected pair.
- It proves classification, disjointness, projection, compact finite example,
  derived-signal, and finite count lemmas.
- The `ChartInvarianceExamples` namespace certifies one small witness for each
  regime: `21` for clean invariance and absorption-shift distortion, `249` for
  absorption-stable signal, and `97` for clean chart distortion.
- `compactObservations` records the twelve finite observations for `21`, `97`,
  `249`, and `996` across bases `10`, `12`, and `30`, including exact row-field
  theorems for the canonical `B`, `q`, `k`, raw-prefix, and carry-position data.
- The compact observations prove `compactObservations_derivedSignalAgreement_count = 10`:
  the ten transparent/early-carry rows are derived, while the two `97`
  state-map rows stay annotated.
- The compact `(10,12,30)` pass is represented by
  `compactBasePairWitnesses`, a twelve-witness list covering `21`, `97`,
  `249`, and `996` across the three base pairs.
- `countWitnessesForBasePair`, `countInvariantWitnessesForBasePair`, and
  `countDistortionWitnessesForBasePair` provide a tiny finite audit layer. The
  compact witnesses prove the same base-pair count shape used by the CLI
  summary: `10/12` has `2` invariant and `2` distortion witnesses, `10/30` has
  `2` and `2`, and `12/30` has `3` and `1`.
- It is claim-free in the Lean module index for now, so the empirical CLI does
  not become a theorem claim by accident.

## The Lens

Visibility Geometry treats a base/block coordinate as a chart. The source is
the remainder orbit; the signal is `qk^j`; the finite carry window is the
projection instrument; the observed trace is the carry-normalized block string.

Plainly: a decimal or block expansion is a readout. A chart observation records
one finite readout together with the arithmetic coordinate that produced it.
Lean now separates the raw finite evidence from the smaller signature used to
compare charts, so the repo can say which parts of the label are derived from
row fields and which parts remain research annotations.

Chart invariance asks:

> When do two charts preserve the same finite-window signal class, and when do
> they distort it?

The important first split is:

- clean chart invariance: signal class and stripped periodic modulus both stay
  fixed;
- absorption-stable signal: signal class stays fixed while the stripped
  periodic modulus changes;
- clean chart distortion: signal class changes while the stripped periodic
  modulus stays fixed;
- absorption-shift distortion: signal class changes while a chart also absorbs
  base-supported factors.

## Command

```bash
search-reptends chart-invariance --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

For a compact check:

```bash
search-reptends chart-invariance --max 120 --bases 10,12,30 --blocks 8 --top 5
```

## Row Groups

- `chart_invariance_summary`: selected bases, bounds, row counts, chart classes,
  and open claim boundary.
- `chart_pair_summary`: one row per base pair, with finite-window agreement,
  clean distortion, absorption distortion, and reveal/hide flip counts.
- `chart_distortion_witness`: denominator rows where signal classes change
  across charts.
- `chart_invariant_case`: denominator rows where signal classes persist across
  the selected charts.

## First Clean Distortion Witness

The first compact signal is still `1/97`:

```text
10:visible_state_compression -> 12:early_carry_intrusion -> 30:hidden_graph_obstruction
10:M=97 -> 12:M=97 -> 30:M=97
```

The stripped periodic modulus stays `97`. That makes this a clean chart
distortion witness: the same source remainder orbit is projected through
different finite carry windows and the visibility class changes.

## Absorption-Stable Calibration

The cases `249` and `996` are useful in the opposite direction:

```text
10:early_carry_intrusion -> 12:early_carry_intrusion -> 30:early_carry_intrusion
```

Their stripped periodic moduli can change under base absorption, but the
finite-window signal class persists. These are calibration anchors, not proofs
of a global invariant.

## Why This Matters

Chart invariance gives a precise empirical question behind the intuition
"different bases are different coordinate charts." It lets the repo separate:

- source-orbit behavior that appears stable under chart changes;
- chart distortions that happen without changing the stripped periodic modulus;
- absorption effects caused by the chosen base;
- reveal/hide flips in the state-map obstruction layer.

The theorem-shaped frontier is to define a true chart-equivalence relation on a
specified family of source orbits. The current CLI and Lean support surface
provide finite-window evidence and audited examples for that future definition.
