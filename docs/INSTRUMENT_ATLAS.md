# Instrument Atlas

## Status

Status: empirical finite-window research surface, not a theorem source.

The Instrument Atlas compares bases as observation instruments. It asks what
each base reveals, absorbs, distorts, or obstructs when the same denominator is
viewed through the finite carry window. It is meant to pressure working axioms,
not to promote a preferred base representation or prove global visibility.

The open boundary remains explicit: `small_k_visibility_threshold` and
`carry_dfa_factorization` are still `open`.

## The Question

The Visibility Optics lens says:

> The reptend is the observed trace; the remainder orbit is the source; the
> finite carry window is the instrument.

The atlas takes the next step: if the base is part of the instrument, then base
choice should be studied as data. A base can make a finite-window trace look
transparent, carry-turbulent, absorptive, or obstructed.

This does not mean base `30` is the natural notation. Base `30` is useful
because it absorbs more small-prime factors, which makes it a deliberately
biased probe. That bias is information.

## Command

```bash
search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

For the smaller decimal/base-30 comparison used in the first pass:

```bash
search-reptends instrument-atlas --max 120 --bases 10,12,30 --blocks 8 --top 5
```

## Row Groups

- `instrument_atlas_summary`: selected bounds, base list, row counts, signal
  vocabulary, and open claim boundary.
- `instrument_profile`: one row per base, with finite-window counts and an
  empirical instrument personality such as `absorptive_instrument`,
  `obstruction_revealer`, or `carry_turbulent_instrument`.
- `instrument_case`: one denominator compared across bases, including the
  instrument signature, absorption signature, reveal/obstruction bases, and
  working-axiom pressure labels.
- `working_axiom_signal`: compact prompts for revising the working vocabulary
  against the finite evidence.

## Example Signal

The case `1/97` pressures the denominator-only viewpoint:

```text
10:visible_state_compression -> 12:early_carry_intrusion -> 30:hidden_graph_obstruction
```

The stripped periodic modulus stays `97`, so this is not just base-factor
absorption. The same source orbit is being observed through different finite
carry instruments.

The case `1/21` pressures a different assumption:

```text
10:transparent_window -> 12:early_carry_intrusion -> 30:early_carry_intrusion
```

Here base `12` and base `30` absorb denominator factors and change the stripped
periodic modulus from `21` to `7`. That makes absorption visible as an
instrument effect.

## Working Axiom Pressure

The atlas currently uses these empirical pressure labels:

- `recoverability_is_instrument_relative`: recoverability from the finite-window
  trace depends on denominator, base, block coordinate, and carry machine.
- `factor_absorption_changes_periodic_core`: base-factor absorption can change
  the stripped periodic modulus and should not be treated as a neutral
  simplification.
- `visible_trace_can_hide_state_obstruction`: a base can make a state-map
  obstruction visible, hidden, or irrelevant to the displayed finite trace.
- `candidate_base_stable_calibration_case`: cases stable across bases are useful
  anchors for separating source behavior from instrument behavior.

These are working research prompts. They do not replace the proof-status atlas.

## Where It Fits

Use the Instrument Atlas after:

```bash
search-reptends visibility-optics --max 1200 --base 10 --blocks 8 --top 20
search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20
```

Then drill into individual cases with:

```bash
search-reptends orbit-carry-trace --base 10 --blocks 8 --members 21,97,996
```

The atlas is a scouting instrument for the next theorem questions: characterize
when a source remainder orbit is recoverable from its carry-normalized trace,
and how that recoverability changes when the observation instrument changes.

For the geometric vocabulary behind "instrument" and "chart", read
[VISIBILITY_GEOMETRY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/VISIBILITY_GEOMETRY.md).
For the pairwise chart comparison surface, read
[CHART_INVARIANCE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CHART_INVARIANCE.md)
and run:

```bash
search-reptends chart-invariance --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```
