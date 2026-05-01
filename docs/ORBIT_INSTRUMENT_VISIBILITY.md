# Orbit, Instrument, Visibility

The reptend is the observed trace; the remainder orbit is the source; the
finite carry window is the instrument.

This is a reader-facing research lens, not a new theorem claim. It uses the
repo's standard labels first: remainder orbit, raw coefficient stream,
carry-propagated block normalization, and finite-window trace.

## Status

The exact support still lives in the proof-status atlas:

- `digit_periodicity` and `preperiod_from_base_factors` describe the orbit
  surface.
- `series_q_weighted_identity` and `positive_q_good_modes` describe the raw
  coefficient stream `qk^j`.
- `carry_window_transducer`, `incoming_carry_position_formula`, and
  `same_core_threshold_shift_interval` describe exact finite-window carry and
  visibility behavior already supported in the repo.

The global `carry_dfa_factorization` claim remains `open`. The minimal/global
visibility theory beneath `small_k_visibility_threshold` also remains `open`.
The language here is meant to make those frontiers easier to see, not to close
them by prose.

## The Lens

The displayed decimal is not the primary mathematical object in this lens. It
is an observation protocol.

- Source: the remainder orbit under multiplication by the block base.
- Signal: the raw coefficient stream `qk^j` from `B = qM + k`.
- Instrument: the finite carry window imposed by positional notation.
- Observation: the displayed reptend blocks after carry-propagated block
  normalization.

Said another way: the orbit is intrinsic, while the displayed block string is
what that orbit looks like after base-`B` notation has measured it.

## The Four Layers

The lens keeps the current throughline intact:

1. The remainder orbit gives the finite cyclic source.
2. The block-coordinate identity gives the raw coefficient signal `qk^j`.
3. The finite carry window normalizes that signal into admissible blocks.
4. The displayed reptend is the observed trace.

This is why carry is not just noise in the pattern. Carry is the instrument of
positional notation. It records where the raw arithmetic signal stops being
directly visible and starts being folded through the finite window.

## Canonical Trace

Use the experimental trace lens to inspect the canonical trio:

```bash
search-reptends orbit-carry-trace --base 10 --blocks 8 --members 21,97,996
```

The intended reading is:

- `21`: the instrument disappears on the visible window. The raw coefficient
  stream is constant, the carry state stays zero, and the observed trace is
  carry-free.
- `97`: the source orbit and raw signal are clean early, then incoming carry
  changes block `4` before local overflow appears at block `5`.
- `996`: the same delayed-carry visibility pattern appears with composite and
  preperiod structure; its stripped periodic core is `249`.

These are finite-window observations. They support the research lens and help
choose theorem targets, but they do not upgrade `carry_dfa_factorization` to a
closed theorem.

## What This Suggests Next

The bold next move is **Visibility Optics**: characterize when the source orbit
is readable through the finite carry window.

The current exact observables already point in that direction: incoming-carry
position, local-overflow position, raw-prefix agreement length, fixed-window
lookahead certificates, same-core shift laws, and observed state-map failures.
The experimental **Visibility Optics workbench** ranks these finite-window
signals without treating the ranking as a theorem:

```bash
search-reptends visibility-optics --max 1200 --base 10 --blocks 8 --top 20
```

The field guide for reading those rows lives in
[VISIBILITY_OPTICS_WORKBENCH.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/VISIBILITY_OPTICS_WORKBENCH.md).
To compare bases as different observation instruments, run:

```bash
search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20
```

To ask what bases reveal, absorb, distort, or obstruct across a wider panel,
run the **Instrument Atlas**:

```bash
search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

See [INSTRUMENT_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/INSTRUMENT_ATLAS.md)
for the working-axiom pressure vocabulary.

The geometry note
[VISIBILITY_GEOMETRY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/VISIBILITY_GEOMETRY.md)
connects that instrument language back to `GeometricStack`: phase space,
capacity thresholds, carry-state fibers, and base charts.
The pairwise chart comparison note
[CHART_INVARIANCE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CHART_INVARIANCE.md)
tracks finite-window invariant candidates and clean distortion witnesses.

The next frontier is to turn those observables into sharper arithmetic and
finite-state criteria while keeping `small_k_visibility_threshold` and
`carry_dfa_factorization` explicitly open until the theorem boundary truly
moves.
