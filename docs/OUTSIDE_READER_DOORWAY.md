# Outside Reader Doorway

## Status

This note is a conceptual invitation for mathematically curious readers. It is
not the proof-status source of truth. For theorem status, use
[PROOF_STATUS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/PROOF_STATUS_ATLAS.md).

The repo studies how hidden arithmetic dynamics become observed traces through
finite representational instruments.

## The Doorway

The decimal is a readout, not the object.

A repeating decimal is exact, but it is not the whole structure. It is what a
source arithmetic motion looks like after passing through a positional
coordinate system. In this repo's current language:

- the remainder orbit is the source,
- the raw coefficient stream `qk^j` is the signal,
- carry-propagated block normalization is the finite carry window,
- the displayed reptend is the finite-window trace.

So the question is not only, "what digits repeat?" It is also, "what source
motion became visible as those digits, and what did the instrument conceal?"

## One Example

Take `1/97` in two-digit blocks, so `B = 100`.

The block coordinate is:

```text
B = 100 = 1 * 97 + 3
q = 1
k = 3
```

The raw coefficient stream begins:

```text
1, 3, 9, 27, 81
```

But the observed blocks begin:

```text
01 03 09 27 83
```

The `83` is the revealing moment. The local raw coefficient is still `81`,
which fits inside a two-digit block. But incoming carry from the less
significant tail changes what the finite carry window displays. The decimal did
not lie; it showed the source through the instrument.

## What The Repo Actually Tracks

The project keeps these layers separate:

- remainder orbit: the cyclic state system under multiplication by the block
  base;
- raw coefficient stream: the exact `qk^j` coefficients coming from
  `B = qM + k`;
- carry-propagated block normalization: the deterministic finite carry process;
- finite-window trace: the displayed blocks and event labels visible in a
  bounded window.

This is why the project treats carries as part of the observation apparatus,
not as decorative arithmetic noise.

## What Is Known And What Is Open

Several pieces are exact or implemented here:

- `series_q_weighted_identity` gives the exact raw coefficient identity;
- `positive_q_good_modes` keeps the positive-q coordinate boundary explicit;
- `carry_window_transducer` implements the finite carry window;
- `incoming_carry_position_formula` and `same_core_threshold_shift_interval`
  expose exact finite-window observables.

The bigger frontiers remain open:

- `small_k_visibility_threshold`: the minimal/global visibility theory;
- `carry_dfa_factorization`: the global canonical factorization of long
  division into orbit plus carry.

Those open labels are a feature of the repo's discipline. They keep the
invitation vivid without letting the prose outrun the proof boundary.

## Try One Command

Start with the canonical trace:

```bash
search-reptends orbit-carry-trace --base 10 --blocks 8 --members 21,97,996
```

Then use the broader ranked workbench:

```bash
search-reptends visibility-optics --max 1200 --base 10 --blocks 8 --top 20
```

To see how the chosen base changes the observation instrument, compare bases:

```bash
search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20
```

To compare bases by what they reveal, absorb, distort, or obstruct, use the
Instrument Atlas:

```bash
search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

Read the output as finite evidence. It is a way to choose examples and sharpen
questions, not a theorem by itself.

## Where To Go Next

- [ORBIT_INSTRUMENT_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/ORBIT_INSTRUMENT_VISIBILITY.md)
  gives the campfire-to-math lens.
- [VISIBILITY_OPTICS_WORKBENCH.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/VISIBILITY_OPTICS_WORKBENCH.md)
  explains the workbench row groups and signal classes.
- [INSTRUMENT_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/INSTRUMENT_ATLAS.md)
  compares bases as observation instruments.
- [VISIBILITY_GEOMETRY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/VISIBILITY_GEOMETRY.md)
  connects the lens to phase space, capacity thresholds, carry fibers, and base
  charts.
- [CHART_INVARIANCE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CHART_INVARIANCE.md)
  compares base-chart pairs for invariant candidates and clean distortion
  witnesses.
- [CARRY_TRANSDUCER.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRY_TRANSDUCER.md)
  documents the finite carry transducer and state-map frontier.
