# Visibility Geometry

## Status

Status: conceptual research lens, not a theorem source.

This note connects the repo's Visibility Optics and Instrument Atlas work to the
existing `GeometricStack` layer. It is meant to guide examples, vocabulary, and
future theorem targets. It does not replace the proof-status atlas, and it does
not close `small_k_visibility_threshold` or `carry_dfa_factorization`.

## The Geometric Picture

The reptend is the observed trace; the remainder orbit is the source; the
finite carry window is the instrument.

The geometric refinement is:

> A displayed expansion is a projection of finite arithmetic motion through a
> base-dependent chart.

In standard labels:

- phase space: the remainder orbit under multiplication by the block base;
- signal over the phase space: the raw coefficient stream `qk^j`;
- capacity geometry: the block capacities that decide what fits in one window;
- fiber over the orbit: the finite carry state attached to each orbit position;
- chart: the chosen base and block coordinate;
- observed trace: the carry-propagated block normalization seen in that chart.

## Geometry Already In The Repo

The repo already has a formal geometric stack surface:

- `GeometricStack.Family`: geometric powers `k^i` and capacities `base^n`;
- `GeometricStack.Capacity`: threshold indices where powers stop fitting;
- `GeometricStack.Scale`: direct part plus overflow part at a fixed scale;
- `GeometricStack.Positional`: the same decomposition as positional digits;
- `GeometricStack.OrbitBufferDuality`: orbit/buffer periodicity companion layer.

That means the geometry is not just metaphor. Overflow and carry are threshold
events in a capacity space. The displayed block is the direct part. The hidden
tail and incoming carry live in the overflow part.

## Four Geometries

### 1. Phase Geometry

The remainder orbit is finite motion:

```text
r_j -> B*r_j mod M
```

This is the source trajectory. For primes it is a cycle in a multiplicative
group; for composites it can be read through CRT product coordinates after
base-supported factors are stripped.

### 2. Capacity Geometry

The raw signal `qk^j` grows or stabilizes against a block capacity `B`.

```text
qk^j < B      raw coefficient fits the block
qk^j >= B     local overflow has appeared
```

But local overflow is not the whole visibility story. Incoming carry can arrive
from the tail before the local coefficient crosses the capacity boundary.

### 3. Fiber Geometry

The carry state is a finite fiber over each orbit position. A trace row is not
only a point of the remainder orbit; it is a pair:

```text
(remainder state, carry state)
```

The open `carry_dfa_factorization` question asks for a global structural
factorization of this combined finite machine. The current trace and workbench
surfaces only inspect bounded fibers.

### 4. Chart Geometry

A base is a chart, not the object. Changing bases changes the instrument:

```text
10:visible_state_compression -> 12:early_carry_intrusion -> 30:hidden_graph_obstruction
```

That `1/97` signature is not just a nicer or uglier notation. It says the same
source orbit can project through different carry windows with different
visibility behavior.

## Canonical Picture: 1/97

In base `10` with block base `B = 100`:

```text
B = 1*97 + 3
raw signal: 1, 3, 9, 27, 81, 243, ...
observed blocks: 01 03 09 27 83 ...
```

Position `4` receives incoming carry before the local raw coefficient overflows
at position `5`. Geometrically, the tail has crossed the finite-window boundary
before the local point itself exits the capacity band.

The Instrument Atlas then changes the chart:

```text
10:visible_state_compression -> 12:early_carry_intrusion -> 30:hidden_graph_obstruction
```

The stripped periodic modulus stays `97` across those bases, so this is a clean
instrument effect rather than only base-factor absorption.

## Composite Product Geometry

Composite examples add product geometry. CRT decomposes the periodic orbit into
component motions, while base-supported factors create preperiod directions that
are absorbed before the purely periodic core is reached.

This is why cases such as `249` and `996` are valuable. They help separate:

- periodic-core motion;
- base-factor absorption;
- same-core threshold shifts;
- carry-window visibility.

The geometry is not one picture. It is a product picture plus a projection.

## What This Suggests Next

The bold research direction is to classify instruments by their projections.

Working questions:

- Which base/block charts preserve the readability of the source orbit?
- Which charts create early-carry turbulence?
- Which charts reveal or hide state-map obstruction?
- Which signatures survive across charts and become calibration anchors?
- Can two base instruments be equivalent on a family of source orbits?

The next empirical move is to search for maximal instrument flips: cases that
are transparent or visibly compressed in one chart and hidden-obstructed in
another, especially when the stripped periodic modulus does not change.

The chart-invariance layer now gives that question a finite formal grammar:
observed rows project to chart signatures, selected chart pairs receive
certified finite classifications, and compact witness counts can be audited in
Lean.

The empirical surface for that question is:

```bash
search-reptends chart-invariance --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

See [CHART_INVARIANCE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CHART_INVARIANCE.md)
for the chart-pair vocabulary and the clean distortion witness `1/97`.
The Lean foothold for this vocabulary is
[QRTour/ChartInvariance.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/ChartInvariance.lean),
which now records finite `ChartObservation` rows, projects them to
`ChartSignature`s, certifies selected `ChartPairWitness` classifications, and
audits the compact `(10,12,30)` family by count.

That formal layer is intentionally partial. It derives `transparentWindow` and
`earlyCarryIntrusion` from finite row evidence, but keeps
`visibleStateCompression` and `hiddenGraphObstruction` as annotated state-map
signals beneath the open `carry_dfa_factorization` boundary.
