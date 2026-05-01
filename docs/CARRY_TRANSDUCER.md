# Carry Transducer Model

Status anchor:

<!-- CARRY_TRANSDUCER_STATUS_ANCHOR_START -->
- Claim ID `carry_window_transducer` is `implemented-here`.
- Claim ID `small_k_visibility_threshold` remains `open` and is now split into exact observables in [CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md).
- Claim ID `carry_dfa_factorization` remains `open`.
- Preferred standard label: `carry-propagated block normalization`.
<!-- CARRY_TRANSDUCER_STATUS_ANCHOR_END -->

This layer is the clean standard language for what the repo used to describe informally as “carry correction.”

## The Three Objects

For a chosen block base `B = base^m`, the repo now separates three standard objects:

1. The remainder orbit under multiplication by the base.
2. The raw coefficient stream `qk^j`.
3. The carry transducer that normalizes those coefficients into displayed blocks.

The long-division DFA and the carry transducer are not the same machine.

- The long-division DFA uses remainder states and emits displayed blocks directly.
- The carry transducer uses carry states and consumes the raw coefficient stream.
- On the finite window used by the repo, both produce the same displayed block word.
- Lean now also packages aligned finite state records carrying
  `(position, coefficient, carryIn, carryOut, remainderIn, remainderOut)` on
  those windows, together with the exact local carry-balance and
  remainder-balance equations at each aligned position, plus exact
  finite-window functional criteria for the observed remainder-to-carry and
  carry-to-remainder state-pair lists, finite transition-compatibility
  theorems under those criteria, and explicit finite conflict lemmas when the
  observed pair list violates them.

That is the implemented bridge, not yet a full canonical factorization theorem.

## Throughline Ladder

Read this note as the carry-facing slice of the repo's orbit-plus-carry
research thesis. The ladder below keeps the exact orbit layer, the exact
block-coordinate layer, the implemented finite-window carry layer, and the
remaining open frontier explicit in one place.

<!-- CARRY_TRANSDUCER_THROUGHLINE_START -->
| Ladder rung | Registry support |
|-------------|------------------|
| Exact orbit support | Claims `digit_periodicity` and `preperiod_from_base_factors`; witnesses `digit_periodicity_prime19_base10` and `preperiod_from_base_factors_n996_base10`. Remainder periodicity and stripping of base-supported factors fix the exact orbit surface before any carry-normalization claim enters. |
| Exact block-coordinate support | Claims `series_q_weighted_identity` and `positive_q_good_modes`; witnesses `series_q_weighted_identity_prime97_stride2`, `series_q_weighted_identity_n249_stride3`, and `positive_q_good_modes_n249_stride3`. The raw coefficient stream is exactly `qk^j`, and the repo only promotes positive-q coordinates once `B > M`. Counterexamples: `legacy_unweighted_series_37` and `legacy_zero_quotient_mode`. |
| Implemented finite-window carry support | Claims `incoming_carry_position_formula`, `same_core_threshold_shift_interval`, and `carry_window_transducer`; witnesses `incoming_carry_position_formula_prime97_stride2`, `incoming_carry_position_formula_n249_stride3`, `same_core_threshold_shift_interval_996_over_249`, `carry_window_transducer_prime97_window6`, `carry_window_transducer_n249_window3`, and `carry_window_transducer_same_core_996_window4`. Finite-window carry-normalized output, exact incoming-carry boundaries, and same-core shift transport are already exact on named windows. Counterexamples: `legacy_visibility_local_overflow_97` and `legacy_visibility_local_overflow_249`. |
| Obstruction / counterexample surface | Claims `carry_dfa_factorization`; witnesses `carry_dfa_factorization_target_21_97_996` and `carry_dfa_factorization_target_249_498_996_same_core`. Observed state-map failures now split into visible preimage compression, hidden graph obstruction, and selector-profile disagreement, showing why finite output agreement does not by itself promote to a state-level theorem. Counterexamples: `carry_state_relabeling_failure_97`, `carry_state_relabeling_failure_996`, `carry_selector_monotonicity_failure_21`, and `carry_selector_core_invariance_failure_996`. |
| Open factorization targets | Claims `small_k_visibility_threshold` and `carry_dfa_factorization`; witnesses `small_k_visibility_threshold_target_97_249_996`, `carry_dfa_factorization_target_21_97_996`, and `carry_dfa_factorization_target_249_498_996_same_core`. The remaining frontier is an exact visibility threshold and a canonical orbit-plus-carry factorization, both kept explicitly open. Counterexamples: `carry_selector_core_invariance_failure_996`. |
<!-- CARRY_TRANSDUCER_THROUGHLINE_END -->

## API Surface

In [transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py):

- `CarryTransducer` is the finite-window normalization machine.
- `CarryRun` stores one concrete run.
- `CarryRun.state_summary()` exposes reachable carry states and the first nonzero carry position.
- `StateGraph` and `MinimizedStateGraph` give the stable observed-graph interface used by both the carry transducer and the remainder DFA.
- `CarryRun.state_summary().graph()` builds the carry-state graph, while `CarryRun.state_summary().minimize()` gives the coarse observed minimization used by the repo.
- `remainder_dfa_run(N, block_base, steps)` builds the long-division DFA run in the same block coordinates.
- `carry_remainder_comparison(N, ...)` packages the finite-window agreement statement, the two graph objects, and the explicit open-boundary wording.
- `ObservedStateMap` now exports the full preimage-fiber profile (state-merging atlas): source fibers, target preimage fibers, visible compression targets, ambiguity records, and compact signature strings in both directions.
- `FactorizationDecisionReport` turns one comparison into a Track 17 decision object: state relabeling candidate, quotient candidate, lift candidate, theorem target, refutation target, and weaker replacement claim.
- `carry_factorization_selector_profile(...)` records how the Track 17 regime changes as the block width `m` varies.
- `state_merging_rows(...)` exports the selected-coordinate preimage-fiber profile directly, together with the visible-vs-hidden obstruction classifier, graph gaps, and short obstruction summaries.
- `state_merging_same_core_rows(...)` groups those selected profiles by stripped periodic core and records where same-core families span relabeling, hidden graph obstruction, and visible compression.
- `same_core_obstruction_phase_rows(...)` turns those same-core families into phase paths, recording first hidden and visible members, re-hiding after visibility, and hidden/visible switch counts.
- `same_core_obstruction_correlate_rows(...)` summarizes bounded empirical correlates of re-hiding versus one-way visibility, including onset kind and first hidden/visible multiplier valuations on the base-10 same-core surface.
- `quotient_obstruction_rows(...)` exports the quotient-only split directly as visible preimage compression versus hidden graph obstruction.
- `quotient_obstruction_family_rows(...)` groups same-core families by whether that visible/hidden split changes across members.
- `carry_selector_profile_rows(...)` exports the selector classification surface directly.
- `non_k_one_state_relabeling_rows(...)` isolates the selected non-`k = 1` relabeling windows.
- `same_core_selector_family_rows(...)` groups selector profiles by stripped periodic core and records where families disagree.
- `canonical_carry_dfa_examples()` returns the named `21`, `97`, `996` comparison suite used across docs, tests, and the published atlas.
- `canonical_carry_selector_case_studies()` and `canonical_carry_selector_family_studies()` promote the strongest selector findings into the published atlas as a research layer.
- `canonical_state_merging_case_studies()` and `canonical_state_merging_family_studies()` promote the canonical `21 / 97 / 89 / 996` and `249 / 498 / 996`, `17 / 34 / 68 / 85` obstruction studies into the published atlas.
- `carry_factorization_rows(...)` performs bounded Track 17 sweeps so candidate notions can be tested on concrete examples before theorem promotion.
- `carry_window_example(N, ...)` builds the combined view:
  raw coefficients, carry-normalized blocks, and long-division blocks.
  When a finite raw prefix is not enough, it automatically adds a small lookahead so the visible block window matches long division exactly.
- `orbit_carry_trace_rows(...)` exports an experimental finite trace lens for
  canonical examples such as `21 / 97 / 996`, aligning cycle index, remainder
  orbit state, raw coefficient, finite carry-window state, and displayed block
  without upgrading `carry_dfa_factorization` beyond its current open status.
- `visibility_optics_workbench_rows(...)` ranks finite-window evidence across
  carried-prefix visibility, orbit/carry trace anchors, state-map compression,
  and same-core drift. It is a probe for the **Visibility Optics workbench**,
  not a proof of global visibility or DFA factorization.

Minimal example:

```python
from bridge_reptends import carry_window_example

example = carry_window_example(97, prefer_m=2, n_blocks=8)
summary = example.run.state_summary()

print(example.raw_coefficients[:8])
print(example.carried_blocks[:8])
print(example.actual_blocks[:8])
print(summary.reachable_states)
print(summary.first_nonzero_position)
print(summary.to_dot())
```

## Experimental Orbit-Carry Trace Lens

The command below is a campfire-friendly report surface for the current thesis:

```bash
search-reptends orbit-carry-trace --base 10 --blocks 8 --members 21,97,996
```

For a broader ranked probe, use:

```bash
search-reptends visibility-optics --max 1200 --base 10 --blocks 8 --top 20
```

Read [VISIBILITY_OPTICS_WORKBENCH.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/VISIBILITY_OPTICS_WORKBENCH.md)
for the signal classes, row groups, and recommended drill-down commands.
The companion base-instrument comparison keeps base `30` as data rather than
as a new default representation:

```bash
search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20
```

The **Instrument Atlas** broadens that probe into base-level profiles and
working-axiom pressure rows:

```bash
search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

The guiding lens is: the reptend is the observed trace; the remainder orbit is
the source; the finite carry window is the instrument. In standard terms, the
trace lens aligns the remainder orbit, raw coefficient stream, and
carry-propagated block normalization so the displayed blocks can be read as an
observation of the orbit through positional notation.

It emits three row groups:

- `case_summary`: the block coordinate, stripped periodic modulus, period,
  lookahead, output agreement, and finite-window factorization regime.
- `trace_step`: one row per visible block, including the cycle index,
  remainder input/output, raw coefficient, carry input/output, displayed block,
  and a visibility event such as `carry_free_raw`,
  `incoming_carry_before_overflow`, or `local_overflow`.
- `state_map_summary`: the observed finite-window functional/injective status
  and signatures in both the remainder-to-carry and carry-to-remainder
  directions.

This lens is intentionally experimental. It is a way to inspect the finite
carry window over the closed remainder orbit, not a new theorem claim and not a
replacement for the open `carry_dfa_factorization` boundary.

## Small Examples

### `N = 21`

In the small-residue block coordinate `10^6 = 47619 * 21 + 1`, the raw coefficients are constant and already below the block base.

- raw coefficients: constant `47619`
- reachable carry states: only `(0,)`
- reachable remainder states in the same block coordinate: only `(1,)`
- interpretation: this is the trivial observed state-relabeling case

This is the cleanest example where the carry layer disappears completely on the
visible window. It is useful in Track 17 precisely because it is the only
canonical case where a simple one-state relabeling survives the full observed
comparison.

### `N = 97`

This is the best small example where the carry-state view adds real information.

- raw coefficients begin as `1, 3, 9, 27, 81, 243, ...`
- displayed blocks begin as `01, 03, 09, 27, 83, 50, ...`
- the first nonzero carry position is block `4`

The key point is that the raw coefficient `81` is still below `100`, but that block becomes `83` because a carry of `2` arrives from the less significant side. A raw block table alone does not make that dependency explicit; the carry-state graph does.

### `N = 89`

This is the clean hidden-obstruction case.

- the aligned finite window is bijective in both directions
- the selected profile shows no visible compression targets
- the observed carry graph and remainder graph still have different sizes

So the failure is real, but it does not live in the preimage fibers. It only
appears once the graph layer is compared to the aligned window.

### `N = 996`

This is the best example where the carry model and the composite model meet.

- the stripped periodic core is `249`
- the actual denominator still has the bridge-style coordinate `10^3 = 1 * 996 + 4`
- the carry states are nontrivial, but the displayed blocks still match the long-division output exactly through `carry_window_example(...)`

This is why `996` is a useful case study: preperiod, composite CRT structure, and carry normalization all appear in one example, while the state-level relation still looks like a quotient candidate rather than a relabeling.

## Track 17 Factorization Ladder

Track 17 now separates four candidate levels instead of one vague open claim.

1. Finite-window word agreement.
   This is implemented: on the visible window, the carry transducer and the long-division DFA emit the same displayed block word.
2. Observed state relabeling.
   This asks whether the observed carry states and remainder states are just two names for the same finite-state run.
3. Observed quotient or lift candidates.
   This asks whether the aligned window defines a functional map from remainder states to carry states, from carry states to remainder states, or both.
4. Canonical global factorization.
   This is still open: a base- and modulus-uniform theorem that long division factors canonically into orbit plus carry.

The repo now makes these distinctions explicitly through
[transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py):

- `21` is the trivial `state_relabeling` case.
- `97` and `996` are `quotient_candidate_only` cases:
  the observed remainder-to-carry map is functional, but the carry-to-remainder
  map is not, so a simple state relabeling already fails on the canonical window.

The new preimage-fiber profile (state-merging atlas) is the finite-window view
of that asymmetry. It does not claim a theorem. It now separates two exact
finite-window obstruction types:

- visible preimage compression: the collapse is already visible in the target fibers
- hidden graph obstruction: the aligned window stays bijective, but the graph layer still blocks relabeling

The newest same-core family rows add a further empirical signal: those hidden
and visible phases need not be monotone under base-supported deformation. In
families like `17 / 34 / 68 / 85 / 136`, visible compression can appear and
then re-hide back into hidden graph obstruction on later same-core members.

At the larger bounded search surface `N <= 2000`, the current classifier shows
two especially sharp empirical correlates:

- `visible_without_hidden` families are one-way visible on the selected window
- `visible_first` families re-hide later in the same-core path

That is still a dataset statement, not a theorem, but it is now exported
directly by `same_core_obstruction_correlate_rows(...)`.

## Decision Criteria

Track 17 is now decision-complete in the following sense.

## Flagship Candidate Statements

Before further search or Lean promotion, Track 17 now commits to one exact
positive candidate and one exact obstruction candidate.

`Positive candidate (restricted remainder-to-carry factorization)`:

For a fixed coprime block coordinate `C`, assume that every finite aligned
carry/remainder window for `C` satisfies all three of the currently exposed
finite criteria:

- finite-word output agreement,
- `remainderToCarryFunctional`,
- remainder-to-carry transition compatibility.

Then there exists a unique orbit-level map `φ_C` from the reachable remainder
states of the long-division DFA to the reachable carry states of the carry
transducer such that:

- `φ_C` sends each observed `remainderIn` state to the corresponding
  `carryIn` state,
- `φ_C` intertwines the remainder update with the carry update driven by the
  raw coefficient stream `qk^j`,
- the carry transducer started from `φ_C(r_0)` emits exactly the long-division
  block word on the full orbit.

This is the first positive theorem candidate for `carry_dfa_factorization`.
It is intentionally coordinate-level; it does not yet assert a base- and
modulus-uniform global factorization theorem.

Lean packages this modest surface in
[QRTour/Factorization.lean](/Users/mikepurvis/other/quadratic-residue-reptends/lean/QRTour/Factorization.lean)
as factorization-frontier support: restricted finite-window morphisms for `21`
and `97`, plus the `996` same-core reverse obstruction, without promoting a
global factorization theorem.

`Obstruction candidate (core/output insufficiency)`:

No canonical factorization theorem for all coprime moduli can depend only on
stripped periodic core, visible output agreement, and the exact same-core shift
data already proved in Lean. In particular, in base `10` the same-core family
with core `249` has a member `249` with an observed `state_relabeling` window
at `m = 6`, while the same-core members `498` and `996` remain
`quotient_candidate_only` on the tested selector surface. Therefore any valid
global theorem must use finer arithmetic than periodic core plus visible-word
data.

The `17 -> 34` selector-family shift is the secondary obstruction family: small
multiple moves can preserve and enlarge relabeling windows rather than merely
shifting them monotonically.

What would count as a theorem:

- a proof of the positive candidate above, or
- a stronger proof that the machines are actually state-relabelings in a
  uniform class of examples.

What would count as a refutation:

- a bounded example where finite-window word agreement holds but even the
  observed remainder-to-carry quotient candidate fails, or
- a proof of the obstruction candidate above, or
- a family where any proposed state-level factorization notion changes form
  unpredictably under harmless coordinate changes.

What would count as a weaker replacement claim:

- finite-window word agreement plus an observed quotient-from-remainder-to-carry
  framework, without asserting a unique or canonical global factorization.

## Bounded Search Surface

The repo now exposes a bounded Track 17 search via:

`search-reptends carry-factorization --max 500 --blocks 8`

This exports, for each tested denominator:

- whether finite-window outputs match,
- whether a simple observed state relabeling candidate holds,
- whether the observed remainder-to-carry quotient candidate holds,
- whether the observed carry-to-remainder lift candidate holds,
- whether the example is already a counterexample to naive state relabeling.

The canonical search outcomes are:

- `21`: trivial state relabeling
- `97`: counterexample to state relabeling, but positive evidence for the quotient candidate
- `996`: the same quotient-only regime in a composite/preperiod setting

## Selector Signal

The selector itself now exposes signal, not just a chosen `m`.

For fixed `N`, the function `carry_factorization_selector_profile(...)` scans
candidate block widths and records the regime transition signature.

Canonical profiles:

- `21` in base `10`: `finite_word_only -> state_relabeling -> finite_word_only`
- `249` in base `10`: `quotient_candidate_only -> state_relabeling -> quotient_candidate_only`
- `996` in base `10`: `quotient_candidate_only` only

The repo now exposes direct family comparison objects through
`compare_carry_selector_profiles(...)`.

Current high-signal family comparisons:

- same-core loss: `249 -> 996` in base `10`
  - `249` has an isolated relabeling window at `m = 6`
  - same-core `996` loses that window entirely
- multiple-family shift: `17 -> 34` in base `10`
  - `17` has relabeling at `m = 5`
  - `34` keeps `m = 5` and gains an extra relabeling window at `m = 7`

This matters for two reasons:

- state-relabeling windows can be isolated and nonmonotone in `m`,
- the same periodic core does not determine the selector profile, since `249`
  and `996` have different Track 17 signatures,
- small multiple families can preserve, shift, enlarge, or destroy relabeling
  windows rather than behaving monotonically.

The new search surface

`search-reptends carry-factorization-selector --max 300 --blocks 8`

exports these profiles directly, so the selector can be studied as a family
object rather than only as a hidden optimization heuristic.

Two additional search surfaces now make the classification systematic:

- `search-reptends carry-selector-non-k1 --max 400 --blocks 8`
- `search-reptends carry-selector-same-core --max 400 --blocks 8`
- `search-reptends carry-selector-research --max 120 --bases 7,10,12 --blocks 8`

These are the reason selector profiles have now been promoted into the
published atlas layer: the repo has stable case studies, stable family studies,
and explicit grouped disagreement outputs rather than only local experiments.

The bounded cross-base summary used in the published atlas currently reports:

- base `7`, `N <= 120`: `26` selected non-`k = 1` relabeling windows and `14` same-core disagreement groups
- base `10`, `N <= 120`: `21` selected non-`k = 1` relabeling windows and `19` same-core disagreement groups
- base `12`, `N <= 120`: `14` selected non-`k = 1` relabeling windows and `14` same-core disagreement groups

This is enough signal to justify a published research layer while still
keeping the stronger theorem-level factorization claim open.

## Implemented Boundary vs Open Claim

What is implemented now:

- the raw coefficient stream `qk^j`,
- the carry transducer and its observed state graph,
- the remainder DFA in the same block coordinates,
- finite-window comparison reports showing that both machines emit the same displayed block word on the visible window,
- explicit observed state-map candidates in both directions,
- a decision framework separating state relabeling, quotient candidates, and the still-open global theorem,
- bounded search rows that surface counterexamples to the strongest naive state-level claim before theorem promotion.

What remains open:

- a canonical global factorization theorem identifying long division with orbit plus carry for all coprime moduli,
- uniqueness statements for that factorization beyond the current explicit examples and finite-window comparisons.
- cleaner closed forms for visibility lookahead and broader global carried-prefix behavior; that Track 16 framework now lives in [docs/CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md).

## Why This Matters

The carry transducer gives the repo a standard finite-state object for the carry layer.

- It exposes reachable carry states instead of only final digits.
- It exports a state graph that can be rendered or compared across examples.
- It makes the relation between raw coefficients and displayed blocks inspectable.

That is higher-signal than introducing more special vocabulary, because it lands on a standard automata/transducer model.
