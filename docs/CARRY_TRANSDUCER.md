# Carry Transducer Model

Status anchor:

- Claim ID `carry_window_transducer` is `implemented-here`.
- Claim ID `small_k_visibility_threshold` remains `open` and is now split into exact observables in [docs/CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md).
- Claim ID `carry_dfa_factorization` remains `open`.
- Preferred standard label: `carry-propagated block normalization`.

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

That is the implemented bridge, not yet a full canonical factorization theorem.

## API Surface

In [transducer.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/transducer.py):

- `CarryTransducer` is the finite-window normalization machine.
- `CarryRun` stores one concrete run.
- `CarryRun.state_summary()` exposes reachable carry states and the first nonzero carry position.
- `StateGraph` and `MinimizedStateGraph` give the stable observed-graph interface used by both the carry transducer and the remainder DFA.
- `CarryRun.state_summary().graph()` builds the carry-state graph, while `CarryRun.state_summary().minimize()` gives the coarse observed minimization used by the repo.
- `remainder_dfa_run(N, block_base, steps)` builds the long-division DFA run in the same block coordinates.
- `carry_remainder_comparison(N, ...)` packages the finite-window agreement statement, the two graph objects, and the explicit open-boundary wording.
- `ObservedStateMap` records whether the observed carry-state and remainder-state alignments define functional or injective state-map candidates.
- `FactorizationDecisionReport` turns one comparison into a Track 17 decision object: state relabeling candidate, quotient candidate, lift candidate, theorem target, refutation target, and weaker replacement claim.
- `carry_factorization_selector_profile(...)` records how the Track 17 regime changes as the block width `m` varies.
- `carry_selector_profile_rows(...)` exports the selector classification surface directly.
- `non_k_one_state_relabeling_rows(...)` isolates the selected non-`k = 1` relabeling windows.
- `same_core_selector_family_rows(...)` groups selector profiles by stripped periodic core and records where families disagree.
- `canonical_carry_dfa_examples()` returns the named `21`, `97`, `996` comparison suite used across docs, tests, and the published atlas.
- `canonical_carry_selector_case_studies()` and `canonical_carry_selector_family_studies()` promote the strongest selector findings into the published atlas as a research layer.
- `carry_factorization_rows(...)` performs bounded Track 17 sweeps so candidate notions can be tested on concrete examples before theorem promotion.
- `carry_window_example(N, ...)` builds the combined view:
  raw coefficients, carry-normalized blocks, and long-division blocks.
  When a finite raw prefix is not enough, it automatically adds a small lookahead so the visible block window matches long division exactly.

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

## Decision Criteria

Track 17 is now decision-complete in the following sense.

What would count as a theorem:

- a proof that the finite-window quotient candidate extends to a canonical
  remainder-to-carry morphism on full orbits, or
- a stronger proof that the machines are actually state-relabelings in a
  uniform class of examples.

What would count as a refutation:

- a bounded example where finite-window word agreement holds but even the
  observed remainder-to-carry quotient candidate fails, or
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
