# Carried-Prefix Visibility Framework

Status anchor:

- Claim ID `small_k_visibility_heuristic` is `empirical`.
- Claim ID `incoming_carry_position_formula` is `classical` and implemented in the repo.
- Claim ID `small_k_visibility_threshold` remains `open`.
- Preferred standard labels: `raw coefficient stream`, `carry-propagated block normalization`, `raw-prefix agreement length`.

Track 16 replaces the vague phrase "visibility threshold" with exact finite-window observables.
The current repo state now closes three subproblems exactly:

- the incoming-carry boundary,
- the raw-prefix agreement boundary,
- a finite-window stabilization certificate for `lookahead_blocks`.

## Exact Inputs and Outputs

For a chosen denominator `N`, base `base`, and block coordinate `B = base^m = qN + k`, the repo now measures:

- `q`, `k`, `B`, and the block width `m`,
- the periodic modulus and its period data,
- the decimal preperiod length,
- the requested visible block count,
- the minimal lookahead needed to stabilize that visible window,
- the first local overflow position where `qk^j >= B`,
- the first incoming-carry position where a later overflow changes an earlier visible block,
- the exact raw-prefix agreement length: how many initial displayed blocks still equal the literal zero-padded raw coefficients `qk^j`.

These are exposed in [visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/visibility.py) through:

- `carried_prefix_visibility_profile(...)`
- `canonical_visibility_case_studies()`
- `canonical_visibility_family_studies()`
- `visibility_profile_rows(...)`

## Implemented Exact Boundary

One subproblem is now closed exactly.

For the raw coefficient stream `c_j = qk^j`, the tail beyond block `j` is

`Σ_{t>=1} qk^(j+t) / B^t = qk^(j+1) / (B-k)`

so the incoming carry into block `j` is

`carry_in(j) = floor(qk^(j+1)/(B-k))`.

Therefore the first incoming-carry position is the least `j` with

`qk^(j+1) >= B-k`.

This is exposed directly through
[visibility.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/visibility.py):

- `incoming_carry_value(...)`
- `predicted_first_incoming_carry_position(...)`

## Quantitative Lookahead Bounds

Two arithmetic controls for `lookahead_blocks` are now implemented.

Necessary lower bound:

If the omitted tail after `n + L - 1` still contributes at least one full block
unit to the visible prefix integer, stabilization is impossible. This yields

`qk^(n+L) < B^L(B-k)`.

The least `L` satisfying this is exposed as
`lookahead_tail_mass_lower_bound(...)`.

Lean now formalizes this lower-bound inequality as a necessary consequence of
the exact fixed-window certificate, so the coarse tail-mass bound and the exact
gap certificate now sit in one theorem layer rather than only in parallel code.

Exact finite-window certificate:

Let `x_L` be the truncation through block `n + L - 1`. Writing

`B^n x_L = I + r_L / B^L`,

the first `n` visible blocks stabilize exactly when the omitted tail is smaller
than the gap to the next integer:

`qk^(n+L) < gap_L (B-k)`,

where `gap_L = B^L - r_L` when `r_L > 0`, and `gap_L = B^L` when `r_L = 0`.

This is exposed through:

- `lookahead_gap_numerator(...)`
- `lookahead_certificate_holds(...)`
- `certified_lookahead_blocks(...)`

Lean now also proves that once this exact certificate holds at some lookahead
`L`, it continues to hold for any larger lookahead window. This is a finite
transport theorem for already-stabilized visible prefixes, not a theorem about
the least/global lookahead itself.

## Implemented Relation for the Visible Raw Prefix

For the finite windows the repo computes exactly, one implemented relation is now explicit:

`raw-prefix agreement length = min(local overflow boundary, incoming-carry boundary)`

This is not the remaining open claim. It is the exact decomposition of the measured window into two failure modes:

1. the local coefficient itself stops fitting in one block, or
2. incoming carry from the tail alters an earlier still-legal coefficient.

The remaining open claim is the search for a sharp arithmetic formula for stabilization lookahead and the larger global visibility behavior once those boundaries are known.

## Canonical Case Studies

### `1/21`

- regime: `fully_visible_window`
- role: positive-`q`, carry-free baseline
- lesson: `q > 1` does not by itself destroy readability

### `1/37`

- regime: `fully_visible_window`
- role: positive-`q` constant-coefficient case
- lesson: `k = 1` can completely suppress carry interaction on the visible window

### `1/97`

- regime: `incoming_carry_before_local_overflow`
- role: primary counterexample target for naive `qk^j < B` visibility rules
- lesson: the raw coefficient `81` is still below `100`, but an incoming carry changes the displayed block to `83`

### `1/249`

- regime: `incoming_carry_before_local_overflow`
- role: positive-`q` counterexample to the same naive rule
- lesson: early carry intrusion is not a `q = 1` only phenomenon

### `1/996`

- regime: `incoming_carry_before_local_overflow`
- role: same periodic core as `249`, but with decimal preperiod
- lesson: visibility observables are not determined by the stripped periodic core alone

## Same-Core Family Laws: `249`, `498`, and `996`

The family with periodic core `249` now has explicit comparison objects via
`same_core_visibility_comparison(...)`.

In the shared block coordinate `B = 1000`, `k = 4`:

- `249` versus `996 = 4 * 249` gives `q_core / q_actual = 4 = k^1`,
- `249` versus `498 = 2 * 249` gives `q_core / q_actual = 2`, which lies strictly between `k^0` and `k^1`.

Exact `k`-power law:

For `996 / 249`, the identity

`q_core * k^j = q_actual * k^(j+1)`

shifts the core stream left by one block. The repo checks that this exact
`k`-power shift also moves:

- the first incoming-carry position,
- the first local-overflow position,
- the raw-prefix agreement boundary.

For `996 / 249`, those boundaries shift by exactly one block.

Broader interval law:

If the same-core ratio satisfies `k^s <= q_core / q_actual < k^(s+1)`, then the
incoming-carry and local-overflow thresholds shift earlier by either `s` or
`s+1` blocks, with the exact `s`-block shift in the power case above.

As recorded under claim `same_core_threshold_shift_interval` in
[docs/PROOF_STATUS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/PROOF_STATUS_ATLAS.md),
the Lean same-core layer now also packages a reusable endpoint criterion for
the non-power interval case: once the actual and stripped-core boundary indices
`a` and `c` are fixed, the lower versus upper label is decided by whether the
stripping factor times the actual raw coefficient at index `a - s` stays below
or already reaches the relevant threshold (`B - k` for incoming carry, `B` for
local overflow).

The comparison `498 / 249` is the default non-power example:

- `q_core / q_actual = 2`,
- `k = 4`, so `k^0 <= 2 < k^1`,
- the observed incoming-carry, local-overflow, and raw-prefix shifts are all `1`.

The certified lookahead still varies more subtly across the family, so it
remains tracked as a stronger family-level observable rather than a closed-form
same-core theorem.

Lean now also packages one exact same-core transport theorem directly beneath
that open boundary: in the `q_core / q_actual = k^s` regime, once the same-core
incoming-carry and local-overflow boundaries are chosen with the core boundary
not later than the actual one, the first visible mismatch position shifts by
exactly `s` blocks as well. This is a transport law for the already-identified
boundary layer, not a closed-form theorem for minimal stabilization lookahead.

Lean now also packages two same-core lookahead-support laws beneath that same
open claim in the exact `q_core / q_actual = k^s` regime:

- the raw tail-mass inequality `q*k^(n+L) < B^L * (B-k)` transports exactly
  between the stripped core at `(n, L)` and the actual denominator at
  `(n + s, L)`, and
- the coarse sufficient condition `k^(n+L) < modulus` transports exactly under
  that same requested-block shift as well, so the stripped core can certify a
  shifted actual window without claiming any least-lookahead theorem.

Lean now also packages the exact fixed-window certificate at that same level:

- in the exact `q_core / q_actual = k^s` regime, the shifted actual prefix
  equality
  `emittedPrefixValue_actual(n + s) = truncatedVisiblePrefixValue_actual(n + s, L)`
  is equivalent to the stripped-core prefix equality
  `emittedPrefixValue_core(n) = truncatedVisiblePrefixValue_core(n, L)`, so
  the exact lookahead certificate itself transports between the stripped core
  at `(n, L)` and the actual denominator at `(n + s, L)`.

This is still a fixed-window theorem. It does not identify the least
stabilizing lookahead for equal requested windows across a same-core family,
and it does not close claim `small_k_visibility_threshold`.

## Cross-Base Fortification

The same-core laws are not just decimal artifacts.

Base `7` exact law:

- `1/56` versus `1/8`, using `B = 7^3 = 343`, `k = 7`
- `q_actual = 6`, `q_core = 42`, so `q_core / q_actual = 7 = k^1`
- the incoming-carry, local-overflow, and raw-prefix thresholds all shift by exactly one block

Base `12` interval and exact laws:

- `1/10` versus `1/5`, using `B = 12^2 = 144`, `k = 4`
- `q_actual = 14`, `q_core = 28`, so `q_core / q_actual = 2` with `4^0 <= 2 < 4^1`
- this realizes the lower endpoint of the interval law: the threshold shift is `0`

- `1/70` versus `1/35`, again with `B = 144`, `k = 4`
- `q_actual = 2`, `q_core = 4`, so `q_core / q_actual = 2` with `4^0 <= 2 < 4^1`
- this realizes the upper endpoint of the same interval law: the threshold shift is `1`

- `1/20` versus `1/5`, still with `B = 144`, `k = 4`
- `q_actual = 7`, `q_core = 28`, so `q_core / q_actual = 4 = k^1`
- this recovers the exact one-block shift law in a non-decimal base

So base `12` now exhibits all three local family behaviors in one shared coordinate:

- lower interval endpoint: `10 / 5`
- upper interval endpoint: `70 / 35`
- exact `k`-power shift law: `20 / 5`

These examples are exported by `search-reptends same-core-visibility --base 7` and
`search-reptends same-core-visibility --base 12`, which now choose same-core
coordinates for family signal rather than generic small-residue auto-modes.
The exported rows also record whether a non-power interval example realizes the
lower endpoint, upper endpoint, or exact point of the threshold-shift law.

## Family-Level Research Targets

The repo now tracks three family studies rather than one vague threshold question:

1. `q = 1` family: `97`, `996`
   Goal: isolate what bridge-style coordinates do and do not force.
2. `q > 1` family: `21`, `37`, `249`
   Goal: separate large positive `q` from actual carry failure.
3. shared periodic core family: `249`, `996`
   Goal: distinguish periodic-core invariants from actual-denominator visibility behavior.

## Track 16 Split: Theorem, Heuristic, Counterexample

Exact theorem candidates:

- cleaner closed forms or asymptotic bounds for the exact finite-window lookahead certificate,
- same-periodic-core criteria describing which visibility observables survive stripping base factors,
- stronger closed forms for raw-prefix agreement length across larger example families.

Empirical heuristics:

- small `k`, and especially `q = 1`, often increases the visible raw prefix,
- `k = 1` often collapses the carry layer entirely on the visible window.

Counterexample targets:

- examples where incoming carry arrives before the local overflow boundary,
- same-periodic-core pairs with different visible-prefix behavior,
- positive-`q` cases that remain fully visible versus positive-`q` cases that fail early.

This is the intended current boundary for Track 16: the incoming-carry boundary, the raw-prefix boundary, and a finite-window lookahead certificate are implemented, while cleaner closed forms and the broader global visibility theory remain open.
