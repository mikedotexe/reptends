# Visibility Optics Workbench

Status: experimental finite-window workbench. This is a ranking and triage
surface, not a new theorem claim.

The workbench asks one practical question:

> Where does the source remainder orbit remain readable through the finite
> carry window, and where does the instrument conceal or compress it?

It keeps the repo's standard labels first: remainder orbit, raw coefficient
stream, carry-propagated block normalization, and finite-window trace.
`small_k_visibility_threshold` and `carry_dfa_factorization` remain `open`.

## Command

```bash
search-reptends visibility-optics --max 1200 --base 10 --blocks 8 --top 20
```

The command ranks finite evidence from existing observables:

- carried-prefix visibility profiles,
- canonical orbit/carry trace anchors,
- selected-coordinate state-map compression,
- same-core visibility and obstruction-phase behavior.

The score is heuristic. Treat it as a lantern for choosing the next examples
to inspect, not as proof that an example satisfies a global visibility theorem.

## Base-Instrument Comparison

Use base comparison when the question is whether a signal belongs to the
arithmetic source or to the chosen positional instrument:

```bash
search-reptends visibility-base-compare --max 1200 --bases 10,12,30 --blocks 8 --top 20
```

This treats bases `10`, `12`, and `30` as observation instruments. Base `30`
is useful because it absorbs more small-prime factors, but it is not promoted
as the default representation of the object. The comparison reports which
finite-window signal classes persist and which shift when the instrument
changes.

## Instrument Atlas

Use the **Instrument Atlas** when the question becomes broader than one
comparison: which bases reveal, absorb, distort, or obstruct the finite-window
trace?

```bash
search-reptends instrument-atlas --max 1200 --bases 7,10,12,30 --blocks 8 --top 20
```

The atlas adds base-level instrument profiles, case-level instrument
signatures, and `working_axiom_signal` rows. These rows are pressure on the
working vocabulary, not theorem claims. The field guide lives in
[INSTRUMENT_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/INSTRUMENT_ATLAS.md).

## Row Groups

- `workbench_summary`: selected bounds, counts, scoring fields, signal classes,
  and the open claim boundary.
- `canonical_anchor`: fixed reference cases `21`, `97`, `249`, and `996`.
- `ranked_case`: individual denominators ranked by finite-window signal.
- `same_core_signal`: family rows showing exact/interval same-core shifts,
  one-way visibility, or re-hiding.

## Signal Classes

- `transparent_window`: the raw coefficient stream is visible across the
  requested window.
- `early_carry_intrusion`: incoming carry changes a block before local raw
  overflow occurs.
- `visible_state_compression`: the state-map obstruction is visible as
  preimage compression.
- `hidden_graph_obstruction`: output agreement hides a state-graph obstruction.
- `same_core_drift`: actual denominators with the same stripped periodic core
  differ in finite-window visibility behavior.

## Reading A Row

Start with the coordinate fields:

```text
n, periodic_modulus, base, m, B, q, k, period, preperiod_digits
```

Then read the visibility fields:

```text
raw_prefix_agreement_length
first_incoming_carry_position
first_local_overflow_position
lookahead_lower_bound
certified_lookahead_blocks
mismatch_regime
```

Finally read the state-map fields when present:

```text
factorization_regime
obstruction_class
carry_state_count
remainder_state_count
forward_preimage_signature
reverse_ambiguity_signature
```

The workbench fields `visibility_signal_score`, `signal_class`,
`score_reasons`, and `why_interesting` explain why the row was selected.

## Canonical Anchors

- `21`: a transparent baseline. The carry state collapses and the raw
  coefficient stream stays visible on the requested window.
- `97`: the clean prime delayed-carry case. Incoming carry appears before local
  overflow, and the selected state map shows visible preimage compression.
- `249`: the positive-q delayed-carry periodic core.
- `996`: the same delayed-carry pattern in the composite/preperiod setting,
  with stripped periodic modulus `249`.

## Follow-Up Commands

Use the workbench to choose a row, then drill down:

```bash
search-reptends orbit-carry-trace --base 10 --blocks 8 --members 21,97,996
search-reptends visibility-profiles --max 500 --base 10 --blocks 8
search-reptends state-merging --max 500 --base 10 --blocks 8
search-reptends same-core-obstruction-phases --max 1200 --base 10 --blocks 8
```

The intended workflow is empirical but disciplined: find signal, inspect the
finite-window trace, compare families, and only then decide whether a sharper
theorem target is actually forming.
