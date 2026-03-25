# Lean 4 Fortification Roadmap

**Updated**: 2026-03-24

This file is the root-level Lean-first companion to [docs/ROADMAP.md](docs/ROADMAP.md).
Use it when the question is specifically:

How should this repository most profitably strengthen its mathematical core in Lean 4?

The broader execution history, registry work, site work, and Agda companion
tracks remain in [docs/ROADMAP.md](docs/ROADMAP.md). This root roadmap is the
shortest current guide to the next Lean-centered theorem passes.

## Survey Summary

Current local survey findings:

- the Lean package in [lean/](lean/) builds with `lake build`
- the existing Lean surface is already substantial in both theorem families:
  - [lean/QRTour](lean/QRTour) covers the prime QR tour, bridge structure,
    composite CRT period structure, and preperiod valuations
  - [lean/GeometricStack](lean/GeometricStack) covers the base-invariant
    geometric-stack and orbit/buffer scaffolding
- the proof atlas already treats the main exact prime/composite claims as
  formalized or Lean-backed, especially:
  - `qr_stride_classification`
  - `crt_period_lcm`
  - `preperiod_from_base_factors`
- the exact block-coordinate and carry-boundary claims are now Lean-backed:
  - `series_q_weighted_identity`
  - `positive_q_good_modes`
  - `incoming_carry_position_formula`
  - `same_core_threshold_shift_interval`
- the strongest remaining exact arithmetic work is now the finite
  carry-normalization layer rather than the raw series/visibility formulas
- the two main open claims remain:
  - `small_k_visibility_threshold`
  - `carry_dfa_factorization`

That means the best Lean work now is not more QR-stride cleanup. It is the
exact carry/series/visibility layer that sits between the current formal core
and the current open problems.

## Working Principles

- Build on Mathlib’s existing `ZMod`, unit-group, order, CRT, and valuation
  machinery instead of re-proving finite-field background locally.
- Keep the theorem boundary exact:
  prove finite identities, divisibility facts, and finite-window carry laws
  before touching global transducer conjectures.
- Keep prime-only structure separate from general block-coordinate arithmetic.
- When a theorem strengthens a claim already tracked in
  [docs/PROOF_STATUS_ATLAS.md](docs/PROOF_STATUS_ATLAS.md), update the claim
  status instead of adding parallel prose.
- Prefer modules that bridge existing exact code paths in
  [bridge_reptends/orbit_weave.py](bridge_reptends/orbit_weave.py),
  [bridge_reptends/visibility.py](bridge_reptends/visibility.py), and
  [bridge_reptends/transducer.py](bridge_reptends/transducer.py) into Lean.

## Recommended Execution Order

### Track L1: Theorem-Hygiene Pass

Status: `implemented`

Goal:
- make the current Lean surface read as a stable library rather than a growing
  notebook

Tasks:
- clean stale commentary in [lean/QRTour/Examples.lean](lean/QRTour/Examples.lean)
  that still mentions a placeholder `sorry` even though the theorem is proved
- add a lightweight guard in CI or local checks that `rg -n "\\bsorry\\b" lean`
  returns no matches
- add one short Lean-facing theorem index or claim map if the atlas alone feels
  too indirect for mathematician readers

Acceptance:
- no stale comments imply missing proofs where Lean already has the theorem
- the repo has a standard “Lean is clean” check in addition to `lake build`

### Track L2: Q-Weighted Series and Orbit-Weave Formalization

Status: `implemented`

Suggested Lean surface:
- [lean/QRTour/OrbitWeave.lean](lean/QRTour/OrbitWeave.lean)

Target claims:
- `series_q_weighted_identity`
- `positive_q_good_modes`

What to prove:
- for `B = qN + k` with `0 <= k < N`, formalize the exact rational identity
  behind the `q*k^j` coefficient stream
- add finite partial-sum versions, not only the infinite geometric-series form
- formalize the exact decomposition used in Python:
  `R = W + F` with the current standard-language naming
- make positivity conditions explicit so “good mode” language becomes a theorem
  with hypotheses, not an intuition

Why this is the best next move:
- it fortifies the algebra that the README places at the center of the project
- it creates the exact bridge from the QR/period layer to the carry layer
- it upgrades a prominent `classical` atlas claim into a Lean-backed theorem

Acceptance:
- the atlas statement for `series_q_weighted_identity` can cite Lean
- the positivity condition for usable block coordinates is stated and proved in Lean

### Track L3: Exact Visibility Formulas

Status: `implemented for target claims`

Suggested Lean surface:
- [lean/QRTour/Visibility.lean](lean/QRTour/Visibility.lean)

Target claims:
- `incoming_carry_position_formula`
- `same_core_threshold_shift_interval`

What to prove:
- the exact incoming-carry formula
  `carry_in(j) = floor(q * k^(j+1) / (B - k))`
- the first-incoming-carry boundary as the least `j` with
  `q * k^(j+1) >= B - k`
- the same-core threshold-shift interval theorem now implemented in Python
- any exact lower-bound or certificate lemmas already used by
  [bridge_reptends/visibility.py](bridge_reptends/visibility.py)

Why this matters:
- it pushes the repo right up to the boundary of the current open visibility claim
- it converts the best exact carry-facing formulas from code into formal theorems
- it creates a disciplined Lean landing zone for future visibility research

Acceptance:
- the atlas can treat the incoming-carry formula as Lean-backed rather than only classical
- the same-core threshold interval is stated in Lean with explicit hypotheses

### Track L4: Finite Carry-Transducer Normalization

Status: `in progress`

Suggested Lean surface:
- [lean/QRTour/CarryTransducer.lean](lean/QRTour/CarryTransducer.lean)

Target claim family:
- finite deterministic normalization behind `carry_window_transducer`

What to prove:
- define a finite coefficient word and its carry-normalization recursion
- prove determinism of the normalization map
- prove agreement between:
  - the raw coefficient word plus carry normalization
  - the displayed finite block word
- prove finite-window lemmas only; do not promote the global DFA factorization
  conjecture here

Current landing:
- [lean/QRTour/CarryTransducer.lean](lean/QRTour/CarryTransducer.lean) now defines the
  finite carry transducer, the right-to-left normalization recursion, a
  determinism lemma for the normalization map, traced finite runs with explicit
  `coefficient/carryIn/blockValue/carryOut` step data, value-preservation
  for finite coefficient words, and an exact evaluation bridge from the
  carry-normalized raw word to the `OrbitWeave` body term `W_L`
- the module also exposes the bridge from `BlockCoordinate.rawCoefficient` words
  to both traced runs and finite carry-normalized words, so the carry layer now
  sits directly on top of the `OrbitWeave` algebra
- the current Lean surface now proves the canonical base-`B` digit theorem for
  the carry-normalized body-term word and, separately, the canonical digit
  theorem for the emitted long-division prefix integer `B^L / N`
- it also records the exact correction identity
  `B^L / N = W_L + k^L / N`, so the comparison between the carry-normalized word
  and the emitted long-division word is honest about the residual tail term
- under the explicit finite-window hypothesis `k^L < N`, Lean now proves exact
  word agreement between the normalized raw word and the emitted long-division
  block word
- the module also now exposes a finite carry/remainder comparison surface via
  paired traces and projection lemmas for coefficients, carry states,
  remainder states, and both output words

Next logical items:
- sharpen the exact finite-window agreement hypothesis from the literal
  `k^L < N` tail-vanishing condition to visibility-style or lookahead-style
  certificates that match the current Python analysis surface more closely
- promote the paired carry/remainder trace surface from projection lemmas to
  explicit finite-window state-comparison theorems
- distinguish carefully between:
  - exact finite-word output agreement
  - observed state-quotient or relabeling candidates
  - the still-open global `carry_dfa_factorization` claim
- only after that, decide whether the state-comparison layer should stay inside
  [lean/QRTour/CarryTransducer.lean](lean/QRTour/CarryTransducer.lean) or split
  into a dedicated comparison module

Why this matters:
- it formalizes the exact part of the carry story without overcommitting to the
  still-open global factorization claim
- it gives the repo an exact finite-word agreement theorem whenever the
  correction tail vanishes inside the visible window
- it sets up a clean later interface for comparing carry states to remainder states

Acceptance:
- the repository can cite a Lean theorem for finite-window carry normalization
- the atlas still keeps `carry_dfa_factorization` marked `open`

### Track L5: Composite-and-Visibility Integration

Status: `after L2-L4`

Suggested Lean surface:
- [lean/QRTour/CompositeVisibility.lean](lean/QRTour/CompositeVisibility.lean)

What to connect:
- [lean/QRTour/CompositePeriod.lean](lean/QRTour/CompositePeriod.lean)
- [lean/QRTour/Preperiod.lean](lean/QRTour/Preperiod.lean)
- the new orbit-weave and visibility modules

What to prove:
- formal statements that compare an actual denominator to its stripped periodic
  core using the existing valuation/preperiod machinery
- family-level lemmas for same-core examples, rather than example-by-example
  computations in Python

Why this matters:
- it turns several strong composite examples into theorem families
- it strengthens the bridge from exact composite arithmetic to the visibility layer

Acceptance:
- the repo can state same-core comparison theorems in Lean, not only in datasets

### Track L6: Release-Facing Lean Surface

Status: `after theorem growth`

Goal:
- make the Lean contribution legible to a mathematician in one pass

Tasks:
- add a short root-level theorem guide or extend the atlas with a Lean module index
- link each promoted exact claim to its Lean module and theorem name
- keep README and atlas wording synchronized with the actual Lean surface

Acceptance:
- a reader can find the main Lean theorem families without reading the Python first

## What Not To Prioritize Yet

- do not spend the next tranche on more concrete `97`-style examples unless
  they reveal a reusable theorem family
- do not try to prove the global `carry_dfa_factorization` conjecture before
  the finite deterministic carry layer is formalized
- do not duplicate Mathlib finite-group background that the current QR modules
  already use successfully
- do not treat empirical visibility heuristics as theorem targets before the
  exact incoming-carry and threshold laws are fully formalized

## Practical First Tranche

If starting the next Lean pass immediately, do this:

1. keep Track L1 green with `python -m bridge_reptends.ci_checks` and `lake build`
2. extend [lean/QRTour/OrbitWeave.lean](lean/QRTour/OrbitWeave.lean) from block-coordinate arithmetic into the weighted-series theorems
3. prove the exact `B = qN + k` weighted-series identity plus a finite partial-sum form
4. update [docs/PROOF_STATUS_ATLAS.md](docs/PROOF_STATUS_ATLAS.md) if that claim moves from `classical` to `reproved-here`

That is the shortest route to a materially stronger Lean story for this repo.
