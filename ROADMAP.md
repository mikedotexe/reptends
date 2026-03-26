# Lean 4 Fortification Roadmap

**Updated**: 2026-03-25

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
  - `digit_periodicity`
  - `signed_bridge_recurrence`
  - `bridge_block_value_periodicity`
  - `crt_period_lcm`
  - `preperiod_from_base_factors`
- the exact block-coordinate and carry-boundary claims are now Lean-backed:
  - `series_q_weighted_identity`
  - `positive_q_good_modes`
  - `incoming_carry_position_formula`
  - `same_core_threshold_shift_interval`
- the finite carry-normalization and fixed-window visibility layers are now
  Lean-backed, including exact fixed-window carry/remainder output agreement
- the strongest remaining Lean work is now family packaging, release-surface
  hardening, and any future step beyond finite-window comparison without
  overclaiming the open global problems
- the next Lean phase now splits naturally into three lanes:
  - theorem-frontier work beneath the two still-open carry/visibility claims
  - promotion or explicit de-promotion of the remaining support modules
  - theorem-witness and research-tooling surfaces that make the formal core
    easier to explore and publish honestly
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

Status: `implemented for finite-window normalization/comparison`

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

Current landing beyond the original target:
- [lean/QRTour/Visibility.lean](lean/QRTour/Visibility.lean) now formalizes the
  exact fixed-window gap certificate and proves it is equivalent to visible
  prefix agreement at fixed `(requestedBlocks, lookaheadBlocks)`
- [lean/QRTour/CarryComparison.lean](lean/QRTour/CarryComparison.lean) now
  splits the comparison layer out of the normalization core and proves exact
  finite carry/remainder output agreement under that certificate
- the repo now has an honest Lean boundary between:
  - finite normalization and traced comparison
  - exact fixed-window visible-word agreement
  - the still-open global `carry_dfa_factorization` claim

Why this matters:
- it formalizes the exact part of the carry story without overcommitting to the
  still-open global factorization claim
- it now gives the repo an exact finite-word agreement theorem using the same
  gap-style fixed-window certificate as the Python visibility layer
- it sets up a clean interface for later state-level comparison work without
  pretending that finite comparison already proves the global conjecture

Acceptance:
- the repository can cite a Lean theorem for finite-window carry normalization
- the atlas still keeps `carry_dfa_factorization` marked `open`

### Track L5: Composite-and-Visibility Integration

Status: `implemented for same-core family packaging`

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

Current landing:
- [lean/QRTour/CompositeVisibility.lean](lean/QRTour/CompositeVisibility.lean)
  now defines the stripped periodic modulus, packages actual/core block
  coordinates, exposes the stripping-factor arithmetic from
  [lean/QRTour/Preperiod.lean](lean/QRTour/Preperiod.lean), and proves
  actual-versus-stripped-core incoming-carry and local-overflow shift theorems
  as Lean family results
- the same module now also packages a reusable endpoint-sensitive criterion for
  the non-power interval cases: at fixed actual/core boundary data, the lower
  versus upper endpoint is decided by whether the stripping factor times the
  actual raw coefficient at the candidate shifted index stays below or reaches
  the relevant threshold
- the same-core family surface is now a Lean module boundary instead of only a
  Python reporting layer

Why this matters:
- it turns several strong composite examples into theorem families
- it strengthens the bridge from exact composite arithmetic to the visibility layer

Acceptance:
- the repo can state same-core comparison theorems in Lean, not only in datasets

### Track L6: Release-Facing Lean Surface

Status: `in progress`

Goal:
- make the Lean contribution legible to a mathematician in one pass

Tasks:
- expand the Lean theorem guide into a true module/claim index
- classify “present but unpromoted” Lean modules as public claim carriers,
  public support modules, or supporting infrastructure
- add stronger focused Lean acceptance checks beyond `lake build` plus no-`sorry`
- keep README and atlas wording synchronized with the actual Lean surface

Acceptance:
- a reader can find the main Lean theorem families without reading the Python first

### Track L7: Theorem Frontier Beyond Exact Fixed-Window Comparison

Status: `in progress`

Goal:
- push the current exact carry/visibility layer one step closer to the two open
  claims without pretending either open claim is solved

Tasks:
- split the remaining theorem work into two explicit subproblems:
  - stronger arithmetic control of fixed-window and minimal-lookahead behavior
    under `small_k_visibility_threshold`
  - stronger finite carry-state invariants and extracted comparison laws under
    `carry_dfa_factorization`
- add exact intermediate theorems such as:
  - transport lemmas for fixed-window lookahead certificates
  - same-core transfer results for visible-word stabilization hypotheses
  - finite state-extraction theorems from aligned carry/remainder traces that
    stop short of global DFA factorization
- require each tranche to end with atlas/theorem-guide wording that still keeps
  both global claims explicitly `open`

Tranches:
- L7.1: visibility-certificate transport and bound sharpening
- L7.2: same-core lookahead transfer and finite-window family theorems
- L7.3: finite carry-state invariant extraction without global morphism claims

Current landing:
- L7.1 is now underway in [lean/QRTour/Visibility.lean](lean/QRTour/Visibility.lean)
  and [lean/QRTour/CarryComparison.lean](lean/QRTour/CarryComparison.lean):
  Lean now packages the necessary tail-mass lower bound beneath the exact
  fixed-window certificate, monotonicity of the truncated visible-prefix
  integer in lookahead, and transport of certificate-driven visible-word
  agreement to larger finite windows
- L7.2 is now started in [lean/QRTour/CompositeVisibility.lean](lean/QRTour/CompositeVisibility.lean):
  Lean now packages exact same-core transport of the first visible mismatch
  boundary in the exact `k`-power regime, together with exact same-core
  transport of the raw tail-mass lower-bound inequality, the shifted coarse
  `k^(n+L) < modulus` sufficient condition, and the exact fixed-window
  lookahead certificate itself between the stripped core at `(n, L)` and the
  actual denominator at `(n + s, L)`
- [lean/QRTour/CarryComparison.lean](lean/QRTour/CarryComparison.lean) now
  consumes that exact same-core certificate transport to reprove shifted
  finite carry/remainder visible-word agreement on the actual denominator from
  a stripped-core certificate
- L7.3 now has its first exact finite state-invariant surface in
  [lean/QRTour/CarryComparison.lean](lean/QRTour/CarryComparison.lean):
  `stateAlignments` now project positions, coefficients, carry inputs/outputs,
  and remainder inputs/outputs; recover the observed finite
  remainder-to-carry and carry-to-remainder state-pair lists; and prove the
  exact local carry-balance and remainder-balance equations at each aligned
  position, together with shifted same-core aligned-output agreement and exact
  finite-window functional criteria for the observed remainder-to-carry and
  carry-to-remainder state-pair lists
- the same module now also proves exact finite transition-compatibility
  theorems: when an observed functional criterion holds, repeated source
  states with the same coefficient force matching finite transition data, and
  explicit conflict lemmas now refute the corresponding finite functional
  criterion whenever the observed pair list disagrees
- this strengthens the exact support beneath `small_k_visibility_threshold`
  and `carry_dfa_factorization` without claiming any least-lookahead or global
  factorization theorem

Acceptance:
- the repo gains exact intermediate theorems that sharpen both open frontiers
- neither `small_k_visibility_threshold` nor `carry_dfa_factorization` is
  restated as closed or nearly closed before the theorem boundary truly moves

### Track L8: Support-Module Promotion Audit

Status: `in progress`

Goal:
- decide which remaining Lean modules deserve atlas-backed claim status and
  which should remain public support or internal infrastructure

Tasks:
- audit:
  - [lean/QRTour/PrimitiveRoots.lean](lean/QRTour/PrimitiveRoots.lean)
  - [lean/QRTour/BridgeQuality.lean](lean/QRTour/BridgeQuality.lean)
  - [lean/QRTour/RemainderOrbit.lean](lean/QRTour/RemainderOrbit.lean)
  - [lean/QRTour/Bridge.lean](lean/QRTour/Bridge.lean)
  - [lean/QRTour/CosetStructure.lean](lean/QRTour/CosetStructure.lean)
  - [lean/GeometricStack.lean](lean/GeometricStack.lean)
- for each module, choose exactly one role:
  - atlas-backed claim carrier
  - public support surface
  - specialized infrastructure
- require any promotion to come with:
  - a claim ID
  - theorem-guide entry
  - atlas/registry sync
  - focused CI coverage
  - one canonical witness or example when appropriate

Tranches:
- L8.1: audit and classify every remaining support module
- L8.2: promote at most one clearly claim-worthy module family
- L8.3: harden CI and public docs around the resulting classification

Current landing:
- L8.1 is now implemented as a machine-readable audit in
  [data/lean_module_index.json](data/lean_module_index.json) and a generated
  module table in [lean/THEOREM_GUIDE.md](lean/THEOREM_GUIDE.md)
- the current pass explicitly classifies `PrimitiveRoots`, `BridgeQuality`,
  `RemainderOrbit`, `Bridge`, `CosetStructure`, `Examples`, and the
  `GeometricStack` surface rather than leaving them in a half-public state
- this tranche does not force any new claim IDs beyond the already-promoted
  `Digits`, `SignedBridge`, and `PAdicBridge` surfaces

Acceptance:
- no mathematically interesting Lean module remains in a half-public state
- the theorem guide and atlas tell the same story about module roles

### Track L9: Theorem-Witness and Research-Tooling Surface

Status: `in progress`

Goal:
- make the formal core and the open frontiers explorable through canonical
  witnesses, generated outputs, and claim-linked research tools

Tasks:
- add a theorem-witness layer keyed by claim ID, with canonical tuples such as:
  - `(base, N, stride, B, q, k)` for block-coordinate claims
  - same-core family pairs and chosen shared coordinates
  - canonical carry/transducer windows for finite comparison results
- expose those witnesses in generated docs, search outputs, or site-facing data
- add bounded research-tooling outputs targeted specifically at:
  - `small_k_visibility_threshold`
  - `carry_dfa_factorization`
  rather than only generic sweeps
- keep theorem witnesses and research witnesses separate from theorem promotion:
  witness-rich does not mean theorem-level

Tranches:
- L9.1: claim-linked theorem-witness atlas
- L9.2: search/export support for canonical witnesses
- L9.3: research tooling for targeted open-claim sweeps and release snapshots

Current landing:
- L9.1 is now implemented as
  [data/theorem_witnesses.json](data/theorem_witnesses.json) together with the
  generated [docs/THEOREM_WITNESS_ATLAS.md](docs/THEOREM_WITNESS_ATLAS.md)
- each current claim ID now has a named canonical witness, empirical witness,
  or open target family with evidence paths checked in CI
- the generated note, theorem guide, and registry-backed doc sync surface now
  point back to those witnesses so public examples are less narrative-driven
- the published atlas in [data/example_atlas.json](data/example_atlas.json) now
  carries claim-linked witness rows, and the site-facing atlas library exports
  those witness rows directly
- visibility and carry search/report rows now expose related claim IDs, open
  claim IDs, and matching witness IDs, and the published atlas case studies now
  thread that claim context directly into individual examples

Acceptance:
- each atlas-backed claim has a canonical witness path in the repo
- each open claim has named target families and bounded research outputs
- the repo can publish claim-linked examples without hand-maintained narrative drift

## What Not To Prioritize Yet

- do not spend the next tranche on more concrete `97`-style examples unless
  they reveal a reusable theorem family
- do not try to prove the global `carry_dfa_factorization` conjecture before
  the finite deterministic carry layer is formalized
- do not duplicate Mathlib finite-group background that the current QR modules
  already use successfully
- do not treat empirical visibility heuristics as theorem targets before the
  exact incoming-carry and threshold laws are fully formalized

## Practical Next Tranches

If starting the next Lean-centered phase immediately, do this:

1. keep the current Lean surface green with `/opt/homebrew/bin/python3.14 -m bridge_reptends.ci_checks` and `lake build`
2. continue Track L7.2 with same-core visibility transport or honest arithmetic bound-sharpening beneath `small_k_visibility_threshold`
3. use Track L8.2 only if one remaining support module truly earns an atlas claim ID without inflating the surface
4. push Track L9.2 so canonical witnesses flow into search outputs, exports, and site-facing data

That is the shortest route to a materially stronger next-phase Lean story for this repo.
