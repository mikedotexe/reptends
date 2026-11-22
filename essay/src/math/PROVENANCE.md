# Arithmetic provenance

`lifts.ts`, `unfolded-notation.ts`, and `triple-contributions.ts` are exact copies of the arithmetic modules developed for the September 2026 chat **! Update recurrence theorem**. Their original source is preserved at:

`/Users/mikepurvis/Documents/Codex/2026-09-02/found-it-three-threads-actually-the/demo/src/`

The corresponding original tests were copied into this site's `test/` directory with only their import paths changed. `site-contract.test.ts` additionally verifies the particular examples and complete periods presented by the website.

The engine uses exact integer arithmetic, checks its recurrence representation against ordinary long division, and keeps finite residuals. These are implementations and explanations of classical arithmetic identities. Display-width annotations are exploratory notation and do not change the mathematical radix. Continued fractions and the original CLI walkthrough are outside this site's arithmetic bundle.


`progression.ts` adapts the positive-digit continuation rule from research phase13's `bridges.mjs`, using this site's existing `advanceRun` accounting. The two presets retain the ordinary base-1000 prefix before the first carried group. Public proof scope is recorded under `retained_progression_handoffs` in the [proof-status atlas](../../../docs/PROOF_STATUS_ATLAS.md), with the unchanged phase13 Lean source imported as [HandoffSearch.lean](../../../lean/RadixRuns/HandoffSearch.lean). Browser code is independently tested, not formally verified.


`field.ts` implements the bounded base-1000 neighbourhood around 997 from the reviewed Remainder Machine field inequality `(1000 − n)² < n`. The public scope and elementary root-width derivation are recorded in [Field around 1000: worked example](../../../docs/PROOF_STATUS_ATLAS.md#field-around-1000-worked-example). Exact division and membership use bounded integers; square roots are drawing coordinates. Tests independently group a decimal long-division walk for all 66 displayed denominators. This UI is not Lean-verified, and the lesson does not introduce the general slide-rule regimes.


`power-dial.ts` implements the bounded family `1/(10^w−3)` for widths 2 through 6 and fixed `1/997` regrouped at widths 3 through 6. The positive quotient series and incoming carry use the existing registered identities; field membership uses `(10^w−n)²<n`. All integer intermediates remain below 10^12; square roots are display coordinates only. Independent decimal division tests check every displayed opening, first carry, and regrouped digit tape. See [Power dial and fixed grouping examples](../../../docs/PROOF_STATUS_ATLAS.md#power-dial-and-fixed-grouping-examples). No Lean source or registry claim changed.
