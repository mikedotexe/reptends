# Release Snapshot

This generated snapshot packages the current proof-status counts, open-claim boundary, Lean public-surface audit, Lean hygiene status, next-frontier lanes, published dataset version, and generated-note status.

## Proof-System Legend

- `Lean-formalized`: proved in the Lean tree and suitable for theorem-level citation in the current public surface.
- `Agda-locally-proved`: discharged inside the Agda pedagogical companion surface without relying on Agda postulates.
- `Agda-postulated but Lean-backed`: still explicit as an Agda postulate, but closed by Lean or an atlas-backed Lean-backed claim in this repo.
- `empirical`: implemented and regression-tested here, but not promoted to theorem status.
- `open`: tracked as an unresolved claim boundary or interface question, not an established result.

## Current Proof Status

Use [PROOF_STATUS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/PROOF_STATUS_ATLAS.md) as the theorem-level status source of truth.
Current registry counts:

- total claims: 15
- classical: 3
- reproved-here: 8
- implemented-here: 1
- empirical: 1
- open: 2

Current open claim IDs:
- `small_k_visibility_threshold` - Exact visibility threshold for carried prefixes
- `carry_dfa_factorization` - Canonical factorization of long division into orbit and carry

## Lean Public Surface

Use [THEOREM_GUIDE.md](/Users/mikepurvis/other/quadratic-residue-reptends/lean/THEOREM_GUIDE.md) and [lean_module_index.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/lean_module_index.json) for the full module audit.
- total indexed Lean modules: `27`
- umbrella surfaces: `QRTour, GeometricStack`
- public theorem surfaces: `8`
- public theorem module ids: `QRTour.QuadraticResidues, QRTour.OrbitWeave, QRTour.Digits, QRTour.SignedBridge, QRTour.PAdicBridge, QRTour.CompositePeriod, QRTour.Preperiod, QRTour.Visibility`
- public support surfaces: `10`
- public support module ids: `QRTour, QRTour.RemainderOrbit, QRTour.Bridge, QRTour.CosetStructure, QRTour.CarryTransducer, QRTour.CarryComparison, QRTour.Factorization, QRTour.CompositeVisibility, GeometricStack.Positional, GeometricStack.OrbitBufferDuality`
- public example surfaces: `1`
- public example module ids: `QRTour.Examples`
- infrastructure-only modules: `8`
- infrastructure module ids: `QRTour.Basic, QRTour.PrimitiveRoots, QRTour.BridgeQuality, GeometricStack, GeometricStack.Family, GeometricStack.Capacity, GeometricStack.Scale, GeometricStack.Valuation`
- claim-tagged modules: `17`
- claim-tagged module ids: `QRTour.RemainderOrbit, QRTour.Bridge, QRTour.CosetStructure, QRTour.QuadraticResidues, QRTour.OrbitWeave, QRTour.Digits, QRTour.SignedBridge, QRTour.PAdicBridge, QRTour.CompositePeriod, QRTour.Preperiod, QRTour.Visibility, QRTour.CarryTransducer, QRTour.CarryComparison, QRTour.Factorization, QRTour.CompositeVisibility, GeometricStack.Positional, GeometricStack.OrbitBufferDuality`
- claim-free modules: `10`
- claim-free module ids: `QRTour, QRTour.Basic, QRTour.PrimitiveRoots, QRTour.BridgeQuality, QRTour.Examples, GeometricStack, GeometricStack.Family, GeometricStack.Capacity, GeometricStack.Scale, GeometricStack.Valuation`

## Lean Hygiene

Use [ci_checks.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/ci_checks.py) for the current theorem-surface hygiene entrypoint.
- CI entrypoint: `ci-checks` via `python -m bridge_reptends.ci_checks`
- no-`sorry` status on `lean`: `clean`
- no-`#eval` status on focused public Lean targets: `clean`
- focused public Lean build targets: `20`
- focused public Lean build target ids: `QRTour.RemainderOrbit, QRTour.Bridge, QRTour.CosetStructure, QRTour.QuadraticResidues, QRTour.OrbitWeave, QRTour.Digits, QRTour.SignedBridge, QRTour.PAdicBridge, QRTour.CompositePeriod, QRTour.Preperiod, QRTour.Visibility, QRTour.CarryTransducer, QRTour.CarryComparison, QRTour.Factorization, QRTour.CompositeVisibility, QRTour.Examples, QRTour, GeometricStack.Positional, GeometricStack.OrbitBufferDuality, GeometricStack`

## Registry-Backed Docs

Use [sync_registry_docs.py](/Users/mikepurvis/other/quadratic-residue-reptends/bridge_reptends/sync_registry_docs.py) for the registry-backed theorem/doc sync entrypoint.
- sync entrypoint: `sync-registry-docs` via `python -m bridge_reptends.sync_registry_docs`
- check command: `python -m bridge_reptends.sync_registry_docs --check`
- managed theorem/doc surfaces: `11`
- sync status: `synchronized`
- drifted docs: `none`

## Lean Claim Surface

Use [lean_claim_carriers.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/lean_claim_carriers.json) and [lean_worked_examples.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/lean_worked_examples.json) for the atlas-backed claim-carrier and worked-example registries.
- atlas-backed claim carriers: `11`
- carrier claim IDs: `series_q_weighted_identity, positive_q_good_modes, digit_periodicity, signed_bridge_recurrence, bridge_block_value_periodicity, incoming_carry_position_formula, same_core_threshold_shift_interval, qr_stride_classification, crt_period_lcm, preperiod_from_base_factors, carry_window_transducer`
- worked example namespaces: `QRTour.Prime19, QRTour.Prime97, QRTour.Composite21, QRTour.Composite249, QRTour.Composite996`

## Next Lean Frontier

Use [THEOREM_GUIDE.md](/Users/mikepurvis/other/quadratic-residue-reptends/lean/THEOREM_GUIDE.md) and [lean_frontier_lanes.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/lean_frontier_lanes.json) for the current registry-backed release-facing frontier lanes.
- frontier lanes: `3`
- theorem frontier: strengthen same-core visibility and fixed-window carry/visibility arithmetic beyond the current quotient-scaling, scaled-raw-coefficient endpoint criteria, and exact certificate layer, while keeping `small_k_visibility_threshold` and `carry_dfa_factorization` explicitly `open`
- promotion audit: decide whether any of `PrimitiveRoots`, `BridgeQuality`, or the remaining bridge-specialized support modules deserve their own atlas claim IDs, and classify the rest explicitly as public support or infrastructure
- theorem-witness tooling: extend the now-generated [THEOREM_WITNESS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/THEOREM_WITNESS_ATLAS.md) into search outputs, site-facing data, and targeted research exports so the formal surface and the open-claim surface are easier to inspect and publish without hand-maintained drift

## Open-Claim Lean Boundary

Use [THEOREM_GUIDE.md](/Users/mikepurvis/other/quadratic-residue-reptends/lean/THEOREM_GUIDE.md) and [lean_open_claim_boundaries.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/lean_open_claim_boundaries.json) for the exact support order beneath the remaining open claims.
- `small_k_visibility_threshold` - `3` support modules / `20` named support theorems: `QRTour.Visibility (5), QRTour.CompositeVisibility (7), QRTour.CarryComparison (8)`.
- `carry_dfa_factorization` - `3` support modules / `17` named support theorems: `QRTour.CarryTransducer (3), QRTour.CarryComparison (10), QRTour.Factorization (4)`.

## Theorem-Witness Surface

Use [THEOREM_WITNESS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/THEOREM_WITNESS_ATLAS.md) as the claim-linked witness source of truth.
- total witness records: 20
- theorem-witness: 16
- empirical-witness: 1
- open-target: 3

## Published Dataset

- [example_atlas.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/example_atlas.json) - dataset `published_example_atlas` with schema `2.16` and status `synchronized`.
- Build command: `search-reptends published-atlas --max 1200 --top 8 --output data/example_atlas.json`
- Source files: `bridge_reptends/search.py, bridge_reptends/composite.py, bridge_reptends/transducer.py, bridge_reptends/visibility.py, data/claim_registry.json, data/lean_worked_examples.json, data/theorem_witnesses.json, data/throughlines.json, data/vocabulary.json`

## Generated Note

- [EXPOSITORY_NOTE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/EXPOSITORY_NOTE.md) - status `synchronized` against `bridge_reptends.build_expository_note:render_expository_note_lines`.
- Build command: `python -m bridge_reptends.build_expository_note`
