# Agda Proof-Surface Audit and Correspondence

This document is the authoritative Track 14 map for the Agda surface.

Agda is a pedagogical/formal companion surface for this repository. It contains
real local proofs of the base-invariant and remainder-orbit scaffolding, but it
still uses explicit postulates for the heavier number-theoretic and
order/period layer. Lean is the theorem-complete formal backend for the current
atlas-level exact claims.

Future public prose must not imply Agda has full proof parity with Lean. When a
claim depends on an Agda postulate, point here and then point to the Lean theorem
or atlas claim that closes it, if one exists.

## Classification Legend

- `locally provable in Agda`: a shallow or structural lemma that should be
  dischargeable inside the current Agda development without importing the full
  finite-group or Mathlib-style number-theory stack.
- `intentionally postulated but Lean-backed`: a result that is left postulated
  in Agda on purpose, but already has a Lean theorem or a Lean-backed repo claim.
- `open or out of scope`: not an Agda-local priority for now. This includes the
  abstract prime predicate, example witnesses, and subgroup/cardinality facts
  that the repo is not currently trying to re-prove inside Agda.

Current audit totals:

- `0` locally provable in Agda
- `16` intentionally postulated but Lean-backed
- `6` open or out of scope

## Notes Before the Table

- Agda already proves `remainders-are-powers` and `stride-orbit` in
  [agda/QRTour/RemainderOrbit.agda](/Users/mikepurvis/other/quadratic-residue-reptends/agda/QRTour/RemainderOrbit.agda). The remaining postulate there is only the subgroup-exhaustion step `qr-orbit-exhaustive`.
- The base-invariant orbit/buffer layer in
  [agda/GeometricStack/OrbitBufferDuality.agda](/Users/mikepurvis/other/quadratic-residue-reptends/agda/GeometricStack/OrbitBufferDuality.agda)
  now proves its shallow structural layer locally under explicit meaningful
  assumptions `b > 0` and `M > 1`. The remaining postulates in that module are
  only the abstract order/period layer.
- Track 15 has already discharged four shallow QR-layer helpers locally:
  `powMod-mult` in [agda/QRTour/PrimeField.agda](/Users/mikepurvis/other/quadratic-residue-reptends/agda/QRTour/PrimeField.agda),
  `neg1-squared-helper` in [agda/QRTour/PrimeField.agda](/Users/mikepurvis/other/quadratic-residue-reptends/agda/QRTour/PrimeField.agda),
  plus `≡ₚ-to-≡-reduced` and `powMod-<p` in
  [agda/QRTour/Cosets.agda](/Users/mikepurvis/other/quadratic-residue-reptends/agda/QRTour/Cosets.agda).
- Track 15 also discharged the shallow orbit/buffer lemmas `repunitRem-closed`,
  `orbit-buffer-duality`, `shift-conjugacy`, and `noMod-step` in
  [agda/GeometricStack/OrbitBufferDuality.agda](/Users/mikepurvis/other/quadratic-residue-reptends/agda/GeometricStack/OrbitBufferDuality.agda).
- Some Agda items correspond to Lean theorems but do not map cleanly to a single
  public claim ID. In those rows the claim column is left as `-`.

## Postulate Inventory and Correspondence

| Module | Agda postulate | Classification | Lean correspondence | Claim ID | Notes |
|--------|----------------|----------------|---------------------|----------|-------|
| `Examples/Prime97.agda` | `prime-97` | `open or out of scope` | `Nat.Prime 97` is decidable in Lean examples, but there is no repo theorem named for this witness | `-` | Example witness only; not part of the theorem atlas. |
| `Examples/Prime97.agda` | `k97-is-qr-generator` | `intentionally postulated but Lean-backed` | `QRTour.Examples.k_is_qr_generator` | `-` | Concrete example witness for the canonical `97` walkthrough. |
| `GeometricStack/OrbitBufferDuality.agda` | `ord` | `intentionally postulated but Lean-backed` | `GeometricStack.OrbitBufferDuality.period` | `-` | Agda abstracts the period; Lean defines it via `orderOf` on units. |
| `GeometricStack/OrbitBufferDuality.agda` | `ord-spec` | `intentionally postulated but Lean-backed` | `GeometricStack.OrbitBufferDuality.pow_period_eq_one` plus positivity of `orderOf` | `-` | Period existence/specification is Lean-backed. |
| `GeometricStack/OrbitBufferDuality.agda` | `ord-period` | `intentionally postulated but Lean-backed` | `GeometricStack.OrbitBufferDuality.pow_period_eq_one` | `-` | Closure of the multiplicative orbit. |
| `GeometricStack/OrbitBufferDuality.agda` | `orbitRem-periodic` | `intentionally postulated but Lean-backed` | `GeometricStack.OrbitBufferDuality.orbitRem_periodic` | `-` | Exact periodicity theorem is already proved in Lean. |
| `GeometricStack/OrbitBufferDuality.agda` | `digitAt-periodic` | `intentionally postulated but Lean-backed` | `GeometricStack.OrbitBufferDuality.digitAt_periodic` | `digit_periodicity` | Exact digit periodicity theorem is already proved in Lean. |
| `QRTour/PrimeField.agda` | `IsPrime` | `open or out of scope` | Lean uses `Nat.Prime` / `Fact (Nat.Prime p)` rather than an abstract predicate | `-` | Agda keeps primality abstract in this layer. |
| `QRTour/PrimeField.agda` | `order-spec` | `intentionally postulated but Lean-backed` | Mathlib `orderOf` machinery used throughout `lean/QRTour` | `qr_stride_classification` | Agda search/minimality is abstract; Lean uses canonical unit orders. |
| `QRTour/PrimeField.agda` | `order-divides-p-1` | `intentionally postulated but Lean-backed` | Lean order arguments inside `QRTour.QuadraticResidues` and `QRTour.CompositePeriod` | `qr_stride_classification` | Supporting divisibility fact for prime-order reductions. |
| `QRTour/PrimeField.agda` | `fermat` | `intentionally postulated but Lean-backed` | Standard Mathlib Fermat/Euler support used by the Lean QR development | `qr_stride_classification` | Classical finite-field fact intentionally not rebuilt in Agda yet. |
| `QRTour/PrimeField.agda` | `inverse` | `intentionally postulated but Lean-backed` | Lean works in units and uses inversion directly in `ZMod p` | `-` | Agda keeps the inverse function abstract; Lean uses the ambient group structure. |
| `QRTour/PrimeField.agda` | `inverse-spec` | `intentionally postulated but Lean-backed` | Lean unit inversion / `ZMod.unitOfCoprime` | `-` | Bezout-style existence is not re-proved in Agda yet. |
| `QRTour/PrimeField.agda` | `inverse-nonzero` | `intentionally postulated but Lean-backed` | Lean unit inversion preserves nonzeroness by construction | `-` | Auxiliary support for the Agda coset lemmas. |
| `QRTour/Cosets.agda` | `euler-qr` | `intentionally postulated but Lean-backed` | `QRTour.isSquare_units_iff_pow_half_eq_one` | `qr_stride_classification` | Forward Euler criterion for quadratic residues. |
| `QRTour/Cosets.agda` | `euler-nqr` | `intentionally postulated but Lean-backed` | Derived in Lean from Euler criterion plus non-square/complement reasoning in `(ZMod p)ˣ` | `qr_stride_classification` | No single repo theorem name, but the Lean QR layer covers the mathematics. |
| `QRTour/Cosets.agda` | `euler-qr-inverse` | `intentionally postulated but Lean-backed` | `QRTour.isSquare_units_iff_pow_half_eq_one` | `qr_stride_classification` | Reverse Euler criterion direction. |
| `QRTour/Cosets.agda` | `ab-pos` | `open or out of scope` | No direct repo theorem | `-` | Local positivity witness inside `nqr-mult-nqr`; likely replaceable by a cleaner formulation later. |
| `QRTour/Cosets.agda` | `qr-count` | `open or out of scope` | No direct repo theorem | `-` | Standard subgroup-cardinality fact, but not currently surfaced as a Lean repo theorem. |
| `QRTour/Cosets.agda` | `nqr-count` | `open or out of scope` | No direct repo theorem | `-` | Same status as `qr-count`. |
| `QRTour/Cosets.agda` | `nqr-as-translate` | `open or out of scope` | No direct repo theorem | `-` | True group-theoretically, but not currently a theorem-level repo dependency. |
| `QRTour/RemainderOrbit.agda` | `qr-orbit-exhaustive` | `intentionally postulated but Lean-backed` | `QRTour.qr_tour_cover` together with `QRTour.pow_isQRGenerator_iff` and related QR-generator lemmas | `qr_stride_classification` | This is the remaining heavy subgroup-exhaustion step after the locally proved stride lemma. |

## Operational Guidance

- Treat Agda as honest if and only if every use of a postulated fact is labeled
  by this document’s classification.
- If a public theorem-level statement relies on an Agda postulate, cite the Lean
  theorem or the claim atlas, not the Agda module alone.
- Track 15 has emptied the `locally provable in Agda` class for the current
  audited surface without pretending to solve the whole parity problem.
