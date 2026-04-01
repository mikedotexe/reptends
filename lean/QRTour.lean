/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.Basic
import QRTour.QuadraticResidues
import QRTour.RemainderOrbit
import QRTour.PrimitiveRoots
import QRTour.Digits
import QRTour.Bridge
import QRTour.BridgeQuality
import QRTour.SignedBridge
import QRTour.PAdicBridge
import QRTour.CosetStructure
import QRTour.CompositePeriod
import QRTour.Preperiod
import QRTour.OrbitWeave
import QRTour.Visibility
import QRTour.CarryTransducer
import QRTour.CarryComparison
import QRTour.CompositeVisibility
import QRTour.Examples

/-!
# Quadratic Residue Tour

This umbrella module re-exports the current Lean 4 formal surface for the
repository. The public theorem-level status lives in
`docs/PROOF_STATUS_ATLAS.md`, and the Lean-facing carrier/index view lives in
`lean/THEOREM_GUIDE.md`.

The library is no longer only a prime QR tour. It now packages:

- prime remainder-orbit, digit, and quadratic-residue structure
- bridge and signed-bridge recurrence layers
- bridge block-value periodicity
- composite CRT period and preperiod arithmetic
- q-weighted block-coordinate algebra
- exact finite-window visibility and carry-normalization interfaces
- same-core composite visibility transport

## Proof-System Framing

Use the same public proof-system legend here as in the theorem guide:

- `Lean-formalized`: proved in the Lean tree and suitable for theorem-level
  citation in the current public surface
- `Agda-locally-proved`: discharged inside the Agda pedagogical companion
  surface without relying on Agda postulates
- `Agda-postulated but Lean-backed`: still explicit as an Agda postulate, but
  closed by Lean or an atlas-backed Lean-backed claim in this repo
- `empirical`: implemented and regression-tested here, but not promoted to
  theorem status
- `open`: tracked as an unresolved claim boundary or interface question, not an
  established result

Lean is the theorem-complete formal backend for the current atlas-backed exact
claims. Agda remains a pedagogical companion surface rather than a theorem-parity
target.

## Current Theorem Surface

The main atlas-backed Lean carriers are:

- `QRTour.QuadraticResidues` for `qr_stride_classification`
- `QRTour.Digits` for `digit_periodicity`
- `QRTour.SignedBridge` for `signed_bridge_recurrence`
- `QRTour.PAdicBridge` for `bridge_block_value_periodicity`
- `QRTour.CompositePeriod` for the Lean-backed CRT period surface
- `QRTour.Preperiod` for the Lean-backed base-factor preperiod surface
- `QRTour.OrbitWeave` for `series_q_weighted_identity` and
  `positive_q_good_modes`
- `QRTour.Visibility` for `incoming_carry_position_formula`
- `QRTour.Visibility` together with `QRTour.CompositeVisibility` for
  `same_core_threshold_shift_interval`

Support modules such as `QRTour.RemainderOrbit`, `QRTour.Bridge`,
`QRTour.CosetStructure`, `QRTour.CarryTransducer`,
`QRTour.CarryComparison`, and `QRTour.CompositeVisibility` package the exact
infrastructure beneath those public statements.

## Exact/Open Boundary

The current Lean surface deliberately stops short of promoting two tracked
claims:

- `small_k_visibility_threshold` remains `open`; Lean currently proves the
  exact fixed-window certificate, same-core transport, and certified finite
  visible-word agreement beneath that boundary
- `carry_dfa_factorization` remains `open`; Lean currently proves finite carry
  normalization, traced comparison, and finite state-alignment criteria beneath
  that boundary

## Example: p = 97, B = 10, m = 2

- k = 10² mod 97 = 3
- ord₉₇(3) = 48 = (97-1)/2
- The sequence 3⁰, 3¹, 3², ..., 3⁴⁷ hits all 48 quadratic residues mod 97

## Modules

- `QRTour.Basic` - Prime field setup with `ZMod p`
- `QRTour.QuadraticResidues` - QR definitions and QR generators
- `QRTour.QuadraticResidues.pow_isQRGenerator_iff` - exact order/gcd classification for QR-generating powers
- `QRTour.RemainderOrbit` - Long division remainders and the main theorem
- `QRTour.PrimitiveRoots` - Full generators (primitive roots) and subgroup generators
- `QRTour.Digits` - Digit-remainder duality and reptend periodicity
- `QRTour.Bridge` - "Bridge primes" of form p = B^k - d with block structure
- `QRTour.BridgeQuality` - Approximate bridges, deficit metrics, factor inheritance
- `QRTour.SignedBridge` - Unified plus/minus bridges, alternating sign structure
- `QRTour.PAdicBridge` - P-adic structure in bridges, block values, periodicity
- `QRTour.CosetStructure` - Two-coset partition based on QR/NQR numerators
- `QRTour.CompositePeriod` - finite-family CRT period theorem for composite moduli
- `QRTour.Preperiod` - local valuation theorem behind composite preperiod lengths
- `QRTour.OrbitWeave` - block-coordinate arithmetic for the q-weighted series layer
- `QRTour.Visibility` - exact incoming-carry boundaries and same-core threshold shifts
- `QRTour.CarryTransducer` - finite carry-normalization on raw coefficient words
- `QRTour.CarryComparison` - exact finite-window carry/remainder trace alignment
- `QRTour.CompositeVisibility` - same-core family packaging for stripped periodic cores
- `QRTour.Examples` - Concrete examples with p = 97

## Notes On Agda Correspondence

The original repository narrative started from an Agda development, but the
Lean tree is now the exact formal backend. For the current Agda-local versus
Lean-backed boundary, use `docs/AGDA_CORRESPONDENCE.md` rather than reading this
module as a simple porting note.

-/
