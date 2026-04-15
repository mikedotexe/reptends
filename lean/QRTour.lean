/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- QRT_SURFACE_IMPORTS_START
import QRTour.Basic
import QRTour.RemainderOrbit
import QRTour.Bridge
import QRTour.CosetStructure
import QRTour.QuadraticResidues
import QRTour.OrbitWeave
import QRTour.Digits
import QRTour.PrimitiveRoots
import QRTour.BridgeQuality
import QRTour.SignedBridge
import QRTour.PAdicBridge
import QRTour.CompositePeriod
import QRTour.Preperiod
import QRTour.Visibility
import QRTour.CarryTransducer
import QRTour.CarryComparison
import QRTour.Factorization
import QRTour.CompositeVisibility
import QRTour.Examples
-- QRT_SURFACE_IMPORTS_END

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
- exact finite-window visibility and carry-transducer interfaces
- same-core composite visibility transport
- restricted finite-window orbit/carry factorization witnesses and obstructions

## Proof-System Framing

Use the same public proof-system legend here as in the theorem guide:

<!-- PROOF_SYSTEM_LEGEND_START -->
- `Lean-formalized`: proved in the Lean tree and suitable for theorem-level citation in the current public surface.
- `Agda-locally-proved`: discharged inside the Agda pedagogical companion surface without relying on Agda postulates.
- `Agda-postulated but Lean-backed`: still explicit as an Agda postulate, but closed by Lean or an atlas-backed Lean-backed claim in this repo.
- `empirical`: implemented and regression-tested here, but not promoted to theorem status.
- `open`: tracked as an unresolved claim boundary or interface question, not an established result.
<!-- PROOF_SYSTEM_LEGEND_END -->

Lean is the theorem-complete formal backend for the current atlas-backed exact
claims. Agda remains a pedagogical companion surface rather than a theorem-parity
target.

## Current Theorem Surface

The main atlas-backed Lean carriers are:

<!-- QRT_SURFACE_THEOREM_SURFACE_START -->
- `QRTour.OrbitWeave` for `series_q_weighted_identity` and `positive_q_good_modes`
- `QRTour.Digits` for `digit_periodicity`
- `QRTour.SignedBridge` for `signed_bridge_recurrence`
- `QRTour.PAdicBridge` for `bridge_block_value_periodicity`
- `QRTour.Visibility` for `incoming_carry_position_formula`
- `QRTour.Visibility` together with `QRTour.CompositeVisibility` for `same_core_threshold_shift_interval`
- `QRTour.QuadraticResidues` for `qr_stride_classification`
- `QRTour.CompositePeriod` for `crt_period_lcm`
- `QRTour.Preperiod` together with `QRTour.CompositeVisibility` for `preperiod_from_base_factors`
- `QRTour.CarryTransducer` together with `QRTour.CarryComparison` for `carry_window_transducer`

Support modules such as `QRTour.RemainderOrbit`, `QRTour.Bridge`,
`QRTour.CosetStructure`, and `QRTour.CompositeVisibility` package the exact
infrastructure beneath those public statements. The carry modules also sit on
the theorem boundary: they carry the exact finite
`carry_window_transducer` claim while still serving as support beneath the
open global `carry_dfa_factorization` claim.
`QRTour.PrimitiveRoots` remains general generator infrastructure above the
current QR-specific claim surface, and `QRTour.BridgeQuality` remains an
exploratory bridge-quality support layer rather than an atlas-backed theorem
carrier.
<!-- QRT_SURFACE_THEOREM_SURFACE_END -->

## Exact/Open Boundary

The current Lean surface deliberately stops short of promoting two tracked
claims:

<!-- QRT_SURFACE_OPEN_BOUNDARY_START -->
- `small_k_visibility_threshold` remains `open`; Lean currently proves the exact fixed-window certificate, same-core transport, and certified finite visible-word agreement beneath that boundary
- `carry_dfa_factorization` remains `open`; Lean currently proves finite carry normalization, traced comparison, restricted coordinate-level morphism packaging, and finite state-alignment criteria beneath that boundary
<!-- QRT_SURFACE_OPEN_BOUNDARY_END -->

## Example: p = 97, base = 10, m = 2, B = 100

- `B = 10^2 = 100` and `k = B mod 97 = 3`
- `ord_97(3) = 48 = (97 - 1) / 2`
- The sequence `3^0, 3^1, 3^2, ..., 3^47` hits all 48 quadratic residues mod 97

## Modules

<!-- QRT_SURFACE_MODULES_START -->
- `QRTour.Basic` - Prime field setup with `ZMod p`
- `QRTour.RemainderOrbit` - Long division remainders and the main theorem
- `QRTour.Bridge` - "Bridge primes" of form p = B^k - d with block structure
- `QRTour.CosetStructure` - Two-coset partition based on QR/NQR numerators
- `QRTour.QuadraticResidues` - QR definitions and QR generators, including the exact order/gcd classification for QR-generating powers
- `QRTour.OrbitWeave` - block-coordinate arithmetic for the q-weighted series layer
- `QRTour.Digits` - Digit-remainder duality and reptend periodicity
- `QRTour.PrimitiveRoots` - Full generators (primitive roots) and subgroup generators; support-only infrastructure above the current atlas-backed QR surface
- `QRTour.BridgeQuality` - Approximate bridges, deficit metrics, factor inheritance; exploratory support only, not an atlas-backed theorem carrier
- `QRTour.SignedBridge` - Unified plus/minus bridges, alternating sign structure
- `QRTour.PAdicBridge` - P-adic structure in bridges, block values, periodicity
- `QRTour.CompositePeriod` - finite-family CRT period theorem for composite moduli
- `QRTour.Preperiod` - local valuation theorem behind composite preperiod lengths
- `QRTour.Visibility` - exact incoming-carry boundaries and same-core threshold shifts
- `QRTour.CarryTransducer` - finite carry-normalization on raw coefficient words
- `QRTour.CarryComparison` - exact finite-window carry/remainder trace alignment
- `QRTour.Factorization` - restricted finite-window remainder-to-carry morphism layer
- `QRTour.CompositeVisibility` - same-core family packaging for stripped periodic cores
- `QRTour.Examples` - Worked prime, small composite, positive-q composite, and same-core composite examples
<!-- QRT_SURFACE_MODULES_END -->

## Notes On Agda Correspondence

The original repository narrative started from an Agda development, but the
Lean tree is now the exact formal backend. For the current Agda-local versus
Lean-backed boundary, use `docs/AGDA_CORRESPONDENCE.md` rather than reading this
module as a simple porting note.

-/
