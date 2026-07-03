/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- GEOMETRIC_STACK_IMPORTS_START
import GeometricStack.Family
import GeometricStack.Capacity
import GeometricStack.Scale
import GeometricStack.Valuation
import GeometricStack.Positional
import GeometricStack.OrbitBufferDuality
-- GEOMETRIC_STACK_IMPORTS_END

/-!
# Geometric Stack

This library provides a framework for analyzing geometric sequences k^0, k^1, k^2, ...
in the context of bounded word sizes.

## Overview

A "geometric stack" models how a geometric sequence interacts with word capacities
of increasing sizes. Given:
- A base radix (e.g., 10 for decimal)
- A geometric multiplier k

We define:
- The geometric sequence: a[i] = k^i
- Word capacities: B[n] = base^n
- Capacity index: T_n = max{i : a[i] < B[n]} = floor(log_k(B[n]))

## Decomposition

At a fixed scale n with capacity B_s = base^n, each term decomposes as:

  a[i] = illegal[i] * B_s + direct[i]

where:
- direct[i] = a[i] mod B_s (fits in the word)
- illegal[i] = a[i] / B_s (overflow)

## The Clean Window

For i ≤ T_n:
- a[i] < B_s
- illegal[i] = 0
- direct[i] = a[i]

This is the "clean geometric region" where no overflow occurs.

## Proof-System Framing

Use the shared public proof-system legend here as on the main Lean theorem
surfaces. `GeometricStack` is a companion infrastructure surface rather than a
direct atlas-backed theorem carrier, but its public role should still stay
legible relative to the rest of the repo.

<!-- PROOF_SYSTEM_LEGEND_START -->
- `Lean-formalized`: proved in the Lean tree and suitable for theorem-level citation in the current public surface.
- `Agda-locally-proved`: discharged inside the Agda pedagogical companion surface without relying on Agda postulates.
- `Agda-postulated but Lean-backed`: still explicit as an Agda postulate, but closed by Lean or an atlas-backed Lean-backed claim in this repo.
- `empirical`: implemented and regression-tested here, but not promoted to theorem status.
- `open`: tracked as an unresolved claim boundary or interface question, not an established result.
<!-- PROOF_SYSTEM_LEGEND_END -->

## Modules

<!-- GEOMETRIC_STACK_MODULES_START -->
- `GeometricStack.Family` - base-invariant family definitions for capacities and geometric powers
- `GeometricStack.Capacity` - capacity-index packaging and threshold-bound layer
- `GeometricStack.Scale` - fixed-scale direct and overflow decomposition layer
- `GeometricStack.Valuation` - capacity-as-valuation and digit-count companion layer
- `GeometricStack.Positional` - positional-digit companion surface for the scale decomposition
- `GeometricStack.OrbitBufferDuality` - repunit remainder-orbit conjugacy and periodicity companion layer
<!-- GEOMETRIC_STACK_MODULES_END -->

## Porting from Agda

The Agda version used postulates for:
- Monotonicity of a
- Existence of capacity indices
- Uniqueness of capacity indices

In Lean, these are proved directly using `Nat.pow_le_pow_right` and `Nat.log`.
-/
