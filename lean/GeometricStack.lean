/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GeometricStack.Family
import GeometricStack.Capacity
import GeometricStack.Scale
import GeometricStack.Valuation
import GeometricStack.Positional
import GeometricStack.OrbitBufferDuality

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

## Modules

- `GeometricStack.Family` - Basic definitions of a and B
- `GeometricStack.Capacity` - Capacity index T_n
- `GeometricStack.Scale` - Decomposition at a fixed scale
- `GeometricStack.Valuation` - Capacity as discrete valuation, Nat.digits connection

## Porting from Agda

The Agda version used postulates for:
- Monotonicity of a
- Existence of capacity indices
- Uniqueness of capacity indices

In Lean, these are proved directly using `Nat.pow_le_pow_right` and `Nat.log`.
-/
