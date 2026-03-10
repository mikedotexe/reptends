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
import QRTour.Examples

/-!
# Quadratic Residue Tour

This library formalizes the connection between decimal expansions and quadratic
residues modulo primes. It is a port of the Agda formalization at
https://github.com/mikepurvis/quadratic-residue-reptends

## Overview

For a prime p and base B coprime to p, the decimal expansion of 1/p in base B
has remainders r[0], r[1], r[2], ... satisfying r[n] = B^n (mod p).

When we sample at stride m, we get r[0], r[m], r[2m], ... which equals
k^0, k^1, k^2, ... where k = B^m mod p.

If k happens to be a "QR generator" (a quadratic residue with order (p-1)/2),
then this stride-m sequence visits every quadratic residue exactly once.

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
- `QRTour.Examples` - Concrete examples with p = 97

## Porting from Agda

The original Agda code used many postulates for facts about modular arithmetic
and group theory. In Lean with Mathlib, most of these become actual theorems:

| Agda Postulate | Lean/Mathlib Equivalent |
|----------------|------------------------|
| `IsPrime` | `Nat.Prime` + `Fact` |
| `_≡ₚ_` | Equality in `ZMod p` |
| `powMod` | `^` in `ZMod p` |
| `order` | `orderOf` on `(ZMod p)ˣ` |
| `order-divides-p-1` | `orderOf_dvd_card` |

-/
