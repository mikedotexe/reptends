/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Nat.Even

/-!
# Prime Field Foundations for Quadratic Residue Tour

This module establishes the foundational definitions for working with prime fields
in the context of the quadratic residue tour.

## Main Definitions

* `QRTour.half p` - The value `(p - 1) / 2` for odd prime `p`
-/

namespace QRTour

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- Half of `p - 1`. For odd prime `p`, this is the size of the quadratic residue subgroup. -/
def half : ℕ := (p - 1) / 2

/-- For odd prime p > 2, we have p - 1 = 2 * half p. -/
theorem half_spec (hp_odd : p ≠ 2) : p - 1 = 2 * half p := by
  -- For odd p, p-1 is even, so p - 1 = 2 * ((p-1)/2)
  simp only [half]
  exact (Nat.two_mul_div_two_of_even (hp.out.even_sub_one hp_odd)).symm

/-- The order of the multiplicative group (ZMod p)ˣ is p - 1. -/
theorem card_units_eq_sub_one : Fintype.card (ZMod p)ˣ = p - 1 :=
  ZMod.card_units p

end QRTour
