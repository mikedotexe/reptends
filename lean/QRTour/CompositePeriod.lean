/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import QRTour.Digits
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.ZMod.QuotientRing

/-!
# Composite Period via CRT

This module packages the CRT period theorem for composite moduli:

- in the pairwise coprime case, the order of a unit modulo `m * n`
  is the least common multiple of its component orders modulo `m` and `n`;
- more generally, Mathlib's finite-family CRT equivalence for `ZMod`
  carries unit orders to the `Finset.lcm` of the component orders.

This is the formal bridge from the prime-side Lean development to the
composite/CRT period story used elsewhere in the repo.
-/

namespace QRTour

open scoped BigOperators Function

/-- The order of an element in a finite product of monoids is the lcm of the component orders. -/
theorem orderOf_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, Monoid (M i)] (x : ∀ i, M i) :
    orderOf x = Finset.lcm Finset.univ (fun i => orderOf (x i)) := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    ext i
    rw [Pi.pow_apply, Pi.one_apply, ← orderOf_dvd_iff_pow_eq_one]
    exact Finset.dvd_lcm (Finset.mem_univ i)
  · apply Finset.lcm_dvd
    intro i hi
    exact orderOf_map_dvd (Pi.evalMonoidHom M i) x

/-- The unit-group form of the Chinese remainder equivalence for coprime moduli. -/
noncomputable def unitsChineseRemainder {m n : ℕ} (h : Nat.Coprime m n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

/-- Under CRT, the order of a unit modulo `m * n` is the lcm of its component orders. -/
theorem orderOf_unitsChineseRemainder {m n : ℕ} (h : Nat.Coprime m n) (u : (ZMod (m * n))ˣ) :
    orderOf u =
      Nat.lcm (orderOf ((unitsChineseRemainder h u).1)) (orderOf ((unitsChineseRemainder h u).2)) := by
  have horder : orderOf u = orderOf ((unitsChineseRemainder h) u) := by
    exact
      (orderOf_injective (unitsChineseRemainder h).toMonoidHom (unitsChineseRemainder h).injective u).symm
  calc
    orderOf u = orderOf ((unitsChineseRemainder h) u) := horder
    _ = Nat.lcm (orderOf ((unitsChineseRemainder h u).1)) (orderOf ((unitsChineseRemainder h u).2)) := by
      exact Prod.orderOf (unitsChineseRemainder h u)

/-- The unit-group form of Mathlib's finite-family CRT equivalence for pairwise coprime moduli. -/
noncomputable def unitsProdEquivPi {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) :
    (ZMod (∏ i, a i))ˣ ≃* Π i, (ZMod (a i))ˣ :=
  (Units.mapEquiv (ZMod.prodEquivPi a coprime).toMulEquiv).trans MulEquiv.piUnits

/-- Under finite-family CRT, the order of a unit is the lcm of the component orders. -/
theorem orderOf_unitsProdEquivPi {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    (coprime : Pairwise (Nat.Coprime on a)) (u : (ZMod (∏ i, a i))ˣ) :
    orderOf u = Finset.lcm Finset.univ (fun i => orderOf ((unitsProdEquivPi a coprime u) i)) := by
  calc
    orderOf u = orderOf ((unitsProdEquivPi a coprime) u) := by
      symm
      exact MulEquiv.orderOf_eq (unitsProdEquivPi a coprime) u
    _ = Finset.lcm Finset.univ (fun i => orderOf ((unitsProdEquivPi a coprime u) i)) := by
      exact orderOf_pi ((unitsProdEquivPi a coprime) u)

/-- The unit-group form of the prime-power CRT decomposition of `ZMod n`. -/
noncomputable def unitsEquivPrimePowers {n : ℕ} (hn : n ≠ 0) :
    (ZMod n)ˣ ≃* Π p : n.primeFactors, (ZMod ((p : ℕ) ^ (n.factorization p)))ˣ :=
  (Units.mapEquiv (ZMod.equivPi (n := n) hn).toMulEquiv).trans MulEquiv.piUnits

/-- For a nonzero modulus, the unit order is the lcm of the prime-power component orders. -/
theorem orderOf_unitsEquivPrimePowers {n : ℕ} (hn : n ≠ 0) (u : (ZMod n)ˣ) :
    orderOf u =
      Finset.lcm Finset.univ
        (fun p : n.primeFactors => orderOf ((unitsEquivPrimePowers hn u) p)) := by
  calc
    orderOf u = orderOf ((unitsEquivPrimePowers hn) u) := by
      symm
      exact MulEquiv.orderOf_eq (unitsEquivPrimePowers hn) u
    _ =
        Finset.lcm Finset.univ
          (fun p : n.primeFactors => orderOf ((unitsEquivPrimePowers hn u) p)) := by
      exact orderOf_pi ((unitsEquivPrimePowers hn) u)

section Examples

example :
    orderOf (1 : (ZMod (3 * 83))ˣ) =
      Nat.lcm (orderOf ((unitsChineseRemainder (by decide : Nat.Coprime 3 83) 1).1))
        (orderOf ((unitsChineseRemainder (by decide : Nat.Coprime 3 83) 1).2)) := by
  exact orderOf_unitsChineseRemainder (m := 3) (n := 83) (by decide : Nat.Coprime 3 83) 1

example :
    orderOf (1 : (ZMod 249)ˣ) =
      Finset.lcm Finset.univ
        (fun p : (249 : ℕ).primeFactors =>
          orderOf ((unitsEquivPrimePowers (n := 249) (by decide : 249 ≠ 0) 1) p)) := by
  exact orderOf_unitsEquivPrimePowers (n := 249) (by decide : 249 ≠ 0) 1

end Examples

end QRTour
