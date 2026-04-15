/-
Copyright (c) 2024 Mike Purvis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
# Orbit-Buffer Duality

This module formalizes the key insight connecting repetend digit computation to
multiplicative orbits:

> **The digit tape is the orbit, because division is a DFA whose state is the remainder.**

We prove that the affine update `f(x) = b·x + (b-1)` (repunit division) is conjugate
to the linear update `g(x) = b·x` (multiplication) via the shift `T(x) = x + 1`.

## Main Results

* `shift_conj` - The conjugacy: `shift (affineStep x) = linearStep (shift x)`
* `shift_affineOrbit_eq_linearOrbit` - Duality: `shift (affineOrbit n) = linearOrbit n`
* `affineOrbit_periodic` - Periodicity of the affine remainder orbit
* `orbitRem_succ_eq_mod` - The executable remainder tape satisfies the Euclidean mod-step recursion
* `digitAt_orbitRem_eq` - The executable digit tape is the corresponding Euclidean quotient
* `orbitRem_periodic` - Periodicity of remainder sequence
* `digitAt_periodic` - Periodicity of digit sequence

## Mathematical Background

In long division of repunits (999...9), the remainder at step t satisfies:
```
r_{t+1} = b·r_t + (b-1)  (mod M)
```
with r_0 = 0. This is an *affine* recurrence.

The multiplicative orbit (powers of b) satisfies:
```
s_{t+1} = b·s_t  (mod M)
```
with s_0 = 1. This is a *linear* recurrence.

The shift T(x) = x + 1 conjugates the two: if we write s_t = r_t + 1, then
the linear recurrence on s_t becomes the affine recurrence on r_t.

This means the "digit tape" of 1/M is fundamentally just the orbit of b in (ℤ/Mℤ)ˣ.
-/

namespace GeometricStack

namespace OrbitBufferDuality

variable {M : ℕ} [NeZero M]

/-!
We work in `ZMod M` for the clean algebra.
Then we expose executable "random access digit" functions using `ZMod.val`.
-/

-- Linear update: x ↦ b*x
def linearStep (b : ℕ) : ZMod M → ZMod M := fun x => (b : ZMod M) * x

-- Affine update: x ↦ b*x + (b - 1)
-- We write (b : ZMod M) - 1 to avoid Nat-truncated subtraction corner cases.
def affineStep (b : ℕ) : ZMod M → ZMod M := fun x => (b : ZMod M) * x + ((b : ZMod M) - 1)

-- Translation: x ↦ x + 1
def shift : ZMod M → ZMod M := fun x => x + 1

-- Conjugacy: shift (affineStep x) = linearStep (shift x)
omit [NeZero M] in
theorem shift_conj (b : ℕ) (x : ZMod M) :
    shift (M := M) (affineStep (M := M) b x) =
      linearStep (M := M) b (shift x) := by
  -- (b*x + (b-1)) + 1 = b*(x+1)
  simp [shift, affineStep, linearStep]
  ring

-- Iterated linear orbit, starting at 1
def linearOrbit (b : ℕ) : ℕ → ZMod M
| 0     => 1
| n + 1 => linearStep (M := M) b (linearOrbit b n)

-- Iterated affine orbit, starting at 0
def affineOrbit (b : ℕ) : ℕ → ZMod M
| 0     => 0
| n + 1 => affineStep (M := M) b (affineOrbit b n)

-- linearOrbit is just powers
omit [NeZero M] in
theorem linearOrbit_eq_pow (b : ℕ) :
    ∀ n, linearOrbit (M := M) b n = (b : ZMod M) ^ n := by
  intro n
  induction n with
  | zero =>
      simp [linearOrbit]
  | succ n ih =>
      simp [linearOrbit, linearStep, ih, pow_succ, mul_comm]

-- affineOrbit is (b^n - 1)
omit [NeZero M] in
theorem affineOrbit_eq_pow_sub_one (b : ℕ) :
    ∀ n, affineOrbit (M := M) b n = (b : ZMod M) ^ n - 1 := by
  intro n
  induction n with
  | zero =>
      simp [affineOrbit]
  | succ n ih =>
      simp [affineOrbit, affineStep, ih, pow_succ]
      ring

-- The orbit-buffer duality: shifting the affine orbit gives the linear orbit
omit [NeZero M] in
theorem shift_affineOrbit_eq_linearOrbit (b : ℕ) :
    ∀ n, shift (M := M) (affineOrbit (M := M) b n) = linearOrbit (M := M) b n := by
  intro n
  simp only [affineOrbit_eq_pow_sub_one, linearOrbit_eq_pow, shift]
  ring

-- Executable: remainder r_t = (b^t mod M) as a Nat representative
def orbitRem (b : ℕ) (t : ℕ) : ℕ :=
  ((b : ZMod M) ^ t).val

-- Executable: digit d_t = floor(b * r_t / M)
def digitAt (b : ℕ) (t : ℕ) : ℕ :=
  (b * orbitRem (M := M) b t) / M

-- The executable remainder tape satisfies the Euclidean mod-step recursion.
theorem orbitRem_succ_eq_mod (b : ℕ) (t : ℕ) :
    orbitRem (M := M) b (t + 1) = (b * orbitRem (M := M) b t) % M := by
  rw [orbitRem, pow_succ, mul_comm]
  conv_lhs => rw [← ZMod.natCast_zmod_val ((b : ZMod M) ^ t)]
  rw [← Nat.cast_mul, ZMod.val_natCast, orbitRem]

-- The executable digit tape is the corresponding Euclidean quotient.
omit [NeZero M] in
theorem digitAt_eq_div (b : ℕ) (t : ℕ) :
    digitAt (M := M) b t = (b * orbitRem (M := M) b t) / M := rfl

-- The executable digit/remainder pair satisfies the Euclidean division law.
theorem digitAt_orbitRem_eq (b : ℕ) (t : ℕ) :
    b * orbitRem (M := M) b t =
      digitAt (M := M) b t * M + orbitRem (M := M) b (t + 1) := by
  rw [orbitRem_succ_eq_mod, digitAt_eq_div]
  exact (Nat.div_add_mod' (b * orbitRem (M := M) b t) M).symm

-- If b is coprime to M, we can package the period using units and orderOf.
-- This is the canonical `L = ord_M(b)` definition in mathlib.
def baseUnit (b : ℕ) (hb : b.Coprime M) : (ZMod M)ˣ :=
  ZMod.unitOfCoprime b hb

noncomputable def period (b : ℕ) (hb : b.Coprime M) : ℕ :=
  orderOf (baseUnit (M := M) b hb)

-- b^period = 1 in ZMod M (the "closure of the orbit")
omit [NeZero M] in
theorem pow_period_eq_one (b : ℕ) (hb : b.Coprime M) :
    ((b : ZMod M) ^ period (M := M) b hb) = 1 := by
  -- In units: u^orderOf u = 1
  have hu : (baseUnit (M := M) b hb) ^ period (M := M) b hb = 1 := by
    simp [period, pow_orderOf_eq_one (baseUnit (M := M) b hb)]
  -- Coerce to ZMod M
  have hz : ((↑((baseUnit (M := M) b hb) ^ period (M := M) b hb) : ZMod M)) = (1 : ZMod M) :=
    congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hu
  simpa [baseUnit] using hz

omit [NeZero M] in
theorem affineOrbit_periodic (b : ℕ) (hb : b.Coprime M) (t : ℕ) :
    affineOrbit (M := M) b (t + period (M := M) b hb) = affineOrbit (M := M) b t := by
  rw [affineOrbit_eq_pow_sub_one (M := M) b (t + period (M := M) b hb)]
  rw [affineOrbit_eq_pow_sub_one (M := M) b t]
  calc
    (b : ZMod M) ^ (t + period (M := M) b hb) - 1
        = ((b : ZMod M) ^ t) * ((b : ZMod M) ^ period (M := M) b hb) - 1 := by
            rw [pow_add]
    _ = ((b : ZMod M) ^ t) * 1 - 1 := by rw [pow_period_eq_one (M := M) b hb]
    _ = (b : ZMod M) ^ t - 1 := by simp

-- Periodicity of the remainder tape (and hence digits) under coprimality
omit [NeZero M] in
theorem orbitRem_periodic (b : ℕ) (hb : b.Coprime M) (t : ℕ) :
    orbitRem (M := M) b (t + period (M := M) b hb) = orbitRem (M := M) b t := by
  have : ((b : ZMod M) ^ (t + period (M := M) b hb)) = ((b : ZMod M) ^ t) := by
    -- b^(t+L) = b^t * b^L = b^t
    simp [pow_add, pow_period_eq_one (M := M) b hb, mul_one]
  exact congrArg ZMod.val this

omit [NeZero M] in
theorem digitAt_periodic (b : ℕ) (hb : b.Coprime M) (t : ℕ) :
    digitAt (M := M) b (t + period (M := M) b hb) = digitAt (M := M) b t := by
  simp [digitAt, orbitRem_periodic (M := M) b hb t]

/-! ## Examples

Small sanity checks recorded as silent executable examples so public Lean builds
do not emit `#eval` output.
-/
section Examples

-- 1/19 = 0.\overline{052631578947368421} in base 10
-- The digits are: 0,5,2,6,3,1,5,7,8,9,4,7,3,6,8,4,2,1
example :
    List.map (digitAt (M := 19) 10) (List.range 18) =
      [0, 5, 2, 6, 3, 1, 5, 7, 8, 9, 4, 7, 3, 6, 8, 4, 2, 1] := by
  native_decide

-- 1/7 = 0.\overline{142857} in base 10
example :
    List.map (digitAt (M := 7) 10) (List.range 6) = [1, 4, 2, 8, 5, 7] := by
  native_decide

-- 1/97 = 0.\overline{...96 digits...} in base 10
-- Period is 96, showing 10 is a primitive root mod 97
example :
    List.map (digitAt (M := 97) 10) (List.range 10) = [0, 1, 0, 3, 0, 9, 2, 7, 8, 3] := by
  native_decide

end Examples

end OrbitBufferDuality

end GeometricStack
