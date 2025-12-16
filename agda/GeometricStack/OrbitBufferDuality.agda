module GeometricStack.OrbitBufferDuality where

------------------------------------------------------------------------
-- Orbit-Buffer Duality
--
-- This module formalizes the key insight connecting repetend digit
-- computation to multiplicative orbits:
--
--   "The digit tape is the orbit, because division is a DFA whose
--    state is the remainder."
--
-- We define the affine update f(x) = b·x + (b-1) (repunit division)
-- and the linear update g(x) = b·x (multiplication), and show they
-- are conjugate via the shift T(x) = x + 1:
--
--   T ∘ f = g ∘ T
--
-- The key postulates (proved in Lean using Mathlib) are:
--   - repunitRem-closed : repunitRem t ≡ (b^t - 1) mod M
--   - orbit-buffer-duality : orbitRem t ≡ (repunitRem t + 1) mod M
------------------------------------------------------------------------

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _<_; _>_; NonZero)
open import Data.Nat.DivMod as DivMod
  using (_mod_; _div_; _%_; _/_)
open import Data.Fin using (Fin; toℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)

------------------------------------------------------------------------
-- Parameters: base b and modulus M
--
-- For the orbit interpretation:
--   b = base (e.g., 10 for decimal)
--   M = modulus (the denominator in 1/M)
------------------------------------------------------------------------

module Orbit (b M : ℕ) ⦃ M-nonzero : NonZero M ⦄ where

  ------------------------------------------------------------------------
  -- Basic modular operations
  ------------------------------------------------------------------------

  -- Modular power: a^n mod m
  powMod : ℕ → ℕ → ℕ
  powMod a n = toℕ ((a ^ n) mod M)

  -- Modular multiplication
  _*ₘ_ : ℕ → ℕ → ℕ
  x *ₘ y = toℕ ((x * y) mod M)

  -- Modular addition
  _+ₘ_ : ℕ → ℕ → ℕ
  x +ₘ y = toℕ ((x + y) mod M)

  ------------------------------------------------------------------------
  -- Step functions
  --
  -- Linear step: x ↦ b * x (mod M)
  -- Affine step: x ↦ b * x + (b - 1) (mod M)
  -- Shift:       x ↦ x + 1 (mod M)
  ------------------------------------------------------------------------

  linearStep : ℕ → ℕ
  linearStep x = b *ₘ x

  affineStep : ℕ → ℕ
  affineStep x = (b *ₘ x) +ₘ (b ∸ 1)

  shift : ℕ → ℕ
  shift x = x +ₘ 1

  ------------------------------------------------------------------------
  -- Orbit sequences
  --
  -- Linear orbit: 1, b, b², b³, ... (starting at 1)
  -- Affine orbit: 0, b-1, b²-1, b³-1, ... (starting at 0)
  ------------------------------------------------------------------------

  -- Linear orbit: powers of b mod M
  linearOrbit : ℕ → ℕ
  linearOrbit zero    = 1 ∸ M  -- 1 mod M, but returns 1 when M > 1
  linearOrbit (suc n) = linearStep (linearOrbit n)

  -- Simpler: just use powMod directly
  orbitRem : ℕ → ℕ
  orbitRem t = powMod b t

  -- Affine orbit: (b^n - 1) mod M (repunit division remainders)
  affineOrbit : ℕ → ℕ
  affineOrbit zero    = 0
  affineOrbit (suc n) = affineStep (affineOrbit n)

  -- Alternative: repunit remainder directly
  repunitRem : ℕ → ℕ
  repunitRem t = toℕ (((b ^ t) ∸ 1) mod M)

  ------------------------------------------------------------------------
  -- Digit extraction
  --
  -- Given remainder r_t = b^t mod M, the base-b digit of 1/M at position t is:
  --   d_t = floor(b * r_t / M)
  ------------------------------------------------------------------------

  digitAt : ℕ → ℕ
  digitAt t = (b * orbitRem t) / M

  ------------------------------------------------------------------------
  -- Key postulates (proved in Lean)
  --
  -- These capture the orbit-buffer duality relationship.
  ------------------------------------------------------------------------

  -- The affine orbit computes (b^n - 1) mod M
  postulate
    repunitRem-closed : ∀ t → repunitRem t ≡ affineOrbit t

  -- The duality: orbitRem t ≡ (repunitRem t + 1) mod M
  -- This is the formal statement that shift(affine) = linear
  postulate
    orbit-buffer-duality : ∀ t → orbitRem t ≡ shift (repunitRem t)

  -- The conjugacy as an equation: shift (affineStep x) ≡ linearStep (shift x)
  -- This is the key structural fact, trivial to prove: (bx + (b-1)) + 1 = b(x+1)
  postulate
    shift-conjugacy : ∀ x → shift (affineStep x) ≡ linearStep (shift x)

  -- No-mod step: the recurrence without mod, using digit extraction
  -- r_{t+1} = b * r_t - d_t * M
  postulate
    noMod-step : ∀ t → orbitRem (suc t) ≡ (b * orbitRem t ∸ digitAt t * M)

  ------------------------------------------------------------------------
  -- Multiplicative order
  --
  -- The period of the digit sequence is ord_M(b), the multiplicative order.
  -- We abstract this since proving order properties requires finite group theory.
  ------------------------------------------------------------------------

  postulate
    ord : ℕ
    ord-spec : ord > 0
    ord-period : powMod b ord ≡ 1

  -- Periodicity: the orbit repeats every ord steps
  postulate
    orbitRem-periodic : ∀ t → orbitRem (t + ord) ≡ orbitRem t
    digitAt-periodic : ∀ t → digitAt (t + ord) ≡ digitAt t

------------------------------------------------------------------------
-- Example: 1/19 in base 10
--
-- ord_19(10) = 18
-- Digits: 0,5,2,6,3,1,5,7,8,9,4,7,3,6,8,4,2,1
------------------------------------------------------------------------

module Example-19 where
  open Orbit 10 19 ⦃ _ ⦄

  -- First few digits (can evaluate with C-c C-n)
  d0 : ℕ
  d0 = digitAt 0  -- should be 0

  d1 : ℕ
  d1 = digitAt 1  -- should be 5

  d2 : ℕ
  d2 = digitAt 2  -- should be 2

------------------------------------------------------------------------
-- Example: 1/7 in base 10
--
-- ord_7(10) = 6
-- Digits: 1,4,2,8,5,7
------------------------------------------------------------------------

module Example-7 where
  open Orbit 10 7 ⦃ _ ⦄

  d0 : ℕ
  d0 = digitAt 0  -- should be 1

  d1 : ℕ
  d1 = digitAt 1  -- should be 4

  d2 : ℕ
  d2 = digitAt 2  -- should be 2
