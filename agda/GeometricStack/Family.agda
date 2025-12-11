module GeometricStack.Family where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_ ; _^_; _≤_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

------------------------------------------------------------------------
-- Geometric stack family:
--   - base : underlying radix (b ≥ 2)
--   - k    : geometric multiplier (k ≥ 1)
--
-- Determines:
--   - a[i] = k^i          (the "source stack")
--   - B n = base^n        (all possible word capacities)
------------------------------------------------------------------------

record Family : Set₁ where
  field
    base   : ℕ
    k      : ℕ
    base≥2 : 2 ≤ base
    k≥1    : 1 ≤ k

  ----------------------------------------------------------------------
  -- The geometric stack: a[i] = k^i
  ----------------------------------------------------------------------

  a : ℕ → ℕ
  a i = k ^ i

  ----------------------------------------------------------------------
  -- Word capacities: B n = base^n
  ----------------------------------------------------------------------

  B : ℕ → ℕ
  B n = base ^ n
