import GeometricStack.Family as Fam

module GeometricStack.Capacity
  (F : Fam.Family)
  where

open Fam.Family F public

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_ ; _^_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

------------------------------------------------------------------------
-- Base-invariant capacity index for the geometric stack a[i] = k^i.
--
-- For each word length n, with capacity B n = base^n, we define a
-- record Capacity n that packages:
--
--   Tₙ       : ℕ
--   powBelow : ∀ i ≤ Tₙ.  a[i] < B n
--   powAbove :            B n ≤ a[Tₙ + 1]
--
-- This is exactly "T = floor(log_k(B))", but phrased arithmetically.
-- It depends only on (base, k) via a[i] and B n. No decimals, no
-- factorization of B n - k, nothing base-specific.
------------------------------------------------------------------------

record Capacity (n : ℕ) : Set where
  field
    Tₙ       : ℕ
    powBelow : ∀ {i} → i ≤ Tₙ → a i < B n
    powAbove : B n ≤ a (suc Tₙ)

------------------------------------------------------------------------
-- Monotonicity of k^i in i (for k ≥ 1), which underlies existence and
-- uniqueness of Tₙ. You can prove this once and reuse everywhere.
------------------------------------------------------------------------

postulate
  a-monotone :
    ∀ {i j} → i ≤ j → a i ≤ a j

------------------------------------------------------------------------
-- Existence of a capacity index for any n with B n > 0.
--
-- In practice, you'll either:
--   - prove this by primitive recursion on i using a-monotone, or
--   - keep it as a postulate while you develop the rest.
------------------------------------------------------------------------

postulate
  capacity-exists : ∀ (n : ℕ) → Capacity n

------------------------------------------------------------------------
-- Uniqueness of the capacity index: if c1 and c2 both satisfy the
-- capacity conditions for the same n, then Tₙ is uniquely determined.
------------------------------------------------------------------------

postulate
  capacity-unique :
    ∀ {n}
      (c1 c2 : Capacity n) →
      Capacity.Tₙ c1 ≡ Capacity.Tₙ c2
