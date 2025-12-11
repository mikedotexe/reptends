import GeometricStack.Family as Fam
import GeometricStack.Capacity as Cap

module GeometricStack.Scale
  (F : Fam.Family)
  where

open Fam.Family F public
open Cap F using (Capacity; capacity-exists)

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_ ; _^_; _≤_; _<_; _∸_; NonZero)
open import Data.Nat.DivMod as DivMod
  using (_div_; _mod_)
open import Data.Fin using (toℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

------------------------------------------------------------------------
-- A single "word-size scale" on the geometric stack a[i] = k^i.
--
-- Given a Family (base, k, a, B), a Scale chooses:
--   - n   : word length (n ≥ 1)
--   - Bₛ  : capacity base^n
--   - capacity : Capacity n (Tₙ, powBelow, powAbove)
--
-- and then defines:
--   direct[i]  = a[i] mod Bₛ
--   illegal[i] = a[i] div Bₛ
--
-- plus the base-invariant clean-window facts:
--   ∀ i ≤ Tₙ.  illegal[i] = 0 and direct[i] = a[i].
------------------------------------------------------------------------

record Scale : Set₁ where
  field
    --------------------------------------------------------------------
    -- Parameters of this scale
    --------------------------------------------------------------------
    n   : ℕ          -- word length
    n≥1 : 1 ≤ n

  ----------------------------------------------------------------------
  -- Word capacity at this scale: Bₛ = base^n
  ----------------------------------------------------------------------

  Bₛ : ℕ
  Bₛ = B n

  ----------------------------------------------------------------------
  -- For the 1/(Bₛ - k) story we typically want Bₛ > k, but that's an
  -- extra assumption beyond the pure geometric stack view.
  ----------------------------------------------------------------------

  field
    k<Bₛ : k < Bₛ

  -- NonZero instance for Bₛ (derivable from k<Bₛ since k ≥ 0 implies Bₛ > 0)
  field
    instance Bₛ-nonzero : NonZero Bₛ

  ----------------------------------------------------------------------
  -- Base-invariant capacity index for this n:
  --
  --   Tₙ       : capacity bound (floor log_k(Bₛ))
  --   powBelow : a[i] < Bₛ for i ≤ Tₙ
  --   powAbove : Bₛ ≤ a[Tₙ + 1]
  ----------------------------------------------------------------------

  field
    cap : Capacity n

  open Capacity cap public
    renaming ( Tₙ       to Tₛ
             ; powBelow to powBelowₛ
             ; powAbove to powAboveₛ
             )

  ----------------------------------------------------------------------
  -- Decomposition of the stack at this scale:
  --
  --   a[i] = illegal[i] * Bₛ + direct[i]
  --
  -- This is the "residue + overflow" split that the stack view shows
  -- in its residue/flux bar charts.
  ----------------------------------------------------------------------

  direct : ℕ → ℕ
  direct i = toℕ (DivMod._mod_ (a i) Bₛ ⦃ Bₛ-nonzero ⦄)

  illegal : ℕ → ℕ
  illegal i = DivMod._div_ (a i) Bₛ ⦃ Bₛ-nonzero ⦄

  field
    direct<Bₛ : ∀ i → direct i < Bₛ

    stack-decomp : ∀ i →
      a i ≡ illegal i * Bₛ + direct i

  ----------------------------------------------------------------------
  -- Clean window: for i ≤ Tₛ (capacity index), a[i] < Bₛ, so we are
  -- guaranteed that:
  --
  --   illegal[i] = 0
  --   direct[i]  = a[i]
  --
  -- These are the "no overflow yet" invariants that show up as the
  -- clean geometric region, and they are base-invariant because
  -- Tₛ and powBelowₛ come from Cap.
  ----------------------------------------------------------------------

  field
    illegal-zero-up-to-T :
      ∀ {i} → i ≤ Tₛ → illegal i ≡ 0

    direct-equals-stack-up-to-T :
      ∀ {i} → i ≤ Tₛ → direct i ≡ a i
