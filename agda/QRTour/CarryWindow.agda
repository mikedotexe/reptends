module QRTour.CarryWindow where

------------------------------------------------------------------------
-- Finite carry-normalization on raw block coefficients.
--
-- This is the Agda companion to the repo's carry-normalization surface:
--
--   - input word: raw coefficients, most- or least-significant first
--   - state: incoming carry from less-significant blocks
--   - output word: normalized blocks
--
-- The module stays intentionally finite and structural. It does not assert
-- any global orbit/carry factorization theorem; it only formalizes the local
-- recursion and its traced finite-window data.
------------------------------------------------------------------------

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; _>_; NonZero; z≤n; s≤s; >-nonZero)
open import Data.Nat.DivMod as DivMod
  using (_div_; _mod_; _/_; _%_; m≡m%n+[m/n]*n; m%n<n)
open import Data.Nat.Properties
  using (≤-trans)
open import Data.Bool
  using (Bool; true; false)
open import Data.List
  using (List; []; _∷_; _++_; map; reverse; length)
open import Data.Product
  using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans)

------------------------------------------------------------------------
-- A finite carry window at one block base.
------------------------------------------------------------------------

module Window (blockBase : ℕ) (blockBase>1 : blockBase > 1) where

  instance
    blockBase-nonzero : NonZero blockBase
    blockBase-nonzero = >-nonZero (≤-trans (s≤s z≤n) blockBase>1)

  ----------------------------------------------------------------------
  -- Single-step carry normalization
  ----------------------------------------------------------------------

  -- On a non-leftmost block, split total mass into visible block + carry-out.
  stepRight : ℕ → ℕ → ℕ × ℕ
  stepRight coefficient carryIn =
    ( (coefficient + carryIn) % blockBase
    , (coefficient + carryIn) / blockBase
    )

  -- On the leftmost block, keep all remaining mass in the visible block.
  stepLeftmost : ℕ → ℕ → ℕ × ℕ
  stepLeftmost coefficient carryIn = coefficient + carryIn , 0

  stepRight-balance : ∀ coefficient carryIn →
    coefficient + carryIn ≡
      proj₁ (stepRight coefficient carryIn) +
        proj₂ (stepRight coefficient carryIn) * blockBase
  stepRight-balance coefficient carryIn =
    m≡m%n+[m/n]*n (coefficient + carryIn) blockBase

  stepRight-block< : ∀ coefficient carryIn →
    proj₁ (stepRight coefficient carryIn) < blockBase
  stepRight-block< coefficient carryIn =
    m%n<n (coefficient + carryIn) blockBase

  ----------------------------------------------------------------------
  -- Finite normalization recursion
  --
  -- Internally this runs on a least-significant-first list because carries
  -- move from right to left in the usual displayed order.
  ----------------------------------------------------------------------

  normalizeReversedAux : List ℕ → ℕ → List ℕ
  normalizeReversedAux [] carryIn = []
  normalizeReversedAux (coefficient ∷ []) carryIn = (coefficient + carryIn) ∷ []
  normalizeReversedAux (coefficient ∷ next ∷ tail) carryIn =
    proj₁ (stepRight coefficient carryIn) ∷
      normalizeReversedAux (next ∷ tail) (proj₂ (stepRight coefficient carryIn))

  normalizeReversed : List ℕ → List ℕ
  normalizeReversed coefficients = normalizeReversedAux coefficients 0

  normalizeBlocks : List ℕ → List ℕ
  normalizeBlocks coefficients = reverse (normalizeReversed (reverse coefficients))

  ----------------------------------------------------------------------
  -- Traced finite runs
  ----------------------------------------------------------------------

  record CarryTraceStep : Set where
    field
      coefficient : ℕ
      carryIn     : ℕ
      blockValue  : ℕ
      carryOut    : ℕ
      isLeftmost  : Bool

  open CarryTraceStep public

  mkTraceRight : ℕ → ℕ → CarryTraceStep
  mkTraceRight coefficient carryIn = record
    { coefficient = coefficient
    ; carryIn     = carryIn
    ; blockValue  = proj₁ (stepRight coefficient carryIn)
    ; carryOut    = proj₂ (stepRight coefficient carryIn)
    ; isLeftmost  = false
    }

  mkTraceLeftmost : ℕ → ℕ → CarryTraceStep
  mkTraceLeftmost coefficient carryIn = record
    { coefficient = coefficient
    ; carryIn     = carryIn
    ; blockValue  = proj₁ (stepLeftmost coefficient carryIn)
    ; carryOut    = proj₂ (stepLeftmost coefficient carryIn)
    ; isLeftmost  = true
    }

  traceReversedAux : List ℕ → ℕ → List CarryTraceStep
  traceReversedAux [] carryIn = []
  traceReversedAux (coefficient ∷ []) carryIn =
    mkTraceLeftmost coefficient carryIn ∷ []
  traceReversedAux (coefficient ∷ next ∷ tail) carryIn =
    let step = mkTraceRight coefficient carryIn in
    step ∷ traceReversedAux (next ∷ tail) (carryOut step)

  traceReversed : List ℕ → List CarryTraceStep
  traceReversed coefficients = traceReversedAux coefficients 0

  traceBlocks : List ℕ → List CarryTraceStep
  traceBlocks coefficients = reverse (traceReversed (reverse coefficients))

  ----------------------------------------------------------------------
  -- Structural local lemmas
  ----------------------------------------------------------------------

  normalizeReversedAux-length : ∀ coefficients carryIn →
    length (normalizeReversedAux coefficients carryIn) ≡ length coefficients
  normalizeReversedAux-length [] carryIn = refl
  normalizeReversedAux-length (coefficient ∷ []) carryIn = refl
  normalizeReversedAux-length (coefficient ∷ next ∷ tail) carryIn =
    cong suc
      (normalizeReversedAux-length
        (next ∷ tail)
        (proj₂ (stepRight coefficient carryIn)))

  traceReversedAux-length : ∀ coefficients carryIn →
    length (traceReversedAux coefficients carryIn) ≡ length coefficients
  traceReversedAux-length [] carryIn = refl
  traceReversedAux-length (coefficient ∷ []) carryIn = refl
  traceReversedAux-length (coefficient ∷ next ∷ tail) carryIn =
    cong suc
      (traceReversedAux-length
        (next ∷ tail)
        (proj₂ (stepRight coefficient carryIn)))

  traceReversedAux-map-blockValue : ∀ coefficients carryIn →
    map blockValue (traceReversedAux coefficients carryIn) ≡
      normalizeReversedAux coefficients carryIn
  traceReversedAux-map-blockValue [] carryIn = refl
  traceReversedAux-map-blockValue (coefficient ∷ []) carryIn = refl
  traceReversedAux-map-blockValue (coefficient ∷ next ∷ tail) carryIn =
    cong
      (proj₁ (stepRight coefficient carryIn) ∷_)
      (traceReversedAux-map-blockValue
        (next ∷ tail)
        (proj₂ (stepRight coefficient carryIn)))

  traceReversedAux-map-coefficient : ∀ coefficients carryIn →
    map coefficient (traceReversedAux coefficients carryIn) ≡ coefficients
  traceReversedAux-map-coefficient [] carryIn = refl
  traceReversedAux-map-coefficient (coefficient ∷ []) carryIn = refl
  traceReversedAux-map-coefficient (coefficient ∷ next ∷ tail) carryIn =
    cong
      (coefficient ∷_)
      (traceReversedAux-map-coefficient
        (next ∷ tail)
        (proj₂ (stepRight coefficient carryIn)))

------------------------------------------------------------------------
-- Small canonical example: block base 100 for the raw `1,3,9,27,81,243,729`
-- skeleton behind the `1/97` carry story.
------------------------------------------------------------------------

module Example-97 where
  open Window 100 (s≤s (s≤s z≤n))

  raw97 : List ℕ
  raw97 = 1 ∷ 3 ∷ 9 ∷ 27 ∷ 81 ∷ 243 ∷ 729 ∷ []

  -- With one extra raw lookahead block, the normalized window is:
  --   01 03 09 27 83 50 29
  normalized97 : normalizeBlocks raw97 ≡ 1 ∷ 3 ∷ 9 ∷ 27 ∷ 83 ∷ 50 ∷ 29 ∷ []
  normalized97 = refl

  traced97-blocks :
    map blockValue (traceReversed (729 ∷ 243 ∷ 81 ∷ 27 ∷ 9 ∷ 3 ∷ 1 ∷ [])) ≡
      normalizeReversed (729 ∷ 243 ∷ 81 ∷ 27 ∷ 9 ∷ 3 ∷ 1 ∷ [])
  traced97-blocks = traceReversedAux-map-blockValue
    (729 ∷ 243 ∷ 81 ∷ 27 ∷ 9 ∷ 3 ∷ 1 ∷ [])
    0
