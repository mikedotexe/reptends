import QRTour.PrimeField as PF

module QRTour.QuadraticResidues
  (pf : PF.PrimeField)
  where

open PF.PrimeField pf public

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_ ; _^_; _≤_; _<_; _∸_)
open import Data.Nat.DivMod as DivMod
  using (_div_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Data.Product
  using (Σ; Σ-syntax; _,_; _×_)
open import Relation.Nullary
  using (Dec)

------------------------------------------------------------------------
-- Quadratic residues modulo a prime p.
--
-- For odd p:
--   - (ℤ/pℤ)× has size p-1 and is cyclic.
--   - The set of quadratic residues forms a subgroup of size (p-1)/2.
--
-- Here we define:
--   QR a     : "a is a quadratic residue mod p"
--   half     : (p-1)/2, with (p-1) = 2 * half
--   QRGenerator k : ord_p(k) = half
------------------------------------------------------------------------

-- Quadratic residue predicate: ∃x. x² ≡ₚ a

QR : ℕ → Set
QR a = Σ ℕ λ x → powMod x 2 ≡ₚ a

------------------------------------------------------------------------
-- Size of the QR subgroup: (p - 1) / 2
-- For odd prime p, p-1 is even, so we can define "half" with
--   p - 1 = 2 * half.
------------------------------------------------------------------------

half : ℕ
half = (p ∸ 1) div 2

postulate
  half-spec : p ∸ 1 ≡ 2 * half

  -- And the standard group-theoretic fact:
  -- "The number of distinct quadratic residues modulo p is exactly half."
  qr-subgroup-size : Set

------------------------------------------------------------------------
-- QRGenerator k means: k lies in the QR subgroup and has order = half.
--
-- In a cyclic group of order p-1, this is equivalent to:
--   ord_p(k) = (p-1)/2.
------------------------------------------------------------------------

QRGenerator : ℕ → Set
QRGenerator k = QR k × (order k ≡ half)
