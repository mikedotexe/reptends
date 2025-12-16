import QRTour.PrimeField as PF

module QRTour.QuadraticResidues
  (pf : PF.PrimeField)
  where

open PF.PrimeField pf public

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_ ; _^_; _≤_; _<_; _∸_)
open import Data.Nat.DivMod as DivMod
  using (_div_; _%_; m≡m%n+[m/n]*n)
open import Data.Nat.Properties
  using (+-identityˡ; *-comm)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
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

-- Proof: By division algorithm, n = n%2 + (n/2)*2.
-- Since p-1-even says (p ∸ 1) % 2 ≡ 0, we get:
-- p ∸ 1 = 0 + half * 2 = 2 * half
half-spec : p ∸ 1 ≡ 2 * half
half-spec = goal
  where
    n = p ∸ 1
    -- Division algorithm: n = n%2 + (n/2)*2
    div-alg : n ≡ n % 2 + (n div 2) * 2
    div-alg = m≡m%n+[m/n]*n n 2
    -- p-1-even gives us n % 2 ≡ 0
    -- Substitute into division algorithm
    step1 : n ≡ 0 + half * 2
    step1 = subst (λ r → n ≡ r + half * 2) p-1-even div-alg
    -- 0 + x = x
    step2 : 0 + half * 2 ≡ half * 2
    step2 = +-identityˡ (half * 2)
    -- x * 2 = 2 * x
    step3 : half * 2 ≡ 2 * half
    step3 = *-comm half 2
    goal : p ∸ 1 ≡ 2 * half
    goal = trans step1 (trans step2 step3)

-- And the standard group-theoretic fact:
-- "The number of distinct quadratic residues modulo p is exactly half."
-- This is a placeholder type; the actual cardinality proof would require
-- formalizing finite sets and bijections.
qr-subgroup-size : Set
qr-subgroup-size = Σ ℕ λ count → count ≡ half

------------------------------------------------------------------------
-- QRGenerator k means: k lies in the QR subgroup and has order = half.
--
-- In a cyclic group of order p-1, this is equivalent to:
--   ord_p(k) = (p-1)/2.
------------------------------------------------------------------------

QRGenerator : ℕ → Set
QRGenerator k = QR k × (order k ≡ half)
