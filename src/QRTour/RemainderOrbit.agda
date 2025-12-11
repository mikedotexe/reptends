import QRTour.PrimeField as PF
import QRTour.QuadraticResidues as QR

module QRTour.RemainderOrbit
  (pf : PF.PrimeField)
  where

open PF.PrimeField pf public
open QR pf using (QR; QRGenerator; half)

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_ ; _^_; _≤_; _<_; _∸_)
open import Data.Nat.DivMod as DivMod
  using (_mod_)
open import Data.Fin using (toℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; trans; sym)
open import Data.Nat.Properties
  using (*-comm; ^-*-assoc)
open import Data.Product
  using (Σ; Σ-syntax; _,_; _×_)
open import Relation.Nullary
  using (Dec)

------------------------------------------------------------------------
-- Long-division remainders for 1/p in base B, and their relation to
-- the k-orbit in (ℤ/pℤ)× when B^m ≡ k (mod p).
--
-- Parameters:
--   B        : base (coprime to p; we abstract that condition)
--   m        : stride length (even; we abstract that too)
--   k        : k ≡ B^m (mod p)
--
-- Definitions:
--   r[n]     : remainder after n long-division steps of 1/p in base B
--   powMod   : from PrimeField (a^n mod p)
--
-- Main lemmas (as postulates for now):
--   remainders-are-powers :
--       r[n] ≡ₚ B^n
--   stride-orbit :
--       r[j * m] ≡ₚ powMod k j
--   qr-tour-cover :
--       if QRGenerator k, then { r[j*m] | j = 0..half-1 }
--       hits every quadratic residue exactly once.
------------------------------------------------------------------------

-- Base and stride parameters

record BaseStride : Set₁ where
  field
    B         : ℕ
    B-coprime : Set   -- placeholder for gcd(B, p) = 1

    m         : ℕ
    m-even    : Set   -- placeholder for "m is even"

  ----------------------------------------------------------------------
  -- k = B^m (mod p)
  ----------------------------------------------------------------------

  k : ℕ
  k = powMod B m

  k-def : k ≡ powMod B m
  k-def = refl

------------------------------------------------------------------------
-- Long-division remainder sequence for 1/p in base B:
--
--   r₀ = 1
--   r_{n+1} = (B * r_n) mod p
--
-- In standard decimal long division, r_n is exactly the remainder
-- after n steps; here we only care about the recurrence mod p.
------------------------------------------------------------------------

remainder : (bs : BaseStride) → ℕ → ℕ
remainder bs zero    = 1
remainder bs (suc n) = toℕ (DivMod._mod_ (BaseStride.B bs * remainder bs n) p ⦃ p-nonzero ⦄)

------------------------------------------------------------------------
-- Lemma: r[n] ≡ B^n (mod p)
-- Proof by induction on n.
------------------------------------------------------------------------

remainders-are-powers : ∀ (bs : BaseStride) (n : ℕ) →
    remainder bs n ≡ₚ (BaseStride.B bs ^ n)
remainders-are-powers bs zero = refl  -- 1 mod p ≡ 1 mod p
remainders-are-powers bs (suc n) =
  -- Goal: toℕ ((B * r[n]) mod p) mod p ≡ (B * B^n) mod p
  -- i.e., remainder bs (suc n) ≡ₚ B^(suc n)
  ≡ₚ-trans
    (mod-≡ₚ (B * remainder bs n))     -- toℕ ((B*r[n]) mod p) ≡ₚ B*r[n]
    (*-cong-≡ₚ-left B (IH n))          -- B * r[n] ≡ₚ B * B^n = B^(suc n)
  where
    B = BaseStride.B bs
    IH = remainders-are-powers bs

------------------------------------------------------------------------
-- Stride lemma: when k ≡ B^m (mod p), we have
--
--   r[j*m] ≡ₚ k^j  for all j.
--
-- Proof: r[j*m] ≡ₚ B^(j*m) = (B^m)^j ≡ₚ k^j ≡ₚ powMod k j
------------------------------------------------------------------------

-- Helper: propositional equality implies modular congruence
≡→≡ₚ : ∀ {x y} → x ≡ y → x ≡ₚ y
≡→≡ₚ refl = refl

stride-orbit : ∀ (bs : BaseStride) (j : ℕ) →
    remainder bs (j * BaseStride.m bs) ≡ₚ powMod (BaseStride.k bs) j
stride-orbit bs j =
  ≡ₚ-trans (remainders-are-powers bs (j * m))       -- r[j*m] ≡ₚ B^(j*m)
  (≡ₚ-trans (≡→≡ₚ eq1)                              -- B^(j*m) ≡ₚ (B^m)^j
  (≡ₚ-trans (^-cong-≡ₚ j (≡ₚ-sym (mod-≡ₚ (B ^ m)))) -- (B^m)^j ≡ₚ k^j
  (≡ₚ-sym (mod-≡ₚ (k ^ j)))))                       -- k^j ≡ₚ powMod k j
  where
    B = BaseStride.B bs
    m = BaseStride.m bs
    k = BaseStride.k bs
    -- B^(j*m) = B^(m*j) = (B^m)^j
    eq1 : B ^ (j * m) ≡ (B ^ m) ^ j
    eq1 = trans (cong (B ^_) (*-comm j m)) (sym (^-*-assoc B m j))

------------------------------------------------------------------------
-- QR tour lemma:
--
-- Assume:
--   - bs : BaseStride with B, m, k as above
--   - QRGenerator (k bs)   (ord_p(k) = (p-1)/2)
--
-- Then the stride-m remainder orbit:
--   j ↦ remainder bs (j * m)
--
-- visits every quadratic residue (mod p) exactly once as j runs from
-- 0 to half-1, where half = (p-1)/2 from QR.
--
-- Proof strategy (all steps are standard group theory):
--   1. QRGenerator k ⇒ order k = half
--   2. order k = half ⇒ {k^0, k^1, ..., k^(half-1)} are all distinct
--   3. k is a QR ⇒ all k^j are QRs
--   4. |QR| = half ⇒ {k^j | j < half} = QR (subgroup of size half)
--   5. For any a ∈ QR, ∃j < half. k^j ≡ₚ a
--   6. By stride-orbit: remainder bs (j*m) ≡ₚ k^j ≡ₚ a
------------------------------------------------------------------------

-- Intermediate lemma: QR-generator orbit covers all QRs
-- This is the core group-theoretic fact
postulate
  qr-orbit-exhaustive :
    ∀ k → QRGenerator k →
      (∀ a → QR a → Σ ℕ λ j → (j < half) × (powMod k j ≡ₚ a))

-- Main theorem: stride-m remainders cover all QRs
qr-tour-cover :
    ∀ (bs : BaseStride) →
      QRGenerator (BaseStride.k bs) →
      (∀ a → QR a →
         Σ ℕ λ j →
           (j < half) × (remainder bs (j * BaseStride.m bs) ≡ₚ a))
qr-tour-cover bs qrgen a qr-a with qr-orbit-exhaustive k qrgen a qr-a
  where k = BaseStride.k bs
... | j , j<half , kj≡a = j , j<half , ≡ₚ-trans (stride-orbit bs j) kj≡a
