module Examples.Prime97 where

------------------------------------------------------------------------
-- Concrete instantiation: p = 97, B = 10, m = 2, k = 3
--
-- This is the canonical example demonstrating the QR-tour structure.
-- 10² = 100 ≡ 3 (mod 97), and ord₉₇(3) = 48 = (97-1)/2.
-- So k = 3 generates the quadratic residue subgroup.
------------------------------------------------------------------------

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_; _>_; _∸_; NonZero; z<s; s≤s)
-- open import Data.Nat.Properties if needed later
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

import QRTour.PrimeField as PF
import QRTour.QuadraticResidues as QR
import QRTour.RemainderOrbit as RO

------------------------------------------------------------------------
-- Assumption legend for this example
--
-- Local Agda proofs in this file:
--   p≥2-proof, p>2-proof, p-1-even-proof, k97≡3, r0
--
-- Local Agda theorems imported from QRTour.RemainderOrbit:
--   remainders-are-powers, stride-orbit
--
-- Lean-backed postulates still assumed here:
--   prime-97, k97-is-qr-generator
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The prime field: p = 97
------------------------------------------------------------------------

-- Proof of 2 ≤ 97: by explicit construction
p≥2-proof : 2 ≤ 97
p≥2-proof = s≤s (s≤s z≤n)
  where open import Data.Nat using (z≤n)

-- 97 > 2: by explicit construction
p>2-proof : 97 > 2
p>2-proof = s≤s (s≤s (s≤s z≤n))
  where open import Data.Nat using (z≤n)

-- 97 - 1 = 96 is even: 96 % 2 = 0
-- 96 = 48 * 2, so 96 % 2 = 0 definitionally
open import Data.Nat using (_%_)
p-1-even-proof : (97 ∸ 1) % 2 ≡ 0
p-1-even-proof = refl

postulate
  prime-97  : PF.IsPrime 97

p97-nonzero : NonZero 97
p97-nonzero = _

pf97 : PF.PrimeField
pf97 = record
  { p         = 97
  ; p≥2       = p≥2-proof
  ; prime-p   = prime-97
  ; p>2       = p>2-proof
  ; p-1-even  = p-1-even-proof
  ; p-nonzero = p97-nonzero
  }

------------------------------------------------------------------------
-- Open the modules (careful not to re-export duplicates)
------------------------------------------------------------------------

-- Open PrimeField for ≡ₚ, powMod, order, etc.
open PF.PrimeField pf97

-- Open QR for QR, QRGenerator, half (but not the re-exported PrimeField stuff)
open QR pf97 hiding (_≡ₚ_; powMod; order; p; p≥2; prime-p; p-nonzero)

------------------------------------------------------------------------
-- The base-stride parameters: B = 10, m = 2
------------------------------------------------------------------------

-- Open RemainderOrbit for BaseStride, remainder, qr-tour-cover
open RO pf97 hiding (_≡ₚ_; powMod; order; p; p≥2; prime-p; p-nonzero)

-- Placeholder types for coprimality and evenness assumptions
-- These are structural placeholders; the actual properties aren't used in proofs
10-coprime-97 : Set
10-coprime-97 = ⊤
  where open import Data.Unit using (⊤)

2-is-even : Set
2-is-even = ⊤
  where open import Data.Unit using (⊤)

bs97 : BaseStride
bs97 = record
  { B         = 10
  ; B-coprime = 10-coprime-97
  ; m         = 2
  ; m-even    = 2-is-even
  }

------------------------------------------------------------------------
-- The key values for p = 97
--
--   k = 10² mod 97 = 100 mod 97 = 3
--   half = (97-1)/2 = 48
--   ord₉₇(3) = 48
------------------------------------------------------------------------

k97 : ℕ
k97 = BaseStride.k bs97  -- Should compute to 3

-- k97 = powMod 10 2 = toℕ ((10²) mod 97) = toℕ (100 mod 97) = 3
-- This is definitionally equal by computation
k97≡3 : k97 ≡ 3
k97≡3 = refl

-- The key property: k = 3 generates the QR subgroup
postulate
  k97-is-qr-generator : QRGenerator k97

------------------------------------------------------------------------
-- Witness the remainder orbit
--
-- r[0] = 1
-- r[2] = 10² mod 97 = 3
-- r[4] = 10⁴ mod 97 = 9
-- r[6] = 10⁶ mod 97 = 27
-- ...
-- r[2j] = 3^j mod 97
--
-- As j goes from 0 to 47, this hits all 48 quadratic residues.
------------------------------------------------------------------------

r : ℕ → ℕ
r = remainder bs97

-- r[0] = 1
r0 : r 0 ≡ 1
r0 = refl

-- The stride-2 sequence: r[2j] = k^j mod 97
stride-remainder : ℕ → ℕ
stride-remainder j = r (j * 2)

------------------------------------------------------------------------
-- Applying the QR tour cover theorem
--
-- Since k97-is-qr-generator holds, qr-tour-cover tells us that
-- for every quadratic residue a mod 97, there exists j < 48 such that
-- stride-remainder j ≡ₚ a.
------------------------------------------------------------------------

open import Data.Product using (Σ-syntax; _×_)

qr-tour-97 : ∀ a → QR a →
  Σ-syntax ℕ (λ j → (j < half) × (stride-remainder j ≡ₚ a))
qr-tour-97 = qr-tour-cover bs97 k97-is-qr-generator
