module Examples.Composite96 where

------------------------------------------------------------------------
-- Composite example: N = 96, base B = 10
--
-- This demonstrates that GeometricStack is purely arithmetic and works
-- for ANY modulus, not just primes. The QR/coset structure requires
-- primes, but the skeleton layer (powers of k) is universal.
--
-- For 96 in base 10:
--   10¹ mod 96 = 10
--   10² mod 96 = 4   ← nice small k!
--   10³ mod 96 = 40
--
-- Using mode m = 2 (2-digit blocks), k = 4.
-- The skeleton shows powers of 4: 1, 4, 16, 64, 256→64 mod 96, ...
------------------------------------------------------------------------

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_; _>_; _∸_; s≤s; z≤n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

import GeometricStack.Family as Fam
import GeometricStack.Capacity as Cap
import GeometricStack.Positional as Pos

------------------------------------------------------------------------
-- Assumption legend for this example
--
-- This example is fully local to GeometricStack. It uses no Lean-backed
-- postulates; the point is to show that the geometric skeleton layer is
-- meaningful even before any prime-field semantics are added.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Family: base = 10, k = 4 (from 10² mod 96)
--
-- This is the geometric skeleton: a[i] = 4^i
-- Word capacities: B n = 10^n
------------------------------------------------------------------------

-- Proof that 2 ≤ 10
base≥2-proof : 2 ≤ 10
base≥2-proof = s≤s (s≤s z≤n)

-- Proof that 1 ≤ 4
k≥1-proof : 1 ≤ 4
k≥1-proof = s≤s z≤n

-- Proof that 4 > 1
k>1-proof : 4 > 1
k>1-proof = s≤s (s≤s z≤n)

-- The geometric family: powers of 4 in base 10
family96 : Fam.Family
family96 = record
  { base   = 10
  ; k      = 4
  ; base≥2 = base≥2-proof
  ; k≥1    = k≥1-proof
  ; k>1    = k>1-proof
  }

------------------------------------------------------------------------
-- Open the modules parameterized by our family
------------------------------------------------------------------------

open Fam.Family family96

-- Verify our definitions
k-is-4 : k ≡ 4
k-is-4 = refl

base-is-10 : base ≡ 10
base-is-10 = refl

-- The geometric sequence: a[i] = 4^i
-- a 0 = 1, a 1 = 4, a 2 = 16, a 3 = 64, ...
a0 : a 0 ≡ 1
a0 = refl

a1 : a 1 ≡ 4
a1 = refl

a2 : a 2 ≡ 16
a2 = refl

a3 : a 3 ≡ 64
a3 = refl

-- Word capacities: B n = 10^n
-- B 0 = 1, B 1 = 10, B 2 = 100, B 3 = 1000, ...
B0 : B 0 ≡ 1
B0 = refl

B1 : B 1 ≡ 10
B1 = refl

B2 : B 2 ≡ 100
B2 = refl

------------------------------------------------------------------------
-- Capacity: finding T where 4^T < 10^n ≤ 4^(T+1)
--
-- For n = 2 (capacity 100):
--   4^0 = 1 < 100
--   4^1 = 4 < 100
--   4^2 = 16 < 100
--   4^3 = 64 < 100
--   4^4 = 256 > 100  ← threshold
--
-- So T_2 = 3: we can fit 4^0, 4^1, 4^2, 4^3 in a 2-digit block
------------------------------------------------------------------------

-- Import capacity module
open Cap family96 hiding (base; k; base≥2; k≥1; a; B)

-- Capacity record is defined in the module
-- T_n satisfies: a i < B n for all i ≤ T_n, and B n ≤ a (suc T_n)

------------------------------------------------------------------------
-- Positional: digit representation in base 10
--
-- This is just standard base-10 representation, nothing prime-specific.
------------------------------------------------------------------------

open Pos family96 hiding (base; k; base≥2; k≥1; a; B)

-- Digit = Fin 10 (digits 0-9)
-- fromDigits converts a list of digits to a number

-- Example: [3, 4] represents 43 (LSB first)
-- fromDigits [3, 4] = 3 + 4 * 10 = 43

------------------------------------------------------------------------
-- The Punchline: Same Structure, Different Semantics
--
-- Prime 97 with k = 3:
--   - Same geometric skeleton: powers of k
--   - QR/NQR coset structure (prime-specific)
--   - Orbit closure after ord_97(10) = 96 steps
--
-- Composite 96 with k = 4:
--   - Same geometric skeleton: powers of k
--   - No QR/NQR structure (not prime)
--   - Orbit closure after ord_96(10) = 4 steps (10^4 ≡ 1 mod 96)
--
-- The GeometricStack layer captures what's common: the skeleton.
-- The QRTour layer adds the prime-specific interpretation.
------------------------------------------------------------------------
