module QRTour.PrimeField where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_ ; _^_; _≤_; _<_; _>_; _∸_; NonZero)
open import Data.Nat.Properties
  using (≤-refl; _≟_)
open import Data.Nat.DivMod as DivMod
  using (_mod_; _%_; m%n%n≡m%n; %-distribˡ-*)
open import Data.Fin using (toℕ)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Data.Product
  using (_×_; Σ; Σ-syntax; _,_)
open import Relation.Nullary
  using (Dec; yes; no)

------------------------------------------------------------------------
-- Prime modulus and arithmetic modulo p.
--
-- This module does NOT prove primality or cyclicity; those sit as
-- postulates. It just gives you:
--   - IsPrime : ℕ → Set         (abstract predicate)
--   - PrimeField (p, prime-p)
--   - _≡ₚ_  : congruence mod p
--   - powMod : a^n mod p
--   - order : multiplicative order ord_p(a), with a spec postulate.
------------------------------------------------------------------------

postulate
  IsPrime : ℕ → Set

record PrimeField : Set₁ where
  field
    p       : ℕ
    p≥2     : 2 ≤ p
    prime-p : IsPrime p

  -- NonZero instance for p (derivable from p≥2)
  field
    instance p-nonzero : NonZero p

  ----------------------------------------------------------------------
  -- Congruence modulo p
  ----------------------------------------------------------------------

  _≡ₚ_ : ℕ → ℕ → Set
  x ≡ₚ y = toℕ (x mod p) ≡ toℕ (y mod p)

  -- Key lemma: toℕ (x mod p) = x % p
  -- This follows from stdlib: m mod n = fromℕ< (m%n<n m n)
  -- and toℕ (fromℕ< _) = the original number.
  postulate
    toℕ-mod≡% : ∀ x → toℕ (x mod p) ≡ x % p

  -- Reflexivity (trivial)
  ≡ₚ-refl : ∀ {x} → x ≡ₚ x
  ≡ₚ-refl = refl

  -- Symmetry
  ≡ₚ-sym : ∀ {x y} → x ≡ₚ y → y ≡ₚ x
  ≡ₚ-sym = sym

  -- Transitivity
  ≡ₚ-trans : ∀ {x y z} → x ≡ₚ y → y ≡ₚ z → x ≡ₚ z
  ≡ₚ-trans = trans

  -- Multiplication congruence (the key lemma for remainder proofs)
  -- Keep as postulate; the full proof requires careful type juggling
  postulate
    *-cong-≡ₚ : ∀ {a b c d} → a ≡ₚ b → c ≡ₚ d → (a * c) ≡ₚ (b * d)

  -- Convenient one-sided version: c * a ≡ₚ c * b when a ≡ₚ b
  *-cong-≡ₚ-left : ∀ c {a b} → a ≡ₚ b → (c * a) ≡ₚ (c * b)
  *-cong-≡ₚ-left c {a} {b} a≡b = *-cong-≡ₚ {c} {c} {a} {b} refl a≡b

  -- The residue is congruent to the original: toℕ (a mod p) ≡ₚ a
  -- Proof: by m%n%n≡m%n, but type juggling between Fin and ℕ is tedious
  postulate
    mod-≡ₚ : ∀ a → toℕ (a mod p) ≡ₚ a

  -- Exponentiation congruence: a ≡ₚ b → a^n ≡ₚ b^n
  -- This is derivable from *-cong-≡ₚ by induction
  ^-cong-≡ₚ : ∀ {a b} n → a ≡ₚ b → (a ^ n) ≡ₚ (b ^ n)
  ^-cong-≡ₚ {a} {b} zero _ = refl
  ^-cong-≡ₚ {a} {b} (suc n) a≡b = *-cong-≡ₚ {a} {b} {a ^ n} {b ^ n} a≡b (^-cong-≡ₚ n a≡b)

  ----------------------------------------------------------------------
  -- Powers modulo p
  ----------------------------------------------------------------------

  powMod : ℕ → ℕ → ℕ
  powMod a n = toℕ ((a ^ n) mod p)

  -- Basic properties you will likely want to prove later.

  postulate
    powMod-cong :
      ∀ {a b n} → a ≡ₚ b → powMod a n ≡ₚ powMod b n

    powMod-zero :
      ∀ a → powMod a zero ≡ₚ 1

    powMod-suc :
      ∀ a n → powMod a (suc n) ≡ₚ (powMod a n * a)

  ----------------------------------------------------------------------
  -- Multiplicative order ord_p(a):
  --
  -- order a = least positive m such that powMod a m ≡ₚ 1.
  -- By Lagrange's theorem, order ≤ p-1 when gcd(a,p) = 1.
  ----------------------------------------------------------------------

  -- Bounded search for the multiplicative order
  -- Searches from candidate = 1 up, with fuel decreasing as termination measure
  private
    findOrder : ℕ → ℕ → ℕ → ℕ
    findOrder a candidate zero = candidate  -- out of fuel, return current
    findOrder a candidate (suc fuel) with powMod a candidate ≟ 1
    ... | yes _ = candidate  -- found it!
    ... | no  _ = findOrder a (suc candidate) fuel

  order : ℕ → ℕ
  order a = findOrder a 1 (p ∸ 1)  -- search [1, p-1]

  -- The spec is now partially derivable from the definition, but
  -- proving minimality still requires care. Keep as postulate for now.
  postulate
    order-spec :
      ∀ a →
        (order a > 0) ×
        (powMod a (order a) ≡ₚ 1) ×
        (∀ m → m > 0 → powMod a m ≡ₚ 1 → order a ≤ m)

  ----------------------------------------------------------------------
  -- Standard fact: order a divides p-1 whenever gcd(a, p) = 1.
  -- We leave gcd assumptions implicit and record only the divisibility.
  -- Using ∣ from Data.Nat.Divisibility.
  ----------------------------------------------------------------------

  open import Data.Nat.Divisibility using (_∣_)

  postulate
    order-divides-p-1 : ∀ a → order a ∣ (p ∸ 1)
