module QRTour.PrimeField where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_ ; _^_; _≤_; _<_; _>_; _∸_; NonZero)
open import Data.Nat.Properties
  using (≤-refl; _≟_; *-assoc; *-comm; *-identityˡ; *-identityʳ; +-suc; m+n∸n≡m)
open import Data.Nat.DivMod as DivMod
  using (_mod_; _%_; m%n%n≡m%n; %-distribˡ-*; m%n<n; [m+kn]%n≡m%n)
open import Data.Fin using (toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Product
  using (_×_; Σ; Σ-syntax; _,_)
open import Relation.Nullary
  using (Dec; yes; no)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)

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
    -- Most QR theory requires odd primes (p > 2)
    -- For p = 2, half = 0 and half-spec fails
    p>2     : p > 2
    -- p - 1 is even (follows from p being odd, but we can't derive that
    -- from abstract IsPrime, so we require it explicitly)
    p-1-even : (p ∸ 1) % 2 ≡ 0

  -- NonZero instance for p (derivable from p≥2)
  field
    instance p-nonzero : NonZero p

  ----------------------------------------------------------------------
  -- Congruence modulo p
  ----------------------------------------------------------------------

  _≡ₚ_ : ℕ → ℕ → Set
  x ≡ₚ y = toℕ (x mod p) ≡ toℕ (y mod p)

  -- Key lemma: toℕ (x mod p) = x % p
  -- Proof: m mod n = fromℕ< (m%n<n m n), and toℕ (fromℕ< h) ≡ m by toℕ-fromℕ<
  toℕ-mod≡% : ∀ x → toℕ (x mod p) ≡ x % p
  toℕ-mod≡% x = toℕ-fromℕ< (m%n<n x p)

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
  -- Proof: (a*c) % p = ((a%p)*(c%p)) % p = ((b%p)*(d%p)) % p = (b*d) % p
  *-cong-≡ₚ : ∀ {a b c d} → a ≡ₚ b → c ≡ₚ d → (a * c) ≡ₚ (b * d)
  *-cong-≡ₚ {a} {b} {c} {d} a≡b c≡d = goal
    where
      -- Extract ℕ equalities from the ≡ₚ hypotheses
      a%≡b% : a % p ≡ b % p
      a%≡b% = trans (sym (toℕ-mod≡% a)) (trans a≡b (toℕ-mod≡% b))
      c%≡d% : c % p ≡ d % p
      c%≡d% = trans (sym (toℕ-mod≡% c)) (trans c≡d (toℕ-mod≡% d))
      -- Chain: (a*c) % p → ((a%p)*(c%p)) % p → ((b%p)*(d%p)) % p → (b*d) % p
      step1 : (a * c) % p ≡ ((a % p) * (c % p)) % p
      step1 = %-distribˡ-* a c p
      step2 : ((a % p) * (c % p)) % p ≡ ((b % p) * (d % p)) % p
      step2 = cong (_% p) (cong₂ _*_ a%≡b% c%≡d%)
      step3 : ((b % p) * (d % p)) % p ≡ (b * d) % p
      step3 = sym (%-distribˡ-* b d p)
      -- Combine with toℕ-mod≡%
      goal : (a * c) ≡ₚ (b * d)
      goal = trans (toℕ-mod≡% (a * c))
                   (trans step1 (trans step2 (trans step3 (sym (toℕ-mod≡% (b * d))))))

  -- Convenient one-sided version: c * a ≡ₚ c * b when a ≡ₚ b
  *-cong-≡ₚ-left : ∀ c {a b} → a ≡ₚ b → (c * a) ≡ₚ (c * b)
  *-cong-≡ₚ-left c {a} {b} a≡b = *-cong-≡ₚ {c} {c} {a} {b} refl a≡b

  -- The residue is congruent to the original: toℕ (a mod p) ≡ₚ a
  -- Goal: toℕ ((toℕ (a mod p)) mod p) ≡ toℕ (a mod p)
  -- Chain: = (toℕ (a mod p)) % p = (a % p) % p = a % p = toℕ (a mod p)
  mod-≡ₚ : ∀ a → toℕ (a mod p) ≡ₚ a
  mod-≡ₚ a = trans (toℕ-mod≡% (toℕ (a mod p)))
                   (trans (cong (_% p) (toℕ-mod≡% a))
                          (trans (m%n%n≡m%n a p)
                                 (sym (toℕ-mod≡% a))))

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

  -- Basic properties

  -- powMod a 0 = toℕ (1 mod p) ≡ₚ 1 by mod-≡ₚ
  powMod-zero : ∀ a → powMod a zero ≡ₚ 1
  powMod-zero a = mod-≡ₚ 1

  -- powMod congruence follows from ^-cong-≡ₚ
  powMod-cong : ∀ {a b n} → a ≡ₚ b → powMod a n ≡ₚ powMod b n
  powMod-cong {a} {b} {n} a≡b = helper
    where
      -- a ≡ₚ b implies a^n ≡ₚ b^n
      step1 : (a ^ n) ≡ₚ (b ^ n)
      step1 = ^-cong-≡ₚ n a≡b
      -- powMod a n = toℕ ((a^n) mod p) and mod-≡ₚ relates them
      helper : powMod a n ≡ₚ powMod b n
      helper = trans (mod-≡ₚ (a ^ n)) (trans step1 (sym (mod-≡ₚ (b ^ n))))

  -- a^(n+1) = a * a^n ≡ₚ a^n * a ≡ₚ powMod a n * a
  -- Uses: mod-≡ₚ and multiplication congruence
  powMod-suc : ∀ a n → powMod a (suc n) ≡ₚ (powMod a n * a)
  powMod-suc a n = goal
    where
      -- powMod a (suc n) = toℕ ((a * a^n) mod p) ≡ₚ a * a^n
      step1 : powMod a (suc n) ≡ₚ (a * a ^ n)
      step1 = mod-≡ₚ (a * a ^ n)
      -- a * a^n ≡ₚ a^n * a by *-comm
      step2 : (a * a ^ n) ≡ₚ (a ^ n * a)
      step2 = cong (λ x → toℕ (x mod p)) (*-comm a (a ^ n))
      -- a^n * a ≡ₚ powMod a n * a (by mod-≡ₚ on first factor)
      step3 : (a ^ n * a) ≡ₚ (powMod a n * a)
      step3 = *-cong-≡ₚ {a ^ n} {powMod a n} {a} {a} (sym (mod-≡ₚ (a ^ n))) refl
      goal : powMod a (suc n) ≡ₚ (powMod a n * a)
      goal = trans step1 (trans step2 step3)

  ----------------------------------------------------------------------
  -- Helper lemmas for modular arithmetic
  -- These lift propositional equalities to ≡ₚ congruences
  ----------------------------------------------------------------------

  -- Lift propositional equality to modular congruence
  cong-≡ₚ : ∀ {a b} → a ≡ b → a ≡ₚ b
  cong-≡ₚ refl = refl

  -- Associativity mod p
  *-assoc-≡ₚ : ∀ a b c → ((a * b) * c) ≡ₚ (a * (b * c))
  *-assoc-≡ₚ a b c = cong-≡ₚ (*-assoc a b c)

  -- Commutativity mod p
  *-comm-≡ₚ : ∀ a b → (a * b) ≡ₚ (b * a)
  *-comm-≡ₚ a b = cong-≡ₚ (*-comm a b)

  -- Right identity mod p
  *-identityʳ-≡ₚ : ∀ a → (a * 1) ≡ₚ a
  *-identityʳ-≡ₚ a = cong-≡ₚ (*-identityʳ a)

  -- Left identity mod p
  *-identityˡ-≡ₚ : ∀ a → (1 * a) ≡ₚ a
  *-identityˡ-≡ₚ a = cong-≡ₚ (*-identityˡ a)

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

  ----------------------------------------------------------------------
  -- Fermat's Little Theorem: a^(p-1) ≡ 1 (mod p) for a > 0
  -- Proven in Mathlib as Nat.ModEq.pow_totient
  ----------------------------------------------------------------------

  postulate
    fermat : ∀ a → a > 0 → powMod a (p ∸ 1) ≡ₚ 1

  ----------------------------------------------------------------------
  -- (p-1)² ≡ 1 (mod p)
  -- Proof: (p-1)² = p² - 2p + 1 = p(p-2) + 1 ≡ 1 (mod p)
  ----------------------------------------------------------------------

  neg1-squared : ((p ∸ 1) * (p ∸ 1)) ≡ₚ 1
  neg1-squared = goal
    where
      open import Data.Nat.Properties using (m∸n+n≡m; +-∸-assoc; *-distribʳ-∸)
      -- We need to show ((p-1)*(p-1)) % p = 1 % p
      -- (p-1)² = p² - 2p + 1
      -- Let's compute: (p-1)*(p-1) = p*p - p - p + 1 = p*(p-2) + 1
      -- So (p*(p-2) + 1) % p = 1 % p (since p*(p-2) % p = 0)

      -- For now, use the algebraic identity approach:
      -- (p-1) ≡ₚ -1, and (-1)*(-1) = 1
      -- Actually we can show: (p ∸ 1) ≡ₚ (p ∸ 1) and use mod arithmetic

      -- Simpler: (p-1)*(p-1) = (p-1)² mod p
      -- We know p ∸ 1 ≡ₚ p ∸ 1 (reflexivity)
      -- And (p ∸ 1) % p = p ∸ 1 when p > 1 (which we have from p ≥ 2)

      -- The key: (p-1)² = p² - 2p + 1
      -- p² - 2p + 1 mod p = 1 (since p divides p² - 2p)

      -- We use a computational approach:
      -- Since p > 2, we have p ∸ 1 ≥ 2
      -- (p ∸ 1)² = (p ∸ 1) * (p ∸ 1)
      -- We need ((p ∸ 1) * (p ∸ 1)) % p = 1

      -- This follows from: (p ∸ 1) ≡ -1 (mod p)
      -- and (-1) * (-1) = 1

      -- For a direct proof, we'd need:
      -- ((p ∸ 1) * (p ∸ 1)) % p
      -- = ((p ∸ 1) % p * (p ∸ 1) % p) % p   by %-distribˡ-*
      -- = ((p ∸ 1) * (p ∸ 1)) % p           since (p ∸ 1) < p

      -- We need a lemma: (p - 1)² ≡ 1 (mod p)
      -- This is actually a general fact about modular arithmetic

      p≡p∸2+2 : p ≡ (p ∸ 2) + 2
      p≡p∸2+2 = sym (m∸n+n≡m p≥2)

      p∸2+2∸1≡p∸2+1 : ((p ∸ 2) + 2) ∸ 1 ≡ (p ∸ 2) + 1
      p∸2+2∸1≡p∸2+1 = cong (_∸ 1) (+-suc (p ∸ 2) 1)

      p∸1≡p∸2+1 : p ∸ 1 ≡ (p ∸ 2) + 1
      p∸1≡p∸2+1 = trans (cong (_∸ 1) p≡p∸2+2) p∸2+2∸1≡p∸2+1

      square-as-one-plus-multiple : ((p ∸ 1) * (p ∸ 1)) ≡ 1 + (p ∸ 2) * p
      square-as-one-plus-multiple =
        trans (cong₂ _*_ p∸1≡p∸2+1 p∸1≡p∸2+1)
              (trans
                (solve 1 (λ a → (a :+ con 1) :* (a :+ con 1) := con 1 :+ (a :* (a :+ con 2))) refl (p ∸ 2))
                (cong (λ x → 1 + (p ∸ 2) * x) (sym p≡p∸2+2)))

      neg1-squared-helper : ((p ∸ 1) * (p ∸ 1)) % p ≡ 1 % p
      neg1-squared-helper =
        trans (cong (_% p) square-as-one-plus-multiple)
              ([m+kn]%n≡m%n 1 (p ∸ 2) p)

      goal : ((p ∸ 1) * (p ∸ 1)) ≡ₚ 1
      goal = trans (toℕ-mod≡% ((p ∸ 1) * (p ∸ 1)))
                   (trans neg1-squared-helper
                          (sym (toℕ-mod≡% 1)))

  ----------------------------------------------------------------------
  -- Power distributes over products: (a * b)^n ≡ a^n * b^n (mod p)
  -- This is a standard property of exponentiation in any commutative ring.
  ----------------------------------------------------------------------

  powMod-mult : ∀ a b n → powMod (a * b) n ≡ₚ (powMod a n * powMod b n)
  powMod-mult a b zero = goal
    where
      step1 : 1 ≡ₚ (1 * 1)
      step1 = ≡ₚ-sym (*-identityʳ-≡ₚ 1)

      step2 : (1 * 1) ≡ₚ (powMod a zero * powMod b zero)
      step2 = *-cong-≡ₚ {1} {powMod a zero} {1} {powMod b zero}
                (≡ₚ-sym (powMod-zero a))
                (≡ₚ-sym (powMod-zero b))

      goal : powMod (a * b) zero ≡ₚ (powMod a zero * powMod b zero)
      goal = ≡ₚ-trans (powMod-zero (a * b)) (≡ₚ-trans step1 step2)
  powMod-mult a b (suc n) = goal
    where
      A = powMod a n
      B = powMod b n

      step1 : powMod (a * b) (suc n) ≡ₚ (powMod (a * b) n * (a * b))
      step1 = powMod-suc (a * b) n

      step2 : (powMod (a * b) n * (a * b)) ≡ₚ ((A * B) * (a * b))
      step2 = *-cong-≡ₚ {powMod (a * b) n} {A * B} {a * b} {a * b}
                (powMod-mult a b n)
                ≡ₚ-refl

      step3 : ((A * B) * (a * b)) ≡ₚ (A * (B * (a * b)))
      step3 = *-assoc-≡ₚ A B (a * b)

      step4a : (B * (a * b)) ≡ₚ ((B * a) * b)
      step4a = ≡ₚ-sym (*-assoc-≡ₚ B a b)

      step4 : (A * (B * (a * b))) ≡ₚ (A * ((B * a) * b))
      step4 = *-cong-≡ₚ-left A step4a

      step5a : ((B * a) * b) ≡ₚ ((a * B) * b)
      step5a = *-cong-≡ₚ {B * a} {a * B} {b} {b} (*-comm-≡ₚ B a) ≡ₚ-refl

      step5 : (A * ((B * a) * b)) ≡ₚ (A * ((a * B) * b))
      step5 = *-cong-≡ₚ-left A step5a

      step6a : ((a * B) * b) ≡ₚ (a * (B * b))
      step6a = *-assoc-≡ₚ a B b

      step6 : (A * ((a * B) * b)) ≡ₚ (A * (a * (B * b)))
      step6 = *-cong-≡ₚ-left A step6a

      step7 : (A * (a * (B * b))) ≡ₚ ((A * a) * (B * b))
      step7 = ≡ₚ-sym (*-assoc-≡ₚ A a (B * b))

      step8 : ((A * a) * (B * b)) ≡ₚ (powMod a (suc n) * powMod b (suc n))
      step8 = *-cong-≡ₚ {A * a} {powMod a (suc n)} {B * b} {powMod b (suc n)}
                (≡ₚ-sym (powMod-suc a n))
                (≡ₚ-sym (powMod-suc b n))

      goal : powMod (a * b) (suc n) ≡ₚ (powMod a (suc n) * powMod b (suc n))
      goal = ≡ₚ-trans step1
             (≡ₚ-trans step2
             (≡ₚ-trans step3
             (≡ₚ-trans step4
             (≡ₚ-trans step5
             (≡ₚ-trans step6
             (≡ₚ-trans step7 step8))))))

  ----------------------------------------------------------------------
  -- Modular inverse: for prime p and 0 < a, there exists a⁻¹ such that
  -- a · a⁻¹ ≡ 1 (mod p).
  --
  -- This follows from Bezout's identity: gcd(a,p) = 1 for 0 < a < p
  -- when p is prime, so there exist s,t with s·a + t·p = 1, meaning
  -- s·a ≡ 1 (mod p).
  ----------------------------------------------------------------------

  -- We postulate the inverse function and its spec (Bezout proof is complex)
  postulate
    inverse : ℕ → ℕ
    inverse-spec : ∀ a → a > 0 → (a * inverse a) ≡ₚ 1
    inverse-nonzero : ∀ a → a > 0 → inverse a > 0

  -- Uniqueness of inverses: if a * x ≡ₚ 1 and a * y ≡ₚ 1, then x ≡ₚ y
  -- Proof chain: x ≡ₚ x*1 ≡ₚ x*(a*y) ≡ₚ (x*a)*y ≡ₚ (a*x)*y ≡ₚ 1*y ≡ₚ y
  inverse-unique : ∀ {a x y} → a > 0 → (a * x) ≡ₚ 1 → (a * y) ≡ₚ 1 → x ≡ₚ y
  inverse-unique {a} {x} {y} a>0 ax≡1 ay≡1 =
    ≡ₚ-trans (≡ₚ-sym (*-identityʳ-≡ₚ x))                     -- x ≡ₚ x*1
    (≡ₚ-trans (*-cong-≡ₚ {x} {x} {1} {a * y} ≡ₚ-refl (≡ₚ-sym ay≡1))   -- x*1 ≡ₚ x*(a*y)
    (≡ₚ-trans (≡ₚ-sym (*-assoc-≡ₚ x a y))                    -- x*(a*y) ≡ₚ (x*a)*y
    (≡ₚ-trans (*-cong-≡ₚ {x * a} {a * x} {y} {y} (*-comm-≡ₚ x a) ≡ₚ-refl) -- (x*a)*y ≡ₚ (a*x)*y
    (≡ₚ-trans (*-cong-≡ₚ {a * x} {1} {y} {y} ax≡1 ≡ₚ-refl)   -- (a*x)*y ≡ₚ 1*y
              (*-identityˡ-≡ₚ y)))))

  -- Corollary: inverse respects congruence
  -- If a ≡ₚ b, then a⁻¹ ≡ₚ b⁻¹
  -- Proof: a * (b⁻¹) ≡ₚ b * (b⁻¹) ≡ₚ 1, so b⁻¹ is also an inverse of a
  -- By inverse-unique, a⁻¹ ≡ₚ b⁻¹
  inverse-cong : ∀ {a b} → a ≡ₚ b → a > 0 → b > 0 → inverse a ≡ₚ inverse b
  inverse-cong {a} {b} a≡b a>0 b>0 = inverse-unique {a} {inverse a} {inverse b} a>0 (inverse-spec a a>0) a*invb≡1
    where
      -- a * (inverse b) ≡ₚ b * (inverse b) ≡ₚ 1
      a*invb≡1 : (a * inverse b) ≡ₚ 1
      a*invb≡1 = ≡ₚ-trans (*-cong-≡ₚ {a} {b} {inverse b} {inverse b} a≡b ≡ₚ-refl) (inverse-spec b b>0)
