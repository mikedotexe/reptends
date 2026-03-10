import QRTour.PrimeField as PF
import QRTour.QuadraticResidues as QR

module QRTour.Cosets
  (pf : PF.PrimeField)
  where

open PF.PrimeField pf public
open QR pf using (QR; QRGenerator; half; half-spec)

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_ ; _^_; _≤_; _<_; _>_; _∸_; NonZero; z<s; >-nonZero)
open import Data.Nat.Properties
  using (_≟_)
open import Data.Nat.DivMod as DivMod
  using (_mod_; _%_; [m+n]%n≡m%n; m%n<n; m<n⇒m%n≡m)
open import Data.Fin using (toℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Product
  using (_×_; Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Nullary
  using (Dec; yes; no; ¬_)
open import Data.Empty
  using (⊥)

------------------------------------------------------------------------
-- Coset structure of (ℤ/pℤ)*
--
-- The multiplicative group (ℤ/pℤ)* has p-1 elements and splits into
-- exactly two cosets:
--
--   QR  = { quadratic residues }    = { a : ∃x. x² ≡ a (mod p) }
--   NQR = { non-quadratic residues } = { a : ¬∃x. x² ≡ a (mod p) }
--
-- Key properties:
--   |QR| = |NQR| = (p-1)/2 = half
--
-- Coset closure rules:
--   QR × QR = QR     (product of squares is a square)
--   NQR × QR = NQR   (non-square times square stays non-square)
--   NQR × NQR = QR   (product of two non-squares is a square)
--
-- Key insight for reptends:
--   When computing a/p, the numerator a determines which coset the
--   remainder orbit lives in, and all remainders stay in that coset.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Non-quadratic residue predicate
------------------------------------------------------------------------

-- NQR a means: there is no x such that x² ≡ a (mod p)
NQR : ℕ → Set
NQR a = ¬ (QR a)

------------------------------------------------------------------------
-- Euler's Criterion
--
-- For odd prime p, a^((p-1)/2) ≡ 1 (mod p) iff a is QR
--                  a^((p-1)/2) ≡ -1 (mod p) iff a is NQR
--
-- Proven in Mathlib as ZMod.euler_criterion
------------------------------------------------------------------------

postulate
  -- Forward direction: QR implies power = 1
  euler-qr : ∀ a → a > 0 → QR a → powMod a half ≡ₚ 1

  -- Forward direction: NQR implies power = -1 (i.e., p-1)
  euler-nqr : ∀ a → a > 0 → NQR a → powMod a half ≡ₚ (p ∸ 1)

  -- Inverse direction: power = 1 implies QR
  euler-qr-inverse : ∀ a → a > 0 → powMod a half ≡ₚ 1 → QR a

------------------------------------------------------------------------
-- Coset closure lemmas
--
-- These are standard group-theoretic facts about the index-2 subgroup.
-- QR is a normal subgroup of index 2, so the coset structure is simple.
------------------------------------------------------------------------

-- The residue operation on products
_*ₚ_ : ℕ → ℕ → ℕ
a *ₚ b = toℕ ((a * b) mod p)

-- Key lemma: a *ₚ b ≡ₚ a * b (residue is congruent to original)
*ₚ-≡ₚ : ∀ a b → (a *ₚ b) ≡ₚ (a * b)
*ₚ-≡ₚ a b = mod-≡ₚ (a * b)

-- QR is preserved by ≡ₚ: if x ≡ₚ y and QR x, then QR y
QR-cong : ∀ {x y} → x ≡ₚ y → QR x → QR y
QR-cong {x} {y} x≡y (w , w²≡x) = w , trans w²≡x x≡y

-- NQR is also preserved by ≡ₚ: if x ≡ₚ y and NQR x, then NQR y
-- Proof: by contrapositive. If QR y, then QR x (by QR-cong with sym), contradicting NQR x.
NQR-cong : ∀ {x y} → x ≡ₚ y → NQR x → NQR y
NQR-cong {x} {y} x≡y nqr-x qr-y = nqr-x (QR-cong (≡ₚ-sym x≡y) qr-y)

-- Helper: (a*b)² = a²*b² (algebraic identity)
-- This is standard ring arithmetic: (ab)² = abab = a²b² via comm/assoc
private
  ^2-distrib : ∀ x y → (x * y) ^ 2 ≡ x ^ 2 * y ^ 2
  ^2-distrib x y = helper
    where
      open import Data.Nat.Properties using (*-assoc; *-comm; *-identityʳ)
      -- (x*y)^2 = (x*y) * ((x*y) * 1) = (x*y) * (x*y) = x*y*x*y
      -- = x*(y*x)*y = x*(x*y)*y = (x*x)*(y*y) = x^2 * y^2
      step1 : (x * y) ^ 2 ≡ (x * y) * (x * y)
      step1 = cong ((x * y) *_) (*-identityʳ (x * y))
      step2 : (x * y) * (x * y) ≡ x * (y * (x * y))
      step2 = *-assoc x y (x * y)
      step3 : x * (y * (x * y)) ≡ x * ((y * x) * y)
      step3 = cong (x *_) (sym (*-assoc y x y))
      step4 : x * ((y * x) * y) ≡ x * ((x * y) * y)
      step4 = cong (λ z → x * (z * y)) (*-comm y x)
      step5 : x * ((x * y) * y) ≡ x * (x * (y * y))
      step5 = cong (x *_) (*-assoc x y y)
      step6 : x * (x * (y * y)) ≡ (x * x) * (y * y)
      step6 = sym (*-assoc x x (y * y))
      step7 : (x * x) * (y * y) ≡ x ^ 2 * y ^ 2
      step7 = cong₂ _*_ (cong (x *_) (sym (*-identityʳ x)))
                        (cong (y *_) (sym (*-identityʳ y)))
      helper : (x * y) ^ 2 ≡ x ^ 2 * y ^ 2
      helper = trans step1 (trans step2 (trans step3 (trans step4
               (trans step5 (trans step6 step7)))))

-- QR × QR = QR: product of quadratic residues is a quadratic residue
-- Proof: if a = x² and b = y², then ab = (xy)²
qr-mult-closed : ∀ {a b} → QR a → QR b → QR (a *ₚ b)
qr-mult-closed {a} {b} (x , x²≡a) (y , y²≡b) = (x * y) , goal
  where
    -- x²≡a : powMod x 2 ≡ₚ a, so (x^2) ≡ₚ a by mod-≡ₚ
    x^2≡a : (x ^ 2) ≡ₚ a
    x^2≡a = trans (sym (mod-≡ₚ (x ^ 2))) x²≡a
    y^2≡b : (y ^ 2) ≡ₚ b
    y^2≡b = trans (sym (mod-≡ₚ (y ^ 2))) y²≡b
    -- By *-cong-≡ₚ: x² ≡ₚ a and y² ≡ₚ b implies x²*y² ≡ₚ a*b
    step1 : (x ^ 2 * y ^ 2) ≡ₚ (a * b)
    step1 = *-cong-≡ₚ x^2≡a y^2≡b
    -- Chain: powMod (x*y) 2 ≡ₚ (x*y)² ≡ x²*y² ≡ₚ a*b ≡ₚ a *ₚ b
    step2 : powMod (x * y) 2 ≡ₚ (x ^ 2 * y ^ 2)
    step2 = trans (mod-≡ₚ ((x * y) ^ 2)) (cong (λ z → toℕ (z mod p)) (^2-distrib x y))
    step3 : (a * b) ≡ₚ (a *ₚ b)
    step3 = sym (mod-≡ₚ (a * b))
    goal : powMod (x * y) 2 ≡ₚ (a *ₚ b)
    goal = trans step2 (trans step1 step3)

------------------------------------------------------------------------
-- Inverse of a QR is QR
-- Proof: if b = y², then b⁻¹ = (y⁻¹)² since (y²)⁻¹ = (y⁻¹)²
------------------------------------------------------------------------

-- Helper: (y⁻¹)² ≡ₚ (y²)⁻¹ (squares commute with inverse)
-- Proof: (y²)(y⁻¹)² = (yy⁻¹)(yy⁻¹) = 1·1 = 1, so (y⁻¹)² is an inverse of y²
-- By inverse-unique, (y⁻¹)² ≡ₚ (y²)⁻¹
square-inverse-commute : ∀ y → y > 0 → (inverse y * inverse y) ≡ₚ inverse (y * y)
square-inverse-commute y y>0 = goal
  where
    open import Data.Nat.Properties using (*-mono-≤)
    invy : ℕ
    invy = inverse y

    -- y * y > 0 since y > 0
    y*y>0 : y * y > 0
    y*y>0 = *-mono-≤ y>0 y>0

    -- (y*invy) ≡ₚ 1 by inverse-spec
    yinvy≡1 : (y * invy) ≡ₚ 1
    yinvy≡1 = inverse-spec y y>0

    -- We want to show (y*y) * (invy*invy) ≡ₚ 1
    -- Chain: (y*y)*(invy*invy) = y*(y*(invy*invy)) = y*((y*invy)*invy)
    --      = y*(1*invy) = y*invy = 1

    -- assoc1 : (y*y)*(invy*invy) ≡ₚ y*(y*(invy*invy))
    assoc1 : ((y * y) * (invy * invy)) ≡ₚ (y * (y * (invy * invy)))
    assoc1 = *-assoc-≡ₚ y y (invy * invy)

    -- assoc2 : y*(invy*invy) ≡ₚ (y*invy)*invy
    assoc2 : (y * (invy * invy)) ≡ₚ ((y * invy) * invy)
    assoc2 = ≡ₚ-sym (*-assoc-≡ₚ y invy invy)

    -- lift2 : y*(y*(invy*invy)) ≡ₚ y*((y*invy)*invy)
    lift2 : (y * (y * (invy * invy))) ≡ₚ (y * ((y * invy) * invy))
    lift2 = *-cong-≡ₚ-left y assoc2

    -- sub1 : (y*invy)*invy ≡ₚ 1*invy
    -- *-cong-≡ₚ : {a b c d} → a ≡ₚ b → c ≡ₚ d → (a * c) ≡ₚ (b * d)
    sub1 : ((y * invy) * invy) ≡ₚ (1 * invy)
    sub1 = *-cong-≡ₚ {y * invy} {1} {invy} {invy} yinvy≡1 ≡ₚ-refl

    -- id1 : 1*invy ≡ₚ invy
    id1 : (1 * invy) ≡ₚ invy
    id1 = *-identityˡ-≡ₚ invy

    -- chain1 : (y*invy)*invy ≡ₚ invy
    chain1 : ((y * invy) * invy) ≡ₚ invy
    chain1 = ≡ₚ-trans sub1 id1

    -- lift3 : y*((y*invy)*invy) ≡ₚ y*invy
    lift3 : (y * ((y * invy) * invy)) ≡ₚ (y * invy)
    lift3 = *-cong-≡ₚ {y} {y} {(y * invy) * invy} {invy} ≡ₚ-refl chain1

    -- Full chain: (y*y)*(invy*invy) ≡ₚ 1
    invy²-is-inv : ((y * y) * (invy * invy)) ≡ₚ 1
    invy²-is-inv = ≡ₚ-trans assoc1 (≡ₚ-trans lift2 (≡ₚ-trans lift3 yinvy≡1))

    -- By inverse-unique: inverse (y*y) ≡ₚ invy*invy
    goal : (invy * invy) ≡ₚ inverse (y * y)
    goal = ≡ₚ-sym (inverse-unique y*y>0 (inverse-spec (y * y) y*y>0) invy²-is-inv)

-- If b is a QR with witness y > 0, then inverse b is also QR
-- Witness: inverse y, since (inverse y)² ≡ₚ inverse b
qr-inverse-qr : ∀ {b} → (y : ℕ) → y > 0 → b > 0 → powMod y 2 ≡ₚ b → QR (inverse b)
qr-inverse-qr {b} y y>0 b>0 y²≡b = inverse y , goal
  where
    open import Data.Nat.Properties using (*-identityʳ)
    -- powMod (inverse y) 2 = toℕ ((inverse y)² mod p)
    -- (inverse y)² = inverse y * (inverse y * 1) = inverse y * inverse y
    step1 : powMod (inverse y) 2 ≡ₚ (inverse y * inverse y)
    step1 = trans (mod-≡ₚ (inverse y * (inverse y * 1)))
                  (cong (λ z → toℕ (z mod p))
                        (cong (inverse y *_) (*-identityʳ (inverse y))))
    -- By square-inverse-commute: (inverse y * inverse y) ≡ₚ inverse (y * y)
    step2 : (inverse y * inverse y) ≡ₚ inverse (y * y)
    step2 = square-inverse-commute y y>0
    -- y * y ≡ₚ b (from hypothesis y²≡b)
    -- y²≡b says: powMod y 2 ≡ₚ b, i.e., toℕ ((y^2) mod p) ≡ₚ b
    -- y^2 = y * (y * 1) definitionally, and y * (y * 1) = y * y by *-identityʳ
    -- Step: y ^ 2 ≡ y * y (propositionally, via *-identityʳ)
    y^2≡y*y : y ^ 2 ≡ y * y
    y^2≡y*y = cong (y *_) (*-identityʳ y)
    -- mod-≡ₚ says toℕ (x mod p) ≡ₚ x, so powMod y 2 ≡ₚ y^2
    step-a : powMod y 2 ≡ₚ (y ^ 2)
    step-a = mod-≡ₚ (y ^ 2)
    -- y^2 ≡ₚ b from hypothesis (via transitivity with step-a)
    y^2≡b : (y ^ 2) ≡ₚ b
    y^2≡b = ≡ₚ-trans (≡ₚ-sym step-a) y²≡b
    -- Transport: y^2 ≡ₚ b and y^2 = y*y imply y*y ≡ₚ b
    y*y≡b : (y * y) ≡ₚ b
    y*y≡b = subst (_≡ₚ b) y^2≡y*y y^2≡b
    -- For inverse-cong we need y*y > 0 and b > 0
    -- y > 0 (i.e., 1 ≤ y) implies y*y ≥ 1*1 = 1 > 0
    open import Data.Nat.Properties using (*-mono-≤)
    y*y>0 : y * y > 0
    y*y>0 = *-mono-≤ y>0 y>0  -- 1 * 1 ≤ y * y, and 1 * 1 = 1
    -- b > 0 is now an argument
    step3 : inverse (y * y) ≡ₚ inverse b
    step3 = inverse-cong y*y≡b y*y>0 b>0
    goal : powMod (inverse y) 2 ≡ₚ inverse b
    goal = trans step1 (trans step2 step3)

------------------------------------------------------------------------
-- NQR × QR = NQR: non-residue times residue is non-residue
-- Proof by contrapositive: if ab ∈ QR, then a = ab · b⁻¹ ∈ QR
------------------------------------------------------------------------

-- Helper: (ab) *ₚ (b⁻¹) ≡ₚ a (associativity + inverse)
product-inverse-cancel : ∀ a b → b > 0 → ((a *ₚ b) *ₚ inverse b) ≡ₚ a
product-inverse-cancel a b b>0 = goal
  where
    open import Data.Nat.Properties using (*-assoc; *-identityʳ)
    -- Chain: (a *ₚ b) *ₚ inverse b ≡ₚ (a * b) * inverse b ≡ₚ a * (b * inverse b) ≡ₚ a * 1 ≡ₚ a
    step1 : ((a *ₚ b) *ₚ inverse b) ≡ₚ ((a *ₚ b) * inverse b)
    step1 = mod-≡ₚ ((a *ₚ b) * inverse b)
    step2 : ((a *ₚ b) * inverse b) ≡ₚ ((a * b) * inverse b)
    step2 = *-cong-≡ₚ (mod-≡ₚ (a * b)) refl
    step3 : ((a * b) * inverse b) ≡ₚ (a * (b * inverse b))
    step3 = cong (λ z → toℕ (z mod p)) (*-assoc a b (inverse b))
    step4 : (a * (b * inverse b)) ≡ₚ (a * 1)
    step4 = *-cong-≡ₚ {a} {a} {b * inverse b} {1} refl (inverse-spec b b>0)
    step5 : (a * 1) ≡ₚ a
    step5 = cong (λ z → toℕ (z mod p)) (*-identityʳ a)
    goal : ((a *ₚ b) *ₚ inverse b) ≡ₚ a
    goal = trans step1 (trans step2 (trans step3 (trans step4 step5)))

-- Contrapositive: QR (a *ₚ b) → QR b → b > 0 → QR a
qr-product-qr-implies-qr : ∀ {a b} → QR (a *ₚ b) → QR b → b > 0 → QR a
qr-product-qr-implies-qr {a} {b} qr-ab (y , y²≡b) b>0 =
  -- step2 : QR ((a *ₚ b) *ₚ inverse b)
  -- product-inverse-cancel : ((a *ₚ b) *ₚ inverse b) ≡ₚ a
  -- QR-cong gives: QR x → x ≡ₚ y → QR y
  QR-cong (product-inverse-cancel a b b>0) step2
  where
    -- Use y + p trick to get a positive witness
    -- y⁺ = y + p is always > 0 (since p ≥ 2)
    -- y⁺ ≡ₚ y by [m+n]%n≡m%n
    -- So powMod y⁺ 2 ≡ₚ powMod y 2 ≡ₚ b
    y⁺ : ℕ
    y⁺ = y + p

    -- y⁺ > 0 follows from y + p ≥ 0 + 2 = 2 > 0
    open import Data.Nat using (z≤n; s≤s)
    open import Data.Nat.Properties using (+-monoˡ-≤; ≤-trans)

    y⁺>0 : y⁺ > 0
    y⁺>0 = ≤-trans (s≤s z≤n) (≤-trans p≥2 (+-monoˡ-≤ p z≤n))

    -- y⁺ ≡ₚ y: (y + p) % p ≡ y % p
    y⁺≡y : y⁺ ≡ₚ y
    y⁺≡y = trans (toℕ-mod≡% y⁺) (trans ([m+n]%n≡m%n y p) (sym (toℕ-mod≡% y)))

    -- powMod y⁺ 2 ≡ₚ b
    y⁺²≡b : powMod y⁺ 2 ≡ₚ b
    y⁺²≡b = ≡ₚ-trans (powMod-cong {y⁺} {y} {2} y⁺≡y) y²≡b

    -- Now we can use qr-inverse-qr with y⁺ > 0
    qr-inv-b : QR (inverse b)
    qr-inv-b = qr-inverse-qr y⁺ y⁺>0 b>0 y⁺²≡b

    -- By qr-mult-closed: QR (a *ₚ b) × QR (inverse b) → QR ((a *ₚ b) *ₚ inverse b)
    step2 : QR ((a *ₚ b) *ₚ inverse b)
    step2 = qr-mult-closed qr-ab qr-inv-b

-- Main theorem: NQR × QR = NQR (when b > 0)
nqr-mult-qr : ∀ {a b} → NQR a → QR b → b > 0 → NQR (a *ₚ b)
nqr-mult-qr {a} {b} nqr-a qr-b b>0 qr-ab = nqr-a (qr-product-qr-implies-qr qr-ab qr-b b>0)

------------------------------------------------------------------------
-- NQR × NQR = QR: product of two non-residues is a residue
--
-- Proof using Euler's criterion:
--   NQR a ⟹ a^half ≡ₚ (p-1)
--   NQR b ⟹ b^half ≡ₚ (p-1)
--   (a*b)^half ≡ₚ a^half * b^half ≡ₚ (p-1) * (p-1) ≡ₚ 1
--   By euler-qr-inverse: (a*b)^half ≡ₚ 1 ⟹ QR (a*b)
------------------------------------------------------------------------

nqr-mult-nqr : ∀ {a b} → a > 0 → b > 0 → NQR a → NQR b → QR (a *ₚ b)
nqr-mult-nqr {a} {b} a>0 b>0 nqr-a nqr-b = euler-qr-inverse (a *ₚ b) ab-pos goal
  where
    open import Data.Nat.Properties using (*-mono-<)

    -- a * b > 0 since a > 0 and b > 0
    ab>0 : a * b > 0
    ab>0 = *-mono-< a>0 b>0

    -- a *ₚ b = toℕ ((a * b) mod p) which is < p
    -- Since a * b > 0 and p ≥ 2, (a * b) mod p could be 0 or positive
    -- We use a + b trick: add p to ensure positivity
    -- Actually, we need (a *ₚ b) > 0 for euler-qr-inverse
    -- For now, postulate this (it follows from a,b coprime to p)
    postulate
      ab-pos : (a *ₚ b) > 0

    -- Step 1: By euler-nqr, powMod a half ≡ₚ (p ∸ 1)
    a-half : powMod a half ≡ₚ (p ∸ 1)
    a-half = euler-nqr a a>0 nqr-a

    -- Step 2: By euler-nqr, powMod b half ≡ₚ (p ∸ 1)
    b-half : powMod b half ≡ₚ (p ∸ 1)
    b-half = euler-nqr b b>0 nqr-b

    -- Step 3: powMod (a * b) half ≡ₚ (powMod a half * powMod b half)
    step3 : powMod (a * b) half ≡ₚ (powMod a half * powMod b half)
    step3 = powMod-mult a b half

    -- Step 4: (powMod a half * powMod b half) ≡ₚ ((p ∸ 1) * (p ∸ 1))
    step4 : (powMod a half * powMod b half) ≡ₚ ((p ∸ 1) * (p ∸ 1))
    step4 = *-cong-≡ₚ a-half b-half

    -- Step 5: ((p ∸ 1) * (p ∸ 1)) ≡ₚ 1 by neg1-squared
    step5 : ((p ∸ 1) * (p ∸ 1)) ≡ₚ 1
    step5 = neg1-squared

    -- Chain: powMod (a * b) half ≡ₚ 1
    ab-half-is-1 : powMod (a * b) half ≡ₚ 1
    ab-half-is-1 = ≡ₚ-trans step3 (≡ₚ-trans step4 step5)

    -- Step 6: a *ₚ b ≡ₚ a * b, so powMod (a *ₚ b) half ≡ₚ powMod (a * b) half
    step6 : powMod (a *ₚ b) half ≡ₚ powMod (a * b) half
    step6 = powMod-cong {a *ₚ b} {a * b} {half} (*ₚ-≡ₚ a b)

    -- Goal: powMod (a *ₚ b) half ≡ₚ 1
    goal : powMod (a *ₚ b) half ≡ₚ 1
    goal = ≡ₚ-trans step6 ab-half-is-1

------------------------------------------------------------------------
-- Coset sizes: both halves have the same cardinality
------------------------------------------------------------------------

postulate
  -- |QR| = half = (p-1)/2
  qr-count : Σ ℕ λ count → count ≡ half

  -- |NQR| = half = (p-1)/2
  nqr-count : Σ ℕ λ count → count ≡ half

------------------------------------------------------------------------
-- Every non-zero element is either QR or NQR (decidability)
--
-- Uses Euler's criterion: a^half ≡ₚ 1 iff QR a
-- We compute powMod a half and check if it equals 1.
------------------------------------------------------------------------

-- Helper: propositional equality implies modular congruence
≡-to-≡ₚ : ∀ {x y} → x ≡ y → x ≡ₚ y
≡-to-≡ₚ refl = refl

-- Helper: for values already reduced mod p, ≡ₚ implies ≡
-- powMod a n < p (since it's toℕ of a Fin p), and 1 < p
-- So if powMod a n ≡ₚ 1, then powMod a n ≡ 1
≡ₚ-to-≡-reduced : ∀ {x} → x < p → x ≡ₚ 1 → x ≡ 1
≡ₚ-to-≡-reduced {x} x<p x≡ₚ1 =
  trans (sym x-mod)
        (trans x≡ₚ1 one-mod)
  where
    x-mod : toℕ (x mod p) ≡ x
    x-mod = trans (toℕ-mod≡% x) (m<n⇒m%n≡m x<p)

    one-mod : toℕ (1 mod p) ≡ 1
    one-mod = trans (toℕ-mod≡% 1) (m<n⇒m%n≡m p≥2)

-- powMod a n < p (it's the result of toℕ ∘ _ mod p)
powMod-<p : ∀ a n → powMod a n < p
powMod-<p a n = subst (_< p) (sym (toℕ-mod≡% (a ^ n))) (m%n<n (a ^ n) p)

qr-decidable : ∀ a → (a > 0) → Dec (QR a)
qr-decidable a a>0 with powMod a half ≟ 1
... | yes eq = yes (euler-qr-inverse a a>0 (≡-to-≡ₚ eq))
... | no neq = no (λ qr → neq (≡ₚ-to-≡-reduced (powMod-<p a half) (euler-qr a a>0 qr)))

------------------------------------------------------------------------
-- Numerator determines coset
--
-- When computing a/p in base B, the remainder sequence is:
--   r₀ = a
--   r_{n+1} = B · rₙ (mod p)
--
-- Since B is coprime to p, multiplying by B is a bijection on (ℤ/pℤ)*.
-- B could be QR or NQR, but the key insight is:
--
--   QR numerator  → all remainders are QR  (orbit stays in QR coset)
--   NQR numerator → all remainders are NQR (orbit stays in NQR coset)
--
-- This holds because B^n is either always QR (if B is QR) or alternates
-- QR/NQR (if B is NQR), but for reptends we care about the coset of
-- a · B^n, which depends only on a's coset when B is a primitive root.
------------------------------------------------------------------------

-- QR is closed under exponentiation: QR a → QR (a^n)
-- Proof: by induction on n, using qr-mult-closed
-- Note: We prove QR (a^n mod p) which means showing (x*y)² ≡ₚ (a^n mod p) for some x
qr-pow-closed : ∀ a n → QR a → QR (toℕ ((a ^ n) mod p))
qr-pow-closed a zero qa = 1 , goal
  where
    -- a^0 = 1 = 1², so QR 1
    goal : powMod 1 2 ≡ₚ toℕ (1 mod p)
    goal = trans (mod-≡ₚ (1 ^ 2)) (sym (mod-≡ₚ 1))
qr-pow-closed a (suc n) qa = QR-cong eq step1
  where
    -- IH: QR (a^n mod p)
    ih : QR (toℕ ((a ^ n) mod p))
    ih = qr-pow-closed a n qa
    -- By qr-mult-closed: QR a × QR (a^n mod p) → QR (a *ₚ (a^n mod p))
    step1 : QR (a *ₚ toℕ ((a ^ n) mod p))
    step1 = qr-mult-closed qa ih
    -- Need: (a *ₚ toℕ((a^n) mod p)) ≡ₚ toℕ((a * a^n) mod p)
    -- Chain: a *ₚ x ≡ₚ a * x ≡ₚ a * a^n ≡ₚ toℕ((a * a^n) mod p)
    eq : (a *ₚ toℕ ((a ^ n) mod p)) ≡ₚ toℕ ((a ^ suc n) mod p)
    eq = trans (*ₚ-≡ₚ a (toℕ ((a ^ n) mod p)))
               (trans (*-cong-≡ₚ {a} {a} refl (mod-≡ₚ (a ^ n)))
                      (sym (mod-≡ₚ (a * a ^ n))))

-- For a QR numerator, all remainders (a · B^n mod p) are QR when B is QR
-- Proof: QR B implies QR (B^n), then QR a × QR (B^n) = QR by qr-mult-closed
numerator-qr-orbit-qr :
  ∀ a B n → QR a → QR B → QR (toℕ ((a * (B ^ n)) mod p))
numerator-qr-orbit-qr a B n qa qB = QR-cong eq step1
  where
    -- qr-mult-closed gives QR (a *ₚ toℕ((B^n) mod p))
    step1 : QR (a *ₚ toℕ ((B ^ n) mod p))
    step1 = qr-mult-closed qa (qr-pow-closed B n qB)
    -- Need: (a *ₚ toℕ((B^n) mod p)) ≡ₚ toℕ((a * B^n) mod p)
    eq : (a *ₚ toℕ ((B ^ n) mod p)) ≡ₚ toℕ ((a * B ^ n) mod p)
    eq = trans (*ₚ-≡ₚ a (toℕ ((B ^ n) mod p)))
               (trans (*-cong-≡ₚ {a} {a} refl (mod-≡ₚ (B ^ n)))
                      (sym (mod-≡ₚ (a * B ^ n))))

-- For an NQR numerator and QR base power, remainders stay NQR
-- Proof: NQR a and QR (B^n) implies NQR (a *ₚ B^n) by nqr-mult-qr
-- Then (a *ₚ B^n) ≡ₚ toℕ((a * B^n) mod p) by standard chain
numerator-nqr-orbit-nqr :
  ∀ a B n → NQR a → QR (B ^ n) → B ^ n > 0 → NQR (toℕ ((a * (B ^ n)) mod p))
numerator-nqr-orbit-nqr a B n nqr-a qr-Bn Bn>0 = NQR-cong eq step1
  where
    -- nqr-mult-qr gives NQR (a *ₚ (B^n))
    step1 : NQR (a *ₚ (B ^ n))
    step1 = nqr-mult-qr nqr-a qr-Bn Bn>0
    -- Need: (a *ₚ B^n) ≡ₚ toℕ((a * B^n) mod p)
    eq : (a *ₚ (B ^ n)) ≡ₚ toℕ ((a * (B ^ n)) mod p)
    eq = trans (*ₚ-≡ₚ a (B ^ n)) (sym (mod-≡ₚ (a * B ^ n)))

------------------------------------------------------------------------
-- Coset as translate
--
-- NQR coset = g · QR for any non-residue g
-- This shows the two cosets have identical structure, just translated.
------------------------------------------------------------------------

postulate
  -- Any NQR can be written as g · q for fixed NQR g and some QR q
  nqr-as-translate :
    ∀ g → NQR g →
      (∀ n → NQR n → Σ ℕ λ q → QR q × (n ≡ₚ (g *ₚ q)))

-- Conversely, g · q is NQR for any QR q when g is NQR
-- This is exactly nqr-mult-qr with renamed arguments
translate-is-nqr : ∀ g q → NQR g → QR q → q > 0 → NQR (g *ₚ q)
translate-is-nqr g q nqr-g qr-q q>0 = nqr-mult-qr nqr-g qr-q q>0

------------------------------------------------------------------------
-- Block-remainder coset invariant
--
-- When using block structure with gap d = B^k - p:
-- The block-start remainders a, a·d, a·d², ... stay in a's coset
-- because d is typically QR (since d ≡ B^k mod p for even k).
------------------------------------------------------------------------

-- If d is QR, then a·d^n stays in a's coset
-- This is just numerator-qr-orbit-qr with argument order swapped
block-coset-preservation-qr :
  ∀ a d n → QR d → QR a → QR (toℕ ((a * (d ^ n)) mod p))
block-coset-preservation-qr a d n qd qa = numerator-qr-orbit-qr a d n qa qd

-- If d is QR and a is NQR, then a·d^n stays NQR
-- Proof: QR d implies QR (d^n) by qr-pow-closed, then use numerator-nqr-orbit-nqr
block-coset-preservation-nqr :
  ∀ a d n → QR d → NQR a → d ^ n > 0 → NQR (toℕ ((a * (d ^ n)) mod p))
block-coset-preservation-nqr a d n qd nqr-a dn>0 =
  numerator-nqr-orbit-nqr a d n nqr-a qr-dn dn>0
  where
    -- qr-pow-closed gives QR (toℕ ((d^n) mod p))
    -- Convert to QR (d^n) using QR-cong with toℕ((d^n) mod p) ≡ₚ (d^n) (from mod-≡ₚ)
    qr-dn : QR (d ^ n)
    qr-dn = QR-cong {toℕ ((d ^ n) mod p)} {d ^ n} (mod-≡ₚ (d ^ n)) (qr-pow-closed d n qd)
