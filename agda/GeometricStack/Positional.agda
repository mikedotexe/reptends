import GeometricStack.Family as Fam

module GeometricStack.Positional
  (F : Fam.Family)
  where

open Fam.Family F public

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_; _>_; NonZero; z<s; s≤s; >-nonZero; s<s⁻¹)
open import Data.Nat.DivMod as DivMod
  using (_div_; _mod_; _%_; _/_; m%n<n; m/n<m; m≡m%n+[m/n]*n; m<n⇒m%n≡m; [m+kn]%n≡m%n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; <-≤-trans; *-comm; +-comm; +-identityʳ; *-identityˡ; *-identityʳ; m^n≢0;
         +-monoˡ-<; *-monoˡ-≤; *-monoʳ-≤; *-distribˡ-+; +-cancelˡ-≡; ≮⇒≥; <⇒≱; m≤m+n; m≤n+m; *-cancelʳ-≡)
open import Data.Fin.Properties
  using (toℕ<n; toℕ-fromℕ<; toℕ-injective)
open import Data.Fin as Fin
  using (Fin; zero; suc; toℕ; fromℕ<)
open import Data.List
  using (List; []; _∷_; [_]; head; tail)
open import Data.Vec as Vec
  using (Vec; []; _∷_)
open import Data.Product
  using (Σ; Σ-syntax; _,_; _×_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst; inspect)
open import Relation.Nullary
  using (Dec; yes; no)
open import Data.Nat.Induction
  using (<-wellFounded)
open import Induction.WellFounded
  using (Acc; acc)

------------------------------------------------------------------------
-- Positional Number System Formalization
--
-- This module formalizes positional (radix-b) representation of natural
-- numbers. For a Family (base, k, base≥2, k≥1), we define:
--
--   Digit     = Fin base             (a single digit: 0 to base-1)
--   Expansion = List Digit           (digit sequence, LSB first)
--
-- Core functions:
--   fromDigits : Expansion → ℕ       (evaluate a digit sequence)
--   toDigits   : ℕ → Expansion       (convert number to digits)
--
-- The connection to Scale's direct/illegal decomposition:
--   direct[i]  = a[i] mod B[n]    ≈  "least significant block" of a[i]
--   illegal[i] = a[i] div B[n]    ≈  "remaining blocks" of a[i]
--
-- When n = 1 (single-digit blocks), direct[i] IS the LSD of a[i].
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Part 1: Digit Types
------------------------------------------------------------------------

-- A single digit in base `base` (bounded: 0 ≤ d < base)
Digit : Set
Digit = Fin base

-- A digit expansion (list of digits, least-significant first)
-- E.g., [3, 2, 1] in base 10 represents 123
Expansion : Set
Expansion = List Digit

-- Fixed-width digit representation (exactly n digits, with leading zeros)
DigitVec : ℕ → Set
DigitVec n = Vec Digit n

------------------------------------------------------------------------
-- Part 2: Evaluation (fromDigits)
--
-- Converts a digit expansion back to the natural number it represents.
-- Follows the stdlib convention: least-significant digit first.
------------------------------------------------------------------------

-- Convert digit expansion to number (LSB first)
fromDigits : Expansion → ℕ
fromDigits []       = 0
fromDigits (d ∷ ds) = toℕ d + fromDigits ds * base

-- Convert fixed-width digit vector to number
fromDigitsVec : {n : ℕ} → DigitVec n → ℕ
fromDigitsVec []       = 0
fromDigitsVec (d ∷ ds) = toℕ d + fromDigitsVec ds * base

------------------------------------------------------------------------
-- Part 3: Basic Properties of fromDigits
------------------------------------------------------------------------

-- Single digit evaluation
fromDigits-singleton : ∀ (d : Digit) → fromDigits [ d ] ≡ toℕ d
fromDigits-singleton d = trans (cong (_+ 0 * base) refl) (+-identityʳ (toℕ d))

-- Each digit is bounded by base
digit-bounded : ∀ (d : Digit) → toℕ d < base
digit-bounded d = toℕ<n d

-- Helper: n + b*n = n*suc(b)
-- Chain: n + b*n = n + n*b = n*1 + n*b = n*(1+b) = n*suc(b)
n+b*n≡n*[1+b] : ∀ n b → n + b * n ≡ n * suc b
n+b*n≡n*[1+b] n b =
  let step1 : n + b * n ≡ n + n * b
      step1 = cong (n +_) (*-comm b n)
      step2 : n + n * b ≡ n * 1 + n * b
      step2 = cong (_+ n * b) (sym (*-identityʳ n))
      step3 : n * 1 + n * b ≡ n * suc b
      step3 = sym (*-distribˡ-+ n 1 b)
  in trans step1 (trans step2 step3)

-- fromDigitsVec result is bounded by B n = base^n
-- Proof: induction on n. Key insight: a + b*n < n*(1+b) ≤ n*m when a<n, b<m
fromDigitsVec-bounded : ∀ {n} (ds : DigitVec n) → fromDigitsVec ds < B n
fromDigitsVec-bounded {zero} [] = s≤s z≤n  -- 0 < 1 = base^0
  where open import Data.Nat using (z≤n)
fromDigitsVec-bounded {suc m} (d ∷ ds) = <-≤-trans step1 step2
  where
    -- IH: fromDigitsVec ds < B m
    ih : fromDigitsVec ds < B m
    ih = fromDigitsVec-bounded ds

    -- Step 1: toℕ d + fromDigitsVec ds * base < base + fromDigitsVec ds * base
    --         (since toℕ d < base)
    step1 : toℕ d + fromDigitsVec ds * base < base + fromDigitsVec ds * base
    step1 = +-monoˡ-< (fromDigitsVec ds * base) (digit-bounded d)

    -- Step 2: base + fromDigitsVec ds * base ≤ base * B m
    --         Rewrite: base + fromDigitsVec ds * base = base * suc (fromDigitsVec ds)
    --         Then: base * suc (fromDigitsVec ds) ≤ base * B m (by IH)
    step2 : base + fromDigitsVec ds * base ≤ base * B m
    step2 = subst (_≤ base * B m) (sym (n+b*n≡n*[1+b] base (fromDigitsVec ds)))
                  (*-monoʳ-≤ base ih)

------------------------------------------------------------------------
-- Part 4: Conversion (toDigits)
--
-- Uses well-founded recursion on n: when base ≥ 2 and n > 0,
-- we have n / base < n, so the recursion terminates.
------------------------------------------------------------------------

-- NonZero instance for base (derived from base≥2)
-- From 2 ≤ base, we get 1 ≤ base (i.e., base > 0), hence NonZero base
base>0 : base > 0
base>0 = ≤-trans (s≤s z≤n) base≥2
  where open import Data.Nat using (z≤n)

base-nonzero : NonZero base
base-nonzero = >-nonZero base>0

-- Helper: extract the least-significant digit
lsd : ℕ → Digit
lsd n = DivMod._mod_ n base ⦃ base-nonzero ⦄

-- Helper: get remaining digits (n / base)
rest : ℕ → ℕ
rest n = DivMod._div_ n base ⦃ base-nonzero ⦄

-- Convert natural number to digit expansion (simple, non-dependent version)
-- Uses well-founded recursion with fuel for simplicity
toDigits′ : ℕ → ℕ → Expansion
toDigits′ zero    n = [ lsd n ]  -- Out of fuel, return single digit
toDigits′ (suc f) zero = []       -- Zero has no digits (or empty list)
toDigits′ (suc f) n with rest n
... | zero = [ lsd n ]            -- Single digit case
... | r    = lsd n ∷ toDigits′ f r

-- Simple toDigits with sufficient fuel
toDigits : ℕ → Expansion
toDigits n = toDigits′ n n

------------------------------------------------------------------------
-- Part 5: Correctness Properties
------------------------------------------------------------------------

-- Helper: toℕ (lsd n) equals n % base
-- lsd n = fromℕ< (m%n<n n base), and toℕ (fromℕ< h) ≡ m by toℕ-fromℕ<
lsd-eq-mod : ∀ n → toℕ (lsd n) ≡ (n % base) ⦃ base-nonzero ⦄
lsd-eq-mod n = toℕ-fromℕ< (m%n<n n base ⦃ base-nonzero ⦄)

-- The fundamental decomposition: n = (n mod base) + (n / base) * base
-- This is a direct application of the division algorithm from stdlib
divmod-spec : ∀ (n : ℕ) → n ≡ toℕ (lsd n) + rest n * base
divmod-spec n = trans (m≡m%n+[m/n]*n n base ⦃ base-nonzero ⦄)
                      (cong (λ x → x + rest n * base) (sym (lsd-eq-mod n)))

-- Correctness: fromDigits (toDigits n) ≡ n
-- Proof strategy: Show toDigits′ f n = n when f is sufficient fuel.
-- The key is that rest n < n when n > 0 and base ≥ 2, so fuel n suffices.

-- Helper: rest n ≤ n (actually rest n < n for n > 0, but ≤ suffices)
private
  rest≤n : ∀ n → rest n ≤ n
  rest≤n n = DivMod.m/n≤m n base ⦃ base-nonzero ⦄

-- Main correctness lemma with fuel tracking
-- When we have at least n fuel, toDigits′ correctly inverts fromDigits

-- Helper: 0 % n = 0 for any NonZero n
-- Proof: By division algorithm, 0 = 0 % n + (0 / n) * n
--        Since 0 / n = 0, we get 0 = 0 % n + 0 = 0 % n
private
  0%n≡0 : ∀ n → .⦃ _ : NonZero n ⦄ → (0 % n) ≡ 0
  0%n≡0 n = sym (trans (m≡m%n+[m/n]*n 0 n)
                       (trans (cong ((0 % n) +_) (cong (_* n) (DivMod.0/n≡0 n)))
                              (+-identityʳ (0 % n))))

  0%base≡0 : (0 % base) ⦃ base-nonzero ⦄ ≡ 0
  0%base≡0 = 0%n≡0 base ⦃ base-nonzero ⦄

fromDigits-toDigits′ : ∀ f n → n ≤ f → fromDigits (toDigits′ f n) ≡ n
fromDigits-toDigits′ zero zero _ =
  -- toDigits′ 0 0 = [lsd 0], fromDigits [lsd 0] = toℕ (lsd 0)
  -- lsd 0 = 0 mod base = 0 (by computation), so toℕ (lsd 0) = 0
  trans (fromDigits-singleton (lsd 0)) (trans (lsd-eq-mod 0) 0%base≡0)
fromDigits-toDigits′ zero (suc n) ()  -- impossible: suc n ≤ 0
fromDigits-toDigits′ (suc f) zero _ = refl  -- toDigits′ (suc f) 0 = [], fromDigits [] = 0
fromDigits-toDigits′ (suc f) (suc n) (s≤s n≤f) with rest (suc n) | inspect rest (suc n)
... | zero | Eq.[ rest≡0 ] =
  -- toDigits′ (suc f) (suc n) = [lsd (suc n)] when rest = 0
  -- fromDigits [lsd (suc n)] = toℕ (lsd (suc n)) = (suc n) % base
  -- When rest = 0, (suc n) / base = 0, so suc n < base, thus (suc n) % base = suc n
  trans (fromDigits-singleton (lsd (suc n)))
        (trans (lsd-eq-mod (suc n))
               (n%b≡n (suc n) rest≡0))
  where
    -- When m/base = 0, by division algorithm: m = m%base + 0*base = m%base
    n%b≡n : ∀ m → rest m ≡ 0 → _%_ m base ⦃ base-nonzero ⦄ ≡ m
    n%b≡n m rest≡0 =
      let eq = m≡m%n+[m/n]*n m base ⦃ base-nonzero ⦄
          m%b = _%_ m base ⦃ base-nonzero ⦄
      in sym (trans eq (trans (cong (m%b +_) (trans (cong (_* base) rest≡0) refl))
                              (+-identityʳ m%b)))
... | suc r | Eq.[ rest≡sr ] =
  -- toDigits′ (suc f) (suc n) = lsd (suc n) ∷ toDigits′ f (suc r)
  -- fromDigits (d ∷ ds) = toℕ d + fromDigits ds * base
  -- IH: fromDigits (toDigits′ f (suc r)) = suc r (need suc r ≤ f)
  -- Goal: toℕ (lsd (suc n)) + (suc r) * base = suc n
  --       = (suc n) % base + (suc n) / base * base = suc n (by divmod)
  trans (cong (toℕ (lsd (suc n)) +_) (cong (_* base) ih))
        (trans (cong (toℕ (lsd (suc n)) +_) (cong (_* base) (sym rest≡sr)))
               (sym (divmod-spec (suc n))))
  where
    -- rest (suc n) = suc r, and (suc n) / base < suc n when base ≥ 2
    -- So suc r < suc n, hence suc r ≤ n ≤ f
    rest<sn : rest (suc n) < suc n
    rest<sn = m/n<m (suc n) base ⦃ _ ⦄ ⦃ base-nonzero ⦄ base≥2
    sr<sn : suc r < suc n
    sr<sn = subst (_< suc n) rest≡sr rest<sn
    -- r < n by s<s⁻¹, and r < n is defined as suc r ≤ n
    sr≤n : suc r ≤ n
    sr≤n = s<s⁻¹ sr<sn
    sr≤f : suc r ≤ f
    sr≤f = ≤-trans sr≤n n≤f
    ih : fromDigits (toDigits′ f (suc r)) ≡ suc r
    ih = fromDigits-toDigits′ f (suc r) sr≤f

-- The main theorem follows from the helper with n as fuel
fromDigits-toDigits : ∀ (n : ℕ) → fromDigits (toDigits n) ≡ n
fromDigits-toDigits n = fromDigits-toDigits′ n n ≤-refl

-- Digit decomposition matches the structure
-- For n > 0, toDigits n = d ∷ ds where d = lsd n
toDigits-lsd : ∀ {n} → n > 0 →
  ∃ λ d → ∃ λ ds → toDigits n ≡ d ∷ ds × toℕ d ≡ toℕ (lsd n)
toDigits-lsd {suc m} _ with rest (suc m) | inspect rest (suc m)
... | zero | Eq.[ eq ] = lsd (suc m) , [] , refl , refl
... | suc r | Eq.[ eq ] = lsd (suc m) , toDigits′ m (suc r) , refl , refl

------------------------------------------------------------------------
-- Part 6: Uniqueness (up to normalization)
------------------------------------------------------------------------

-- A normalized expansion has no trailing zeros (except for 0 itself)
-- [] represents 0; non-empty lists must have nonzero most-significant digit
-- In LSB-first notation, this means the LAST element must be nonzero
data Normalized : Expansion → Set where
  norm-empty : Normalized []
  norm-single : ∀ d → toℕ d > 0 → Normalized [ d ]  -- single nonzero digit
  norm-cons : ∀ d ds → Normalized ds →
              fromDigits ds > 0 →  -- tail is nonzero
              Normalized (d ∷ ds)

-- Uniqueness: two normalized expansions with the same value are equal
-- Helper: fromDigits (d ∷ ds) where fromDigits ds > 0 is at least base
private
  open import Data.Nat using (z≤n; _≥_)
  open import Data.Empty using (⊥-elim)

  fromDigits-cons-≥base : ∀ d ds → fromDigits ds > 0 → fromDigits (d ∷ ds) ≥ base
  fromDigits-cons-≥base d ds ds>0 =
    ≤-trans step1 (m≤n+m (fromDigits ds * base) (toℕ d))
    where
      -- ds>0 : fromDigits ds ≥ 1
      -- fromDigits ds * base ≥ 1 * base = base
      -- Using *-monoˡ-≤ : n → (x ≤ y) → (x * n ≤ y * n)
      step1′ : 1 * base ≤ fromDigits ds * base
      step1′ = *-monoˡ-≤ base {1} {fromDigits ds} ds>0
      step1 : base ≤ fromDigits ds * base
      step1 = subst (_≤ fromDigits ds * base) (*-identityˡ base) step1′

  -- If toℕ d₁ + x = toℕ d₂ + y where x = ds₁ * base, y = ds₂ * base,
  -- and both d₁, d₂ are digits (< base), then d₁ = d₂ and x = y
  -- Proof: take mod base of both sides
  digit-eq-from-sum : ∀ (d₁ d₂ : Digit) (x y : ℕ) →
    toℕ d₁ + x * base ≡ toℕ d₂ + y * base →
    toℕ d₁ ≡ toℕ d₂
  digit-eq-from-sum d₁ d₂ x y eq =
    let
      -- toℕ d₁ < base, so toℕ d₁ % base = toℕ d₁
      d₁%b : (toℕ d₁ % base) ⦃ base-nonzero ⦄ ≡ toℕ d₁
      d₁%b = m<n⇒m%n≡m ⦃ base-nonzero ⦄ (digit-bounded d₁)
      -- toℕ d₂ < base, so toℕ d₂ % base = toℕ d₂
      d₂%b : (toℕ d₂ % base) ⦃ base-nonzero ⦄ ≡ toℕ d₂
      d₂%b = m<n⇒m%n≡m ⦃ base-nonzero ⦄ (digit-bounded d₂)
      -- (toℕ d₁ + x * base) % base = toℕ d₁ % base
      lhs : ((toℕ d₁ + x * base) % base) ⦃ base-nonzero ⦄ ≡ (toℕ d₁ % base) ⦃ base-nonzero ⦄
      lhs = [m+kn]%n≡m%n (toℕ d₁) x base ⦃ base-nonzero ⦄
      -- (toℕ d₂ + y * base) % base = toℕ d₂ % base
      rhs : ((toℕ d₂ + y * base) % base) ⦃ base-nonzero ⦄ ≡ (toℕ d₂ % base) ⦃ base-nonzero ⦄
      rhs = [m+kn]%n≡m%n (toℕ d₂) y base ⦃ base-nonzero ⦄
      -- eq % base: LHS % base = RHS % base
      eq% : ((toℕ d₁ + x * base) % base) ⦃ base-nonzero ⦄ ≡ ((toℕ d₂ + y * base) % base) ⦃ base-nonzero ⦄
      eq% = cong (λ z → (z % base) ⦃ base-nonzero ⦄) eq
      -- Chain: toℕ d₁ = toℕ d₁ % base = LHS % base = RHS % base = toℕ d₂ % base = toℕ d₂
    in trans (sym d₁%b) (trans (sym lhs) (trans eq% (trans rhs d₂%b)))

  tail-eq-from-sum : ∀ (d₁ d₂ : Digit) (x y : ℕ) →
    toℕ d₁ + x * base ≡ toℕ d₂ + y * base →
    toℕ d₁ ≡ toℕ d₂ →
    x ≡ y
  tail-eq-from-sum d₁ d₂ x y eq d-eq =
    let
      -- From d-eq we can rewrite toℕ d₂ to toℕ d₁ in eq
      eq′ : toℕ d₁ + x * base ≡ toℕ d₁ + y * base
      eq′ = trans eq (cong (_+ y * base) (sym d-eq))
      -- From d₁ = d₂ and eq, we get x * base = y * base
      x*b≡y*b : x * base ≡ y * base
      x*b≡y*b = +-cancelˡ-≡ (toℕ d₁) (x * base) (y * base) eq′
    in *-cancelʳ-≡ x y base ⦃ base-nonzero ⦄ x*b≡y*b

  -- Normalized non-empty singleton has nonzero value
  single-nonzero : ∀ d → toℕ d > 0 → fromDigits [ d ] > 0
  single-nonzero d d>0 = subst (_> 0) (sym (fromDigits-singleton d)) d>0

  -- Normalized cons has positive value (already in constructor via fromDigits ds > 0)
  cons-nonzero : ∀ d ds → fromDigits ds > 0 → fromDigits (d ∷ ds) > 0
  cons-nonzero d ds ds>0 = ≤-trans base>0 (fromDigits-cons-≥base d ds ds>0)

  -- Single digit has value < base
  single-<-base : ∀ d → fromDigits [ d ] < base
  single-<-base d = subst (_< base) (sym (fromDigits-singleton d)) (digit-bounded d)

  -- Helper for impossible cases
  0≥1-impossible : 0 ≥ 1 → ∀ {A : Set} → A
  0≥1-impossible ()

  0≥base-impossible : 0 ≥ base → ∀ {A : Set} → A
  0≥base-impossible h with () ← ≤-trans base≥2 h

-- Main uniqueness theorem
toDigits-unique : ∀ {ds₁ ds₂ : Expansion} →
  fromDigits ds₁ ≡ fromDigits ds₂ →
  Normalized ds₁ → Normalized ds₂ →
  ds₁ ≡ ds₂
toDigits-unique {[]} {[]} _ _ _ = refl
toDigits-unique {[]} {d ∷ []} eq _ (norm-single .d d>0) =
  -- fromDigits [] = 0, fromDigits [d] = toℕ d > 0, contradiction
  0≥1-impossible (subst (_≥ 1) (sym (trans eq (fromDigits-singleton d))) d>0)
toDigits-unique {[]} {d ∷ ds@(_ ∷ _)} eq _ (norm-cons .d .ds norm-ds ds>0) =
  -- fromDigits [] = 0, fromDigits (d ∷ ds) ≥ base > 0, contradiction
  0≥base-impossible (subst (_≥ base) (sym eq) (fromDigits-cons-≥base d ds ds>0))
toDigits-unique {d ∷ []} {[]} eq (norm-single .d d>0) _ =
  sym (toDigits-unique {[]} {d ∷ []} (sym eq) norm-empty (norm-single d d>0))
toDigits-unique {d ∷ ds@(_ ∷ _)} {[]} eq (norm-cons .d .ds norm-ds ds>0) _ =
  sym (toDigits-unique {[]} {d ∷ ds} (sym eq) norm-empty (norm-cons d ds norm-ds ds>0))
toDigits-unique {d₁ ∷ []} {d₂ ∷ []} eq (norm-single .d₁ _) (norm-single .d₂ _) =
  -- Both singletons: fromDigits [d₁] = toℕ d₁ = toℕ d₂ = fromDigits [d₂]
  -- Chain: toℕ d₁ ← fromDigits [d₁] = fromDigits [d₂] → toℕ d₂
  cong [_] (toℕ-injective (trans (sym (fromDigits-singleton d₁)) (trans eq (fromDigits-singleton d₂))))
toDigits-unique {d₁ ∷ []} {d₂ ∷ ds₂@(_ ∷ _)} eq (norm-single .d₁ _) (norm-cons .d₂ .ds₂ _ ds₂>0) =
  -- fromDigits [d₁] < base, fromDigits (d₂ ∷ ds₂) ≥ base, contradiction
  ⊥-elim (<⇒≱ (single-<-base d₁) (subst (_≥ base) (sym eq) (fromDigits-cons-≥base d₂ ds₂ ds₂>0)))
toDigits-unique {d₁ ∷ ds₁@(_ ∷ _)} {d₂ ∷ []} eq (norm-cons .d₁ .ds₁ norm-ds₁ ds₁>0) (norm-single .d₂ d₂>0) =
  sym (toDigits-unique {d₂ ∷ []} {d₁ ∷ ds₁} (sym eq) (norm-single d₂ d₂>0) (norm-cons d₁ ds₁ norm-ds₁ ds₁>0))
toDigits-unique {d₁ ∷ ds₁@(_ ∷ _)} {d₂ ∷ ds₂@(_ ∷ _)} eq
                (norm-cons .d₁ .ds₁ norm-ds₁ ds₁>0) (norm-cons .d₂ .ds₂ norm-ds₂ ds₂>0) =
  -- Extract: toℕ d₁ + fromDigits ds₁ * base = toℕ d₂ + fromDigits ds₂ * base
  cong₂ _∷_ (toℕ-injective d-eq) ds₁≡ds₂
  where
    fd₁ = fromDigits ds₁
    fd₂ = fromDigits ds₂
    d-eq : toℕ d₁ ≡ toℕ d₂
    d-eq = digit-eq-from-sum d₁ d₂ fd₁ fd₂ eq
    ds-eq : fd₁ ≡ fd₂
    ds-eq = tail-eq-from-sum d₁ d₂ fd₁ fd₂ eq d-eq
    -- Recurse
    ds₁≡ds₂ : ds₁ ≡ ds₂
    ds₁≡ds₂ = toDigits-unique {ds₁} {ds₂} ds-eq norm-ds₁ norm-ds₂

------------------------------------------------------------------------
-- Part 7: Connection to Scale Decomposition
--
-- When viewing a[i] = k^i at scale n (word size B[n] = base^n),
-- Scale.direct and Scale.illegal correspond to extracting digit blocks.
--
-- For n = 1 (single digits):
--   direct[i] = a[i] mod base = LSD of a[i]
--   illegal[i] = a[i] / base = rest of a[i]
------------------------------------------------------------------------

module ScaleConnection where
  -- Connection: direct at n=1 equals the least significant digit
  -- Both sides are literally toℕ (a i mod base)
  direct-is-lsd : ∀ i →
    toℕ (DivMod._mod_ (a i) base ⦃ base-nonzero ⦄) ≡ toℕ (lsd (a i))
  direct-is-lsd i = refl

  -- The Scale decomposition a[i] = illegal[i] * base + direct[i]
  -- is exactly the positional digit extraction step
  -- Note: divmod-spec gives a i ≡ toℕ (lsd (a i)) + rest (a i) * base
  -- We need to reorder with +-comm to get the expected form
  scale-is-digit-step : ∀ i →
    a i ≡ (DivMod._div_ (a i) base ⦃ base-nonzero ⦄) * base
        + toℕ (DivMod._mod_ (a i) base ⦃ base-nonzero ⦄)
  scale-is-digit-step i = trans (divmod-spec (a i))
                                (+-comm (toℕ (lsd (a i))) (rest (a i) * base))

------------------------------------------------------------------------
-- Part 8: Multi-digit blocks
--
-- For n > 1, we can view a[i] as having "blocks" of n digits each.
-- This connects to the reptend analysis where blocks are k^0, k^1, ...
------------------------------------------------------------------------

-- NonZero instance for B n (base^n > 0 when base ≥ 2)
-- Uses m^n≢0 from stdlib: NonZero base → NonZero (base ^ n)
Bn-nonzero : ∀ n → NonZero (B n)
Bn-nonzero n = m^n≢0 base n ⦃ base-nonzero ⦄

-- Extract an n-digit block (the low-order n digits as a number)
block : (n : ℕ) → ℕ → ℕ
block n x = toℕ (DivMod._mod_ x (B n) ⦃ Bn-nonzero n ⦄)

-- The block is bounded by B n
-- block n x = toℕ (x mod B n) : Fin (B n), so toℕ < B n by Fin semantics
block-bounded : ∀ n x → block n x < B n
block-bounded n x = toℕ<n (DivMod._mod_ x (B n) ⦃ Bn-nonzero n ⦄)

-- Block extraction matches Scale.direct when the scale has word-size n
-- This is literally a tautology: both sides are the same expression
block-is-direct : ∀ n i →
  block n (a i) ≡ toℕ (DivMod._mod_ (a i) (B n) ⦃ Bn-nonzero n ⦄)
block-is-direct n i = refl
