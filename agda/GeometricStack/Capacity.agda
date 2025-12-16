import GeometricStack.Family as Fam

module GeometricStack.Capacity
  (F : Fam.Family)
  where

open Fam.Family F public

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_ ; _^_; _≤_; _<_; _>_; NonZero; z<s; s≤s; z≤n; >-nonZero; _≤?_)
open import Data.Nat.Properties
  using (^-monoʳ-≤; ≤-trans; ≤-antisym; <⇒≤; ≰⇒>; <-irrefl; ≤-<-trans; m^n>0; <⇒≢;
         ≤-refl; <-transˡ; <-transʳ; +-monoʳ-<; *-monoˡ-≤; n<1+n; ≤-step; +-identityʳ;
         ^-monoˡ-≤; m≤m+n; +-comm; *-monoʳ-≤; <-≤-trans)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary
  using (yes; no; ¬_)

------------------------------------------------------------------------
-- Base-invariant capacity index for the geometric stack a[i] = k^i.
--
-- For each word length n, with capacity B n = base^n, we define a
-- record Capacity n that packages:
--
--   Tₙ       : ℕ
--   powBelow : ∀ i ≤ Tₙ.  a[i] < B n
--   powAbove :            B n ≤ a[Tₙ + 1]
--
-- This is exactly "T = floor(log_k(B))", but phrased arithmetically.
-- It depends only on (base, k) via a[i] and B n. No decimals, no
-- factorization of B n - k, nothing base-specific.
------------------------------------------------------------------------

record Capacity (n : ℕ) : Set where
  field
    Tₙ       : ℕ
    powBelow : ∀ {i} → i ≤ Tₙ → a i < B n
    powAbove : B n ≤ a (suc Tₙ)

------------------------------------------------------------------------
-- Monotonicity of k^i in i (for k ≥ 1), which underlies existence and
-- uniqueness of Tₙ. You can prove this once and reuse everywhere.
------------------------------------------------------------------------

-- NonZero k follows from k≥1
k>0 : k > 0
k>0 = ≤-trans (s≤s z≤n) k≥1

k-nonzero : NonZero k
k-nonzero = >-nonZero k>0

-- Monotonicity of a[i] = k^i: uses ^-monoʳ-≤ from stdlib
a-monotone : ∀ {i j} → i ≤ j → a i ≤ a j
a-monotone {i} {j} i≤j = ^-monoʳ-≤ k ⦃ k-nonzero ⦄ i≤j

------------------------------------------------------------------------
-- Key lemma: 2^m > m for all m
-- We first prove 2^m ≥ suc m (equivalent to 2^m > m) by induction.
------------------------------------------------------------------------
private
  -- Helper: 2^m ≥ 1 for all m
  2^n≥1 : ∀ m → 1 ≤ 2 ^ m
  2^n≥1 zero = ≤-refl  -- 1 ≤ 1
  2^n≥1 (suc m) = ≤-trans (2^n≥1 m) (m≤m+n (2 ^ m) (2 ^ m + 0))

  -- Main lemma: 2^m ≥ suc m (i.e., 2^m > m)
  2^n>n : ∀ m → 2 ^ m > m
  2^n>n zero = s≤s z≤n  -- 1 > 0
  2^n>n (suc m) = goal
    where
      open import Data.Nat.Properties using (+-monoˡ-≤; +-monoʳ-≤)
      -- IH: 2^m ≥ suc m
      ih : suc m ≤ 2 ^ m
      ih = 2^n>n m
      -- 1 ≤ 2^m
      one≤2^m : 1 ≤ 2 ^ m
      one≤2^m = 2^n≥1 m
      -- 2^(suc m) = 2^m + (2^m + 0)
      -- We want: suc (suc m) ≤ 2^m + (2^m + 0)
      -- Step 1: 1 + suc m ≤ 2^m + suc m (since 1 ≤ 2^m, add suc m on right)
      step1 : 1 + suc m ≤ 2 ^ m + suc m
      step1 = +-monoˡ-≤ (suc m) one≤2^m
      -- Step 2: 2^m + suc m ≤ 2^m + 2^m (since suc m ≤ 2^m, add 2^m on left)
      step2 : 2 ^ m + suc m ≤ 2 ^ m + 2 ^ m
      step2 = +-monoʳ-≤ (2 ^ m) ih
      -- 2^m + (2^m + 0) = 2^m + 2^m by +-identityʳ
      eq : 2 ^ m + (2 ^ m + 0) ≡ 2 ^ m + 2 ^ m
      eq = cong (2 ^ m +_) (+-identityʳ (2 ^ m))
      -- Chain them together: 1 + suc m ≤ 2^m + suc m ≤ 2^m + 2^m = 2^(suc m)
      goal : suc (suc m) ≤ 2 ^ suc m
      goal = subst (1 + suc m ≤_) (sym eq) (≤-trans step1 step2)

  -- Since k ≥ 2, k^m ≥ 2^m > m
  k^n>n : ∀ m → k ^ m > m
  k^n>n m = <-≤-trans (2^n>n m) (^-monoˡ-≤ m k>1)

------------------------------------------------------------------------
-- Existence of a capacity index for n ≥ 1.
--
-- For n = 0, B 0 = 1 and a 0 = 1, so a 0 < 1 is impossible.
-- For n ≥ 1, we use bounded search to find T where a T < B n ≤ a (suc T).
--
-- The search works because:
--   - k > 1 implies k^i grows without bound
--   - Eventually k^i will exceed B n = base^n
------------------------------------------------------------------------

-- Bounded search: find T where B n ≤ a (suc T)
-- Fuel ensures termination; decreases each step
private
  findCapacity : (n : ℕ) → (candidate : ℕ) → (fuel : ℕ) → ℕ
  findCapacity n T zero = T  -- out of fuel
  findCapacity n T (suc f) with B n ≤? a (suc T)
  ... | yes _ = T  -- found it
  ... | no  _ = findCapacity n (suc T) f

-- For n ≥ 1, base^n ≥ base ≥ 2 > 1 = k^0
-- So we need T where k^T < base^n ≤ k^(T+1)
-- Since k > 1, this T exists and is bounded by n * log_k(base)
-- We use base^n as fuel (generous upper bound)

-- For the proof, we need additional imports
open import Data.Nat using (_≥_)

-- Key lemma: a 0 = 1 < B n for n > 0
-- a 0 = k^0 = 1
-- B n = base^n ≥ base^1 = base ≥ 2 > 1 for n > 0
-- So 1 < 2 ≤ base ≤ base^n = B n
a0<Bn : ∀ n → n > 0 → a 0 < B n
a0<Bn (suc n) _ = step3
  where
    open import Data.Nat.Properties using (*-monoʳ-≤; *-identityʳ)
    -- a 0 = k^0 = 1
    -- We need 1 < B (suc n) = base^(suc n) = base * base^n
    -- Since base ≥ 2 and base^n ≥ 1, we have base * base^n ≥ 2 * 1 = 2 > 1

    -- base^n ≥ 1 (by m^n>0)
    -- m^n>0 : ∀ m n → .⦃ NonZero m ⦄ → m ^ n > 0
    instance
      base-nonzero : NonZero base
      base-nonzero = >-nonZero (≤-trans (s≤s z≤n) base≥2)
    base^n≥1 : base ^ n ≥ 1
    base^n≥1 = m^n>0 base n

    -- B (suc n) = base * base^n ≥ base * 1 = base
    step1 : B (suc n) ≥ base * 1
    step1 = *-monoʳ-≤ base base^n≥1

    -- base * 1 = base by *-identityʳ
    step1' : B (suc n) ≥ base
    step1' = subst (B (suc n) ≥_) (*-identityʳ base) step1

    -- 1 < base follows from base ≥ 2, i.e., 2 ≤ base, i.e., suc 1 ≤ base
    one<base : 1 < base
    one<base = ≤-trans (s≤s (s≤s z≤n)) base≥2

    -- 1 < base ≤ B (suc n), so 1 < B (suc n)
    step3 : 1 < B (suc n)
    step3 = <-≤-trans one<base step1'

-- Key lemma: For m ≥ B n, we have a m > B n
-- Because a m = k^m > m ≥ B n (by k^n>n)
a-exceeds-Bn : ∀ n m → B n ≤ m → B n < a m
a-exceeds-Bn n m Bn≤m = ≤-<-trans Bn≤m (k^n>n m)

-- Bounded search with invariant tracking
-- Returns T along with proofs that:
--   (1) All i ≤ T have a i < B n (powBelow)
--   (2) B n ≤ a (suc T) (powAbove)
private
  -- The search state: candidate T, with proof that a T < B n
  record SearchState (n : ℕ) : Set where
    field
      T      : ℕ
      aT<Bn  : a T < B n

  -- Search with fuel, maintaining invariant
  -- inv : ∀ i ≤ T → a i < B n (all candidates so far are below)
  findCapacity′ : ∀ n (fuel : ℕ) (T : ℕ) →
    (inv : ∀ {i} → i ≤ T → a i < B n) →
    (enough : T + fuel ≥ B n) →
    Capacity n
  findCapacity′ n zero T inv enough with B n ≤? a (suc T)
  ... | yes prf = record { Tₙ = T ; powBelow = inv ; powAbove = prf }
  ... | no ¬prf with a-exceeds-Bn n T Bn≤T
    where
      -- enough : T + 0 ≥ B n, i.e., B n ≤ T + 0
      -- +-identityʳ T : T + 0 ≡ T
      -- subst (B n ≤_) gives B n ≤ T
      Bn≤T : B n ≤ T
      Bn≤T = subst (B n ≤_) (+-identityʳ T) enough
  -- T ≥ B n, so a T > B n by a-exceeds-Bn
  -- But inv says a T < B n for T ≤ T (i.e., a T < B n). Contradiction!
  ...   | aT>Bn with <-irrefl refl (≤-<-trans (<⇒≤ aT>Bn) (inv ≤-refl))
  ...     | ()
  findCapacity′ n (suc f) T inv enough with B n ≤? a (suc T)
  ... | yes prf = record { Tₙ = T ; powBelow = inv ; powAbove = prf }
  ... | no ¬prf = findCapacity′ n f (suc T) inv′ enough′
    where
      -- ¬(B n ≤ a (suc T)) means a (suc T) < B n
      -- ≰⇒> : ¬(m ≤ n) → m > n, and m > n = n < m
      asT<Bn : a (suc T) < B n
      asT<Bn = ≰⇒> ¬prf
      -- Extend invariant: for i ≤ suc T, a i < B n
      inv′ : ∀ {i} → i ≤ suc T → a i < B n
      inv′ {i} i≤sT with i ≤? T
        where open import Data.Nat using (_≤?_)
      ... | yes i≤T = inv i≤T
      ... | no ¬i≤T with ≤-antisym i≤sT (≰⇒> ¬i≤T)
      -- i ≤ suc T and ¬(i ≤ T) means i = suc T
      ...   | refl = asT<Bn
      -- Fuel decreases, T increases
      -- enough : T + suc f ≥ B n (i.e., B n ≤ T + suc f)
      -- We need: suc T + f ≥ B n (i.e., B n ≤ suc T + f)
      -- suc T + f = suc (T + f) definitionally
      -- T + suc f = suc (T + f) by +-suc
      -- So we use subst with +-suc
      open import Data.Nat.Properties using (+-suc)
      enough′ : suc T + f ≥ B n
      enough′ = subst (B n ≤_) (+-suc T f) enough

-- Main theorem: capacity exists for n > 0
capacity-exists : ∀ (n : ℕ) → n > 0 → Capacity n
capacity-exists n n>0 = findCapacity′ n (B n) 0 inv₀ enough₀
  where
    -- Initial invariant: a 0 < B n (for n > 0)
    inv₀ : ∀ {i} → i ≤ 0 → a i < B n
    inv₀ {zero} _ = a0<Bn n n>0
    inv₀ {suc i} ()
    -- Initial fuel is enough: 0 + B n = B n ≥ B n
    enough₀ : 0 + B n ≥ B n
    enough₀ = ≤-refl

------------------------------------------------------------------------
-- Uniqueness of the capacity index: if c1 and c2 both satisfy the
-- capacity conditions for the same n, then Tₙ is uniquely determined.
------------------------------------------------------------------------

-- Uniqueness: by antisymmetry. If T₁ < T₂, then a(T₁+1) < B n (by c2.powBelow)
-- but B n ≤ a(T₁+1) (by c1.powAbove). Contradiction. Similarly for T₂ < T₁.
capacity-unique :
    ∀ {n}
      (c1 c2 : Capacity n) →
      Capacity.Tₙ c1 ≡ Capacity.Tₙ c2
capacity-unique {n} c1 c2 = ≤-antisym T₁≤T₂ T₂≤T₁
  where
    open Capacity
    T₁ = Tₙ c1
    T₂ = Tₙ c2

    -- If suc T₁ ≤ T₂, then a(suc T₁) < B n by c2.powBelow
    -- But c1.powAbove says B n ≤ a(suc T₁). Contradiction.
    T₁≤T₂ : T₁ ≤ T₂
    T₁≤T₂ with T₁ ≤? T₂
      where open import Data.Nat using (_≤?_)
    ... | yes p = p
    ... | no ¬p = contradiction
      where
        open import Data.Empty using (⊥-elim)
        -- ¬(T₁ ≤ T₂) means T₂ < T₁ (by ≰⇒>)
        T₂<T₁ : T₂ < T₁
        T₂<T₁ = ≰⇒> ¬p
        -- From suc T₂ ≤ T₁, by c1.powBelow: a(suc T₂) < B n
        step : a (suc T₂) < B n
        step = powBelow c1 T₂<T₁
        -- But c2.powAbove: B n ≤ a(suc T₂)
        -- Combined: B n ≤ a(suc T₂) < B n, so B n < B n. Contradiction!
        contradiction : T₁ ≤ T₂
        contradiction = ⊥-elim (<-irrefl refl (≤-<-trans (powAbove c2) step))

    T₂≤T₁ : T₂ ≤ T₁
    T₂≤T₁ with T₂ ≤? T₁
      where open import Data.Nat using (_≤?_)
    ... | yes p = p
    ... | no ¬p = contradiction
      where
        open import Data.Empty using (⊥-elim)
        T₁<T₂ : T₁ < T₂
        T₁<T₂ = ≰⇒> ¬p
        step : a (suc T₁) < B n
        step = powBelow c2 T₁<T₂
        -- Combined: B n ≤ a(suc T₁) < B n, so B n < B n. Contradiction!
        contradiction : T₂ ≤ T₁
        contradiction = ⊥-elim (<-irrefl refl (≤-<-trans (powAbove c1) step))
