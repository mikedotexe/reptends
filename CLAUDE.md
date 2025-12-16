# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build and Run Commands

### Python (bridge_reptends package)

```bash
# Install the package in development mode
pip install -e .

# Skeleton analysis (works for ANY N, prime or composite)
python -c "from bridge_reptends import print_skeleton_analysis; print_skeleton_analysis(996)"

# Run core analysis demo
python -m bridge_reptends.analysis

# Sweep primes up to N with specific bases
sweep-primes --max 500 --bases 2,7,10,12 --output data/results.csv

# Run pattern analysis
python -m bridge_reptends.patterns

# Educational examples
python -m bridge_reptends.examples.prime_19
python -m bridge_reptends.examples.backwards
python -m bridge_reptends.examples.progression
```

### Agda (Formal Proofs)

```bash
# Run from the agda/ directory (where qr-reptends.agda-lib is located)
cd agda

# Typecheck the main example
agda Examples/Prime97.agda

# Typecheck a specific module
agda QRTour/RemainderOrbit.agda

# The qr-reptends.agda-lib file configures stdlib dependency automatically
```

### Lean 4 (Formal Proofs)

```bash
# Run from the lean/ directory
cd lean

# First time: download Mathlib cache (~5GB)
lake exe cache get

# Build all modules
lake build

# Typecheck a specific module
lake build QRTour.RemainderOrbit

# The Lean version proves what Agda postulates, using Mathlib
```

### Web Visualization (site/)

```bash
cd site
yarn install
yarn dev      # Development server
yarn build    # Production build
```

---

# Bridge Reptends

## The Paradigm Shift

**Contemporary view**: Reptends (repeating decimal expansions) are "base-10 curiosities" - interesting patterns that emerge when you divide.

**Our view**: Reptends are **geometric series** with carry correction.

### The Universal Structure (Any N)

For any N coprime to base B, with k = B mod N:

```
1/N = (1/B) × 1/(1 - k/B) = Σ k^j / B^(j+1)
```

The digit blocks are **powers of k**: 1, k, k², k³, ...

| Layer | What | Universal? |
|-------|------|------------|
| Skeleton | Raw powers k^j | Yes, any N |
| Carry | Overflow correction when k^j ≥ B^m | Yes, any N |
| Closure | Cyclic wrap after ord_N(B) blocks | Yes, any N |

This is the foundation. It works for 1/96, 1/996, 1/9996 just as well as 1/97.

### The Prime Bonus (Coset Structure)

When N is prime, we get additional structure: (ℤ/pℤ)* splits into two cosets:

```
(ℤ/pℤ)* = QR ⊔ NQR
        = {squares} ⊔ {non-squares}
```

This explains:
- **Numerator a** determines which coset the orbit lives in
- All remainders stay in that coset forever
- The **gap d = B^k - p** traverses within the coset
- QR-generators have order exactly (p-1)/2

### Coset Closure Rules (Prime Only)

- QR × QR = QR (product of squares is a square)
- NQR × QR = NQR (non-square times square stays non-square)
- NQR × NQR = QR (product of two non-squares is a square)

### Key Insight

**Primes add structure; they don't create it.** The geometric skeleton exists for any N.
Primes give us the QR/NQR interpretation of that skeleton.

---

## The Canonical Example: 1/97 in Base 10

This walkthrough shows exactly how the coset structure works.

### Setup
- p = 97 (prime)
- Base B = 10
- k = 2 (block width)

### Step 1: Compute the gap d

```
10² = 100 ≡ 3 (mod 97)
d = 3  (the gap: 10² - 97 = 3)
```

### Step 2: Is d a QR-generator?

For d to traverse the entire QR coset:
- The QR coset has size (p-1)/2 = **48**
- d must have multiplicative order exactly 48

Check: ord₉₇(3) = 48 ✓

Since ord₉₇(3) = (p-1)/2, **d=3 generates the QR subgroup**.

### Step 3: Coset membership

1 is a QR (1 = 1²), so 1/97 lives in the **QR coset**.
3 is an NQR, so 3/97 lives in the **NQR coset**.

Both orbits have identical structure—they traverse their respective cosets at the same rate—but they never intersect.

### Step 4: Block structure

Long division of 1/97 produces remainders rₙ ≡ 10ⁿ (mod 97).

Every-other remainder (r₀, r₂, r₄, ...) equals powers of d:
```
r₀  = 10⁰ ≡ 1   = 3⁰
r₂  = 10² ≡ 3   = 3¹
r₄  = 10⁴ ≡ 9   = 3²
r₆  = 10⁶ ≡ 27  = 3³
...
```

Since d=3 generates all 48 quadratic residues, the stride-2 remainders visit every QR exactly once before cycling.

### The Punchline

The "magic" of 1/97's decimal expansion is coset structure:
- The gap d=3 determines how we traverse within the coset
- The numerator determines which coset we're in
- Any base B where B^k - p = 3 for some k would show the same structure

---

## The Algebraic Decomposition: Orbit Weave + Closure Flux

A complementary view: instead of studying remainder sequences, study the reptend *integer* R and its algebraic structure.

### The Key Identity

For modulus M coprime to base B, the reptend integer decomposes:

```
R = W + F

where:
  R = (B^L - 1) / M      (reptend integer)
  W = (B^L - k^L) / M    (orbit weave - finite body)
  F = (k^L - 1) / M      (closure flux - the correction)
  k = B mod M            (bridge residue)
  L = ord_M(B)           (orbit length)
```

### Example: 1/97 in Mode m=2

```
B = 10² = 100
k = 100 mod 97 = 3        (bridge residue)
L = ord₉₇(100) = 48       (orbit length in blocks)

R = (100⁴⁸ - 1) / 97
W = (100⁴⁸ - 3⁴⁸) / 97
F = (3⁴⁸ - 1) / 97

R = W + F ✓
```

### Connection to Coset Structure

- **k = B mod M** is the gap d when M = B^m - d (sweet spot primes)
- **W (weave)** encodes the geometric orbit structure: blocks show powers of k
- **F (flux)** is the "carry correction" that seals the loop
- When k is a **QR-generator**, the weave W traverses the QR subgroup

### Mode Selection and Good Coordinates

The "mode" m (block width) determines k = base^m mod M. The fundamental equation:

```
B = qM + k

where:
  B = base^m     (block base)
  k = B mod M    (bridge residue)
  q = (B - k)/M  (quotient)
```

**"Good coordinates"** = finding m where k is SMALL.

Why small k matters: The reptend is a geometric series with digit blocks = powers of k:
```
1/M = Σ k^j / B^(j+1)    →    blocks are 1, k, k², k³, ...
```

When k is small, the powers stay small longer before overflowing. You can SEE the skeleton.

### The 37 Example (k=1 is perfect!)

| m | B | k = B mod 37 | q |
|---|---|--------------|---|
| 1 | 10 | 10 | 0 |
| 2 | 100 | 26 | 2 |
| **3** | **1000** | **1** | **27** |

At m=3: 1000 = 27×37 + 1, so k=1.

When k=1, the skeleton is constant: 1, 1, 1, 1, ...
So **1/37 = 27/999 = 27/(1000-1) = 0.027027027...**

```python
from bridge_reptends import find_good_modes, canonical_fraction, orbit_weave_analysis

# Find ALL modes with small k
modes = find_good_modes(37, base=10, kmax=5)
# Returns: [(3, 1, 27), (6, 1, 27027), ...]  -- k=1 at m=3, 6, 9, ...

# Show the canonical fraction identity
q, denom, explanation = canonical_fraction(37, 3)
# (27, 999, "1/37 = 27/999 = 27/(1000-1)")

# Full orbit weave analysis (auto-selects good mode)
ow = orbit_weave_analysis(97)
print(f"mode m={ow.m}, k={ow.k}, q={ow.q}")  # m=2, k=3, q=1
```

### Composites

Unlike coset analysis (prime-only), this works for any M coprime to base:

```python
ow = orbit_weave_analysis(996)  # 996 = 4 × 249
# Strips 2² → M = 249
# Finds mode m=3 where k=4 (small!)
# Computes R = W + F for 1/249
```

### Skeleton Analysis

The `print_skeleton_analysis()` function visualizes the three layers:

```python
from bridge_reptends import print_skeleton_analysis

# Works for any N - prime or composite
print_skeleton_analysis(996)   # Composite: k=4 powers
print_skeleton_analysis(97)    # Prime: same skeleton, QR interpretation available
```

---

## The Architecture

Our Agda formalization has two layers, reflecting a clean conceptual separation:

### Layer 1: GeometricStack (Base-Invariant)

These modules know **nothing about primes or quadratic residues**. They're pure exponential/modular arithmetic.

| Module | Purpose |
|--------|---------|
| `agda/GeometricStack/Family.agda` | The (base, k) pair defining a[i] = k^i and B[n] = base^n |
| `agda/GeometricStack/Capacity.agda` | Capacity index T_n where k^T < B^n ≤ k^(T+1) |
| `agda/GeometricStack/Scale.agda` | Word-size decomposition: direct[i] = a[i] mod B, illegal[i] = a[i] div B |

**Key insight**: Nothing here mentions "10" or "97" or "decimal". The structure is parameterized by (base, k). Base-invariance is **structural**, not asserted.

### Layer 2: QRTour (Prime-Field Semantics)

These modules add the number-theoretic meaning.

| Module | Purpose |
|--------|---------|
| `agda/QRTour/PrimeField.agda` | Prime modulus p, congruence ≡ₚ, powMod, multiplicative order |
| `agda/QRTour/QuadraticResidues.agda` | QR predicate, half = (p-1)/2, QRGenerator |
| `agda/QRTour/Cosets.agda` | NQR predicate, coset closure lemmas, numerator-determines-coset |
| `agda/QRTour/RemainderOrbit.agda` | Long-division remainders, stride lemma, QR tour coverage |

**Why this separation?** It makes base-invariance undeniable. GeometricStack compiles without knowing what a prime is. The group-theoretic interpretation lives in QRTour, cleanly separated from the mechanical computation.

---

## Design Decisions

### 1. Postulates First, Proofs Later

The heavy group-theory facts are marked as `postulate` for now:
- `remainders-are-powers` - r[n] ≡ B^n (mod p)
- `stride-orbit` - r[j*m] ≡ k^j (mod p)
- `qr-tour-cover` - QRGenerator k ⇒ orbit hits all QRs
- `capacity-exists`, `capacity-unique` - existence/uniqueness of T_n
- `order-spec`, `order-divides-p-1` - multiplicative order properties

This lets us build the full structure now and fill in proofs incrementally.

### 2. Base-Invariance is Structural

The GeometricStack modules are parameterized by a `Family` record containing (base, k). There's no way to accidentally bake in base-10 assumptions - the types prevent it.

### 3. Parameterized Modules

```agda
module GeometricStack.Capacity (F : Family) where ...
module GeometricStack.Scale (F : Family) where ...
module QRTour.QuadraticResidues (pf : PrimeField) where ...
module QRTour.RemainderOrbit (pf : PrimeField) where ...
```

This gives us composability: instantiate with different primes or bases without changing the module code.

### 4. Agda 2.8.0 / stdlib 2.x Compatibility

- `NonZero` instances must be explicit (passed via ⦃ ⦄ syntax)
- `_mod_` returns `Fin n`, so use `toℕ` for conversion to `ℕ`
- Record instance fields need explicit reference within the same record

---

## Key Postulates (Proof Targets)

Priority order for turning postulates into theorems:

1. **`remainders-are-powers`** - Simple induction on n. Good warmup.

2. **`stride-orbit`** - Follows from above plus properties of exponentiation mod p.

3. **`qr-tour-cover`** - Requires group-theoretic machinery: showing that a QR-generator's orbit exhausts the QR subgroup.

4. **`order-spec`** - Existence and minimality of multiplicative order. May want to use stdlib's GCD/Bezout.

---

## Collaboration Workflow

### Shared Documentation

The `collab/` folder contains documentation for sharing with collaborators:
- `collab/ORBIT_CORE.md` - Full Orbit Core framework (canonical decomposition, good coordinates)
- `collab/QUICK_START.md` - One-page onboarding for collaborators

When working with Claude on this project:

### Concrete Examples
Provide (B, p, m, k) tuples:
```
base B = 10, p = 97, m = 2, k = 3
ord_p(k) = 48
QRGenerator(k) holds
```

### Agda Feedback
Paste typecheck errors verbatim. Include the exact line numbers and error messages.

### Proof Requests
Be specific: "Please turn `remainders-are-powers` into a proof" rather than "prove some stuff".

### Empirical Observations
Share any patterns from Python exploration:
- Hit rates across bases
- Counterexamples where ord_p(k) < (p-1)/2
- Unexpected primes

---

## Continuity Reminders

**Hold these ideas present while building:**

1. **The skeleton is universal.** 1/N = Σ k^j / B^(j+1) works for ANY N coprime to base. This is the foundation - primality adds structure but doesn't create it.

2. **Three layers**: Skeleton (raw powers k^j), Carry (overflow correction), Closure (cyclic wrap). All three work for composites and primes alike.

3. **Primes give the QR/NQR interpretation.** When N is prime, (ℤ/pℤ)* = QR ⊔ NQR. Coset closure rules explain why remainders stay in their coset.

4. **"QR-generator" is the key prime-specific property**, not "full reptend prime." The latter is base-specific; the former is intrinsic to (p, d).

5. **The bridge residue k = B mod N is central.** When k is small, you get clean block structure visible for many steps. This is why some (N, B) pairs are "sweet spots".

6. **Base-invariance means**: the same GeometricStack code works for base 7, base 2, base 13. If you ever want to "add base-10 specific handling", stop and reconsider - the structure should be uniform.

7. **Postulates are promises**, not holes. Each one represents a theorem we believe is true and intend to prove. They're not shortcuts to avoid work - they're deferred work with a clear specification.

---

## Empirical Discoveries (from Python exploration)

The **Trichotomy Theorem** (empirically verified on primes < 500):

| Reptend Type | Condition | Stride Pattern | Stride Count |
|--------------|-----------|----------------|--------------|
| **Full** | ord_p(B) = p-1 | All EVEN [2,4,6,...] | φ(half) |
| **Half** | ord_p(B) = (p-1)/2 | All CONSECUTIVE [1,2,3,...] | φ(half) |
| **Degenerate** | ord_p(B) < (p-1)/2 | EMPTY [] | 0 |

Key insight: stride count is **base-invariant** when no base is degenerate. See `DISCOVERIES.md` for full details.
