# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build and Run Commands

### Agda (Formal Proofs)

```bash
# Typecheck all modules
agda src/Examples/Prime97.agda

# Typecheck a specific module
agda src/QRTour/RemainderOrbit.agda

# Watch for changes (if you have agda-mode or similar)
# The .agda-lib file configures stdlib dependency automatically
```

### Python (Empirical Exploration)

```bash
# Run core analysis demo
python3 reptend_analysis.py

# Sweep primes up to N with specific bases
python3 prime_sweep.py --max 500 --bases 2,7,10,12 --output results.csv

# Run pattern analysis
python3 pattern_analysis.py
```

---

# Quadratic Residue Reptends

## The Paradigm Shift

**Contemporary view**: Reptends (repeating decimal expansions of 1/p) are "base-10 curiosities" - interesting patterns that emerge when you divide by certain primes.

**Our view**: Reptends reveal **group-theoretic structure** that is completely **base-invariant**. The patterns aren't about decimals at all - they're about orbits in multiplicative groups.

### Key Reframes

| Contemporary Language | Our Language |
|----------------------|--------------|
| "Period length of 1/p" | Orbit length in (ℤ/pℤ)* |
| "Digit patterns" | Residue classes under modular exponentiation |
| "97 is special in base 10" | 97 has a QR-generating element k=3 where 10²≡k |
| "Full reptend prime" | Prime where ord_p(base) = p-1 |

**Why this matters**: We're not studying decimal folklore. We're studying the subgroup structure of multiplicative groups, which happens to manifest visually when you write out reptends. The "magic" is group theory wearing a decimal costume.

---

## The Canonical Example: 1/97 in Base 10

This walkthrough shows exactly how the group-theoretic structure works.

### Setup
- p = 97 (prime)
- Base B = 10
- m = 2 (we'll look at B² mod p)

### Step 1: Compute k

```
10² = 100 ≡ 3 (mod 97)
```

So **k = 3**.

### Step 2: Is k a QR-generator?

For k to generate the entire quadratic residue (QR) subgroup:
- The QR subgroup has size (p-1)/2 = (97-1)/2 = **48**
- k must have multiplicative order exactly 48

Check: ord₉₇(3) = 48
- 3^48 ≡ 1 (mod 97) ✓
- No smaller positive power works ✓

Since ord₉₇(3) = (p-1)/2, **k=3 generates the QR subgroup**.

### Step 3: What This Means for 1/97

Long division of 1/97 in base 10 produces remainders:
```
r₀ = 1
r_{n+1} = 10 · rₙ (mod 97)
```

So rₙ ≡ 10ⁿ (mod 97).

**The key observation**: Every-other remainder (r₀, r₂, r₄, ...) equals powers of k:
```
r₀  = 10⁰ ≡ 1   = 3⁰
r₂  = 10² ≡ 3   = 3¹
r₄  = 10⁴ ≡ 9   = 3²
r₆  = 10⁶ ≡ 27  = 3³
...
```

Since k=3 generates all 48 quadratic residues, the stride-2 remainders visit every QR exactly once before cycling.

### The Punchline

The "magic" of 1/97's decimal expansion is just the orbit of 3 in (ℤ/97ℤ)*. There's nothing special about base 10 here - if you picked any base B where B^m ≡ 3 (mod 97) for even m, you'd see the same QR tour structure.

---

## The Architecture

Our Agda formalization has two layers, reflecting a clean conceptual separation:

### Layer 1: GeometricStack (Base-Invariant)

These modules know **nothing about primes or quadratic residues**. They're pure exponential/modular arithmetic.

| Module | Purpose |
|--------|---------|
| `GeometricStack.Family` | The (base, k) pair defining a[i] = k^i and B[n] = base^n |
| `GeometricStack.Capacity` | Capacity index T_n where k^T < B^n ≤ k^(T+1) |
| `GeometricStack.Scale` | Word-size decomposition: direct[i] = a[i] mod B, illegal[i] = a[i] div B |

**Key insight**: Nothing here mentions "10" or "97" or "decimal". The structure is parameterized by (base, k). Base-invariance is **structural**, not asserted.

### Layer 2: QRTour (Prime-Field Semantics)

These modules add the number-theoretic meaning.

| Module | Purpose |
|--------|---------|
| `QRTour.PrimeField` | Prime modulus p, congruence ≡ₚ, powMod, multiplicative order |
| `QRTour.QuadraticResidues` | QR predicate, half = (p-1)/2, QRGenerator |
| `QRTour.RemainderOrbit` | Long-division remainders, stride lemma, QR tour coverage |

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

1. **This is group theory wearing a decimal costume.** Every "decimal pattern" observation should translate to a group-theoretic statement. If it doesn't, we're missing something.

2. **"QR-generator" is the key property**, not "full reptend prime." The latter is base-specific; the former is intrinsic to (p, k).

3. **The φ((p-1)/2) / ((p-1)/2) heuristic** for hit-rates is probabilistic/empirical, not proven. It's a conjecture about how k distributes in the QR subgroup.

4. **Base-invariance means**: the same GeometricStack code works for base 7, base 2, base 13. If you ever want to "add base-10 specific handling", stop and reconsider - the structure should be uniform.

5. **Postulates are promises**, not holes. Each one represents a theorem we believe is true and intend to prove. They're not shortcuts to avoid work - they're deferred work with a clear specification.

---

## Empirical Discoveries (from Python exploration)

The **Trichotomy Theorem** (empirically verified on primes < 500):

| Reptend Type | Condition | Stride Pattern | Stride Count |
|--------------|-----------|----------------|--------------|
| **Full** | ord_p(B) = p-1 | All EVEN [2,4,6,...] | φ(half) |
| **Half** | ord_p(B) = (p-1)/2 | All CONSECUTIVE [1,2,3,...] | φ(half) |
| **Degenerate** | ord_p(B) < (p-1)/2 | EMPTY [] | 0 |

Key insight: stride count is **base-invariant** when no base is degenerate. See `DISCOVERIES.md` for full details.
