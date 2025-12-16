# Discoveries from Systematic Exploration

## The Universal Structure (Foundation)

Before the prime-specific patterns, there's a universal mechanism that works for ANY N coprime to base.

### The Geometric Series Skeleton

For any N coprime to base B, with k = B mod N:

```
1/N = (1/B) × 1/(1 - k/B) = Σ k^j / B^(j+1)
```

The digit blocks are **powers of k**: 1, k, k², k³, ...

This skeleton is visible until carry (overflow) disrupts the clean pattern.

### The Three Layers

| Layer | What | Universal? |
|-------|------|------------|
| Skeleton | Raw powers k^j | Yes, any N |
| Carry | Overflow correction when k^j ≥ B^m | Yes, any N |
| Closure | Cyclic wrap after ord_N(B) blocks | Yes, any N |

### Examples Across the 10^n - 4 Family

All these have k = 4, showing identical skeleton structure:

| N | k | First overflow k^j | Skeleton valid |
|---|---|-------------------|----------------|
| 96 | 4 | k⁴ = 256 > 100 | ~4 blocks clean |
| 996 | 4 | k⁵ = 1024 > 1000 | ~5 blocks clean |
| 9996 | 4 | k⁷ = 16384 > 10000 | ~7 blocks clean |

**Primality doesn't affect this layer** - 96 (composite) and 97 (prime) both show the skeleton.

```python
from bridge_reptends import print_skeleton_analysis

print_skeleton_analysis(996)   # Composite: k=4 powers visible
print_skeleton_analysis(97)    # Prime: k=3 powers visible
```

### Key Insight

The skeleton is the **foundation**. Prime-specific structure (cosets, QR/NQR) is an **additional interpretation layer** that explains WHY certain primes are sweet spots—but the skeleton exists for any N.

---

## Key Findings: Prime-Specific Structure (December 2025)

### 1. The Trichotomy Theorem

**THEOREM (empirically verified on primes < 500):**

For prime p and base B coprime to p, exactly ONE of these holds:

| Reptend Type | Condition | Stride Pattern | Stride Count |
|--------------|-----------|----------------|--------------|
| **Full** | ord_p(B) = p-1 | All EVEN [2,4,6,...] | φ(half) |
| **Half** | ord_p(B) = (p-1)/2 | All CONSECUTIVE [1,2,3,...] | φ(half) |
| **Degenerate** | ord_p(B) < (p-1)/2 | EMPTY [] | 0 |

**Group-theoretic explanation:**
- **Full reptend**: B generates all of (ℤ/pℤ)*, so B^m is a QR iff m is even (QRs have even index in the cyclic group)
- **Half reptend**: B is already in the QR subgroup, so all powers B^m are QRs; consecutive strides
- **Degenerate**: B's orbit is too small to intersect the QR subgroup meaningfully

### 2. Base-Invariance of Stride Count

**THEOREM (empirically verified):**

The stride COUNT is base-invariant when no base has a degenerate reptend.

More precisely: if for all bases B in consideration, ord_p(B) ∈ {p-1, (p-1)/2}, then all bases have the same stride count φ(half).

**Examples from p=23:**
| Base | ord_p(B) | Type | Strides | Count |
|------|----------|------|---------|-------|
| 2 | 11 | half | [1,2,...,10] | 10 |
| 7 | 22 | full | [2,4,...,20] | 10 |
| 10 | 22 | full | [2,4,...,20] | 10 |
| 12 | 11 | half | [1,2,...,10] | 10 |

The VALUES differ but the COUNT is invariant!

### 3. Stride Count = φ((p-1)/2)

When stride_count ≠ 0, we have:
```
stride_count = φ((p-1)/2)
```

This is the Euler phi function of half the group order.

### 4. Half-Reptend ⟺ Stride 1

**THEOREM:**
```
ord_p(B) = (p-1)/2  ⟺  1 ∈ qr_strides(p, B)
```

In other words: the base is a QR-generator if and only if it has half-length reptend.

### 5. The Coset Picture

The multiplicative group (ℤ/pℤ)* has p-1 elements and splits into exactly **two cosets**:

| Coset | Size | Members | Multiplication Rule |
|-------|------|---------|---------------------|
| **QR** (squares) | (p-1)/2 | {1, 4, 9, 16, ...} | QR × QR = QR |
| **NQR** (non-squares) | (p-1)/2 | {2, 3, 5, 6, ...} | NQR × QR = NQR |

**Key insight**: When computing a/p in base B:
- The **numerator a** determines which coset the orbit lives in
- All remainders in the orbit stay in that coset forever
- The **gap d = B^k - p** (when small) traverses the coset cleanly

**Coset closure rules**:
- QR × QR = QR (product of squares is a square)
- NQR × QR = NQR (non-square times square stays non-square)
- NQR × NQR = QR (product of two non-squares is a square)

**Why this matters**: The "magic" of reptends isn't about digits—it's about coset orbits.
Different numerators give different "flavors" because they live in different cosets,
but the structure within each coset is identical.

**Example (p=139, B=12)**:
```
d = 12² - 139 = 5  (gap is small → sweet spot)

1/139: remainders stay in QR coset   (1 is QR)
3/139: remainders stay in NQR coset  (3 is NQR)

Both orbits have identical structure—just translated by ×3.
```

---

## Spectacular Examples

| Prime | half | Pattern | Notable Property |
|-------|------|---------|------------------|
| 83 | 41 | [1,...,40] | ALL 40 strides! (half is prime) |
| 107 | 53 | [1,...,52] | ALL 52 strides! (half is prime) |
| 47 | 23 | [2,4,...,44] or [1,...,22] | Count-invariant across bases |
| 59 | 29 | [2,4,...,56] or [1,...,28] | Count-invariant, half prime |
| 97 | 48 | [2,10,14,22,...] | Diffs alternate [8,4,8,4...] |

**When half is PRIME**: φ(half) = half - 1, so stride count is maximal.

---

## Verified Statistics (primes < 500)

- Total primes analyzed: 93
- Count-invariant primes: 30 (32%)
- Primes with 0 QR-strides (base 10): 28 (30%)
- Primes where base 10 is QR-generator: 30

---

## Conjectures Awaiting Proof

### Conjecture 1: The Trichotomy is Complete
Every prime-base pair falls into exactly one of: full, half, or degenerate.
(No other reptend lengths produce QR-strides.)

### Conjecture 2: Parity Determines Pattern
- Full reptend → ALL strides are even multiples of gcd(2, ord_p(B))
- Half reptend → ALL consecutive integers from 1 to φ(half)

### Conjecture 3: Count Invariance Criterion
If for all bases B₁, B₂: ord_p(B₁) ∣ (p-1) and ord_p(B₂) ∣ (p-1) with same ratio to half, then counts match.

---

## Open Questions

1. **The [8,4,8,4...] pattern for p=97** - Where do the gaps come from? Related to factorization of 48 = 2⁴×3?

2. **Can we characterize degenerate primes?** When does ord_p(10) fail to be p-1 or (p-1)/2?

3. **Is there a closed form for stride values?** The strides seem to follow patterns related to coprimality with certain divisors of half.

4. **Connection to quadratic reciprocity?** Does Legendre symbol (B/p) predict reptend type?

5. **Sweet spot characterization**: For which (p, B) pairs is the gap d = B^k - p small enough to give clean block structure? Is there a density result?

---

## Files and Data

- `reptend_analysis.py` - Core analysis functions
- `prime_sweep.py` - Sweep infrastructure
- `pattern_analysis.py` - Deeper pattern investigation
- `data_sweep_500.csv` - Full data for primes < 500

---

## The Orbit Weave + Closure Flux Decomposition

### The Key Identity

For modulus M coprime to base B, the reptend integer R decomposes:

```
R = W + F

R = (B^L - 1) / M      (reptend integer)
W = (B^L - k^L) / M    (orbit weave)
F = (k^L - 1) / M      (closure flux)
k = B mod M            (bridge residue)
L = ord_M(B)           (orbit length)
```

### Example: p = 97, mode m = 2

```
B = 100, k = 3, L = 48
R = (100^48 - 1) / 97
W = (100^48 - 3^48) / 97
F = (3^48 - 1) / 97
R = W + F ✓
```

### Connection to Coset Structure

- **k = B mod M** is the gap d when M = B^m - d (bridge primes)
- When k is a **QR-generator**, the weave W traverses the QR subgroup
- The flux F encodes "carry propagation" - the correction that closes the loop

### Research Questions

1. **Minimal bridge residue**: For a given M, how small can k = base^m mod M get as m varies? What's the distribution?

2. **Mode invariants**: How does mode choice m affect flux F? Are there quantities invariant under mode change?

3. **Factorization structure**: Does W or F factor in interesting ways? When does gcd(W, F) reveal structure?

4. **Coset connection**: How do W and F relate to QR/NQR orbits? Does the decomposition simplify for QR-generators?

5. **Carry automaton**: Can we factor the reptend into "pure orbit" + "carry transducer" canonically?

6. **Composite reptends**: For M = p₁p₂, how does the decomposition relate to the CRT?

---

## Connection to Agda Formalization

These empirical findings suggest new theorems to prove in the QRTour modules:

1. **Prove Trichotomy**: Show ord_p(B) ∈ {p-1, (p-1)/2} ⟹ stride_count = φ(half)
2. **Prove Parity Theorem**: Full reptend ⟹ QR-strides are exactly even integers < reptend
3. **Prove Base Invariance**: Formalize when stride count is base-independent
4. **Prove Decomposition**: R = W + F follows algebraically from definitions

---

## The Orbit Core Framework

See `collab/ORBIT_CORE.md` for the complete framework documentation.

### The Canonical Decomposition

For any modulus M and block width m:
```
B = qM + k  →  1/M = q/(B-k)
```

Where:
- B = base^m (block base)
- k = B mod M (bridge residue)
- q = (B - k) / M (quotient)

### Good Coordinates

A "good coordinate" is a block width m where k is small. Use `find_good_modes(M, base, kmax)` to find all such coordinates.

```python
from bridge_reptends import find_good_modes, canonical_fraction

# For M=37, find k=1 at m=3!
modes = find_good_modes(37, base=10, kmax=5)
# Returns: [(3, 1, 27), ...]

# 1000 = 27×37 + 1
q, denom, explanation = canonical_fraction(37, 3)
print(explanation)  # "1/37 = 27/999 = 27/(1000-1)"
```

### Canonical vs Coordinate-Dependent

| Object | Canonical? |
|--------|-----------|
| R, L, orbit dynamics | Yes |
| k, q, W, F, skeleton visibility | No (depend on m) |

The orbit is the invariant. The skeleton/weave/flux split is a lens - meaningful when k is small.
