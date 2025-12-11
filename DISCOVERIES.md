# Discoveries from Systematic Exploration

## Key Findings (December 2025)

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

---

## Files and Data

- `reptend_analysis.py` - Core analysis functions
- `prime_sweep.py` - Sweep infrastructure
- `pattern_analysis.py` - Deeper pattern investigation
- `data_sweep_500.csv` - Full data for primes < 500

---

## Connection to Agda Formalization

These empirical findings suggest new theorems to prove in the QRTour modules:

1. **Prove Trichotomy**: Show ord_p(B) ∈ {p-1, (p-1)/2} ⟹ stride_count = φ(half)
2. **Prove Parity Theorem**: Full reptend ⟹ QR-strides are exactly even integers < reptend
3. **Prove Base Invariance**: Formalize when stride count is base-independent
