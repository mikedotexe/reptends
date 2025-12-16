# Bridge Reptends

> Reptends are geometric series with carry correction.

## The Core Insight

For any N coprime to base B, with k = B mod N:

```
1/N = (1/B) × 1/(1 - k/B) = Σ k^j / B^(j+1)
```

The digit blocks are **powers of k**: 1, k, k², k³, ...

When k is small ("bridge" denominators like N = 10² - 3 = 97), the power
pattern is visible for many blocks before carry disrupts it.

### The Three Layers

| Layer | What | Universal? |
|-------|------|------------|
| Skeleton | Raw powers k^j | Yes, any N |
| Carry | Overflow correction when k^j ≥ B^m | Yes, any N |
| Closure | Cyclic wrap after ord_N(B) blocks | Yes, any N |

This works for 1/96, 1/996, 1/9996 just as well as 1/97.

### The Prime Bonus

When N is prime, (ℤ/pℤ)* splits into exactly two cosets (QR and NQR):

```
(ℤ/pℤ)* = QR ⊔ NQR
        = {squares} ⊔ {non-squares}
```

This explains:
- Why certain k values generate half the group
- The trichotomy (full/half/degenerate reptends)
- Base-invariant stride counts

**Key insight:** Primes add structure; they don't create it. The skeleton
exists for any N. Primes give us the QR/NQR interpretation of that skeleton.

## Quick Start

```bash
# Install the package
pip install -e .

# Skeleton analysis (works for any N!)
python -c "from bridge_reptends import print_skeleton_analysis; print_skeleton_analysis(996)"

# Prime-specific QR analysis
python -c "from bridge_reptends import analyze_prime; print(analyze_prime(97))"
```

## Guided Tours: The Mathematician's Entry Point

Run these to see the group theory in action. Each script outputs annotated proofs
using standard terminology (Lagrange's Theorem, Euler's criterion, index-2 subgroups).

### 1. Exhaustive Trace: 1/19

```bash
python -m bridge_reptends.examples.prime_19
```

**What you'll see**: Every step of long division as orbit traversal in (Z/19Z)*.
Demonstrates: cyclic group structure, primitive roots, Fermat's Little Theorem,
why the reptend has exactly 18 digits.

### 2. Working Backwards

```bash
python -m bridge_reptends.examples.backwards
```

**What you'll see**: Given only a reptend, recover the group structure.
Demonstrates: Euler's criterion for QR detection, orbit closure by Lagrange,
the proof that "infinite" decimals encode finite information.

### 3. The 2×10^m - 1 Family

```bash
python -m bridge_reptends.examples.progression
```

**What you'll see**: Why 19, 199, 1999 share structure.
Demonstrates: QR-generators, index-2 subgroups, stride-m orbit termination.

*Run these before diving into formalism—they show the mathematics in action.*

---

### Agda (Formal Proofs)

```bash
# Run from the agda/ directory
cd agda

# Typecheck the main example
agda Examples/Prime97.agda

# Typecheck theory modules
agda QRTour/RemainderOrbit.agda
```

### Lean 4 (Formal Proofs)

```bash
cd lean

# Install dependencies (requires Mathlib cache)
lake exe cache get

# Build all modules
lake build

# Typecheck specific module
lake build QRTour.RemainderOrbit
```

The Lean formalization proves most facts that are postulated in Agda:
- `remainder_eq_pow` - r[n] = B^n (mod p)
- `stride_orbit` - r[j*m] = k^j
- `qr_tour_cover` - QR generator covers all QRs
- `Bridge.remainder_k_step` - r[n+k] = d × r[n] for bridge primes

### Web Visualization

```bash
cd site
yarn install
yarn dev
```

## Project Structure

```
bridge-reptends/
├── bridge_reptends/      # Python analysis library
│   ├── analysis.py       # Core: ord, remainders, QR-gen detection
│   ├── orbit_weave.py    # Skeleton + carry analysis (works for any N)
│   ├── coset.py          # Prime-specific QR/NQR analysis
│   ├── sweep.py          # Systematic prime exploration
│   ├── patterns.py       # Hypothesis testing
│   └── examples/         # Educational demonstrations
│       ├── prime_19.py   # Deep dive on 1/19
│       ├── backwards.py  # Proving reptends are finite
│       └── progression.py # The 2×10^m - 1 family
├── agda/                 # Agda formal proofs (uses postulates)
│   ├── GeometricStack/   # Base-invariant layer (no primes)
│   │   ├── Family.agda   # (base, k) parameterization
│   │   ├── Capacity.agda # Capacity index T_n
│   │   └── Scale.agda    # Word-size decomposition
│   ├── QRTour/           # Number-theoretic semantics
│   │   ├── PrimeField.agda
│   │   ├── QuadraticResidues.agda
│   │   └── RemainderOrbit.agda
│   └── Examples/
│       └── Prime97.agda  # Canonical example
├── lean/                 # Lean 4 formal proofs (Mathlib, actual proofs)
│   ├── GeometricStack/   # Base-invariant layer
│   │   ├── Family.lean   # Geometric sequences k^i
│   │   ├── Capacity.lean # Capacity index via Nat.log
│   │   └── Scale.lean    # Word-size decomposition
│   └── QRTour/           # Number-theoretic semantics
│       ├── RemainderOrbit.lean   # Main theorem: stride covers QRs
│       ├── Bridge.lean           # p = B^k - d structure
│       └── CosetStructure.lean   # QR/NQR partition
├── collab/               # Shared documentation for collaborators
│   ├── ORBIT_CORE.md     # Full Orbit Core framework
│   └── QUICK_START.md    # One-page onboarding
├── site/                 # Interactive web visualization
│   └── src/components/   # React components with OrbitClock, StackVisualizer
└── data/                 # Generated analysis outputs
    └── sweep_500.csv     # Pre-computed sweep results
```

## The Canonical Example: 1/97

**Setup:** p = 97, base B = 10

**Step 1: Compute the gap**
```
10² = 100 ≡ 3 (mod 97)
d = 3  (the gap: 10² - 97 = 3)
```

**Step 2: Is d a QR-generator?**

For d to traverse the entire QR coset:
- The QR coset has size (p-1)/2 = 48
- d must have multiplicative order exactly 48

Check: ord₉₇(3) = 48 ✓

Since ord₉₇(3) = (p-1)/2, **d=3 generates the QR subgroup**.

**Step 3: Coset membership**

1 is a QR (1 = 1²), so 1/97 lives in the QR coset.
3 is an NQR, so 3/97 lives in the NQR coset.

Both orbits have the same structure—they traverse their respective
cosets at the same rate—but they never intersect.

**Step 4: Block structure**

Long division of 1/97 produces remainders r_n ≡ 10^n (mod 97).

Every-other remainder (r₀, r₂, r₄, ...) equals powers of d:
```
r₀  = 10⁰ ≡ 1  = 3⁰
r₂  = 10² ≡ 3  = 3¹
r₄  = 10⁴ ≡ 9  = 3²
...
```

Since d=3 generates all 48 quadratic residues, the stride-2 remainders visit every QR exactly once before cycling.

**The Punchline:** This isn't decimal magic—it's coset structure. The gap d determines traversal within the coset, and the numerator determines which coset.

## Empirical Patterns

See [DISCOVERIES.md](DISCOVERIES.md) for detailed findings, including:

### The Trichotomy Pattern

| Reptend Type | Condition | Stride Pattern |
|--------------|-----------|----------------|
| **Full** | ord_p(B) = p-1 | All EVEN [2,4,6,...] |
| **Half** | ord_p(B) = (p-1)/2 | All CONSECUTIVE [1,2,3,...] |
| **Degenerate** | ord_p(B) < (p-1)/2 | EMPTY [] |

### Base Invariance (Empirical)

Stride count appears to be **base-invariant** when no base is degenerate—verified on primes < 500 across multiple bases. The specific stride values differ by base, but the count φ((p-1)/2) is preserved.

## Architecture

*For intuition before formalism, see [Guided Tours](#guided-tours-the-mathematicians-entry-point) above.*

Both formalizations (Agda and Lean) share the same two-layer architecture:

1. **GeometricStack** (base-invariant): Pure modular arithmetic, parameterized by a `Family` record containing (base, k). There's no way to accidentally bake in base-10 assumptions—the types prevent it.

2. **QRTour** (number-theoretic): Adds prime field semantics, multiplicative order, QR subgroup structure.

This makes base-invariance *structural*—the code can't accidentally bake in base-specific assumptions because the types don't allow it.

**Lean vs Agda:** The Lean formalization proves most facts that the Agda version postulates, using Mathlib's `orderOf`, `ZMod`, and `Nat.log`. The Lean version also includes additional modules for bridge primes (`Bridge.lean`), signed bridges (`SignedBridge.lean`), and p-adic structure (`PAdicBridge.lean`).

## Python API

### Universal Functions (Any N Coprime to Base)

```python
from bridge_reptends import (
    print_skeleton_analysis,    # Visualize skeleton + carry structure
    skeleton_vs_actual,         # Compare raw powers to actual blocks
    orbit_weave_analysis,       # Algebraic decomposition R = W + F
    multiplicative_order,       # ord_n(a)
    find_good_modes,            # Find block widths where k is small
    canonical_fraction,         # Show 1/M = q/(B-k) identity
)

# Skeleton analysis works for ANY N (prime or composite)
print_skeleton_analysis(996)   # Composite: shows k=4 powers
print_skeleton_analysis(97)    # Prime: same structure, QR interpretation available

# The skeleton: raw powers k^j before carry
result = skeleton_vs_actual(996)
for i, (raw, carried, actual) in enumerate(zip(
        result['raw_blocks'], result['carried_blocks'], result['actual_blocks'])):
    print(f"Block {i}: raw={raw}, carried={carried}, actual={actual}")
```

### Algebraic Decomposition (Orbit Weave + Closure Flux)

```python
from bridge_reptends import orbit_weave_analysis

# Analyze reptend integer decomposition R = W + F
ow = orbit_weave_analysis(97)
print(f"Modulus M = {ow.M}")           # 97
print(f"Mode m = {ow.m}")              # 2 (block width)
print(f"Bridge k = {ow.k}")            # 3 (100 mod 97)
print(f"Orbit L = {ow.L}")             # 48 blocks

# The decomposition identity
print(f"R = W + F: {ow.R == ow.W + ow.F}")  # True

# Works for composites too
ow = orbit_weave_analysis(996)         # 996 = 4 × 249
print(f"Stripped to M = {ow.M}")       # 249
print(f"Mode m = {ow.m}, k = {ow.k}")  # m=3, k=4 (small!)
```

### Good Coordinates (Finding Clean Block Widths)

The fundamental equation: **B = qM + k** where k = B mod M.

"Good coordinates" = finding block widths m where k is small.

```python
from bridge_reptends import find_good_modes, canonical_fraction

# For M=37, find all modes with small k
modes = find_good_modes(37, base=10, kmax=5)
# Returns: [(3, 1, 27), (6, 1, 27027), ...]
# At m=3: 1000 = 27×37 + 1, so k=1 (perfect!)

# Show the canonical fraction identity
q, denom, explanation = canonical_fraction(37, 3)
print(explanation)  # "1/37 = 27/999 = 27/(1000-1)"

# When k=1, the skeleton is constant: 1, 1, 1, 1, ...
# So 1/37 = 0.027027027...
```

### Prime-Specific Functions (QR/Coset Analysis)

```python
from bridge_reptends import (
    is_qr,                      # Test QR membership (Euler's criterion)
    is_qr_generator,            # Check if k generates QR subgroup
    analyze_prime,              # Complete reptend analysis
    analyze_coset_structure,    # Coset/block structure analysis
    get_blocks,                 # Extract digit blocks
)

# Coset membership (requires prime!)
print(f"1 is {'QR' if is_qr(1, 97) else 'NQR'} mod 97")  # QR
print(f"3 is {'QR' if is_qr(3, 97) else 'NQR'} mod 97")  # NQR

# Analyze coset structure for p=139, base=12 (sweet spot example)
coset = analyze_coset_structure(139, base=12)
print(f"Block width k = {coset.block.k}")              # 2
print(f"Gap d = {coset.block.d}")                      # 5
print(f"Gap ratio = {coset.block.gap_ratio:.1%}")      # 3.6%

# Extract digit blocks showing coset traversal
blocks = get_blocks(numerator=1, p=139, base=12, k=2, n_blocks=5)
for b in blocks:
    print(f"  Block {b.index}: rem={b.start_remainder:3}, digits={b.digits}, {b.coset}")
```

## Contributing

See [CLAUDE.md](CLAUDE.md) for detailed technical guidance and collaboration workflow.

## License

MIT

---

*This project explores the beautiful connection between decimal expansions and abstract algebra. The "infinite" repeating decimal is just a finite geometric series on infinite repeat.*
