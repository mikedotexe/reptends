# Quadratic Residue Reptends

> Reptends aren't decimal curiosities—they're group theory wearing a decimal costume.

## The Core Insight

When you compute 1/97 in base 10, the repeating decimal has a period of 96 digits. But *why*? The answer lies in the multiplicative group (ℤ/97ℤ)*.

**Key reframe:**

| Contemporary Language | Our Language |
|----------------------|--------------|
| "Period length of 1/p" | Orbit length in (ℤ/pℤ)* |
| "Digit patterns" | Residue classes under modular exponentiation |
| "97 is special in base 10" | 97 has a QR-generating element k=3 where 10²≡k |
| "Full reptend prime" | Prime where ord_p(base) = p-1 |

The "magic" of certain primes isn't about base 10—it's about whether `10^m` generates the quadratic residue subgroup for some `m`.

## Quick Start

### Python

```bash
# Install the package
pip install -e .

# Analyze a prime
python -c "from qr_reptends import analyze_prime; print(analyze_prime(97))"

# Sweep primes with multiple bases
sweep-primes --max 500 --bases 2,7,10,12 --output results.csv

# Run educational examples
python -m qr_reptends.examples.prime_19
python -m qr_reptends.examples.backwards
python -m qr_reptends.examples.progression
```

### Agda (Formal Proofs)

```bash
# Run from the agda/ directory
cd agda

# Typecheck the main example
agda Examples/Prime97.agda

# Typecheck theory modules
agda QRTour/RemainderOrbit.agda
```

### Web Visualization

```bash
cd site
yarn install
yarn dev
```

## Project Structure

```
qr-reptends/
├── qr_reptends/          # Python analysis library
│   ├── analysis.py       # Core: ord, remainders, QR-gen detection
│   ├── sweep.py          # Systematic prime exploration
│   ├── patterns.py       # Hypothesis testing
│   └── examples/         # Educational demonstrations
│       ├── prime_19.py   # Deep dive on 1/19
│       ├── backwards.py  # Proving reptends are finite
│       └── progression.py # The 2×10^m - 1 family
├── agda/                 # Formal proofs
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
├── site/                 # Interactive web visualization
│   └── src/components/   # React components with OrbitClock, StackVisualizer
└── data/                 # Generated analysis outputs
    └── sweep_500.csv     # Pre-computed sweep results
```

## The Canonical Example: 1/97

**Setup:** p = 97, base B = 10

**Step 1: Compute k**
```
10² = 100 ≡ 3 (mod 97)
```
So k = 3.

**Step 2: Is k a QR-generator?**

For k to generate the entire quadratic residue (QR) subgroup:
- The QR subgroup has size (p-1)/2 = 48
- k must have multiplicative order exactly 48

Check: ord₉₇(3) = 48 ✓

Since ord₉₇(3) = (p-1)/2, **k=3 generates the QR subgroup**.

**Step 3: What This Means**

Long division of 1/97 produces remainders r_n ≡ 10^n (mod 97).

Every-other remainder (r₀, r₂, r₄, ...) equals powers of k:
```
r₀  = 10⁰ ≡ 1  = 3⁰
r₂  = 10² ≡ 3  = 3¹
r₄  = 10⁴ ≡ 9  = 3²
...
```

Since k=3 generates all 48 quadratic residues, the stride-2 remainders visit every QR exactly once before cycling.

**The Punchline:** This isn't decimal magic—it's group theory. Any base B where B^m ≡ 3 (mod 97) for even m would exhibit the same structure.

## Key Discoveries

See [DISCOVERIES.md](DISCOVERIES.md) for empirical findings, including:

### The Trichotomy Theorem

| Reptend Type | Condition | Stride Pattern |
|--------------|-----------|----------------|
| **Full** | ord_p(B) = p-1 | All EVEN [2,4,6,...] |
| **Half** | ord_p(B) = (p-1)/2 | All CONSECUTIVE [1,2,3,...] |
| **Degenerate** | ord_p(B) < (p-1)/2 | EMPTY [] |

### Base Invariance

Stride count is **base-invariant** when no base is degenerate. The specific stride values differ by base, but the count φ((p-1)/2) is preserved.

## Architecture

The Agda formalization separates two layers:

1. **GeometricStack** (base-invariant): Pure modular arithmetic, parameterized by a `Family` record containing (base, k). There's no way to accidentally bake in base-10 assumptions—the types prevent it.

2. **QRTour** (number-theoretic): Adds prime field semantics, multiplicative order, QR subgroup structure.

This makes base-invariance *structural*—the code can't accidentally bake in base-specific assumptions because the types don't allow it.

## Python API

```python
from qr_reptends import (
    multiplicative_order,    # ord_p(a)
    is_qr_generator,         # Check if k generates QR subgroup
    find_qr_strides,         # Find all m where base^m is QR-generator
    analyze_prime,           # Complete analysis
    PrimeAnalysis,           # Result dataclass
)

# Analyze p=97 in base 10
analysis = analyze_prime(97, base=10)
print(f"Reptend length: {analysis.reptend_length}")  # 96
print(f"QR-strides: {analysis.qr_strides[:5]}...")   # [2, 6, 10, 14, 18]...
print(f"Stride count: {analysis.stride_count}")      # 24
```

## Contributing

See [CLAUDE.md](CLAUDE.md) for detailed technical guidance and collaboration workflow.

## License

MIT

---

*This project explores the beautiful connection between decimal expansions and abstract algebra. The "infinite" repeating decimal is just finite group theory on infinite repeat.*
