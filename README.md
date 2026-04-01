# Bridge Reptends

> Reptends are geometric series with carry correction.

## The Core Identity

Choose a block width `m` and write `B = base^m`. For any modulus `N`, there
are unique integers `q, k` with

```
B = qN + k,   0 ≤ k < N.
```

When `B > N` (the good-mode case, equivalently `q > 0`), we have the exact identity

```
1/N = q/(B-k) = (q/B) × 1/(1 - k/B) = Σ q k^j / B^(j+1)
```

The clean `1, k, k², k³, ...` pattern is the special case `q = 1`, equivalently
`N = B - k`. This is the "bridge" case emphasized by the examples like `97 = 100 - 3`.

### The Three Layers

| Layer | What | Universal? |
|-------|------|------------|
| Skeleton | Raw coefficients `q k^j` (`k^j` when `q=1`) | Yes, any `N` |
| Carry | Overflow correction when `q k^j ≥ B` | Yes, any `N` |
| Closure | Cyclic wrap of the purely periodic part | Yes |

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

**Key insight:** primes add structure; they do not create the algebra. The
`q k^j` mechanism is general, while prime moduli add the QR/NQR interpretation.

## Quick Start

```bash
# Install the package
pip install -e .

# Skeleton/carry analysis (exact q*k^j coefficients, special powers when q=1)
python -c "from bridge_reptends import print_skeleton_analysis; print_skeleton_analysis(996)"

# Prime-specific QR analysis
python -c "from bridge_reptends import analyze_prime; print(analyze_prime(97))"

# Carry-state demo: raw coefficients -> carry transducer -> displayed blocks
python -m bridge_reptends.examples.carry_transducer_demo

# Ranked datasets for readable small-residue coordinates, canonical QR examples, and composites
search-reptends small-residue-coordinates --max 500 --top 20
search-reptends small-residue-coordinates-q1 --max 1500 --top 10
search-reptends prime-qr-generators --max 500 --top 10
search-reptends legacy-counterexamples --max 500 --bases 2,7,10,12
search-reptends composite-profiles --max 500
search-reptends visibility-profiles --max 500 --blocks 8
search-reptends visibility-counterexamples --max 500 --blocks 8
search-reptends same-core-visibility --base 7 --max 100 --blocks 8
search-reptends same-core-visibility --base 12 --max 200 --blocks 8
search-reptends carry-factorization --max 500 --blocks 8
search-reptends carry-factorization-selector --max 300 --blocks 8
search-reptends carry-selector-non-k1 --max 400 --blocks 8
search-reptends carry-selector-same-core --max 400 --blocks 8
search-reptends carry-selector-research --max 120 --bases 7,10,12 --blocks 8
search-reptends published-atlas --max 1200 --top 8 --output data/example_atlas.json
ci-checks
```

## CI Scope

The hosted CI in [`.github/workflows/ci.yml`](.github/workflows/ci.yml) is intentionally minimal for the current iteration stage:

- Python focused checks via `ci-checks`
- Lean build via `lake build`
- Site build via `yarn build`

Agda remains a deliberate manual/formal-companion surface for now rather than a hosted CI requirement. That keeps CI fast and stable while the Agda toolchain and proof-surface boundary continue to evolve.

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

### Agda (Pedagogical Companion Surface)

```bash
# Run from the agda/ directory
cd agda

# Typecheck the main example
agda Examples/Prime97.agda

# Typecheck theory modules
agda QRTour/RemainderOrbit.agda
```

Agda is a pedagogical companion surface with selective local proofs and explicit
postulates. Use [docs/AGDA_CORRESPONDENCE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/AGDA_CORRESPONDENCE.md)
as the authoritative map of what Agda proves locally, what is intentionally
postulated but Lean-backed, and what remains out of scope for the Agda layer.
The base-invariant orbit/buffer scaffolding is now locally proved in Agda; the
remaining postulates are concentrated in the heavier order, Euler-criterion,
subgroup-cardinality, and concrete-example witness layer.

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

Lean is the theorem-complete formal backend for the current atlas-level exact
claims. It closes the main results that Agda still leaves postulated:
- `remainder_eq_pow` - r[n] = B^n (mod p)
- `stride_orbit` - r[j*m] = k^j
- `pow_isQRGenerator_iff` - `B^m` is a QR-generator exactly when the order/gcd formula gives `(p-1)/2`
- `qrGenerator_pow_count_eq_totient` - a fixed QR generator has exactly `φ((p-1)/2)` QR-generating powers
- `base_qrGenerator_pow_count_eq_totient` - when `ord_p(B)` is `h` or `2h`, the number of QR-generating strides for the actual base element is exactly `φ(h)`
- `qr_tour_cover` - QR generator covers all QRs
- `Bridge.remainder_k_step` - r[n+k] = d × r[n] for bridge primes
- `SignedBridge.remainder_2k_step` - if `B^k ≡ ±d`, then `r[n+2k] = d² × r[n]` and the sign cancels
- `Bridge.blockValue_periodic` - bridge block values are powers of `d` and repeat with period `ord_p(d)`
- `orderOf_unitsChineseRemainder` - pairwise CRT sends unit order to the lcm of two component orders
- `orderOf_unitsEquivPrimePowers` - finite prime-power CRT sends unit order to the lcm of all prime-power component orders
- `preperiodPrimeSteps_le_iff` - the local preperiod contribution of a base prime is `ceil(v_p(N)/v_p(base))`
- `preperiodSteps_le_of_local_bounds` - the global preperiod is the maximum of those local step counts across the base primes
- `basePrimeSupportFactor_dvd_base_pow_preperiodSteps` - the full base-supported prime-power part of the denominator divides `base^preperiodSteps`

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
│   ├── orbit_weave.py    # Exact B = qN + k analysis, W + F decomposition
│   ├── composite.py      # Composite/CRT period profiles
│   ├── coset.py          # Prime-specific QR/NQR analysis
│   ├── transducer.py     # Carry/remainder graph layer and finite-window comparison reports
│   ├── registry.py       # Claim/vocabulary/source registry loaders
│   ├── search.py         # Ranked datasets and counterexample search
│   ├── sweep.py          # Systematic prime exploration
│   ├── patterns.py       # Exact formulas + secondary pattern study
│   └── examples/         # Educational demonstrations
│       ├── prime_19.py   # Deep dive on 1/19
│       ├── backwards.py  # Proving reptends are finite
│       ├── progression.py # The 2×10^m - 1 family
│       └── carry_transducer_demo.py # Carry-state examples
├── agda/                 # Agda pedagogical companion surface (local proofs + explicit postulates)
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
│       ├── CompositePeriod.lean  # Finite-family CRT period theorem
│       ├── Preperiod.lean        # Local valuation theorem for preperiod steps
│       └── CosetStructure.lean   # QR/NQR partition
├── site/                 # Interactive web visualization
│   └── src/components/   # React components with OrbitClock, StackVisualizer
├── docs/                 # Proof atlas, vocabulary, literature, composites
└── data/                 # Generated outputs + machine-readable registries
    ├── claim_registry.json
    ├── counterexamples.json
    ├── example_atlas.json
    ├── lean_module_index.json
    ├── literature_map.json
    ├── theorem_witnesses.json
    ├── vocabulary.json
    └── sweep_500.csv
```

## Documentation Map

The repo now keeps its public claims, counterexamples, and terminology in explicit registries:

Refresh the registry-backed Markdown blocks with:

```bash
python -m bridge_reptends.sync_registry_docs
build-expository-note
```

### Registry Snapshot

<!-- REGISTRY_SUMMARY_START -->
- total claims: 15
- classical: 3
- reproved-here: 8
- implemented-here: 1
- empirical: 1
- open: 2
<!-- REGISTRY_SUMMARY_END -->

Current open claim IDs:

<!-- OPEN_CLAIMS_START -->
- `small_k_visibility_threshold` - Exact visibility threshold for carried prefixes
- `carry_dfa_factorization` - Canonical factorization of long division into orbit and carry
<!-- OPEN_CLAIMS_END -->

Proof-system legend for the public theorem surface:

<!-- PROOF_SYSTEM_LEGEND_START -->
- `Lean-formalized`: proved in the Lean tree and suitable for theorem-level citation in the current public surface.
- `Agda-locally-proved`: discharged inside the Agda pedagogical companion surface without relying on Agda postulates.
- `Agda-postulated but Lean-backed`: still explicit as an Agda postulate, but closed by Lean or an atlas-backed Lean-backed claim in this repo.
- `empirical`: implemented and regression-tested here, but not promoted to theorem status.
- `open`: tracked as an unresolved claim boundary or interface question, not an established result.
<!-- PROOF_SYSTEM_LEGEND_END -->

- [ROADMAP.md](/Users/mikepurvis/other/quadratic-residue-reptends/ROADMAP.md) - root Lean-first fortification roadmap
- [docs/ROADMAP.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/ROADMAP.md) - broader working todo list and execution order
- [AGENT_TRACK_PLAYBOOK.md](/Users/mikepurvis/other/quadratic-residue-reptends/AGENT_TRACK_PLAYBOOK.md) - repository-agnostic guide for creating track-based hardening agents
- [docs/AGDA_CORRESPONDENCE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/AGDA_CORRESPONDENCE.md) - Agda postulate audit, Lean correspondences, and proof-surface legend
- [docs/PROOF_STATUS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/PROOF_STATUS_ATLAS.md) - exact claims, tagged by status
- [docs/THEOREM_WITNESS_ATLAS.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/THEOREM_WITNESS_ATLAS.md) - generated canonical witness and open-target atlas keyed by claim ID
- [docs/COUNTEREXAMPLES.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/COUNTEREXAMPLES.md) - concrete failures of older prose
- [DISCOVERIES.md](/Users/mikepurvis/other/quadratic-residue-reptends/DISCOVERIES.md) - empirical notes and curated examples, not a theorem source
- [docs/LITERATURE_MAP.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/LITERATURE_MAP.md) - where each claim family comes from
- [docs/VOCABULARY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/VOCABULARY.md) - preferred standardized terms
- [lean/THEOREM_GUIDE.md](/Users/mikepurvis/other/quadratic-residue-reptends/lean/THEOREM_GUIDE.md) - Lean-facing claim carriers and generated module audit
- [docs/COMPOSITES_CRT.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/COMPOSITES_CRT.md) - composite/CRT generalization
- [docs/CARRY_TRANSDUCER.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRY_TRANSDUCER.md) - carry layer as a standard transducer with explicit graph/comparison interfaces
- [docs/CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md) - exact Track 16 observables for raw-prefix agreement, incoming carry, and stabilization lookahead
- [docs/EXPOSITORY_NOTE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/EXPOSITORY_NOTE.md) - generated note built from the registry and published atlas
- [data/example_atlas.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/example_atlas.json) - curated Track 3 atlas of canonical search examples
- [data/theorem_witnesses.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/theorem_witnesses.json) - machine-readable canonical witnesses and open-target families
- [data/lean_module_index.json](/Users/mikepurvis/other/quadratic-residue-reptends/data/lean_module_index.json) - machine-readable Lean module role and promotion audit

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
5 is an NQR, so 5/97 lives in the NQR coset.

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

### Exact Stride Classification

Let `r = ord_p(B)` and `h = (p-1)/2`. Then

```
ord_p(B^m) = r / gcd(r, m)
```

so `B^m` is a QR-generator exactly when

```
r / gcd(r, m) = h.
```

Consequences:

| Reptend Type | Condition | Exact stride description |
|--------------|-----------|--------------------------|
| **Full** | `ord_p(B) = p-1` | `m = 2u` with `gcd(u, h) = 1` |
| **Half** | `ord_p(B) = h` | `gcd(m, h) = 1` |
| **Degenerate** | `ord_p(B) < h` | No QR-generating strides |

### Base Invariance (Empirical)

When `ord_p(B)` is `h` or `p-1`, the stride count is exactly `φ(h)`. So the
count is base-invariant across non-degenerate bases, even though the concrete
stride values differ.

## Architecture

*For intuition before formalism, see [Guided Tours](#guided-tours-the-mathematicians-entry-point) above.*

Agda and Lean share the same two-layer architecture, but they do not currently
have theorem parity:

1. **GeometricStack** (base-invariant): Pure modular arithmetic, parameterized by a `Family` record containing (base, k). There's no way to accidentally bake in base-10 assumptions—the types prevent it.

2. **QRTour** (number-theoretic): Adds prime field semantics, multiplicative order, QR subgroup structure.

This makes base-invariance *structural*—the code can't accidentally bake in
base-specific assumptions because the types don't allow it.

**Lean vs Agda:** Agda is the pedagogical companion surface with explicit
postulates; Lean is the theorem-complete backend for the repo's current exact
claims. Agda already proves local items such as `remainders-are-powers` and
`stride-orbit`, but heavier order/Euler/subgroup facts remain postulated there.
Use [docs/AGDA_CORRESPONDENCE.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/AGDA_CORRESPONDENCE.md)
before describing the Agda proof status in public prose.

## Python API

### Universal Functions (Any N Coprime to Base)

```python
from bridge_reptends import (
    print_skeleton_analysis,    # Visualize q*k^j coefficients + carry
    skeleton_vs_actual,         # Compare exact coefficients to actual blocks
    orbit_weave_analysis,       # Algebraic decomposition R = W + F
    multiplicative_order,       # ord_n(a)
    stride_order,               # ord_p(base^m) = ord_p(base)/gcd(...)
    reptend_type,               # full / half / degenerate
    find_good_modes,            # Find block widths where k is small
    canonical_fraction,         # Show 1/M = q/(B-k) identity
)

# Skeleton analysis works for ANY N
print_skeleton_analysis(37)    # q=27, k=1 gives constant 027 blocks
print_skeleton_analysis(996)   # q=1 bridge case: literal powers of 4

# Exact coefficients before carry
result = skeleton_vs_actual(996)
print(result['q'])             # 1
for i, (raw, carried, actual) in enumerate(zip(
        result['raw'], result['carried'], result['actual'])):
    print(f"Block {i}: raw={raw}, carried={carried}, actual={actual}")
```

### Algebraic Decomposition (Standard W + F Split)

```python
from bridge_reptends import orbit_weave_analysis

# Analyze the exact integer decomposition R = W + F
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

# When k=1, the exact coefficients are constant: q, q, q, q, ...
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
print(f"3 is {'QR' if is_qr(3, 97) else 'NQR'} mod 97")  # QR

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

*This project explores the connection between repeating expansions and modular arithmetic. The "infinite" reptend is a finite orbit written on infinite repeat.*
