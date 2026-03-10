# CLAUDE.md

This file provides guidance to Claude Code when working in this repository.

## Build and Run Commands

### Python (`bridge_reptends`)

```bash
# Install the package in development mode
pip install -e .

# Core analysis
python -c "from bridge_reptends import print_skeleton_analysis; print_skeleton_analysis(996)"
python -m bridge_reptends.analysis
python -m bridge_reptends.patterns

# Dataset and search entry points
sweep-primes --max 500 --bases 2,7,10,12 --output data/results.csv
search-reptends bridges --max 500 --top 20
search-reptends legacy-counterexamples --max 500 --bases 2,7,10,12
search-reptends composites --max 500

# Educational examples
python -m bridge_reptends.examples.prime_19
python -m bridge_reptends.examples.backwards
python -m bridge_reptends.examples.progression
```

### Agda

```bash
cd agda
agda Examples/Prime97.agda
agda QRTour/RemainderOrbit.agda
```

### Lean 4

```bash
cd lean
lake exe cache get
lake build
lake build QRTour.RemainderOrbit
```

### Web Visualization

```bash
cd site
yarn install
yarn dev
yarn build
```

## Canonical Sources

Use these as the mathematical and editorial source of truth:

- [README.md](README.md) for the project overview and command map.
- [docs/AGDA_CORRESPONDENCE.md](docs/AGDA_CORRESPONDENCE.md) for the Agda postulate audit and Lean correspondence map.
- [docs/PROOF_STATUS_ATLAS.md](docs/PROOF_STATUS_ATLAS.md) for theorem status and claim IDs.
- [docs/VOCABULARY.md](docs/VOCABULARY.md) for standard-label-first terminology.
- [docs/ROADMAP.md](docs/ROADMAP.md) for execution order and current priorities.
- [DISCOVERIES.md](DISCOVERIES.md) for empirical notes and curated examples only.

## Non-Negotiable Mathematical Invariants

- Claim `series_q_weighted_identity`: for a block base `B = base^m`, write `B = qN + k` with `0 <= k < N`. Then `1/N = q/(B-k) = (q/B) * 1/(1-k/B) = Σ q*k^j / B^(j+1)`. The literal `1, k, k^2, ...` pattern is only the special case `q = 1`.
- Claim `qr_stride_classification`: for an odd prime `p`, base `B`, stride `m`, and `h = (p-1)/2`, the stride is QR-generating exactly when `ord_p(B) / gcd(ord_p(B), m) = h`. Do not restate this as "all even strides" or "all consecutive strides."
- Claim `positive_q_good_modes`: call a coordinate or mode "good" only when `B > M`, so `q = (B-k)/M` is positive.
- Standard-label-first vocabulary: say remainder `k = B mod M` before "bridge residue"; body term `W` before "orbit weave"; correction term `F` before "closure flux."
- Public theorem-level prose must cite the proof-status atlas before introducing a claim. If a statement is not already in the atlas, mark it `empirical` or `open`, not theorem-level fact.

## Collaboration Workflow

When working with Claude Code on this project:

- Start from the canonical sources above instead of copying math prose out of this file.
- For concrete examples, provide full tuples such as `(base, N, m, B, q, k, L)` or `(base, p, stride, ord_p(base))`.
- When discussing results, explicitly label them `classical`, `reproved-here`, `implemented-here`, `empirical`, or `open`.
- For documentation or UI changes, keep the standard label first and put the repo alias second.
- For proof requests, point to the claim ID when one exists.
- Treat Agda as a pedagogical companion surface with explicit postulates, not as a silent theorem-parity target with Lean.
