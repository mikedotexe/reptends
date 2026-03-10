# Empirical Notes and Exact Consequences

This file is not the proof-status source of truth for the repository. Use [docs/PROOF_STATUS_ATLAS.md](docs/PROOF_STATUS_ATLAS.md) for authoritative claim status and [docs/VOCABULARY.md](docs/VOCABULARY.md) for standard terminology.

Tag legend used throughout the repo:

- `classical`: standard mathematics used here as background.
- `reproved-here`: a classical result with an explicit proof artifact in this repo.
- `empirical`: observed computationally or used as a heuristic.
- `open`: not established here and not treated as theorem-level fact.

## How to Read This File

- The next section lists exact consequences that are already justified elsewhere in the repo, with claim IDs and short reminders only.
- The empirical section collects curated examples, sweep statistics, and visibility heuristics that are useful for exploration but are not promoted to theorem-level results.
- Open questions remain deliberately separated from exact statements.
- Standard labels come first. Repo aliases such as "orbit weave" and "closure flux" are kept only as secondary explanatory names.

## Exact Consequences Already Justified Elsewhere

These are not new discoveries. They are short summaries of results whose status is tracked in the proof-status atlas.

| Claim ID | Status | Short reminder |
|----------|--------|----------------|
| `series_q_weighted_identity` | `classical` | For `B = qN + k`, we have `1/N = q/(B-k) = Σ q*k^j / B^(j+1)`. The literal `k^j` pattern is the special case `q = 1`. |
| `qr_stride_classification` | `reproved-here` | For an odd prime `p`, `B^m` is QR-generating exactly when `ord_p(B) / gcd(ord_p(B), m) = (p-1)/2`. When QR-generating strides exist, the count is `phi((p-1)/2)`. |
| `positive_q_good_modes` | `classical` | A coordinate choice is only "good" once `B > M`, so `q = (B-k)/M` is positive. |
| `crt_period_lcm` | `classical` | For composite `M = product p_i^e_i` coprime to the base, the global period is the least common multiple of the local prime-power orders. |
| `preperiod_from_base_factors` | `classical` | Base factors control the preperiod. Stripping them leaves the purely periodic modulus `M`. |

The reptend decomposition also remains a standard exact identity:

- body term `W = (B^L - k^L) / M` (repo alias: "orbit weave")
- correction term `F = (k^L - 1) / M` (repo alias: "closure flux")
- reptend integer `R = W + F`

These labels are optional aliases for the standard algebraic split. They are not introduced here as novel mathematical objects.

## Empirical Observations and Curated Examples

### Visibility heuristic for small residues

Status: `empirical`

Small `k`, and especially the bridge case `q = 1`, tends to delay visible carry interactions. This is useful for choosing readable examples, but it is a heuristic rather than a theorem-level classification.

Use [docs/CARRIED_PREFIX_VISIBILITY.md](/Users/mikepurvis/other/quadratic-residue-reptends/docs/CARRIED_PREFIX_VISIBILITY.md) for the exact Track 16 observables:
raw-prefix agreement length, first incoming-carry position, local overflow boundary, and stabilization lookahead.

Examples in base 10:

| Modulus | Mode `m` | `B` | `q` | `k` | What stays visible early |
|---------|----------|-----|-----|-----|--------------------------|
| `37` | `3` | `1000` | `27` | `1` | constant coefficients `27, 27, 27, ...` |
| `97` | `2` | `100` | `1` | `3` | literal powers `1, 3, 9, 27, 81, ...` before carry pressure |
| `249` | `3` | `1000` | `4` | `4` | small `q*k^j` coefficients for several blocks |
| `996` | `3` | `1000` | `1` | `4` | bridge-style composite example with `q = 1` |

### Base-invariant stride counts when nondegenerate

Status: exact consequence plus curated example

When every base under consideration has `ord_p(B)` equal to either `(p-1)/2` or `p-1`, the QR-generating stride count is exactly `phi((p-1)/2)` for each such base. The stride values differ by base, but the count does not.

Example at `p = 23`:

| Base | `ord_p(B)` | Reptend type | QR-generating stride count |
|------|------------|--------------|----------------------------|
| `2` | `11` | half | `10` |
| `7` | `22` | full | `10` |
| `10` | `22` | full | `10` |
| `12` | `11` | half | `10` |

### Curated prime examples

Status: `empirical`

- `p = 19`, base `10`: useful counterexample to the legacy "all even strides" prose. Exact QR-generating strides are `[2, 4, 8, 10, 14, 16]`.
- `p = 31`, base `10`: useful counterexample to the legacy "all consecutive strides" prose. Exact QR-generating strides are `[1, 2, 4, 7, 8, 11, 13, 14]`.
- `p = 97`, base `10`: canonical bridge example with `q = 1`, `k = 3`, and a clean QR-generator at stride `2`.

### Curated composite examples

Status: `empirical`

- `21`: simple CRT example with period `lcm(ord_3(10), ord_7(10)) = 6`.
- `27`: prime-power composite with nontrivial local structure.
- `249 = 3 * 83`: stripped periodic core of `996`, useful for composite block analysis.
- `996`: example where stripping base factors exposes the purely periodic modulus `249`.

### Current sweep statistics

Status: `empirical`

From the current prime sweep under `data/sweep_500.csv`:

- total odd primes analyzed under `500`: `93`
- count-invariant primes across bases `{2, 7, 10, 12}`: `30`
- primes with `0` QR-generating strides in base `10`: `28`
- primes where base `10` itself is a QR-generator: `30`

These numbers are useful for orientation and example selection. They are not a replacement for exact proofs.

## Open Questions

Status of every item in this section: `open`

1. Can the repo characterize the most instructive nontrivial bridge examples without trivial period-1 cases dominating the search output?
2. What is the cleanest exact interface between the carry transducer and the long-division DFA?
3. Which composite examples best expose CRT local order structure and carry behavior together?
4. Can the `phi((p-1)/2)` stride-count theorem be formalized cleanly in Lean without fighting finite-cardinality notation?
5. Which empirical visibility heuristics for small `k` can be upgraded to exact statements, and which should remain heuristics?
